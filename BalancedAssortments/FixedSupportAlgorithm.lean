import BalancedAssortments.FixedSupportAlgorithmBreakpoints
import BalancedAssortments.ContinuousKnapsack

namespace BalancedAssortments.FixedSupportAlgorithm

/-- Executable rational score used to order continuous-knapsack increments. -/
def score {n : ℕ} (r v : Fin n → ℚ) (ρ : ℚ) (i : Fin n) : ℚ := (r i - ρ) * v i

def scoreLine {n : ℕ} (r v : Fin n → ℚ) (i : Fin n) : Affine (𝕜 := ℚ) :=
  (-v i, r i * v i)

def scoreDifference {n : ℕ} (r v : Fin n → ℚ) (ij : Fin n × Fin n) : Affine (𝕜 := ℚ) :=
  (v ij.2 - v ij.1, r ij.1 * v ij.1 - r ij.2 * v ij.2)

def scoreLines {n : ℕ} (r v : Fin n → ℚ) : Finset (Affine (𝕜 := ℚ)) :=
  Finset.univ.image (scoreLine r v) ∪ Finset.univ.image (scoreDifference r v)

def revenueUpper {n : ℕ} (r : Fin n → ℚ) : ℚ :=
  (insert 0 (Finset.univ.image r)).max' (Finset.insert_nonempty _ _)

def inverseSum {n : ℕ} (v : Fin n → ℚ) : ℚ := ∑ i, 1 / v i

/-- The exact largest feasible common baseline; this also handles an empty
coordinate type by the field's totalized zero-division convention. -/
def scaleUpper {n : ℕ} (v : Fin n → ℚ) (K : ℚ) : ℚ :=
  (insert (K / inverseSum v) (Finset.univ.image v)).min' (Finset.insert_nonempty _ _)

def scoreSamples {n : ℕ} (r v : Fin n → ℚ) : Finset ℚ :=
  regimeSamples (affineCritical 0 (revenueUpper r) (scoreLines r v))

def scoreOrder {n : ℕ} (r v : Fin n → ℚ) (ρ : ℚ) : List (Fin n) :=
  (List.finRange n).mergeSort (fun i j => score r v ρ j ≤ score r v ρ i)

def rationalCap {n : ℕ} (v : Fin n → ℚ) (α t : ℚ) (i : Fin n) : ℚ :=
  min 1 (t / (α * v i)) - t / v i

def rationalBudget {n : ℕ} (v : Fin n → ℚ) (K t : ℚ) : ℚ := K - t * inverseSum v

def capCuts {n : ℕ} (v : Fin n → ℚ) (α T : ℚ) : Finset ℚ :=
  insert 0 (insert T ((Finset.univ.image (fun i => α * v i)).filter (fun t => 0 ≤ t ∧ t ≤ T)))

def cappedAt {n : ℕ} (v : Fin n → ℚ) (α a : ℚ) : Finset (Fin n) :=
  Finset.univ.filter fun i => α * v i ≤ a

def prefixDenominator {n : ℕ} (v : Fin n → ℚ) (α : ℚ)
    (P C : Finset (Fin n)) : ℚ :=
  (∑ i ∈ Finset.univ \ P, 1 / v i) + (1 / α) * ∑ i ∈ P \ C, 1 / v i

/-- When the slope denominator vanishes, the value zero is merely a redundant
feasible candidate; no existence of an isolated root is asserted in that case. -/
def prefixRoot {n : ℕ} (v : Fin n → ℚ) (α K a : ℚ) (P : Finset (Fin n)) : ℚ :=
  (K - ((P ∩ cappedAt v α a).card : ℚ)) / prefixDenominator v α P (cappedAt v α a)

def scaleSamples {n : ℕ} (r v : Fin n → ℚ) (α K ρ : ℚ) : Finset ℚ :=
  let T := scaleUpper v K
  let C := capCuts v α T
  C ∪ ((C.product (Finset.range (n + 1))).image
    (fun ak => prefixRoot v α K ak.1 ((scoreOrder r v ρ).take ak.2).toFinset)).filter
      (fun t => 0 ≤ t ∧ t ≤ T)

/-- All score-pattern/scale pairs. Every list operation is executable; there is
no noncomputable convex-hull, LP, optimizer, or root-finding oracle. -/
def candidates {n : ℕ} (r v : Fin n → ℚ) (α K : ℚ) : List (ℚ × ℚ) :=
  (scoreSamples r v).sort (· ≤ ·) |>.flatMap fun ρ =>
    ((scaleSamples r v α K ρ).sort (· ≤ ·)).map (fun t => (ρ, t))

def knapsackItems {n : ℕ} (r v : Fin n → ℚ) (α ρ t : ℚ) : List ContinuousKnapsack.Item :=
  (scoreOrder r v ρ).map fun i => ⟨score r v ρ i, rationalCap v α t i⟩

/-- Recover labels after the exact continuous-knapsack solver. -/
def candidateVector {n : ℕ} (r v : Fin n → ℚ) (α K : ℚ) (p : ℚ × ℚ) : Fin n → ℚ :=
  let o := scoreOrder r v p.1
  let y := (ContinuousKnapsack.solve (rationalBudget v K p.2) (knapsackItems r v α p.1 p.2)).1
  fun i => p.2 + v i * (y[o.idxOf i]?.getD 0)

def fractionalRevenue {n : ℕ} (r w : Fin n → ℚ) : ℚ :=
  (∑ i, r i * w i) / (1 + ∑ i, w i)

def bestCandidate {n : ℕ} (r v : Fin n → ℚ) (α K : ℚ) : ℚ × ℚ :=
  (candidates r v α K).foldl (fun a b =>
    if fractionalRevenue r (candidateVector r v α K a) ≤
      fractionalRevenue r (candidateVector r v α K b) then b else a) (0, 0)

def optimize {n : ℕ} (r v : Fin n → ℚ) (α K : ℚ) : Fin n → ℚ :=
  candidateVector r v α K (bestCandidate r v α K)

@[simp] theorem scoreLine_value {n : ℕ} (r v : Fin n → ℚ) (ρ : ℚ) (i : Fin n) :
    affineValue (scoreLine r v i) ρ = score r v ρ i := by
  simp [affineValue, scoreLine, score]; ring

@[simp] theorem scoreDifference_value {n : ℕ} (r v : Fin n → ℚ) (ρ : ℚ) (i j : Fin n) :
    affineValue (scoreDifference r v (i, j)) ρ = score r v ρ i - score r v ρ j := by
  simp [affineValue, scoreDifference, score]; ring

theorem revenueUpper_nonneg {n : ℕ} (r : Fin n → ℚ) : 0 ≤ revenueUpper r :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem revenue_le_upper {n : ℕ} (r : Fin n → ℚ) (i : Fin n) : r i ≤ revenueUpper r :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

theorem scoreLines_card {n : ℕ} (r v : Fin n → ℚ) : (scoreLines r v).card ≤ n + n ^ 2 := by
  calc
    (scoreLines r v).card ≤ (Finset.univ.image (scoreLine r v)).card +
      (Finset.univ.image (scoreDifference r v)).card := Finset.card_union_le _ _
    _ ≤ Fintype.card (Fin n) + Fintype.card (Fin n × Fin n) :=
      Nat.add_le_add (Finset.card_image_le.trans (by simp)) (Finset.card_image_le.trans (by simp))
    _ = n + n ^ 2 := by simp [pow_two]

theorem affineCritical_card {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (lo hi : 𝕜) (F : Finset (Affine (𝕜 := 𝕜))) :
    (affineCritical lo hi F).card ≤ F.card + 2 := by
  unfold affineCritical
  have h1 := Finset.card_insert_le lo (insert hi
    (((F.filter (fun f => f.1 ≠ 0)).image affineRoot).filter (fun c => lo ≤ c ∧ c ≤ hi)))
  have h2 := Finset.card_insert_le hi
    (((F.filter (fun f => f.1 ≠ 0)).image affineRoot).filter (fun c => lo ≤ c ∧ c ≤ hi))
  have h3 := Finset.card_filter_le (((F.filter (fun f => f.1 ≠ 0)).image affineRoot))
    (fun c => lo ≤ c ∧ c ≤ hi)
  have h4 := Finset.card_image_le (s := F.filter (fun f => f.1 ≠ 0)) (f := affineRoot)
  have h5 := Finset.card_filter_le F (fun f => f.1 ≠ 0)
  omega

theorem scoreSamples_card {n : ℕ} (r v : Fin n → ℚ) :
    (scoreSamples r v).card ≤ (n + n^2 + 2) + (n + n^2 + 2)^2 := by
  have hc := affineCritical_card 0 (revenueUpper r) (scoreLines r v)
  have hf := scoreLines_card r v
  have hs := regimeSamples_card (affineCritical 0 (revenueUpper r) (scoreLines r v))
  unfold scoreSamples
  nlinarith

theorem capCuts_card {n : ℕ} (v : Fin n → ℚ) (α T : ℚ) : (capCuts v α T).card ≤ n + 2 := by
  have h1 := Finset.card_insert_le 0 (insert T
    ((Finset.univ.image (fun i => α * v i)).filter (fun t => 0 ≤ t ∧ t ≤ T)))
  have h2 := Finset.card_insert_le T
    ((Finset.univ.image (fun i => α * v i)).filter (fun t => 0 ≤ t ∧ t ≤ T))
  have h3 := Finset.card_filter_le (Finset.univ.image (fun i => α * v i))
    (fun t => 0 ≤ t ∧ t ≤ T)
  have h4 := Finset.card_image_le (s := Finset.univ) (f := fun i : Fin n => α * v i)
  simp only [Finset.card_univ, Fintype.card_fin] at h4
  unfold capCuts
  omega

@[simp] theorem scoreOrder_length {n : ℕ} (r v : Fin n → ℚ) (ρ : ℚ) :
    (scoreOrder r v ρ).length = n := by simp [scoreOrder]

theorem scaleSamples_card {n : ℕ} (r v : Fin n → ℚ) (α K ρ : ℚ) :
    (scaleSamples r v α K ρ).card ≤ (n + 2)^2 := by
  let C := capCuts v α (scaleUpper v K)
  have hc : C.card ≤ n + 2 := capCuts_card v α _
  have h1 := Finset.card_union_le C
    (((C.product (Finset.range (n + 1))).image
      (fun ak => prefixRoot v α K ak.1 ((scoreOrder r v ρ).take ak.2).toFinset)).filter
        (fun t => 0 ≤ t ∧ t ≤ scaleUpper v K))
  have h2 := Finset.card_filter_le
    ((C.product (Finset.range (n + 1))).image
      (fun ak => prefixRoot v α K ak.1 ((scoreOrder r v ρ).take ak.2).toFinset))
    (fun t => 0 ≤ t ∧ t ≤ scaleUpper v K)
  have h3 := Finset.card_image_le (s := C.product (Finset.range (n + 1)))
    (f := fun ak => prefixRoot v α K ak.1 ((scoreOrder r v ρ).take ak.2).toFinset)
  have hprod : (C.product (Finset.range (n + 1))).card = C.card * (n + 1) := by simp
  rw [hprod] at h3
  apply h1.trans
  apply (Nat.add_le_add_left (h2.trans h3) C.card).trans
  nlinarith [hc]

end BalancedAssortments.FixedSupportAlgorithm
