import BalancedAssortments.DecompositionCostBounds

namespace BalancedAssortments.Decomposition

/-- Integer-grid representation of residual marginals. -/
def gridValues {n : ℕ} (R : ℕ) (a : Fin n → ℕ) : Fin n → ℚ :=
  fun i => (a i : ℚ) / R

def gridFractional {n : ℕ} (R : ℕ) (a : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => a i ≠ 0 ∧ a i ≠ R

def gridOnes {n : ℕ} (R : ℕ) (a : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => a i = R

def gridPositive {n : ℕ} (a : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 < a i

/-- The same index-order selection as `greedySet`, using only natural-number
comparison, finite filtering, and list operations. -/
def gridSet {n : ℕ} (K R : ℕ) (a : Fin n → ℕ) : Finset (Fin n) :=
  gridOnes R a ∪ (((gridPositive a \ gridOnes R a).sort (· ≤ ·)).take
    (K - (gridOnes R a).card)).toFinset

def gridStepBound {n : ℕ} (R : ℕ) (a : Fin n → ℕ)
    (S : Finset (Fin n)) (i : Fin n) : ℕ := if i ∈ S then a i else R - a i

def gridStep {n : ℕ} (R : ℕ) (a : Fin n → ℕ) (S : Finset (Fin n)) : ℕ :=
  if hf : (gridFractional R a).Nonempty then
    ((gridFractional R a).image (gridStepBound R a S)).min' (hf.image _)
  else R

def gridResidual {n : ℕ} (a : Fin n → ℕ) (S : Finset (Fin n)) (m : ℕ) : Fin n → ℕ :=
  fun i => if i ∈ S then a i - m else a i

/-- Unreduced fractions: all atoms share the input denominator. This output
representation deliberately does not invoke gcd or rational normalization. -/
abbrev GridAtom (n : ℕ) := ℕ × Finset (Fin n)

def gridAux {n : ℕ} : ℕ → ℕ → ℕ → (Fin n → ℕ) → List (GridAtom n)
  | 0, _, R, a => [(R, gridOnes R a)]
  | fuel + 1, K, R, a =>
    if gridFractional R a = ∅ then [(R, gridOnes R a)] else
      let S := gridSet K R a
      let m := gridStep R a S
      (m, S) :: gridAux fuel K (R - m) (gridResidual a S m)

/-- Mathematical interpretation of an unreduced-fraction output, not a step of
its binary implementation. -/
def interpretGrid {n : ℕ} (D : ℕ) (p : List (GridAtom n)) : List (Atom n) :=
  p.map fun a => ((a.1 : ℚ) / D, a.2)

@[simp] theorem fractional_gridValues {n R : ℕ} (hR : 0 < R) (a : Fin n → ℕ) :
    fractional (gridValues R a) = gridFractional R a := by
  ext i
  have hRq : (R : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  simp [fractional, gridFractional, gridValues, div_eq_one_iff_eq hRq, hRq, ne_of_gt hR]

@[simp] theorem ones_gridValues {n R : ℕ} (hR : 0 < R) (a : Fin n → ℕ) :
    ones (gridValues R a) = gridOnes R a := by
  ext i
  have hRq : (R : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  simp [ones, gridOnes, gridValues, div_eq_one_iff_eq hRq]

@[simp] theorem positive_gridValues {n R : ℕ} (hR : 0 < R) (a : Fin n → ℕ) :
    positive (gridValues R a) = gridPositive a := by
  ext i
  have hRq : (0 : ℚ) < R := by exact_mod_cast hR
  simp [positive, gridPositive, gridValues, div_pos_iff_of_pos_right hRq]

@[simp] theorem greedySet_gridValues {n K R : ℕ} (hR : 0 < R) (a : Fin n → ℕ) :
    greedySet K (gridValues R a) = gridSet K R a := by
  simp [greedySet, gridSet, hR]

theorem stepBound_gridValues {n R : ℕ} (hR : 0 < R) (a : Fin n → ℕ)
    (ha : ∀ i, a i ≤ R) (S : Finset (Fin n)) (i : Fin n) :
    stepBound (gridValues R a) S i = (gridStepBound R a S i : ℚ) / R := by
  have hRq : (R : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  by_cases hi : i ∈ S
  · simp [stepBound, gridStepBound, gridValues, hi]
  · simp only [stepBound, gridStepBound, hi, ↓reduceIte, gridValues, Nat.cast_sub (ha i)]
    field_simp

/-- Integer minimum and rational minimum select the same boundary distance. -/
theorem greedyStep_gridValues {n K R : ℕ} (hR : 0 < R) (a : Fin n → ℕ)
    (h : Feasible K (gridValues R a)) (S : Finset (Fin n)) :
    greedyStep (gridValues R a) S = (gridStep R a S : ℚ) / R := by
  have hRq : (0 : ℚ) < R := by exact_mod_cast hR
  have ha : ∀ i, a i ≤ R := by
    intro i
    have hh := (h.1 i).2
    dsimp [gridValues] at hh
    have hh' := (div_le_one hRq).mp hh
    exact_mod_cast hh'
  by_cases hf : (gridFractional R a).Nonempty
  · have hqf : (fractional (gridValues R a)).Nonempty := by simpa [hR] using hf
    simp only [greedyStep, dif_pos hqf, gridStep, dif_pos hf]
    obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp
      (((gridFractional R a).image (gridStepBound R a S)).min'_mem (hf.image _))
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp
      (((fractional (gridValues R a)).image (stepBound (gridValues R a) S)).min'_mem (hqf.image _))
    apply le_antisymm
    · rw [← hie, ← stepBound_gridValues hR a ha S i]
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨i, by simpa [hR] using hi, rfl⟩
    · rw [← hje, stepBound_gridValues hR a ha S j]
      apply (div_le_div_iff_of_pos_right hRq).mpr
      exact_mod_cast Finset.min'_le ((gridFractional R a).image (gridStepBound R a S))
        (gridStepBound R a S j) (Finset.mem_image.mpr ⟨j, by simpa [hR] using hj, rfl⟩)
  · have hqf : ¬(fractional (gridValues R a)).Nonempty := by simpa [hR] using hf
    simp [greedyStep, gridStep, hf, hqf, ne_of_gt hR]

theorem gridResidual_values {n R m : ℕ} (hR : 0 < R) (hm : m < R)
    (a : Fin n → ℕ) (S : Finset (Fin n)) (ha : ∀ i ∈ S, m ≤ a i) :
    gridValues (R - m) (gridResidual a S m) =
      residual (gridValues R a) S ((m : ℚ) / R) := by
  funext i
  have hRq : (R : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  have hmR : (R : ℚ) - m ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr (by exact_mod_cast hm)
  by_cases hi : i ∈ S
  · simp only [gridValues, gridResidual, residual, hi, ↓reduceIte,
      Nat.cast_sub hm.le, Nat.cast_sub (ha i hi)]
    field_simp
    <;> ring
  · simp only [gridValues, gridResidual, residual, hi, ↓reduceIte,
      Nat.cast_sub hm.le, sub_zero]
    field_simp
    <;> ring

/-- Grid execution represents exactly the rational algorithm, with every atom
scaled by the current remaining probability mass `R/D`. -/
theorem gridAux_eq_greedyAux {n D : ℕ} (fuel K R : ℕ) (a : Fin n → ℕ)
    (hR : 0 < R) (h : Feasible K (gridValues R a)) :
    interpretGrid D (gridAux fuel K R a) =
      (greedyAux fuel K (gridValues R a)).map (fun b => ((R : ℚ) / D * b.1, b.2)) := by
  induction fuel generalizing R a with
  | zero => simp [gridAux, greedyAux, interpretGrid, hR]
  | succ fuel ih =>
    by_cases hf : gridFractional R a = ∅
    · simp [gridAux, greedyAux, interpretGrid, hR, hf]
    · let S := gridSet K R a
      let m := gridStep R a S
      have hS : PeelSet K (gridValues R a) S := by
        simpa [S, hR] using greedySet_valid h
      have hqf : (fractional (gridValues R a)).Nonempty := by
        simpa [hR] using Finset.nonempty_iff_ne_empty.mpr hf
      obtain ⟨ht0, ht1, hb, _, _, _⟩ := greedyStep_spec h hS hqf
      rw [greedyStep_gridValues hR a h S] at ht0 ht1 hb
      change 0 < (m : ℚ) / R at ht0
      change (m : ℚ) / R < 1 at ht1
      have hRq : (0 : ℚ) < R := by exact_mod_cast hR
      have hm : m < R := by exact_mod_cast (div_lt_one hRq).mp ht1
      have hma : ∀ i ∈ S, m ≤ a i := by
        intro i hi
        have hh := hb i
        simp only [stepBound, hi, ↓reduceIte, gridValues] at hh
        exact_mod_cast (div_le_div_iff_of_pos_right hRq).mp hh
      have hreseq := gridResidual_values hR hm a S hma
      have hres : Feasible K (gridValues (R - m) (gridResidual a S m)) := by
        rw [hreseq]
        exact residual_feasible h hS ht1 hb
      have hi := ih (R - m) (gridResidual a S m) (Nat.sub_pos_of_lt hm) hres
      simp only [gridAux, if_neg hf, greedyAux, fractional_gridValues hR a,
        if_neg hf, greedySet_gridValues hR a, greedyStep_gridValues hR a h] 
      change interpretGrid D ((m, S) :: gridAux fuel K (R - m) (gridResidual a S m)) =
        (prependPeel S ((m : ℚ) / R)
          (greedyAux fuel K (residual (gridValues R a) S ((m : ℚ) / R)))).map _
      simp only [interpretGrid, List.map_cons] at hi ⊢
      rw [hi, hreseq]
      simp only [prependPeel, List.map_cons, List.map_map, Function.comp_def]
      congr 1
      · congr 1
        field_simp
      · apply List.map_congr_left
        intro b _
        apply Prod.ext
        · dsimp
          rw [Nat.cast_sub hm.le]
          field_simp
          <;> ring
        · rfl

/-- Common-grid input counts computed without division or gcd: multiply the
input numerator by the product of every *other* denominator. -/
def initialGridCounts {n : ℕ} (z : Fin n → ℚ) (i : Fin n) : ℕ :=
  (z i).num.natAbs * ∏ j ∈ Finset.univ.erase i, (z j).den

/-- Integer-grid implementation returns natural numerators and one shared
natural denominator, with no normalization required in the output format. -/
def gridGreedy {n : ℕ} (K : ℕ) (z : Fin n → ℚ) : ℕ × List (GridAtom n) :=
  (commonDenominator z, gridAux n K (commonDenominator z) (initialGridCounts z))

theorem initialGridValues {n : ℕ} {z : Fin n → ℚ} (hz : ∀ i, 0 ≤ z i) :
    gridValues (commonDenominator z) (initialGridCounts z) = z := by
  funext i
  have hp : 0 < ∏ j ∈ Finset.univ.erase i, (z j).den :=
    Finset.prod_pos (fun j _ => Rat.den_pos _)
  have hprod : commonDenominator z = (z i).den * ∏ j ∈ Finset.univ.erase i, (z j).den := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hnum : ((z i).num.natAbs : ℚ) = ((z i).num : ℚ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (Rat.num_nonneg.mpr (hz i))]
  simp only [gridValues, initialGridCounts, Nat.cast_mul, hnum, hprod]
  rw [mul_div_mul_right _ _ (by exact_mod_cast ne_of_gt hp), Rat.num_div_den]

/-- Exact refinement theorem: interpreting the unnormalized integer output
recovers the original certified rational greedy policy, atom for atom. -/
theorem gridGreedy_eq_greedy {n K : ℕ} {z : Fin n → ℚ} (h : Feasible K z) :
    interpretGrid (gridGreedy K z).1 (gridGreedy K z).2 = greedy K z := by
  have hi := initialGridValues (fun i => (h.1 i).1)
  have hg := gridAux_eq_greedyAux (D := commonDenominator z) n K
    (commonDenominator z) (initialGridCounts z) (commonDenominator_pos z) (by rwa [hi])
  simpa [gridGreedy, greedy, hi, ne_of_gt (commonDenominator_pos z)] using hg

theorem gridGreedy_correct {n K : ℕ} {z : Fin n → ℚ} (h : Feasible K z) :
    ValidDecomposition K z (interpretGrid (gridGreedy K z).1 (gridGreedy K z).2) ∧
      (gridGreedy K z).2.length ≤ n + 1 := by
  constructor
  · rw [gridGreedy_eq_greedy h]
    exact (greedy_correct h).1
  · have hh := (greedy_correct h).2
    rw [← gridGreedy_eq_greedy h] at hh
    simpa [interpretGrid] using hh

/-- All initial natural quantities have at most the common denominator's size. -/
theorem initialGridCounts_le {n K : ℕ} {z : Fin n → ℚ} (h : Feasible K z)
    (i : Fin n) : initialGridCounts z i ≤ commonDenominator z := by
  have he := congrFun (initialGridValues (fun i => (h.1 i).1)) i
  have hD : (0 : ℚ) < commonDenominator z := by exact_mod_cast commonDenominator_pos z
  have hh : ((initialGridCounts z i : ℕ) : ℚ) / commonDenominator z ≤ 1 := by
    change gridValues (commonDenominator z) (initialGridCounts z) i ≤ 1
    rw [he]
    exact (h.1 i).2
  exact_mod_cast (div_le_one hD).mp hh

end BalancedAssortments.Decomposition
