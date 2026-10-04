import BalancedAssortments.PolyhedralBasis
import BalancedAssortments.SalesIntegration

/-! Explicit rational inequality rows for the paper's guessed-support
revenue-threshold certificate, with exact semantic equivalence. -/
namespace BalancedAssortments.DecisionPolyhedron
open scoped BigOperators

inductive Row (n : ℕ)
  | nonnegative (i : Fin n)
  | cap (i : Fin n)
  | rank
  | balance (i j : Fin n)
  | offsupport (i : Fin n)
  | target
  deriving DecidableEq, Fintype

def coefficient {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (A : Finset (Fin n)) :
    Row n → Fin n → ℚ
  | .nonnegative i, j => if j = i then -1 else 0
  | .cap i, j => if j = i then 1 else 0
  | .rank, j => 1 / v j
  | .balance i k, j => if i ∈ A ∧ k ∈ A then
      α * (if j = k then 1 else 0) - (if j = i then 1 else 0) else 0
  | .offsupport i, j => if i ∈ A then 0 else if j = i then 1 else 0
  | .target, j => H - r j

def bound {n : ℕ} (v : Fin n → ℚ) (K : ℕ) (H : ℚ) : Row n → ℚ
  | .cap i => v i
  | .rank => K
  | .target => -H
  | _ => 0

noncomputable def realMatrix {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ)
    (A : Finset (Fin n)) : Matrix (Row n) (Fin n) ℝ :=
  fun row j => (coefficient v r α H A row j : ℝ)

noncomputable def realBound {n : ℕ} (v : Fin n → ℚ) (K : ℕ) (H : ℚ) : Row n → ℝ :=
  fun row => (bound v K H row : ℝ)

/-- Linear guessed-support constraints, including the transformed target row. -/
def LinearFeasible {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) (w : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ w i ∧ w i ≤ (v i : ℝ)) ∧
  (∑ i, w i / (v i : ℝ)) ≤ (K : ℝ) ∧
  (∀ i, i ∉ A → w i = 0) ∧
  (∀ i ∈ A, ∀ j ∈ A, (α : ℝ) * w j ≤ w i) ∧
  (H : ℝ) ≤ ∑ i, ((r i : ℝ) - H) * w i

private lemma ratCast_ite (p : Prop) [Decidable p] (a b : ℚ) :
    ((if p then a else b : ℚ) : ℝ) = if p then (a : ℝ) else (b : ℝ) := by
  split_ifs <;> rfl

private lemma eval_nonnegative {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ)
    (A : Finset (Fin n)) (w : Fin n → ℝ) (i : Fin n) :
    PolyhedralBasis.evaluate (realMatrix v r α H A) w (.nonnegative i) = -w i := by
  simp [PolyhedralBasis.evaluate, realMatrix, coefficient, ratCast_ite, ite_mul, Finset.sum_ite_eq']

private lemma eval_cap {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ)
    (A : Finset (Fin n)) (w : Fin n → ℝ) (i : Fin n) :
    PolyhedralBasis.evaluate (realMatrix v r α H A) w (.cap i) = w i := by
  simp [PolyhedralBasis.evaluate, realMatrix, coefficient, ratCast_ite, ite_mul, Finset.sum_ite_eq']

private lemma eval_rank {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ)
    (A : Finset (Fin n)) (w : Fin n → ℝ) :
    PolyhedralBasis.evaluate (realMatrix v r α H A) w .rank = ∑ i, w i / (v i : ℝ) := by
  simp [PolyhedralBasis.evaluate, realMatrix, coefficient, ratCast_ite, div_eq_mul_inv, mul_comm]

private lemma eval_balance {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ)
    (A : Finset (Fin n)) (w : Fin n → ℝ) (i j : Fin n) :
    PolyhedralBasis.evaluate (realMatrix v r α H A) w (.balance i j) =
      if i ∈ A ∧ j ∈ A then (α : ℝ) * w j - w i else 0 := by
  by_cases h : i ∈ A ∧ j ∈ A
  · simp [PolyhedralBasis.evaluate, realMatrix, coefficient, ratCast_ite, h, sub_mul,
      Finset.sum_sub_distrib, ite_mul, mul_ite, Finset.sum_ite_eq']
  · simp [PolyhedralBasis.evaluate, realMatrix, coefficient, ratCast_ite, h]

private lemma eval_offsupport {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ)
    (A : Finset (Fin n)) (w : Fin n → ℝ) (i : Fin n) :
    PolyhedralBasis.evaluate (realMatrix v r α H A) w (.offsupport i) =
      if i ∈ A then 0 else w i := by
  by_cases h : i ∈ A
  · simp [PolyhedralBasis.evaluate, realMatrix, coefficient, ratCast_ite, h]
  · simp [PolyhedralBasis.evaluate, realMatrix, coefficient, ratCast_ite, h, ite_mul, Finset.sum_ite_eq']

private lemma eval_target {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ)
    (A : Finset (Fin n)) (w : Fin n → ℝ) :
    PolyhedralBasis.evaluate (realMatrix v r α H A) w .target =
      -(∑ i, ((r i : ℝ) - H) * w i) := by
  simp only [PolyhedralBasis.evaluate, realMatrix, coefficient, ratCast_ite, Rat.cast_sub,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The row datatype represents exactly the intended source linear constraints. -/
theorem rows_iff {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) (w : Fin n → ℝ) :
    w ∈ PolyhedralBasis.polyhedron (realMatrix v r α H A) (realBound v K H) ↔
      LinearFeasible v r α H K A w := by
  constructor
  · intro hw
    have hn : ∀ i, 0 ≤ w i := by
      intro i
      have hh := hw (.nonnegative i)
      rw [eval_nonnegative] at hh
      simpa [realBound, bound] using hh
    refine ⟨fun i => ⟨hn i, ?_⟩, ?_, ?_, ?_, ?_⟩
    · have hh := hw (.cap i)
      simpa [eval_cap, realBound, bound] using hh
    · have hh := hw .rank
      simpa [eval_rank, realBound, bound] using hh
    · intro i hi
      have hh := hw (.offsupport i)
      rw [eval_offsupport, if_neg hi] at hh
      have hh' : w i ≤ 0 := by simpa [realBound, bound] using hh
      exact le_antisymm hh' (hn i)
    · intro i hi j hj
      have hh := hw (.balance i j)
      rw [eval_balance, if_pos ⟨hi, hj⟩] at hh
      have hh' : (α : ℝ) * w j - w i ≤ 0 := by simpa [realBound, bound] using hh
      linarith
    · have hh := hw .target
      rw [eval_target] at hh
      simpa [realBound, bound] using hh
  · rintro ⟨hc, hr, ho, hb, ht⟩ row
    cases row with
    | nonnegative i => simpa [eval_nonnegative, realBound, bound] using (hc i).1
    | cap i => simpa [eval_cap, realBound, bound] using (hc i).2
    | rank => simpa [eval_rank, realBound, bound] using hr
    | balance i j =>
      rw [eval_balance]
      by_cases h : i ∈ A ∧ j ∈ A
      · simp only [if_pos h]
        have hh := hb i h.1 j h.2
        simp only [realBound, bound, Rat.cast_zero]
        change (α : ℝ) * w j - w i ≤ 0
        linarith
      · simp [h, realBound, bound]
    | offsupport i =>
      rw [eval_offsupport]
      by_cases h : i ∈ A
      · simp [h, realBound, bound]
      · simp [h, ho i h, realBound, bound]
    | target => simpa [eval_target, realBound, bound] using ht

/-- The transformed target row is equivalent to the paper's actual fractional objective. -/
theorem target_iff {n : ℕ} (r : Fin n → ℚ) (H : ℚ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (H : ℝ) ≤ (∑ i, ((r i : ℝ) - H) * w i) ↔
      (H : ℝ) ≤ Sales.objective (fun i => (r i : ℝ)) w := by
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hw i)
  unfold Sales.objective
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 + ∑ i, w i)]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  constructor <;> intro h <;> nlinarith

/-- Coordinate cap rows make the actual encoded polyhedron compact. -/
theorem rows_compact {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) :
    IsCompact (PolyhedralBasis.polyhedron (realMatrix v r α H A) (realBound v K H)) := by
  apply PolyhedralBasis.polyhedron_compact _ _ (fun _ => 0) (fun i => (v i : ℝ))
  intro w hw i
  exact ((rows_iff v r α H K A w).1 hw).1 i


/-- A feasible guessed-support row system is feasible for the original compact
model and attains the requested objective threshold. -/
theorem rows_source_sound {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) (w : Fin n → ℝ)
    (hw : w ∈ PolyhedralBasis.polyhedron (realMatrix v r α H A) (realBound v K H)) :
    Sales.CompactFeasible (fun i => (v i : ℝ)) w K ∧ Sales.Balanced (α : ℝ) w ∧
      (H : ℝ) ≤ Sales.objective (fun i => (r i : ℝ)) w := by
  obtain ⟨hc, hr, ho, hb, ht⟩ := (rows_iff v r α H K A w).1 hw
  refine ⟨⟨hc, hr⟩, ?_, (target_iff r H w (fun i => (hc i).1)).1 ht⟩
  intro i
  by_cases hz : w i = 0
  · exact Or.inl hz
  · right
    have hi : i ∈ A := by
      by_contra hi
      exact hz (ho i hi)
    intro j
    by_cases hj : j ∈ A
    · exact hb i hi j hj
    · rw [ho j hj, mul_zero]
      exact (hc i).1

/-- Conversely, guessing exactly the nonzero support encodes every original
compact feasible solution, including the all-zero case. -/
theorem source_rows_complete {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (w : Fin n → ℝ)
    (hc : Sales.CompactFeasible (fun i => (v i : ℝ)) w K)
    (hb : Sales.Balanced (α : ℝ) w)
    (ht : (H : ℝ) ≤ Sales.objective (fun i => (r i : ℝ)) w) :
    ∃ A : Finset (Fin n),
      w ∈ PolyhedralBasis.polyhedron (realMatrix v r α H A) (realBound v K H) := by
  classical
  let A := Finset.univ.filter fun i => w i ≠ 0
  refine ⟨A, (rows_iff v r α H K A w).2 ?_⟩
  refine ⟨hc.1, hc.2, ?_, ?_, (target_iff r H w (fun i => (hc.1 i).1)).2 ht⟩
  · intro i hi
    simpa [A] using hi
  · intro i hi j _
    have hwi : w i ≠ 0 := (Finset.mem_filter.mp hi).2
    exact (hb i).resolve_left hwi j

/-- Exact source decision problem equals existence of a nonempty encoded row
polyhedron for some guessed finite support. -/
theorem source_decision_iff {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ) :
    (∃ w : Fin n → ℝ,
      Sales.CompactFeasible (fun i => (v i : ℝ)) w K ∧ Sales.Balanced (α : ℝ) w ∧
        (H : ℝ) ≤ Sales.objective (fun i => (r i : ℝ)) w) ↔
    ∃ A : Finset (Fin n),
      (PolyhedralBasis.polyhedron (realMatrix v r α H A) (realBound v K H)).Nonempty := by
  constructor
  · rintro ⟨w, hc, hb, ht⟩
    obtain ⟨A, hw⟩ := source_rows_complete v r α H K w hc hb ht
    exact ⟨A, w, hw⟩
  · rintro ⟨A, w, hw⟩
    exact ⟨w, rows_source_sound v r α H K A w hw⟩


/-- The concrete row enumeration has a quadratic number of inequalities. -/
def rowEquiv (n : ℕ) : Row n ≃
    (Fin n ⊕ Fin n ⊕ Unit ⊕ (Fin n × Fin n) ⊕ Fin n ⊕ Unit) where
  toFun
    | .nonnegative i => .inl i
    | .cap i => .inr (.inl i)
    | .rank => .inr (.inr (.inl ()))
    | .balance i j => .inr (.inr (.inr (.inl (i, j))))
    | .offsupport i => .inr (.inr (.inr (.inr (.inl i))))
    | .target => .inr (.inr (.inr (.inr (.inr ()))))
  invFun
    | .inl i => .nonnegative i
    | .inr (.inl i) => .cap i
    | .inr (.inr (.inl _)) => .rank
    | .inr (.inr (.inr (.inl (i, j)))) => .balance i j
    | .inr (.inr (.inr (.inr (.inl i)))) => .offsupport i
    | .inr (.inr (.inr (.inr (.inr _)))) => .target
  left_inv row := by cases row <;> rfl
  right_inv row := by
    rcases row with i | i | u | ⟨i, j⟩ | i | u
    all_goals first | rfl | cases u; rfl

theorem row_count (n : ℕ) : Fintype.card (Row n) = n*n + 3*n + 2 := by
  rw [Fintype.card_congr (rowEquiv n)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  omega

end BalancedAssortments.DecisionPolyhedron
