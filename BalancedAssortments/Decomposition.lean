import Mathlib

/-!
# Executable rational circular-interval decomposition

This file defines the paper's circular-interval construction directly over `ℚ`.
No convex-hull oracle is used. This circular implementation is an optional
reference whose general correctness is not asserted here. The fully certified
constructive algorithm is `greedy` in `DecompositionAlgorithm.lean`, proved
correct for every feasible rational input. `ValidDecomposition` is an exact,
decidable output certificate, not an assumption on the input polytope.
-/

namespace BalancedAssortments
namespace Decomposition

abbrev Atom (n : ℕ) := ℚ × Finset (Fin n)

/-- Cumulative endpoints of the product intervals. -/
def cumulative {n : ℕ} (z : Fin n → ℚ) (j : ℕ) : ℚ :=
  ∑ i : Fin n, if i.val < j then z i else 0

/-- Fractional endpoints, including repetitions. Repetitions make zero-weight
atoms and do not harm the linear support bound. -/
def cuts {n : ℕ} (z : Fin n → ℚ) : List ℚ :=
  ((List.finRange n).map fun i => Int.fract (cumulative z (i.val + 1))).mergeSort (· ≤ ·)

/-- Adjacent cells of a list of endpoints. -/
def cells : List ℚ → List (ℚ × ℚ)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: cells (b :: rest)

/-- The products whose half-open intervals cover a lattice translate of `u`.
The finite lattice range makes this definition executable even on invalid input. -/
def selected {n : ℕ} (K : ℕ) (z : Fin n → ℚ) (u : ℚ) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ j ∈ Finset.range K,
    cumulative z i.val ≤ u + (j : ℚ) ∧ u + (j : ℚ) < cumulative z (i.val + 1)

/-- The rational algorithm. Each cell is sampled at its midpoint. -/
def circular {n : ℕ} (K : ℕ) (z : Fin n → ℚ) : List (Atom n) :=
  (cells (0 :: cuts z ++ [1])).map fun ab =>
    (ab.2 - ab.1, selected K z ((ab.1 + ab.2) / 2))

/-- Exactly checkable distribution certificate. -/
def ValidDecomposition {n : ℕ} (K : ℕ) (z : Fin n → ℚ)
    (p : List (Atom n)) : Prop :=
  (∀ a ∈ p, 0 ≤ a.1) ∧
  (p.map Prod.fst).sum = 1 ∧
  (∀ a ∈ p, a.1 ≠ 0 → a.2.card ≤ K) ∧
  (∀ i : Fin n, (p.map fun a => if i ∈ a.2 then a.1 else 0).sum = z i)

instance {n : ℕ} (K : ℕ) (z : Fin n → ℚ) (p : List (Atom n)) :
    Decidable (ValidDecomposition K z p) := by
  unfold ValidDecomposition
  infer_instance

/-- A terminating proof-producing wrapper: accepts exactly outputs satisfying
all distribution and marginal requirements. Rejection is explicit. -/
def checkedCircular {n : ℕ} (K : ℕ) (z : Fin n → ℚ) :
    Option {p : List (Atom n) // ValidDecomposition K z p} :=
  if h : ValidDecomposition K z (circular K z) then some ⟨circular K z, h⟩ else none

@[simp] theorem cuts_length {n : ℕ} (z : Fin n → ℚ) : (cuts z).length = n := by
  simp [cuts]

@[simp] theorem cells_length (l : List ℚ) : (cells l).length = l.length - 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simp only [cells, List.length_cons] at *; omega

/-- The algorithm always returns at most `n+1` atoms, including zero weights.
Thus its number of positive-support assortments is at most `n+1`. -/
theorem circular_length {n : ℕ} (K : ℕ) (z : Fin n → ℚ) :
    (circular K z).length = n + 1 := by
  simp [circular]

private theorem cells_telescope (a b : ℚ) (l : List ℚ) :
    ((cells (a :: l ++ [b])).map fun ab => ab.2 - ab.1).sum = b - a := by
  induction l generalizing a with
  | nil => simp [cells]
  | cons c l ih =>
    simp only [List.cons_append, cells, List.map_cons, List.sum_cons]
    rw [show (cells (c :: (l ++ [b])) |>.map fun ab => ab.2 - ab.1).sum = b - c from ih c]
    ring

/-- All atom weights sum to exactly one, even before certificate checking. -/
theorem circular_mass {n : ℕ} (K : ℕ) (z : Fin n → ℚ) :
    ((circular K z).map Prod.fst).sum = 1 := by
  simp only [circular, List.map_map, Function.comp_def]
  simpa using cells_telescope 0 1 (cuts z)

/-- Successful checking carries the exact feasibility/marginal proof. -/
theorem checkedCircular_sound {n : ℕ} (K : ℕ) (z : Fin n → ℚ)
    (p : {p : List (Atom n) // ValidDecomposition K z p})
    (_h : checkedCircular K z = some p) : ValidDecomposition K z p.val := p.property

@[simp] theorem selected_zero {n : ℕ} (z : Fin n → ℚ) (u : ℚ) :
    selected 0 z u = ∅ := by simp [selected]

end Decomposition
end BalancedAssortments
