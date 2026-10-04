import BalancedAssortments.ComplexityTimeBinary

namespace BalancedAssortments.KnapsackCostRange
open ComplexityTimeBinary

/-- Unary loop count, binary counter contents. No decoded integer increment. -/
def rangeFrom : ℕ → List Bool → List (List Bool) × ℕ
  | 0, _ => ([], 1)
  | n+1, x =>
      let next := addCarry x [true] false
      let rest := rangeFrom n next.1
      (x :: rest.1, next.2 + rest.2 + 4)

theorem rangeFrom_length (n : ℕ) (x : List Bool) : (rangeFrom n x).1.length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [rangeFrom, ih]

theorem rangeFrom_values (n : ℕ) (x : List Bool) :
    (rangeFrom n x).1.map value = (List.range n).map (fun j => value x + j) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [rangeFrom, List.map_cons, ih, List.map_map, addCarry_value, value,
      Bool.toNat_true, List.nil_eq, Bool.toNat_false, Nat.add_zero, Nat.mul_zero,
      Function.comp_apply]
    congr 1
    apply List.map_congr_left
    intro j _
    dsimp only [Function.comp_apply]
    omega

theorem rangeFrom_width (n : ℕ) (x : List Bool) :
    ∀ p ∈ (rangeFrom n x).1, p.length ≤ x.length + 2*n := by
  induction n generalizing x with
  | zero => simp [rangeFrom]
  | succ n ih =>
    intro p hp
    simp only [rangeFrom, List.mem_cons] at hp
    rcases hp with rfl | hp
    · omega
    · have hh := ih (addCarry x [true] false).1 p hp
      rw [addCarry_length] at hh
      simp only [List.length_cons, List.length_nil] at hh
      omega

theorem rangeFrom_cost (n : ℕ) (x : List Bool) :
    (rangeFrom n x).2 ≤ 64*n*(x.length+2*n+1)+1 := by
  induction n generalizing x with
  | zero => simp [rangeFrom]
  | succ n ih =>
    have hh := ih (addCarry x [true] false).1
    simp only [addCarry_length, List.length_cons, List.length_nil] at hh
    simp only [rangeFrom, addCarry_cost, List.length_cons, List.length_nil]
    have hm : max x.length 1 ≤ x.length+1 := by omega
    have hm' := Nat.mul_le_mul_left n hm
    simp only [Nat.zero_add] at hh ⊢
    nlinarith

def scoreRange (bound : ℕ) := rangeFrom (bound+1) []

theorem scoreRange_values (bound : ℕ) :
    (scoreRange bound).1.map value = List.range (bound+1) := by
  simpa [scoreRange, value] using rangeFrom_values (bound+1) []

end BalancedAssortments.KnapsackCostRange
