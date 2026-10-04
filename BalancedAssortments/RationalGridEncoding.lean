import BalancedAssortments.GridBounds
import Mathlib

/-! Explicit numerator/denominator representations of the geometric grid.
The polynomial bit bounds here are mathematical output-size bounds; no
machine-time assertion is hidden in them. -/
namespace BalancedAssortments.RationalGridEncoding

def gridNumerator (a δ : ℚ) (j : ℕ) : ℕ :=
  a.num.natAbs * (δ.den + δ.num.natAbs) ^ j

def gridDenominator (a δ : ℚ) (j : ℕ) : ℕ := a.den * δ.den ^ j

theorem natAbs_num_cast {q : ℚ} (hq : 0 ≤ q) : (q.num.natAbs : ℚ) = q.num := by
  calc (q.num.natAbs : ℚ) = ((q.num.natAbs : ℤ) : ℚ) := by simp
       _ = (q.num : ℚ) := congrArg (fun z : ℤ => (z : ℚ))
         (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq))

theorem grid_representation {a δ : ℚ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (j : ℕ) :
    a * (1 + δ) ^ j = (gridNumerator a δ j : ℚ) / gridDenominator a δ j := by
  have had : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  have hδd : (δ.den : ℚ) ≠ 0 := by exact_mod_cast δ.den_nz
  have haeq : a = (a.num.natAbs : ℚ) / a.den := by
    rw [natAbs_num_cast ha]; exact (Rat.num_div_den a).symm
  have hδeq : 1 + δ = ((δ.den + δ.num.natAbs : ℕ) : ℚ) / δ.den := by
    push_cast
    rw [natAbs_num_cast hδ]
    calc 1 + δ = 1 + (δ.num : ℚ) / δ.den := congrArg (fun x : ℚ => 1 + x) (Rat.num_div_den δ).symm
         _ = ((δ.den : ℚ) + δ.num) / δ.den := by field_simp
  calc a * (1 + δ) ^ j = ((a.num.natAbs : ℚ) / a.den) *
        (((δ.den + δ.num.natAbs : ℕ) : ℚ) / δ.den) ^ j :=
          congrArg₂ (· * ·) haeq (congrArg (· ^ j) hδeq)
       _ = _ := by simp only [gridNumerator, gridDenominator, Nat.cast_mul, Nat.cast_pow, div_pow, div_mul_div_comm]

theorem grid_denominator_positive (a δ : ℚ) (j : ℕ) :
    0 < gridDenominator a δ j := by
  exact Nat.mul_pos a.den_pos (Nat.pow_pos δ.den_pos)

theorem grid_numerator_bound {a δ : ℚ} {b j : ℕ}
    (ha : a.num.natAbs < 2 ^ b) (hn : δ.num.natAbs < 2 ^ b)
    (hd : δ.den < 2 ^ b) : gridNumerator a δ j < 2 ^ (b + (b + 1) * j) := by
  have hsum : δ.den + δ.num.natAbs ≤ 2 ^ (b + 1) := by
    rw [pow_succ]; omega
  have hp := Nat.pow_le_pow_left hsum j
  unfold gridNumerator
  calc a.num.natAbs * (δ.den + δ.num.natAbs) ^ j
      ≤ a.num.natAbs * (2 ^ (b+1)) ^ j := Nat.mul_le_mul_left _ hp
    _ < 2 ^ b * (2 ^ (b+1)) ^ j := Nat.mul_lt_mul_of_pos_right ha (by positivity)
    _ = 2 ^ (b + (b + 1) * j) := by rw [pow_add (2 : ℕ) b ((b+1)*j), pow_mul]

theorem grid_denominator_bound {a δ : ℚ} {b j : ℕ}
    (ha : a.den < 2 ^ b) (hd : δ.den < 2 ^ b) :
    gridDenominator a δ j < 2 ^ (b * (j + 1)) := by
  have hp := Nat.pow_le_pow_left hd.le j
  unfold gridDenominator
  calc a.den * δ.den ^ j ≤ a.den * (2 ^ b) ^ j := Nat.mul_le_mul_left _ hp
    _ < 2 ^ b * (2 ^ b) ^ j := Nat.mul_lt_mul_of_pos_right ha (by positivity)
    _ = 2 ^ (b * (j + 1)) := by rw [Nat.mul_add, Nat.mul_one, pow_add, pow_mul]; ring

theorem grid_representation_bit_bound {a δ : ℚ} {b j : ℕ}
    (ha : a.num.natAbs.size ≤ b) (had : a.den.size ≤ b)
    (hδ : δ.num.natAbs.size ≤ b) (hδd : δ.den.size ≤ b) :
    (gridNumerator a δ j).size ≤ b + (b + 1) * j ∧
    (gridDenominator a δ j).size ≤ b * (j + 1) := by
  exact ⟨Nat.size_le.mpr (grid_numerator_bound (Nat.size_le.mp ha)
    (Nat.size_le.mp hδ) (Nat.size_le.mp hδd)),
    Nat.size_le.mpr (grid_denominator_bound (Nat.size_le.mp had) (Nat.size_le.mp hδd))⟩
end BalancedAssortments.RationalGridEncoding
