import BalancedAssortments.KnapsackCostState
import BalancedAssortments.ComplexityTimeDivision

namespace BalancedAssortments.KnapsackCostRational
open ComplexityTimeBinary ComplexityTimeDivision

/-- Floor of p/θ, computed by binary cross products and long division. -/
def floorRatio (p θ : Fraction) : List Bool × ℕ :=
  let a := mulBits p.numerator θ.denominator
  let b := mulBits θ.numerator p.denominator
  let d := divBits a.1 b.1
  (d.quotient, a.2 + b.2 + d.cost + 8)

theorem floorRatio_correct {p θ : Fraction} (hp : p.Valid) (hθ : θ.Valid)
    (hθpos : 0 < θ.decode) :
    value (floorRatio p θ).1 = ⌊p.decode / θ.decode⌋₊ := by
  have hθd : (0 : ℚ) < value θ.denominator := by exact_mod_cast hθ
  have hθn : 0 < value θ.numerator := by
    have hh := (div_pos_iff_of_pos_right hθd).mp hθpos
    exact_mod_cast hh
  have hd : 0 < value (mulBits θ.numerator p.denominator).1 := by
    rw [mulBits_value]; exact Nat.mul_pos hθn hp
  have he : p.decode / θ.decode =
      ((value p.numerator * value θ.denominator : ℕ) : ℚ) /
        (value θ.numerator * value p.denominator : ℕ) := by
    simp only [Fraction.decode, Nat.cast_mul]
    field_simp
  simp only [floorRatio]
  rw [divBits_quotient _ _ hd, mulBits_value, mulBits_value, he, Nat.floor_div_eq_div]

theorem floorRatio_width {p θ : Fraction} {b : ℕ} (hp : p.Width b) (hθ : θ.Width b) :
    (floorRatio p θ).1.length ≤ 3*b := by
  have ha := mulBits_length p.numerator θ.denominator
  have hp₁ := hp.1; have hθ₂ := hθ.2
  simp only [floorRatio, divBits_lengths]
  have hh := (divBits_lengths (mulBits p.numerator θ.denominator).1
    (mulBits θ.numerator p.denominator).1).1
  omega

theorem floorRatio_cost {p θ : Fraction} {b : ℕ} (hp : p.Width b) (hθ : θ.Width b) :
    (floorRatio p θ).2 ≤ 4096 * (b+1)^2 := by
  have hp₁ := hp.1; have hp₂ := hp.2; have ht₁ := hθ.1; have ht₂ := hθ.2
  have ha := mulBits_cost p.numerator θ.denominator
  have hb := mulBits_cost θ.numerator p.denominator
  have la := mulBits_length p.numerator θ.denominator
  have lb := mulBits_length θ.numerator p.denominator
  have ld := divBits_cost (mulBits p.numerator θ.denominator).1
    (mulBits θ.numerator p.denominator).1
  have ma : p.numerator.length * (p.numerator.length + θ.denominator.length + 1) ≤
      b * (2*b+1) := Nat.mul_le_mul hp₁ (by omega)
  have mb : θ.numerator.length * (θ.numerator.length + p.denominator.length + 1) ≤
      b * (2*b+1) := Nat.mul_le_mul ht₁ (by omega)
  have md : (mulBits p.numerator θ.denominator).1.length *
      ((mulBits p.numerator θ.denominator).1.length +
        (mulBits θ.numerator p.denominator).1.length + 1) ≤ (3*b) * (6*b+1) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [floorRatio]
  nlinarith

end BalancedAssortments.KnapsackCostRational
