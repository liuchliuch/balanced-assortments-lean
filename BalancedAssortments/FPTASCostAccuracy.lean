import BalancedAssortments.FPTASCostGridFuel

/-! The epsilon/10 conversion is itself binary, rather than a free rational input
preprocessing step. -/
namespace BalancedAssortments.FPTASCostSeeds
open ComplexityTimeBinary KnapsackCostRational FPTASCostGrid

def ten : Fraction := ⟨[false,true,false,true],[true]⟩
lemma ten_valid : ten.Valid := by norm_num [ten, Fraction.Valid, value]
lemma ten_decode : ten.decode = 10 := by norm_num [ten, Fraction.decode, value]
lemma ten_width : ten.Width 4 := by norm_num [ten, Fraction.Width]

def accuracyFraction (epsilon : Fraction) : Fraction × ℕ := divideFresh epsilon ten

lemma accuracyFraction_decode (epsilon : Fraction) :
    (accuracyFraction epsilon).1.decode = epsilon.decode/10 := by
  simp only [accuracyFraction, divideFresh_decode, ten_decode]

lemma accuracyFraction_valid {epsilon : Fraction} (he : epsilon.Valid) :
    (accuracyFraction epsilon).1.Valid := divideFresh_valid he (by rw [ten_decode]; norm_num)

lemma accuracyFraction_positive {epsilon : Fraction} (he : 0 < epsilon.decode) :
    0 < (accuracyFraction epsilon).1.decode := by rw [accuracyFraction_decode]; positivity

lemma accuracyFraction_width {epsilon : Fraction} {b : ℕ} (he : epsilon.Width b) :
    (accuracyFraction epsilon).1.Width (b+8) := by
  simpa using divideFresh_width he ten_width

lemma accuracyFraction_cost {epsilon : Fraction} {b : ℕ} (he : epsilon.Width b) :
    (accuracyFraction epsilon).2 ≤ 256*(b+5)^2+8 := by
  simpa using divideFresh_cost he ten_width

/-- The actual computed loop quota is at most 10/epsilon+1, so allowing unary
accuracy quota tokens is fully polynomial in the required accuracy parameter. -/
theorem actual_accuracy_quota_bound (epsilon : Fraction) (he : epsilon.Valid)
    (hepos : 0 < epsilon.decode) :
    (value (reciprocalCeilingBits (accuracyFraction epsilon).1).1 : ℚ) ≤
      10/epsilon.decode+1 := by
  have h := reciprocalCeilingBits_upper (accuracyFraction epsilon).1
    (accuracyFraction_valid he) (accuracyFraction_positive hepos)
  rw [accuracyFraction_decode] at h
  have heq : 1/(epsilon.decode/10) = 10/epsilon.decode := by field_simp
  rwa [heq] at h

end BalancedAssortments.FPTASCostSeeds
