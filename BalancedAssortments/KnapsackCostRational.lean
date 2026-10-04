import BalancedAssortments.ComplexityTimeBinary

/-! Unreduced, nonnegative rational arithmetic implemented on bit lists.
Multiplication is oriented with the fresh bounded-size operand first, so the
padding of accumulated numerators/denominators grows only linearly per addition.
Costs count the actual binary primitives and constant record/list overhead.
No gcd or unit-cost rational operation occurs in these implementations. -/
namespace BalancedAssortments.KnapsackCostRational
open ComplexityTimeBinary

structure Fraction where
  numerator : List Bool
  denominator : List Bool
  deriving Repr

def Fraction.decode (x : Fraction) : ℚ := (value x.numerator : ℚ) / value x.denominator
def Fraction.Valid (x : Fraction) : Prop := 0 < value x.denominator
def Fraction.Width (x : Fraction) (b : ℕ) : Prop :=
  x.numerator.length ≤ b ∧ x.denominator.length ≤ b

def encode (x : ℚ) : Fraction := ⟨x.num.natAbs.bits, x.den.bits⟩

theorem encode_valid (x : ℚ) : (encode x).Valid := by
  simpa [Fraction.Valid, encode] using x.den_pos

theorem encode_decode {x : ℚ} (hx : 0 ≤ x) : (encode x).decode = x := by
  simp only [Fraction.decode, encode, value_bits]
  have he : (x.num.natAbs : ℚ) = x.num := by
    calc (x.num.natAbs : ℚ) = ((x.num.natAbs : ℤ) : ℚ) := by simp
         _ = (x.num : ℚ) := congrArg (fun z : ℤ => (z : ℚ))
           (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hx))
  rw [he, Rat.num_div_den]

/-- Add a fresh fraction y to an accumulated fraction x. -/
def add (x y : Fraction) : Fraction × ℕ :=
  let a := mulBits y.denominator x.numerator
  let b := mulBits y.numerator x.denominator
  let c := addCarry a.1 b.1 false
  let d := mulBits y.denominator x.denominator
  (⟨c.1, d.1⟩, a.2 + b.2 + c.2 + d.2 + 8)

theorem add_valid {x y : Fraction} (hx : x.Valid) (hy : y.Valid) : (add x y).1.Valid := by
  simp only [add, Fraction.Valid, mulBits_value]
  exact Nat.mul_pos hy hx

theorem add_decode {x y : Fraction} (hx : x.Valid) (hy : y.Valid) :
    (add x y).1.decode = x.decode + y.decode := by
  have hxq : (value x.denominator : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  have hyq : (value y.denominator : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
  simp only [add, Fraction.decode, addCarry_value, mulBits_value, Bool.toNat_false,
    Nat.add_zero, Nat.cast_add, Nat.cast_mul]
  field_simp

/-- Linear growth in the accumulated width, rather than repeated doubling. -/
theorem add_width {x y : Fraction} {a b : ℕ} (hx : x.Width a) (hy : y.Width b) :
    (add x y).1.Width (a + 2*b + 1) := by
  have h₁ := mulBits_length y.denominator x.numerator
  have h₂ := mulBits_length y.numerator x.denominator
  have h₃ := mulBits_length y.denominator x.denominator
  simp only [add, Fraction.Width, addCarry_length]
  rcases hx with ⟨hx₁,hx₂⟩
  rcases hy with ⟨hy₁,hy₂⟩
  constructor <;> omega

/-- A concrete quadratic binary-operation bound for rational addition. -/
theorem add_cost {x y : Fraction} {a b : ℕ} (hx : x.Width a) (hy : y.Width b) :
    (add x y).2 ≤ 256 * (a + b + 1)^2 := by
  have hx1 := hx.1; have hx2 := hx.2; have hy1 := hy.1; have hy2 := hy.2
  have h₁ := mulBits_cost y.denominator x.numerator
  have h₂ := mulBits_cost y.numerator x.denominator
  have h₃ := mulBits_cost y.denominator x.denominator
  have l₁ := mulBits_length y.denominator x.numerator
  have l₂ := mulBits_length y.numerator x.denominator
  have hmax : max (mulBits y.denominator x.numerator).1.length
      (mulBits y.numerator x.denominator).1.length ≤ a + 2*b := by
    rcases hx with ⟨hx₁,hx₂⟩; rcases hy with ⟨hy₁,hy₂⟩; omega
  have hm₁ : y.denominator.length * (y.denominator.length + x.numerator.length + 1) ≤
      b * (a+b+1) := Nat.mul_le_mul hy.2 (by omega)
  have hm₂ : y.numerator.length * (y.numerator.length + x.denominator.length + 1) ≤
      b * (a+b+1) := Nat.mul_le_mul hy.1 (by omega)
  have hm₃ : y.denominator.length * (y.denominator.length + x.denominator.length + 1) ≤
      b * (a+b+1) := Nat.mul_le_mul hy.2 (by omega)
  simp only [add, addCarry_cost]
  nlinarith

/-- Exact cross-multiplication comparator, with all multiplications charged. -/
def compare (x y : Fraction) : Ordering × ℕ :=
  let a := mulBits x.numerator y.denominator
  let b := mulBits y.numerator x.denominator
  let c := compareBits a.1 b.1
  (c.1, a.2 + b.2 + c.2 + 4)

def rationalMeaning (o : Ordering) (x y : ℚ) : Prop :=
  match o with
  | .lt => x < y
  | .eq => x = y
  | .gt => y < x

theorem compare_correct {x y : Fraction} (hx : x.Valid) (hy : y.Valid) :
    rationalMeaning (compare x y).1 x.decode y.decode := by
  have hxq : (0 : ℚ) < value x.denominator := by exact_mod_cast hx
  have hyq : (0 : ℚ) < value y.denominator := by exact_mod_cast hy
  have h := compareBits_correct (mulBits x.numerator y.denominator).1
    (mulBits y.numerator x.denominator).1
  simp only [mulBits_value] at h
  change rationalMeaning (compareBits (mulBits x.numerator y.denominator).1
    (mulBits y.numerator x.denominator).1).1 x.decode y.decode
  generalize ho : (compareBits (mulBits x.numerator y.denominator).1
    (mulBits y.numerator x.denominator).1).1 = o at h ⊢
  cases o <;> simp only [rationalMeaning, comparisonMeaning, Fraction.decode] at h ⊢
  · apply (div_lt_div_iff₀ hxq hyq).2
    exact_mod_cast h
  · apply (div_eq_div_iff hxq.ne' hyq.ne').2
    exact_mod_cast h
  · apply (div_lt_div_iff₀ hyq hxq).2
    exact_mod_cast h

theorem compare_cost {x y : Fraction} {b : ℕ} (hx : x.Width b) (hy : y.Width b) :
    (compare x y).2 ≤ 512 * (b + 1)^2 := by
  have hx1 := hx.1; have hx2 := hx.2; have hy1 := hy.1; have hy2 := hy.2
  have h₁ := mulBits_cost x.numerator y.denominator
  have h₂ := mulBits_cost y.numerator x.denominator
  have l₁ := mulBits_length x.numerator y.denominator
  have l₂ := mulBits_length y.numerator x.denominator
  have hm₁ : x.numerator.length * (x.numerator.length + y.denominator.length + 1) ≤
      b * (2*b+1) := Nat.mul_le_mul hx.1 (by omega)
  have hm₂ : y.numerator.length * (y.numerator.length + x.denominator.length + 1) ≤
      b * (2*b+1) := Nat.mul_le_mul hy.1 (by omega)
  have hmax : max (mulBits x.numerator y.denominator).1.length
      (mulBits y.numerator x.denominator).1.length ≤ 3*b := by omega
  simp only [compare, compareBits_cost]
  nlinarith

end BalancedAssortments.KnapsackCostRational
