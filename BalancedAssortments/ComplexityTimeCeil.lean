import BalancedAssortments.ComplexityTimeDivision
import BalancedAssortments.KnapsackCostRational

set_option maxRecDepth 4096
namespace BalancedAssortments.ComplexityTimeCeil
open ComplexityTimeBinary ComplexityTimeDivision KnapsackCostRational

def isZero (xs : List Bool) : Bool := (compareBits xs []).1 == Ordering.eq
lemma isZero_correct (xs : List Bool) : isZero xs = true ↔ value xs = 0 := by
  have h := compareBits_correct xs []
  unfold isZero
  generalize he : (compareBits xs []).1 = o at *
  cases o <;> simp_all [comparisonMeaning, value] <;> omega

def ceilDivide (xs ds : List Bool) : List Bool × ℕ :=
  let d := divBits xs ds
  let z := compareBits d.remainder []
  if z.1 == Ordering.eq then (d.quotient,d.cost+z.2+8) else
    let inc := addCarry d.quotient [true] false
    (inc.1,d.cost+z.2+inc.2+8)

theorem ceilDivide_value (xs ds : List Bool) (hd : 0 < value ds) :
    value (ceilDivide xs ds).1 = ⌈(value xs : ℚ) / value ds⌉₊ := by
  obtain ⟨he, hr⟩ := divBits_spec xs ds hd
  have hdq : (0 : ℚ) < value ds := by exact_mod_cast hd
  have heq : (value (divBits xs ds).quotient : ℚ) * value ds +
      value (divBits xs ds).remainder = (value xs : ℚ) := by exact_mod_cast he
  by_cases hz : value (divBits xs ds).remainder = 0
  · have hc := (isZero_correct (divBits xs ds).remainder).mpr hz
    change ((compareBits (divBits xs ds).remainder []).1 == Ordering.eq) = true at hc
    simp only [ceilDivide, hc, ↓reduceIte]
    have he' : (value xs : ℚ)/value ds = (value (divBits xs ds).quotient : ℚ) := by
      apply (div_eq_iff hdq.ne').2
      simpa [hz] using heq.symm
    rw [he', Nat.ceil_natCast]
  · have hc : ¬ isZero (divBits xs ds).remainder = true := by simpa [isZero_correct] using hz
    simp only [ceilDivide, isZero] at hc ⊢
    rw [if_neg hc, addCarry_value]
    simp only [value, Bool.toNat_true, Bool.toNat_false, zero_add, add_zero, mul_zero]
    symm
    apply (Nat.ceil_eq_iff (by omega : value (divBits xs ds).quotient + 1 ≠ 0)).2
    have hp : (0 : ℚ) < value (divBits xs ds).remainder := by exact_mod_cast (Nat.pos_of_ne_zero hz)
    have hrq : (value (divBits xs ds).remainder : ℚ) < value ds := by exact_mod_cast hr
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    constructor
    · apply (lt_div_iff₀ hdq).2
      nlinarith
    · apply (div_le_iff₀ hdq).2
      nlinarith

theorem ceilDivide_length (xs ds : List Bool) :
    (ceilDivide xs ds).1.length ≤ xs.length + 2 := by
  have h := (divBits_lengths xs ds).1
  dsimp only [ceilDivide]
  split_ifs
  · change (divBits xs ds).quotient.length ≤ xs.length+2
    omega
  · rw [addCarry_length]
    simp only [List.length_cons, List.length_nil]
    omega

theorem ceilDivide_cost (xs ds : List Bool) :
    (ceilDivide xs ds).2 ≤ 128*(xs.length+ds.length+2)^2 := by
  have hd := divBits_cost xs ds
  have hl := divBits_lengths xs ds
  have hi := addCarry_cost (divBits xs ds).quotient [true] false
  have hm : max (divBits xs ds).quotient.length 1 ≤ xs.length+1 := by omega
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at hi
  have hib : (addCarry (divBits xs ds).quotient [true] false).2 ≤ 16*(xs.length+1)+1 := by omega
  dsimp only [ceilDivide]
  split_ifs <;> rw [compareBits_cost] <;> simp only [List.length_nil, Nat.max_zero]
  · nlinarith [hl.2]
  · nlinarith [hl.2]

/-- Ceiling of a rational ratio, using cross products and binary division. -/
def ceilRatio (x y : Fraction) : List Bool × ℕ :=
  let num := mulBits x.numerator y.denominator
  let den := mulBits x.denominator y.numerator
  let out := ceilDivide num.1 den.1
  (out.1,num.2+den.2+out.2+6)

theorem ceilRatio_value {x y : Fraction} (hx : x.Valid) (hy : 0 < y.decode) :
    value (ceilRatio x y).1 = ⌈x.decode / y.decode⌉₊ := by
  have hyn : 0 < value y.numerator := by
    by_contra h
    have hz : value y.numerator = 0 := by omega
    simp [Fraction.decode, hz] at hy
  have hd : 0 < value (mulBits x.denominator y.numerator).1 := by
    rw [mulBits_value]; exact Nat.mul_pos hx hyn
  rw [ceilRatio, ceilDivide_value _ _ hd]
  congr 1
  simp only [Fraction.decode, mulBits_value, Nat.cast_mul]
  field_simp

theorem ceilRatio_length {x y : Fraction} {b : ℕ} (hx : x.Width b) (hy : y.Width b) :
    (ceilRatio x y).1.length ≤ 3*b+2 := by
  have hm := mulBits_length x.numerator y.denominator
  have hh := ceilDivide_length (mulBits x.numerator y.denominator).1 (mulBits x.denominator y.numerator).1
  dsimp only [ceilRatio]
  rcases hx with ⟨hx1,hx2⟩
  rcases hy with ⟨hy1,hy2⟩
  omega

theorem ceilRatio_cost {x y : Fraction} {b : ℕ} (hx : x.Width b) (hy : y.Width b) :
    (ceilRatio x y).2 ≤ 8192*(b+1)^2 := by
  have h₁ := mulBits_cost x.numerator y.denominator
  have h₂ := mulBits_cost x.denominator y.numerator
  have l₁ := mulBits_length x.numerator y.denominator
  have l₂ := mulBits_length x.denominator y.numerator
  have hc := ceilDivide_cost (mulBits x.numerator y.denominator).1 (mulBits x.denominator y.numerator).1
  dsimp only [ceilRatio]
  nlinarith [hx.1,hx.2,hy.1,hy.2]

/-- The exact source cutoff N*ceil(N/delta), including the binary product. -/
def cutoff (ns : List Bool) (δ : Fraction) : List Bool × ℕ :=
  let count : Fraction := ⟨ns,[true]⟩
  let c := ceilRatio count δ
  let p := mulBits ns c.1
  (p.1,c.2+p.2+4)

theorem cutoff_value (ns : List Bool) {δ : Fraction} (hδ : 0 < δ.decode) :
    value (cutoff ns δ).1 = value ns * ⌈(value ns : ℚ)/δ.decode⌉₊ := by
  have hv : (⟨ns,[true]⟩ : Fraction).Valid := by norm_num [Fraction.Valid,value]
  simp only [cutoff,mulBits_value,ceilRatio_value hv hδ]
  simp [Fraction.decode,value]

theorem cutoff_cost {ns : List Bool} {δ : Fraction} {b : ℕ}
    (hn : ns.length ≤ b) (hb : 1 ≤ b) (hδ : δ.Width b) :
    (cutoff ns δ).2 ≤ 16384*(b+1)^2 := by
  have hc : (⟨ns,[true]⟩ : Fraction).Width b := ⟨hn,by simpa using hb⟩
  have h1 := ceilRatio_cost hc hδ
  have h2 := ceilRatio_length hc hδ
  have h3 := mulBits_cost ns (ceilRatio ⟨ns,[true]⟩ δ).1
  dsimp only [cutoff]
  nlinarith
end BalancedAssortments.ComplexityTimeCeil
