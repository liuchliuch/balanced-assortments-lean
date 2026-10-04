import BalancedAssortments.ComplexityTimeSourceParsing
import BalancedAssortments.FPTASCostInputSeeds

/-! Explicit rejection of illegal decoded source instances. No magnitude is
converted to a free loop bound; product count is computed from the parsed list. -/
namespace BalancedAssortments.ComplexityTimeSourceParsing
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions ComplexityTimeSourceRows
open ComplexityTimeSourcePipeline

def bitsPositive (xs : List Bool) : Bool × ℕ :=
  let c := compareBits [] xs
  (c.1 == Ordering.lt,c.2+2)

theorem bitsPositive_correct (xs : List Bool) : (bitsPositive xs).1 = true ↔ 0 < value xs := by
  have h := compareBits_correct [] xs
  cases he : (compareBits [] xs).1 <;> simp_all [bitsPositive,comparisonMeaning,value] <;> omega

def bitsLE (xs ys : List Bool) : Bool × ℕ :=
  let c := compareBits xs ys
  (c.1 != Ordering.gt,c.2+2)

theorem bitsLE_correct (xs ys : List Bool) : (bitsLE xs ys).1 = true ↔ value xs ≤ value ys :=
  leBits_correct xs ys

def bitsEQ (xs ys : List Bool) : Bool × ℕ :=
  let c := compareBits xs ys
  (c.1 == Ordering.eq,c.2+2)

theorem bitsEQ_correct (xs ys : List Bool) : (bitsEQ xs ys).1 = true ↔ value xs = value ys := by
  have h := compareBits_correct xs ys
  cases he : (compareBits xs ys).1 <;> simp_all [bitsEQ,comparisonMeaning] <;> omega

def integerPositive (z : ZBits) : Bool × ℕ :=
  let c := zle z zzero
  (!c.1,c.2+2)

theorem integerPositive_correct (z : ZBits) : (integerPositive z).1 = true ↔ 0 < zvalue z := by
  have h := zle_correct z zzero
  have hz : zvalue zzero = 0 := by simp [zvalue,zzero,value]
  rw [hz] at h
  cases he : (zle z zzero).1 <;> simp_all [integerPositive] <;> omega

def fractionPositive (x : Fraction) : Bool × ℕ :=
  let d := bitsPositive x.den
  let p := integerPositive x.num
  (d.1 && p.1,d.2+p.2+4)

theorem fractionPositive_correct (x : Fraction) :
    (fractionPositive x).1 = true ↔ Valid x ∧ 0 < decode x := by
  simp only [fractionPositive,Bool.and_eq_true,bitsPositive_correct,integerPositive_correct]
  constructor
  · rintro ⟨hd,hn⟩
    refine ⟨hd,?_⟩
    exact div_pos (by exact_mod_cast hn) (by exact_mod_cast hd)
  · rintro ⟨hd,hv⟩
    exact ⟨hd,positive_num x hd hv⟩

def alphaUpper (x : Fraction) : Bool × ℕ := zle x.num (x.den,[])

theorem alphaUpper_correct (x : Fraction) (hd : Valid x) :
    (alphaUpper x).1 = true ↔ decode x ≤ 1 := by
  rw [alphaUpper,zle_correct]
  have hdp : (0:ℚ) < value x.den := by exact_mod_cast hd
  unfold decode
  rw [div_le_iff₀ hdp]
  simp only [zvalue,value,Nat.cast_zero,sub_zero,one_mul]
  exact_mod_cast Iff.rfl

def validateProducts : List (Fraction × Fraction) → Bool × ℕ
  | [] => (true,1)
  | (r,v)::xs =>
      let a := fractionPositive r
      let b := fractionPositive v
      let tail := validateProducts xs
      (a.1 && b.1 && tail.1,a.2+b.2+tail.2+8)

theorem validateProducts_correct (xs : List (Fraction × Fraction)) :
    (validateProducts xs).1 = true ↔
      ∀ rv ∈ xs, (Valid rv.1 ∧ 0 < decode rv.1) ∧ (Valid rv.2 ∧ 0 < decode rv.2) := by
  induction xs with
  | nil => simp [validateProducts]
  | cons rv xs ih => cases rv; simp [validateProducts,fractionPositive_correct,ih,and_assoc]

def LegalSource (s : Source) : Prop :=
  value s.declaredCount = s.products.length ∧ 0 < s.products.length ∧
  0 < value s.capacity ∧ value s.capacity ≤ s.products.length ∧
  (Valid s.alpha ∧ 0 < decode s.alpha) ∧ decode s.alpha ≤ 1 ∧ Valid s.target ∧
  ∀ rv ∈ s.products, (Valid rv.1 ∧ 0 < decode rv.1) ∧ (Valid rv.2 ∧ 0 < decode rv.2)

/-- All source-domain checks are executed. The target's sign is unrestricted. -/
def validateSource (s : Source) : Bool × ℕ :=
  let count := FPTASCostSeeds.countBits s.products
  let dimension := bitsEQ s.declaredCount count.1
  let nonempty := bitsPositive count.1
  let kpos := bitsPositive s.capacity
  let krange := bitsLE s.capacity count.1
  let apos := fractionPositive s.alpha
  let aupper := alphaUpper s.alpha
  let hvalid := bitsPositive s.target.den
  let products := validateProducts s.products
  (dimension.1 && nonempty.1 && kpos.1 && krange.1 && apos.1 && aupper.1 && hvalid.1 && products.1,
    count.2+dimension.2+nonempty.2+kpos.2+krange.2+apos.2+aupper.2+hvalid.2+products.2+24)

theorem validateSource_correct (s : Source) : (validateSource s).1 = true ↔ LegalSource s := by
  simp only [validateSource,Bool.and_eq_true,bitsEQ_correct,bitsPositive_correct,bitsLE_correct,
    FPTASCostSeeds.countBits_value,fractionPositive_correct,validateProducts_correct]
  unfold LegalSource
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨hd,hn⟩,hk⟩,hkr⟩,ha⟩,hau⟩,hh⟩,hp⟩
    exact ⟨hd,hn,hk,hkr,ha,(alphaUpper_correct s.alpha ha.1).mp hau,hh,hp⟩
  · rintro ⟨hd,hn,hk,hkr,ha,hau,hh,hp⟩
    exact ⟨⟨⟨⟨⟨⟨⟨hd,hn⟩,hk⟩,hkr⟩,ha⟩,(alphaUpper_correct s.alpha ha.1).mpr hau⟩,hh⟩,hp⟩

/-- Certificates are validated against the actual parsed source dimension. -/
def validateCertificate (s : Source) (c : Certificate) : Bool × ℕ :=
  let d := sameLength s.products c.numerators
  let m := sameLength c.mask c.numerators
  let q := integerPositive c.denominator
  (d.1 && m.1 && q.1,d.2+m.2+q.2+8)

theorem validateCertificate_correct (s : Source) (c : Certificate) :
    (validateCertificate s c).1 = true ↔
      c.numerators.length = s.products.length ∧ c.mask.length = c.numerators.length ∧ 0 < zvalue c.denominator := by
  simp only [validateCertificate,Bool.and_eq_true,sameLength_correct,integerPositive_correct]
  omega

end BalancedAssortments.ComplexityTimeSourceParsing
