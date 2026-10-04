import BalancedAssortments.ComplexityTimeFractions

/-! Signed unreduced binary rational arithmetic for the exact-support evaluator.
Fresh operands are placed first in multiplication, so accumulated raw widths
increase additively rather than doubling at each straight-line addition. -/
namespace BalancedAssortments.FixedSupportCostRational
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions

abbrev Fraction := ComplexityTimeFractions.Fraction

def addFresh (x y : Fraction) : Fraction × ℕ :=
  let l := zmul (y.den,[]) x.num
  let r := zmul y.num (x.den,[])
  let s := zadd l.1 r.1
  let d := mulBits y.den x.den
  (⟨s.1,d.1⟩,l.2+r.2+s.2+d.2+8)

lemma addFresh_decode (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    decode (addFresh x y).1 = decode x+decode y := by
  have hxd : (value x.den : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  have hyd : (value y.den : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
  simp only [addFresh,decode]
  rw [zadd_value,zmul_value,zmul_value,mulBits_value]
  simp only [zvalue,value]
  push_cast
  field_simp
  <;> ring

lemma addFresh_valid (x y : Fraction) (hx : Valid x) (hy : Valid y) : Valid (addFresh x y).1 := by
  change 0 < value (mulBits y.den x.den).1
  rw [mulBits_value]
  exact Nat.mul_pos hy hx

private lemma pieces {x : Fraction} {b : ℕ} (h : ComplexityTimeFractions.width x ≤ b) :
    ComplexityTimeVerifier.width x.num ≤ b ∧ x.den.length ≤ b :=
  ⟨(le_max_left _ _).trans h,(le_max_right _ _).trans h⟩

private lemma positivePair_width (xs : List Bool) : ComplexityTimeVerifier.width (xs,[]) = xs.length := by
  simp [ComplexityTimeVerifier.width]

lemma addFresh_width {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    ComplexityTimeFractions.width (addFresh x y).1 ≤ a+2*b+2 := by
  obtain ⟨hxn,hxd⟩ := pieces hx
  obtain ⟨hyn,hyd⟩ := pieces hy
  have hl := zmul_width (y.den,[]) x.num
  have hr := zmul_width y.num (x.den,[])
  rw [positivePair_width] at hl hr
  have hs := zadd_width (zmul (y.den,[]) x.num).1 (zmul y.num (x.den,[])).1
  have hd := mulBits_length y.den x.den
  dsimp only [addFresh,ComplexityTimeFractions.width]
  apply max_le <;> omega

lemma addFresh_cost {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    (addFresh x y).2 ≤ 4096*(a+b+1)^2 := by
  obtain ⟨hxn,hxd⟩ := pieces hx
  obtain ⟨hyn,hyd⟩ := pieces hy
  have hl := zmul_cost (y.den,[]) x.num
  have hr := zmul_cost y.num (x.den,[])
  have hlw := zmul_width (y.den,[]) x.num
  have hrw := zmul_width y.num (x.den,[])
  rw [positivePair_width] at hl hr hlw hrw
  have hs := zadd_cost (zmul (y.den,[]) x.num).1 (zmul y.num (x.den,[])).1
  have hd := mulBits_cost y.den x.den
  have hmx : max (ComplexityTimeVerifier.width (zmul (y.den,[]) x.num).1)
      (ComplexityTimeVerifier.width (zmul y.num (x.den,[])).1) ≤ a+2*b+1 := by omega
  have hp1 := Nat.pow_le_pow_left (show y.den.length+ComplexityTimeVerifier.width x.num+1 ≤ a+b+1 by omega) 2
  have hp2 := Nat.pow_le_pow_left (show ComplexityTimeVerifier.width y.num+x.den.length+1 ≤ a+b+1 by omega) 2
  have hm := Nat.mul_le_mul hyd (show y.den.length+x.den.length+1 ≤ a+b+1 by omega)
  simp only [addFresh]
  nlinarith

def subtractFresh (x y : Fraction) : Fraction × ℕ :=
  let r := addFresh x (negative y)
  (r.1,r.2+2)

lemma subtractFresh_decode (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    decode (subtractFresh x y).1 = decode x-decode y := by
  simp only [subtractFresh,addFresh_decode x (negative y) hx hy,negative_decode,sub_eq_add_neg]

lemma subtractFresh_valid (x y : Fraction) (hx : Valid x) (hy : Valid y) : Valid (subtractFresh x y).1 :=
  addFresh_valid x (negative y) hx hy

lemma subtractFresh_width {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    ComplexityTimeFractions.width (subtractFresh x y).1 ≤ a+2*b+2 := by
  exact addFresh_width hx (by simpa using hy)

lemma subtractFresh_cost {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    (subtractFresh x y).2 ≤ 4096*(a+b+1)^2+2 :=
  Nat.add_le_add_right (addFresh_cost hx (by simpa using hy)) 2

def multiplyFresh (x y : Fraction) : Fraction × ℕ :=
  let num := zmul y.num x.num
  let den := mulBits y.den x.den
  (⟨num.1,den.1⟩,num.2+den.2+4)

lemma multiplyFresh_decode (x y : Fraction) : decode (multiplyFresh x y).1 = decode x*decode y := by
  simp only [multiplyFresh,decode,zmul_value,mulBits_value,Int.cast_mul,Nat.cast_mul]
  rw [mul_div_mul_comm]
  ring

lemma multiplyFresh_valid (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    Valid (multiplyFresh x y).1 := by
  change 0 < value (mulBits y.den x.den).1
  rw [mulBits_value]
  exact Nat.mul_pos hy hx

lemma multiplyFresh_width {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    ComplexityTimeFractions.width (multiplyFresh x y).1 ≤ a+2*b+1 := by
  obtain ⟨hxn,hxd⟩ := pieces hx
  obtain ⟨hyn,hyd⟩ := pieces hy
  have hn := zmul_width y.num x.num
  have hd := mulBits_length y.den x.den
  dsimp only [multiplyFresh,ComplexityTimeFractions.width]
  apply max_le <;> omega

lemma multiplyFresh_cost {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    (multiplyFresh x y).2 ≤ 1024*(a+b+1)^2 := by
  obtain ⟨hxn,hxd⟩ := pieces hx
  obtain ⟨hyn,hyd⟩ := pieces hy
  have hn := zmul_cost y.num x.num
  have hd := mulBits_cost y.den x.den
  have hp := Nat.pow_le_pow_left (show ComplexityTimeVerifier.width y.num+ComplexityTimeVerifier.width x.num+1 ≤ a+b+1 by omega) 2
  have hm := Nat.mul_le_mul hyd (show y.den.length+x.den.length+1 ≤ a+b+1 by omega)
  simp only [multiplyFresh]
  nlinarith

private lemma positivePair_value (xs : List Bool) : zvalue (xs,[]) = (value xs : ℤ) := by
  simp [zvalue,value]

/-- Exact signed comparison via integer cross-products. -/
def le (x y : Fraction) : Bool × ℕ :=
  let l := zmul (y.den,[]) x.num
  let r := zmul y.num (x.den,[])
  let c := zle l.1 r.1
  (c.1,l.2+r.2+c.2+6)

lemma le_correct (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    (le x y).1 = true ↔ decode x ≤ decode y := by
  have hxq : (0:ℚ) < value x.den := by exact_mod_cast hx
  have hyq : (0:ℚ) < value y.den := by exact_mod_cast hy
  simp only [le,zle_correct,zmul_value,positivePair_value,decode]
  rw [div_le_div_iff₀ hxq hyq]
  rw [mul_comm (value y.den : ℤ)]
  constructor <;> intro h <;> exact_mod_cast h

lemma le_cost {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    (le x y).2 ≤ 2048*(a+b+1)^2 := by
  obtain ⟨hxn,hxd⟩ := pieces hx
  obtain ⟨hyn,hyd⟩ := pieces hy
  have hl := zmul_cost (y.den,[]) x.num
  have hr := zmul_cost y.num (x.den,[])
  have hlw := zmul_width (y.den,[]) x.num
  have hrw := zmul_width y.num (x.den,[])
  rw [positivePair_width] at hl hr hlw hrw
  have hc := zle_cost (zmul (y.den,[]) x.num).1 (zmul y.num (x.den,[])).1
  have hmx : max (ComplexityTimeVerifier.width (zmul (y.den,[]) x.num).1)
      (ComplexityTimeVerifier.width (zmul y.num (x.den,[])).1) ≤ a+2*b+1 := by omega
  have hp1 := Nat.pow_le_pow_left (show y.den.length+ComplexityTimeVerifier.width x.num+1 ≤ a+b+1 by omega) 2
  have hp2 := Nat.pow_le_pow_left (show ComplexityTimeVerifier.width y.num+x.den.length+1 ≤ a+b+1 by omega) 2
  simp only [le]
  nlinarith

/-- Total reciprocal, with explicit sign comparison and binary magnitude
subtraction. Zero maps to zero, exactly as the rational field operation. -/
def reciprocal (x : Fraction) : Fraction × ℕ :=
  let c := compareBits x.num.1 x.num.2
  match c.1 with
  | .eq => (zero,c.2+4)
  | .lt => let p := reciprocalPositive (negative x); (negative p.1,c.2+p.2+6)
  | .gt => let p := reciprocalPositive x; (p.1,c.2+p.2+4)

lemma reciprocal_decode (x : Fraction) : decode (reciprocal x).1 = 1/decode x := by
  have h := compareBits_correct x.num.1 x.num.2
  cases he : (compareBits x.num.1 x.num.2).1 with
  | lt =>
    simp only [he,comparisonMeaning] at h
    have hn : 0 < zvalue (negative x).num := by change 0 < (value x.num.2 : ℤ)-value x.num.1; omega
    simp only [reciprocal,he,negative_decode,reciprocalPositive_decode (negative x) hn]
    simp
  | eq =>
    simp only [he,comparisonMeaning] at h
    have hn : zvalue x.num = 0 := by unfold zvalue; omega
    simp only [reciprocal,he]
    rw [zero_decode]
    have hx : decode x = 0 := by simp [decode,hn]
    rw [hx]
    simp
  | gt =>
    simp only [he,comparisonMeaning] at h
    have hn : 0 < zvalue x.num := by unfold zvalue; omega
    simp only [reciprocal,he,reciprocalPositive_decode x hn]

lemma reciprocal_valid (x : Fraction) : Valid (reciprocal x).1 := by
  have h := compareBits_correct x.num.1 x.num.2
  cases he : (compareBits x.num.1 x.num.2).1 with
  | lt =>
    simp only [he,comparisonMeaning] at h
    have hn : 0 < zvalue (negative x).num := by change 0 < (value x.num.2 : ℤ)-value x.num.1; omega
    simpa only [reciprocal,he,negative_valid] using reciprocalPositive_valid (negative x) hn
  | eq => simpa only [reciprocal,he] using zero_valid
  | gt =>
    simp only [he,comparisonMeaning] at h
    have hn : 0 < zvalue x.num := by unfold zvalue; omega
    simpa only [reciprocal,he] using reciprocalPositive_valid x hn

lemma reciprocal_width_max (x : Fraction) :
    ComplexityTimeFractions.width (reciprocal x).1 ≤ max (ComplexityTimeFractions.width x) 1 := by
  cases he : (compareBits x.num.1 x.num.2).1 with
  | lt =>
    simp only [reciprocal,he,negative_width]
    exact (reciprocalPositive_width (negative x)).trans (by simp)
  | eq => simp only [reciprocal,he,zero_width]; exact le_max_right _ _
  | gt =>
    simp only [reciprocal,he]
    exact (reciprocalPositive_width x).trans (le_max_left _ _)

lemma valid_width_positive (x : Fraction) (hx : Valid x) : 1 ≤ ComplexityTimeFractions.width x := by
  have hn : x.den ≠ [] := by intro he; simp [Valid,he,value] at hx
  have hl := List.length_pos_iff.mpr hn
  have hm : x.den.length ≤ ComplexityTimeFractions.width x := le_max_right _ _
  omega

lemma reciprocal_width (x : Fraction) (hx : Valid x) :
    ComplexityTimeFractions.width (reciprocal x).1 ≤ ComplexityTimeFractions.width x := by
  simpa [max_eq_left (valid_width_positive x hx)] using reciprocal_width_max x

lemma reciprocal_cost (x : Fraction) : (reciprocal x).2 ≤ 64*ComplexityTimeFractions.width x+32 := by
  have hc := compareBits_cost x.num.1 x.num.2
  have hm : max x.num.1.length x.num.2.length ≤ ComplexityTimeFractions.width x := le_max_left _ _
  have hp := reciprocalPositive_cost x
  have hn := reciprocalPositive_cost (negative x)
  rw [negative_width] at hn
  cases he : (compareBits x.num.1 x.num.2).1 <;> simp only [reciprocal,he] <;> omega

def divideFresh (x y : Fraction) : Fraction × ℕ :=
  let r := reciprocal y
  let p := multiplyFresh x r.1
  (p.1,r.2+p.2+2)

lemma divideFresh_decode (x y : Fraction) : decode (divideFresh x y).1 = decode x/decode y := by
  simp only [divideFresh,multiplyFresh_decode,reciprocal_decode]
  ring

lemma divideFresh_valid (x y : Fraction) (hx : Valid x) (_hy : Valid y) : Valid (divideFresh x y).1 :=
  multiplyFresh_valid x (reciprocal y).1 hx (reciprocal_valid y)

lemma divideFresh_width {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    ComplexityTimeFractions.width (divideFresh x y).1 ≤ a+2*b+3 := by
  have hr : ComplexityTimeFractions.width (reciprocal y).1 ≤ b+1 :=
    (reciprocal_width_max y).trans (by omega)
  have hp := multiplyFresh_width hx hr
  convert hp using 1 <;> omega

lemma divideFresh_width_valid {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) (hyv : Valid y) :
    ComplexityTimeFractions.width (divideFresh x y).1 ≤ a+2*b+1 :=
  multiplyFresh_width hx ((reciprocal_width y hyv).trans hy)

lemma divideFresh_cost {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    (divideFresh x y).2 ≤ 1024*(a+b+2)^2+64*b+34 := by
  have hr : ComplexityTimeFractions.width (reciprocal y).1 ≤ b+1 :=
    (reciprocal_width_max y).trans (by omega)
  have hc := reciprocal_cost y
  have hp := multiplyFresh_cost hx hr
  dsimp only [divideFresh]
  rw [show a+(b+1)+1 = a+b+2 by omega] at hp
  omega

def compare (x y : Fraction) : Ordering × ℕ :=
  let l := le x y
  let r := le y x
  (if l.1 then (if r.1 then .eq else .lt) else .gt,l.2+r.2+6)

def Comparison (o : Ordering) (x y : ℚ) : Prop :=
  match o with
  | .lt => x<y
  | .eq => x=y
  | .gt => y<x

lemma compare_correct (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    Comparison (compare x y).1 (decode x) (decode y) := by
  have hl := le_correct x y hx hy
  have hr := le_correct y x hy hx
  dsimp only [compare]
  split_ifs with hle hge
  · exact le_antisymm (hl.1 hle) (hr.1 hge)
  · exact lt_of_not_ge (fun h => hge (hr.2 h))
  · exact lt_of_not_ge (fun h => hle (hl.2 h))

lemma compare_cost {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    (compare x y).2 ≤ 4096*(a+b+1)^2+6 := by
  have hl := le_cost hx hy
  have hr := le_cost hy hx
  rw [Nat.add_comm b a] at hr
  dsimp only [compare]
  omega

def negate (x : Fraction) : Fraction × ℕ := (negative x,2)
lemma negate_decode (x : Fraction) : decode (negate x).1 = -decode x := negative_decode x
lemma negate_valid (x : Fraction) (hx : Valid x) : Valid (negate x).1 := hx
lemma negate_width (x : Fraction) : ComplexityTimeFractions.width (negate x).1 = ComplexityTimeFractions.width x := negative_width x
lemma negate_cost (x : Fraction) : (negate x).2 = 2 := rfl

def minimum (x y : Fraction) : Fraction × ℕ :=
  let c := le x y
  (if c.1 then x else y,c.2+2)

def maximum (x y : Fraction) : Fraction × ℕ :=
  let c := le x y
  (if c.1 then y else x,c.2+2)

lemma minimum_decode (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    decode (minimum x y).1 = min (decode x) (decode y) := by
  by_cases h : (le x y).1 = true
  · simp only [minimum,h,↓reduceIte,min_eq_left ((le_correct x y hx hy).1 h)]
  · have hh : decode y ≤ decode x := (lt_of_not_ge (fun he => h ((le_correct x y hx hy).2 he))).le
    simp [minimum,h,min_eq_right hh]

lemma maximum_decode (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    decode (maximum x y).1 = max (decode x) (decode y) := by
  by_cases h : (le x y).1 = true
  · simp only [maximum,h,↓reduceIte,max_eq_right ((le_correct x y hx hy).1 h)]
  · have hh : decode y ≤ decode x := (lt_of_not_ge (fun he => h ((le_correct x y hx hy).2 he))).le
    simp [maximum,h,max_eq_left hh]

lemma minimum_valid (x y : Fraction) (hx : Valid x) (hy : Valid y) : Valid (minimum x y).1 := by
  dsimp only [minimum]
  split_ifs <;> assumption
lemma maximum_valid (x y : Fraction) (hx : Valid x) (hy : Valid y) : Valid (maximum x y).1 := by
  dsimp only [maximum]
  split_ifs <;> assumption

lemma minimum_width (x y : Fraction) : ComplexityTimeFractions.width (minimum x y).1 ≤
    max (ComplexityTimeFractions.width x) (ComplexityTimeFractions.width y) := by
  dsimp only [minimum]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _
lemma maximum_width (x y : Fraction) : ComplexityTimeFractions.width (maximum x y).1 ≤
    max (ComplexityTimeFractions.width x) (ComplexityTimeFractions.width y) := by
  dsimp only [maximum]
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _

lemma minimum_cost {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    (minimum x y).2 ≤ 2048*(a+b+1)^2+2 := Nat.add_le_add_right (le_cost hx hy) 2
lemma maximum_cost {x y : Fraction} {a b : ℕ}
    (hx : ComplexityTimeFractions.width x ≤ a) (hy : ComplexityTimeFractions.width y ≤ b) :
    (maximum x y).2 ≤ 2048*(a+b+1)^2+2 := Nat.add_le_add_right (le_cost hx hy) 2

end BalancedAssortments.FixedSupportCostRational
