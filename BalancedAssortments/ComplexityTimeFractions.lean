import BalancedAssortments.ComplexityTimeVerifier
import BalancedAssortments.DecompositionCostBinary

/-! Division-free raw signed-fraction arithmetic for source-row construction.
Denominators remain unreduced; normalization and gcd are unnecessary. -/
namespace BalancedAssortments.ComplexityTimeFractions
open ComplexityTimeBinary ComplexityTimeVerifier Decomposition.CostBinary

structure Fraction where
  num : ZBits
  den : List Bool
  deriving DecidableEq

def decode (x : Fraction) : ℚ := (zvalue x.num : ℚ)/(value x.den : ℚ)
def Valid (x : Fraction) : Prop := 0 < value x.den
def width (x : Fraction) : ℕ := max (ComplexityTimeVerifier.width x.num) x.den.length

def zero : Fraction := ⟨([],[]),[true]⟩
def one : Fraction := ⟨([true],[]),[true]⟩
def negative (x : Fraction) : Fraction := ⟨(x.num.2,x.num.1),x.den⟩

@[simp] theorem zero_decode : decode zero = 0 := by simp [decode,zero,zvalue,value]
@[simp] theorem one_decode : decode one = 1 := by simp [decode,one,zvalue,value]
@[simp] theorem zero_valid : Valid zero := by norm_num [Valid,zero,value]
@[simp] theorem one_valid : Valid one := by norm_num [Valid,one,value]
@[simp] theorem zero_width : width zero = 1 := by rfl
@[simp] theorem one_width : width one = 1 := by rfl

@[simp] theorem negative_decode (x : Fraction) : decode (negative x) = -decode x := by
  simp [decode,negative,zvalue]
  ring
@[simp] theorem negative_valid (x : Fraction) : Valid (negative x) ↔ Valid x := Iff.rfl
@[simp] theorem negative_width (x : Fraction) : width (negative x) = width x := by
  simp [negative,width,ComplexityTimeVerifier.width,max_comm]

/-- Raw subtraction uses three schoolbook products and a signed addition. -/
def subtract (x y : Fraction) : Fraction × ℕ :=
  let l := zmul x.num (y.den,[])
  let r := zmul y.num (x.den,[])
  let n := zadd l.1 (r.1.2,r.1.1)
  let d := mulBits x.den y.den
  (⟨n.1,d.1⟩,l.2+r.2+n.2+d.2+8)

theorem subtract_decode (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    decode (subtract x y).1 = decode x-decode y := by
  have hxd : (value x.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  have hyd : (value y.den : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
  have he (z : ZBits) : zvalue (z.2,z.1) = -zvalue z := by simp [zvalue] <;> ring
  simp only [subtract,decode,zadd_value,he,zmul_value,mulBits_value]
  simp only [zvalue,value]
  push_cast
  field_simp
  <;> ring

theorem subtract_valid (x y : Fraction) (hx : Valid x) (hy : Valid y) : Valid (subtract x y).1 := by
  change 0 < value (mulBits x.den y.den).1
  rw [mulBits_value]
  exact Nat.mul_pos hx hy

theorem subtract_width (x y : Fraction) (L : ℕ) (hx : width x ≤ L) (hy : width y ≤ L) :
    width (subtract x y).1 ≤ 3*L+2 := by
  have hxn : ComplexityTimeVerifier.width x.num ≤ L := (le_max_left _ _).trans hx
  have hyn : ComplexityTimeVerifier.width y.num ≤ L := (le_max_left _ _).trans hy
  have hxd : x.den.length ≤ L := (le_max_right _ _).trans hx
  have hyd : y.den.length ≤ L := (le_max_right _ _).trans hy
  have he (d : List Bool) : ComplexityTimeVerifier.width (d,[]) = d.length := by
    simp [ComplexityTimeVerifier.width]
  have hs (z : ZBits) : ComplexityTimeVerifier.width (z.2,z.1) = ComplexityTimeVerifier.width z := by
    simp [ComplexityTimeVerifier.width,max_comm]
  have hl := zmul_width x.num (y.den,[])
  have hr := zmul_width y.num (x.den,[])
  rw [he] at hl hr
  have hll : ComplexityTimeVerifier.width (zmul x.num (y.den,[])).1 ≤ 3*L+1 := by omega
  have hrr : ComplexityTimeVerifier.width (zmul y.num (x.den,[])).1 ≤ 3*L+1 := by omega
  have hn := zadd_width (zmul x.num (y.den,[])).1
    ((zmul y.num (x.den,[])).1.2,(zmul y.num (x.den,[])).1.1)
  rw [hs] at hn
  have hmax := max_le hll hrr
  have hd := mulBits_length x.den y.den
  change max (ComplexityTimeVerifier.width (zadd (zmul x.num (y.den,[])).1
    ((zmul y.num (x.den,[])).1.2,(zmul y.num (x.den,[])).1.1)).1)
    (mulBits x.den y.den).1.length ≤ _
  apply max_le <;> omega

theorem subtract_cost (x y : Fraction) (L : ℕ) (hx : width x ≤ L) (hy : width y ≤ L) :
    (subtract x y).2 ≤ 4000*(L+1)^2 := by
  have hxn : ComplexityTimeVerifier.width x.num ≤ L := (le_max_left _ _).trans hx
  have hyn : ComplexityTimeVerifier.width y.num ≤ L := (le_max_left _ _).trans hy
  have hxd : x.den.length ≤ L := (le_max_right _ _).trans hx
  have hyd : y.den.length ≤ L := (le_max_right _ _).trans hy
  have hl := zmul_cost x.num (y.den,[])
  have hr := zmul_cost y.num (x.den,[])
  have hlw := zmul_width x.num (y.den,[])
  have hrw := zmul_width y.num (x.den,[])
  have hn := zadd_cost (zmul x.num (y.den,[])).1
    ((zmul y.num (x.den,[])).1.2,(zmul y.num (x.den,[])).1.1)
  have hd := mulBits_cost x.den y.den
  simp only [ComplexityTimeVerifier.width,List.length_nil,Nat.max_zero] at hl hr hlw hrw hn hxn hyn
  have hsq1 := Nat.pow_le_pow_left (show max x.num.1.length x.num.2.length+y.den.length+1 ≤ 2*(L+1) by omega) 2
  have hsq2 := Nat.pow_le_pow_left (show max y.num.1.length y.num.2.length+x.den.length+1 ≤ 2*(L+1) by omega) 2
  have hm : max (max (zmul x.num (y.den,[])).1.1.length (zmul x.num (y.den,[])).1.2.length)
      (max (zmul y.num (x.den,[])).1.2.length (zmul y.num (x.den,[])).1.1.length) ≤ 3*L+1 := by omega
  simp only [subtract]
  nlinarith [Nat.mul_self_le_mul_self hxd]

/-- Positive reciprocal computes the numerator magnitude using the explicit
ripple-borrow subtractor; the old denominator becomes the new numerator. -/
def reciprocalPositive (x : Fraction) : Fraction × ℕ :=
  let n := subBits x.num.1 x.num.2
  (⟨(x.den,[]),n.1⟩,n.2+4)

theorem reciprocalPositive_decode (x : Fraction) (hx : 0 < zvalue x.num) :
    decode (reciprocalPositive x).1 = 1/decode x := by
  have hle : value x.num.2 ≤ value x.num.1 := by unfold zvalue at hx; omega
  have hn : ((value x.num.1-value x.num.2 : ℕ) : ℚ) = (zvalue x.num : ℚ) := by
    simp only [zvalue,Int.cast_sub,Int.cast_natCast,Nat.cast_sub hle]
  simp only [reciprocalPositive,decode,zvalue,value,Int.sub_zero,Int.cast_natCast,subBits_value]
  rw [Nat.cast_sub hle]
  simp only [Int.cast_sub,Int.cast_natCast]
  rw [one_div_div]
  simp

theorem reciprocalPositive_valid (x : Fraction) (hx : 0 < zvalue x.num) :
    Valid (reciprocalPositive x).1 := by
  simp only [Valid,reciprocalPositive,subBits_value]
  unfold zvalue at hx
  omega

theorem reciprocalPositive_width (x : Fraction) : width (reciprocalPositive x).1 ≤ width x := by
  have h := subBits_length x.num.1 x.num.2
  simp only [reciprocalPositive,width,ComplexityTimeVerifier.width,List.length_nil,Nat.max_zero]
  omega

theorem reciprocalPositive_cost (x : Fraction) : (reciprocalPositive x).2 ≤ 16*width x+6 := by
  simp only [reciprocalPositive,subBits_cost,width,ComplexityTimeVerifier.width]
  omega

end BalancedAssortments.ComplexityTimeFractions
