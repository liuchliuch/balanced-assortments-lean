import BalancedAssortments.ComplexityTimeBinary

/-! Concrete binary integer arithmetic and linear-inequality verification.
Signed integers are represented as differences of two nonnegative bit strings;
no subtraction, division, rational arithmetic, or gcd is an oracle operation. -/
namespace BalancedAssortments.ComplexityTimeVerifier
open ComplexityTimeBinary

abbrev ZBits := List Bool × List Bool

def zvalue (x : ZBits) : ℤ := (value x.1 : ℤ) - value x.2
def width (x : ZBits) : ℕ := max x.1.length x.2.length

def zzero : ZBits := ([], [])

def zadd (x y : ZBits) : ZBits × ℕ :=
  let p := addCarry x.1 y.1 false
  let n := addCarry x.2 y.2 false
  ((p.1,n.1), p.2+n.2+3)

theorem zadd_value (x y : ZBits) : zvalue (zadd x y).1 = zvalue x + zvalue y := by
  simp [zadd, zvalue, addCarry_value]
  ring

theorem zadd_width (x y : ZBits) : width (zadd x y).1 ≤ max (width x) (width y)+1 := by
  simp only [zadd, width, addCarry_length]
  omega

theorem zadd_cost (x y : ZBits) : (zadd x y).2 ≤ 32*max (width x) (width y)+5 := by
  simp only [zadd, width, addCarry_cost]
  omega

def zmul (x y : ZBits) : ZBits × ℕ :=
  let pp := mulBits x.1 y.1
  let nn := mulBits x.2 y.2
  let pn := mulBits x.1 y.2
  let np := mulBits x.2 y.1
  let p := addCarry pp.1 nn.1 false
  let n := addCarry pn.1 np.1 false
  ((p.1,n.1), pp.2+nn.2+pn.2+np.2+p.2+n.2+9)

theorem zmul_value (x y : ZBits) : zvalue (zmul x y).1 = zvalue x * zvalue y := by
  simp [zmul, zvalue, addCarry_value, mulBits_value]
  ring

theorem zmul_width (x y : ZBits) : width (zmul x y).1 ≤ 2*width x+width y+1 := by
  have hpp := mulBits_length x.1 y.1
  have hnn := mulBits_length x.2 y.2
  have hpn := mulBits_length x.1 y.2
  have hnp := mulBits_length x.2 y.1
  simp only [zmul, width, addCarry_length]
  omega

theorem zmul_cost (x y : ZBits) : (zmul x y).2 ≤ 400*(width x+width y+1)^2 := by
  have hpp := mulBits_length x.1 y.1
  have hnn := mulBits_length x.2 y.2
  have hpn := mulBits_length x.1 y.2
  have hnp := mulBits_length x.2 y.1
  have hpx : x.1.length ≤ width x := le_max_left _ _
  have hnx : x.2.length ≤ width x := le_max_right _ _
  have hpy : y.1.length ≤ width y := le_max_left _ _
  have hny : y.2.length ≤ width y := le_max_right _ _
  have hc (a b : List Bool) (ha : a.length ≤ width x) (hb : b.length ≤ width y) :
      (mulBits a b).2 ≤ 64*width x*(width x+width y+1)+1 := by
    apply (mulBits_cost a b).trans
    exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 64 ha) (by omega)) 1
  have hc1 := hc x.1 y.1 hpx hpy
  have hc2 := hc x.2 y.2 hnx hny
  have hc3 := hc x.1 y.2 hpx hny
  have hc4 := hc x.2 y.1 hnx hpy
  have hm1 : max (mulBits x.1 y.1).1.length (mulBits x.2 y.2).1.length ≤ 2*width x+width y := by omega
  have hm2 : max (mulBits x.1 y.2).1.length (mulBits x.2 y.1).1.length ≤ 2*width x+width y := by omega
  simp only [zmul, addCarry_cost]
  nlinarith

def zle (x y : ZBits) : Bool × ℕ :=
  let l := addCarry x.1 y.2 false
  let r := addCarry y.1 x.2 false
  let c := compareBits l.1 r.1
  (c.1 != Ordering.gt, l.2+r.2+c.2+3)

theorem zle_correct (x y : ZBits) : (zle x y).1 = true ↔ zvalue x ≤ zvalue y := by
  change leBits (addCarry x.1 y.2 false).1 (addCarry y.1 x.2 false).1 = true ↔ _
  rw [leBits_correct]
  simp only [addCarry_value, Bool.toNat_false, Nat.add_zero, zvalue]
  omega

theorem zle_cost (x y : ZBits) : (zle x y).2 ≤ 48*max (width x) (width y)+22 := by
  simp only [zle, addCarry_cost, compareBits_cost, addCarry_length, width]
  omega

/-- Finite dot product. The two operands of each multiplication are supplied
as a pair, so no mismatch or truncated zip is silently accepted. -/
def dot : List (ZBits × ZBits) → ZBits × ℕ
  | [] => (zzero, 1)
  | (x,y) :: rest =>
      let p := zmul x y
      let r := dot rest
      let s := zadd p.1 r.1
      (s.1, p.2+r.2+s.2+4)

theorem dot_value (xs : List (ZBits × ZBits)) :
    zvalue (dot xs).1 = (xs.map (fun p => zvalue p.1*zvalue p.2)).sum := by
  induction xs with
  | nil => simp [dot, zzero, zvalue, value]
  | cons p xs ih => simp [dot, zadd_value, zmul_value, ih]

theorem dot_width (xs : List (ZBits × ZBits)) (L : ℕ)
    (h : ∀ p ∈ xs, width p.1 ≤ L ∧ width p.2 ≤ L) :
    width (dot xs).1 ≤ 3*L+2*xs.length := by
  induction xs with
  | nil => simp [dot, zzero, width]
  | cons p xs ih =>
    have hp := h p (by simp)
    have hi := ih (fun p hp => h p (by simp [hp]))
    have hm := zmul_width p.1 p.2
    have ha := zadd_width (zmul p.1 p.2).1 (dot xs).1
    simp only [dot, List.length_cons]
    omega

theorem dot_cost (xs : List (ZBits × ZBits)) (L : ℕ)
    (h : ∀ p ∈ xs, width p.1 ≤ L ∧ width p.2 ≤ L) :
    (dot xs).2 ≤ xs.length * (1600*(L+1)^2+32*(3*L+2*xs.length+1)+20)+1 := by
  induction xs with
  | nil => simp [dot]
  | cons p xs ih =>
    have hp := h p (by simp)
    have hi := ih (fun p hp => h p (by simp [hp]))
    have hl := dot_width xs L (fun p hp => h p (by simp [hp]))
    have hmW := zmul_width p.1 p.2
    have hmC := zmul_cost p.1 p.2
    have hm : (zmul p.1 p.2).2 ≤ 1600*(L+1)^2 := by
      have hw : width p.1+width p.2+1 ≤ 2*(L+1) := by omega
      have hh := Nat.pow_le_pow_left hw 2
      nlinarith
    have ha := zadd_cost (zmul p.1 p.2).1 (dot xs).1
    have hh : max (width (zmul p.1 p.2).1) (width (dot xs).1) ≤ 3*L+2*xs.length+1 := by omega
    simp only [dot, List.length_cons]
    nlinarith

/-- Check an integer inequality against a shared-denominator certificate:
Σ A_i p_i ≤ b q. No rational division is executed by the verifier. -/
def checkRow (xs : List (ZBits × ZBits)) (b q : ZBits) : Bool × ℕ :=
  let l := dot xs
  let r := zmul b q
  let c := zle l.1 r.1
  (c.1, l.2+r.2+c.2+4)

theorem checkRow_correct (xs : List (ZBits × ZBits)) (b q : ZBits) :
    (checkRow xs b q).1 = true ↔
      (xs.map (fun p => zvalue p.1*zvalue p.2)).sum ≤ zvalue b*zvalue q := by
  simp only [checkRow, zle_correct, dot_value, zmul_value]

theorem checkRow_cost (xs : List (ZBits × ZBits)) (b q : ZBits) (L : ℕ)
    (h : ∀ p ∈ xs, width p.1 ≤ L ∧ width p.2 ≤ L)
    (hb : width b ≤ L) (hq : width q ≤ L) :
    (checkRow xs b q).2 ≤
      (xs.length+1)*(4000*(L+1)^2+128*(3*L+2*xs.length+1)+200) := by
  have hd := dot_cost xs L h
  have hdW := dot_width xs L h
  have hmW := zmul_width b q
  have hmC := zmul_cost b q
  have hm : (zmul b q).2 ≤ 1600*(L+1)^2 := by
    have hw : width b+width q+1 ≤ 2*(L+1) := by omega
    have hh := Nat.pow_le_pow_left hw 2
    nlinarith
  have hc := zle_cost (dot xs).1 (zmul b q).1
  have hw : max (width (dot xs).1) (width (zmul b q).1) ≤ 3*L+2*xs.length+1 := by omega
  simp only [checkRow]
  nlinarith

/-- Algebraic bridge from the checked integer inequality to the corresponding
rational LP row; the positive shared denominator is explicit. -/
theorem integer_check_iff_rational (xs : List (ZBits × ZBits)) (b q : ZBits)
    (hq : 0 < zvalue q) :
    (checkRow xs b q).1 = true ↔
      (xs.map (fun p => (zvalue p.1 : ℚ) * ((zvalue p.2 : ℚ)/(zvalue q : ℚ)))).sum ≤
        (zvalue b : ℚ) := by
  rw [checkRow_correct]
  have hqr : (0 : ℚ) < zvalue q := by exact_mod_cast hq
  have he : (xs.map (fun p => (zvalue p.1 : ℚ) * ((zvalue p.2 : ℚ)/(zvalue q : ℚ)))).sum =
      ((xs.map (fun p => zvalue p.1*zvalue p.2)).sum : ℤ) / (zvalue q : ℚ) := by
    induction xs with
    | nil => simp
    | cons p xs ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, add_div, ih]
      ring
  rw [he, div_le_iff₀ hqr]
  exact_mod_cast Iff.rfl

end BalancedAssortments.ComplexityTimeVerifier
