import BalancedAssortments.FPTASCostGrid

/-! Concrete bit/list scalar primitives needed to form the FPTAS's outer seeds:
reciprocal/division and finite min/max. All costs include binary comparisons. -/
namespace BalancedAssortments.FPTASCostSeeds
open ComplexityTimeBinary KnapsackCostRational FPTASCostGrid

def reciprocal (x : Fraction) : Fraction := ⟨x.denominator, x.numerator⟩

lemma reciprocal_decode (x : Fraction) : (reciprocal x).decode = x.decode⁻¹ := by
  simp [reciprocal, Fraction.decode, inv_div]

lemma reciprocal_valid {x : Fraction} (hpos : 0 < x.decode) : (reciprocal x).Valid := by
  change 0 < value x.numerator
  have hn : 0 ≤ (value x.numerator : ℚ) := by positivity
  have hd : 0 ≤ (value x.denominator : ℚ) := by positivity
  have hp : 0 < (value x.numerator : ℚ) := by
    by_contra h
    have he : (value x.numerator : ℚ) = 0 := le_antisymm (le_of_not_gt h) hn
    simp [Fraction.decode, he] at hpos
  exact_mod_cast hp

def divideFresh (x y : Fraction) : Fraction × ℕ :=
  let out := multiplyFresh x (reciprocal y)
  (out.1, out.2+2)

lemma divideFresh_decode (x y : Fraction) : (divideFresh x y).1.decode = x.decode / y.decode := by
  simp only [divideFresh, multiplyFresh_decode, reciprocal_decode, div_eq_mul_inv]

lemma divideFresh_valid {x y : Fraction} (hx : x.Valid) (hy : 0 < y.decode) :
    (divideFresh x y).1.Valid := multiplyFresh_valid hx (reciprocal_valid hy)

lemma divideFresh_width {x y : Fraction} {a b : ℕ} (hx : x.Width a) (hy : y.Width b) :
    (divideFresh x y).1.Width (a+2*b) := multiplyFresh_width hx ⟨hy.2,hy.1⟩

lemma divideFresh_cost {x y : Fraction} {a b : ℕ} (hx : x.Width a) (hy : y.Width b) :
    (divideFresh x y).2 ≤ 256*(a+b+1)^2+8 := by
  exact Nat.add_le_add_right (multiplyFresh_cost hx ⟨hy.2,hy.1⟩) 2

/-- Select an existing representation, avoiding any normalization work. -/
def choose (small : Bool) (x y : Fraction) : Fraction × ℕ :=
  let cmp := compare x y
  (if (if small then cmp.1 = .gt else cmp.1 = .lt) then y else x, cmp.2+6)

def extremum (small : Bool) (a b : ℚ) : ℚ := if small then min a b else max a b

lemma choose_decode (small : Bool) {x y : Fraction} (hx : x.Valid) (hy : y.Valid) :
    (choose small x y).1.decode = extremum small x.decode y.decode := by
  have h := compare_correct hx hy
  cases small <;> cases he : (compare x y).1 <;>
    simp only [he, rationalMeaning] at h <;>
    simp [choose, he, extremum, min_eq_left, min_eq_right, max_eq_left, max_eq_right,
      le_of_lt, le_of_eq, h, h.le, h.symm.le]

lemma choose_valid (small : Bool) {x y : Fraction} (hx : x.Valid) (hy : y.Valid) :
    (choose small x y).1.Valid := by
  cases small <;> dsimp [choose] <;> split_ifs <;> assumption

lemma choose_width (small : Bool) {x y : Fraction} {b : ℕ} (hx : x.Width b) (hy : y.Width b) :
    (choose small x y).1.Width b := by
  cases small <;> dsimp [choose] <;> split_ifs <;> assumption

lemma choose_cost (small : Bool) {x y : Fraction} {b : ℕ} (hx : x.Width b) (hy : y.Width b) :
    (choose small x y).2 ≤ 512*(b+1)^2+6 := Nat.add_le_add_right (compare_cost hx hy) 6

def foldExtreme (small : Bool) : Fraction → List Fraction → Fraction × ℕ
  | seed, [] => (seed, 1)
  | seed, x::xs =>
      let picked := choose small seed x
      let rest := foldExtreme small picked.1 xs
      (rest.1, picked.2+rest.2+4)

lemma foldExtreme_decode (small : Bool) (seed : Fraction) (xs : List Fraction)
    (hs : seed.Valid) (hx : ∀ x ∈ xs, x.Valid) :
    (foldExtreme small seed xs).1.decode =
      (xs.map Fraction.decode).foldl (extremum small) seed.decode := by
  induction xs generalizing seed with
  | nil => rfl
  | cons x xs ih =>
    have hp := choose_valid small hs (hx x (by simp))
    have hi := ih (choose small seed x).1 hp (fun y hy => hx y (by simp [hy]))
    simpa only [foldExtreme, List.map_cons, List.foldl_cons, choose_decode small hs (hx x (by simp))] using hi

lemma foldExtreme_valid (small : Bool) (seed : Fraction) (xs : List Fraction)
    (hs : seed.Valid) (hx : ∀ x ∈ xs, x.Valid) : (foldExtreme small seed xs).1.Valid := by
  induction xs generalizing seed with
  | nil => exact hs
  | cons x xs ih =>
    exact ih _ (choose_valid small hs (hx x (by simp)))
      (fun y hy => hx y (by simp [hy]))

lemma foldExtreme_width (small : Bool) (seed : Fraction) (xs : List Fraction) {b : ℕ}
    (hs : seed.Width b) (hx : ∀ x ∈ xs, x.Width b) : (foldExtreme small seed xs).1.Width b := by
  induction xs generalizing seed with
  | nil => exact hs
  | cons x xs ih =>
    exact ih _ (choose_width small hs (hx x (by simp)))
      (fun y hy => hx y (by simp [hy]))

/-- Exact finite extrema have a linear number of polynomial binary comparisons. -/
theorem foldExtreme_cost (small : Bool) (seed : Fraction) (xs : List Fraction) {b : ℕ}
    (hs : seed.Width b) (hx : ∀ x ∈ xs, x.Width b) :
    (foldExtreme small seed xs).2 ≤ xs.length*(512*(b+1)^2+10)+1 := by
  induction xs generalizing seed with
  | nil => simp [foldExtreme]
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have hp := choose_cost small hs hxx
    have hi := ih _ (choose_width small hs hxx) (fun y hy => hx y (by simp [hy]))
    simp only [foldExtreme, List.length_cons]
    rw [Nat.succ_mul]
    omega

def one : Fraction := ⟨[true],[true]⟩
lemma one_valid : one.Valid := by norm_num [one, Fraction.Valid, value]
lemma one_decode : one.decode = 1 := by norm_num [one, Fraction.decode, value]
lemma one_width : one.Width 1 := by simp [one, Fraction.Width]
lemma decode_nonnegative (x : Fraction) : 0 ≤ x.decode := by unfold Fraction.decode; positivity

/-- Bit-level construction of one singleton revenue r*v/(1+v). -/
def singletonRevenue (r v : Fraction) : Fraction × ℕ :=
  let numerator := multiplyFresh r v
  let denominator := KnapsackCostRational.add one v
  let out := divideFresh numerator.1 denominator.1
  (out.1, numerator.2+denominator.2+out.2+8)

lemma singletonRevenue_decode {r v : Fraction} (hv : v.Valid) :
    (singletonRevenue r v).1.decode = r.decode*v.decode/(1+v.decode) := by
  simp only [singletonRevenue, divideFresh_decode, multiplyFresh_decode,
    add_decode one_valid hv, one_decode]

lemma singletonRevenue_valid {r v : Fraction} (hr : r.Valid) (hv : v.Valid) :
    (singletonRevenue r v).1.Valid := by
  apply divideFresh_valid (multiplyFresh_valid hr hv)
  rw [add_decode one_valid hv, one_decode]
  have := decode_nonnegative v
  linarith

lemma singletonRevenue_width {r v : Fraction} {b : ℕ} (hr : r.Width b) (hv : v.Width b) :
    (singletonRevenue r v).1.Width (7*b+4) := by
  have hm := multiplyFresh_width hr hv
  have ha := add_width one_width hv
  have hd := divideFresh_width hm ha
  convert hd using 1 <;> omega

lemma singletonRevenue_cost {r v : Fraction} {b : ℕ} (hr : r.Width b) (hv : v.Width b) :
    (singletonRevenue r v).2 ≤ 32768*(b+1)^2+32 := by
  have hm := multiplyFresh_cost hr hv
  have ha := add_cost one_width hv
  have hd := divideFresh_cost (multiplyFresh_width hr hv) (add_width one_width hv)
  have h1 : 256*(b+b+1)^2 ≤ 1024*(b+1)^2 := by
    calc _ ≤ 256*(2*(b+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
         _ = _ := by ring
  have h2 : 256*(1+b+1)^2 ≤ 1024*(b+1)^2 := by
    calc _ ≤ 256*(2*(b+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
         _ = _ := by ring
  have h3 : 256*(b+2*b+(1+2*b+1)+1)^2 ≤ 6400*(b+1)^2 := by
    calc _ ≤ 256*(5*(b+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
         _ = _ := by ring
  simp only [singletonRevenue]
  omega

/-- Scale-base straight-line program alpha*vmin/N, supplied the exact finite
minimum representation and positive product-count representation. -/
def scaleBase (alpha minimum count : Fraction) : Fraction × ℕ :=
  let p := multiplyFresh alpha minimum
  let q := divideFresh p.1 count
  (q.1, p.2+q.2+4)

lemma scaleBase_decode (alpha minimum count : Fraction) :
    (scaleBase alpha minimum count).1.decode = alpha.decode*minimum.decode/count.decode := by
  simp only [scaleBase, divideFresh_decode, multiplyFresh_decode]

lemma scaleBase_valid {alpha minimum count : Fraction}
    (ha : alpha.Valid) (hm : minimum.Valid) (hn : 0 < count.decode) :
    (scaleBase alpha minimum count).1.Valid := divideFresh_valid (multiplyFresh_valid ha hm) hn

lemma scaleBase_width {alpha minimum count : Fraction} {b : ℕ}
    (ha : alpha.Width b) (hm : minimum.Width b) (hn : count.Width b) :
    (scaleBase alpha minimum count).1.Width (5*b) := by
  convert divideFresh_width (multiplyFresh_width ha hm) hn using 1 <;> omega

lemma scaleBase_cost {alpha minimum count : Fraction} {b : ℕ}
    (ha : alpha.Width b) (hm : minimum.Width b) (hn : count.Width b) :
    (scaleBase alpha minimum count).2 ≤ 8192*(b+1)^2+32 := by
  have hp := multiplyFresh_cost ha hm
  have hq := divideFresh_cost (multiplyFresh_width ha hm) hn
  have h1 : 256*(b+b+1)^2 ≤ 1024*(b+1)^2 := by
    calc _ ≤ 256*(2*(b+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
         _ = _ := by ring
  have h2 : 256*(b+2*b+b+1)^2 ≤ 4096*(b+1)^2 := by
    calc _ ≤ 256*(4*(b+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
         _ = _ := by ring
  simp only [scaleBase]
  omega

end BalancedAssortments.FPTASCostSeeds
