import BalancedAssortments.FPTASCostSeeds
import BalancedAssortments.KnapsackCostState

/-! Binary rational arithmetic for final revenue comparison and reverse tilt.
All output fractions are unreduced; no gcd or rational-arithmetic oracle is used. -/
namespace BalancedAssortments.FPTASCostOutput
open ComplexityTimeBinary KnapsackCostRational FPTASCostGrid FPTASCostSeeds

def zero : Fraction := ⟨[],[true]⟩
lemma zero_valid : zero.Valid := by norm_num [zero, Fraction.Valid, value]
lemma zero_width : zero.Width 1 := by simp [zero, Fraction.Width]
lemma zero_decode : zero.decode = 0 := by norm_num [zero, Fraction.decode, value]

def sumFractions : List Fraction → Fraction × ℕ
  | [] => (zero,1)
  | x::xs =>
      let tail := sumFractions xs
      let out := add tail.1 x
      (out.1,tail.2+out.2+4)

lemma sumFractions_valid (xs : List Fraction) (hx : ∀ x ∈ xs, x.Valid) :
    (sumFractions xs).1.Valid := by
  induction xs with
  | nil => exact zero_valid
  | cons x xs ih => exact add_valid (ih fun y hy => hx y (by simp [hy])) (hx x (by simp))

lemma sumFractions_decode (xs : List Fraction) (hx : ∀ x ∈ xs, x.Valid) :
    (sumFractions xs).1.decode = (xs.map Fraction.decode).sum := by
  induction xs with
  | nil => exact zero_decode
  | cons x xs ih =>
    have ht : ∀ y ∈ xs, y.Valid := fun y hy => hx y (by simp [hy])
    simp only [sumFractions, add_decode (sumFractions_valid xs ht) (hx x (by simp)),
      ih ht, List.map_cons, List.sum_cons]
    ring

lemma sumFractions_width (xs : List Fraction) {b : ℕ} (hx : ∀ x ∈ xs, x.Width b) :
    (sumFractions xs).1.Width (1+xs.length*(2*b+1)) := by
  induction xs with
  | nil => simpa [sumFractions] using zero_width
  | cons x xs ih =>
    have hh := add_width (ih fun y hy => hx y (by simp [hy])) (hx x (by simp))
    change (add (sumFractions xs).1 x).1.Width (1+(xs.length+1)*(2*b+1))
    rw [show 1+(xs.length+1)*(2*b+1) = (1+xs.length*(2*b+1))+2*b+1 by ring]
    exact hh

lemma sumFractions_cost (xs : List Fraction) {b : ℕ} (hx : ∀ x ∈ xs, x.Width b) :
    (sumFractions xs).2 ≤ xs.length*(256*(2+xs.length*(2*b+1)+b)^2+4)+1 := by
  induction xs with
  | nil => simp [sumFractions]
  | cons x xs ih =>
    have ht : ∀ y ∈ xs, y.Width b := fun y hy => hx y (by simp [hy])
    have ha := add_cost (sumFractions_width xs ht) (hx x (by simp))
    have hi := ih ht
    have hle : (2+xs.length*(2*b+1)+b)^2 ≤ (2+(xs.length+1)*(2*b+1)+b)^2 := by
      apply Nat.pow_le_pow_left
      nlinarith
    simp only [sumFractions, List.length_cons]
    nlinarith

/-- Pointwise products, stopping at the shorter input as ordinary list zip does. -/
def products : List Fraction → List Fraction → List Fraction × ℕ
  | [], _ => ([],1)
  | _, [] => ([],1)
  | r::rs, w::ws =>
      let p := multiplyFresh r w
      let tail := products rs ws
      (p.1::tail.1,p.2+tail.2+4)

lemma products_length (rs ws : List Fraction) : (products rs ws).1.length = min rs.length ws.length := by
  induction rs generalizing ws with
  | nil => simp [products]
  | cons r rs ih => cases ws <;> simp [products, ih]

lemma products_valid (rs ws : List Fraction) (hr : ∀ r ∈ rs, r.Valid) (hw : ∀ w ∈ ws, w.Valid) :
    ∀ x ∈ (products rs ws).1, x.Valid := by
  induction rs generalizing ws with
  | nil => simp [products]
  | cons r rs ih =>
    cases ws with
    | nil => simp [products]
    | cons w ws =>
      intro x hx
      simp only [products, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact multiplyFresh_valid (hr r (by simp)) (hw w (by simp))
      · exact ih ws (fun y hy => hr y (by simp [hy])) (fun y hy => hw y (by simp [hy])) x hx

lemma products_decode (rs ws : List Fraction) :
    (products rs ws).1.map Fraction.decode = (rs.zip ws).map (fun rw => rw.1.decode*rw.2.decode) := by
  induction rs generalizing ws with
  | nil => simp [products]
  | cons r rs ih => cases ws <;> simp [products, multiplyFresh_decode, ih]

lemma products_width (rs ws : List Fraction) {b : ℕ}
    (hr : ∀ r ∈ rs, r.Width b) (hw : ∀ w ∈ ws, w.Width b) :
    ∀ x ∈ (products rs ws).1, x.Width (3*b) := by
  induction rs generalizing ws with
  | nil => simp [products]
  | cons r rs ih =>
    cases ws with
    | nil => simp [products]
    | cons w ws =>
      intro x hx
      simp only [products, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa [Nat.mul_add, Nat.add_mul, show b+2*b=3*b by omega] using
          multiplyFresh_width (hr r (by simp)) (hw w (by simp))
      · exact ih ws (fun y hy => hr y (by simp [hy])) (fun y hy => hw y (by simp [hy])) x hx

lemma products_cost (rs ws : List Fraction) {b : ℕ}
    (hr : ∀ r ∈ rs, r.Width b) (hw : ∀ w ∈ ws, w.Width b) :
    (products rs ws).2 ≤ rs.length*(256*(2*b+1)^2+10)+1 := by
  induction rs generalizing ws with
  | nil => simp [products]
  | cons r rs ih =>
    cases ws with
    | nil => simp [products]
    | cons w ws =>
      have hp := multiplyFresh_cost (hr r (by simp)) (hw w (by simp))
      have ht := ih ws (fun y hy => hr y (by simp [hy])) (fun y hy => hw y (by simp [hy]))
      simp only [products, List.length_cons]
      nlinarith

/-- Expected revenue directly on decoded input/sales fractions. -/
def revenue (rs ws : List Fraction) : Fraction × ℕ :=
  let ps := products rs ws
  let num := sumFractions ps.1
  let W := sumFractions ws
  let den := add W.1 one
  let out := divideFresh num.1 den.1
  (out.1,ps.2+num.2+W.2+den.2+out.2+12)

lemma revenue_decode (rs ws : List Fraction) (hr : ∀ r ∈ rs, r.Valid) (hw : ∀ w ∈ ws, w.Valid) :
    (revenue rs ws).1.decode = ((rs.zip ws).map (fun rw => rw.1.decode*rw.2.decode)).sum /
      (1+(ws.map Fraction.decode).sum) := by
  simp only [revenue, divideFresh_decode, sumFractions_decode _ (products_valid rs ws hr hw),
    products_decode, add_decode (sumFractions_valid ws hw) one_valid, one_decode,
    sumFractions_decode ws hw]
  congr 1
  ring

lemma revenue_valid (rs ws : List Fraction) (hr : ∀ r ∈ rs, r.Valid) (hw : ∀ w ∈ ws, w.Valid) :
    (revenue rs ws).1.Valid := by
  apply divideFresh_valid (sumFractions_valid _ (products_valid rs ws hr hw))
  rw [add_decode (sumFractions_valid ws hw) one_valid, one_decode]
  have := decode_nonnegative (sumFractions ws).1
  linarith

def sumWidth (n b : ℕ) : ℕ := 1+n*(2*b+1)
def sumBudget (n b : ℕ) : ℕ := n*(256*(2+n*(2*b+1)+b)^2+4)+1

theorem sumFractions_width_bounded (xs : List Fraction) {n b : ℕ}
    (hlen : xs.length ≤ n) (hx : ∀ x ∈ xs, x.Width b) :
    (sumFractions xs).1.Width (sumWidth n b) := by
  have hh := sumFractions_width xs hx
  have he : 1+xs.length*(2*b+1) ≤ sumWidth n b := Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) _
  exact ⟨hh.1.trans he, hh.2.trans he⟩

theorem sumFractions_cost_bounded (xs : List Fraction) {n b : ℕ}
    (hlen : xs.length ≤ n) (hx : ∀ x ∈ xs, x.Width b) :
    (sumFractions xs).2 ≤ sumBudget n b := by
  have hh := sumFractions_cost xs hx
  have he : 2+xs.length*(2*b+1)+b ≤ 2+n*(2*b+1)+b := by
    have := Nat.mul_le_mul_right (2*b+1) hlen
    omega
  have hp := Nat.pow_le_pow_left he 2
  have hm := Nat.mul_le_mul hlen (Nat.add_le_add_right (Nat.mul_le_mul_left 256 hp) 4)
  exact hh.trans (Nat.add_le_add_right hm 1)

def revenueWidth (n b : ℕ) : ℕ := sumWidth n (3*b)+2*(sumWidth n b+3)
def revenueBudget (n b : ℕ) : ℕ :=
  (n*(256*(2*b+1)^2+10)+1) + sumBudget n (3*b) + sumBudget n b +
  256*(sumWidth n b+2)^2 + 256*(sumWidth n (3*b)+(sumWidth n b+3)+1)^2 + 20

theorem revenue_width (rs ws : List Fraction) {n b : ℕ}
    (hnr : rs.length ≤ n) (hnw : ws.length ≤ n)
    (hr : ∀ r ∈ rs, r.Width b) (hw : ∀ w ∈ ws, w.Width b) :
    (revenue rs ws).1.Width (revenueWidth n b) := by
  have hp : (products rs ws).1.length ≤ n := by rw [products_length]; exact (min_le_left _ _).trans hnr
  have hnum := sumFractions_width_bounded _ hp (products_width rs ws hr hw)
  have hW := sumFractions_width_bounded ws hnw hw
  have hd := add_width hW one_width
  have ho := divideFresh_width hnum hd
  simpa [revenue, revenueWidth] using ho

theorem revenue_cost (rs ws : List Fraction) {n b : ℕ}
    (hnr : rs.length ≤ n) (hnw : ws.length ≤ n)
    (hr : ∀ r ∈ rs, r.Width b) (hw : ∀ w ∈ ws, w.Width b) :
    (revenue rs ws).2 ≤ revenueBudget n b := by
  have hp : (products rs ws).1.length ≤ n := by rw [products_length]; exact (min_le_left _ _).trans hnr
  have hnum := sumFractions_width_bounded _ hp (products_width rs ws hr hw)
  have hW := sumFractions_width_bounded ws hnw hw
  have hd := add_width hW one_width
  have cp := (products_cost rs ws hr hw).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hnr) 1)
  have cn := sumFractions_cost_bounded _ hp (products_width rs ws hr hw)
  have cw := sumFractions_cost_bounded ws hnw hw
  have cd := add_cost hW one_width
  have co := divideFresh_cost hnum hd
  dsimp only [revenue, revenueBudget]
  norm_num only [Nat.mul_one, Nat.add_assoc] at cd co ⊢
  omega

/-- Unrounded transformed-profit test, using binary cross-products. -/
def accepts (ρ profit : Fraction) : Bool × ℕ :=
  let c := compare ρ profit
  (c.1 != Ordering.gt,c.2+2)

theorem accepts_correct {ρ profit : Fraction} (hr : ρ.Valid) (hp : profit.Valid) :
    (accepts ρ profit).1 = true ↔ ρ.decode ≤ profit.decode := by
  have hh := compare_correct hr hp
  unfold accepts
  generalize he : (compare ρ profit).1 = o at *
  cases o <;> simp_all [rationalMeaning] <;> linarith

theorem accepts_cost {ρ profit : Fraction} {b : ℕ} (hr : ρ.Width b) (hp : profit.Width b) :
    (accepts ρ profit).2 ≤ 512*(b+1)^2+2 := Nat.add_le_add_right (compare_cost hr hp) 2

/-- Select between complete candidate vectors by actual unrounded revenue.
Ties retain the incumbent, as in the paper's strict improvement update. -/
def improve (rs old next : List Fraction) : List Fraction × ℕ :=
  let ro := revenue rs old
  let rn := revenue rs next
  let c := compare ro.1 rn.1
  (if c.1 == Ordering.lt then next else old,ro.2+rn.2+c.2+6)

theorem improve_cases (rs old next : List Fraction) :
    (improve rs old next).1 = old ∨ (improve rs old next).1 = next := by
  dsimp only [improve]
  split_ifs <;> simp

theorem improve_max (rs old next : List Fraction)
    (hr : ∀ x ∈ rs, x.Valid) (ho : ∀ x ∈ old, x.Valid) (hn : ∀ x ∈ next, x.Valid) :
    (revenue rs (improve rs old next).1).1.decode =
      max (revenue rs old).1.decode (revenue rs next).1.decode := by
  have h := compare_correct (revenue_valid rs old hr ho) (revenue_valid rs next hr hn)
  generalize he : (compare (revenue rs old).1 (revenue rs next).1).1 = o at *
  cases o <;> simp only [he, rationalMeaning] at h <;>
    simp [improve,he,max_eq_left,max_eq_right,h,h.le,h.symm.le]

theorem improve_cost (rs old next : List Fraction) {n b : ℕ}
    (hR : rs.length ≤ n) (hO : old.length ≤ n) (hN : next.length ≤ n)
    (hr : ∀ x ∈ rs, x.Width b) (ho : ∀ x ∈ old, x.Width b) (hn : ∀ x ∈ next, x.Width b) :
    (improve rs old next).2 ≤ 2*revenueBudget n b+512*(revenueWidth n b+1)^2+6 := by
  have co := revenue_cost rs old hR hO hr ho
  have cn := revenue_cost rs next hR hN hr hn
  have cc := compare_cost (revenue_width rs old hR hO hr ho) (revenue_width rs next hR hN hr hn)
  dsimp only [improve]
  omega

def selectFractions : List Fraction → List Bool → List Fraction × ℕ
  | [], _ => ([],1)
  | x::xs, ms =>
      let tail := selectFractions xs ms.tail
      (if ms.headD false then x::tail.1 else tail.1,tail.2+4)

lemma selectFractions_length (xs : List Fraction) (ms : List Bool) :
    (selectFractions xs ms).1.length ≤ xs.length := by
  induction xs generalizing ms with
  | nil => simp [selectFractions]
  | cons x xs ih => dsimp only [selectFractions]; split_ifs <;> simp only [List.length_cons] <;> have := ih ms.tail <;> omega

lemma selectFractions_mem (xs : List Fraction) (ms : List Bool) :
    ∀ x ∈ (selectFractions xs ms).1, x ∈ xs := by
  induction xs generalizing ms with
  | nil => simp [selectFractions]
  | cons x xs ih =>
    intro y hy
    dsimp only [selectFractions] at hy
    split_ifs at hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · simp
      · exact List.mem_cons_of_mem _ (ih ms.tail y hy)
    · exact List.mem_cons_of_mem _ (ih ms.tail y hy)

lemma selectFractions_cost (xs : List Fraction) (ms : List Bool) :
    (selectFractions xs ms).2 = 4*xs.length+1 := by
  induction xs generalizing ms <;> simp [selectFractions, *] <;> omega

lemma selectFractions_decode (xs : List Fraction) (ms : List Bool) :
    ((selectFractions xs ms).1.map Fraction.decode).sum =
      (((xs.zip ms).filter fun p => p.2).map fun p => p.1.decode).sum := by
  induction xs generalizing ms with
  | nil => simp [selectFractions]
  | cons x xs ih =>
    cases ms with
    | nil => simpa [selectFractions] using ih []
    | cons b bs => cases b <;> simp [selectFractions,List.filter_cons,ih]

/-- The attraction denominator of one assortment mask. -/
def displayDenominator (vs : List Fraction) (mask : List Bool) : Fraction × ℕ :=
  let selected := selectFractions vs mask
  let total := sumFractions selected.1
  let out := add total.1 one
  (out.1,selected.2+total.2+out.2+4)

lemma displayDenominator_valid (vs : List Fraction) (mask : List Bool)
    (hv : ∀ v ∈ vs, v.Valid) : (displayDenominator vs mask).1.Valid :=
  add_valid (sumFractions_valid _ (fun x hx => hv x (selectFractions_mem vs mask x hx))) one_valid

lemma displayDenominator_decode (vs : List Fraction) (mask : List Bool)
    (hv : ∀ v ∈ vs, v.Valid) :
    (displayDenominator vs mask).1.decode =
      1+(((vs.zip mask).filter fun p => p.2).map fun p => p.1.decode).sum := by
  simp only [displayDenominator,add_decode (sumFractions_valid _
    (fun x hx => hv x (selectFractions_mem vs mask x hx))) one_valid,
    sumFractions_decode _ (fun x hx => hv x (selectFractions_mem vs mask x hx)),one_decode,
    selectFractions_decode]
  ring

def displayWidth (n b : ℕ) : ℕ := sumWidth n b+3
def displayBudget (n b : ℕ) : ℕ := 4*n+1+sumBudget n b+256*(sumWidth n b+2)^2+4

theorem displayDenominator_width (vs : List Fraction) (mask : List Bool) {n b : ℕ}
    (hn : vs.length ≤ n) (hv : ∀ v ∈ vs, v.Width b) :
    (displayDenominator vs mask).1.Width (displayWidth n b) := by
  have hs := sumFractions_width_bounded _ ((selectFractions_length vs mask).trans hn)
    (fun x hx => hv x (selectFractions_mem vs mask x hx))
  simpa [displayDenominator,displayWidth] using add_width hs one_width

theorem displayDenominator_cost (vs : List Fraction) (mask : List Bool) {n b : ℕ}
    (hn : vs.length ≤ n) (hv : ∀ v ∈ vs, v.Width b) :
    (displayDenominator vs mask).2 ≤ displayBudget n b := by
  have hs := sumFractions_width_bounded _ ((selectFractions_length vs mask).trans hn)
    (fun x hx => hv x (selectFractions_mem vs mask x hx))
  have cs := sumFractions_cost_bounded _ ((selectFractions_length vs mask).trans hn)
    (fun x hx => hv x (selectFractions_mem vs mask x hx))
  have ca := add_cost hs one_width
  dsimp only [displayDenominator,displayBudget]
  rw [selectFractions_cost]
  norm_num only [Nat.add_assoc] at ca ⊢
  omega

/-- Reverse the denominator tilt for one atom with an already-computed common
normalizer. The mask and unreduced input mass are retained exactly. -/
def reverseWeight (vs : List Fraction) (normalizer mass : Fraction) (mask : List Bool) : Fraction × ℕ :=
  let d := displayDenominator vs mask
  let m := multiplyFresh mass d.1
  let q := divideFresh m.1 normalizer
  (q.1,d.2+m.2+q.2+4)

theorem reverseWeight_decode (vs : List Fraction) (normalizer mass : Fraction) (mask : List Bool)
    (hv : ∀ v ∈ vs, v.Valid) :
    (reverseWeight vs normalizer mass mask).1.decode =
      mass.decode*(1+(((vs.zip mask).filter fun p => p.2).map fun p => p.1.decode).sum)/normalizer.decode := by
  simp only [reverseWeight,divideFresh_decode,multiplyFresh_decode,displayDenominator_decode vs mask hv]

theorem reverseWeight_valid (vs : List Fraction) {normalizer mass : Fraction} (mask : List Bool)
    (hv : ∀ v ∈ vs, v.Valid) (hm : mass.Valid) (hn : 0 < normalizer.decode) :
    (reverseWeight vs normalizer mass mask).1.Valid :=
  divideFresh_valid (multiplyFresh_valid hm (displayDenominator_valid vs mask hv)) hn

def reverseWidth (n b c : ℕ) : ℕ := b+2*displayWidth n b+2*c
def reverseBudget (n b c : ℕ) : ℕ := displayBudget n b +
  256*(b+displayWidth n b+1)^2+6 + 256*(b+2*displayWidth n b+c+1)^2+8+4

theorem reverseWeight_width (vs : List Fraction) {normalizer mass : Fraction} (mask : List Bool)
    {n b c : ℕ} (hl : vs.length ≤ n) (hv : ∀ v ∈ vs, v.Width b)
    (hm : mass.Width b) (hn : normalizer.Width c) :
    (reverseWeight vs normalizer mass mask).1.Width (reverseWidth n b c) := by
  exact divideFresh_width (multiplyFresh_width hm (displayDenominator_width vs mask hl hv)) hn

theorem reverseWeight_cost (vs : List Fraction) {normalizer mass : Fraction} (mask : List Bool)
    {n b c : ℕ} (hl : vs.length ≤ n) (hv : ∀ v ∈ vs, v.Width b)
    (hm : mass.Width b) (hn : normalizer.Width c) :
    (reverseWeight vs normalizer mass mask).2 ≤ reverseBudget n b c := by
  have hd := displayDenominator_width vs mask hl hv
  have cd := displayDenominator_cost vs mask hl hv
  have cm := multiplyFresh_cost hm hd
  have cq := divideFresh_cost (multiplyFresh_width hm hd) hn
  dsimp only [reverseWeight,reverseBudget]
  omega

abbrev PolicyAtom := Fraction × List Bool

def tiltAtoms (vs : List Fraction) (normalizer : Fraction) : List PolicyAtom → List PolicyAtom × ℕ
  | [] => ([],1)
  | a::as =>
      let q := reverseWeight vs normalizer a.1 a.2
      let tail := tiltAtoms vs normalizer as
      ((q.1,a.2)::tail.1,q.2+tail.2+4)

theorem tiltAtoms_length (vs : List Fraction) (normalizer : Fraction) (as : List PolicyAtom) :
    (tiltAtoms vs normalizer as).1.length = as.length := by
  induction as <;> simp [tiltAtoms, *]

theorem tiltAtoms_decode (vs : List Fraction) (normalizer : Fraction) (as : List PolicyAtom)
    (hv : ∀ v ∈ vs, v.Valid) :
    ((tiltAtoms vs normalizer as).1.map fun a => (a.1.decode,a.2)) =
    as.map (fun a => (a.1.decode*(1+(((vs.zip a.2).filter fun p => p.2).map fun p => p.1.decode).sum)/normalizer.decode,a.2)) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [tiltAtoms,List.map_cons,reverseWeight_decode vs normalizer a.1 a.2 hv,ih]

theorem tiltAtoms_cost (vs : List Fraction) (normalizer : Fraction) (as : List PolicyAtom)
    {n b c : ℕ} (hl : vs.length ≤ n) (hv : ∀ v ∈ vs, v.Width b)
    (ha : ∀ a ∈ as, a.1.Width b) (hn : normalizer.Width c) :
    (tiltAtoms vs normalizer as).2 ≤ as.length*(reverseBudget n b c+4)+1 := by
  induction as with
  | nil => simp [tiltAtoms]
  | cons a as ih =>
    have ca := reverseWeight_cost vs a.2 hl hv (ha a (by simp)) hn
    have ct := ih (fun a hm => ha a (by simp [hm]))
    dsimp only [tiltAtoms]
    simp only [List.length_cons]
    nlinarith
end BalancedAssortments.FPTASCostOutput
