import BalancedAssortments.FPTASCostAccuracy

/-! Full outer seed preparation from a raw product list and epsilon. Both the
product count and epsilon/10 are computed by charged binary-list programs. -/
namespace BalancedAssortments.FPTASCostSeeds
open ComplexityTimeBinary KnapsackCostRational FPTASCostGrid FPTAS

/-- Count an input list using binary increments, with no decoded Nat counter. -/
def countBits {α : Type*} : List α → List Bool × ℕ
  | [] => ([],1)
  | _::xs =>
      let r := countBits xs
      let up := addCarry r.1 [true] false
      (up.1,r.2+up.2+4)

lemma countBits_value {α : Type*} (xs : List α) : value (countBits xs).1 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [countBits, addCarry_value, value, ih]

lemma countBits_width {α : Type*} (xs : List α) : (countBits xs).1.length ≤ xs.length+1 := by
  induction xs with
  | nil => simp [countBits]
  | cons x xs ih => simp only [countBits, addCarry_length, List.length_cons, List.length_nil]; omega

lemma countBits_cost {α : Type*} (xs : List α) :
    (countBits xs).2 ≤ 64*(xs.length+1)^2+1 := by
  induction xs with
  | nil => simp [countBits]
  | cons x xs ih =>
    have hw := countBits_width xs
    simp only [countBits, addCarry_cost, List.length_cons, List.length_nil]
    have hm : max (countBits xs).1.length 1 ≤ xs.length+1 := by omega
    simp only [Nat.zero_add]
    nlinarith

def countFraction (products : List Product) : Fraction × ℕ :=
  let bits := countBits products
  (⟨bits.1,[true]⟩,bits.2+2)

lemma countFraction_decode (products : List Product) :
    (countFraction products).1.decode = products.length := by
  simp [countFraction, Fraction.decode, countBits_value, value]

lemma countFraction_valid (products : List Product) : (countFraction products).1.Valid := by
  norm_num [countFraction, Fraction.Valid, value]

lemma countFraction_width (products : List Product) :
    (countFraction products).1.Width (products.length+1) :=
  ⟨countBits_width products, by change 1 ≤ products.length+1; omega⟩

def initialAttraction : List Product → Fraction
  | [] => one
  | rv::_ => rv.2

/-- Return delta and all five outer seed fields; input products are traversed
explicitly and their count fraction is computed rather than supplied. -/
def prepareSeeds (alpha epsilon : Fraction) (products : List Product) : (Fraction × SeedPack) × ℕ :=
  let delta := accuracyFraction epsilon
  let count := countFraction products
  let out := outerSeeds alpha delta.1 count.1 (initialAttraction products) products
  ((delta.1,out.1),delta.2+count.2+out.2+4)

lemma prepareSeeds_actual {n : ℕ} (d : Input n) (ε : ℚ)
    (alpha epsilon : Fraction) (rv : Fin (n+1) → Product)
    (ha : alpha.decode = d.α) (he : epsilon.decode = ε) (hev : epsilon.Valid)
    (hv : ∀ i, (rv i).1.Valid ∧ (rv i).2.Valid)
    (hrd : ∀ i, (rv i).1.decode = d.r i) (hvd : ∀ i, (rv i).2.decode = d.v i) :
    let out := (prepareSeeds alpha epsilon ((List.finRange (n+1)).map rv)).1
    out.1.decode = ε/10 ∧ out.2.scaleBase.decode = d.α*vmin d/(n+1 : ℚ) ∧
    out.2.scaleCap.decode = d.α*vmax d ∧ out.2.revenueBase.decode = singletonValue d ∧
    out.2.revenueCap.decode = rmax d ∧ out.2.ratio.decode = 1+ε/10 := by
  have hi : initialAttraction ((List.finRange (n+1)).map rv) = (rv 0).2 := by
    rw [List.finRange_succ]
    rfl
  have hdelta : (accuracyFraction epsilon).1.decode = ε/10 := by rw [accuracyFraction_decode,he]
  have hs := outerSeeds_actual d (ε/10) alpha (accuracyFraction epsilon).1
    (countFraction ((List.finRange (n+1)).map rv)).1 rv ha hdelta
    (by simp [countFraction_decode]) (accuracyFraction_valid hev) hv hrd hvd
  dsimp only [prepareSeeds]
  rw [hi]
  exact ⟨hdelta,hs⟩

/-- Full seed-preparation polynomial with no free cardinality or accuracy input. -/
theorem prepareSeeds_cost (alpha epsilon : Fraction) (products : List Product) {b : ℕ}
    (hb : 1 ≤ b) (ha : alpha.Width b) (he : epsilon.Width b)
    (hp : ∀ p ∈ products, p.1.Width b ∧ p.2.Width b) :
    let B := b+products.length+9
    (prepareSeeds alpha epsilon products).2 ≤
      256*(b+5)^2+8 + 64*(products.length+1)^2+3 + seedCost products.length B+4 := by
  let B := b+products.length+9
  have hmono : b ≤ B := by dsimp [B]; omega
  have hα : alpha.Width B := ⟨ha.1.trans hmono,ha.2.trans hmono⟩
  have hδ : (accuracyFraction epsilon).1.Width B := by
    have hh := accuracyFraction_width he
    exact ⟨hh.1.trans (by dsimp [B];omega),hh.2.trans (by dsimp [B];omega)⟩
  have hN : (countFraction products).1.Width B := by
    have hh := countFraction_width products
    exact ⟨hh.1.trans (by dsimp [B];omega),hh.2.trans (by dsimp [B];omega)⟩
  have hinit : (initialAttraction products).Width B := by
    cases products with
    | nil => exact ⟨one_width.1.trans (by dsimp [B];omega),one_width.2.trans (by dsimp [B];omega)⟩
    | cons p ps =>
      have hh := (hp p (by simp)).2
      exact ⟨hh.1.trans hmono,hh.2.trans hmono⟩
  have hproducts : ∀ p ∈ products, p.1.Width B ∧ p.2.Width B := by
    intro p hh
    obtain ⟨hr,hv⟩ := hp p hh
    exact ⟨⟨hr.1.trans hmono,hr.2.trans hmono⟩,⟨hv.1.trans hmono,hv.2.trans hmono⟩⟩
  have hs := outerSeeds_cost alpha (accuracyFraction epsilon).1 (countFraction products).1
    (initialAttraction products) products (show 1 ≤ B by dsimp [B];omega) hα hδ hN hinit hproducts
  have hc := countBits_cost products
  have hd := accuracyFraction_cost he
  have hcount : (countFraction products).2 ≤ 64*(products.length+1)^2+3 := by
    exact Nat.add_le_add_right hc 2
  dsimp only [prepareSeeds]
  dsimp only [B] at hs
  omega

lemma initialAttraction_valid (products : List Product)
    (hp : ∀ p ∈ products, p.1.Valid ∧ p.2.Valid) : (initialAttraction products).Valid := by
  cases products with
  | nil => exact one_valid
  | cons p ps => exact (hp p (by simp)).2

lemma initialAttraction_width (products : List Product) {b : ℕ} (hb : 1 ≤ b)
    (hp : ∀ p ∈ products, p.1.Width b ∧ p.2.Width b) : (initialAttraction products).Width b := by
  cases products with
  | nil => exact ⟨one_width.1.trans hb,one_width.2.trans hb⟩
  | cons p ps => exact (hp p (by simp)).2

lemma prepareSeeds_valid (alpha epsilon : Fraction) (products : List Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (hp : ∀ p ∈ products, p.1.Valid ∧ p.2.Valid)
    (hn : products ≠ []) :
    (prepareSeeds alpha epsilon products).1.1.Valid ∧
      (prepareSeeds alpha epsilon products).1.2.Valid := by
  have hcount : 0 < (countFraction products).1.decode := by
    rw [countFraction_decode]
    exact_mod_cast List.length_pos.mpr hn
  exact ⟨accuracyFraction_valid he, outerSeeds_valid _ _ _ _ _ ha
    (accuracyFraction_valid he) hcount (initialAttraction_valid products hp) hp⟩

lemma prepareSeeds_width (alpha epsilon : Fraction) (products : List Product) {b : ℕ}
    (hb : 1 ≤ b) (ha : alpha.Width b) (he : epsilon.Width b)
    (hp : ∀ p ∈ products, p.1.Width b ∧ p.2.Width b) :
    let B := b+products.length+9
    (prepareSeeds alpha epsilon products).1.1.Width B ∧
      (prepareSeeds alpha epsilon products).1.2.Width (7*B+4) := by
  let B := b+products.length+9
  have hmono : b ≤ B := by dsimp [B];omega
  have hα : alpha.Width B := ⟨ha.1.trans hmono,ha.2.trans hmono⟩
  have hδ : (accuracyFraction epsilon).1.Width B := by
    have hh := accuracyFraction_width he
    exact ⟨hh.1.trans (by dsimp [B];omega),hh.2.trans (by dsimp [B];omega)⟩
  have hN : (countFraction products).1.Width B := by
    have hh := countFraction_width products
    exact ⟨hh.1.trans (by dsimp [B];omega),hh.2.trans (by dsimp [B];omega)⟩
  have hinit : (initialAttraction products).Width B := by
    have hh := initialAttraction_width products hb hp
    exact ⟨hh.1.trans hmono,hh.2.trans hmono⟩
  have hproducts : ∀ p ∈ products, p.1.Width B ∧ p.2.Width B := by
    intro p hh
    obtain ⟨hr,hv⟩ := hp p hh
    exact ⟨⟨hr.1.trans hmono,hr.2.trans hmono⟩,⟨hv.1.trans hmono,hv.2.trans hmono⟩⟩
  exact ⟨hδ,outerSeeds_width _ _ _ _ _ (by omega) hα hδ hN hinit hproducts⟩

end BalancedAssortments.FPTASCostSeeds
