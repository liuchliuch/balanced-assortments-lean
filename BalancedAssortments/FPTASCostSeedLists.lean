import BalancedAssortments.FPTASCostSeeds
import BalancedAssortments.FPTAS

/-! Bit/list construction of singleton and extremal data from the original product
list. It consumes binary fractions directly and never invokes rational normalization. -/
namespace BalancedAssortments.FPTASCostSeeds
open ComplexityTimeBinary KnapsackCostRational FPTASCostGrid

abbrev Product := Fraction × Fraction

def singletonList : List Product → List Fraction × ℕ
  | [] => ([],1)
  | rv :: rest =>
      let s := singletonRevenue rv.1 rv.2
      let tail := singletonList rest
      (s.1 :: tail.1, s.2+tail.2+4)

lemma singletonList_decode (xs : List Product) (hv : ∀ x ∈ xs, x.2.Valid) :
    (singletonList xs).1.map Fraction.decode =
      xs.map (fun rv => rv.1.decode*rv.2.decode/(1+rv.2.decode)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [singletonList, List.map_cons, singletonRevenue_decode (hv x (by simp))]
    rw [ih (fun y hy => hv y (by simp [hy]))]

lemma singletonList_valid (xs : List Product) (hv : ∀ x ∈ xs, x.1.Valid ∧ x.2.Valid) :
    ∀ y ∈ (singletonList xs).1, y.Valid := by
  induction xs with
  | nil => simp [singletonList]
  | cons x xs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact singletonRevenue_valid (hv x (by simp)).1 (hv x (by simp)).2
    · exact ih (fun z hz => hv z (by simp [hz])) y hy

lemma singletonList_width (xs : List Product) {b : ℕ}
    (hw : ∀ x ∈ xs, x.1.Width b ∧ x.2.Width b) :
    ∀ y ∈ (singletonList xs).1, y.Width (7*b+4) := by
  induction xs with
  | nil => simp [singletonList]
  | cons x xs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact singletonRevenue_width (hw x (by simp)).1 (hw x (by simp)).2
    · exact ih (fun z hz => hw z (by simp [hz])) y hy

lemma singletonList_length (xs : List Product) : (singletonList xs).1.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [singletonList, List.length_cons, ih]

theorem singletonList_cost (xs : List Product) {b : ℕ}
    (hw : ∀ x ∈ xs, x.1.Width b ∧ x.2.Width b) :
    (singletonList xs).2 ≤ xs.length*(32768*(b+1)^2+36)+1 := by
  induction xs with
  | nil => simp [singletonList]
  | cons x xs ih =>
    have hs := singletonRevenue_cost (hw x (by simp)).1 (hw x (by simp)).2
    have ht := ih (fun z hz => hw z (by simp [hz]))
    simp only [singletonList, List.length_cons]
    rw [Nat.succ_mul]
    omega

/-- Zero is used only as the initial max accumulator, matching the actual wrapper. -/
def zero : Fraction := ⟨[],[true]⟩
lemma zero_valid : zero.Valid := by norm_num [zero, Fraction.Valid, value]
lemma zero_decode : zero.decode = 0 := by norm_num [zero, Fraction.decode, value]
lemma zero_width {b : ℕ} (hb : 1 ≤ b) : zero.Width b := by
  simp [zero, Fraction.Width]; omega

/-- Actual binary best-singleton computation, including generation and comparisons. -/
def bestSingleton (xs : List Product) : Fraction × ℕ :=
  let ys := singletonList xs
  let ans := foldExtreme false zero ys.1
  (ans.1, ys.2+ans.2+4)

lemma bestSingleton_decode (xs : List Product) (hv : ∀ x ∈ xs, x.1.Valid ∧ x.2.Valid) :
    (bestSingleton xs).1.decode = FPTAS.maxList
      (xs.map (fun rv => rv.1.decode*rv.2.decode/(1+rv.2.decode))) := by
  simp only [bestSingleton]
  rw [foldExtreme_decode false zero _ zero_valid (singletonList_valid xs hv),
    singletonList_decode xs (fun x hx => (hv x hx).2), zero_decode]
  rfl

lemma bestSingleton_valid (xs : List Product) (hv : ∀ x ∈ xs, x.1.Valid ∧ x.2.Valid) :
    (bestSingleton xs).1.Valid := foldExtreme_valid false zero _ zero_valid (singletonList_valid xs hv)

lemma bestSingleton_width (xs : List Product) {b : ℕ}
    (hw : ∀ x ∈ xs, x.1.Width b ∧ x.2.Width b) :
    (bestSingleton xs).1.Width (7*b+4) :=
  foldExtreme_width false zero _ (zero_width (by omega)) (singletonList_width xs hw)

/-- Fully concrete bound before any generic big-O abstraction. -/
theorem bestSingleton_cost (xs : List Product) {b : ℕ}
    (hw : ∀ x ∈ xs, x.1.Width b ∧ x.2.Width b) :
    (bestSingleton xs).2 ≤
      xs.length*(32768*(b+1)^2+36) + xs.length*(512*(7*b+5)^2+10)+6 := by
  have hs := singletonList_cost xs hw
  have hm := foldExtreme_cost false zero (singletonList xs).1
    (zero_width (show 1 ≤ 7*b+4 by omega)) (singletonList_width xs hw)
  rw [singletonList_length, show 7*b+4+1 = 7*b+5 by omega] at hm
  simp only [bestSingleton]
  omega

end BalancedAssortments.FPTASCostSeeds
