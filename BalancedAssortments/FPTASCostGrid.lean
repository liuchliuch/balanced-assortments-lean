import BalancedAssortments.KnapsackCostRational
import BalancedAssortments.Grids

/-! A genuinely bit/list implemented geometric grid: successive unreduced
fraction multiplication and exact cross-product comparisons. No unit-cost
rational arithmetic is executed by gridBits. -/
namespace BalancedAssortments.FPTASCostGrid
open ComplexityTimeBinary KnapsackCostRational

/-- Multiply by a fresh bounded-size ratio, with that operand first in both
schoolbook products; this prevents repeated doubling of padded state widths. -/
def multiplyFresh (x ratio : Fraction) : Fraction × ℕ :=
  let num := mulBits ratio.numerator x.numerator
  let den := mulBits ratio.denominator x.denominator
  (⟨num.1, den.1⟩, num.2 + den.2 + 4)

lemma multiplyFresh_decode (x ratio : Fraction) :
    (multiplyFresh x ratio).1.decode = x.decode * ratio.decode := by
  simp only [multiplyFresh, Fraction.decode, mulBits_value, Nat.cast_mul]
  rw [mul_div_mul_comm]
  ring

lemma multiplyFresh_valid {x ratio : Fraction} (hx : x.Valid) (hr : ratio.Valid) :
    (multiplyFresh x ratio).1.Valid := by
  simpa only [multiplyFresh, Fraction.Valid, mulBits_value] using Nat.mul_pos hr hx

lemma multiplyFresh_width {x ratio : Fraction} {a b : ℕ} (hx : x.Width a) (hr : ratio.Width b) :
    (multiplyFresh x ratio).1.Width (a+2*b) := by
  have hn := mulBits_length ratio.numerator x.numerator
  have hd := mulBits_length ratio.denominator x.denominator
  rcases hx with ⟨hx1,hx2⟩
  rcases hr with ⟨hr1,hr2⟩
  constructor <;> dsimp [multiplyFresh] <;> omega

lemma multiplyFresh_cost {x ratio : Fraction} {a b : ℕ} (hx : x.Width a) (hr : ratio.Width b) :
    (multiplyFresh x ratio).2 ≤ 256*(a+b+1)^2+6 := by
  have hn := mulBits_cost ratio.numerator x.numerator
  have hd := mulBits_cost ratio.denominator x.denominator
  have hnp : ratio.numerator.length*(ratio.numerator.length+x.numerator.length+1) ≤ b*(a+b+1) :=
    Nat.mul_le_mul hr.1 (by have := hx.1; have := hr.1; omega)
  have hdp : ratio.denominator.length*(ratio.denominator.length+x.denominator.length+1) ≤ b*(a+b+1) :=
    Nat.mul_le_mul hr.2 (by have := hx.2; have := hr.2; omega)
  simp only [multiplyFresh]
  nlinarith

/-- Process every requested exponent, retaining exactly the values below the cap.
The recursion count is explicit; there is no unchecked stopping heuristic. -/
def gridBits : ℕ → Fraction → Fraction → Fraction → List Fraction × ℕ
  | 0, _, _, _ => ([], 1)
  | k+1, current, ratio, cap =>
      let cmp := compare current cap
      let nxt := multiplyFresh current ratio
      let rest := gridBits k nxt.1 ratio cap
      (if cmp.1 = Ordering.gt then rest.1 else current :: rest.1,
        cmp.2 + nxt.2 + rest.2 + 8)

lemma compare_gt_iff {x y : Fraction} (hx : x.Valid) (hy : y.Valid) :
    (compare x y).1 = Ordering.gt ↔ y.decode < x.decode := by
  have hc := compare_correct hx hy
  cases he : (compare x y).1 <;> simp_all [rationalMeaning] <;> linarith

lemma gridBits_decode (k : ℕ) (current ratio cap : Fraction)
    (hc : current.Valid) (hr : ratio.Valid) (hp : cap.Valid) :
    (gridBits k current ratio cap).1.map Fraction.decode =
      ((List.range k).map fun j => current.decode * ratio.decode ^ j).filter (· ≤ cap.decode) := by
  induction k generalizing current with
  | zero => simp [gridBits]
  | succ k ih =>
    have hi := ih (multiplyFresh current ratio).1 (multiplyFresh_valid hc hr)
    have he : ((List.range k).map fun j => (multiplyFresh current ratio).1.decode * ratio.decode^j) =
        (List.range k).map (fun j => current.decode * ratio.decode^(j+1)) := by
      apply List.map_congr_left
      intro j _
      rw [multiplyFresh_decode, pow_succ]
      ring
    rw [he] at hi
    simp only [gridBits]
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, pow_zero, mul_one, List.filter_cons]
    by_cases hg : (compare current cap).1 = Ordering.gt
    · have hh : ¬ current.decode ≤ cap.decode := not_le.mpr ((compare_gt_iff hc hp).1 hg)
      simp only [hg, ↓reduceIte, decide_eq_false hh, Bool.false_eq_true, ↓reduceIte]
      exact hi
    · have hh : current.decode ≤ cap.decode := le_of_not_gt (fun hlt => hg ((compare_gt_iff hc hp).2 hlt))
      simp only [hg, ↓reduceIte, List.map_cons, decide_eq_true hh, ↓reduceIte]
      exact congrArg (current.decode :: ·) hi

lemma gridBits_length (k : ℕ) (current ratio cap : Fraction) :
    (gridBits k current ratio cap).1.length ≤ k := by
  induction k generalizing current with
  | zero => simp [gridBits]
  | succ k ih =>
    have hi := ih (multiplyFresh current ratio).1
    by_cases hg : (compare current cap).1 = Ordering.gt
    · simpa only [gridBits, hg, ↓reduceIte] using hi.trans (Nat.le_succ k)
    · simpa only [gridBits, hg, ↓reduceIte, List.length_cons] using Nat.succ_le_succ hi

/-- Polynomial binary running cost, including multiplication, comparisons and
list construction at every exponent. -/
theorem gridBits_cost (k : ℕ) (current ratio cap : Fraction) {a b c : ℕ}
    (hc : current.Width a) (hr : ratio.Width b) (hp : cap.Width c) :
    (gridBits k current ratio cap).2 ≤
      k*(2048*(a+2*b*k+b+c+2)^2+20)+1 := by
  induction k generalizing current a with
  | zero => simp [gridBits]
  | succ k ih =>
    have hi := ih (multiplyFresh current ratio).1 (multiplyFresh_width hc hr)
    have he : a+2*b+2*b*k+b+c+2 = a+2*b*(k+1)+b+c+2 := by ring
    rw [he] at hi
    let W := a+2*b*(k+1)+b+c+1
    have hca : a ≤ W := by dsimp [W]; omega
    have hcp : c ≤ W := by dsimp [W]; omega
    have hcmp := compare_cost ((show current.Width W from ⟨hc.1.trans hca, hc.2.trans hca⟩)) ((show cap.Width W from ⟨hp.1.trans hcp, hp.2.trans hcp⟩))
    have hmul := multiplyFresh_cost hc hr
    have hbase : a+b+1 ≤ W+1 := by dsimp [W]; omega
    have hpow := Nat.pow_le_pow_left hbase 2
    have hpow' := Nat.mul_le_mul_left 256 hpow
    have hstep : (compare current cap).2 + (multiplyFresh current ratio).2 + 8 ≤
        2048*(W+1)^2+20 := by nlinarith
    have hW : W+1 = a+2*b*(k+1)+b+c+2 := by rfl
    rw [hW] at hstep
    simp only [gridBits]
    rw [Nat.succ_mul]
    omega

/-- Refinement to the exact paper grid for arbitrary valid binary encodings of
its base, ratio and cap. Encoding generation is outside this routine's boundary. -/
theorem gridBits_refines (horizon : ℕ) (current ratio cap : Fraction)
    (hc : current.Valid) (hr : ratio.Valid) (hp : cap.Valid)
    (a δ upper : ℚ) (ha : current.decode = a) (hδ : ratio.decode = 1+δ)
    (hu : cap.decode = upper) :
    (gridBits (horizon+1) current ratio cap).1.map Fraction.decode =
      Grids.geometricGrid a δ upper horizon := by
  rw [gridBits_decode _ _ _ _ hc hr hp, ha, hδ, hu]
  rfl

lemma gridBits_valid (k : ℕ) (current ratio cap : Fraction)
    (hc : current.Valid) (hr : ratio.Valid) :
    ∀ x ∈ (gridBits k current ratio cap).1, x.Valid := by
  induction k generalizing current with
  | zero => simp [gridBits]
  | succ k ih =>
    have ht := ih (multiplyFresh current ratio).1 (multiplyFresh_valid hc hr)
    intro x hx
    simp only [gridBits] at hx
    split_ifs at hx
    · exact ht x hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hc
      · exact ht x hx

lemma gridBits_width (k : ℕ) (current ratio cap : Fraction) {a b : ℕ}
    (hc : current.Width a) (hr : ratio.Width b) :
    ∀ x ∈ (gridBits k current ratio cap).1, x.Width (a+2*b*k) := by
  induction k generalizing current a with
  | zero => simp [gridBits]
  | succ k ih =>
    have ht := ih (multiplyFresh current ratio).1 (multiplyFresh_width hc hr)
    have he : a+2*b+2*b*k = a+2*b*(k+1) := by ring
    rw [he] at ht
    intro x hx
    simp only [gridBits] at hx
    split_ifs at hx
    · exact ht x hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hc.1.trans (by omega), hc.2.trans (by omega)⟩
      · exact ht x hx

end BalancedAssortments.FPTASCostGrid
