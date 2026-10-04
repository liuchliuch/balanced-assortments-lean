import Mathlib

/-!
# Approximation inequalities used by the FPTAS

These are arithmetic lemmas, not a certification of a bit-polynomial algorithm.
The implementation-to-specification and bit-complexity obligations are separate.
-/
namespace BalancedAssortments.Approximation

/-- Fractional revenue expressed through its numerator and total sales. -/
noncomputable def revenue (numerator total : ℝ) : ℝ := numerator / (1 + total)

/-- The exact unrounded acceptance test. -/
theorem revenue_test {a w ρ : ℝ} (hw : 0 ≤ w) :
    ρ ≤ revenue a w ↔ ρ ≤ a - ρ * w := by
  unfold revenue
  rw [le_div_iff₀ (by positivity : 0 < 1 + w)]
  constructor <;> intro h <;> nlinarith

/-- Simultaneously shrinking every coordinate loses at most the shrink factor. -/
theorem uniform_shrink {a w t : ℝ} (ha : 0 ≤ a) (hw : 0 ≤ w)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * revenue a w ≤ revenue (t * a) (t * w) := by
  unfold revenue
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity : 0 < 1 + w)
    (by positivity : 0 < 1 + t * w)]
  have ht0 : 0 ≤ 1 - t := by linarith
  have h : 0 ≤ t * a * w * (1 - t) := by positivity
  nlinarith

/-- Coordinatewise rounding can be summarized by numerator and denominator bounds. -/
theorem downward_rounding {a b w z c : ℝ} (ha : 0 ≤ a)
    (hw : 0 ≤ w) (hz : 0 ≤ z) (hzw : z ≤ w) (hc : 0 < c)
    (hab : a / c ≤ b) : revenue a w / c ≤ revenue b z := by
  have hb : 0 ≤ b := le_trans (by positivity) hab
  have hnum : a ≤ b * c := (div_le_iff₀ hc).mp hab
  unfold revenue
  rw [div_div]
  apply (div_le_div_iff₀ (mul_pos (by positivity) hc) (by positivity)).2
  nlinarith [mul_nonneg hb (sub_nonneg.mpr hzw),
    mul_nonneg (sub_nonneg.mpr hnum) (show 0 ≤ 1 + z by positivity)]

/-- Coordinatewise rounding gives the aggregate revenue guarantee for nonnegative revenues. -/
theorem coordinate_rounding {ι : Type*} [Fintype ι] (r w y : ι → ℝ) {c : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i) (hy : ∀ i, 0 ≤ y i)
    (hc : 0 < c) (hdown : ∀ i, y i ≤ w i) (hnear : ∀ i, w i / c ≤ y i) :
    revenue (∑ i, r i * w i) (∑ i, w i) / c ≤
      revenue (∑ i, r i * y i) (∑ i, y i) := by
  apply downward_rounding
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hr i) (hw i))
  · exact Finset.sum_nonneg (fun i _ => hw i)
  · exact Finset.sum_nonneg (fun i _ => hy i)
  · exact Finset.sum_le_sum (fun i _ => hdown i)
  · exact hc
  · rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hnear i) (hr i)

/-- A common multiplicative band implies the pairwise BMS inequalities. -/
theorem common_band_balance {α τ x y : ℝ} (hα : 0 < α)
    (hx : τ ≤ x) (hy : y ≤ τ / α) : α * y ≤ x := by
  have : y * α ≤ τ := (le_div_iff₀ hα).mp hy
  nlinarith

/-- The slack inserted in the revenue test absorbs the knapsack loss. -/
theorem acceptance_slack {δ ρ p : ℝ} (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2)
    (hρ : 0 ≤ ρ) (hp : (1 - δ) * ((1 + 2 * δ) * ρ) ≤ p) : ρ ≤ p := by
  have hnon : 0 ≤ 1 - 2 * δ := by linarith
  have : 0 ≤ δ * (1 - 2 * δ) * ρ := by positivity
  nlinarith

/-- An algebraic version of the paper's final approximation-factor estimate. -/
theorem final_factor {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - ε ≤ 1 / ((1 + ε / 10) ^ 3 * (1 + 2 * (ε / 10))) := by
  have hd : 0 < (1 + ε / 10) ^ 3 * (1 + 2 * (ε / 10)) := by positivity
  rw [le_div_iff₀ hd]
  have h2 : ε ^ 2 ≤ ε := by nlinarith
  have h3 : ε ^ 3 ≤ ε := by nlinarith [mul_nonneg hε (show 0 ≤ 1 - ε by linarith)]
  have h4 : ε ^ 4 ≤ ε := by nlinarith [sq_nonneg (ε * (1 - ε))]
  have h5 : 0 ≤ ε ^ 5 := by positivity
  nlinarith

/-- Composition of the two discretization losses and the revenue-test losses. -/
theorem approximation_chain {opt disc alg δ : ℝ}
    (hd : 0 ≤ δ)
    (hdisc : opt / (1 + δ) ^ 2 ≤ disc)
    (halg : disc / ((1 + δ) * (1 + 2 * δ)) ≤ alg) :
    opt / ((1 + δ) ^ 3 * (1 + 2 * δ)) ≤ alg := by
  have hp : 0 < (1 + δ) * (1 + 2 * δ) := by positivity
  have h := (div_le_div_iff_of_pos_right hp).2 hdisc
  have he : opt / (1 + δ) ^ 2 / ((1 + δ) * (1 + 2 * δ)) =
      opt / ((1 + δ) ^ 3 * (1 + 2 * δ)) := by
    rw [div_div]
    congr 1
    ring
  rw [he] at h
  exact h.trans halg

end BalancedAssortments.Approximation
