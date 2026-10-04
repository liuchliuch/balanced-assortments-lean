import Mathlib

/-! Exact real-variable certificate for Proposition 6 and its appendix.
The coordinates below are products 1, 2, 3 in the source order.
This file proves the compact-model counterexample without assuming an LP oracle.
-/
namespace BalancedAssortments.Counterexample

def Feasible (a b c : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a ≤ 3 ∧ b ≤ 2 ∧ c ≤ 14 ∧
  a / 3 + b / 2 + c / 14 ≤ 2 ∧
  (a = 0 ∨ (b ≤ 6 * a ∧ c ≤ 6 * a)) ∧
  (b = 0 ∨ (a ≤ 6 * b ∧ c ≤ 6 * b)) ∧
  (c = 0 ∨ (a ≤ 6 * c ∧ b ≤ 6 * c))

noncomputable def revenue (a b c : ℝ) : ℝ := (65 * a + 80 * b + 64 * c) / (1 + a + b + c)

lemma denom_pos {a b c : ℝ} (h : Feasible a b c) : 0 < 1 + a + b + c := by
  rcases h with ⟨ha, hb, hc, _⟩
  linarith

lemma full_support_certificate {a b c : ℝ} (h : Feasible a b c) (ha : a ≠ 0) :
    686 * a + 3611 * b + 491 * c ≤ 11989 := by
  rcases h with ⟨_, _, _, _, hb, _, hr, hbal, _⟩
  have hca : c ≤ 6 * a := (hbal.resolve_left ha).2
  linarith

lemma full_support_bound {a b c : ℝ} (h : Feasible a b c) (ha : a ≠ 0) :
    revenue a b c ≤ 11989 / 195 := by
  have hd := denom_pos h
  have hc := full_support_certificate h ha
  unfold revenue
  apply (div_le_iff₀ hd).2
  linarith

lemma optimum_feasible : Feasible 0 2 12 := by norm_num [Feasible]
lemma optimum_value : revenue 0 2 12 = 928 / 15 := by norm_num [revenue]

/-- The appendix certificate actually gives a strict bound whenever product 1 is active. -/
theorem global_bound {a b c : ℝ} (h : Feasible a b c) : revenue a b c ≤ 928 / 15 := by
  by_cases ha : a = 0
  · subst a
    have hd := denom_pos h
    rcases h with ⟨_, hb0, hc0, _, hb, hc, _, _, hbal, _⟩
    unfold revenue
    apply (div_le_iff₀ hd).2
    rcases hbal with hzero | ⟨_, hcb⟩
    · subst b; nlinarith
    · nlinarith
  · have hu := full_support_bound h ha
    linarith

/-- The optimizing vector itself, and thus its positive support, is unique. -/
theorem unique_optimizer {a b c : ℝ} (h : Feasible a b c)
    (heq : revenue a b c = 928 / 15) : a = 0 ∧ b = 2 ∧ c = 12 := by
  have ha : a = 0 := by
    by_contra hn
    have hu := full_support_bound h hn
    linarith
  subst a
  have hd := denom_pos h
  have hv := (div_eq_iff hd.ne').1 heq
  rcases h with ⟨_, hb0, hc0, _, hb, hc, _, _, hbal, _⟩
  change 65 * 0 + 80 * b + 64 * c = (928 / 15) * (1 + 0 + b + c) at hv
  rcases hbal with hzero | ⟨_, hcb⟩
  · subst b; nlinarith
  · constructor
    · rfl
    · constructor <;> nlinarith

/-- Every northeast rectangle containing products 2 and 3 also contains 1. -/
theorem rectangle_obstruction (rbar vbar : ℝ)
    (h2 : rbar ≤ 80 ∧ vbar ≤ 2) (h3 : rbar ≤ 64 ∧ vbar ≤ 14) :
    rbar ≤ 65 ∧ vbar ≤ 3 := by constructor <;> linarith [h2.2, h3.1]

/-- Exact singleton and pair maxima from the appendix, as upper bounds. -/
lemma singleton_one_bound {a : ℝ} (h : Feasible a 0 0) : revenue a 0 0 ≤ 195 / 4 := by
  have hd := denom_pos h
  have ha := h.2.2.2.1
  unfold revenue
  apply (div_le_iff₀ hd).2
  linarith

lemma singleton_two_bound {b : ℝ} (h : Feasible 0 b 0) : revenue 0 b 0 ≤ 160 / 3 := by
  have hd := denom_pos h
  have hb := h.2.2.2.2.1
  unfold revenue
  apply (div_le_iff₀ hd).2
  linarith

lemma singleton_three_bound {c : ℝ} (h : Feasible 0 0 c) : revenue 0 0 c ≤ 896 / 15 := by
  have hd := denom_pos h
  have hc := h.2.2.2.2.2.1
  unfold revenue
  apply (div_le_iff₀ hd).2
  linarith

lemma pair_one_two_bound {a b : ℝ} (h : Feasible a b 0) : revenue a b 0 ≤ 355 / 6 := by
  have hd := denom_pos h
  have ha := h.2.2.2.1
  have hb := h.2.2.2.2.1
  unfold revenue
  apply (div_le_iff₀ hd).2
  linarith

lemma pair_one_three_bound {a c : ℝ} (h : Feasible a 0 c) : revenue a 0 c ≤ 1091 / 18 := by
  have hd := denom_pos h
  have ha := h.2.2.2.1
  have hc := h.2.2.2.2.2.1
  unfold revenue
  apply (div_le_iff₀ hd).2
  linarith

lemma appendix_table_attainment :
    (Feasible 3 0 0 ∧ revenue 3 0 0 = 195 / 4) ∧
    (Feasible 0 2 0 ∧ revenue 0 2 0 = 160 / 3) ∧
    (Feasible 0 0 14 ∧ revenue 0 0 14 = 896 / 15) ∧
    (Feasible 3 2 0 ∧ revenue 3 2 0 = 355 / 6) ∧
    (Feasible 3 0 14 ∧ revenue 3 0 14 = 1091 / 18) := by
  norm_num [Feasible, revenue]

/-- A northeast threshold rectangle cannot have exactly the unique optimal support. -/
theorem optimal_support_not_rectangle : ¬ ∃ rbar vbar : ℝ,
    (¬ (rbar ≤ 65 ∧ vbar ≤ 3)) ∧ (rbar ≤ 80 ∧ vbar ≤ 2) ∧
      (rbar ≤ 64 ∧ vbar ≤ 14) := by
  rintro ⟨rbar, vbar, hn, h2, h3⟩
  exact hn (rectangle_obstruction rbar vbar h2 h3)

lemma full_support_attains :
    Feasible (21 / 16) 2 (63 / 8) ∧ revenue (21 / 16) 2 (63 / 8) = 11989 / 195 := by
  norm_num [Feasible, revenue]

/-- The two explicitly listed policy probabilities sum to one. -/
lemma policy_mass : (34 / 35 : ℚ) + 1 / 35 = 1 := by norm_num

/-- MNL denominator tilt of the appendix policy gives x0=1/15, x2=2/15, x3=12/15. -/
lemma policy_sales :
    (34 / 35 : ℚ) / (1 + 2 + 14) + (1 / 35) / (1 + 2) = 1 / 15 ∧
    (34 / 35 : ℚ) * 2 / (1 + 2 + 14) + (1 / 35) * 2 / (1 + 2) = 2 / 15 ∧
    (34 / 35 : ℚ) * 14 / (1 + 2 + 14) = 12 / 15 := by norm_num

end BalancedAssortments.Counterexample
