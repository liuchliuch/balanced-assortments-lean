import Mathlib

/-! Real compact sales-space optimization. These results concern mathematical
attainment, not the computational complexity of solving the problem. -/
namespace BalancedAssortments.Optimization
noncomputable section
open Finset
variable {I : Type*} [Fintype I]

 def balanced (α : ℝ) (w : I → ℝ) : Prop :=
  ∀ i, w i = 0 ∨ ∀ j, α * w j ≤ w i
 def feasible (v : I → ℝ) (α K : ℝ) (w : I → ℝ) : Prop :=
  (∀ i, 0 ≤ w i ∧ w i ≤ v i) ∧ (∑ i, w i / v i) ≤ K ∧ balanced α w
 def revenue (r w : I → ℝ) : ℝ := (∑ i, r i * w i) / (1 + ∑ i, w i)

 theorem feasible_zero (v : I → ℝ) (hv : ∀ i, 0 ≤ v i) (α K : ℝ)
    (hK : 0 ≤ K) : feasible v α K (fun _ => 0) := by
  refine ⟨fun i => ⟨le_rfl, hv i⟩, ?_, fun i => Or.inl rfl⟩
  simpa using hK

 theorem feasible_closed (v : I → ℝ) (α K : ℝ) : IsClosed {w | feasible v α K w} := by
  have hc : IsClosed {w : I → ℝ | ∀ i, 0 ≤ w i ∧ w i ≤ v i} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    exact (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)
  have hr : IsClosed {w : I → ℝ | (∑ i, w i / v i) ≤ K} := by
    apply isClosed_le _ continuous_const
    exact continuous_finset_sum _ (fun i _ => (continuous_apply i).div_const _)
  have hb : IsClosed {w : I → ℝ | balanced α w} := by
    unfold balanced
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    apply IsClosed.union
    · exact isClosed_eq (continuous_apply i) continuous_const
    · change IsClosed {w : I → ℝ | ∀ j, α * w j ≤ w i}
      simp only [Set.setOf_forall]
      apply isClosed_iInter
      intro j
      exact isClosed_le (continuous_const.mul (continuous_apply j)) (continuous_apply i)
  exact hc.inter (hr.inter hb)

 theorem feasible_compact (v : I → ℝ) (α K : ℝ) : IsCompact {w | feasible v α K w} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : I => (0:ℝ)) v)).of_isClosed_subset
    (feasible_closed v α K)
  intro w hw
  exact ⟨fun i => (hw.1 i).1, fun i => (hw.1 i).2⟩

 theorem revenue_continuousOn (r v : I → ℝ) (α K : ℝ) :
    ContinuousOn (revenue r) {w | feasible v α K w} := by
  apply ContinuousOn.div
  · exact (continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_apply i))).continuousOn
  · exact (continuous_const.add (continuous_finset_sum _ (fun i _ => continuous_apply i))).continuousOn
  · intro w hw
    have : 0 ≤ ∑ i, w i := sum_nonneg fun i _ => (hw.1 i).1
    linarith

 theorem optimum_exists (r v : I → ℝ) (hv : ∀ i, 0 ≤ v i) (α K : ℝ)
    (hK : 0 ≤ K) : ∃ w, feasible v α K w ∧
      ∀ u, feasible v α K u → revenue r u ≤ revenue r w := by
  exact (feasible_compact v α K).exists_isMaxOn
    ⟨_, feasible_zero v hv α K hK⟩ (revenue_continuousOn r v α K)

 theorem balanced_scale {α c : ℝ} {w : I → ℝ}
    (hc : 0 ≤ c) (hb : balanced α w) : balanced α (fun i => c * w i) := by
  intro i
  rcases hb i with hi | hi
  · exact Or.inl (by simp [hi])
  · right
    intro j
    nlinarith [hi j]

 theorem revenue_scale_strict {r w : I → ℝ} {c : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hR : 0 < ∑ i, r i * w i) (hc : 1 < c) :
    revenue r w < revenue r (fun i => c * w i) := by
  have hW : 0 ≤ ∑ i, w i := sum_nonneg fun i _ => hw i
  have hsum : (∑ i, r i * (c * w i)) = c * ∑ i, r i * w i := by
    rw [mul_sum]; apply sum_congr rfl; intro i _; ring
  have hsumW : (∑ i, c * w i) = c * ∑ i, w i := by rw [mul_sum]
  unfold revenue
  rw [hsum, hsumW]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

 theorem singleton_feasible [DecidableEq I] (r v : I → ℝ) (j : I)
    (hv : ∀ i, 0 < v i) {α K : ℝ} (hα : α ≤ 1) (hK : 1 ≤ K) :
    feasible v α K (fun i => if i = j then v j else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with h
    · subst i; exact ⟨(hv j).le, le_rfl⟩
    · exact ⟨le_rfl, (hv i).le⟩
  · simpa [ite_div, Finset.sum_ite_eq', ne_of_gt (hv j)] using hK
  · intro i
    by_cases hi : i = j
    · subst i
      right
      intro k
      simp only [ite_true]
      split_ifs
      · nlinarith [hv j]
      · simp; exact (hv j).le
    · left; simp [hi]

 theorem optimum_positive [Nonempty I] (r v : I → ℝ)
    (hr : ∀ i, 0 < r i) (hv : ∀ i, 0 < v i) {α K : ℝ}
    (hα : α ≤ 1) (hK : 1 ≤ K) {w : I → ℝ}
    (hmax : ∀ u, feasible v α K u → revenue r u ≤ revenue r w) :
    0 < revenue r w := by
  classical
  obtain ⟨j⟩ := ‹Nonempty I›
  have h := hmax _ (singleton_feasible r v j hv hα hK)
  have hs : revenue r (fun i => if i = j then v j else 0) =
      r j * v j / (1 + v j) := by
    simp [revenue, mul_ite, Finset.sum_ite_eq']
  rw [hs] at h
  exact lt_of_lt_of_le (div_pos (mul_pos (hr j) (hv j)) (by linarith [hv j])) h

 /-- The lower scale bound follows directly by scaling to vmin/n. This does not
 assume an unproved cap-tightness characterization. -/
 theorem maximum_lower_bound [Nonempty I] (r v w : I → ℝ)
    {α K vmin M : ℝ} (hK : 1 ≤ K) (hvmin : 0 < vmin)
    (hv : ∀ i, vmin ≤ v i) (hw : feasible v α K w)
    (hR : 0 < ∑ i, r i * w i) (hM : 0 < M) (hupper : ∀ i, w i ≤ M)
    (hmax : ∀ u, feasible v α K u → revenue r u ≤ revenue r w) :
    vmin / Fintype.card I ≤ M := by
  by_contra hn
  have hn : M < vmin / Fintype.card I := lt_of_not_ge hn
  have hnNat : 0 < Fintype.card I := Fintype.card_pos
  have hnReal : (0 : ℝ) < Fintype.card I := by exact_mod_cast hnNat
  have hnOne : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast hnNat
  let c := (vmin / Fintype.card I) / M
  have hc : 1 < c := (lt_div_iff₀ hM).2 (by simpa using hn)
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcM : c * M = vmin / Fintype.card I := by dsimp [c]; field_simp
  have hscaled : ∀ i, c * w i ≤ vmin / Fintype.card I := by
    intro i
    calc c * w i ≤ c * M := mul_le_mul_of_nonneg_left (hupper i) hc0.le
         _ = _ := hcM
  have hC : vmin / (Fintype.card I : ℝ) ≤ vmin := by
    apply (div_le_iff₀ hnReal).2
    nlinarith
  have hfeas : feasible v α K (fun i => c * w i) := by
    refine ⟨fun i => ⟨mul_nonneg hc0.le (hw.1 i).1, (hscaled i).trans (hC.trans (hv i))⟩, ?_,
      balanced_scale hc0.le hw.2.2⟩
    have hterms : ∀ i, c * w i / v i ≤ 1 / (Fintype.card I : ℝ) := by
      intro i
      have hvi : 0 < v i := hvmin.trans_le (hv i)
      apply (div_le_div_iff₀ hvi hnReal).2
      have hh := (le_div_iff₀ hnReal).1 (hscaled i)
      nlinarith [hv i]
    calc (∑ i, c * w i / v i) ≤ ∑ _ : I, 1 / (Fintype.card I : ℝ) :=
          sum_le_sum fun i _ => hterms i
         _ = 1 := by simp [ne_of_gt hnReal]
         _ ≤ K := hK
  exact (not_lt_of_ge (hmax _ hfeas))
    (revenue_scale_strict (fun i => (hw.1 i).1) hR hc)
/-- An attained optimum with the exact scale range of Lemma 7. The witnesses
 `imin` and `imaxv` name the minimum and maximum attractiveness, and `imaxw`
 names the maximum sales coordinate. -/
theorem scale_range [Nonempty I] (r v : I → ℝ)
    (hr : ∀ i, 0 < r i) (hv : ∀ i, 0 < v i) {α K : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hK : 1 ≤ K) :
    ∃ w : I → ℝ, ∃ imin imaxv imaxw : I,
      feasible v α K w ∧
      (∀ u, feasible v α K u → revenue r u ≤ revenue r w) ∧
      (∀ i, v imin ≤ v i) ∧ (∀ i, v i ≤ v imaxv) ∧
      (∀ i, w i ≤ w imaxw) ∧
      α * v imin / Fintype.card I ≤ α * w imaxw ∧
      α * w imaxw ≤ α * v imaxv := by
  classical
  obtain ⟨w, hw, hmax⟩ := optimum_exists r v (fun i => (hv i).le) α K (by linarith)
  obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  obtain ⟨imaxv, _, hmaxv⟩ := Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  obtain ⟨imaxw, _, hmaxw⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  have hpos := optimum_positive r v hr hv hα1 hK hmax
  have hden : 0 < 1 + ∑ i, w i := by
    have := sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hw.1 i).1)
    linarith
  have hR : 0 < ∑ i, r i * w i := (div_pos_iff_of_pos_right hden).mp hpos
  have hM : 0 < w imaxw := by
    by_contra hn
    have hM0 : w imaxw ≤ 0 := le_of_not_gt hn
    have : (∑ i, r i * w i) ≤ 0 := sum_nonpos fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (hr i).le ((hmaxw i (mem_univ i)).trans hM0)
    linarith
  have hlo := maximum_lower_bound r v w hK (hv imin)
    (fun i => hmin i (mem_univ i)) hw hR hM (fun i => hmaxw i (mem_univ i)) hmax
  refine ⟨w, imin, imaxv, imaxw, hw, hmax, (fun i => hmin i (mem_univ i)),
    (fun i => hmaxv i (mem_univ i)), (fun i => hmaxw i (mem_univ i)), ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hlo hα.le
    simpa [mul_div_assoc] using this
  · exact mul_le_mul_of_nonneg_left ((hw.1 imaxw).2.trans (hmaxv _ (mem_univ _))) hα.le
end
end BalancedAssortments.Optimization
