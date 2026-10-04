import BalancedAssortments.FPTASOptimal
import BalancedAssortments.ApproximationCandidate
import BalancedAssortments.FPTASPolicy

namespace BalancedAssortments.FPTAS

/-- The revenue grid used by the executable wrapper has a predecessor at the
required slackened discrete revenue, with the precise multiplicative loss. -/
theorem revenue_grid_predecessor {n : ℕ} (d : Input n) (hd : Valid d)
    {δ F : ℚ} (hδ : 0 < δ) (hF : F ≤ rmax d)
    (hL : singletonValue d ≤ F / (1 + 2*δ)) :
    ∃ ρ ∈ revenues d δ,
      0 < ρ ∧ (1 + 2*δ)*ρ ≤ F ∧
      F / ((1+2*δ)*(1+δ)) < ρ := by
  have hLpos := singletonValue_pos d hd.1
  have hD : (0 : ℚ) < 1 + 2*δ := by linarith
  have hFpos : 0 < F := by
    have : 0 < F / (1 + 2*δ) := hLpos.trans_le hL
    exact (div_pos_iff_of_pos_right hD).mp this
  have hx : F / (1+2*δ) ≤ rmax d := by
    apply le_trans _ hF
    apply (div_le_iff₀ hD).2
    nlinarith
  obtain ⟨ρ, hm, hlo, hhi⟩ := GridBounds.explicit_grid_round hLpos hδ hL hx
  have hρ : 0 < ρ := hLpos.trans_le (Grids.grid_lower_bound hLpos.le hδ.le hm)
  refine ⟨ρ, hm, hρ, ?_, ?_⟩
  · have := (le_div_iff₀ hD).mp hlo
    nlinarith
  · have he : F / ((1+2*δ)*(1+δ)) = (F / (1+2*δ)) / (1+δ) := by field_simp
    rw [he]
    exact (div_lt_iff₀ (by linarith : (0:ℚ)<1+δ)).2 (by nlinarith)

theorem candidate_mem_raw {n : ℕ} (d : Input n) {ε τ ρ : ℚ}
    (hτ : τ ∈ scales d (ε/10)) (hρ : ρ ∈ revenues d (ε/10))
    {z : Fin (n+1) → ℚ} (hz : candidateAt d (ε/10) τ ρ = some z) :
    z ∈ rawCandidates d ε := by
  unfold rawCandidates
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨τ, hτ, ?_⟩
  exact List.mem_filterMap.mpr ⟨ρ, hρ, hz⟩

theorem candidate_success_improves {n : ℕ} (d : Input n) {ε τ ρ : ℚ}
    (hτ : τ ∈ scales d (ε/10)) (hρ : ρ ∈ revenues d (ε/10))
    {z : Fin (n+1) → ℚ} (hz : candidateAt d (ε/10) τ ρ = some z)
    (hf : Feasible d z) (hr : ρ ≤ revenue d z) :
    ρ ≤ revenue d (runSales d ε) :=
  hr.trans (runSales_dominates d ε (candidate_mem_raw d hτ hρ hz) hf)

/-- The actual executable rational sales algorithm attains the requested ratio
against EVERY feasible real sales vector. This is the mathematical approximation
and exact-feasibility guarantee; bit-operation runtime is a separate theorem. -/
theorem runSales_approximation {n : ℕ} (d : Input n) (hd : Valid d) (ε : ℚ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ u : Fin (n+1) → ℝ,
      Optimization.feasible (fun i => (d.v i : ℝ)) d.α d.K u →
      (1 - (ε : ℝ)) * Optimization.revenue (fun i => (d.r i : ℝ)) u ≤
        (revenue d (runSales d ε) : ℝ) := by
  let δ : ℚ := ε/10
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ2 : δ ≤ 1/2 := by dsimp [δ]; linarith
  obtain ⟨w, hw, hmax, τ, hτmem, y, hy, hyf, hyrev⟩ := discrete_candidate_exists d hd hδ
  have hFnon : 0 ≤ revenue d y := by
    unfold revenue
    apply div_nonneg
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (hd.1 i).1.le (hyf.1 i).1
    · have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hyf.1 i).1)
      linarith
  have halgQ : revenue d y / ((1+δ)*(1+2*δ)) ≤ revenue d (runSales d ε) := by
    by_cases hL : singletonValue d ≤ revenue d y / (1+2*δ)
    · obtain ⟨ρ, hρmem, hρ, hρF, hnear⟩ := revenue_grid_predecessor d hd hδ
        (revenue_le_rmax d y (fun i => (hyf.1 i).1)) hL
      have ha : 0 ≤ d.α * vmin d / (n+1 : ℚ) := by
        exact div_nonneg (mul_nonneg hd.2.1.le (vmin_pos d (fun i => (hd.1 i).2)).le) (by positivity)
      have hτ : 0 ≤ τ := ha.trans (Grids.grid_lower_bound ha hδ.le hτmem)
      obtain ⟨z, hz, hzf, hzρ⟩ := ApproximationCandidate.candidateAt_success hd hδ hδ2 hτ hρ y hyf hy hρF
      have ha := candidate_success_improves d hτmem hρmem hz hzf hzρ
      have hn : revenue d y / ((1+δ)*(1+2*δ)) ≤ ρ := by simpa [mul_comm] using hnear.le
      exact hn.trans ha
    · have hsmall : revenue d y / (1+2*δ) ≤ revenue d (runSales d ε) :=
        (le_of_lt (lt_of_not_ge hL)).trans (runSales_ge_singletonValue d hd ε)
      have hdown : (revenue d y / (1+2*δ)) / (1+δ) ≤ revenue d y / (1+2*δ) :=
        div_le_self (div_nonneg hFnon (by linarith)) (by linarith)
      have he : (revenue d y / (1+2*δ)) / (1+δ) = revenue d y / ((1+δ)*(1+2*δ)) := by
        rw [div_div]; ring
      rw [he] at hdown
      exact hdown.trans hsmall
  have hδR : (0 : ℝ) ≤ δ := by exact_mod_cast hδ.le
  have halgR : (revenue d y : ℝ) / ((1+(δ:ℝ))*(1+2*(δ:ℝ))) ≤
      (revenue d (runSales d ε) : ℝ) := by exact_mod_cast halgQ
  have hchain := Approximation.approximation_chain hδR hyrev halgR
  have heR : (0 : ℝ) ≤ ε := by exact_mod_cast hε.le
  have heR1 : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1.le
  have hfactor := Approximation.final_factor heR heR1
  have hopt : 0 ≤ Optimization.revenue (fun i => (d.r i : ℝ)) w := by
    apply le_of_lt
    apply Optimization.optimum_positive (fun i => (d.r i : ℝ)) (fun i => (d.v i : ℝ)) (α := (d.α : ℝ)) (K := (d.K : ℝ)) (w := w)
    · intro i; dsimp only; exact_mod_cast (hd.1 i).1
    · intro i; dsimp only; exact_mod_cast (hd.1 i).2
    · exact_mod_cast hd.2.2.1
    · exact_mod_cast hd.2.2.2.1
    · exact hmax
  intro u hu
  calc (1-(ε:ℝ)) * Optimization.revenue (fun i => (d.r i : ℝ)) u
      ≤ (1-(ε:ℝ)) * Optimization.revenue (fun i => (d.r i : ℝ)) w :=
        mul_le_mul_of_nonneg_left (hmax u hu) (by linarith)
    _ ≤ Optimization.revenue (fun i => (d.r i : ℝ)) w /
        ((1+(δ:ℝ))^3*(1+2*(δ:ℝ))) := by
      have h := mul_le_mul_of_nonneg_right hfactor hopt
      simpa [δ, div_eq_mul_inv, mul_comm] using h
    _ ≤ _ := hchain

/-- End-to-end guarantee against every feasible original randomized MNL policy.
The output is the actual executable rational `runPolicy`, whose exact legality
and linear support bound are established in `runPolicy_valid`. -/
theorem runPolicy_approximation {n : ℕ} (d : Input n) (hd : Valid d) (ε : ℚ)
    (hε : 0 < ε) (hε1 : ε < 1) {A : Type*} [Fintype A]
    (S : A → Finset (Fin (n+1))) (q : A → ℝ) (hq : Sales.Distribution q)
    (hK : ∀ a, (S a).card ≤ d.K)
    (hb : Sales.Balanced (d.α : ℝ) (Sales.sales (fun i => (d.v i : ℝ)) S q)) :
    (1 - (ε : ℝ)) * Sales.revenue (fun i => (d.r i : ℝ))
      (Sales.sales (fun i => (d.v i : ℝ)) S q) ≤
      Sales.revenue (fun i => (d.r i : ℝ)) (policySales d.v (runPolicy d ε)) := by
  have hv : ∀ i, (0 : ℝ) < d.v i := fun i => by exact_mod_cast (hd.1 i).2
  obtain ⟨w, hw, hs⟩ := Sales.policy_to_compact (fun i => (d.v i : ℝ)) hv S hq d.K hK
  have hbw : Sales.Balanced (d.α : ℝ) w := by
    rw [hs] at hb
    exact (Sales.compact_balance (d.α : ℝ) w (fun i => (hw.1 i).1)).mp hb
  have hfeas := (Sales.optimization_feasible_iff (fun i => (d.v i : ℝ)) w d.α d.K).mpr ⟨hw, hbw⟩
  have hh := runSales_approximation d hd ε hε hε1 w hfeas
  rw [hs, Sales.compact_revenue, (runPolicy_balance_revenue d ε (fun i => (hd.1 i).2)).2]
  exact hh
end BalancedAssortments.FPTAS
