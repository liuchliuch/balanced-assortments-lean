import BalancedAssortments.FixedSupportCandidatePrefix
import BalancedAssortments.FixedSupportAlgorithmScaleDominance
import BalancedAssortments.FixedSupportAlgorithmDomain

/-! Exact correctness of the executed finite prescribed-support solver against
all real feasible vectors. No rational-optimum or LP-oracle premise is used. -/
namespace BalancedAssortments.FixedSupportAlgorithm
open scoped BigOperators

private theorem target_profit_iff {n : ℕ} (r w : Fin n → ℝ) (ρ : ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    ρ ≤ FixedSupportReal.revenue r w ↔ ρ ≤ ∑ i, (r i-ρ)*w i := by
  have hd := FixedSupportReal.denominator_pos w hw
  unfold FixedSupportReal.revenue
  rw [le_div_iff₀ hd]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  constructor <;> intro h <;> nlinarith

theorem realRevenue_cast {n : ℕ} (r w : Fin n → ℚ) :
    FixedSupportReal.revenue (fun i => (r i : ℝ)) (fun i => (w i : ℝ)) =
      (fractionalRevenue r w : ℝ) := by
  simp [FixedSupportReal.revenue, fractionalRevenue]

private theorem real_revenue_bounds {n : ℕ} (r : Fin n → ℚ) (hr : ∀ i, 0 ≤ r i)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ FixedSupportReal.revenue (fun i => (r i : ℝ)) w ∧
      FixedSupportReal.revenue (fun i => (r i : ℝ)) w ≤ (revenueUpper r : ℝ) := by
  have hd := FixedSupportReal.denominator_pos w hw
  have hsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hR : (0 : ℝ) ≤ (revenueUpper r : ℝ) := by exact_mod_cast revenueUpper_nonneg r
  constructor
  · apply div_nonneg _ hd.le
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (by dsimp only; exact_mod_cast hr i) (hw i))
  · have hnum : (∑ i, (r i : ℝ)*w i) ≤ (revenueUpper r : ℝ)*(∑ i, w i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast revenue_le_upper r i) (hw i)
    unfold FixedSupportReal.revenue
    apply (div_le_iff₀ hd).2
    nlinarith

/-- The selected executable output is feasible for the actual real closed
prescribed-support polytope. -/
theorem optimize_feasible {n : ℕ} (hn : 0 < n) (r v : Fin n → ℚ)
    (hv : ∀ i, 0 < v i) {α K : ℚ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 < K) :
    FixedSupportReal.Feasible (fun i => (v i : ℝ)) (α : ℝ) (K : ℝ)
      (fun i => (optimize r v α K i : ℝ)) := by
  have hm := (mem_candidates r v α K _).1 (bestCandidate_mem r v α K)
  have ht := scaleSamples_bounds r v α K _ (scaleUpper_pos hn v hv hK).le hm.2
  have hh := candidateVector_feasible r v hv hα hα1 hK.le ht.1 ht.2
    (ρ := (bestCandidate r v α K).1)
  simpa only [optimize, Prod.mk.eta] using hh

/-- The actual finite rational candidate algorithm is globally optimal against
EVERY real feasible vector, rather than only against its enumerated candidates. -/
theorem optimize_optimal {n : ℕ} (hn : 0 < n) (r v : Fin n → ℚ)
    (hr : ∀ i, 0 < r i) (hv : ∀ i, 0 < v i)
    {α K : ℚ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 < K)
    (w : Fin n → ℝ) (hw : FixedSupportReal.Feasible (fun i => (v i : ℝ)) (α : ℝ) (K : ℝ) w) :
    FixedSupportReal.revenue (fun i => (r i : ℝ)) w ≤
      (fractionalRevenue r (optimize r v α K) : ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hvR : ∀ i, (0 : ℝ) < (v i : ℝ) := fun i => by exact_mod_cast hv i
  have hαR : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  let ρ := FixedSupportReal.revenue (fun i => (r i : ℝ)) w
  have hρ := real_revenue_bounds r (fun i => (hr i).le) w (fun i => (hw.1 i).1)
  obtain ⟨q, hqmem, hq⟩ := scoreSamples_cover_real r v hρ
  obtain ⟨t, z, hz, hzw⟩ := FixedSupportKnapsack.fixed_to_scale
    (fun i => (v i : ℝ)) w hvR hαR hw
  have hdom := FixedSupportKnapsack.scaleFeasible_domain (fun i => (v i : ℝ)) hvR hαR hz
  have ht := (real_scaleDomain_iff hn v hv K t).1 hdom
  have hT := (scaleUpper_pos hn v hv hK).le
  obtain ⟨u, humem, hu⟩ := scaleSamples_dominate_real r v ρ hv hα hα1 hT ht (q := q)
  have hub := scaleSamples_bounds r v α K q hT humem
  have hdomu := (real_scaleDomain_iff hn v hv K (u : ℝ)).2 (by exact_mod_cast hub)
  have hbase : ρ ≤ ∑ i, ((r i : ℝ)-ρ)*w i :=
    (target_profit_iff _ w ρ (fun i => (hw.1 i).1)).1 le_rfl
  have hgreedy := realCandidate_transformed_optimal r v α K q ρ t hq z hz
  rw [hzw] at hgreedy
  rw [prefixObjective_eq_candidate r v α K q ρ t hv hα hα1 hdom,
    prefixObjective_eq_candidate r v α K q ρ (u : ℝ) hv hα hα1 hdomu,
    realCandidateVector_cast] at hu
  have htarget := hbase.trans (hgreedy.trans hu)
  have huf := candidateVector_feasible r v hv hα hα1 hK.le hub.1 hub.2 (ρ := q)
  have hrev := (target_profit_iff (fun i => (r i : ℝ))
    (fun i => (candidateVector r v α K (q,u) i : ℝ)) ρ (fun i => (huf.1 i).1)).2 htarget
  rw [realRevenue_cast] at hrev
  have hmem := (mem_candidates r v α K (q,u)).2 ⟨hqmem, humem⟩
  have hbest : (fractionalRevenue r (candidateVector r v α K (q,u)) : ℝ) ≤
      (fractionalRevenue r (optimize r v α K) : ℝ) := by
    exact_mod_cast optimize_dominates_candidates r v α K hmem
  exact hrev.trans hbest

/-- Positive data and a positive budget make the exact optimal output positive
on every prescribed coordinate, so the closed-polytope zero point does not
weaken the paper's exact-active-support requirement. -/
theorem optimize_exact_support {n : ℕ} (hn : 0 < n) (r v : Fin n → ℚ)
    (hr : ∀ i, 0 < r i) (hv : ∀ i, 0 < v i)
    {α K : ℚ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 < K) :
    ∀ i, 0 < optimize r v α K i := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hT : (0 : ℝ) < (scaleUpper v K : ℝ) := by exact_mod_cast scaleUpper_pos hn v hv hK
  let t : ℝ := (scaleUpper v K : ℝ)/2
  have ht : 0 < t := by dsimp [t]; positivity
  have hvR : ∀ i, (0 : ℝ) < (v i : ℝ) := fun i => by exact_mod_cast hv i
  have hαR : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hαR1 : (α : ℝ) ≤ 1 := by exact_mod_cast hα1
  have hd := (real_scaleDomain_iff hn v hv K t).2 ⟨ht.le, by dsimp [t]; linarith⟩
  have hz := FixedSupportKnapsack.domain_zero_feasible (fun i => (v i : ℝ)) hvR hαR hαR1 hd
  have hw := FixedSupportKnapsack.scale_to_fixed (fun i => (v i : ℝ)) hvR hαR hz
  let w := FixedSupportKnapsack.reconstruct (fun i => (v i : ℝ)) t (fun _ => 0)
  have hwpos : ∀ i, 0 < w i := by intro i; simpa [w, FixedSupportKnapsack.reconstruct] using ht
  have hnum : 0 < ∑ i, (r i : ℝ)*w i :=
    Finset.sum_pos (fun i _ => mul_pos (by exact_mod_cast hr i) (hwpos i)) Finset.univ_nonempty
  have hrev : 0 < FixedSupportReal.revenue (fun i => (r i : ℝ)) w :=
    div_pos hnum (FixedSupportReal.denominator_pos w (fun i => (hwpos i).le))
  have hopt := optimize_optimal hn r v hr hv hα hα1 hK w hw
  have hoptf := optimize_feasible hn r v hv hα hα1 hK
  have hoptr : 0 < FixedSupportReal.revenue (fun i => (r i : ℝ))
      (fun i => (optimize r v α K i : ℝ)) := by rw [realRevenue_cast]; exact hrev.trans_le hopt
  have hoptN := (div_pos_iff_of_pos_right
    (FixedSupportReal.denominator_pos _ (fun i => (hoptf.1 i).1))).1 hoptr
  have hpositive := FixedSupportReal.positive_objective_exact_support
    (fun i => (r i : ℝ)) (fun i => (optimize r v α K i : ℝ)) (α : ℝ)
    hαR (fun i => (hoptf.1 i).1) hoptf.2.2 hoptN
  intro i
  have hh := hpositive i
  dsimp only at hh
  exact_mod_cast hh

end BalancedAssortments.FixedSupportAlgorithm
