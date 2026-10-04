import BalancedAssortments.FPTASBounds
import BalancedAssortments.Optimization
import BalancedAssortments.ApproximationDiscretization

namespace BalancedAssortments.FPTAS
open Finset

theorem options_feasible {n : ℕ} (d : Input n) (hd : Valid d) {δ τ : ℚ}
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (y : Fin (n+1) → ℚ)
    (hy : ∀ i, y i ∈ Grids.productOptions τ δ d.α (d.v i)
      (GridBounds.gridHorizon τ δ (min (d.v i) (τ / d.α))))
    (hrank : (∑ i, y i / d.v i) ≤ d.K) : Feasible d y := by
  have hb := fun i => Grids.option_band hτ.le hδ (hy i)
  have hn : ∀ i, 0 ≤ y i := by
    intro i; rcases hb i with hz | hp
    · simp [hz]
    · exact hτ.le.trans hp.1
  refine ⟨?_, hrank, ?_⟩
  · intro i; refine ⟨hn i, ?_⟩
    rcases hb i with hz | hp
    · simpa [hz] using (hd.1 i).2.le
    · exact hp.2.1
  · intro i
    rcases hb i with hz | hp
    · exact Or.inl hz
    · right; intro j
      rcases hb j with hz | hj
      · simpa [hz] using hn i
      · have h := (le_div_iff₀ hd.2.1).mp hj.2.2
        nlinarith [hp.1]

/-- Lemma 8 for the actual input and actual scale/option enumerators. The
reference optimum is over all real feasible vectors, not merely rational ones. -/
theorem discrete_candidate_exists {n : ℕ} (d : Input n) (hd : Valid d) {δ : ℚ}
    (hδ : 0 < δ) :
    ∃ w : Fin (n+1) → ℝ,
      Optimization.feasible (fun i => (d.v i : ℝ)) d.α d.K w ∧
      (∀ u, Optimization.feasible (fun i => (d.v i : ℝ)) d.α d.K u →
        Optimization.revenue (fun i => (d.r i : ℝ)) u ≤
          Optimization.revenue (fun i => (d.r i : ℝ)) w) ∧
      ∃ τ ∈ scales d δ, ∃ y : Fin (n+1) → ℚ,
        (∀ i, y i ∈ Grids.productOptions τ δ d.α (d.v i)
          (GridBounds.gridHorizon τ δ (min (d.v i) (τ / d.α)))) ∧
        Feasible d y ∧
        Optimization.revenue (fun i => (d.r i : ℝ)) w / (1 + (δ : ℝ))^2 ≤
          (revenue d y : ℝ) := by
  have hr : ∀ i, (0 : ℝ) < d.r i := fun i => by exact_mod_cast (hd.1 i).1
  have hv : ∀ i, (0 : ℝ) < d.v i := fun i => by exact_mod_cast (hd.1 i).2
  have hα : (0 : ℝ) < d.α := by exact_mod_cast hd.2.1
  have hα1 : (d.α : ℝ) ≤ 1 := by exact_mod_cast hd.2.2.1
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast hd.2.2.2.1
  obtain ⟨w, imin, imaxv, imaxw, hw, hmax, hminv, hmaxv, hmaxw, hlo, hhi⟩ :=
    Optimization.scale_range (fun i => (d.r i : ℝ)) (fun i => (d.v i : ℝ)) hr hv hα hα1 hK
  let a : ℚ := d.α * vmin d / (n+1)
  let cap : ℚ := d.α * vmax d
  let τstar : ℝ := (d.α : ℝ) * w imaxw
  have ha : 0 < a := div_pos (mul_pos hd.2.1 (vmin_pos d (fun i => (hd.1 i).2))) (by positivity)
  have hslo : (a : ℝ) ≤ τstar := by
    have hvm : (vmin d : ℝ) ≤ d.v imin := by exact_mod_cast vmin_le d imin
    have hmul := mul_le_mul_of_nonneg_left hvm hα.le
    have hdiv := div_le_div_of_nonneg_right hmul (show (0 : ℝ) ≤ n+1 by positivity)
    dsimp [a, τstar]
    push_cast
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hlo
    exact hdiv.trans hlo
  have hshi : τstar ≤ (cap : ℝ) := by
    have hvm : (d.v imaxv : ℝ) ≤ vmax d := by exact_mod_cast le_vmax d imaxv
    have hmul := mul_le_mul_of_nonneg_left hvm hα.le
    exact hhi.trans (by simpa [cap] using hmul)
  have hband : ∀ i, w i = 0 ∨ τstar ≤ w i ∧ w i ≤ τstar / (d.α : ℝ) := by
    intro i
    rcases hw.2.2 i with hz | hp
    · exact Or.inl hz
    · refine Or.inr ⟨hp imaxw, ?_⟩
      have he : τstar / (d.α : ℝ) = w imaxw := by dsimp [τstar]; field_simp
      rw [he]; exact hmaxw i
  obtain ⟨τ, hτmem, y, hy, hyw, hyrev⟩ :=
    ApproximationDiscretization.scale_discretization (fun i => (d.r i : ℝ)) w d.v
      ha hδ hd.2.1 hslo hshi (fun i => (hr i).le) (fun i => (hw.1 i).2) hband
  have hτ : 0 < τ := ha.trans_le (Grids.grid_lower_bound ha.le hδ.le hτmem)
  have hrank : (∑ i, y i / d.v i) ≤ (d.K : ℚ) := by
    have ht : (∑ i, (y i : ℝ) / d.v i) ≤ ∑ i, w i / d.v i :=
      sum_le_sum fun i _ => div_le_div_of_nonneg_right (hyw i) (hv i).le
    have hh := ht.trans hw.2.1
    exact_mod_cast hh
  refine ⟨w, hw, hmax, τ, hτmem, y, hy, options_feasible d hd hδ.le hτ y hy hrank, ?_⟩
  simpa [Optimization.revenue, Approximation.revenue, revenue] using hyrev
end BalancedAssortments.FPTAS
