import BalancedAssortments.FixedSupportAlgorithmFinite
import BalancedAssortments.FixedSupportKnapsack

namespace BalancedAssortments.FixedSupportAlgorithm

/-- The rational endpoint `scaleUpper` describes the entire real scale domain,
including arbitrary real feasible source points. -/
theorem real_scaleDomain_iff {n : ℕ} (hn : 0 < n) (v : Fin n → ℚ)
    (hv : ∀ i, 0 < v i) (K : ℚ) (t : ℝ) :
    FixedSupportKnapsack.ScaleDomain (fun i => (v i : ℝ)) (K : ℝ) t ↔
      0 ≤ t ∧ t ≤ (scaleUpper v K : ℝ) := by
  have hs := inverseSum_pos hn v hv
  have hsR : (0 : ℝ) < (inverseSum v : ℝ) := by exact_mod_cast hs
  have he : (inverseSum v : ℝ) = ∑ i, (1 : ℝ) / (v i : ℝ) := by simp [inverseSum]
  constructor
  · intro ht
    refine ⟨ht.1, ?_⟩
    have hm := (insert (K / inverseSum v) (Finset.univ.image v)).min'_mem (Finset.insert_nonempty _ _)
    rcases Finset.mem_insert.mp hm with hm | hm
    · have hTe : scaleUpper v K = K / inverseSum v := hm
      rw [hTe]
      push_cast
      apply (le_div_iff₀ hsR).mpr
      have hh := ht.2.2
      dsimp [FixedSupportKnapsack.budget] at hh
      rw [← he] at hh
      linarith
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      change v i = scaleUpper v K at hi
      rw [← hi]
      exact ht.2.1 i
  · intro ht
    refine ⟨ht.1, ?_, ?_⟩
    · intro i
      apply ht.2.trans
      change (scaleUpper v K : ℝ) ≤ (v i : ℝ)
      exact_mod_cast scaleUpper_le_coordinate v K i
    · have hmul : scaleUpper v K * inverseSum v ≤ K :=
        (le_div_iff₀ hs).mp (scaleUpper_le_budgetQuotient v K)
      have hmulR : (scaleUpper v K : ℝ) * (inverseSum v : ℝ) ≤ (K : ℝ) := by exact_mod_cast hmul
      dsimp [FixedSupportKnapsack.budget]
      rw [← he]
      nlinarith

end BalancedAssortments.FixedSupportAlgorithm
