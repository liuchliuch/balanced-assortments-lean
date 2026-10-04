import BalancedAssortments.FixedSupportAlgorithmPrefixPieces

set_option maxHeartbeats 2000000
namespace BalancedAssortments.FixedSupportAlgorithm

/-- The executable rational scale superset dominates every real scale for each
fixed sampled score pattern. The proof covers cap ties, zero residual slopes,
zero allocations, and all prefix-budget switch points exactly. -/
theorem scaleSamples_dominate_real {n : ℕ} (r v : Fin n → ℚ) {α K q : ℚ} (ρ : ℝ)
    (hv : ∀ i, 0 < v i) (hα : 0 < α) (hα1 : α ≤ 1)
    (hT : 0 ≤ scaleUpper v K) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ (scaleUpper v K : ℝ)) :
    ∃ u ∈ scaleSamples r v α K q,
      prefixObjective r v α K q ρ t ≤ prefixObjective r v α K q ρ (u : ℝ) := by
  classical
  obtain ⟨a, ha, b, hb, hat, htb, hgap⟩ := rational_adjacent_bracket
    (C := capCuts v α (scaleUpper v K)) (lo := 0) (hi := scaleUpper v K)
    (by simp [capCuts]) (by simp [capCuts]) (by simpa using ht)
  have had := capCuts_bounds v α hT ha
  have hbd := capCuts_bounds v α hT hb
  have ham : a ∈ scaleSamples r v α K q := Finset.mem_union_left _ ha
  have hbm : b ∈ scaleSamples r v α K q := Finset.mem_union_left _ hb
  have hab : a ≤ b := by exact_mod_cast hat.trans htb
  by_cases heq : a = b
  · refine ⟨a, ham, ?_⟩
    have hta : t = (a : ℝ) := le_antisymm (by simpa [heq] using htb) hat
    rw [hta]
  have hab' : a < b := lt_of_le_of_ne hab heq
  have hcross := capCuts_no_crossing v hv hα hT hb hgap
  let Ds := (scaleSamples r v α K q).filter (fun u => a ≤ u ∧ u ≤ b)
  let D := Ds.image (fun u : ℚ => (u : ℝ))
  have haD : (a : ℝ) ∈ D := Finset.mem_image.mpr
    ⟨a, Finset.mem_filter.mpr ⟨ham, le_rfl, hab⟩, rfl⟩
  have hbD : (b : ℝ) ∈ D := Finset.mem_image.mpr
    ⟨b, Finset.mem_filter.mpr ⟨hbm, hab, le_rfl⟩, rfl⟩
  have hDb : ∀ u ∈ D, (a : ℝ) ≤ u ∧ u ≤ (b : ℝ) := by
    intro u hu
    obtain ⟨u, hurat, rfl⟩ := Finset.mem_image.mp hu
    exact_mod_cast (Finset.mem_filter.mp hurat).2
  have hroot (k : ℕ) (hk : k ≤ n) :
      (a : ℝ) ≤ affineRoot (realLine (prefixLine v α K a (orderedPrefix r v q k))) →
      affineRoot (realLine (prefixLine v α K a (orderedPrefix r v q k))) ≤ (b : ℝ) →
      affineRoot (realLine (prefixLine v α K a (orderedPrefix r v q k))) ∈ D := by
    intro hl hh
    rw [affineRoot_realLine, prefixLine_root] at hl hh ⊢
    have hla : a ≤ prefixRoot v α K a (orderedPrefix r v q k) := by exact_mod_cast hl
    have hhb : prefixRoot v α K a (orderedPrefix r v q k) ≤ b := by exact_mod_cast hh
    apply Finset.mem_image.mpr
    refine ⟨prefixRoot v α K a (orderedPrefix r v q k), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨prefixRoot_mem_scaleSamples r v α K q ha hk
      ⟨had.1.trans hla, hhb.trans hbd.2⟩, hla, hhb⟩
  have hcap : ∀ k : Fin n, ∀ u : ℝ, (a : ℝ) ≤ u → u ≤ (b : ℝ) →
      0 ≤ affineValue (realLine (capLine v α a (orderedLabel r v q k))) u := by
    intro k u hua hub
    dsimp only [realLine]
    rw [← capLine_real v hv hα hcross ⟨hua, hub⟩]
    apply FixedSupportKnapsack.cap_nonneg _ (fun i => by exact_mod_cast hv i)
      (by exact_mod_cast hα) (by exact_mod_cast hα1)
    · exact (by exact_mod_cast had.1 : (0 : ℝ) ≤ a).trans hua
    · intro i
      exact hub.trans (by exact_mod_cast hbd.2.trans (scaleUpper_le_coordinate v K i))
  obtain ⟨u, hu, hval⟩ := clippedObjective_endpoint
    (∑ i, ((r i : ℝ) - ρ)) (fun k => realScore r v ρ (orderedLabel r v q k))
    (fun k => decide (0 < score r v q (orderedLabel r v q k)))
    (fun k => realLine (capLine v α a (orderedLabel r v q k)))
    (fun k => realLine (prefixLine v α K a (orderedPrefix r v q k.val))) D
    haD hbD hDb ⟨hat, htb⟩ hcap
    (fun k _ hl hh => hroot k.val k.isLt.le hl hh)
    (by
      intro k hn hl hh
      have he := prefixLine_step r v hv hα hab' hcross k (K := K) (q := q)
      rw [he] at hl hh ⊢
      exact hroot (k.val + 1) k.isLt hl hh)
  obtain ⟨u, hurat, rfl⟩ := Finset.mem_image.mp hu
  have hum := Finset.mem_filter.mp hurat
  have huR : (a : ℝ) ≤ (u : ℝ) ∧ (u : ℝ) ≤ (b : ℝ) := by exact_mod_cast hum.2
  refine ⟨u, hum.1, ?_⟩
  rw [prefixObjective_affine_form r v ρ hv hα hcross ⟨hat, htb⟩,
    prefixObjective_affine_form r v ρ hv hα hcross huR]
  exact hval

end BalancedAssortments.FixedSupportAlgorithm
