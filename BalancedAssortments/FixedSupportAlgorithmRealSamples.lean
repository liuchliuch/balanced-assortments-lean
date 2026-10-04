import BalancedAssortments.FixedSupportAlgorithmRegimes

namespace BalancedAssortments.FixedSupportAlgorithm

private theorem sample_real_preimage (C : Finset ℚ) {s : ℝ}
    (hs : s ∈ regimeSamples (C.image (fun q : ℚ => (q : ℝ)))) :
    ∃ q ∈ regimeSamples C, (q : ℝ) = s := by
  rcases Finset.mem_union.mp hs with hs | hs
  · obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hs
    exact ⟨q, Finset.mem_union_left _ hq, he⟩
  · obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.mp hs
    obtain ⟨qa, hqa, rfl⟩ := Finset.mem_image.mp (Finset.mem_product.mp hab).1
    obtain ⟨qb, hqb, rfl⟩ := Finset.mem_image.mp (Finset.mem_product.mp hab).2
    refine ⟨(qa + qb) / 2, Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨(qa, qb), Finset.mem_product.mpr ⟨hqa, hqb⟩, rfl⟩), ?_⟩
    push_cast
    exact he

/-- Arbitrary real targets are covered by the executable *rational* sample
set. No rational-optimum assumption or density argument is needed. -/
theorem rational_samples_cover_real {lo hi : ℚ} (hdom : lo ≤ hi)
    (F : Finset (Affine (𝕜 := ℚ))) {x : ℝ} (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) :
    ∃ q ∈ regimeSamples (affineCritical lo hi F), lo ≤ q ∧ q ≤ hi ∧
      ∀ f ∈ F,
        (affineValue ((f.1 : ℝ), (f.2 : ℝ)) x ≤ 0 ↔ ((affineValue f q : ℚ) : ℝ) ≤ 0) ∧
        (0 ≤ affineValue ((f.1 : ℝ), (f.2 : ℝ)) x ↔ 0 ≤ ((affineValue f q : ℚ) : ℝ)) := by
  classical
  let C := affineCritical lo hi F
  let D := C.image (fun q : ℚ => (q : ℝ))
  have hlo : (lo : ℝ) ∈ D := Finset.mem_image.mpr ⟨lo, by simp [C, affineCritical], rfl⟩
  have hhi : (hi : ℝ) ∈ D := Finset.mem_image.mpr ⟨hi, by simp [C, affineCritical], rfl⟩
  obtain ⟨s, hs, hreg⟩ := exists_regime_sample hlo hhi hx
  obtain ⟨q, hq, hqs⟩ := sample_real_preimage C hs
  have hqb := regimeSamples_bounds (affineCritical_bounds hdom F) hq
  have hsb : (lo : ℝ) ≤ s ∧ s ≤ (hi : ℝ) := by rw [← hqs]; exact_mod_cast hqb
  refine ⟨q, hq, hqb.1, hqb.2, ?_⟩
  intro f hf
  have hh := affine_signs_same_of_roots hx hsb hreg ((f.1 : ℝ), (f.2 : ℝ)) (by
    intro hf0 hl hh
    have hf0' : f.1 ≠ 0 := by
      change (f.1 : ℝ) ≠ 0 at hf0
      exact_mod_cast hf0
    have he : affineRoot ((f.1 : ℝ), (f.2 : ℝ)) = ((affineRoot f : ℚ) : ℝ) := by
      simp [affineRoot]
    rw [he] at hl hh ⊢
    apply Finset.mem_image.mpr
    refine ⟨affineRoot f, ?_, rfl⟩
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, hf0'⟩, rfl⟩, ?_, ?_⟩
    · exact_mod_cast hl
    · exact_mod_cast hh)
  rw [← hqs] at hh
  simpa [affineValue] using hh

end BalancedAssortments.FixedSupportAlgorithm
