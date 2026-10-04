import BalancedAssortments.FixedSupportCostPointsDecode

namespace BalancedAssortments.FixedSupportCostPoints
open FixedSupportAlgorithm

private theorem fold_max_spec (xs : List ℚ) (a u : ℚ) :
    xs.foldl max a ≤ u ↔ a ≤ u ∧ ∀ x ∈ xs, x ≤ u := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, max_le_iff, List.forall_mem_cons]; tauto

theorem upperValue_ofFn {n : ℕ} (r v : Fin n → ℚ) :
    upperValue (List.ofFn (fun i => (r i, v i))) = revenueUpper r := by
  have he : (List.ofFn (fun i => (r i, v i))).map Prod.fst = List.ofFn r := by simp [List.map_ofFn, Function.comp_def]
  unfold upperValue
  rw [he]
  have hh := (fold_max_spec (List.ofFn r) 0 ((List.ofFn r).foldl max 0)).mp le_rfl
  apply le_antisymm
  · apply (fold_max_spec _ _ _).mpr
    refine ⟨revenueUpper_nonneg r, ?_⟩
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact revenue_le_upper r i
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hh.1
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hh.2 (r i) (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem scoreLine_root {n : ℕ} (r v : Fin n → ℚ) (i : Fin n) (hv : v i ≠ 0) :
    affineRoot (scoreLine r v i) = r i := by
  change -(r i * v i) / (-v i) = r i
  rw [neg_div_neg_eq]
  field_simp

theorem crossingValue_root {n : ℕ} (r v : Fin n → ℚ) (i j : Fin n) :
    crossingValue (r i, v i) (r j, v j) = affineRoot (scoreDifference r v (i, j)) := by
  unfold crossingValue affineRoot scoreDifference
  dsimp only
  rw [show v j - v i = -(v i - v j) by ring, neg_div_neg_eq]

private theorem root_mem_critical {lo hi : ℚ} {F : Finset (Affine (𝕜 := ℚ))}
    {f : Affine (𝕜 := ℚ)} (hf : f ∈ F) (hz : f.1 ≠ 0)
    (hb : lo ≤ affineRoot f ∧ affineRoot f ≤ hi) : affineRoot f ∈ affineCritical lo hi F := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, hz⟩, rfl⟩, hb⟩

/-- Numerical duplicates and zero-slope zero sentinels do not change the exact
critical set used by the certified rational optimizer. -/
theorem criticalValues_toFinset {n : ℕ} (r v : Fin n → ℚ) (hv : ∀ i, v i ≠ 0) :
    (criticalValues (List.ofFn (fun i => (r i, v i)))).toFinset =
      affineCritical 0 (revenueUpper r) (scoreLines r v) := by
  classical
  let ps := List.ofFn (fun i => (r i, v i))
  have hu : upperValue (List.ofFn (fun i => (r i, v i))) = revenueUpper r := upperValue_ofFn r v
  ext c
  rw [List.mem_toFinset]
  constructor
  · intro hc
    simp only [criticalValues, hu, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_filter, decide_eq_true_eq] at hc
    rcases hc with hc | ⟨hc, hb⟩
    · rcases hc with rfl | rfl <;> simp [affineCritical]
    · rcases hc with hc | hc
      · obtain ⟨p, hp, hpc⟩ := List.mem_map.mp hc
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
        dsimp only at hpc
        subst c
        have hf : scoreLine r v i ∈ scoreLines r v :=
          Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
        rw [← scoreLine_root r v i (hv i)]
        exact root_mem_critical hf (neg_ne_zero.mpr (hv i)) (by simpa [scoreLine_root r v i (hv i)] using hb)
      · obtain ⟨p, hp, hc⟩ := List.mem_flatMap.mp hc
        obtain ⟨s, hs, hsc⟩ := List.mem_map.mp hc
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
        subst c
        by_cases heq : v i = v j
        · simp [crossingValue, heq, affineCritical]
        · rw [crossingValue_root]
          apply root_mem_critical
          · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
          · exact sub_ne_zero.mpr (Ne.symm heq)
          · simpa [crossingValue_root] using hb
  · intro hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · simp [criticalValues]
    rcases Finset.mem_insert.mp hc with rfl | hc
    · simp [criticalValues, hu]
    have hb := (Finset.mem_filter.mp hc).2
    obtain ⟨f, hf, hfc⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
    have hf' := (Finset.mem_filter.mp hf).1
    rcases Finset.mem_union.mp hf' with hf' | hf'
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf'
      have hci : r i = c := by simpa [scoreLine_root r v i (hv i)] using hfc
      clear hfc
      subst c
      apply List.mem_append.mpr
      right
      apply List.mem_filter.mpr
      refine ⟨?_, by simpa [hu] using hb⟩
      apply List.mem_append.mpr
      left
      exact List.mem_map.mpr ⟨(r i, v i), List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩
    · obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hf'
      have hci : crossingValue (r i, v i) (r j, v j) = c := by simpa [crossingValue_root] using hfc
      clear hfc
      subst c
      apply List.mem_append.mpr
      right
      apply List.mem_filter.mpr
      refine ⟨?_, by simpa [hu] using hb⟩
      apply List.mem_append.mpr
      right
      exact List.mem_flatMap.mpr ⟨(r i, v i), List.mem_ofFn.mpr ⟨i, rfl⟩,
        List.mem_map.mpr ⟨(r j, v j), List.mem_ofFn.mpr ⟨j, rfl⟩, rfl⟩⟩

theorem scoreValues_toFinset {n : ℕ} (r v : Fin n → ℚ) (hv : ∀ i, v i ≠ 0) :
    (scoreValues (List.ofFn (fun i => (r i, v i)))).toFinset = scoreSamples r v := by
  unfold scoreSamples
  rw [scoreValues, ← criticalValues_toFinset r v hv]
  ext x
  simp [regimeSamples, List.mem_flatMap, List.mem_map, Finset.mem_image, Finset.mem_product]
  aesop

end BalancedAssortments.FixedSupportCostPoints
