import BalancedAssortments.FixedSupportAlgorithmRegimes

namespace BalancedAssortments.FixedSupportAlgorithm
section OrderedField
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Finite exact breakpoint coverage, with degenerate intervals when the target
is itself already an enumerated breakpoint. -/
theorem exists_adjacent_bracket {C : Finset 𝕜} {lo hi x : 𝕜}
    (hlo : lo ∈ C) (hhi : hi ∈ C) (hx : lo ≤ x ∧ x ≤ hi) :
    ∃ a ∈ C, ∃ b ∈ C, a ≤ x ∧ x ≤ b ∧
      ∀ c ∈ C, c ≤ a ∨ b ≤ c := by
  by_cases hxc : x ∈ C
  · exact ⟨x, hxc, x, hxc, le_rfl, le_rfl, fun c _ => le_total c x⟩
  let A := C.filter (fun c => c ≤ x)
  let B := C.filter (fun c => x ≤ c)
  have hA : A.Nonempty := ⟨lo, Finset.mem_filter.mpr ⟨hlo, hx.1⟩⟩
  have hB : B.Nonempty := ⟨hi, Finset.mem_filter.mpr ⟨hhi, hx.2⟩⟩
  let a := A.max' hA
  let b := B.min' hB
  have ha : a ∈ C ∧ a ≤ x := Finset.mem_filter.mp (A.max'_mem hA)
  have hb : b ∈ C ∧ x ≤ b := Finset.mem_filter.mp (B.min'_mem hB)
  refine ⟨a, ha.1, b, hb.1, ha.2, hb.2, ?_⟩
  intro c hc
  by_cases hh : c ≤ x
  · exact Or.inl (A.le_max' c (Finset.mem_filter.mpr ⟨hc, hh⟩))
  · exact Or.inr (B.min'_le c (Finset.mem_filter.mpr ⟨hc, (lt_of_not_ge hh).le⟩))

theorem affine_endpoint_max (f : Affine (𝕜 := 𝕜)) {a b x : 𝕜}
    (hx : a ≤ x ∧ x ≤ b) :
    affineValue f x ≤ max (affineValue f a) (affineValue f b) := by
  by_cases hf : 0 ≤ f.1
  · apply le_trans _ (le_max_right _ _)
    dsimp [affineValue]
    nlinarith [mul_nonneg hf (sub_nonneg.mpr hx.2)]
  · apply le_trans _ (le_max_left _ _)
    dsimp [affineValue]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hf) (sub_nonneg.mpr hx.1)]

/-- If the only possible root is not strictly inside an interval, one weak sign
holds throughout the closed interval. Root endpoints and identically zero
functions require no tie-breaking convention. -/
theorem affine_constant_sign {f : Affine (𝕜 := 𝕜)} {a b : 𝕜}
    (hroot : f.1 ≠ 0 → ¬(a < affineRoot f ∧ affineRoot f < b)) :
    (∀ t, a ≤ t → t ≤ b → affineValue f t ≤ 0) ∨
      (∀ t, a ≤ t → t ≤ b → 0 ≤ affineValue f t) := by
  by_cases hz : f.1 = 0
  · by_cases hb : f.2 ≤ 0
    · left; intro t _ _; simpa [affineValue, hz] using hb
    · right; intro t _ _; simpa [affineValue, hz] using (le_of_not_ge hb)
  · have he (t : 𝕜) : affineValue f t = f.1 * (t - affineRoot f) := by
      dsimp [affineValue, affineRoot]
      field_simp
      <;> ring
    have hr : affineRoot f ≤ a ∨ b ≤ affineRoot f := by
      by_cases ha : a < affineRoot f
      · exact Or.inr (le_of_not_gt (fun hb => hroot hz ⟨ha, hb⟩))
      · exact Or.inl (le_of_not_gt ha)
    rcases hr with hr | hr <;> by_cases hp : 0 ≤ f.1
    · right; intro t ht _; rw [he]; exact mul_nonneg hp (sub_nonneg.mpr (hr.trans ht))
    · left; intro t ht _; rw [he]; exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) (sub_nonneg.mpr (hr.trans ht))
    · left; intro t _ ht; rw [he]; exact mul_nonpos_of_nonneg_of_nonpos hp (sub_nonpos.mpr (ht.trans hr))
    · right; intro t _ ht; rw [he]; exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hp) (sub_nonpos.mpr (ht.trans hr))

/-- Every clipped greedy allocation is affine between the roots of the budget
residual before and after its capacity. These are exactly consecutive-prefix
residual roots in continuous knapsack. -/
theorem clipped_affine_piece {c r : Affine (𝕜 := 𝕜)} {a b : 𝕜}
    (hc : ∀ t, a ≤ t → t ≤ b → 0 ≤ affineValue c t)
    (hr : r.1 ≠ 0 → ¬(a < affineRoot r ∧ affineRoot r < b))
    (hd : (r.1 - c.1) ≠ 0 →
      ¬(a < affineRoot (r.1 - c.1, r.2 - c.2) ∧
        affineRoot (r.1 - c.1, r.2 - c.2) < b)) :
    ∃ f : Affine (𝕜 := 𝕜), ∀ t, a ≤ t → t ≤ b →
      min (affineValue c t) (max (affineValue r t) 0) = affineValue f t := by
  rcases affine_constant_sign hr with hrneg | hrpos
  · refine ⟨(0, 0), ?_⟩
    intro t hta htb
    rw [max_eq_right (hrneg t hta htb), min_eq_right (hc t hta htb)]
    simp [affineValue]
  · rcases affine_constant_sign (f := (r.1 - c.1, r.2 - c.2)) hd with hdneg | hdpos
    · refine ⟨r, ?_⟩
      intro t hta htb
      rw [max_eq_left (hrpos t hta htb)]
      apply min_eq_right
      have hh := hdneg t hta htb
      dsimp [affineValue] at hh ⊢
      nlinarith
    · refine ⟨c, ?_⟩
      intro t hta htb
      rw [max_eq_left (hrpos t hta htb)]
      apply min_eq_left
      have hh := hdpos t hta htb
      dsimp [affineValue] at hh ⊢
      nlinarith

/-- Weighted finite sums of the selected affine pieces remain affine. -/
theorem affine_weighted_sum {ι : Type*} [Fintype ι] (w : ι → 𝕜)
    (f : ι → Affine (𝕜 := 𝕜)) (t : 𝕜) :
    (∑ i, w i * affineValue (f i) t) =
      affineValue (∑ i, w i * (f i).1, ∑ i, w i * (f i).2) t := by
  simp [affineValue, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]

end OrderedField
end BalancedAssortments.FixedSupportAlgorithm
