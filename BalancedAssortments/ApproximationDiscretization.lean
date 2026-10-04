import BalancedAssortments.Approximation
import BalancedAssortments.GridBounds

/-! Rounding arbitrary real sales to the executable rational option grids. -/
namespace BalancedAssortments.ApproximationDiscretization

/-- Rational grid entries round a real target, using the explicit binary-size horizon. -/
theorem real_grid_round {a δ cap : ℚ} {x : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hax : (a : ℝ) ≤ x) (hcap : x ≤ (cap : ℝ)) :
    ∃ y ∈ Grids.geometricGrid a δ cap (GridBounds.gridHorizon a δ cap),
      (y : ℝ) ≤ x ∧ x < (1 + (δ : ℝ)) * y := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hd' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hc : 0 < cap := by exact_mod_cast (ha'.trans_le (hax.trans hcap))
  have hcover : (cap : ℝ) < (a : ℝ) * (1 + (δ : ℝ)) ^
      GridBounds.gridHorizon a δ cap := by
    exact_mod_cast GridBounds.gridHorizon_covers ha hδ hc
  have hratio : (1 : ℝ) ≤ x / a := (le_div_iff₀ ha').2 (by simpa using hax)
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near hratio (show 1 < 1 + (δ : ℝ) by linarith)
  have hlo : (a : ℝ) * (1 + (δ : ℝ)) ^ j ≤ x := by
    have := (le_div_iff₀ ha').mp hj
    nlinarith
  have hhi : x < (1 + (δ : ℝ)) * ((a : ℝ) * (1 + (δ : ℝ)) ^ j) := by
    have := (div_lt_iff₀ ha').mp hj'
    rw [pow_succ] at this
    nlinarith
  have hjh : j ≤ GridBounds.gridHorizon a δ cap := by
    by_contra hn
    have hpow : (1 + (δ : ℝ)) ^ GridBounds.gridHorizon a δ cap ≤
        (1 + (δ : ℝ)) ^ j := pow_le_pow_right₀ (by linarith) (by omega)
    have := mul_le_mul_of_nonneg_left hpow ha'.le
    linarith
  refine ⟨a * (1 + δ) ^ j, ?_, ?_, ?_⟩
  · apply Grids.mem_geometricGrid.mpr
    refine ⟨j, hjh, rfl, ?_⟩
    exact_mod_cast hlo.trans hcap
  · exact_mod_cast hlo
  · exact_mod_cast hhi

/-- Each coordinate in a real common band admits a rational option which rounds
only downward and loses less than a factor 1+δ. -/
theorem real_option_round {τ δ α v : ℚ} {w : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ)
    (hw : w = 0 ∨ ((τ : ℝ) ≤ w ∧ w ≤ ((min v (τ / α) : ℚ) : ℝ))) :
    ∃ y ∈ Grids.productOptions τ δ α v (GridBounds.gridHorizon τ δ (min v (τ / α))),
      (y : ℝ) ≤ w ∧ w / (1 + (δ : ℝ)) ≤ y ∧ 0 ≤ y := by
  have hd : (0 : ℝ) < 1 + (δ : ℝ) := by
    have : (0 : ℝ) < δ := by exact_mod_cast hδ
    linarith
  rcases hw with rfl | ⟨hl, hu⟩
  · exact ⟨0, by simp [Grids.productOptions], by simp, by simp, le_rfl⟩
  · obtain ⟨y, hy, hyw, hwy⟩ := real_grid_round hτ hδ hl hu
    refine ⟨y, List.mem_cons_of_mem _ hy, hyw, ?_, ?_⟩
    · apply (div_le_iff₀ hd).2
      nlinarith
    · exact (hτ.le.trans (Grids.grid_lower_bound hτ.le hδ.le hy))

/-- Simultaneous rational rounding with the aggregate fractional-revenue guarantee. -/
theorem discretize_real_band {ι : Type*} [Fintype ι]
    (r w : ι → ℝ) (v : ι → ℚ) {τ δ α : ℚ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hr : ∀ i, 0 ≤ r i)
    (hw : ∀ i, w i = 0 ∨ ((τ : ℝ) ≤ w i ∧
      w i ≤ ((min (v i) (τ / α) : ℚ) : ℝ))) :
    ∃ y : ι → ℚ,
      (∀ i, y i ∈ Grids.productOptions τ δ α (v i)
        (GridBounds.gridHorizon τ δ (min (v i) (τ / α)))) ∧
      (∀ i, (y i : ℝ) ≤ w i) ∧
      (∀ i, w i / (1 + (δ : ℝ)) ≤ y i) ∧
      Approximation.revenue (∑ i, r i * w i) (∑ i, w i) / (1 + (δ : ℝ)) ≤
        Approximation.revenue (∑ i, r i * y i) (∑ i, (y i : ℝ)) := by
  classical
  choose y hy hdown hnear hnon using fun i => real_option_round hτ hδ (hw i)
  refine ⟨y, hy, hdown, hnear, ?_⟩
  apply Approximation.coordinate_rounding r w (fun i => (y i : ℝ)) hr
  · intro i
    rcases hw i with hz | ⟨hl, _⟩
    · simp [hz]
    · have : (0 : ℝ) < τ := by exact_mod_cast hτ
      linarith
  · intro i; exact_mod_cast hnon i
  · have : (0 : ℝ) < δ := by exact_mod_cast hδ
    linarith
  · exact hdown
  · exact hnear

/-- Two rounds (scale alignment followed by coordinate discretization) give the
paper's squared loss. The aligned vector z is an explicit input, with its exact
band and coordinatewise shrink bounds as hypotheses. -/
theorem two_stage_discretization {ι : Type*} [Fintype ι]
    (r w z : ι → ℝ) (v : ι → ℚ) {τ δ α : ℚ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hznon : ∀ i, 0 ≤ z i) (hzdown : ∀ i, z i ≤ w i)
    (hznear : ∀ i, w i / (1 + (δ : ℝ)) ≤ z i)
    (hzband : ∀ i, z i = 0 ∨ ((τ : ℝ) ≤ z i ∧
      z i ≤ ((min (v i) (τ / α) : ℚ) : ℝ))) :
    ∃ y : ι → ℚ,
      (∀ i, y i ∈ Grids.productOptions τ δ α (v i)
        (GridBounds.gridHorizon τ δ (min (v i) (τ / α)))) ∧
      (∀ i, (y i : ℝ) ≤ w i) ∧
      Approximation.revenue (∑ i, r i * w i) (∑ i, w i) / (1 + (δ : ℝ)) ^ 2 ≤
        Approximation.revenue (∑ i, r i * y i) (∑ i, (y i : ℝ)) := by
  have hd : (0 : ℝ) < 1 + (δ : ℝ) := by
    have : (0 : ℝ) < δ := by exact_mod_cast hδ
    linarith
  obtain ⟨y, hy, hydown, _, hyrev⟩ := discretize_real_band r z v hτ hδ hr hzband
  refine ⟨y, hy, fun i => (hydown i).trans (hzdown i), ?_⟩
  have hzrev := Approximation.coordinate_rounding r w z hr hw hznon hd hzdown hznear
  have hh := (div_le_div_iff_of_pos_right hd).2 hzrev
  rw [div_div, ← pow_two] at hh
  exact hh.trans hyrev

/-- Scalar alignment to a smaller geometric scale has precisely the coordinate
bounds required by two-stage discretization. -/
theorem scale_alignment {τstar w : ℝ} {τ δ : ℚ}
    (hs : 0 < τstar) (hτ : 0 < τ) (hd : 0 < δ) (hw : 0 ≤ w)
    (hlo : (τ : ℝ) ≤ τstar) (hhi : τstar < (1 + (δ : ℝ)) * τ) :
    w / (1 + (δ : ℝ)) ≤ ((τ : ℝ) / τstar) * w ∧
      ((τ : ℝ) / τstar) * w ≤ w := by
  have hd' : (0 : ℝ) < 1 + (δ : ℝ) := by
    have : (0 : ℝ) < δ := by exact_mod_cast hd
    linarith
  have hratio : 1 / (1 + (δ : ℝ)) ≤ (τ : ℝ) / τstar := by
    apply (div_le_div_iff₀ hd' hs).2
    nlinarith
  have hratio' : (τ : ℝ) / τstar ≤ 1 := (div_le_one hs).2 hlo
  constructor
  · have := mul_le_mul_of_nonneg_right hratio hw
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  · simpa using mul_le_mul_of_nonneg_right hratio' hw

/-- Uniform scaling aligns the balance band while preserving coordinate caps. -/
theorem aligned_band {τstar w : ℝ} {τ α v : ℚ}
    (hs : 0 < τstar) (hτ : 0 < τ) (hα : 0 < α)
    (hts : (τ : ℝ) ≤ τstar) (hwcap : w ≤ (v : ℝ))
    (hw : w = 0 ∨ (τstar ≤ w ∧ w ≤ τstar / (α : ℝ))) :
    ((τ : ℝ) / τstar) * w = 0 ∨
      ((τ : ℝ) ≤ ((τ : ℝ) / τstar) * w ∧
        ((τ : ℝ) / τstar) * w ≤ ((min v (τ / α) : ℚ) : ℝ)) := by
  rcases hw with rfl | ⟨hl, hu⟩
  · simp
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hα' : (0 : ℝ) < α := by exact_mod_cast hα
  have hratio : (τ : ℝ) / τstar ≤ 1 := (div_le_one hs).2 hts
  have hratnon : 0 ≤ (τ : ℝ) / τstar := div_nonneg hτ'.le hs.le
  have hdown : ((τ : ℝ) / τstar) * w ≤ w := by
    simpa using mul_le_mul_of_nonneg_right hratio (hs.le.trans hl)
  have hupper : ((τ : ℝ) / τstar) * w ≤ (τ : ℝ) / α := by
    calc ((τ : ℝ) / τstar) * w ≤ ((τ : ℝ) / τstar) * (τstar / (α : ℝ)) :=
           mul_le_mul_of_nonneg_left hu hratnon
         _ = (τ : ℝ) / α := by field_simp
  refine Or.inr ⟨?_, ?_⟩
  · calc (τ : ℝ) = ((τ : ℝ) / τstar) * τstar := by field_simp
         _ ≤ ((τ : ℝ) / τstar) * w := mul_le_mul_of_nonneg_left hl hratnon
  · simp only [Rat.cast_min, Rat.cast_div]
    exact le_min (hdown.trans hwcap) hupper

/-- The complete two-grid discretization statement: an arbitrary real band
scale in range yields an explicitly enumerated rational scale and option vector,
with the squared geometric loss and only downward changes to coordinates. -/
theorem scale_discretization {ι : Type*} [Fintype ι]
    (r w : ι → ℝ) (v : ι → ℚ) {a cap δ α : ℚ} {τstar : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hα : 0 < α)
    (hslo : (a : ℝ) ≤ τstar) (hshi : τstar ≤ (cap : ℝ))
    (hr : ∀ i, 0 ≤ r i) (hwcap : ∀ i, w i ≤ (v i : ℝ))
    (hwband : ∀ i, w i = 0 ∨ (τstar ≤ w i ∧ w i ≤ τstar / (α : ℝ))) :
    ∃ τ ∈ Grids.geometricGrid a δ cap (GridBounds.gridHorizon a δ cap),
      ∃ y : ι → ℚ,
      (∀ i, y i ∈ Grids.productOptions τ δ α (v i)
        (GridBounds.gridHorizon τ δ (min (v i) (τ / α)))) ∧
      (∀ i, (y i : ℝ) ≤ w i) ∧
      Approximation.revenue (∑ i, r i * w i) (∑ i, w i) / (1 + (δ : ℝ)) ^ 2 ≤
        Approximation.revenue (∑ i, r i * y i) (∑ i, (y i : ℝ)) := by
  obtain ⟨τ, hτmem, hτlo, hτhi⟩ := real_grid_round ha hδ hslo hshi
  have hτ : 0 < τ := ha.trans_le (Grids.grid_lower_bound ha.le hδ.le hτmem)
  have hs : 0 < τstar := by
    have : (0 : ℝ) < a := by exact_mod_cast ha
    linarith
  have hwnon : ∀ i, 0 ≤ w i := by
    intro i
    rcases hwband i with hz | ⟨hl, _⟩
    · simp [hz]
    · exact hs.le.trans hl
  let z : ι → ℝ := fun i => ((τ : ℝ) / τstar) * w i
  have halign : ∀ i, w i / (1 + (δ : ℝ)) ≤ z i ∧ z i ≤ w i :=
    fun i => scale_alignment hs hτ hδ (hwnon i) hτlo hτhi
  have hznon : ∀ i, 0 ≤ z i := by
    intro i
    apply mul_nonneg (div_nonneg _ hs.le) (hwnon i)
    exact_mod_cast hτ.le
  obtain ⟨y, hy, hyw, hyrev⟩ := two_stage_discretization r w z v hτ hδ hr hwnon hznon
    (fun i => (halign i).2) (fun i => (halign i).1)
    (fun i => aligned_band hs hτ hα hτlo (hwcap i) (hwband i))
  exact ⟨τ, hτmem, y, hy, hyw, hyrev⟩

end BalancedAssortments.ApproximationDiscretization
