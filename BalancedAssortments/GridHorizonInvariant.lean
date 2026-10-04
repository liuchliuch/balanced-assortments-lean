import BalancedAssortments.GridBounds

namespace BalancedAssortments.Grids

/-- Appending one exponent beyond the cap leaves the actual filtered grid unchanged. -/
theorem geometricGrid_succ_of_covered {a δ cap : ℚ} (h : ℕ)
    (hc : cap < a * (1+δ)^(h+1)) :
    geometricGrid a δ cap (h+1) = geometricGrid a δ cap h := by
  simp only [geometricGrid, List.range_succ, List.map_append, List.map_singleton,
    List.filter_append, List.filter_cons, List.filter_nil]
  simp [not_le_of_gt hc]

/-- After a covering horizon, arbitrarily padding the iteration count adds no
options. This supports an unreduced-fraction binary implementation without
computing normalized rational numerator/denominator sizes. -/
theorem geometricGrid_padding {a δ cap : ℚ} {h : ℕ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hc : cap < a*(1+δ)^(h+1)) (k : ℕ) :
    geometricGrid a δ cap (h+k) = geometricGrid a δ cap h := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : (1+δ)^(h+1) ≤ (1+δ)^(h+k+1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hh := hc.trans_le (mul_le_mul_of_nonneg_left hp ha)
    rw [show h + (k+1) = (h+k)+1 by omega, geometricGrid_succ_of_covered (h+k) hh]
    exact ih

theorem geometricGrid_eq_of_covers {a δ cap : ℚ} {h k : ℕ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hh : cap < a*(1+δ)^(h+1)) (hk : cap < a*(1+δ)^(k+1)) :
    geometricGrid a δ cap h = geometricGrid a δ cap k := by
  rcases le_total h k with hle | hle
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact (geometricGrid_padding ha hδ hh m).symm
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact geometricGrid_padding ha hδ hk m

theorem geometricGrid_eq_canonical {a δ cap : ℚ} {h : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hc : 0 < cap)
    (hh : cap < a*(1+δ)^(h+1)) :
    geometricGrid a δ cap h =
      geometricGrid a δ cap (GridBounds.gridHorizon a δ cap) := by
  apply geometricGrid_eq_of_covers ha.le hδ.le hh
  have hp : (1+δ)^GridBounds.gridHorizon a δ cap ≤
      (1+δ)^(GridBounds.gridHorizon a δ cap+1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  exact (GridBounds.gridHorizon_covers ha hδ hc).trans_le (mul_le_mul_of_nonneg_left hp ha.le)
end BalancedAssortments.Grids
