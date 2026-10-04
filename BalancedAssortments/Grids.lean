import Mathlib

/-! Executable finite rational geometric grids and their local rounding guarantee.
The finite horizon is an explicit input. No polynomial horizon/bit-size claim is made here. -/
namespace BalancedAssortments.Grids

/-- Geometric grid, truncated both by an explicit exponent horizon and a cap. -/
def geometricGrid (a δ cap : ℚ) (horizon : ℕ) : List ℚ :=
  ((List.range (horizon + 1)).map fun j => a * (1 + δ) ^ j).filter (· ≤ cap)

/-- Options for one product; zero is retained independently of cap and balance. -/
def productOptions (τ δ α v : ℚ) (horizon : ℕ) : List ℚ :=
  0 :: geometricGrid τ δ (min v (τ / α)) horizon

theorem mem_geometricGrid {a δ cap x : ℚ} {horizon : ℕ} :
    x ∈ geometricGrid a δ cap horizon ↔
      ∃ j ≤ horizon, x = a * (1 + δ) ^ j ∧ x ≤ cap := by
  simp only [geometricGrid, List.mem_filter, decide_eq_true_eq, List.mem_map,
    List.mem_range]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hc⟩
    exact ⟨j, by omega, rfl, hc⟩
  · rintro ⟨j, hj, rfl, hc⟩
    exact ⟨⟨j, by omega, rfl⟩, hc⟩

theorem grid_lower_bound {a δ cap x : ℚ} {horizon : ℕ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hx : x ∈ geometricGrid a δ cap horizon) : a ≤ x := by
  obtain ⟨j, _, rfl, _⟩ := mem_geometricGrid.mp hx
  have hp : (1 : ℚ) ≤ (1 + δ) ^ j := one_le_pow₀ (by linarith)
  nlinarith

/-- Membership alone enforces the exact cap and balance band. -/
theorem option_band {τ δ α v x : ℚ} {horizon : ℕ}
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (hx : x ∈ productOptions τ δ α v horizon) :
    x = 0 ∨ (τ ≤ x ∧ x ≤ v ∧ x ≤ τ / α) := by
  simp only [productOptions, List.mem_cons] at hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · have hl := grid_lower_bound hτ hδ hx
    obtain ⟨_, _, _, hc⟩ := mem_geometricGrid.mp hx
    exact Or.inr ⟨hl, (le_min_iff.mp hc).1, (le_min_iff.mp hc).2⟩

/-- Unbounded geometric rounding exists over rational inputs. -/
theorem exists_geometric_round {a δ x : ℚ} (ha : 0 < a) (hδ : 0 < δ)
    (hax : a ≤ x) :
    ∃ j : ℕ, a * (1 + δ) ^ j ≤ x ∧ x < (1 + δ) * (a * (1 + δ) ^ j) := by
  have hratio : (1 : ℚ) ≤ x / a := (le_div_iff₀ ha).2 (by simpa using hax)
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near hratio (show (1 : ℚ) < 1 + δ by linarith)
  refine ⟨j, ?_, ?_⟩
  · have := (le_div_iff₀ ha).mp hj
    nlinarith
  · have := (div_lt_iff₀ ha).mp hj'
    rw [pow_succ] at this
    nlinarith

/-- Any horizon beyond the target contains a rounding option with loss below 1+δ. -/
theorem finite_grid_round {a δ x cap : ℚ} {horizon : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hax : a ≤ x) (hcap : x ≤ cap)
    (hcover : x < a * (1 + δ) ^ (horizon + 1)) :
    ∃ y ∈ geometricGrid a δ cap horizon, y ≤ x ∧ x < (1 + δ) * y := by
  obtain ⟨j, hj, hnext⟩ := exists_geometric_round ha hδ hax
  have hjh : j ≤ horizon := by
    by_contra hn
    have hpow : (1 + δ) ^ (horizon + 1) ≤ (1 + δ) ^ j :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have := mul_le_mul_of_nonneg_left hpow ha.le
    linarith
  refine ⟨a * (1 + δ) ^ j, mem_geometricGrid.mpr ⟨j, hjh, rfl, hj.trans hcap⟩,
    hj, hnext⟩

end BalancedAssortments.Grids
