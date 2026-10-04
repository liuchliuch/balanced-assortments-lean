import BalancedAssortments.Grids
import Mathlib

/-! Explicit finite geometric-grid horizons. Bounds are expressed in binary
length and inverse accuracy; this module is not by itself an algorithmic
bit-operation complexity proof. -/
namespace BalancedAssortments.GridBounds

def blockLength (δ : ℚ) : ℕ := ⌈1 / δ⌉₊
def ratioBits (a cap : ℚ) : ℕ := cap.num.natAbs.size + a.den.size

theorem block_growth {δ : ℚ} (hδ : 0 < δ) :
    2 ≤ (1 + δ) ^ blockLength δ := by
  have hc := Nat.le_ceil (1 / δ)
  have hm := mul_le_mul_of_nonneg_right hc hδ.le
  rw [div_mul_cancel₀ _ hδ.ne'] at hm
  have hp := one_add_mul_le_pow (show (-2 : ℚ) ≤ δ by linarith) (blockLength δ)
  dsimp [blockLength] at hp ⊢
  linarith

theorem blocks_growth {δ : ℚ} (hδ : 0 < δ) (b : ℕ) :
    (2 : ℚ) ^ b ≤ (1 + δ) ^ (blockLength δ * b) := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (block_growth hδ) b

theorem blockLength_bound {δ : ℚ} (hδ : 0 < δ) :
    (blockLength δ : ℚ) < 1 / δ + 1 :=
  Nat.ceil_lt_add_one (by positivity)

theorem ratio_lt_pow {a cap : ℚ} (ha : 0 < a) (hc : 0 < cap) :
    cap / a < (2 : ℚ) ^ ratioBits a cap := by
  have han : (1 : ℤ) ≤ a.num := (Rat.num_pos.mpr ha)
  have hcn : 0 ≤ cap.num := (Rat.num_pos.mpr hc).le
  have had : (0 : ℚ) < a.den := by exact_mod_cast a.den_pos
  have hcd : (1 : ℚ) ≤ cap.den := by exact_mod_cast cap.den_pos
  have hanq : (1 : ℚ) ≤ a.num := by exact_mod_cast han
  have hcnq : (0 : ℚ) ≤ cap.num := by exact_mod_cast hcn
  have hcap : cap ≤ cap.num := by
    calc cap = (cap.num : ℚ) / cap.den := (Rat.num_div_den cap).symm
         _ ≤ cap.num := ?_
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hcd)).2
    nlinarith
  have haLower : 1 / (a.den : ℚ) ≤ a := by
    calc 1 / (a.den : ℚ) ≤ (a.num : ℚ) / a.den := div_le_div_of_nonneg_right hanq had.le
         _ = a := Rat.num_div_den a
  have hr : cap / a ≤ (cap.num : ℚ) * a.den := by
    apply (div_le_iff₀ ha).2
    have hm := mul_le_mul_of_nonneg_left haLower (mul_nonneg hcnq had.le)
    have hs : (cap.num : ℚ) * a.den * (1 / a.den) = cap.num := by field_simp
    rw [hs] at hm
    exact hcap.trans hm
  have hnum : (cap.num : ℚ) < 2 ^ cap.num.natAbs.size := by
    have hb : cap.num.natAbs < 2 ^ cap.num.natAbs.size := Nat.size_le.mp le_rfl
    have he : (cap.num.natAbs : ℚ) = cap.num := by
      calc (cap.num.natAbs : ℚ) = ((cap.num.natAbs : ℤ) : ℚ) := by simp
           _ = (cap.num : ℚ) := congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg hcn)
    rw [← he]
    exact_mod_cast hb
  have hden : (a.den : ℚ) < 2 ^ a.den.size := by
    exact_mod_cast (Nat.size_le.mp (le_refl a.den.size))
  apply hr.trans_lt
  unfold ratioBits
  rw [pow_add]
  exact mul_lt_mul hnum hden.le had (by positivity)

def gridHorizon (a δ cap : ℚ) : ℕ := blockLength δ * ratioBits a cap

theorem gridHorizon_covers {a δ cap : ℚ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : 0 < cap) : cap < a * (1 + δ) ^ gridHorizon a δ cap := by
  have hh := (ratio_lt_pow ha hc).trans_le (blocks_growth hδ (ratioBits a cap))
  simpa [gridHorizon, mul_comm] using (div_lt_iff₀ ha).1 hh

/-- No externally supplied horizon remains: every positive target between the
base and cap has a grid predecessor with relative gap less than 1+δ. -/
theorem explicit_grid_round {a δ x cap : ℚ}
    (ha : 0 < a) (hδ : 0 < δ) (hax : a ≤ x) (hcap : x ≤ cap) :
    ∃ y ∈ Grids.geometricGrid a δ cap (gridHorizon a δ cap),
      y ≤ x ∧ x < (1 + δ) * y := by
  apply Grids.finite_grid_round ha hδ hax hcap
  have hc : 0 < cap := ha.trans_le (hax.trans hcap)
  have hp : (1 + δ) ^ gridHorizon a δ cap ≤
      (1 + δ) ^ (gridHorizon a δ cap + 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  exact hcap.trans_lt ((gridHorizon_covers ha hδ hc).trans_le
    (mul_le_mul_of_nonneg_left hp ha.le))
end BalancedAssortments.GridBounds
