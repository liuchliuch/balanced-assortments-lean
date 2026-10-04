import BalancedAssortments.FPTASCostSeedRefinement
import BalancedAssortments.KnapsackCostEncoding
import BalancedAssortments.GridHorizonInvariant

/-! Covering grid horizons from unreduced bit representations, avoiding all
canonical-rational normalization during horizon construction. -/
namespace BalancedAssortments.FPTASCostGrid
open ComplexityTimeBinary KnapsackCostRational

/-- A safe reciprocal ceiling, rounded up even when the quotient is integral. -/
def reciprocalCeilingBits (delta : Fraction) : List Bool × ℕ :=
  let floor := floorRatio FPTASCostSeeds.one delta
  let up := addCarry floor.1 [true] false
  (up.1, floor.2+up.2+4)

lemma reciprocalCeilingBits_value (delta : Fraction) (hd : delta.Valid) (hp : 0 < delta.decode) :
    value (reciprocalCeilingBits delta).1 = ⌊1/delta.decode⌋₊+1 := by
  simp only [reciprocalCeilingBits, addCarry_value, value, Bool.toNat_true,
    Bool.toNat_false, Nat.add_zero, Nat.mul_zero]
  rw [floorRatio_correct FPTASCostSeeds.one_valid hd hp, FPTASCostSeeds.one_decode]

lemma reciprocalCeilingBits_covers (delta : Fraction) (hd : delta.Valid) (hp : 0 < delta.decode) :
    GridBounds.blockLength delta.decode ≤ value (reciprocalCeilingBits delta).1 := by
  rw [reciprocalCeilingBits_value delta hd hp]
  apply Nat.ceil_le.mpr
  simpa using (Nat.lt_floor_add_one (1/delta.decode)).le

lemma reciprocalCeilingBits_upper (delta : Fraction) (hd : delta.Valid) (hp : 0 < delta.decode) :
    (value (reciprocalCeilingBits delta).1 : ℚ) ≤ 1/delta.decode+1 := by
  rw [reciprocalCeilingBits_value delta hd hp]
  push_cast
  exact add_le_add_right (Nat.floor_le (by positivity)) 1

lemma reciprocalCeilingBits_cost (delta : Fraction) {b : ℕ} (hb : 1 ≤ b) (hd : delta.Width b) :
    (reciprocalCeilingBits delta).2 ≤ 4096*(b+1)^2+48*b+21 := by
  have hone : FPTASCostSeeds.one.Width b := ⟨FPTASCostSeeds.one_width.1.trans hb,
    FPTASCostSeeds.one_width.2.trans hb⟩
  have hc := floorRatio_cost hone hd
  have hw := floorRatio_width hone hd
  simp only [reciprocalCeilingBits, addCarry_cost, List.length_cons, List.length_nil]
  have hm : max (floorRatio FPTASCostSeeds.one delta).1.length 1 ≤ 3*b+1 := by omega
  omega

lemma decode_specific_sizes {x : Fraction} (hx : x.Valid) :
    x.decode.num.natAbs.size ≤ x.numerator.length ∧ x.decode.den.size ≤ x.denominator.length := by
  have h := decode_num_den_bounds hx
  constructor
  · exact Nat.size_le.mpr (h.1.trans_lt (Decomposition.CostBinary.value_lt_pow_length x.numerator))
  · exact Nat.size_le.mpr (h.2.trans_lt (Decomposition.CostBinary.value_lt_pow_length x.denominator))

/-- Only raw denominator/numerator bit lengths appear in this horizon. -/
def rawHorizon (base delta cap : Fraction) : ℕ :=
  value (reciprocalCeilingBits delta).1 * (base.denominator.length+cap.numerator.length)

lemma rawHorizon_ge_canonical (base delta cap : Fraction)
    (hb : base.Valid) (hd : delta.Valid) (hc : cap.Valid) (hδ : 0 < delta.decode) :
    GridBounds.gridHorizon base.decode delta.decode cap.decode ≤ rawHorizon base delta cap := by
  unfold GridBounds.gridHorizon GridBounds.ratioBits rawHorizon
  apply Nat.mul_le_mul (reciprocalCeilingBits_covers delta hd hδ)
  have hbase := (decode_specific_sizes hb).2
  have hcap := (decode_specific_sizes hc).1
  omega

/-- The raw-width horizon yields precisely the canonical rational grid list. -/
theorem gridBits_raw_refines (base delta ratio cap : Fraction)
    (hb : base.Valid) (hd : delta.Valid) (hr : ratio.Valid) (hc : cap.Valid)
    (ha : 0 < base.decode) (hδ : 0 < delta.decode) (hcap : 0 < cap.decode)
    (hRatio : ratio.decode = 1+delta.decode) :
    (gridBits (rawHorizon base delta cap+1) base ratio cap).1.map Fraction.decode =
      Grids.geometricGrid base.decode delta.decode cap.decode
        (GridBounds.gridHorizon base.decode delta.decode cap.decode) := by
  rw [gridBits_refines _ _ _ _ hb hr hc _ _ _ rfl hRatio rfl]
  apply Grids.geometricGrid_eq_canonical ha hδ hcap
  have hcover := GridBounds.gridHorizon_covers ha hδ hcap
  have hhor := rawHorizon_ge_canonical base delta cap hb hd hc hδ
  have hpow : (1+delta.decode)^GridBounds.gridHorizon base.decode delta.decode cap.decode ≤
      (1+delta.decode)^(rawHorizon base delta cap+1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  exact hcover.trans_le (mul_le_mul_of_nonneg_left hpow ha.le)

lemma rawHorizon_bound (base delta cap : Fraction) {b : ℕ}
    (hb : base.Width b) (hc : cap.Width b) :
    rawHorizon base delta cap ≤ value (reciprocalCeilingBits delta).1*(2*b) := by
  unfold rawHorizon
  apply Nat.mul_le_mul_left
  have := hb.2
  have := hc.1
  omega

lemma reciprocalCeilingBits_le_succ (delta : Fraction) (hd : delta.Valid) (hp : 0 < delta.decode) :
    value (reciprocalCeilingBits delta).1 ≤ GridBounds.blockLength delta.decode+1 := by
  rw [reciprocalCeilingBits_value delta hd hp]
  have hfloor := Nat.floor_le (show (0:ℚ) ≤ 1/delta.decode by positivity)
  have hceil := Nat.le_ceil (1/delta.decode)
  have hh : (⌊1/delta.decode⌋₊ : ℚ) ≤ (⌈1/delta.decode⌉₊ : ℚ) := hfloor.trans hceil
  have hn : ⌊1/delta.decode⌋₊ ≤ ⌈1/delta.decode⌉₊ := by exact_mod_cast hh
  exact Nat.add_le_add_right hn 1

/-- Padding from raw representations preserves polynomial dependence on the
same reciprocal-accuracy parameter used by the mathematical FPTAS. -/
theorem rawHorizon_polynomial (base delta cap : Fraction) {b : ℕ}
    (hb : base.Width b) (hc : cap.Width b) (hd : delta.Valid) (hp : 0 < delta.decode) :
    rawHorizon base delta cap ≤ (GridBounds.blockLength delta.decode+1)*(2*b) := by
  exact (rawHorizon_bound base delta cap hb hc).trans
    (Nat.mul_le_mul_right _ (reciprocalCeilingBits_le_succ delta hd hp))

end BalancedAssortments.FPTASCostGrid
