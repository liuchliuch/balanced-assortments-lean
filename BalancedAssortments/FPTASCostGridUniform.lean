import BalancedAssortments.FPTASCostGridFuel

/-! Uniform polynomial interface for the fully charged raw binary grid routine. -/
namespace BalancedAssortments.FPTASCostGrid
open ComplexityTimeBinary KnapsackCostRational

def gridQuota (b Q : ℕ) : ℕ := 2*b*(Q+1)+1
def gridWidth (b Q : ℕ) : ℕ := b+2*b*gridQuota b Q

def gridBudget (b Q : ℕ) : ℕ :=
  (4096*(b+1)^2+48*b+21)+(Q+1)*(2*b+6)+4*(3*b+1)+10*b+14 +
    gridQuota b Q*(2048*(b+2*b*gridQuota b Q+b+b+2)^2+20)+5

lemma reciprocalCeiling_width {delta : Fraction} {b : ℕ} (hb : 1 ≤ b) (hd : delta.Width b) :
    (reciprocalCeilingBits delta).1.length ≤ 3*b+1 := by
  have hone : FPTASCostSeeds.one.Width b := ⟨FPTASCostSeeds.one_width.1.trans hb,
    FPTASCostSeeds.one_width.2.trans hb⟩
  have hh := floorRatio_width hone hd
  simp only [reciprocalCeilingBits, addCarry_length, List.length_cons, List.length_nil]
  omega

lemma rawGrid_quota {base delta cap : Fraction} {b : ℕ}
    (hb : base.Width b) (hc : cap.Width b) (hdv : delta.Valid) (hdp : 0 < delta.decode) :
    rawHorizon base delta cap+1 ≤ gridQuota b (GridBounds.blockLength delta.decode) := by
  have hh := rawHorizon_polynomial base delta cap hb hc hdv hdp
  unfold gridQuota
  nlinarith

theorem rawGrid_uniform_bounds (base delta ratio cap : Fraction) {b : ℕ}
    (hbase : base.Width b) (hratio : ratio.Width b) (hcap : cap.Width b)
    (hdv : delta.Valid) (hdp : 0 < delta.decode) (hbv : base.Valid) (hrv : ratio.Valid) :
    (rawGrid base delta ratio cap).1.length ≤ gridQuota b (GridBounds.blockLength delta.decode) ∧
    ∀ x ∈ (rawGrid base delta ratio cap).1,
      x.Valid ∧ x.Width (gridWidth b (GridBounds.blockLength delta.decode)) := by
  have hk := rawGrid_quota hbase hcap hdv hdp
  simp only [rawGrid, gridTokens_eq, rawGridFuel_length]
  constructor
  · exact (gridBits_length _ _ _ _).trans hk
  · intro x hx
    have hv := gridBits_valid _ _ _ _ hbv hrv x hx
    have hw := gridBits_width _ _ _ _ hbase hratio x hx
    have hm : b+2*b*(rawHorizon base delta cap+1) ≤ gridWidth b (GridBounds.blockLength delta.decode) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left (2*b) hk) b
    exact ⟨hv,⟨hw.1.trans hm,hw.2.trans hm⟩⟩

/-- No field-length, horizon or reciprocal ceiling bound is assumed beyond raw
input widths and a valid positive accuracy fraction. -/
theorem rawGrid_uniform_cost (base delta ratio cap : Fraction) {b : ℕ}
    (hb : 1 ≤ b) (hbase : base.Width b) (hdelta : delta.Width b)
    (hratio : ratio.Width b) (hcap : cap.Width b) (hdv : delta.Valid) (hdp : 0 < delta.decode) :
    (rawGrid base delta ratio cap).2 ≤ gridBudget b (GridBounds.blockLength delta.decode) := by
  let Q := GridBounds.blockLength delta.decode
  let q := value (reciprocalCeilingBits delta).1
  let L := base.denominator.length+cap.numerator.length
  let k := q*L+1
  have hq : q ≤ Q+1 := reciprocalCeilingBits_le_succ delta hdv hdp
  have hL : L ≤ 2*b := by dsimp [L]; have := hbase.2; have := hcap.1; omega
  have hk : k ≤ gridQuota b Q := rawGrid_quota hbase hcap hdv hdp
  have hrec := reciprocalCeilingBits_cost delta hb hdelta
  have hlen := reciprocalCeiling_width hb hdelta
  have ht := rawGrid_cost base delta ratio cap hbase hratio hcap
  have hprod : q*(L+6) ≤ (Q+1)*(2*b+6) := Nat.mul_le_mul hq (by omega)
  have harg : b+2*b*k+b+b+2 ≤ b+2*b*gridQuota b Q+b+b+2 := by
    have := Nat.mul_le_mul_left (2*b) hk
    omega
  have hpoly := Nat.pow_le_pow_left harg 2
  have hterm := Nat.mul_le_mul hk (Nat.add_le_add_right (Nat.mul_le_mul_left 2048 hpoly) 20)
  change (rawGrid base delta ratio cap).2 ≤
    (reciprocalCeilingBits delta).2+q*(L+6)+4*(reciprocalCeilingBits delta).1.length+5*L+14+
      k*(2048*(b+2*b*k+b+b+2)^2+20)+5 at ht
  unfold gridBudget
  change _ ≤ (4096*(b+1)^2+48*b+21)+(Q+1)*(2*b+6)+4*(3*b+1)+10*b+14+
    gridQuota b Q*(2048*(b+2*b*gridQuota b Q+b+b+2)^2+20)+5
  omega

end BalancedAssortments.FPTASCostGrid
