import BalancedAssortments.FPTASCostProgram
import BalancedAssortments.FPTASCostInputSeeds
import BalancedAssortments.FPTASBounds

/-! All seed/grid/cutoff premises of the actual binary program are discharged
from the raw input representation and the paper's input legality conditions. -/
namespace BalancedAssortments.FPTASCostProgram
open KnapsackCostRational FPTASCostSeeds FPTASCostGrid FPTASCostCutoff FPTAS

def sourceProducts {n : ℕ} (rv : Fin (n+1) → Product) : List Product := (List.finRange (n+1)).map rv
def programDelta {n : ℕ} (alpha epsilon : Fraction) (rv : Fin (n+1) → Product) : Fraction :=
  (prepareSeeds alpha epsilon (sourceProducts rv)).1.1
def programSeeds {n : ℕ} (alpha epsilon : Fraction) (rv : Fin (n+1) → Product) : SeedPack :=
  (prepareSeeds alpha epsilon (sourceProducts rv)).1.2
def programCount {n : ℕ} (rv : Fin (n+1) → Product) : Fraction :=
  countAsFraction (countBits (sourceProducts rv)).1
def programFuel {n : ℕ} (alpha epsilon : Fraction) (rv : Fin (n+1) → Product) : List Unit :=
  (cutoffFuel (countBits (sourceProducts rv)).1 (programDelta alpha epsilon rv)).1
def programScales {n : ℕ} (alpha epsilon : Fraction) (rv : Fin (n+1) → Product) : List Fraction :=
  (rawGrid (programSeeds alpha epsilon rv).scaleBase (programDelta alpha epsilon rv)
    (programSeeds alpha epsilon rv).ratio (programSeeds alpha epsilon rv).scaleCap).1
def programRevenues {n : ℕ} (alpha epsilon : Fraction) (rv : Fin (n+1) → Product) : List Fraction :=
  (rawGrid (programSeeds alpha epsilon rv).revenueBase (programDelta alpha epsilon rv)
    (programSeeds alpha epsilon rv).ratio (programSeeds alpha epsilon rv).revenueCap).1

structure ProgramSeedFacts {n : ℕ} (d : Input n) (ε : ℚ)
    (alpha epsilon capacity : Fraction) (rv : Fin (n+1) → Product) : Prop where
  products_valid : ∀ p ∈ sourceProducts rv, p.1.Valid ∧ p.2.Valid
  capacity_valid : capacity.Valid
  capacity_decode : capacity.decode = d.K
  count_valid : (programCount rv).Valid
  count_decode : (programCount rv).decode = (n+1 : ℚ)
  delta_valid : (programDelta alpha epsilon rv).Valid
  delta_decode : (programDelta alpha epsilon rv).decode = ε/10
  delta_positive : 0 < (programDelta alpha epsilon rv).decode
  seeds_valid : (programSeeds alpha epsilon rv).Valid
  ratio_decode : (programSeeds alpha epsilon rv).ratio.decode = 1+(programDelta alpha epsilon rv).decode
  fuel_length : (programFuel alpha epsilon rv).length = (n+1)*⌈(n+1 : ℚ)/(ε/10)⌉₊
  scales_decode : (programScales alpha epsilon rv).map Fraction.decode = scales d (ε/10)
  revenues_decode : (programRevenues alpha epsilon rv).map Fraction.decode = revenues d (ε/10)
  scales_valid_positive : ∀ τ ∈ programScales alpha epsilon rv, τ.Valid ∧ 0 < τ.decode
  revenues_valid_positive : ∀ ρ ∈ programRevenues alpha epsilon rv, ρ.Valid ∧ 0 < ρ.decode

private lemma rawGrid_valid (base delta ratio cap : Fraction) (hb : base.Valid) (hr : ratio.Valid) :
    ∀ x ∈ (rawGrid base delta ratio cap).1, x.Valid := by
  simp only [rawGrid, gridTokens_eq, rawGridFuel_length]
  exact gridBits_valid _ _ _ _ hb hr

/-- No seed oracle, grid coverage, numerical cutoff, or scalar-count premise
remains: this record is derived for exactly the inputs consumed by runSalesBits. -/
theorem programSeedFacts {n : ℕ} (d : Input n) (hd : Valid d) (ε : ℚ) (hε : 0 < ε)
    (alpha epsilon capacity : Fraction) (rv : Fin (n+1) → Product)
    (hαv : alpha.Valid) (hev : epsilon.Valid) (hcv : capacity.Valid)
    (hαd : alpha.decode = d.α) (hed : epsilon.decode = ε) (hcd : capacity.decode = d.K)
    (hv : ∀ i, (rv i).1.Valid ∧ (rv i).2.Valid)
    (hrd : ∀ i, (rv i).1.decode = d.r i) (hvd : ∀ i, (rv i).2.decode = d.v i) :
    ProgramSeedFacts d ε alpha epsilon capacity rv := by
  have hproducts : ∀ p ∈ sourceProducts rv, p.1.Valid ∧ p.2.Valid := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact hv i
  have hnonempty : sourceProducts rv ≠ [] := by simp [sourceProducts,List.finRange_succ]
  obtain ⟨hδv,hsv⟩ := prepareSeeds_valid alpha epsilon (sourceProducts rv) hαv hev hproducts hnonempty
  obtain ⟨hδd,hbase,hcap,hbest,hrmax,hratio⟩ := prepareSeeds_actual d ε alpha epsilon rv hαd hed hev hv hrd hvd
  change (programDelta alpha epsilon rv).Valid at hδv
  change (programSeeds alpha epsilon rv).Valid at hsv
  change (programDelta alpha epsilon rv).decode = ε/10 at hδd
  change (programSeeds alpha epsilon rv).scaleBase.decode = _ at hbase
  change (programSeeds alpha epsilon rv).scaleCap.decode = _ at hcap
  change (programSeeds alpha epsilon rv).revenueBase.decode = _ at hbest
  change (programSeeds alpha epsilon rv).revenueCap.decode = _ at hrmax
  change (programSeeds alpha epsilon rv).ratio.decode = _ at hratio
  have hδpos : 0 < (programDelta alpha epsilon rv).decode := by rw [hδd]; positivity
  have hratio' : (programSeeds alpha epsilon rv).ratio.decode = 1+(programDelta alpha epsilon rv).decode := by
    rw [hδd]; exact hratio
  have hbasepos : 0 < (programSeeds alpha epsilon rv).scaleBase.decode := by
    rw [hbase]
    exact div_pos (mul_pos hd.2.1 (vmin_pos d (fun i => (hd.1 i).2))) (by positivity)
  have hcappos : 0 < (programSeeds alpha epsilon rv).scaleCap.decode := by
    rw [hcap]
    exact mul_pos hd.2.1 ((hd.1 0).2.trans_le (le_vmax d 0))
  have hbestpos : 0 < (programSeeds alpha epsilon rv).revenueBase.decode := by
    rw [hbest]; exact singletonValue_pos d hd.1
  have hrmaxpos : 0 < (programSeeds alpha epsilon rv).revenueCap.decode := by
    rw [hrmax]; exact (hd.1 0).1.trans_le (le_rmax d 0)
  have hscales : (programScales alpha epsilon rv).map Fraction.decode = scales d (ε/10) := by
    have hh := rawGrid_refines _ _ _ _ hsv.1 hδv hsv.2.2.2.2 hsv.2.1
      hbasepos hδpos hcappos hratio'
    change (programScales alpha epsilon rv).map Fraction.decode = _ at hh
    rw [hbase,hcap,hδd] at hh
    exact hh
  have hrevenues : (programRevenues alpha epsilon rv).map Fraction.decode = revenues d (ε/10) := by
    have hh := rawGrid_refines _ _ _ _ hsv.2.2.1 hδv hsv.2.2.2.2 hsv.2.2.2.1
      hbestpos hδpos hrmaxpos hratio'
    change (programRevenues alpha epsilon rv).map Fraction.decode = _ at hh
    rw [hbest,hrmax,hδd] at hh
    exact hh
  refine ⟨hproducts,hcv,hcd,?_,?_,hδv,hδd,hδpos,hsv,hratio',?_,hscales,hrevenues,?_,?_⟩
  · norm_num [programCount,countAsFraction,Fraction.Valid,ComplexityTimeBinary.value]
  · simp [programCount,countAsFraction,Fraction.decode,countBits_value,sourceProducts,ComplexityTimeBinary.value]
  · have hh := cutoffFuel_length (countBits (sourceProducts rv)).1 hδpos
    simpa [programFuel,countBits_value,sourceProducts,hδd] using hh
  · intro τ hτ
    have hτv := rawGrid_valid _ _ _ _ hsv.1 hsv.2.2.2.2 τ hτ
    have hmem : τ.decode ∈ scales d (ε/10) := by
      rw [← hscales]; exact List.mem_map.mpr ⟨τ,hτ,rfl⟩
    have hpos : 0 < d.α*vmin d/(n+1 : ℚ) := by rw [← hbase]; exact hbasepos
    exact ⟨hτv,hpos.trans_le (Grids.grid_lower_bound hpos.le (by positivity) hmem)⟩
  · intro ρ hρ
    have hρv := rawGrid_valid _ _ _ _ hsv.2.2.1 hsv.2.2.2.2 ρ hρ
    have hmem : ρ.decode ∈ revenues d (ε/10) := by
      rw [← hrevenues]; exact List.mem_map.mpr ⟨ρ,hρ,rfl⟩
    have hpos := singletonValue_pos d hd.1
    exact ⟨hρv,hpos.trans_le (Grids.grid_lower_bound hpos.le (by positivity) hmem)⟩

end BalancedAssortments.FPTASCostProgram
