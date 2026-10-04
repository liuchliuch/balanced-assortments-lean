import BalancedAssortments.CookLevinRawInitial

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

def builtDimensions (M : Machine) (word : List Bool) (clock : List Unit) : RawDimensions :=
  ⟨(machineConstants M).q,(machineConstants M).g,
    (FPTASCostSeeds.countBits (rawWindowFuel word clock).1).1,
    (FPTASCostSeeds.countBits clock).1,(machineConstants M).r⟩

lemma builtDimensions_valid (M : Machine) (word : List Bool) (clock : List Unit) :
    DimensionsValid (M.stateExtra+1) (M.symbolExtra+3) (windowWidth word clock.length)
      clock.length (M.rules.length+1) (builtDimensions M word clock) := by
  constructor <;> simp [builtDimensions,machineConstants,FPTASCostSeeds.countBits_value,rawWindowFuel_length]

def builtFormula (M : Machine) (word : List Bool) (clock : List Unit) : Encoding.BitFormula × ℕ :=
  let c := machineConstants M
  let d := builtDimensions M word clock
  let cells := (enumerateBits (rawWindowFuel word clock).1).1
  let steps := (enumerateBits clock).1
  let times := (enumerateBits (()::clock)).1
  rawAppend (rawShape d times steps c.states cells c.symbols c.choices)
    (rawAppend (rawInitial d c.start cells (rawInputCells word clock).1)
      (rawAppend (rawAccept d d.t c.accepting)
        (rawTransitions d steps c.states cells c.symbols c.accepting c.choices c.rules)))

lemma builtFormula_refines (M : Machine) (word : List Bool) (clock : List Unit) :
    decodeFormula (builtFormula M word clock).1=tableauFormula M word clock.length := by
  let d := builtDimensions M word clock
  have hd := builtDimensions_valid M word clock
  have hc : (enumerateBits (rawWindowFuel word clock).1).1.map value=List.range (windowWidth word clock.length) := by
    rw [enumerateBits_decode,rawWindowFuel_length]
  have ht : (enumerateBits (()::clock)).1.map value=List.range (clock.length+1) := by
    rw [enumerateBits_decode]; rfl
  have hs := enumerateBits_decode clock
  unfold builtFormula tableauFormula
  simp only [rawAppend_decode]
  rw [rawShape_refines M hd _ _ _ _ _ _ ht hs (machineConstants_ranges M).1 hc
    (machineConstants_ranges M).2.1 (machineConstants_ranges M).2.2.1]
  rw [rawInitial_refines M word clock hd _ hc]
  rw [rawAccept_refines M hd (Fin.last clock.length) hd.t_eq _ (machineConstants_ranges M).2.2.2]
  rw [rawTransitions_refines M hd _ _ hs hc]

/-- Exact formula and valid catalog produced by the actual structural bit-list
constructor, including all padded binary indices and the initial tape margins. -/
theorem constructRaw_refines (M : Machine) (word : List Bool) (clock : List Unit) :
    (constructRaw (machineConstants M) word clock).1.decode=
      catalogue (tableauFormula M word clock.length) := by
  change (Encoding.catalogueBits (builtFormula M word clock).1).1.decode=_
  rw [Encoding.catalogueBits_decode]
  change catalogue (decodeFormula (builtFormula M word clock).1)=_
  rw [builtFormula_refines]

/-- No semantic oracle remains in this executable map: its output is obtained
from binary index circuits, structural list loops, and self-delimiting emission.
Clock-fuel generation, its polynomial cost, and machine compilation are separate. -/
theorem constructBits_correct (M : Machine) (word : List Bool) (clock : List Unit) :
    Encoding.CNFLanguage (constructBits (machineConstants M) word clock).1 ↔
      AcceptsWithin M word clock.length := by
  simp only [constructBits,Encoding.emit_eq,Encoding.CNFLanguage_encode,constructRaw_refines]
  rw [and_iff_right (catalogue_valid _)]
  change Sat (tableauFormula M word clock.length) ↔ _
  exact tableau_satisfiable_iff_acceptsWithin M word clock.length

end BalancedAssortments.CookLevin
