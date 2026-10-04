import BalancedAssortments.NPSATSubsetSumReduction
import BalancedAssortments.NPSATStackVariables

namespace BalancedAssortments.NPSATStackSemantics
open NPCNF NPCNF.Encoding NPSATSubsetSum ComplexityTimeBinary

lemma listSubsetSum_reverse (items : List ℕ) (target : ℕ) :
    ListSubsetSum items.reverse target ↔ ListSubsetSum items target := by
  constructor
  · rintro ⟨xs,hxs,hs⟩
    exact ⟨xs.reverse,by simpa using hxs.reverse,by simpa using hs⟩
  · rintro ⟨xs,hxs,hs⟩
    exact ⟨xs.reverse,hxs.reverse,by simpa using hs⟩

/-- Arbitrary padded integer fields are accepted by the positive Subset Sum
language exactly according to their decoded values; no normalization is assumed. -/
lemma raw_wire_language (target : List Bool) (items : List (List Bool)) :
    PositiveSubsetSumLanguage (NPCNF.Encoding.encodeFields (target::items)) ↔
      0<value target ∧ (∀x∈items,0<value x) ∧ ListSubsetSum (items.map value) (value target) := by
  unfold PositiveSubsetSumLanguage
  rw [NPCNF.Encoding.parseFields_encode]

lemma raw_reversed_wire_language (target : List Bool) (items : List (List Bool)) :
    PositiveSubsetSumLanguage (NPCNF.Encoding.encodeFields (target::items.reverse)) ↔
      0<value target ∧ (∀x∈items,0<value x) ∧ ListSubsetSum (items.map value) (value target) := by
  rw [raw_wire_language,List.map_reverse,listSubsetSum_reverse]
  simp

/-- Numeric refinement is sufficient for a machine implementation with a
different padded bit representation and reversed output item order. -/
theorem gadget_refinement (raw : Raw) (target : List Bool) (items : List (List Bool))
    (hv : raw.decode.Valid) (ht : ThreeCNF raw.decode.formula)
    (hne : ¬(raw.catalog=[] ∧ raw.formula=[]))
    (hTarget : value target=value (construct raw).1.1)
    (hItems : items.map value=(construct raw).1.2.map value) :
    PositiveSubsetSumLanguage (NPCNF.Encoding.encodeFields (target::items.reverse)) ↔ raw.decode.Sat := by
  have hpositive := construct_positive raw hv hne
  have hi : ∀x∈items,0<value x := by
    intro x hx
    have hm : value x∈items.map value := List.mem_map.mpr ⟨x,hx,rfl⟩
    rw [hItems] at hm
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hm
    rw [← he]
    exact hpositive.2 y hy
  rw [raw_reversed_wire_language,hTarget,hItems]
  exact ⟨fun h=>(construct_correct raw hv ht).mpr h.2.2,
    fun h=>⟨hpositive.1,hi,(construct_correct raw hv ht).mp h⟩⟩

lemma serializeBits_eq_encodePayload (bits : List Bool) :
    FPTASCostProgram.serializeBits bits=NPCNF.Encoding.encodePayload bits := rfl

lemma serialized_fields_eq (fields : List (List Bool)) :
    fields.flatMap FPTASCostProgram.serializeBits=NPCNF.Encoding.encodeFields fields := rfl

end BalancedAssortments.NPSATStackSemantics
