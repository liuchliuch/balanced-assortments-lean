import BalancedAssortments.NPCNFThreeReduction
import BalancedAssortments.NPCNFStackTransformCost

namespace BalancedAssortments.NPCNF.StackTransform
open NPStack NPStack.Macros NPStackFields Encoding ComplexityTimeBinary

def FreshFor (next : List Bool) (input : Raw) : Prop :=
  ∀ x∈input.catalog,value x<value next

lemma input_bounded (next : List Bool) (input : Raw) (hv : input.decode.Valid) (hf : FreshFor next input) :
    variablesBounded (value next) input.decode.formula := by
  intro c hc l hl
  have hm := hv.2 c hc l hl
  obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
  rw [← he]
  exact hf x hx

lemma result_decode (next : List Bool) (input : Raw) :
    (result next input).decode =
      ⟨input.decode.catalog.reverse++allocatedLabels (value next) (freshCount input.decode.formula),
        (toThree (value next) input.decode.formula).1⟩ := by
  have hf := congrArg Prod.fst (bitFormula_decode next input.formula)
  simp only at hf
  unfold result Raw.decode
  simp only [List.map_append,List.map_reverse,StackFormula.formulaLabels_values]
  rw [hf]

/-- Raw output catalogue validity for any fresh counter above all original
labels. Original order may be reversed; semantic membership and uniqueness are
unchanged. Every allocated label appears exactly once. -/
theorem result_valid (next : List Bool) (input : Raw) (hv : input.decode.Valid) (hf : FreshFor next input) :
    (result next input).decode.Valid := by
  rw [result_decode]
  constructor
  · apply List.nodup_append.mpr
    refine ⟨by simpa using hv.1,allocated_nodup _ _,?_⟩
    intro a ha b hb he
    have hmem : a∈input.decode.catalog := by simpa using ha
    obtain ⟨x,hx,hxa⟩ := List.mem_map.mp hmem
    have hx' := hf x hx
    have hb' := (allocated_mem _ _ b).1 hb
    omega
  · intro c hc l hl
    have horigin := toThree_labels (P := fun z=>z∈input.decode.catalog ∨ value next≤z)
      (value next) input.decode.formula (fun c hc l hl=>Or.inl (hv.2 c hc l hl)) (fun z hz=>Or.inr hz)
    have hbound := toThree_bounded (input_bounded next input hv hf) c hc l hl
    rw [toThree_next] at hbound
    change l.var∈input.decode.catalog.reverse++allocatedLabels (value next) (freshCount input.decode.formula)
    rcases horigin c hc l hl with ho | ho
    · exact List.mem_append_left _ (by simpa using ho)
    · exact List.mem_append_right _ ((allocated_mem _ _ _).2 ⟨ho,hbound⟩)

theorem result_three (next : List Bool) (input : Raw) : ThreeCNF (result next input).decode.formula := by
  rw [result_decode]
  exact toThree_three _ _

theorem result_sat_iff (next : List Bool) (input : Raw) (hv : input.decode.Valid) (hf : FreshFor next input) :
    (result next input).decode.Sat ↔ input.decode.Sat := by
  rw [result_decode]
  exact toThree_sat_iff (input_bounded next input hv hf)

/-- Source/target encoded languages for the exact bytes emitted by the linked
finite transformation on a checked source record. -/
theorem encoded_result_correct (next : List Bool) (input : Raw) (hv : input.decode.Valid) (hf : FreshFor next input) :
    ThreeCNFLanguage (encode (result next input)) ↔ CNFLanguage (encode input) := by
  rw [ThreeCNFLanguage_encode,CNFLanguage_encode]
  exact ⟨fun h=>⟨hv,(result_sat_iff next input hv hf).1 h.2.2⟩,
    fun h=>⟨result_valid next input hv hf,result_three next input,(result_sat_iff next input hv hf).2 h.2⟩⟩

end BalancedAssortments.NPCNF.StackTransform
