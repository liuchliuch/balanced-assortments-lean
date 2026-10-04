import BalancedAssortments.NPSATStackSemantics
import BalancedAssortments.NPSATStackSlackLoop

namespace BalancedAssortments.NPSATStackSemantics
open NPCNF NPCNF.Encoding NPSATSubsetSum ComplexityTimeBinary

lemma zero_prefix_succ (p : ℕ) (row : List ℕ) :
    List.replicate (p+1) 0++row=List.replicate p 0++0::row := by
  rw [List.replicate_add]
  simp

lemma slackBits_value (p r : ℕ) (digit : List Bool) :
    value (NPSATStackSlack.slackBits p r digit)=
      Nat.ofDigits 10 (List.replicate p 0++value digit::List.replicate r 0) := by
  simp [NPSATStackSlack.slackBits,NPSATStackSlack.slackDigits,packBits_value,List.map_append,value]

lemma slackNumbers_value (p m : ℕ) :
    (NPSATStackSlack.slackNumbers p m).map value=
      (slackRows m).map (fun row=>Nat.ofDigits 10 (List.replicate p 0++row)) := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    simp only [NPSATStackSlack.slackNumbers,List.map_cons,slackBits_value,slackRows,List.map_map]
    norm_num only [value,Bool.toNat_true,Bool.toNat_false]
    congr 2
    rw [ih]
    apply List.map_congr_left
    intro row hrow
    rw [zero_prefix_succ]
    rfl

lemma slack_fields_value (raw : Raw) :
    (NPSATStackSlack.slackNumbers raw.catalog.length raw.formula.length).map value=
      (packSlack (zeroColumns raw.catalog).1 (slackColumns raw.formula).1).1.map value := by
  rw [slackNumbers_value,packSlack_value,zeroColumns_eq]
  have h := congrArg (List.map (fun row=>Nat.ofDigits 10 (List.replicate raw.catalog.length 0++row)))
    (slackColumns_values raw.formula)
  simpa [List.map_map,List.map_append,value] using h.symm

lemma targetBits_value (n m : ℕ) :
    value (NPSATStackSlack.targetBits n m)=targetValue n m := by
  rw [targetValue_list]
  simp [NPSATStackSlack.targetBits,NPSATStackSlack.targetDigits,packBits_value,List.map_append,value]

def actualItems (raw : Raw) : List (List Bool) :=
  NPSATStackVariables.variableFields raw.catalog raw.formula raw.catalog++
    NPSATStackSlack.slackNumbers raw.catalog.length raw.formula.length

lemma actualItems_value (raw : Raw) (hF : ∀c∈raw.formula,c.length≤3) :
    (actualItems raw).map value=(construct raw).1.2.map value := by
  rw [actualItems,List.map_append,NPSATStackVariables.variableFields_value _ _ _ hF,slack_fields_value]
  simp [construct]

def successWire (raw : Raw) : List Bool :=
  NPSATStackSlack.resultWire raw.catalog.length raw.formula.length
    (NPSATStackVariables.output raw.catalog raw.formula raw.catalog [])

lemma successWire_fields (raw : Raw) :
    successWire raw=NPCNF.Encoding.encodeFields
      (NPSATStackSlack.targetBits raw.catalog.length raw.formula.length::(actualItems raw).reverse) := by
  simp only [successWire,NPSATStackSlack.resultWire,NPSATStackSlack.slackWire_eq,NPSATStackVariables.output_fields,
    actualItems,List.reverse_append,List.flatMap_append,List.append_nil]
  simp only [NPCNF.Encoding.encodeFields,List.flatMap_cons,List.flatMap_append,List.append_assoc]
  rfl

lemma successWire_correct (raw : Raw) (hv : raw.decode.Valid) (ht : ThreeCNF raw.decode.formula)
    (hne : ¬(raw.catalog=[] ∧ raw.formula=[])) :
    PositiveSubsetSumLanguage (successWire raw) ↔ raw.decode.Sat := by
  rw [successWire_fields]
  apply gadget_refinement raw _ _ hv ht hne
  · rw [targetBits_value,construct_target]
  · apply actualItems_value
    simpa [ThreeCNF,Raw.decode] using ht

end BalancedAssortments.NPSATStackSemantics
