import BalancedAssortments.NPCNFStackReductionSemantics
import BalancedAssortments.NPCNFMeasure

namespace BalancedAssortments.NPCNF.StackReduction
open NPStack NPStack.Macros NPStackFields Encoding

lemma dataFields_reverse_length (xs : List (List Bool)) : (dataFields xs.reverse).length=(dataFields xs).length := by
  simp [NPStackFields.dataFields_length,List.map_reverse]

lemma dataFields_encoding_length (raw : Raw) : (dataFields (fields raw)).length=(encode raw).length := by
  exact (NPStackFieldsEncode.wireFields_length (fields raw)).symm

lemma catalogue_data_le_fields (labels : List (List Bool)) :
    (dataFields labels).length≤(dataFields (catalogFields labels)).length := by
  induction labels with
  | nil => simp [dataFields]
  | cons x xs ih =>
    simp only [catalogFields,dataFields,List.flatMap_cons,List.length_append,List.length_singleton] at *
    simp only [tagBits,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_cons,List.length_nil] at *
    omega

lemma original_parts_bound (raw : Raw) :
    (dataFields raw.catalog).length≤(encode raw).length ∧
    (StackFormula.formulaData raw.formula).length≤(encode raw).length := by
  have h := dataFields_encoding_length raw
  have hc := catalogue_data_le_fields raw.catalog
  change (dataFields (catalogFields raw.catalog++formulaFields raw.formula)).length=_ at h
  rw [StackFormula.dataFields_append,List.length_append] at h
  dsimp only [StackFormula.formulaData]
  omega

lemma fresh_original_bound (raw : Raw) : (StackValidate.freshBits raw.catalog).length≤(encode raw).length+1 := by
  have hm := parsed_rawMeasure_bound (parse_encode raw)
  have hw := (rawMeasure_widths raw).1
  exact StackCatalogue.fresh_length raw.catalog (fun x hx=>(hw x hx).trans hm)

lemma parser_cost_bound (raw : Raw) : parseCost raw≤10*(encode raw).length+2 := by
  have h := dataFields_encoding_length raw
  rw [NPStackFields.dataFields_length] at h
  unfold parseCost
  omega

lemma prepared_original_bound (raw : Raw) :
    StackTransform.preparedSize (StackValidate.freshBits raw.catalog) (reversedInput raw)≤3*(encode raw).length+1 := by
  obtain ⟨hc,hf⟩ := original_parts_bound raw
  have hz := fresh_original_bound raw
  simp only [StackTransform.preparedSize,reversedInput,dataFields_reverse_length]
  omega

lemma transformBudget_mono {a b : ℕ} (h : a≤b) : StackTransform.transformBudget a≤StackTransform.transformBudget b := by
  unfold StackTransform.transformBudget
  gcongr

/-- Everything after validation is bounded in the ORIGINAL flat wire length;
the supplied fresh counter and split records are derived, never input promises. -/
theorem success_cost_bound (raw : Raw) :
    successCost raw≤StackValidate.preparationCost raw+
      StackTransform.transformBudget (3*(encode raw).length+1)+30*(encode raw).length+22 := by
  have hp := parser_cost_bound raw
  have ht := (StackTransform.prepared_cost_bound (StackValidate.freshBits raw.catalog) (reversedInput raw)).trans
    (transformBudget_mono (prepared_original_bound raw))
  obtain ⟨hc,hf⟩ := original_parts_bound raw
  have hz := fresh_original_bound raw
  have ha := dataFields_encoding_length raw
  have hr := dataFields_reverse_length raw.catalog
  dsimp only [StackFormula.formulaData] at hf
  unfold successCost
  omega

theorem success_output_bound (raw : Raw) : (encode (successResult raw)).length≤
    StackTransform.transformBudget (3*(encode raw).length+1) :=
  (StackTransform.encoded_output_bound (StackValidate.freshBits raw.catalog) (reversedInput raw)).trans
    (transformBudget_mono (prepared_original_bound raw))

end BalancedAssortments.NPCNF.StackReduction
