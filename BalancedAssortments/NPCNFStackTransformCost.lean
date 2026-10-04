import BalancedAssortments.NPCNFStackTransform

namespace BalancedAssortments.NPCNF.StackTransform
open NPStack NPStack.Macros NPStackFields Encoding

lemma formula_output_sizes (next : List Bool) (F : BitFormula) :
    (StackFormula.formulaData (bitFormula next F).1.1).length≤StackFormula.formulaCost next F [] ∧
    (StackFormula.formulaAllocated next F).length≤StackFormula.formulaCost next F [] := by
  have h := StackFormula.formula_run next F [] []
  have ho := h.stack_length StackChain.Register.output
  have ha := h.stack_length StackChain.Register.allocated
  simpa [StackFormula.cfg,StackChain.store] using And.intro ho ha

lemma cost_bound (next : List Bool) (input : Raw) :
    cost next input≤110*StackFormula.formulaCost next input.formula []+90*(dataFields input.catalog).length+66 := by
  obtain ⟨hf,ha⟩ := formula_output_sizes next input.formula
  rw [StackFormula.formulaAllocated_fields] at ha
  have hc := StackCatalogueOutput.catalogue_cost_bound input.catalog (StackFormula.formulaLabels next input.formula).reverse
  have hout := StackCatalogueOutput.output_length_bound input.catalog (StackFormula.formulaLabels next input.formula).reverse
    (StackFormula.formulaData (bitFormula next input.formula).1.1)
  simp only [List.reverse_reverse] at hout
  have he := NPStackFieldsEncode.encode_cost_linear (fields (result next input))
  have hfields : dataFields (fields (result next input))=
      dataFields (catalogFields (input.catalog.reverse++StackFormula.formulaLabels next input.formula))++
        StackFormula.formulaData (bitFormula next input.formula).1.1 := by
    simp [fields,result,StackFormula.formulaData,dataFields,List.flatMap_append]
  rw [hfields] at he
  unfold cost
  omega

def preparedSize (next : List Bool) (input : Raw) : ℕ :=
  next.length+(StackFormula.formulaData input.formula).length+(dataFields input.catalog).length

def transformBudget (I : ℕ) : ℕ :=
  110*((I+1)*(4*I+10000*(I+1)*(3*I+1)))+90*I+66

/-- Polynomial primitive-step bound from the actual stored prepared input.
Output and allocation sizes follow from primitive stack growth, rather than
being supplied as unproved intermediate bounds. -/
theorem prepared_cost_bound (next : List Bool) (input : Raw) :
    cost next input≤transformBudget (preparedSize next input) := by
  have hc := cost_bound next input
  have hf := StackFormula.formula_cost_input_bound next input.formula []
  simp only [List.length_nil,Nat.add_zero] at hf
  let I := preparedSize next input
  have hbase : next.length+(StackFormula.formulaData input.formula).length≤I := by dsimp [I,preparedSize];omega
  have hcat : (dataFields input.catalog).length≤I := by dsimp [I,preparedSize];omega
  have hp : StackFormula.formulaCost next input.formula []≤(I+1)*(4*I+10000*(I+1)*(3*I+1)) := by
    apply hf.trans
    gcongr
  dsimp only [transformBudget]
  nlinarith

theorem encoded_output_bound (next : List Bool) (input : Raw) :
    (encode (result next input)).length≤transformBudget (preparedSize next input) := by
  have h := (transform_run next input).stack_length (Sum.inl StackChain.Register.input)
  simp only [store,StackChain.store] at h
  -- The reused output register initially holds the original tagged formula.
  have hc := prepared_cost_bound next input
  have houtput : (encode (result next input)).length≤
      (StackFormula.formulaData input.formula).length+cost next input := h
  -- A sharper bound follows from catalogue assembly and serialization lengths.
  obtain ⟨hf,ha⟩ := formula_output_sizes next input.formula
  rw [StackFormula.formulaAllocated_fields] at ha
  have hout := StackCatalogueOutput.output_length_bound input.catalog (StackFormula.formulaLabels next input.formula).reverse
    (StackFormula.formulaData (bitFormula next input.formula).1.1)
  simp only [List.reverse_reverse] at hout
  have hlen : (encode (result next input)).length=
      (dataFields (catalogFields (input.catalog.reverse++StackFormula.formulaLabels next input.formula))++
       StackFormula.formulaData (bitFormula next input.formula).1.1).length := by
    change (NPStackFieldsEncode.wireFields (fields (result next input))).length=_
    rw [NPStackFieldsEncode.wireFields_length]
    simp [fields,result,StackFormula.formulaData,dataFields,List.flatMap_append]
  rw [hlen]
  have hI : (dataFields input.catalog).length≤preparedSize next input := by unfold preparedSize;omega
  have hfc := StackFormula.formula_cost_input_bound next input.formula []
  simp only [List.length_nil,Nat.add_zero] at hfc
  have hp : StackFormula.formulaCost next input.formula []≤
      (preparedSize next input+1)*(4*preparedSize next input+10000*(preparedSize next input+1)*(3*preparedSize next input+1)) := by
    apply hfc.trans
    gcongr <;> unfold preparedSize <;> omega
  unfold transformBudget
  omega

end BalancedAssortments.NPCNF.StackTransform
