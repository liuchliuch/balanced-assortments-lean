import BalancedAssortments.NPCNFStackTransformSemantics

namespace BalancedAssortments.NPCNF.StackTransform
open NPStack NPStack.Macros NPStackFields Encoding

lemma encoder_noChoice : NoChoice NPStackFieldsEncode.program := by
  intro q a b
  cases q with
  | probe s => simp [NPStackFieldsEncode.program]
  | restore s bit => simp [NPStackFieldsEncode.program]
  | read s q => cases q <;> simp [NPStackFieldsEncode.program,NPStackFieldData.readProgram,Instr.rename]
  | emit q => cases q <;> simp [NPStackFieldsEncode.program,NPStackFieldData.emitProgram,Instr.rename]
  | encode q => cases q <;> simp [NPStackFieldsEncode.program,NPStackFieldEncode.program,Instr.rename]
  | accept => simp [NPStackFieldsEncode.program]

lemma program_noChoice : NoChoice program := by
  intro q a b
  have hf (q : StackFormula.State) : (StackFormula.program.code q).rename (Sum.inl : StackChain.Register → Register) State.formula≠.choice a b :=
    rename_not_choice _ _ _ (StackFormula.program_noChoice q) _ _
  have hc (q : Label StackCatalogueOutput.State) : (StackCatalogueOutput.program.code q).rename catalogueMap State.catalogue≠.choice a b :=
    rename_not_choice _ _ _ (compile_noChoice StackCatalogueOutput.macroCode .marker0 .original .output q) _ _
  cases q with
  | formula q =>
    cases q with
    | outer q => cases q with
      | main q => cases q <;> simp only [program,code] <;> first | apply hf | simp
      | «local» q st => exact hf _
    | chain q => exact hf _
  | catalogue q => cases q with
    | main q => cases q <;> simp only [program,code] <;> first | apply hc | simp
    | «local» q st => exact hc _
  | encode q => exact rename_not_choice _ _ _ (encoder_noChoice q) _ _

/-- Any halting execution from the checked prepared record produces the exact
serialized reduction output in the designated output register. -/
theorem transform_halted_correct (next : List Bool) (input : Raw)
    {t : ℕ} {c : Config Register State} {accepted : Bool}
    (hr : Run program t
      ⟨.formula (.outer (.main .readHeader)),store (StackFormula.formulaData input.formula) next [] [] (dataFields input.catalog)⟩ c)
    (hc : program.code c.pc=.halt accepted) :
    t=cost next input ∧ c=⟨.encode .accept,store (encode (result next input)) (bitFormula next input.formula).1.2 [] [] []⟩ := by
  exact hr.halted_unique (noChoice_deterministic program_noChoice) (transform_run next input) hc rfl

end BalancedAssortments.NPCNF.StackTransform
