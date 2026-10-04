import BalancedAssortments.NPCNFStackFormulaCost

namespace BalancedAssortments.NPCNF.StackFormula
open NPStack NPStack.Macros StackChain NPStackFields Encoding

lemma program_noChoice : NoChoice program := by
  intro q a b
  have ho := compile_noChoice macroCode .readHeader StackChain.Register.input StackChain.Register.output
  have hc := compile_noChoice StackChain.macroCode (.readSign false) StackChain.Register.input StackChain.Register.output
  have ho' (q : Label Main) : (Macros.code macroCode q).rename id State.outer≠.choice a b :=
    rename_not_choice (Macros.code macroCode q) id State.outer (ho q) a b
  have hc' (q : Label StackChain.State) : ((StackChain.program false).code q).rename id State.chain≠.choice a b :=
    rename_not_choice ((StackChain.program false).code q) id State.chain (hc q) a b
  cases q with
  | outer q =>
    cases q with
    | main q => cases q <;> simp only [program,code] <;> first | apply ho' | simp
    | «local» q st => exact ho' _
  | chain q =>
    cases q with
    | main q => cases q <;> simp only [program,code] <;> first | apply hc' | simp
    | «local» q st => exact hc' _

/-- Every halting execution on a well-formed formula has the exact transformed
formula and counter, not merely the exhibited reduction path. -/
theorem formula_halted_correct (next : List Bool) (F : BitFormula) (out allocated : List Bool)
    {t : ℕ} {c : Config Register State} {accepted : Bool}
    (hr : Run program t (cfg .readHeader (store (formulaData F) [] [] next out allocated)) c)
    (hc : program.code c.pc=.halt accepted) :
    t=formulaCost next F out ∧ c=cfg .accept (store [] [] [] (bitFormula next F).1.2
      (out++formulaData (bitFormula next F).1.1) (formulaAllocated next F++allocated)) := by
  exact hr.halted_unique (noChoice_deterministic program_noChoice) (formula_run next F out allocated) hc rfl

lemma clause_data_length_cons (a : BitLiteral) (c : BitClause) :
    (dataFields (clauseFields (a::c))).length=2*a.labelBits.length+4+(dataFields (clauseFields c)).length := by
  simp [clauseFields,dataFields,tagBits_length]
  omega

lemma formula_data_length_cons (c : BitClause) (cs : BitFormula) :
    (formulaData (c::cs)).length=3+(dataFields (clauseFields c)).length+(formulaData cs).length := by
  simp [formulaData,formulaFields,dataFields,List.flatMap_append,tagBits_length]
  omega

lemma clause_size_bound (c : BitClause) : c.length≤(dataFields (clauseFields c)).length := by
  induction c with
  | nil => simp
  | cons a c ih => rw [clause_data_length_cons];simp only [List.length_cons];omega

lemma formula_size_bound (F : BitFormula) : formulaSize F≤(formulaData F).length := by
  induction F with
  | nil => simp
  | cons c cs ih => rw [formulaSize_cons,formula_data_length_cons];have := clause_size_bound c;omega

lemma clause_label_width (c : BitClause) (l : BitLiteral) (hl : l∈c) :
    l.labelBits.length≤(dataFields (clauseFields c)).length := by
  induction c with
  | nil => simp at hl
  | cons a c ih =>
    rw [clause_data_length_cons]
    rcases List.mem_cons.mp hl with rfl | hl
    · omega
    · have := ih hl;omega

lemma formula_label_width (F : BitFormula) (c : BitClause) (hc : c∈F) (l : BitLiteral) (hl : l∈c) :
    l.labelBits.length≤(formulaData F).length := by
  induction F with
  | nil => simp at hc
  | cons d ds ih =>
    rw [formula_data_length_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · have := clause_label_width c l hl;omega
    · have := ih hc;omega

/-- Prepared-input polynomial bound: I counts all stored input bits supplied
to the transformation, including the raw fresh counter and existing output. -/
theorem formula_cost_input_bound (next : List Bool) (F : BitFormula) (out : List Bool) :
    let I := next.length+(formulaData F).length+out.length
    formulaCost next F out≤(I+1)*(4*I+10000*(I+1)*(3*I+1)) := by
  let I := next.length+(formulaData F).length+out.length
  have hs := formula_size_bound F
  have hh := formulaCost_bound next F out (3*I)
    (by intro c hc l hl;have := formula_label_width F c hc l hl;dsimp [I];omega)
    (by dsimp [I];omega)
  apply hh.trans
  gcongr <;> dsimp [I] <;> omega

end BalancedAssortments.NPCNF.StackFormula
