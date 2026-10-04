import BalancedAssortments.NPSATStackVariables
import BalancedAssortments.NPCNFStackValidateBounds

namespace BalancedAssortments.NPSATStackZeroColumns
open NPStack NPCNF.Encoding NPStackFields ComplexityTimeBinary

lemma variable_zero (query : List Bool) (labels : List (List Bool))
    (hf : ∀label∈labels,value query≠value label) :
    (NPSATSubsetSum.variableColumns query labels).1=List.replicate labels.length [] := by
  rw [← NPSATStackVariableColumns.digits_refine]
  induction labels with
  | nil => rfl
  | cons label labels ih =>
    have hhead := hf label (by simp)
    have htail := ih (by intro x hx;exact hf x (by simp [hx]))
    simp [NPSATStackVariableColumns.digit,hhead,htail,List.replicate_succ]

lemma advance_zero (query : List Bool) (polarity : Bool) (c : BitClause)
    (hf : ∀l∈c,value query≠value l.labelBits) :
    NPSATStackClauseDigits.advance query polarity .zero c=.zero := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    have hh := hf l (by simp)
    have ht := ih (by intro x hx;exact hf x (by simp [hx]))
    simp [NPSATStackClauseDigits.advance,hh,ht]

lemma clause_zero (query : List Bool) (polarity : Bool) (F : BitFormula)
    (hf : ∀c∈F,∀l∈c,value query≠value l.labelBits) :
    F.map (NPSATStackClauseDigits.clauseDigit query polarity)=List.replicate F.length [] := by
  induction F with
  | nil => rfl
  | cons c cs ih =>
    have hh := advance_zero query polarity c (hf c (by simp))
    have ht := ih (by intro d hd l hl;exact hf d (by simp [hd]) l hl)
    simp [NPSATStackClauseDigits.clauseDigit,hh,ht,NPSATStackThreeCheck.Count.val,List.replicate_succ]

lemma dataFields_zeroes (n : ℕ) : dataFields (List.replicate n [])=List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,dataFields,tagBits] using congrArg (List.cons false) ih

/-- Unary variable-column tokens are produced by an actual label scan.
The numeral in the postcondition is not read or executed by the program. -/
theorem variable_tokens_run (query : List Bool) (labels : List (List Bool)) (out : List Bool) (B : ℕ)
    (hw : ∀label∈labels,label.length≤B) (hf : ∀label∈labels,value query≠value label) :
    ∃t≤54*(labels.length+1)*(query.length+B+1),
      Run (NPStack.Structured.program NPSATStackVariableColumns.loop NPSATStackVariableColumns.Reg.input NPSATStackVariableColumns.Reg.output) t
        ⟨NPStack.Structured.entry NPSATStackVariableColumns.loop,NPSATStackVariableColumns.store (dataFields labels) query [] [] [] [] out⟩
        ⟨NPStack.Structured.finish NPSATStackVariableColumns.loop,NPSATStackVariableColumns.store [] query [] [] [] [] (List.replicate labels.length false++out)⟩ := by
  obtain ⟨t,ht,hr⟩ := NPSATStackVariableColumns.variableColumns_run query labels out B hw
  exact ⟨t,ht,by simpa [variable_zero query labels hf,dataFields_zeroes] using hr⟩

/-- Clause-column tokens likewise come from the concrete three-literal parser. -/
theorem clause_tokens_run (query : List Bool) (F : BitFormula) (out : List Bool)
    (hF : ∀c∈F,c.length≤3) (hf : ∀c∈F,∀l∈c,value query≠value l.labelBits) :
    ∃t ≤ NPSATStackClauseDigits.formulaBudget query F+2,
      Run (NPStack.Structured.program (NPSATStackClauseDigits.formula false) NPSATStackClauseDigits.Reg.input NPSATStackClauseDigits.Reg.output) t
        ⟨NPStack.Structured.entry (NPSATStackClauseDigits.formula false),NPSATStackClauseDigits.store (dataFields (formulaFields F)) query [] [] [] [] [] out⟩
        ⟨NPStack.Structured.finish (NPSATStackClauseDigits.formula false),NPSATStackClauseDigits.store [] query [] [] [] [] [] (List.replicate F.length false++out)⟩ := by
  obtain ⟨t,ht,hr⟩ := NPSATStackClauseDigits.clauseColumns_run false query F out hF
  exact ⟨t,ht,by simpa [clause_zero query false F hf,dataFields_zeroes] using hr⟩

end BalancedAssortments.NPSATStackZeroColumns
