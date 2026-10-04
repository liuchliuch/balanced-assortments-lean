import BalancedAssortments.NPSATStackVariableColumns
import BalancedAssortments.NPSATStackClauseColumns
import BalancedAssortments.NPSATStackPack
import BalancedAssortments.NPSATStackLink
import BalancedAssortments.NPStackStructuredFieldAtoms

noncomputable section
namespace BalancedAssortments.NPSATStackItem
open NPStack NPStack.Structured NPCNF.Encoding NPStackFields ComplexityTimeBinary

inductive Extra where
  | catalog | formula | query | catalogWork | formulaWork | digits
  | label | copied | scratch | test | sign | wire
  deriving DecidableEq, Fintype
abbrev Reg := MulStack ⊕ Extra

def variableMap : NPSATStackVariableColumns.Reg → Reg
  | .input => .inr .catalogWork | .query => .inr .query | .label => .inr .label
  | .copied => .inr .copied | .scratch => .inr .scratch | .test => .inr .test | .output => .inr .digits

def clauseMap : NPSATStackClauseDigits.Reg → Reg
  | .input => .inr .formulaWork | .query => .inr .query | .label => .inr .label
  | .copied => .inr .copied | .scratch => .inr .scratch | .test => .inr .test
  | .sign => .inr .sign | .output => .inr .digits

def packMap : NPSATStackPack.Reg → Reg
  | .inl k => .inl k | .inr .digits => .inr .digits | .inr .digit => .inr .label

lemma variableMap_injective : Function.Injective variableMap := by
  intro a b h;cases a <;> cases b <;> simp_all [variableMap]
lemma clauseMap_injective : Function.Injective clauseMap := by
  intro a b h;cases a <;> cases b <;> simp_all [clauseMap]
lemma packMap_injective : Function.Injective packMap := by
  intro a b h;rcases a with a|a <;> rcases b with b|b
  · simpa [packMap] using h
  · cases b <;> simp [packMap] at h
  · cases a <;> simp [packMap] at h
  · cases a <;> cases b <;> simp_all [packMap]

def variableAtom : Atom Reg := embeddedAtom (Structured.program NPSATStackVariableColumns.loop NPSATStackVariableColumns.Reg.input NPSATStackVariableColumns.Reg.output)
  (finish NPSATStackVariableColumns.loop) (code_finish NPSATStackVariableColumns.loop) (program_noChoice _ _ _) variableMap (.inr .catalogWork) (.inr .digits)
def clauseAtom (polarity : Bool) : Atom Reg := embeddedAtom (Structured.program (NPSATStackClauseDigits.formula polarity) NPSATStackClauseDigits.Reg.input NPSATStackClauseDigits.Reg.output)
  (finish (NPSATStackClauseDigits.formula polarity)) (code_finish _) (program_noChoice _ _ _) clauseMap (.inr .formulaWork) (.inr .digits)
def packAtom : Atom Reg := embeddedAtom NPSATStackPack.program (.main .done) rfl NPSATStackPack.noChoice packMap (.inr .digits) (.inl .factor)

def item (polarity : Bool) : Block Reg :=
  .seq (.atom (copyAtom (.inr .catalog) (.inr .scratch) (.inr .catalogWork)))
    (.seq (.atom variableAtom)
      (.seq (.atom (copyAtom (.inr .formula) (.inr .scratch) (.inr .formulaWork)))
        (.seq (.atom (clauseAtom polarity))
          (.seq (.atom packAtom)
            (.atom (encodeAtom (.inl .factor) (.inl .input) (.inl .pending) (.inr .wire)))))))

def store (catalog formula query catalogWork formulaWork digits number wire : List Bool) : Store Reg
  | .inr .catalog => catalog | .inr .formula => formula | .inr .query => query
  | .inr .catalogWork => catalogWork | .inr .formulaWork => formulaWork | .inr .digits => digits
  | .inl .factor => number | .inr .wire => wire | _ => []

@[simp] lemma update_catalog (catalog formula query catalogWork formulaWork digits number wire v : List Bool) :
    Function.update (store catalog formula query catalogWork formulaWork digits number wire) (.inr .catalog) v=store v formula query catalogWork formulaWork digits number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_formula (catalog formula query catalogWork formulaWork digits number wire v : List Bool) :
    Function.update (store catalog formula query catalogWork formulaWork digits number wire) (.inr .formula) v=store catalog v query catalogWork formulaWork digits number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_query (catalog formula query catalogWork formulaWork digits number wire v : List Bool) :
    Function.update (store catalog formula query catalogWork formulaWork digits number wire) (.inr .query) v=store catalog formula v catalogWork formulaWork digits number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_catalogWork (catalog formula query catalogWork formulaWork digits number wire v : List Bool) :
    Function.update (store catalog formula query catalogWork formulaWork digits number wire) (.inr .catalogWork) v=store catalog formula query v formulaWork digits number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_formulaWork (catalog formula query catalogWork formulaWork digits number wire v : List Bool) :
    Function.update (store catalog formula query catalogWork formulaWork digits number wire) (.inr .formulaWork) v=store catalog formula query catalogWork v digits number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_digits (catalog formula query catalogWork formulaWork digits number wire v : List Bool) :
    Function.update (store catalog formula query catalogWork formulaWork digits number wire) (.inr .digits) v=store catalog formula query catalogWork formulaWork v number wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_number (catalog formula query catalogWork formulaWork digits number wire v : List Bool) :
    Function.update (store catalog formula query catalogWork formulaWork digits number wire) (.inl .factor) v=store catalog formula query catalogWork formulaWork digits v wire := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

@[simp] lemma update_wire (catalog formula query catalogWork formulaWork digits number wire v : List Bool) :
    Function.update (store catalog formula query catalogWork formulaWork digits number wire) (.inr .wire) v=store catalog formula query catalogWork formulaWork digits number v := by
  funext k;rcases k with k|k <;> cases k <;> simp [store]

lemma variable_exec (catalog formula query cw fw digits number wire : List Bool)
    (labels : List (List Bool)) (hlabels : cw=dataFields labels) (B : ℕ)
    (hw : ∀label∈labels,label.length≤B) :
    ∃t≤54*(labels.length+1)*(query.length+B+1),Exec (.atom variableAtom)
      (store catalog formula query cw fw digits number wire)
      (store catalog formula query [] fw
        (dataFields (NPSATSubsetSum.variableColumns query labels).1.reverse++digits) number wire) t := by
  subst cw
  obtain ⟨t,ht,hr⟩ := NPSATStackVariableColumns.variableColumns_run query labels digits B hw
  refine ⟨t,ht,?_⟩
  have hh := embeddedAtom_exec_writes (Structured.program NPSATStackVariableColumns.loop NPSATStackVariableColumns.Reg.input NPSATStackVariableColumns.Reg.output)
    (finish NPSATStackVariableColumns.loop) (code_finish _) (program_noChoice _ _ _) variableMap variableMap_injective
    (.inr .catalogWork) (.inr .digits) hr (store catalog formula query (dataFields labels) fw digits number wire)
    (by intro a;cases a <;> rfl)
    [(NPSATStackVariableColumns.Reg.input,[]),(NPSATStackVariableColumns.Reg.output,dataFields (NPSATSubsetSum.variableColumns query labels).1.reverse++digits)]
    (by simp [Macros.writes])
  simpa only [variableAtom,Macros.writes,List.map_cons,List.map_nil,variableMap,update_catalogWork,update_digits] using hh

lemma clause_exec (polarity : Bool) (catalog formula query cw digits number wire : List Bool)
    (F : BitFormula) (hF : ∀c∈F,c.length≤3) :
    ∃t≤NPSATStackClauseDigits.formulaBudget query F+2,Exec (.atom (clauseAtom polarity))
      (store catalog formula query cw (dataFields (formulaFields F)) digits number wire)
      (store catalog formula query cw []
        (dataFields (F.map (NPSATStackClauseDigits.clauseDigit query polarity)).reverse++digits) number wire) t := by
  obtain ⟨t,ht,hr⟩ := NPSATStackClauseDigits.clauseColumns_run polarity query F digits hF
  refine ⟨t,ht,?_⟩
  have hh := embeddedAtom_exec_writes (Structured.program (NPSATStackClauseDigits.formula polarity) NPSATStackClauseDigits.Reg.input NPSATStackClauseDigits.Reg.output)
    (finish (NPSATStackClauseDigits.formula polarity)) (code_finish _) (program_noChoice _ _ _) clauseMap clauseMap_injective
    (.inr .formulaWork) (.inr .digits) hr
    (store catalog formula query cw (dataFields (formulaFields F)) digits number wire)
    (by intro a;cases a <;> rfl)
    [(NPSATStackClauseDigits.Reg.input,[]),(NPSATStackClauseDigits.Reg.output,dataFields (F.map (NPSATStackClauseDigits.clauseDigit query polarity)).reverse++digits)]
    (by simp [Macros.writes])
  simpa only [clauseAtom,Macros.writes,List.map_cons,List.map_nil,clauseMap,update_formulaWork,update_digits] using hh

lemma pack_exec (catalog formula query cw fw wire : List Bool) (digits : List (List Bool))
    (hw : ∀d∈digits,d.length≤3) :
    ∃t≤1100*(digits.length+1)*(digits.length*12+4),Exec (.atom packAtom)
      (store catalog formula query cw fw (dataFields digits.reverse) [] wire)
      (store catalog formula query cw fw [] (NPSATSubsetSum.packBits digits).1 wire) t := by
  obtain ⟨t,ht,hr⟩ := NPSATStackPack.pack_run digits 3 hw
  refine ⟨t,by simpa using ht,?_⟩
  have hh := embeddedAtom_exec_writes NPSATStackPack.program (.main .done) rfl NPSATStackPack.noChoice packMap packMap_injective
    (.inr .digits) (.inl .factor) hr (store catalog formula query cw fw (dataFields digits.reverse) [] wire)
    (by intro a;rcases a with a|a <;> cases a <;> rfl)
    [((Sum.inr NPSATStackPack.Extra.digits : NPSATStackPack.Reg),[]),((Sum.inl MulStack.factor : NPSATStackPack.Reg),(NPSATSubsetSum.packBits digits).1)]
    (by simp [Macros.writes])
  simpa only [packAtom,Macros.writes,List.map_cons,List.map_nil,packMap,update_digits,update_number] using hh

end BalancedAssortments.NPSATStackItem
