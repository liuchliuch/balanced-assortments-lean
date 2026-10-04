import BalancedAssortments.NPSATStackZeroColumns
import BalancedAssortments.NPStackStructuredUnary

set_option maxHeartbeats 3000000
noncomputable section
namespace BalancedAssortments.NPSATStackItem
open NPStack NPStack.Structured NPCNF.Encoding NPStackFields ComplexityTimeBinary

def tokens : Block Reg :=
  .seq (.atom (copyAtom (.inr .catalog) (.inr .scratch) (.inr .catalogWork)))
    (.seq (.atom variableAtom)
      (.seq (.atom (copyAtom (.inr .digits) (.inr .scratch) (.inr .catalogWork)))
        (.seq (clearStack (.inr .digits))
          (.seq (.atom (copyAtom (.inr .formula) (.inr .scratch) (.inr .formulaWork)))
            (.seq (.atom (clauseAtom false))
              (.seq (.atom (copyAtom (.inr .digits) (.inr .scratch) (.inr .formulaWork)))
                (clearStack (.inr .digits))))))))

def tokensBudget (catalog : List (List Bool)) (F : BitFormula) (query : List Bool) (B : ℕ) : ℕ :=
  5*(dataFields catalog).length+54*(catalog.length+1)*(query.length+B+1)+8*catalog.length+
  5*(dataFields (formulaFields F)).length+NPSATStackClauseDigits.formulaBudget query F+8*F.length+19

lemma tokens_exec (catalog : List (List Bool)) (F : BitFormula) (query wire : List Bool) (B : ℕ)
    (hw : ∀label∈catalog,label.length≤B) (hF : ∀c∈F,c.length≤3)
    (hfcat : ∀label∈catalog,value query≠value label)
    (hfform : ∀c∈F,∀l∈c,value query≠value l.labelBits) :
    ∃t ≤ tokensBudget catalog F query B,Exec tokens
      (store (dataFields catalog) (dataFields (formulaFields F)) query [] [] [] [] wire)
      (store (dataFields catalog) (dataFields (formulaFields F)) query
        (List.replicate catalog.length false) (List.replicate F.length false) [] [] wire) t := by
  let cat := dataFields catalog
  let form := dataFields (formulaFields F)
  let nt := List.replicate catalog.length false
  let mt := List.replicate F.length false
  have hcc := copyAtom_run (K := Reg) (.inr .catalog) (.inr .scratch) (.inr .catalogWork)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap]) (store cat form query [] [] [] [] wire) rfl
  have h1 : Exec (.atom (copyAtom (.inr .catalog) (.inr .scratch) (.inr .catalogWork)))
      (store cat form query [] [] [] [] wire) (store cat form query cat [] [] [] wire) (5*cat.length+2) := by
    simpa only [store,List.append_nil,update_catalogWork] using hcc
  obtain ⟨tv,htv,hv⟩ := variable_exec cat form query cat [] [] [] wire catalog rfl B hw
  have h2 : Exec (.atom variableAtom) (store cat form query cat [] [] [] wire)
      (store cat form query [] [] nt [] wire) tv := by
    simpa [NPSATStackZeroColumns.variable_zero query catalog hfcat,NPSATStackZeroColumns.dataFields_zeroes,nt] using hv
  have hcopy := copyAtom_run (K := Reg) (.inr .digits) (.inr .scratch) (.inr .catalogWork)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap]) (store cat form query [] [] nt [] wire) rfl
  have h3 : Exec (.atom (copyAtom (.inr .digits) (.inr .scratch) (.inr .catalogWork)))
      (store cat form query [] [] nt [] wire) (store cat form query nt [] nt [] wire) (5*catalog.length+2) := by
    simpa only [store,List.append_nil,update_catalogWork,nt,List.length_replicate] using hcopy
  have hclear := clearStack_exec (Sum.inr Extra.digits) (store cat form query nt [] nt [] wire)
  have h4 : Exec (clearStack (Sum.inr Extra.digits)) (store cat form query nt [] nt [] wire)
      (store cat form query nt [] [] [] wire) (3*catalog.length+1) := by
    simpa only [store,update_digits,nt,List.length_replicate] using hclear
  have hfc := copyAtom_run (K := Reg) (.inr .formula) (.inr .scratch) (.inr .formulaWork)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap]) (store cat form query nt [] [] [] wire) rfl
  have h5 : Exec (.atom (copyAtom (.inr .formula) (.inr .scratch) (.inr .formulaWork)))
      (store cat form query nt [] [] [] wire) (store cat form query nt form [] [] wire) (5*form.length+2) := by
    simpa only [store,List.append_nil,update_formulaWork] using hfc
  obtain ⟨tc,htc,hc⟩ := clause_exec false cat form query nt [] [] wire F hF
  have h6 : Exec (.atom (clauseAtom false)) (store cat form query nt form [] [] wire)
      (store cat form query nt [] mt [] wire) tc := by
    simpa [NPSATStackZeroColumns.clause_zero query false F hfform,NPSATStackZeroColumns.dataFields_zeroes,mt] using hc
  have hcopy2 := copyAtom_run (K := Reg) (.inr .digits) (.inr .scratch) (.inr .formulaWork)
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap]) (store cat form query nt [] mt [] wire) rfl
  have h7 : Exec (.atom (copyAtom (.inr .digits) (.inr .scratch) (.inr .formulaWork)))
      (store cat form query nt [] mt [] wire) (store cat form query nt mt mt [] wire) (5*F.length+2) := by
    simpa only [store,List.append_nil,update_formulaWork,mt,List.length_replicate] using hcopy2
  have hclear2 := clearStack_exec (Sum.inr Extra.digits) (store cat form query nt mt mt [] wire)
  have h8 : Exec (clearStack (Sum.inr Extra.digits)) (store cat form query nt mt mt [] wire)
      (store cat form query nt mt [] [] wire) (3*F.length+1) := by
    simpa only [store,update_digits,mt,List.length_replicate] using hclear2
  have hall := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))
  refine ⟨_,?_,hall⟩
  unfold tokensBudget
  dsimp only [cat,form] at *
  omega

end BalancedAssortments.NPSATStackItem
