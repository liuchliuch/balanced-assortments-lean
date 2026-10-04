import BalancedAssortments.NPCNFStackFormulaRead

namespace BalancedAssortments.NPCNF.StackFormula
open NPStack NPStack.Macros StackChain StackGate NPStackFields Encoding

def formulaData (F : BitFormula) : List Bool := dataFields (formulaFields F)

lemma fields_body (F : BitFormula) : formulaFields F=bodyFields F++[[false]] := by
  induction F <;> simp_all [formulaFields,bodyFields,List.append_assoc]
lemma dataFields_append (F G : List (List Bool)) : dataFields (F++G)=dataFields F++dataFields G := by
  simp [dataFields,List.flatMap_append]
lemma formulaData_append (F G : BitFormula) : formulaData (F++G)=bodyData F++formulaData G := by
  simp [formulaData,fields_body,bodyFields,dataFields,List.flatMap_append,bodyData,List.append_assoc]

lemma data_formulaFields_append (F G : BitFormula) :
    dataFields (formulaFields (F++G))=bodyData F++dataFields (formulaFields G) := formulaData_append F G

lemma body_emptyClause : bodyData ([[]] : BitFormula)=blockBits .emptyClause := rfl
lemma formula_empty : formulaData ([] : BitFormula)=blockBits .formulaEnd := rfl

def clauseAllocated (next : List Bool) : BitClause → List Bool
  | [] => []
  | _::bs => chainAllocated next bs

def formulaAllocated (next : List Bool) : BitFormula → List Bool
  | [] => []
  | c::cs => formulaAllocated (bitClause next c).1.2 cs++clauseAllocated next c

def formulaCost (next : List Bool) : BitFormula → List Bool → ℕ
  | [],out => 4*out.length+18
  | []::cs,out => 4*out.length+23+formulaCost next cs (out++bodyData [[]])
  | (a::as)::cs,out => 5*a.labelBits.length+chainCost next a as out+(chainLast next a as).length+29+
      formulaCost (bitChain next a as).1.2 cs (out++bodyData (bitChain next a as).1.1)

/-- The actual finite formula transformer produces exactly the earlier raw
bitFormula OR-chain clauses, including empty clauses and the final marker. -/
theorem formula_run (next : List Bool) (F : BitFormula) (out allocated : List Bool) :
    Run program (formulaCost next F out)
      (cfg .readHeader (store (formulaData F) [] [] next out allocated))
      (cfg .accept (store [] [] [] (bitFormula next F).1.2
        (out++formulaData (bitFormula next F).1.1) (formulaAllocated next F++allocated))) := by
  induction F generalizing next out allocated with
  | nil =>
    have h1 := header_run false [] next out allocated
    have h2 : Step program (cfg .checkInputEnd (store [] [] [] next out allocated))
        (cfg (.saveOutput .formulaEnd) (store [] [] [] next out allocated)) := by
      simp [Step,successors,program,code,Macros.code,macroCode,cfg,Instr.rename,store]
    have h3 := append_constant .formulaEnd (store [] [] [] next out allocated) rfl
    rw [emitted_store] at h3
    have hh := h1.trans (Run.succ h2 h3)
    convert hh using 1 <;> simp [formulaCost,formulaAllocated,bitFormula,formulaData,formulaFields,dataFields,tagBits,
      afterConstant,blockBits,store,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega
  | cons c cs ih =>
    cases c with
    | nil =>
      have h1 := header_run true (false::formulaData cs) next out allocated
      have h2 := first_empty (formulaData cs) next out allocated
      have h3 := append_constant .emptyClause (store (formulaData cs) [] [] next out allocated) rfl
      rw [emitted_store] at h3
      have h4 := ih next (out++bodyData [[]]) allocated
      have hh := h1.trans (h2.trans (h3.trans h4))
      convert hh using 1 <;> simp [formulaCost,formulaAllocated,clauseAllocated,bitFormula,bitClause,formulaData,
        formulaFields,clauseFields,dataFields,tagBits,afterConstant,blockBits,body_emptyClause,
        bodyData,bodyFields,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,store] <;> omega
    | cons a as =>
      let tail := dataFields (clauseFields as)++formulaData cs
      let newOut := out++bodyData (bitChain next a as).1.1
      have h1 := header_run true (tagBits [a.positive]++false::(tagBits a.labelBits++false::tail)) next out allocated
      have h2 := first_literal a.positive tail a.labelBits next out allocated
      have h3 := invoke_chain next a as (formulaData cs) out allocated
      have h4 := clear_left (formulaData cs) (chainLast next a as) (bitChain next a as).1.2 newOut (chainAllocated next as++allocated)
      have h5 := ih (bitChain next a as).1.2 newOut (chainAllocated next as++allocated)
      have hh := h1.trans (h2.trans (h3.trans (h4.trans h5)))
      have ho : newOut++formulaData (bitFormula (bitChain next a as).1.2 cs).1.1 =
          out++formulaData ((bitChain next a as).1.1++(bitFormula (bitChain next a as).1.2 cs).1.1) := by
        simp only [newOut,formulaData_append,List.append_assoc]
      rw [ho] at hh
      convert hh using 1 <;> simp [formulaCost,formulaAllocated,clauseAllocated,bitFormula,bitClause,formulaData_append,
        formulaData,data_formulaFields_append,formulaFields,clauseFields,dataFields,tagBits,tail,newOut,
        List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> try omega
      all_goals simp [fields_body,bodyFields,bodyData,dataFields,List.flatMap_append,List.append_assoc]

end BalancedAssortments.NPCNF.StackFormula
