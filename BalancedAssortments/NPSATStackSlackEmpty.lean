import BalancedAssortments.NPSATStackSlackBound
import BalancedAssortments.NPSATSubsetSumReduction

noncomputable section
namespace BalancedAssortments.NPSATStackSlack
open NPStack NPStack.Structured

def replaceEmpty : Block Reg := .seq (clearStack (.inr .wire)) (pushWord (.inr .wire) NPSATSubsetSum.fixedYes)
def emptyPatch : Block Reg :=
  .branch (.inr .vars)
    (.branch (.inr .clauses) replaceEmpty (.push (.inr .clauses) false) (.push (.inr .clauses) true))
    (.push (.inr .vars) false) (.push (.inr .vars) true)

def patchedWire (n m : ℕ) (wire : List Bool) := if n=0 ∧ m=0 then NPSATSubsetSum.fixedYes else wire

lemma replaceEmpty_exec (vars clauses pre remaining temporary digits number wire : List Bool) :
    Exec replaceEmpty (store vars clauses pre remaining temporary digits number wire)
      (store vars clauses pre remaining temporary digits number NPSATSubsetSum.fixedYes)
      (3*wire.length+2*NPSATSubsetSum.fixedYes.length+3) := by
  have hc:=clearStack_exec (.inr Extra.wire : Reg) (store vars clauses pre remaining temporary digits number wire)
  have hp:=pushWord_exec (.inr Extra.wire : Reg) NPSATSubsetSum.fixedYes (store vars clauses pre remaining temporary digits number [])
  have hc' : Exec (clearStack (.inr .wire)) (store vars clauses pre remaining temporary digits number wire)
      (store vars clauses pre remaining temporary digits number []) (3*wire.length+1) := by
    simpa only [store,update_wire] using hc
  have hp' : Exec (pushWord (.inr .wire) NPSATSubsetSum.fixedYes) (store vars clauses pre remaining temporary digits number [])
      (store vars clauses pre remaining temporary digits number NPSATSubsetSum.fixedYes) (2*NPSATSubsetSum.fixedYes.length+1) := by
    simpa only [store,update_wire,List.append_nil] using hp
  convert hc'.seq hp' using 1 <;> omega

theorem emptyPatch_exec (n m : ℕ) (pre remaining temporary digits number wire : List Bool) :
    ∃t≤3*wire.length+2*NPSATSubsetSum.fixedYes.length+10,Exec emptyPatch
      (store (List.replicate n false) (List.replicate m false) pre remaining temporary digits number wire)
      (store (List.replicate n false) (List.replicate m false) pre remaining temporary digits number (patchedWire n m wire)) t := by
  cases n with
  | zero =>
    cases m with
    | zero =>
      have h:=replaceEmpty_exec [] [] pre remaining temporary digits number wire
      have hi : Exec (.branch (.inr .clauses) replaceEmpty (.push (.inr .clauses) false) (.push (.inr .clauses) true))
          (store [] [] pre remaining temporary digits number wire)
          (store [] [] pre remaining temporary digits number NPSATSubsetSum.fixedYes)
          ((3*wire.length+2*NPSATSubsetSum.fixedYes.length+3)+2) := Exec.branch_nil rfl h
      have ho : Exec emptyPatch (store [] [] pre remaining temporary digits number wire)
          (store [] [] pre remaining temporary digits number NPSATSubsetSum.fixedYes)
          (((3*wire.length+2*NPSATSubsetSum.fixedYes.length+3)+2)+2) := Exec.branch_nil rfl hi
      exact ⟨3*wire.length+2*NPSATSubsetSum.fixedYes.length+7,by omega,by simpa [patchedWire] using ho⟩
    | succ m =>
      have hp:=Exec.push (store [] (List.replicate m false) pre remaining temporary digits number wire) (.inr Extra.clauses) false
      have hi : Exec (.branch (.inr .clauses) replaceEmpty (.push (.inr .clauses) false) (.push (.inr .clauses) true))
          (store [] (List.replicate (m+1) false) pre remaining temporary digits number wire)
          (store [] (List.replicate (m+1) false) pre remaining temporary digits number wire) 3 := by
        apply Exec.branch_false (bs:=List.replicate m false) (by simp [store,List.replicate_succ])
        simpa only [update_clauses,store,List.replicate_succ] using hp
      have ho : Exec emptyPatch (store [] (List.replicate (m+1) false) pre remaining temporary digits number wire)
          (store [] (List.replicate (m+1) false) pre remaining temporary digits number wire) 5 := Exec.branch_nil rfl hi
      exact ⟨5,by omega,by simpa [patchedWire] using ho⟩
  | succ n =>
    have hp:=Exec.push (store (List.replicate n false) (List.replicate m false) pre remaining temporary digits number wire) (.inr Extra.vars) false
    have ho : Exec emptyPatch
        (store (List.replicate (n+1) false) (List.replicate m false) pre remaining temporary digits number wire)
        (store (List.replicate (n+1) false) (List.replicate m false) pre remaining temporary digits number wire) 3 := by
      apply Exec.branch_false (bs:=List.replicate n false) (by simp [store,List.replicate_succ])
      simpa only [update_variables,store,List.replicate_succ] using hp
    exact ⟨3,by omega,by simpa [patchedWire] using ho⟩

end BalancedAssortments.NPSATStackSlack
