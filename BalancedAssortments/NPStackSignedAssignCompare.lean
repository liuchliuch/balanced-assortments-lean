import BalancedAssortments.NPStackSignedAssignmentCopy
import BalancedAssortments.NPStackSignedFractionSound

namespace BalancedAssortments.NPStack.SignedAssignCompare
open NPStack ComplexityTimeVerifier SignedAssignment
variable {V : Type*} [DecidableEq V]

inductive State | copy (o : Operand) (q : CopyState) | compare (q : SignedCompareState) | result (bit : Bool)
  deriving DecidableEq, Fintype

def copyNext : Operand→State
  | .xp => .copy .xn .readSource | .xn => .copy .yp .readSource
  | .yp => .copy .yn .readSource | .yn => .compare (.addLeft (.readX false))

def compareMap : SignedCompareStack→Stack V
  | .ap => .work .xp | .an => .work .xn | .bp => .work .yp | .bn => .work .yn
  | .leftSum => .work (.product .pp) | .rightSum => .work (.product .nn)
  | .scratch => .work .addScratch | .output => .work .positive

def program (a b : V) : Program (Stack V) State where
  code
    | .copy o .done => .jump (copyNext o)
    | .copy o q => (copyProgram.code q).rename (copyMap a b o) (.copy o)
    | .compare q => if q=(.compare .done) then .pop (.work .positive) (.result false) (.result false) (.result true)
      else (signedCompareProgram.code q).rename compareMap State.compare
    | .result b => .halt b
  start := .copy .xp .readSource
  inputStack := .reg a false
  outputStack := .work .positive

lemma copy_code (a b : V) (o : Operand) : CodeExtends copyProgram (program a b)
    (copyMap a b o) (.copy o) := by
  intro q h;cases q <;> simp_all [program,copyProgram]
lemma compareMap_injective : Function.Injective (compareMap : SignedCompareStack→Stack V) := by
  intro a b h;cases a <;> cases b <;> simp_all [compareMap]
lemma compare_code (a b : V) : CodeExtends signedCompareProgram (program a b)
    compareMap State.compare := by
  intro q h
  have hn : q≠SignedCompareState.compare .done := by intro he;subst q;exact h true rfl
  simp [program,hn]

lemma copy_run (a b : V) (o : Operand) (s : Stack V→List Bool)
    (hw : s .copyScratch=[]) (ht : s (.work (operandWork o))=[]) :
    Run (program a b) (5*(s (sourceReg a b o)).length+2)
      ⟨.copy o .readSource,s⟩ ⟨.copy o .done,Function.update s (.work (operandWork o)) (s (sourceReg a b o))⟩ := by
  let xs := s (sourceReg a b o)
  have hs : ∀ k,s (copyMap a b o k)=copyStacks xs [] [] k := by
    intro k;cases k <;> simp [copyMap,copyStacks,xs,sourceReg,hw,ht]
  apply (NPStack.copy_run xs []).relocate_exact (copyMap a b o) (.copy o)
    (copyMap_injective a b o) (copy_code a b o) ⟨rfl,hs⟩
  · refine ⟨rfl,?_⟩
    have hh := update_relocated (copyMap a b o) (copyMap_injective a b o)
      (copyStacks xs [] []) s hs .target xs
    intro k
    change (Function.update s (copyMap a b o .target) xs) (copyMap a b o k)=_
    rw [hh]
    cases k <;> simp [copyConfig,copyStacks,Function.update]
  · intro k hk
    exact Function.update_of_ne (Ne.symm (hk .target)) _ _

lemma copy_return (a b : V) (o : Operand) (s : Stack V→List Bool) :
    Step (program a b) ⟨.copy o .done,s⟩ ⟨copyNext o,s⟩ := by
  simp [Step,successors,program]

end BalancedAssortments.NPStack.SignedAssignCompare
