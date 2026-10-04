import BalancedAssortments.NPStackSignedAssignment

namespace BalancedAssortments.NPStack.SignedAssignment
open NPStack ComplexityTimeVerifier
variable {V : Type*} [DecidableEq V]

def sourceReg (a b : V) (o : Operand) : Stack V := .reg (operandVariable a b o) (operandSign o)

lemma copy_run (a b dst : V) (o : Operand) (s : Stack V→List Bool)
    (hw : s .copyScratch=[]) (ht : s (.work (operandWork o))=[]) :
    Run (program a b dst) (5*(s (sourceReg a b o)).length+2)
      ⟨.copy o .readSource,s⟩ ⟨.copy o .done,Function.update s (.work (operandWork o)) (s (sourceReg a b o))⟩ := by
  let xs := s (sourceReg a b o)
  have hs : ∀ k,s (copyMap a b o k)=copyStacks xs [] [] k := by
    intro k;cases k <;> simp [copyMap,copyStacks,xs,sourceReg,hw,ht]
  apply (NPStack.copy_run xs []).relocate_exact (copyMap a b o) (.copy o)
    (copyMap_injective a b o) (copy_code a b dst o) ⟨rfl,hs⟩
  · refine ⟨rfl,?_⟩
    have hh := update_relocated (copyMap a b o) (copyMap_injective a b o)
      (copyStacks xs [] []) s hs .target xs
    intro k
    change (Function.update s (copyMap a b o .target) xs) (copyMap a b o k)=_
    rw [hh]
    cases k <;> simp [copyConfig,copyStacks,Function.update]
  · intro k hk
    exact Function.update_of_ne (Ne.symm (hk .target)) _ _

lemma copy_return (a b dst : V) (o : Operand) (s : Stack V→List Bool) :
    Step (program a b dst) ⟨.copy o .done,s⟩ ⟨copyNext o,s⟩ := by
  simp [Step,successors,program]

def replaceWork (s : Stack V→List Bool) (w : SignedMulStack→List Bool) : Stack V→List Bool
  | .work k => w k
  | k => s k

lemma multiply_run (a b dst : V) (x y : ZBits) (s : Stack V→List Bool)
    (hs : ∀ k,s (.work k)=signedMulInitial x y k) :
    ∃ t≤signedMultiplyBudget x y,
      Run (program a b dst) t ⟨.multiply (.copy false .readSource),s⟩
        ⟨.multiply (.add (.negative .done)),replaceWork s (signedMulFinal y (zmul x y).1)⟩ := by
  obtain ⟨t,ht,hr⟩ := signedMultiply_run x y
  refine ⟨t,ht,hr.relocate_exact Stack.work State.multiply work_injective (multiply_code a b dst)
    ⟨rfl,hs⟩ ⟨rfl,fun _ => rfl⟩ ?_⟩
  intro k hk
  cases k with
  | work k => exact False.elim (hk k rfl)
  | reg v n | copyScratch | transferScratch => rfl

lemma multiply_return (a b dst : V) (s : Stack V→List Bool) :
    Step (program a b dst) ⟨.multiply (.add (.negative .done)),s⟩ ⟨.clearDest false,s⟩ := by
  simp [Step,successors,program]

def clearDestNext (n : Bool) : State := if n then .clearFactor false else .clearDest true
def clearFactorNext (n : Bool) : State := if n then .move false false .read else .clearFactor true
def factorWork (n : Bool) : SignedMulStack := if n then .yn else .yp

lemma clearDest_run (a b dst : V) (n : Bool) (s : Stack V→List Bool) :
    Run (program a b dst) ((s (.reg dst n)).length+1) ⟨.clearDest n,s⟩
      ⟨clearDestNext n,Function.update s (.reg dst n) []⟩ := by
  apply clear_linked
  cases n <;> rfl

lemma clearFactor_run (a b dst : V) (n : Bool) (s : Stack V→List Bool) :
    Run (program a b dst) ((s (.work (factorWork n))).length+1) ⟨.clearFactor n,s⟩
      ⟨clearFactorNext n,Function.update s (.work (factorWork n)) []⟩ := by
  apply clear_linked
  cases n <;> rfl

def moveSource (n p : Bool) : Stack V := if p then .transferScratch else .work (outputWork n)
def moveTarget (dst : V) (n p : Bool) : Stack V := if p then .reg dst n else .transferScratch

lemma move_run (a b dst : V) (n p : Bool) (s : Stack V→List Bool) :
    Run (program a b dst) (2*(s (moveSource n p)).length+1) ⟨.move n p .read,s⟩
      ⟨.move n p .done,Function.update (Function.update s (moveSource n p) []) (moveTarget dst n p)
        ((s (moveSource n p)).reverse++s (moveTarget dst n p))⟩ := by
  apply reverse_linked (moveSource n p) (moveTarget dst n p)
    (by cases p <;> simp [moveSource,moveTarget]) (State.move n p)
  cases p <;> simpa [moveMap,moveSource,moveTarget,reverseStackMap] using move_code a b dst n _

lemma move_return (a b dst : V) (n p : Bool) (s : Stack V→List Bool) :
    Step (program a b dst) ⟨.move n p .done,s⟩ ⟨moveNext n p,s⟩ := by
  simp [Step,successors,program]

end BalancedAssortments.NPStack.SignedAssignment
