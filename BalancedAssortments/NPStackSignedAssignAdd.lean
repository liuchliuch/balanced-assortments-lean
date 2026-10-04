import BalancedAssortments.NPStackSignedAssignmentClean
import BalancedAssortments.NPStackSignedAdd

namespace BalancedAssortments.NPStack.SignedAssignAdd
open NPStack ComplexityTimeVerifier SignedAssignment
variable {V : Type*}

def addWork : SignedAddStack→SignedMulStack
  | .ap => .xp | .an => .xn | .bp => .yp | .bn => .yn
  | .scratch => .addScratch | .positive => .positive | .negative => .negative

def program (a b dst : V) : Program (Stack V) State where
  code
    | .multiply (.copy false .readSource) => .jump (.multiply (.add (.positive (.readX false))))
    | .multiply (.add (.negative .done)) => .jump (.clearDest false)
    | .multiply (.add q) => (signedAddProgram.code q).rename
        (fun k => Stack.work (addWork k)) (fun q => State.multiply (.add q))
    | .multiply _ => .halt false
    | q => (SignedAssignment.program a b dst).code q
  start := .copy .xp .readSource
  inputStack := .reg a false
  outputStack := .reg dst false

lemma copy_code (a b dst : V) (o : Operand) : CodeExtends copyProgram (program a b dst)
    (copyMap a b o) (.copy o) := by
  intro q h;cases q <;> simp_all [program,SignedAssignment.program,copyProgram]
lemma move_code (a b dst : V) (n p : Bool) : CodeExtends reverseProgram (program a b dst)
    (moveMap dst n p) (.move n p) := by
  intro q h;cases q <;> simp_all [program,SignedAssignment.program,reverseProgram]

lemma addWork_injective : Function.Injective addWork := by
  intro a b h;cases a <;> cases b <;> simp_all [addWork]
lemma add_code (a b dst : V) : CodeExtends signedAddProgram (program a b dst)
    (fun k => Stack.work (addWork k)) (fun q => State.multiply (.add q)) := by
  intro q h
  cases q with
  | positive q => simp [program]
  | negative q => cases q <;> simp_all [program,signedAddProgram,addProgram,Instr.rename]

end BalancedAssortments.NPStack.SignedAssignAdd
