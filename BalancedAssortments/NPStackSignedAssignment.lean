import BalancedAssortments.NPStackSignedMultiplySound
import BalancedAssortments.NPStackReverseLink
import BalancedAssortments.NPStackClearLink

namespace BalancedAssortments.NPStack.SignedAssignment
open NPStack ComplexityTimeVerifier
variable {V : Type*}

inductive Operand | xp | xn | yp | yn deriving DecidableEq, Fintype
inductive Stack (V : Type*)
  | reg (v : V) (negative : Bool) | work (k : SignedMulStack) | copyScratch | transferScratch
  deriving DecidableEq, Fintype
inductive State
  | copy (o : Operand) (q : CopyState) | multiply (q : SignedMulState)
  | clearDest (negative : Bool) | clearFactor (negative : Bool)
  | move (negative pass : Bool) (q : ReverseState) | done
  deriving DecidableEq, Fintype

def operandVariable (a b : V) : Operand→V | .xp | .xn => a | .yp | .yn => b
def operandSign : Operand→Bool | .xp | .yp => false | .xn | .yn => true
def operandWork : Operand→SignedMulStack | .xp => .xp | .xn => .xn | .yp => .yp | .yn => .yn

def copyMap (a b : V) (o : Operand) : CopyStack→Stack V
  | .source => .reg (operandVariable a b o) (operandSign o)
  | .scratch => .copyScratch
  | .target => .work (operandWork o)

def copyNext : Operand→State
  | .xp => .copy .xn .readSource | .xn => .copy .yp .readSource
  | .yp => .copy .yn .readSource | .yn => .multiply (.copy false .readSource)

def outputWork (negative : Bool) : SignedMulStack := if negative then .negative else .positive

def moveMap (dst : V) (negative pass : Bool) : Bool→Stack V :=
  if pass then fun b => if b then .reg dst negative else .transferScratch
  else fun b => if b then .transferScratch else .work (outputWork negative)

def moveNext (negative pass : Bool) : State :=
  if pass then if negative then .done else .move true false .read
  else .move negative true .read

def program (a b dst : V) : Program (Stack V) State where
  code
    | .copy o .done => .jump (copyNext o)
    | .copy o q => (copyProgram.code q).rename (copyMap a b o) (.copy o)
    | .multiply q => if q=(.add (.negative .done)) then .jump (.clearDest false)
      else (signedMultiplyProgram.code q).rename Stack.work State.multiply
    | .clearDest false => .pop (.reg dst false) (.clearDest true) (.clearDest false) (.clearDest false)
    | .clearDest true => .pop (.reg dst true) (.clearFactor false) (.clearDest true) (.clearDest true)
    | .clearFactor false => .pop (.work .yp) (.clearFactor true) (.clearFactor false) (.clearFactor false)
    | .clearFactor true => .pop (.work .yn) (.move false false .read) (.clearFactor true) (.clearFactor true)
    | .move n p .done => .jump (moveNext n p)
    | .move n p q => (reverseProgram.code q).rename (moveMap dst n p) (.move n p)
    | .done => .halt true
  start := .copy .xp .readSource
  inputStack := .reg a false
  outputStack := .reg dst false

def store (s : V→ZBits) (w : SignedMulStack→List Bool) (copy transfer : List Bool) : Stack V→List Bool
  | .reg v n => if n then (s v).2 else (s v).1
  | .work k => w k
  | .copyScratch => copy
  | .transferScratch => transfer

def initialStore (s : V→ZBits) : Stack V→List Bool := store s (fun _ => []) [] []

lemma copyMap_injective (a b : V) (o : Operand) : Function.Injective (copyMap a b o) := by
  intro x y h;cases x <;> cases y <;> simp_all [copyMap]
lemma work_injective : Function.Injective (Stack.work : SignedMulStack→Stack V) := by
  intro a b h
  exact Stack.work.inj h
lemma moveMap_injective (dst : V) (n p : Bool) : Function.Injective (moveMap dst n p) := by
  intro x y h;cases p <;> cases x <;> cases y <;> simp_all [moveMap]

lemma copy_code (a b dst : V) (o : Operand) : CodeExtends copyProgram (program a b dst)
    (copyMap a b o) (.copy o) := by
  intro q h;cases q <;> simp_all [program,copyProgram]
lemma multiply_code (a b dst : V) : CodeExtends signedMultiplyProgram (program a b dst)
    Stack.work State.multiply := by
  intro q h
  have hn : q≠SignedMulState.add (.negative .done) := by intro he;subst q;exact h true rfl
  simp [program,hn]
lemma move_code (a b dst : V) (n p : Bool) : CodeExtends reverseProgram (program a b dst)
    (moveMap dst n p) (.move n p) := by
  intro q h;cases q <;> simp_all [program,reverseProgram]

end BalancedAssortments.NPStack.SignedAssignment
