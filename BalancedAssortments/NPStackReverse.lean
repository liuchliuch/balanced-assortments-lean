import BalancedAssortments.NPStackMachine

namespace BalancedAssortments.NPStack

inductive ReverseState | read | pushFalse | pushTrue | done
  deriving DecidableEq, Fintype

def reverseProgram : Program Bool ReverseState where
  code
    | .read => .pop false .done .pushFalse .pushTrue
    | .pushFalse => .push true false .read
    | .pushTrue => .push true true .read
    | .done => .halt true
  start := .read
  inputStack := false
  outputStack := true

def twoStacks (xs ys : List Bool) : Bool → List Bool := fun k => if k then ys else xs

def reverseConfig (q : ReverseState) (xs ys : List Bool) : Config Bool ReverseState := ⟨q,twoStacks xs ys⟩

@[simp] lemma twoStacks_false (xs ys : List Bool) : twoStacks xs ys false=xs := rfl
@[simp] lemma twoStacks_true (xs ys : List Bool) : twoStacks xs ys true=ys := rfl
@[simp] lemma update_twoStacks_false (xs ys zs : List Bool) :
    Function.update (twoStacks xs ys) false zs=twoStacks zs ys := by funext k; cases k <;> simp [twoStacks]
@[simp] lemma update_twoStacks_true (xs ys zs : List Bool) :
    Function.update (twoStacks xs ys) true zs=twoStacks xs zs := by funext k; cases k <;> simp [twoStacks]

lemma reverse_read_nil (ys : List Bool) :
    Step reverseProgram (reverseConfig .read [] ys) (reverseConfig .done [] ys) := by
  simp [Step,successors,reverseProgram,reverseConfig]

lemma reverse_read_cons (b : Bool) (xs ys : List Bool) :
    Step reverseProgram (reverseConfig .read (b::xs) ys)
      (reverseConfig (if b then .pushTrue else .pushFalse) xs ys) := by
  cases b <;> simp [Step,successors,reverseProgram,reverseConfig]

lemma reverse_push (b : Bool) (xs ys : List Bool) :
    Step reverseProgram (reverseConfig (if b then .pushTrue else .pushFalse) xs ys)
      (reverseConfig .read xs (b::ys)) := by
  cases b <;> simp [Step,successors,reverseProgram,reverseConfig]

/-- An actual finite bytecode run, counting every pop and push transition. -/
theorem reverse_run (xs ys : List Bool) :
    Run reverseProgram (2*xs.length+1) (reverseConfig .read xs ys)
      (reverseConfig .done [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => simpa using Run.one (reverse_read_nil ys)
  | cons b xs ih =>
    have hh := Run.succ (reverse_read_cons b xs ys) (Run.succ (reverse_push b xs ys) (ih (b::ys)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

lemma reverse_initial (xs : List Bool) : initial reverseProgram xs=reverseConfig .read xs [] := by
  unfold initial reverseConfig reverseProgram
  congr 1
  funext k
  cases k <;> simp [twoStacks,Function.update]

/-- Concrete Boolean-stack machine computing list reversal in linear time. -/
theorem reverse_outputs (xs : List Bool) : OutputsIn reverseProgram xs xs.reverse (2*xs.length+1) := by
  refine ⟨2*xs.length+1,le_rfl,reverseConfig .done [] xs.reverse,?_,rfl,rfl⟩
  rw [reverse_initial]
  simpa using reverse_run xs []

def finiteReverse : FiniteProgram where
  K := Bool
  Q := ReverseState
  program := reverseProgram

end BalancedAssortments.NPStack
