import BalancedAssortments.NPStackMachine

namespace BalancedAssortments.NPStack

inductive CopyStack | source | scratch | target deriving DecidableEq, Fintype
inductive CopyState | readSource | save (b : Bool) | readScratch | restore (b : Bool) | emit (b : Bool) | done
  deriving DecidableEq, Fintype

def copyProgram : Program CopyStack CopyState where
  code
    | .readSource => .pop .source .readScratch (.save false) (.save true)
    | .save b => .push .scratch b .readSource
    | .readScratch => .pop .scratch .done (.restore false) (.restore true)
    | .restore b => .push .source b (.emit b)
    | .emit b => .push .target b .readScratch
    | .done => .halt true
  start := .readSource
  inputStack := .source
  outputStack := .target

def copyStacks (xs zs ys : List Bool) : CopyStack → List Bool
  | .source => xs
  | .scratch => zs
  | .target => ys

def copyConfig (q : CopyState) (xs zs ys : List Bool) : Config CopyStack CopyState :=
  ⟨q,copyStacks xs zs ys⟩

@[simp] lemma update_copy_source (xs zs ys vs : List Bool) :
    Function.update (copyStacks xs zs ys) .source vs=copyStacks vs zs ys := by
  funext k; cases k <;> simp [copyStacks]
@[simp] lemma update_copy_scratch (xs zs ys vs : List Bool) :
    Function.update (copyStacks xs zs ys) .scratch vs=copyStacks xs vs ys := by
  funext k; cases k <;> simp [copyStacks]
@[simp] lemma update_copy_target (xs zs ys vs : List Bool) :
    Function.update (copyStacks xs zs ys) .target vs=copyStacks xs zs vs := by
  funext k; cases k <;> simp [copyStacks]

lemma copy_scan (xs zs ys : List Bool) :
    Run copyProgram (2*xs.length+1) (copyConfig .readSource xs zs ys)
      (copyConfig .readScratch [] (xs.reverse++zs) ys) := by
  induction xs generalizing zs with
  | nil => apply Run.one; simp [Step,successors,copyProgram,copyConfig,copyStacks]
  | cons b xs ih =>
    have h1 : Step copyProgram (copyConfig .readSource (b::xs) zs ys) (copyConfig (.save b) xs zs ys) := by
      cases b <;> simp [Step,successors,copyProgram,copyConfig,copyStacks]
    have h2 : Step copyProgram (copyConfig (.save b) xs zs ys) (copyConfig .readSource xs (b::zs) ys) := by
      simp [Step,successors,copyProgram,copyConfig,copyStacks]
    have hh := Run.succ h1 (Run.succ h2 (ih (b::zs)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

lemma copy_restore (xs zs ys : List Bool) :
    Run copyProgram (3*zs.length+1) (copyConfig .readScratch xs zs ys)
      (copyConfig .done (zs.reverse++xs) [] (zs.reverse++ys)) := by
  induction zs generalizing xs ys with
  | nil => apply Run.one; simp [Step,successors,copyProgram,copyConfig,copyStacks]
  | cons b zs ih =>
    have h1 : Step copyProgram (copyConfig .readScratch xs (b::zs) ys) (copyConfig (.restore b) xs zs ys) := by
      cases b <;> simp [Step,successors,copyProgram,copyConfig,copyStacks]
    have h2 : Step copyProgram (copyConfig (.restore b) xs zs ys) (copyConfig (.emit b) (b::xs) zs ys) := by
      simp [Step,successors,copyProgram,copyConfig,copyStacks]
    have h3 : Step copyProgram (copyConfig (.emit b) (b::xs) zs ys) (copyConfig .readScratch (b::xs) zs (b::ys)) := by
      simp [Step,successors,copyProgram,copyConfig,copyStacks]
    have hh := Run.succ h1 (Run.succ h2 (Run.succ h3 (ih (b::xs) (b::ys))))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

/-- Concrete source-preserving copy, including every restoration step. -/
theorem copy_run (xs ys : List Bool) :
    Run copyProgram (5*xs.length+2) (copyConfig .readSource xs [] ys)
      (copyConfig .done xs [] (xs++ys)) := by
  have h1 := copy_scan xs [] ys
  simp only [List.append_nil] at h1
  have hh := h1.trans (copy_restore [] xs.reverse ys)
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hh
  convert hh using 1 <;> omega

def finiteCopy : FiniteProgram where
  K := CopyStack
  Q := CopyState
  program := copyProgram

end BalancedAssortments.NPStack
