import BalancedAssortments.NPStackVerifierControlRun
import BalancedAssortments.NPStackSignedAssignCompareCorrect
import BalancedAssortments.DirectVerifierHeader

namespace BalancedAssortments.NPStack.VerifierCommands
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

abbrev Control := SignedAssignCompare.State

def comparisons (a b : RowReg) : Program VerifierControl.Stack Control := SignedAssignCompare.program a b

def compareTime (a b : RowReg) (s : Registers) : ℕ := SignedAssignCompare.guardCost (s a) (s b)

def program (c : Command) := VerifierControl.program comparisons SignedAssignCompare.State.result c

def cfg (c : Command) (s : Registers) := VerifierControl.cfg comparisons c s

lemma comparison_halts (a b : RowReg) (v : Bool) : (comparisons a b).code (.result v)=.halt v := rfl
lemma comparison_runs (a b : RowReg) (s : Registers) :
    ∃ t≤compareTime a b s,Run (comparisons a b) t ⟨(comparisons a b).start,SignedAssignment.initialStore s⟩
      ⟨.result (zle (s a) (s b)).1,SignedAssignment.initialStore s⟩ :=
  ⟨_,le_rfl,SignedAssignCompare.guard_run a b s⟩

/-- Every static verifier guard block is now a literal finite Boolean-stack
program with total operational correctness, not an arithmetic callback. -/
theorem command_run (c : Command) (s : Registers) :
    ∃ t≤VerifierControl.budget compareTime c s,
      Run (program c) t (cfg c s) (VerifierControl.result c s) :=
  VerifierControl.run_command comparisons SignedAssignCompare.State.result compareTime
    comparison_halts comparison_runs c s

theorem command_noChoice (c : Command) : NoChoice (program c) :=
  VerifierControl.program_noChoice comparisons SignedAssignCompare.State.result
    SignedAssignCompare.program_noChoice c

theorem command_halted_result (c : Command) (s : Registers)
    {t : ℕ} {out : Config VerifierControl.Stack (VerifierControl.State Control c)} {b : Bool}
    (hr : Run (program c) t (cfg c s) out) (hc : (program c).code out.pc=.halt b) :
    t≤VerifierControl.budget compareTime c s ∧ out=VerifierControl.result c s :=
  VerifierControl.halted_result comparisons SignedAssignCompare.State.result compareTime
    comparison_halts comparison_runs SignedAssignCompare.program_noChoice c s hr hc

def guardLE (a b : RowReg) (next : Command) : Command := .branchLE a b next (.halt false)
def guardPositive (a : RowReg) (next : Command) : Command := .branchLE a .zero (.halt false) next

def maxCommand : Command := .branchLE .maximum .numerator
  (.script [.add .maximum .numerator .zero] (.halt true)) (.halt true)

def rowCommand (active : Bool) : Command :=
  guardPositive .priceDen <| guardPositive .price <|
  guardPositive .attractionDen <| guardPositive .attraction <|
  guardLE .zero .numerator <| .script capAssignments <|
  guardLE .term .product <|
  (if active then .script accumulatorAssignments maxCommand
   else guardLE .numerator .zero (.script accumulatorAssignments maxCommand))

def headerCommand : Command :=
  guardLE .declaredCount .count <| guardLE .count .declaredCount <|
  guardPositive .count <| guardPositive .capacity <| guardLE .capacity .count <|
  guardPositive .alpha <| guardPositive .alphaDen <| guardLE .alpha .alphaDen <|
  guardPositive .targetDen <| guardPositive .q (.halt true)

def rankCommand : Command := .script finalAssignments (guardLE .rankNum .product (.halt true))
def revenueCommand : Command := .script revenueAssignments (guardLE .term .product (.halt true))
def balanceCommand (active : Bool) : Command :=
  if active then .script balanceAssignments (guardLE .term .product (.halt true)) else .halt true

def finiteCommand (c : Command) : FiniteProgram where
  K := VerifierControl.Stack
  Q := VerifierControl.State Control c
  program := program c

lemma eval_script (ops : List ArithmeticAssignment) (next : Command) (s : Registers) :
    eval (.script ops next) s=eval next (evalAssignments ops s) := rfl
lemma maxCommand_accepts (s : Registers) : (eval maxCommand s).1=true := by
  unfold maxCommand eval
  split_ifs <;> rfl

lemma guardLE_accepts (a b : RowReg) (next : Command) (s : Registers) :
    (eval (guardLE a b next) s).1=((zle (s a) (s b)).1 && (eval next s).1) := by
  cases h : (zle (s a) (s b)).1 <;> simp [guardLE,eval,h]
lemma guardPositive_accepts (a : RowReg) (next : Command) (s : Registers) :
    (eval (guardPositive a next) s).1=(!(zle (s a) (s .zero)).1 && (eval next s).1) := by
  cases h : (zle (s a) (s .zero)).1 <;> simp [guardPositive,eval,h]

end BalancedAssortments.NPStack.VerifierCommands
