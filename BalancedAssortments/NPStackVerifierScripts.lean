import BalancedAssortments.NPStackArithmeticScript
import BalancedAssortments.NPStackSignedAssignAddCorrect
import BalancedAssortments.NPStackSignedAssignmentCorrect

namespace BalancedAssortments.NPStack.VerifierScripts
open NPStack DirectVerifier ComplexityTimeVerifier
abbrev Stack := SignedAssignment.Stack RowReg
abbrev AssignmentState := SignedAssignment.State

def assignmentProgram : ArithmeticAssignment→Program Stack AssignmentState
  | .add dst a b => SignedAssignAdd.program a b dst
  | .multiply dst a b => SignedAssignment.program a b dst

def assignmentWidth : ArithmeticAssignment→(RowReg→ZBits)→ℕ
  | .add dst a b,s => max (width (s a)) (max (width (s b)) (width (s dst)))
  | .multiply dst a b,s => max (width (s a)) (max (width (s b)) (width (s dst)))
def assignmentTime (op : ArithmeticAssignment) (s : RowReg→ZBits) : ℕ := 128*(assignmentWidth op s+1)^2

def program (ops : List ArithmeticAssignment) := ArithmeticScript.program assignmentProgram
  (fun _ => SignedAssignment.State.done) (.reg .zero false) (.reg .total false) ops

def cfg (ops : List ArithmeticAssignment) (s : RowReg→ZBits) :
    Config Stack (ArithmeticScript.State AssignmentState ops) :=
  ⟨ArithmeticScript.start assignmentProgram ops,SignedAssignment.initialStore s⟩
def result (ops : List ArithmeticAssignment) (s : RowReg→ZBits) :
    Config Stack (ArithmeticScript.State AssignmentState ops) :=
  ⟨ArithmeticScript.done ops,SignedAssignment.initialStore s⟩

lemma assignment_run (op : ArithmeticAssignment) (s : RowReg→ZBits) :
    ∃ t≤assignmentTime op s,Run (assignmentProgram op) t
      ⟨(assignmentProgram op).start,SignedAssignment.initialStore s⟩
      ⟨.done,SignedAssignment.initialStore (evalAssignment op s)⟩ := by
  cases op with
  | add dst a b =>
    exact SignedAssignAdd.assignment_polynomial a b dst s (le_max_left _ _)
      ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
  | multiply dst a b =>
    exact SignedAssignment.assignment_polynomial a b dst s (le_max_left _ _)
      ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))

lemma assignment_noChoice (op : ArithmeticAssignment) : NoChoice (assignmentProgram op) := by
  cases op with
  | add dst a b => exact SignedAssignAdd.program_noChoice a b dst
  | multiply dst a b => exact SignedAssignment.program_noChoice a b dst

lemma assignment_halts (op : ArithmeticAssignment) : (assignmentProgram op).code .done=.halt true := by
  cases op <;> rfl

/-- Fully instantiated arithmetic script: every operation is expanded to the
actual copy/add/multiply/clear/reversal bytecode proved above. -/
theorem script_run (ops : List ArithmeticAssignment) (s : RowReg→ZBits) :
    ∃ t≤ArithmeticScript.budget assignmentTime ops s,
      Run (program ops) t (cfg ops s) (result ops (evalAssignments ops s)) :=
  ArithmeticScript.run_script assignmentProgram (fun _ => .done) (.reg .zero false) (.reg .total false)
    SignedAssignment.initialStore assignmentTime assignment_halts assignment_run ops s

theorem script_noChoice (ops : List ArithmeticAssignment) : NoChoice (program ops) :=
  ArithmeticScript.program_noChoice assignmentProgram (fun _ => .done) (.reg .zero false) (.reg .total false)
    assignment_noChoice ops

theorem script_halted_result (ops : List ArithmeticAssignment) (s : RowReg→ZBits)
    {t : ℕ} {c : Config Stack (ArithmeticScript.State AssignmentState ops)} {b : Bool}
    (hr : Run (program ops) t (cfg ops s) c) (hc : (program ops).code c.pc=.halt b) :
    t≤ArithmeticScript.budget assignmentTime ops s ∧ c=result ops (evalAssignments ops s) :=
  ArithmeticScript.halted_result assignmentProgram (fun _ => .done) (.reg .zero false) (.reg .total false)
    SignedAssignment.initialStore assignmentTime assignment_halts assignment_run assignment_noChoice ops s hr hc

/-- Concrete realization of the fixed twelve-assignment streaming row
arithmetic, with exact rank/revenue accumulators and witness-total update. -/
theorem accumulator_script_run (s : RowReg→ZBits) (x : WitnessRecord) (hx : HoldsRecord s x) :
    ∃ t≤ArithmeticScript.budget assignmentTime accumulatorAssignments s,
      Run (program accumulatorAssignments) t (cfg accumulatorAssignments s)
        (result accumulatorAssignments (evalAssignments accumulatorAssignments s)) ∧
      (registerState (evalAssignments accumulatorAssignments s)).rank=(streamStep (registerState s) x).rank ∧
      (registerState (evalAssignments accumulatorAssignments s)).revenue=(streamStep (registerState s) x).revenue ∧
      (registerState (evalAssignments accumulatorAssignments s)).total=(streamStep (registerState s) x).total := by
  obtain ⟨t,ht,hr⟩ := script_run accumulatorAssignments s
  have hh := accumulatorAssignments_correct s x hx
  exact ⟨t,ht,hr,hh.1,hh.2.1,hh.2.2.1⟩

def finiteScript (ops : List ArithmeticAssignment) : FiniteProgram where
  K := Stack
  Q := ArithmeticScript.State AssignmentState ops
  program := program ops

end BalancedAssortments.NPStack.VerifierScripts
