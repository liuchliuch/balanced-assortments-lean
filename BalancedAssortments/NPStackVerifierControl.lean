import BalancedAssortments.NPStackVerifierScriptsBound

namespace BalancedAssortments.NPStack.VerifierControl
open NPStack DirectVerifier ComplexityTimeVerifier
abbrev Stack := VerifierScripts.Stack
abbrev Registers := RowReg→ZBits

/-- A static structured verifier block. Scripts and comparisons are compiled
to their literal finite subroutine instructions below. -/
inductive Command
  | halt (accepted : Bool)
  | script (ops : List ArithmeticAssignment) (next : Command)
  | branchLE (a b : RowReg) (yes no : Command)

def eval : Command→Registers→Bool×Registers
  | .halt b,s => (b,s)
  | .script ops next,s => eval next (evalAssignments ops s)
  | .branchLE a b yes no,s => if (zle (s a) (s b)).1 then eval yes s else eval no s

def State (Q : Type) : Command→Type
  | .halt _ => Unit
  | .script ops next => Sum (ArithmeticScript.State SignedAssignment.State ops) (State Q next)
  | .branchLE _ _ yes no => Sum Q (Sum (State Q yes) (State Q no))

variable {Q : Type} [DecidableEq Q]
instance stateDecidable : (c : Command)→DecidableEq (State Q c)
  | .halt _ => inferInstanceAs (DecidableEq Unit)
  | .script ops next =>
    letI := stateDecidable next
    inferInstanceAs (DecidableEq (ArithmeticScript.State SignedAssignment.State ops ⊕ State Q next))
  | .branchLE _ _ yes no =>
    letI := stateDecidable yes
    letI := stateDecidable no
    inferInstanceAs (DecidableEq (Q ⊕ State Q yes ⊕ State Q no))
instance stateFinite [Fintype Q] : (c : Command)→Fintype (State Q c)
  | .halt _ => inferInstanceAs (Fintype Unit)
  | .script ops next =>
    letI := stateFinite next
    inferInstanceAs (Fintype (ArithmeticScript.State SignedAssignment.State ops ⊕ State Q next))
  | .branchLE _ _ yes no =>
    letI := stateFinite yes
    letI := stateFinite no
    inferInstanceAs (Fintype (Q ⊕ State Q yes ⊕ State Q no))

def start (C : RowReg→RowReg→Program Stack Q) : (c : Command)→State Q c
  | .halt _ => ()
  | .script ops _ => .inl (ArithmeticScript.start VerifierScripts.assignmentProgram ops)
  | .branchLE a b _ _ => .inl (C a b).start

def terminal : (c : Command)→Registers→State Q c
  | .halt _,_ => ()
  | .script ops next,s => .inr (terminal next (evalAssignments ops s))
  | .branchLE a b yes no,s =>
      if (zle (s a) (s b)).1 then .inr (.inl (terminal yes s)) else .inr (.inr (terminal no s))

def code (C : RowReg→RowReg→Program Stack Q) (exit : Bool→Q) :
    (c : Command)→State Q c→Instr Stack (State Q c)
  | .halt b,_ => .halt b
  | .script ops next,.inl q => if q=ArithmeticScript.done ops then .jump (.inr (start C next))
      else ((VerifierScripts.program ops).code q).rename id Sum.inl
  | .script _ next,.inr q => (code C exit next q).rename id Sum.inr
  | .branchLE a b yes no,.inl q =>
      if q=exit true then .jump (.inr (.inl (start C yes)))
      else if q=exit false then .jump (.inr (.inr (start C no)))
      else ((C a b).code q).rename id Sum.inl
  | .branchLE _ _ yes _,.inr (.inl q) => (code C exit yes q).rename id (fun q => .inr (.inl q))
  | .branchLE _ _ _ no,.inr (.inr q) => (code C exit no q).rename id (fun q => .inr (.inr q))

def program (C : RowReg→RowReg→Program Stack Q) (exit : Bool→Q) (c : Command) : Program Stack (State Q c) :=
  ⟨code C exit c,start C c,.reg .zero false,.reg .total false⟩

def cfg (C : RowReg→RowReg→Program Stack Q) (c : Command) (s : Registers) : Config Stack (State Q c) :=
  ⟨start C c,SignedAssignment.initialStore s⟩
def result (c : Command) (s : Registers) : Config Stack (State Q c) :=
  ⟨terminal c s,SignedAssignment.initialStore (eval c s).2⟩

def budget (T : RowReg→RowReg→Registers→ℕ) : Command→Registers→ℕ
  | .halt _,_ => 0
  | .script ops next,s => ArithmeticScript.budget VerifierScripts.assignmentTime ops s+1+
      budget T next (evalAssignments ops s)
  | .branchLE a b yes no,s => T a b s+1+
      if (zle (s a) (s b)).1 then budget T yes s else budget T no s

lemma terminal_halts (C : RowReg→RowReg→Program Stack Q) (exit : Bool→Q) (c : Command) (s : Registers) :
    (program C exit c).code (terminal c s)=.halt (eval c s).1 := by
  induction c generalizing s with
  | halt => rfl
  | script ops next ih =>
    simpa only [program,code,terminal,eval,Instr.rename] using
      (congrArg (Instr.rename id Sum.inr) (ih (evalAssignments ops s)))
  | branchLE a b yes no ihy ihn =>
    cases hb : (zle (s a) (s b)).1 <;>
      simp only [program,terminal,eval,hb,Bool.false_eq_true,if_false,if_true,code]
    · simpa only [program,Instr.rename] using congrArg (Instr.rename id (fun q => Sum.inr (Sum.inr q))) (ihn s)
    · simpa only [program,Instr.rename] using congrArg (Instr.rename id (fun q => Sum.inr (Sum.inl q))) (ihy s)

lemma script_extends (C : RowReg→RowReg→Program Stack Q) (exit : Bool→Q)
    (ops : List ArithmeticAssignment) (next : Command) :
    CodeExtends (VerifierScripts.program ops) (program C exit (.script ops next)) id Sum.inl := by
  intro q h
  have hh : q≠ArithmeticScript.done ops := by
    intro he;subst q
    exact h true (ArithmeticScript.done_halts _ _ _ _ _)
  simp only [program,code,hh,if_false]

lemma compare_extends (C : RowReg→RowReg→Program Stack Q) (exit : Bool→Q)
    (he : ∀ a b v,(C a b).code (exit v)=.halt v) (a b : RowReg) (yes no : Command) :
    CodeExtends (C a b) (program C exit (.branchLE a b yes no)) id Sum.inl := by
  intro q h
  have ht : q≠exit true := by intro hq;subst q;exact h true (he a b true)
  have hf : q≠exit false := by intro hq;subst q;exact h false (he a b false)
  simp only [program,code,ht,hf,if_false]

lemma script_next_extends (C : RowReg→RowReg→Program Stack Q) (exit : Bool→Q)
    (ops : List ArithmeticAssignment) (next : Command) :
    CodeExtends (program C exit next) (program C exit (.script ops next)) id Sum.inr := by intro q h;rfl
lemma yes_extends (C : RowReg→RowReg→Program Stack Q) (exit : Bool→Q)
    (a b : RowReg) (yes no : Command) :
    CodeExtends (program C exit yes) (program C exit (.branchLE a b yes no)) id
      (fun q => Sum.inr (Sum.inl q)) := by intro q h;rfl
lemma no_extends (C : RowReg→RowReg→Program Stack Q) (exit : Bool→Q)
    (a b : RowReg) (yes no : Command) :
    CodeExtends (program C exit no) (program C exit (.branchLE a b yes no)) id
      (fun q => Sum.inr (Sum.inr q)) := by intro q h;rfl

end BalancedAssortments.NPStack.VerifierControl
