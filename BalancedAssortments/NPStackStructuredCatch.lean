import BalancedAssortments.NPStackStructuredAtoms

/-! Convert both finite subroutine halts into one actual returned Boolean flag.
This permits total parser-error handling without treating failure as an oracle. -/
noncomputable section
namespace BalancedAssortments.NPStack.Structured
open NPStack
variable {K Q : Type*}

def catchProgram (P : Program K Q) (flag : K) : Program K (Q ⊕ Unit) where
  code
    | .inl q => match P.code q with
      | .halt b => .push flag b (.inr ())
      | i => i.rename id Sum.inl
    | .inr _ => .halt true
  start := .inl P.start
  inputStack := P.inputStack
  outputStack := P.outputStack

lemma catchProgram_extends (P : Program K Q) (flag : K) : CodeExtends P (catchProgram P flag) id Sum.inl := by
  intro q hq
  cases he : P.code q <;> simp [catchProgram,he]
  exact False.elim (hq _ he)
lemma catchProgram_noChoice (P : Program K Q) (flag : K) (h : NoChoice P) : NoChoice (catchProgram P flag) := by
  intro q a b
  cases q with
  | inr q => simp [catchProgram]
  | inl q =>
    cases he : P.code q <;> simp [catchProgram,he,Instr.rename]
    exact False.elim (h q _ _ he)

variable [DecidableEq K]
lemma catchProgram_run (P : Program K Q) (flag : K) {s t : Store K} {q : Q} {n : ℕ} {b : Bool}
    (hr : Run P n ⟨P.start,s⟩ ⟨q,t⟩) (hh : P.code q=.halt b) :
    Run (catchProgram P flag) (n+1) ⟨.inl P.start,s⟩
      ⟨.inr (),Function.update t flag (b::t flag)⟩ := by
  have h1 := sameStore_lift Sum.inl (catchProgram_extends P flag) hr
  have h2 : Step (catchProgram P flag) ⟨.inl q,t⟩ ⟨.inr (),Function.update t flag (b::t flag)⟩ := by
    simp [Step,successors,catchProgram,hh]
  exact h1.trans (Run.one h2)

variable [Fintype Q]
def catchAtom (P : Program K Q) (flag : K) (h : NoChoice P) : Atom K :=
  atomOfProgram (catchProgram P flag) (.inr ()) rfl (catchProgram_noChoice P flag h)

lemma catchAtom_exec (P : Program K Q) (flag : K) (h : NoChoice P)
    {s t : Store K} {q : Q} {n : ℕ} {b : Bool}
    (hr : Run P n ⟨P.start,s⟩ ⟨q,t⟩) (hh : P.code q=.halt b) :
    Exec (.atom (catchAtom P flag h)) s (Function.update t flag (b::t flag)) (n+1) :=
  Exec.of_program_run (catchProgram P flag) (.inr ()) rfl (catchProgram_noChoice P flag h)
    (catchProgram_run P flag hr hh) P.inputStack P.outputStack

end BalancedAssortments.NPStack.Structured
