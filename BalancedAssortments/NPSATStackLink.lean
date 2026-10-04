import BalancedAssortments.NPStackStructuredAtoms

noncomputable section
namespace BalancedAssortments.NPStack.Structured
open NPStack
variable {A Q K : Type*} [DecidableEq A] [DecidableEq K] [Fintype Q]

def embeddedAtom (P : Program A Q) (exit : Q) (he : P.code exit=.halt true)
    (hn : NoChoice P) (fk : A → K) (input output : K) : Atom K :=
  atomOfProgram (relocateProgram P fk input output) exit
    (by simp [relocateProgram,he,Instr.rename])
    (relocateProgram_noChoice P fk input output hn)

/-- A subroutine call is justified by an actual finite primitive run and exact
register projection/frame equalities. No semantic operation is added to code. -/
lemma embeddedAtom_exec (P : Program A Q) (exit : Q) (he : P.code exit=.halt true)
    (hn : NoChoice P) (fk : A → K) (hi : Function.Injective fk) (input output : K)
    {n : ℕ} {s t : Store A} (hr : Run P n ⟨P.start,s⟩ ⟨exit,t⟩)
    (before after : Store K) (hb : ∀a,before (fk a)=s a) (ha : ∀a,after (fk a)=t a)
    (hf : ∀k,(∀a,fk a≠k) → after k=before k) :
    Exec (.atom (embeddedAtom P exit he hn fk input output)) before after n := by
  have hh := hr.relocate_exact fk id hi (relocateProgram_extends P fk input output)
    (c' := ⟨P.start,before⟩) (d' := ⟨exit,after⟩) ⟨rfl,hb⟩ ⟨rfl,ha⟩ hf
  exact Exec.of_program_run (relocateProgram P fk input output) exit
    (by simp [relocateProgram,he,Instr.rename]) (relocateProgram_noChoice P fk input output hn) hh input output

lemma embeddedAtom_exec_writes (P : Program A Q) (exit : Q) (he : P.code exit=.halt true)
    (hn : NoChoice P) (fk : A → K) (hi : Function.Injective fk) (input output : K)
    {n : ℕ} {s t : Store A} (hr : Run P n ⟨P.start,s⟩ ⟨exit,t⟩)
    (before : Store K) (hb : ∀a,before (fk a)=s a) (bindings : List (A×List Bool))
    (ha : Macros.writes s bindings=t) :
    Exec (.atom (embeddedAtom P exit he hn fk input output)) before
      (Macros.writes before (bindings.map (fun p => (fk p.1,p.2)))) n := by
  apply embeddedAtom_exec P exit he hn fk hi input output hr before _ hb
  · intro a
    rw [Macros.writes_project fk hi s before hb bindings a,ha]
  · exact Macros.writes_frame fk before bindings

end BalancedAssortments.NPStack.Structured
