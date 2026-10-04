import BalancedAssortments.NPStackStructuredSemantics
import BalancedAssortments.NPStackMacroData

/-! Embedding explicit finite primitive instruction tables as structured atoms.
Only labels are reindexed; every primitive instruction and step is preserved. -/
noncomputable section
namespace BalancedAssortments.NPStack.Structured
open NPStack
variable {K Q : Type*} [Fintype Q]

def atomOfProgram (P : Program K Q) (exit : Q) (he : P.code exit=.halt true) (hn : NoChoice P) : Atom K where
  states := Fintype.card Q
  instructions i := (P.code ((Fintype.equivFin Q).symm i)).rename id (Fintype.equivFin Q)
  start := Fintype.equivFin Q P.start
  exit := Fintype.equivFin Q exit
  halted := by simp [he,Instr.rename]
  noChoice := by
    intro q a b
    cases h : P.code ((Fintype.equivFin Q).symm q) <;> simp [Instr.rename]
    exact False.elim (hn _ _ _ h)

lemma atomOfProgram_extends (P : Program K Q) (exit : Q) (he : P.code exit=.halt true)
    (hn : NoChoice P) (input output : K) :
    CodeExtends P (program (.atom (atomOfProgram P exit he hn)) input output) id (Fintype.equivFin Q) := by
  intro q hq
  simp [program,code,atomOfProgram]

variable [DecidableEq K]

/-- The premises contain an actual primitive Run, never an arbitrary source
function asserted to be executable. The atom's control table is finite. -/
theorem Exec.of_program_run (P : Program K Q) (exit : Q) (he : P.code exit=.halt true)
    (hn : NoChoice P) {s t : Store K} {n : ℕ}
    (h : Run P n ⟨P.start,s⟩ ⟨exit,t⟩) (input output : K) :
    Exec (.atom (atomOfProgram P exit he hn)) s t n := by
  apply Exec.atom input output
  exact sameStore_lift (Fintype.equivFin Q) (atomOfProgram_extends P exit he hn input output) h

/-- Finite external register relocation is compiled into each primitive table
entry. Extra caller stacks are untouched according to the embedding theorem. -/
def relocateProgram {A B : Type*} (P : Program A B) (fk : A → K) (input output : K) : Program K B :=
  ⟨fun q => (P.code q).rename fk id,P.start,input,output⟩

lemma relocateProgram_extends {A B : Type*} (P : Program A B) (fk : A → K) (input output : K) :
    CodeExtends P (relocateProgram P fk input output) fk id := by intro q hq;rfl
lemma relocateProgram_noChoice {A B : Type*} (P : Program A B) (fk : A → K) (input output : K)
    (h : NoChoice P) : NoChoice (relocateProgram P fk input output) := by
  intro q a b
  cases hh : P.code q <;> simp [relocateProgram,hh,Instr.rename]
  exact False.elim (h q _ _ hh)

/-- Exact-register copy becomes a structured finite atom. -/
def copyAtom (source scratch target : K) : Atom K :=
  let P := relocateProgram copyProgram (Macros.copyMap source scratch target) source target
  atomOfProgram P .done rfl (relocateProgram_noChoice _ _ _ _ copy_noChoice)

lemma copyAtom_run (source scratch target : K)
    (hi : Function.Injective (Macros.copyMap source scratch target)) (s : Store K) (hw : s scratch=[]) :
    Exec (.atom (copyAtom source scratch target)) s (Function.update s target (s source++s target))
      (5*(s source).length+2) := by
  let P := relocateProgram copyProgram (Macros.copyMap source scratch target) source target
  have hr := copy_run (s source) (s target)
  have he := hr.relocate_exact (Macros.copyMap source scratch target) id hi
    (relocateProgram_extends copyProgram _ source target)
    (c' := ⟨CopyState.readSource,s⟩) (d' := ⟨CopyState.done,Function.update s target (s source++s target)⟩)
    (by constructor; rfl; intro k;cases k <;> simp [Macros.copyMap,copyConfig,copyStacks,hw])
    (by
      constructor
      · rfl
      · intro k
        have hst : source≠target := fun h => by have hh := hi (show Macros.copyMap source scratch target .source=Macros.copyMap source scratch target .target from h);cases hh
        have hwt : scratch≠target := fun h => by have hh := hi (show Macros.copyMap source scratch target .scratch=Macros.copyMap source scratch target .target from h);cases hh
        cases k <;> simp [Macros.copyMap,copyConfig,copyStacks,Function.update,hst,hwt,hw])
    (by intro k hk;exact Function.update_of_ne (Ne.symm (hk .target)) _ _)
  exact Exec.of_program_run P .done rfl (relocateProgram_noChoice _ _ _ _ copy_noChoice) he source target

end BalancedAssortments.NPStack.Structured
