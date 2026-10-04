import BalancedAssortments.NPStackCatalogueMemberRun

namespace BalancedAssortments.NPStackCatalogueMember
open NPStack NPStack.Macros
open NPStackFields (dataFields)
open ComplexityTimeBinary (value)

lemma program_noChoice : NoChoice program := by
  have hout (q : Label Main) (a b : State) :
      (Macros.code macroCode q).rename id State.outer≠.choice a b :=
    rename_not_choice _ id State.outer (compile_noChoice macroCode (.probe false) Register.catalogue Register.output q) a b
  have heq (f : Bool) (q : CompareState) (a b : State) :
      (NPStackLabelEqual.program.code q).rename equalMap (.equal f)≠.choice a b :=
    rename_not_choice _ equalMap (.equal f) (NPStackLabelEqual.program_noChoice q) a b
  intro q a b
  cases q with
  | outer q =>
    cases q with
    | main q => cases q <;> simp only [program,code] <;> first | exact hout _ a b | simp
    | «local» q st => exact hout _ a b
  | equal f q => cases q <;> simp only [program,code] <;> first | exact heq f _ a b | simp

lemma program_deterministic : Deterministic program := noChoice_deterministic program_noChoice

/-- Sound for every accepting execution, with query and catalogue restored
byte-for-byte and all internal work registers empty. -/
theorem accepting_result (query : List Bool) (labels : List (List Bool)) (out : List Bool)
    {t : ℕ} {d : Config Register State}
    (hr : Run program t (cfg (.probe false) (store query (dataFields labels) [] [] [] [] [] [] out)) d)
    (ha : accepts program d) :
    d=cfg .accept (store query (dataFields labels) [] [] [] [] [] []
      (decide (value query∈labels.map value)::out)) ∧ t=memberCost query labels := by
  have hh := (member_run query labels out).halted_unique program_deterministic hr rfl ha
  exact ⟨hh.2.symm,hh.1.symm⟩

lemma matches_original_contains (query : List Bool) (labels : List (List Bool)) :
    decide (value query∈labels.map value)=(NPCNF.Encoding.containsLabel query labels).1 := by
  apply Bool.eq_iff_iff.mpr
  simp [NPCNF.Encoding.containsLabel_correct]

def finiteProgram : FiniteProgram where
  K := Register
  Q := State
  program := program

end BalancedAssortments.NPStackCatalogueMember
