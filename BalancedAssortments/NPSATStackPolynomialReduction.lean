import BalancedAssortments.NPSATStackReductionSuccess
import BalancedAssortments.NPSATStackReductionSemantics
import BalancedAssortments.NPSATStackGadgetBound
import BalancedAssortments.NPStackClockedCorrect

set_option synthInstance.maxSize 10000
set_option maxRecDepth 4096
noncomputable section
namespace BalancedAssortments.NPSATStackReduction
open NPStack NPCNF.Encoding NPStackFields

lemma bad_reject (bits : List Bool) (hn : ¬NPSATStackPrepare.GoodInput bits) :
    ∃t s,Run program t (initial program bits) ⟨.reject,s⟩ := by
  obtain ⟨t,p,hr⟩ := NPSATStackPrepare.bad_input_reject bits hn
  let s := combined p (fun _=>[])
  have hh := hr.relocate_exact prepareMap State.prepare Sum.inl_injective prepare_extends
    (c' := ⟨.prepare NPSATStackPrepare.program.start,combined (initial NPSATStackPrepare.program bits).stk (fun _=>[])⟩)
    (d' := ⟨.prepare .reject,s⟩) ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;rcases k with k|k
        · exact False.elim (hk k rfl)
        · rfl)
  have hj : Step program ⟨.prepare .reject,s⟩ ⟨.reject,s⟩ := by
    simp [Step,successors,program,code,Macros.returnCode,NPSATStackPrepare.program,NPSATStackPrepare.code]
  refine ⟨t+1,s,?_⟩
  rw [initial_combined]
  exact hh.trans (Run.one hj)

/-- Soundness covers every accepting execution, without any clock or legality
assumption. Bad inputs have an actual rejecting prefix of the same program. -/
theorem accepting_output (bits : List Bool) {t : ℕ} {c : Config Reg State}
    (hr : Run program t (initial program bits) c) (ha : accepts program c) : c.stk output=reduction bits := by
  classical
  by_cases hg : NPSATStackPrepare.GoodInput bits
  · obtain ⟨raw,hp,hv,ht⟩ := hg
    obtain ⟨u,hu,known⟩ := valid_run raw hv ht
    rw [← NPSATStackPrepare.parse_input_eq_encode bits raw hp] at known
    have he := hr.halted_unique (noChoice_deterministic noChoice) known ha rfl
    rw [he.2]
    exact (final_output raw).trans (reduction_of_good bits raw hp hv ht).symm
  · obtain ⟨u,s,hrej⟩ := bad_reject bits hg
    exact False.elim (rejecting_run_excludes_acceptance (noChoice_deterministic noChoice) hrej rfl hr ha)

/-- A literal polynomial in the original encoded input length. It includes
parsing, semantic catalogue validation, all three physical register copies,
complete arithmetic construction, wire serialization and the empty-case patch. -/
def validClock : Polynomial ℕ :=
  1100*(Polynomial.X+1)^3+NPSATStackGadget.completedPolynomial+10*Polynomial.X+16

lemma validClock_eval (N : ℕ) : validClock.eval N=
    1100*(N+1)^3+NPSATStackGadget.completedPolynomial.eval N+10*N+16 := by
  simp [validClock]

lemma successBudget_bound (raw : Raw) (ht : NPCNF.ThreeCNF raw.decode.formula) :
    successBudget raw≤validClock.eval (encode raw).length := by
  have hp := NPSATStackPrepare.successCost_bound raw
  have hg := NPSATStackGadget.completed_budget_original raw ((NPSATStackPrepare.three_raw_iff raw).mp ht)
  have hs := NPCNF.StackValidate.output_size_bound raw
  have hlen : (dataFields (fields raw)).length=(encode raw).length :=
    (NPStackFields.dataFields_length _).trans (NPStackFields.encoding_length _).symm
  rw [validClock_eval]
  unfold successBudget constructBudget
  omega

theorem good_computes (bits : List Bool) (hg : NPSATStackPrepare.GoodInput bits) :
    OutputsIn program bits (reduction bits) (validClock.eval bits.length) := by
  obtain ⟨raw,hp,hv,ht⟩ := hg
  obtain ⟨t,hbound,hr⟩ := valid_run raw hv ht
  have henc := NPSATStackPrepare.parse_input_eq_encode bits raw hp
  refine ⟨t,?_,⟨.accept,finalStore raw⟩,?_,rfl,?_⟩
  · rw [henc]
    exact hbound.trans (successBudget_bound raw ht)
  · rwa [henc]
  · exact (final_output raw).trans (reduction_of_good bits raw hp hv ht).symm

def finiteProgram : FiniteProgram where
  K := Reg
  Q := State
  program := program

/-- The complete total reduction is a genuine finite Boolean-stack program.
Clock generation, timeout execution and fixed-no fallback emission are also
compiled programs, not assumed cost annotations around the semantic function. -/
theorem reduction_polyComputable : PolyComputable reduction :=
  Clocked.polyComputable finiteProgram reduction NPSATStackPrepare.GoodInput validClock NPSATSubsetSum.fixedNo
    noChoice (fun bits t c hr ha=>accepting_output bits hr ha) good_computes reduction_of_not_good

/-- Unconditional machine-backed many-one reduction on the exact serialized
languages, including malformed input, redundant labels and zero dimensions. -/
theorem three_cnf_reduces_positiveSubsetSum :
    PolyManyOne NPCNF.Encoding.ThreeCNFLanguage NPSATSubsetSum.PositiveSubsetSumLanguage := by
  exact ⟨reduction,reduction_polyComputable,fun bits=>(reduction_correct bits).symm⟩

end BalancedAssortments.NPSATStackReduction
