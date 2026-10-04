import BalancedAssortments.NPStackSignedAssignCompareCopy
import BalancedAssortments.NPStackEmbeddingDeterministic

namespace BalancedAssortments.NPStack.SignedAssignCompare
open NPStack ComplexityTimeVerifier SignedAssignment
variable {V : Type*} [DecidableEq V]
set_option maxHeartbeats 1500000

lemma compare_run (a b : V) (s : V→ZBits) :
    Run (program a b) (signedCompareTime (s a) (s b))
      ⟨.compare (.addLeft (.readX false)),store s (signedMulInitial (s a) (s b)) [] []⟩
      ⟨.compare (.compare .done),Function.update (initialStore s) (.work .positive) [(zle (s a) (s b)).1]⟩ := by
  apply (signedCompare_run (s a) (s b) []).relocate_exact compareMap State.compare
    compareMap_injective (compare_code a b)
  · refine ⟨rfl,?_⟩
    intro k;cases k <;> rfl
  · refine ⟨rfl,?_⟩
    intro k;cases k <;> simp [compareMap,initialStore,store,Function.update,signedConfig,signedStacks]
  · intro k hk
    have ha:=hk .ap;have hb:=hk .an;have hc:=hk .bp;have hd:=hk .bn
    have he:=hk .leftSum;have hf:=hk .rightSum;have hg:=hk .scratch;have hh:=hk .output
    cases k with
    | reg v n => rfl
    | copyScratch | transferScratch => rfl
    | work k => cases k <;> simp_all [compareMap,initialStore,store,signedMulInitial,Function.update]

lemma compare_finish (a b : V) (s : V→ZBits) (bit : Bool) :
    Step (program a b)
      ⟨.compare (.compare .done),Function.update (initialStore s) (.work .positive) [bit]⟩
      ⟨.result bit,initialStore s⟩ := by
  have he : Function.update (initialStore s) (.work .positive) []=initialStore s := by
    funext k
    by_cases hk : k=Stack.work .positive
    · subst k; rfl
    · simp [Function.update,hk]
  cases bit <;> simp [Step,successors,program,Function.update_idem,he]

def guardCost (x y : ZBits) : ℕ := copyCost x y+signedCompareTime x y+1

/-- Alias-safe comparison returns through the Boolean halt label, without
leaving a result cell or modifying any original signed register. -/
theorem guard_run (a b : V) (s : V→ZBits) :
    Run (program a b) (guardCost (s a) (s b))
      ⟨.copy .xp .readSource,initialStore s⟩
      ⟨.result (zle (s a) (s b)).1,initialStore s⟩ :=
  ((copy_operands_run a b s).trans (compare_run a b s)).trans
    (Run.one (compare_finish a b s _))

lemma guardCost_bound (x y : ZBits) {W : ℕ} (hx : width x≤W) (hy : width y≤W) :
    guardCost x y≤32*W+33 := by
  have hc := signedCompareTime_bound x y
  have hxp : x.1.length≤W := by unfold width at hx;omega
  have hxn : x.2.length≤W := by unfold width at hx;omega
  have hyp : y.1.length≤W := by unfold width at hy;omega
  have hyn : y.2.length≤W := by unfold width at hy;omega
  unfold guardCost copyCost
  omega

lemma program_noChoice (a b : V) : NoChoice (program a b) := by
  intro q x y
  cases q with
  | copy o q => cases q <;> simp [program,copyProgram,Instr.rename]
  | compare q =>
    simp only [program]
    split
    · simp
    · exact Instr.rename_no_choice _ (signedCompare_noChoice q) _ _ x y
  | result bit => simp [program]

/-- Every halting run, on either Boolean branch, has exactly the proved
result. The caller can patch the two halt labels to finite branch targets. -/
theorem guard_halted_result (a b : V) (s : V→ZBits) {t : ℕ} {c : Config (Stack V) State} {bit : Bool}
    (hr : Run (program a b) t ⟨.copy .xp .readSource,initialStore s⟩ c)
    (hc : (program a b).code c.pc=.halt bit) :
    t=guardCost (s a) (s b) ∧ c=⟨.result (zle (s a) (s b)).1,initialStore s⟩ ∧
      (bit=true ↔ zvalue (s a)≤zvalue (s b)) := by
  have he := hr.halted_unique (noChoice_deterministic (program_noChoice a b)) (guard_run a b s) hc rfl
  refine ⟨he.1,he.2,?_⟩
  rw [he.2] at hc
  change Instr.halt (zle (s a) (s b)).1=Instr.halt bit at hc
  have hb : (zle (s a) (s b)).1=bit := Instr.halt.inj hc
  rw [← hb]
  exact zle_correct (s a) (s b)

end BalancedAssortments.NPStack.SignedAssignCompare
