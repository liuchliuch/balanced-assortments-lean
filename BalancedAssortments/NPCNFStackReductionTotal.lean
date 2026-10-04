import BalancedAssortments.NPCNFStackReductionFailure
import BalancedAssortments.NPCNFStackValidateTotal
import BalancedAssortments.NPCNFStackValidateBounds

namespace BalancedAssortments.NPCNF.StackReduction
open NPStack NPStack.Macros NPStackFields Encoding

lemma program_noChoice : NoChoice program := by
  intro q a b
  cases q with
  | parse q => exact return_not_choice _ _ _ _ _ (NPStackFields.program_noChoice q) _ _
  | validate q => exact return_not_choice _ _ _ _ _ (StackValidate.program_noChoice q) _ _
  | transform q => exact return_not_choice _ _ _ _ _ (StackTransform.program_noChoice q) _ _
  | transfer t q => exact return_not_choice _ _ _ _ _ (copy_noChoice q) _ _
  | failureClear => simp [program,code]
  | failureEmit pc => simp only [program,code];split <;> simp
  | accept => simp [program,code]

def GoodInput (bits : List Bool) : Prop := ∃ raw,(parse bits).1=some raw ∧ raw.decode.Valid

lemma reduction_of_good (bits : List Bool) (raw : Raw) (hp : (parse bits).1=some raw) (hv : raw.decode.Valid) :
    reduction bits=encode (successResult raw) := by
  have hh := (validate_correct raw).2 hv
  simp [reduction,hp,hh]

lemma reduction_of_not_good (bits : List Bool) (hn : ¬GoodInput bits) : reduction bits=failureBits := by
  cases hp : (parse bits).1 with
  | none => simp [reduction,hp]
  | some raw =>
    have hv : (validate raw).1=false := by
      cases hc : (validate raw).1 with
      | false => rfl
      | true => exact False.elim (hn ⟨raw,hp,(validate_correct raw).1 hc⟩)
    simp [reduction,hp,hv]

/-- The untimed source reduction has a real terminating primitive run on every
input. The finite timeout wrapper will supply the uniform malformed-input clock. -/
theorem unbounded_computes (bits : List Bool) :
    ∃ t c,Run program t (initial program bits) c ∧ accepts program c ∧ c.stk output=reduction bits := by
  classical
  by_cases hgood : GoodInput bits
  · obtain ⟨raw,hp,hv⟩ := hgood
    obtain ⟨s,hr,ho⟩ := valid_run raw hv
    have he := parse_input_eq_encode bits raw hp
    rw [← he] at hr
    refine ⟨successCost raw,⟨.accept,s⟩,hr,rfl,?_⟩
    rw [reduction_of_good bits raw hp hv]
    exact ho
  · have hf := reduction_of_not_good bits hgood
    cases hp : (EncodingTime.parse bits).1 with
    | none =>
      obtain ⟨t,ht,s,hr,ho⟩ := framing_failure bits hp
      exact ⟨t,⟨.accept,s⟩,hr,rfl,by simpa [hf] using ho⟩
    | some fs =>
      obtain ⟨t,d,b,hr,hd⟩ := StackValidate.prepare_total_halts fs
      cases b with
      | false =>
        obtain ⟨u,hu,s,hs,ho⟩ := validation_failure bits fs hp hr hd
        exact ⟨u,⟨.accept,s⟩,hs,rfl,by simpa [hf] using ho⟩
      | true =>
        obtain ⟨raw,hpack,hv,hfields,_,_⟩ := StackValidate.prepare_accepting_result fs hr hd
        have hraw : (parse bits).1=some raw := by simp [parse,hp,hpack]
        exact False.elim (hgood ⟨raw,hraw,hv⟩)

theorem accepting_output (bits : List Bool) {t : ℕ} {c : Config Register State}
    (hr : Run program t (initial program bits) c) (ha : accepts program c) : c.stk output=reduction bits := by
  obtain ⟨u,d,hd,haccept,hout⟩ := unbounded_computes bits
  have he := hr.halted_unique (noChoice_deterministic program_noChoice) hd ha haccept
  rw [he.2]
  exact hout

/-- Literal polynomial for every valid-source execution, in original wire
length. Malformed inputs will be cut off by actual finite unary-fuel code. -/
noncomputable def validClock : Polynomial ℕ :=
  let X := Polynomial.X
  let I := 3*X+1
  1000*(X+1)^3+110*((I+1)*(4*I+10000*(I+1)*(3*I+1)))+90*I+66+30*X+22

lemma validClock_eval (N : ℕ) : validClock.eval N=
    StackValidate.prepBudget N+StackTransform.transformBudget (3*N+1)+30*N+22 := by
  simp [validClock,StackValidate.prepBudget,StackTransform.transformBudget]
  ring

theorem valid_cost_bound (raw : Raw) : successCost raw≤validClock.eval (encode raw).length := by
  have h := success_cost_bound raw
  have hp := StackValidate.preparationCost_bound raw
  rw [dataFields_encoding_length] at hp
  rw [validClock_eval]
  omega

/-- Every well-formed valid input finishes before the advertised timeout. -/
theorem good_computes (bits : List Bool) (hg : GoodInput bits) :
    OutputsIn program bits (reduction bits) (validClock.eval bits.length) := by
  obtain ⟨raw,hp,hv⟩ := hg
  have he := parse_input_eq_encode bits raw hp
  obtain ⟨s,hr,ho⟩ := valid_run raw hv
  refine ⟨successCost raw,?_,⟨.accept,s⟩,?_,rfl,?_⟩
  · rw [he];exact valid_cost_bound raw
  · rwa [he]
  · rw [reduction_of_good bits raw hp hv];exact ho

end BalancedAssortments.NPCNF.StackReduction
