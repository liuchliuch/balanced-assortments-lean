import BalancedAssortments.NPSATStackPrepareFailure

namespace BalancedAssortments.NPSATStackPrepare
open NPStack NPCNF.Encoding NPStackFields

def GoodInput (bits : List Bool) : Prop :=
  ∃raw,(parse bits).1=some raw ∧ raw.decode.Valid ∧ NPCNF.ThreeCNF raw.decode.formula

lemma parse_input_eq_encode (bits : List Bool) (raw : Raw) (hp : (parse bits).1=some raw) : bits=encode raw := by
  unfold parse at hp
  cases hf : (EncodingTime.parse bits).1 with
  | none => simp [hf] at hp
  | some fs =>
    have hpack : (pack fs).1=some raw := by simpa [hf] using hp
    have he := pack_sound fs raw hpack
    rw [NPStackFields.parse_sound bits fs hf,← he]
    rfl

/-- Every malformed framing, invalid sparse catalogue, bad formula skeleton,
or clause longer than three has a real rejecting execution. -/
theorem bad_input_reject (bits : List Bool) (hn : ¬GoodInput bits) :
    ∃t s,Run program t (initial program bits) ⟨.reject,s⟩ := by
  cases hp : (EncodingTime.parse bits).1 with
  | none => exact framing_failure bits hp
  | some fs =>
    obtain ⟨t,c,b,hr,hc⟩ := NPCNF.StackValidate.prepare_total_halts fs
    cases b with
    | false => exact validation_failure bits fs hp hr hc
    | true =>
      obtain ⟨raw,hpack,hv,hfields,_,_⟩ := NPCNF.StackValidate.prepare_accepting_result fs hr hc
      have hraw : (parse bits).1=some raw := by simp [parse,hp,hpack]
      have hthree : ¬NPCNF.ThreeCNF raw.decode.formula := fun h=>hn ⟨raw,hraw,hv,h⟩
      rw [parse_input_eq_encode bits raw hraw]
      exact three_failure raw hv hthree

/-- Complete backward characterization of all accepting runs of the concrete
binary parser/validator/three-clause preprocessor. -/
theorem accepting_result (bits : List Bool) {t : ℕ} {c : Config Register State}
    (hr : Run program t (initial program bits) c) (ha : accepts program c) :
    ∃raw,(parse bits).1=some raw ∧ raw.decode.Valid ∧ NPCNF.ThreeCNF raw.decode.formula ∧
      c=⟨.accept,finalStore raw⟩ ∧ t=successCost raw := by
  classical
  by_cases hg : GoodInput bits
  · obtain ⟨raw,hp,hv,ht⟩ := hg
    have known := valid_run raw hv ht
    rw [← parse_input_eq_encode bits raw hp] at known
    have hh := known.halted_unique (noChoice_deterministic noChoice) hr rfl ha
    exact ⟨raw,hp,hv,ht,hh.2.symm,hh.1.symm⟩
  · obtain ⟨u,s,hrej⟩ := bad_input_reject bits hg
    exact False.elim (rejecting_run_excludes_acceptance (noChoice_deterministic noChoice) hrej rfl hr ha)

lemma final_original (raw : Raw) : finalStore raw original=dataFields (formulaFields raw.formula) := rfl
lemma final_catalog (raw : Raw) : finalStore raw catalog=dataFields raw.catalog.reverse := rfl
lemma final_fresh (raw : Raw) : finalStore raw (validatorMap NPCNF.StackValidate.fresh)=NPCNF.StackValidate.freshBits raw.catalog := rfl

end BalancedAssortments.NPSATStackPrepare
