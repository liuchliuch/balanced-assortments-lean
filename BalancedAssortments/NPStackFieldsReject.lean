import BalancedAssortments.NPStackFieldsParsing

namespace BalancedAssortments.NPStackFields
open NPStack

lemma field_reject_code (q : NPStackField.State) (h : NPStackField.program.code q=.halt false) :
    program.code (.field q)=.halt false := by
  cases q <;> simp_all [program,NPStackField.program]

lemma reject_field (bits acc : List Bool) (h : (EncodingTime.parseField bits).1=none) :
    ∃ t≤7*bits.length+3,∃ c,Run program t (cfg (.field .header) bits [] [] [] acc) c ∧ program.code c.pc=.halt false := by
  obtain ⟨t,ht,c,hr,hc⟩ := NPStackField.parseField_reject bits h
  rw [NPStackField.initial_cfg] at hr
  obtain ⟨d,hd,hrel,_⟩ := hr.relocate Sum.inl State.field Sum.inl_injective field_code
    (field_relocated .header bits [] [] [] acc)
  refine ⟨t,ht,d,hd,?_⟩
  rw [hrel.1]
  exact field_reject_code c.pc hc

/-- Malformed entire input is rejected; a valid prefix cannot hide a malformed
suffix. The accumulator contains already parsed records and is never trusted. -/
theorem parse_reject (bits acc : List Bool) (h : (EncodingTime.parse bits).1=none) :
    ∃ t≤10*bits.length+5,∃ c,Run program t (cfg .probe bits [] [] [] acc) c ∧ program.code c.pc=.halt false := by
  induction hn : bits.length using Nat.strong_induction_on generalizing bits acc with
  | h n ih =>
    cases bits with
    | nil => simp [parse_nil] at h
    | cons b bs =>
      cases hp : (EncodingTime.parseField (b::bs)).1 with
      | none =>
        obtain ⟨t,ht,c,hr,hc⟩ := reject_field (b::bs) acc hp
        refine ⟨2+t,by omega,c,(probe_cons b bs acc).trans hr,hc⟩
      | some p =>
        rcases p with ⟨payload,rest⟩
        have he := parse_after_field (b::bs) payload rest (by simp) hp
        have hrnone : (EncodingTime.parse rest).1=none := by
          rw [h] at he
          cases ht : (EncodingTime.parse rest).1 with
          | none => rfl
          | some fs => simp only [ht,Option.map_some] at he; cases he
        have hl := ComplexityEncoding.decodeRawNat_lengths (by rw [← EncodingTime.parseField_correct];exact hp)
        have hbits := NPStackField.parseField_sound (b::bs) payload rest hp
        have hlen : (b::bs).length=2*payload.length+1+rest.length := by
          rw [hbits]
          simp [FPTASCostProgram.serializeBits]
          omega
        simp only [List.length_cons] at hn hl
        obtain ⟨t,ht,c,hr,hc⟩ := ih rest.length (by omega) rest
          ((tagBits payload++[false]).reverse++acc) hrnone rfl
        have hpRun := parse_one payload rest acc
        rw [← hbits] at hpRun
        refine ⟨(10*payload.length+8)+t,?_,c,hpRun.trans hr,hc⟩
        omega

end BalancedAssortments.NPStackFields
