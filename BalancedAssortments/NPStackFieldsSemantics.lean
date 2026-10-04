import BalancedAssortments.NPStackFieldsRun

namespace BalancedAssortments.NPStackFields
open NPStack

lemma parseAux_sound (fuel bits : List Bool) (fs : List (List Bool))
    (h : (EncodingTime.parseAux fuel bits).1=some fs) : bits=NPCNF.Encoding.encodeFields fs := by
  induction fuel generalizing bits fs with
  | nil =>
    cases bits with
    | nil => simp only [EncodingTime.parseAux,Option.some.injEq] at h; subst fs; rfl
    | cons b bs => simp [EncodingTime.parseAux] at h
  | cons f fuel ih =>
    cases bits with
    | nil => simp only [EncodingTime.parseAux,Option.some.injEq] at h; subst fs; rfl
    | cons b bs =>
      cases hp : (EncodingTime.parseField (b::bs)).1 with
      | none => simp [EncodingTime.parseAux,hp] at h
      | some p =>
        rcases p with ⟨payload,rest⟩
        cases ht : (EncodingTime.parseAux fuel rest).1 with
        | none => simp [EncodingTime.parseAux,hp,ht] at h
        | some tail =>
          simp only [EncodingTime.parseAux,hp,ht,Option.map_some,Option.some.injEq] at h
          subst fs
          have hb := NPStackField.parseField_sound (b::bs) payload rest hp
          have hr := ih rest tail ht
          rw [hr] at hb
          exact hb

/-- Framing is lossless, including noncanonical padded payloads. -/
theorem parse_sound (bits : List Bool) (fs : List (List Bool))
    (h : (EncodingTime.parse bits).1=some fs) : bits=NPCNF.Encoding.encodeFields fs :=
  parseAux_sound bits bits fs h

/-- The actual finite program refines every successful original raw parser
call, at linear real transition cost in the original serialized word. -/
theorem parsed_fields_outputs (bits : List Bool) (fs : List (List Bool))
    (h : (EncodingTime.parse bits).1=some fs) :
    OutputsIn program bits (dataFields fs) (10*bits.length+2) := by
  rw [parse_sound bits fs h]
  exact fields_outputs fs

end BalancedAssortments.NPStackFields
