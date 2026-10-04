import BalancedAssortments.NPStackFieldsSemantics

namespace BalancedAssortments.NPStackFields
open NPStack

lemma parseAux_fuel_irrelevant (bits f g : List Bool) (hf : bits.length≤f.length) (hg : bits.length≤g.length) :
    (EncodingTime.parseAux f bits).1=(EncodingTime.parseAux g bits).1 := by
  induction hn : bits.length using Nat.strong_induction_on generalizing bits f g with
  | h n ih =>
    cases bits with
    | nil => cases f <;> cases g <;> rfl
    | cons b bs =>
      cases f with
      | nil => simp at hf
      | cons a f =>
        cases g with
        | nil => simp at hg
        | cons c g =>
          cases hp : (EncodingTime.parseField (b::bs)).1 with
          | none => simp [EncodingTime.parseAux,hp]
          | some p =>
            rcases p with ⟨payload,rest⟩
            have hl := ComplexityEncoding.decodeRawNat_lengths (by rw [← EncodingTime.parseField_correct];exact hp)
            simp only [List.length_cons] at hl hf hg hn
            have hi := ih rest.length (by omega) rest f g
              (by omega)
              (by omega) rfl
            simp only [EncodingTime.parseAux,hp,hi]

lemma parse_after_field (bits payload rest : List Bool) (hne : bits≠[])
    (hp : (EncodingTime.parseField bits).1=some (payload,rest)) :
    (EncodingTime.parse bits).1=(EncodingTime.parse rest).1.map (payload::·) := by
  cases bits with
  | nil => contradiction
  | cons b bs =>
    have hl := ComplexityEncoding.decodeRawNat_lengths (by rw [← EncodingTime.parseField_correct];exact hp)
    have he := parseAux_fuel_irrelevant rest bs rest (by simp only [List.length_cons] at hl;omega) le_rfl
    simp only [EncodingTime.parse,EncodingTime.parseAux,hp,he]

lemma parse_nil : (EncodingTime.parse []).1=some [] := rfl

end BalancedAssortments.NPStackFields
