import BalancedAssortments.NPCNFStackReductionSuccess
import BalancedAssortments.NPCNFParsingBounds

namespace BalancedAssortments.NPCNF.StackReduction
open NPStack NPStack.Macros Encoding ComplexityTimeBinary

lemma reversed_valid (raw : Raw) (hv : raw.decode.Valid) : (reversedInput raw).decode.Valid := by
  constructor
  · simpa [reversedInput,Raw.decode,List.map_reverse] using hv.1
  · intro c hc l hl
    have hh := hv.2 c hc l hl
    simpa [reversedInput,Raw.decode,List.map_reverse] using hh

lemma fresh_for_reversed (raw : Raw) : StackTransform.FreshFor (StackValidate.freshBits raw.catalog) (reversedInput raw) := by
  intro x hx
  have hm : x∈raw.catalog := by simpa [reversedInput] using hx
  have hh := label_le_max (List.mem_map.mpr ⟨x,hm,rfl⟩ : value x∈raw.catalog.map value)
  rw [StackValidate.freshBits_value]
  omega

lemma success_encoded_correct (raw : Raw) (hv : raw.decode.Valid) :
    ThreeCNFLanguage (encode (successResult raw)) ↔ CNFLanguage (encode raw) := by
  unfold successResult
  rw [StackTransform.encoded_result_correct _ _ (reversed_valid raw hv) (fresh_for_reversed raw),
    CNFLanguage_encode,CNFLanguage_encode]
  exact ⟨fun h=>⟨hv,h.2⟩,fun h=>⟨reversed_valid raw hv,h.2⟩⟩

/-- Specification of the total bytecode reduction; the operational proofs use
real parser/validator runs and never invoke this function as an instruction. -/
def reduction (bits : List Bool) : List Bool :=
  match (parse bits).1 with
  | none => failureBits
  | some raw => if (validate raw).1 then encode (successResult raw) else failureBits

lemma source_iff_of_parse (bits : List Bool) (raw : Raw) (h : (parse bits).1=some raw) :
    CNFLanguage bits ↔ raw.decode.Valid ∧ raw.decode.Sat := by simp [CNFLanguage,h]

/-- Unconditional language equivalence of the total output specification,
including every malformed framing/skeleton and invalid sparse catalogue. -/
theorem reduction_correct (bits : List Bool) : ThreeCNFLanguage (reduction bits) ↔ CNFLanguage bits := by
  cases hp : (parse bits).1 with
  | none => simp [reduction,hp,CNFLanguage,failure_not_threeCNF]
  | some raw =>
    cases hv : (validate raw).1 with
    | false =>
      have hn : ¬raw.decode.Valid := by
        intro h
        have hh := (validate_correct raw).2 h
        simp [hv] at hh
      simp [reduction,hp,hv,source_iff_of_parse bits raw hp,hn,failure_not_threeCNF]
    | true =>
      have hvalid := (validate_correct raw).1 hv
      simp only [reduction,hp,hv,ite_true]
      rw [success_encoded_correct raw hvalid,CNFLanguage_encode,source_iff_of_parse bits raw hp]

lemma parse_input_eq_encode (bits : List Bool) (raw : Raw) (h : (parse bits).1=some raw) : bits=encode raw := by
  unfold parse at h
  cases hf : (EncodingTime.parse bits).1 with
  | none => simp [hf] at h
  | some fs =>
    have hp : (pack fs).1=some raw := by simpa [hf] using h
    have he := pack_sound fs raw hp
    rw [NPStackFields.parse_sound bits fs hf,← he]
    rfl

end BalancedAssortments.NPCNF.StackReduction
