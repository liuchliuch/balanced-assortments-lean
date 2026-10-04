import BalancedAssortments.NPStackField

namespace BalancedAssortments.NPStackField
open NPStack ComplexityEncoding

lemma unary_sound (bits rest : List Bool) (n : ℕ) (h : readUnary bits=some (n,rest)) :
    bits=List.replicate n true++false::rest := by
  induction bits generalizing n with
  | nil => simp [readUnary] at h
  | cons b bs ih =>
    cases b with
    | false => simp only [readUnary,Option.some.injEq,Prod.mk.injEq] at h
               rcases h with ⟨rfl,rfl⟩; rfl
    | true =>
      cases ht : readUnary bs with
      | none => simp [readUnary,ht] at h
      | some p =>
        rcases p with ⟨m,rs⟩
        simp only [readUnary,ht,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        have hh := ih m ht
        simp [hh,List.replicate_succ]

lemma parseField_sound (bits payload rest : List Bool)
    (h : (EncodingTime.parseField bits).1=some (payload,rest)) :
    bits=FPTASCostProgram.serializeBits payload++rest := by
  rw [EncodingTime.parseField_correct] at h
  unfold decodeRawNat at h
  cases hu : readUnary bits with
  | none => simp [hu] at h
  | some p =>
    rcases p with ⟨n,remaining⟩
    simp only [hu,bind,Option.bind] at h
    split_ifs at h with hn
    · simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rw [unary_sound bits remaining n hu]
      simp only [FPTASCostProgram.serializeBits,List.length_take, min_eq_left hn,
        List.append_assoc,List.cons_append,List.take_append_drop]

/-- Every successful raw parser invocation is realized by the concrete finite
program, preserving the unconsumed input suffix exactly. -/
theorem parseField_run (bits payload rest : List Bool)
    (h : (EncodingTime.parseField bits).1=some (payload,rest)) :
    Run program (7*payload.length+3) (cfg .header bits [] [] []) (cfg .accept rest [] [] payload) := by
  rw [parseField_sound bits payload rest h]
  exact field_run payload rest

lemma initial_cfg (bits : List Bool) : initial program bits=cfg .header bits [] [] [] := by
  unfold initial cfg
  congr 1
  funext k
  cases k <;> simp [program]

/-- Operational output, not merely decoded mathematical existence. -/
theorem serialized_field_output (payload : List Bool) :
    OutputsIn program (FPTASCostProgram.serializeBits payload) payload (7*payload.length+3) := by
  refine ⟨7*payload.length+3,le_rfl,cfg .accept [] [] [] payload,?_,?_,?_⟩
  · rw [initial_cfg]
    simpa using field_run payload []
  · rfl
  · rfl

end BalancedAssortments.NPStackField
