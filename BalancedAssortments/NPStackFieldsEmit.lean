import BalancedAssortments.NPStackFields

namespace BalancedAssortments.NPStackFields
open NPStack

lemma emit_cons (b : Bool) (i bs acc : List Bool) :
    Run program 3 (cfg .emit i [] [] (b::bs) acc) (cfg .emit i [] [] bs (b::true::acc)) := by
  cases b
  · apply Run.succ (d := cfg .tagFalse i [] [] bs acc)
    · simp [Step,successors,program,cfg,output]; funext k; cases k with
      | inl j => cases j <;> simp
      | inr u => simp
    · apply Run.succ (d := cfg .bitFalse i [] [] bs (true::acc))
      · simp [Step,successors,program,cfg,accumulator]; funext k; cases k with
        | inl j => cases j <;> simp
        | inr u => cases u; simp
      · apply Run.one
        simp [Step,successors,program,cfg,accumulator]; funext k; cases k with
        | inl j => cases j <;> simp
        | inr u => cases u; simp
  · apply Run.succ (d := cfg .tagTrue i [] [] bs acc)
    · simp [Step,successors,program,cfg,output]; funext k; cases k with
      | inl j => cases j <;> simp
      | inr u => simp
    · apply Run.succ (d := cfg .bitTrue i [] [] bs (true::acc))
      · simp [Step,successors,program,cfg,accumulator]; funext k; cases k with
        | inl j => cases j <;> simp
        | inr u => cases u; simp
      · apply Run.one
        simp [Step,successors,program,cfg,accumulator]; funext k; cases k with
        | inl j => cases j <;> simp
        | inr u => cases u; simp

lemma emit_nil (i acc : List Bool) :
    Run program 2 (cfg .emit i [] [] [] acc) (cfg .probe i [] [] [] (false::acc)) := by
  apply Run.succ (d := cfg .delimiter i [] [] [] acc)
  · simp [Step,successors,program,cfg,output]
  · apply Run.one
    simp [Step,successors,program,cfg,accumulator]; funext k; cases k with
    | inl j => cases j <;> simp
    | inr u => cases u; simp

lemma emit_payload (payload i acc : List Bool) :
    Run program (3*payload.length+2) (cfg .emit i [] [] payload acc)
      (cfg .probe i [] [] [] ((tagBits payload++[false]).reverse++acc)) := by
  induction payload generalizing acc with
  | nil => simpa [tagBits] using emit_nil i acc
  | cons b bs ih =>
    have h := (emit_cons b i bs acc).trans (ih (b::true::acc))
    simpa [tagBits,List.reverse_append,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma field_return (i payload acc : List Bool) :
    Run program 1 (cfg (.field .accept) i [] [] payload acc) (cfg .emit i [] [] payload acc) := by
  apply Run.one; simp [Step,successors,program,cfg]

lemma parse_one (payload suffix acc : List Bool) :
    Run program (10*payload.length+8)
      (cfg .probe (FPTASCostProgram.serializeBits payload++suffix) [] [] [] acc)
      (cfg .probe suffix [] [] [] ((tagBits payload++[false]).reverse++acc)) := by
  have hne : FPTASCostProgram.serializeBits payload++suffix≠[] := by
    intro h
    have hh := congrArg List.length h
    simp [FPTASCostProgram.serializeBits] at hh
  have hp : Run program 2
      (cfg .probe (FPTASCostProgram.serializeBits payload++suffix) [] [] [] acc)
      (cfg (.field .header) (FPTASCostProgram.serializeBits payload++suffix) [] [] [] acc) := by
    cases h : FPTASCostProgram.serializeBits payload++suffix with
    | nil => exact False.elim (hne h)
    | cons b bs => exact probe_cons b bs acc
  have hf := field_run (NPStackField.field_run payload suffix) acc
  have he := emit_payload payload suffix acc
  have h := ((hp.trans hf).trans (field_return suffix payload acc)).trans he
  convert h using 1 <;> omega

end BalancedAssortments.NPStackFields
