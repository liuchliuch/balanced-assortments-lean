import BalancedAssortments.NPStackFieldsEmit

namespace BalancedAssortments.NPStackFields
open NPStack

lemma reverse_cons (b : Bool) (acc out : List Bool) :
    Run program 2 (cfg .reverse [] [] [] out (b::acc)) (cfg .reverse [] [] [] (b::out) acc) := by
  cases b
  · apply Run.succ (d := cfg .reverseFalse [] [] [] out acc)
    · simp [Step,successors,program,cfg,accumulator]; funext k; cases k with
      | inl j => cases j <;> simp
      | inr u => cases u; simp
    · apply Run.one
      simp [Step,successors,program,cfg,output]; funext k; cases k with
      | inl j => cases j <;> simp
      | inr u => simp
  · apply Run.succ (d := cfg .reverseTrue [] [] [] out acc)
    · simp [Step,successors,program,cfg,accumulator]; funext k; cases k with
      | inl j => cases j <;> simp
      | inr u => cases u; simp
    · apply Run.one
      simp [Step,successors,program,cfg,output]; funext k; cases k with
      | inl j => cases j <;> simp
      | inr u => simp

lemma reverse_run (acc out : List Bool) :
    Run program (2*acc.length+1) (cfg .reverse [] [] [] out acc)
      (cfg .accept [] [] [] (acc.reverse++out) []) := by
  induction acc generalizing out with
  | nil => apply Run.one; simp [Step,successors,program,cfg,accumulator]
  | cons b bs ih =>
    have h := (reverse_cons b bs out).trans (ih (b::out))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma finish_run (acc : List Bool) :
    Run program (2*acc.length+2) (cfg .probe [] [] [] [] acc) (cfg .accept [] [] [] acc.reverse []) := by
  have hs : Step program (cfg .probe [] [] [] [] acc) (cfg .reverse [] [] [] [] acc) := by
    simp [Step,successors,program,cfg,input]
  have h := Run.succ hs (reverse_run acc [])
  simpa [Nat.add_assoc] using h

lemma tagBits_length (bits : List Bool) : (tagBits bits).length=2*bits.length := by
  induction bits <;> simp_all [tagBits] <;> omega

lemma dataFields_length (fs : List (List Bool)) :
    (dataFields fs).length=2*(fs.map List.length).sum+fs.length := by
  induction fs with
  | nil => rfl
  | cons x xs ih => simp [dataFields,tagBits_length] at *; omega

lemma fields_run (fs : List (List Bool)) (acc : List Bool) :
    Run program (14*(fs.map List.length).sum+10*fs.length+2*acc.length+2)
      (cfg .probe (NPCNF.Encoding.encodeFields fs) [] [] [] acc)
      (cfg .accept [] [] [] (acc.reverse++dataFields fs) []) := by
  induction fs generalizing acc with
  | nil => simpa [NPCNF.Encoding.encodeFields,dataFields] using finish_run acc
  | cons x xs ih =>
    have hp := parse_one x (NPCNF.Encoding.encodeFields xs) acc
    have ht := ih ((tagBits x++[false]).reverse++acc)
    have h := hp.trans ht
    convert h using 1
    · simp only [List.map_cons,List.sum_cons,List.length_cons,List.length_append,
        List.length_reverse,tagBits_length,List.length_nil]
      omega
    · simp [dataFields,List.reverse_append,List.append_assoc]

lemma initial_cfg (bits : List Bool) : initial program bits=cfg .probe bits [] [] [] [] := by
  unfold initial cfg
  congr 1
  funext k
  cases k with
  | inl j => cases j <;> simp [program,input]
  | inr u => simp [program,input]

lemma encoding_length (fs : List (List Bool)) :
    (NPCNF.Encoding.encodeFields fs).length=2*(fs.map List.length).sum+fs.length := by
  induction fs with
  | nil => rfl
  | cons x xs ih =>
    simp only [NPCNF.Encoding.encodeFields,List.flatMap_cons,List.length_append,
      NPCNF.Encoding.encodePayload_length,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

/-- Actual finite-stack realization of the raw field-list parser on every
well-framed input, with a linear bound in original serialized input length. -/
theorem fields_outputs (fs : List (List Bool)) :
    OutputsIn program (NPCNF.Encoding.encodeFields fs) (dataFields fs)
      (10*(NPCNF.Encoding.encodeFields fs).length+2) := by
  refine ⟨14*(fs.map List.length).sum+10*fs.length+2,?_,cfg .accept [] [] [] (dataFields fs) [],?_,rfl,rfl⟩
  · rw [encoding_length]
    omega
  · rw [initial_cfg]
    simpa using fields_run fs []

end BalancedAssortments.NPStackFields
