import BalancedAssortments.NPStackFieldSemantics

namespace BalancedAssortments.NPStackField
open NPStack ComplexityEncoding

lemma header_empty (count rev out : List Bool) :
    Run program 1 (cfg .header [] count rev out) (cfg .reject [] count rev out) := by
  apply Run.one
  simp [Step,successors,program,cfg]

lemma header_unterminated (n : ℕ) (count rev out : List Bool) :
    Run program (2*n+1) (cfg .header (List.replicate n true) count rev out)
      (cfg .reject [] (List.replicate n true++count) rev out) := by
  induction n generalizing count with
  | zero => simpa using header_empty count rev out
  | succ n ih =>
    have hh := header_true (List.replicate n true) count rev out
    have ht := ih (true::count)
    have he : List.replicate n true ++ true::count = List.replicate (n+1) true ++ count := by
      rw [List.replicate_succ']; simp only [List.append_assoc,List.singleton_append]
    rw [he] at ht
    have h := hh.trans ht
    simpa [List.replicate_succ,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma unary_none (bits : List Bool) (h : readUnary bits=none) : bits=List.replicate bits.length true := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · simp [readUnary] at h
    · have ht : readUnary bs=none := by simpa [readUnary] using h
      simpa [List.replicate_succ] using congrArg (true::·) (ih ht)

lemma consume_missing (count rev out : List Bool) :
    Run program 2 (cfg .consume [] (true::count) rev out) (cfg .reject [] count rev out) := by
  apply Run.succ (d := cfg .readBit [] count rev out)
  · simp [Step,successors,program,cfg]; funext k; cases k <;> simp
  · apply Run.one; simp [Step,successors,program,cfg]

lemma consume_short (input rev out : List Bool) (n : ℕ) (h : input.length<n) :
    Run program (3*input.length+2)
      (cfg .consume input (List.replicate n true) rev out)
      (cfg .reject [] (List.replicate (n-input.length-1) true) (input.reverse++rev) out) := by
  induction input generalizing n rev with
  | nil =>
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    simpa [List.replicate_succ] using consume_missing (List.replicate m true) rev out
  | cons b bs ih =>
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    have hh := consume_bit b bs (List.replicate m true) rev out
    have ht := ih (b::rev) m (by simpa using h)
    have hz : m-bs.length-1=(m+1)-(b::bs).length-1 := by simp
    have run := hh.trans ht
    simpa [List.replicate_succ,List.reverse_cons,List.append_assoc,Nat.mul_add,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run

lemma header_count (n : ℕ) (input count rev out : List Bool) :
    Run program (2*n+1) (cfg .header (List.replicate n true++false::input) count rev out)
      (cfg .consume input (List.replicate n true++count) rev out) := by
  induction n generalizing count with
  | zero => simpa using header_false input count rev out
  | succ n ih =>
    have hh := header_true (List.replicate n true++false::input) count rev out
    have ht := ih (true::count)
    have he : List.replicate n true ++ true::count = List.replicate (n+1) true ++ count := by
      rw [List.replicate_succ']; simp only [List.append_assoc,List.singleton_append]
    rw [he] at ht
    have h := hh.trans ht
    simpa [List.replicate_succ,List.cons_append,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Malformed frames reach a rejecting halt in linear actual bytecode time. -/
theorem parseField_reject (bits : List Bool) (h : (EncodingTime.parseField bits).1=none) :
    ∃ t≤7*bits.length+3,∃ c,Run program t (initial program bits) c ∧ program.code c.pc=.halt false := by
  rw [EncodingTime.parseField_correct] at h
  cases hu : readUnary bits with
  | none =>
    have hb := unary_none bits hu
    refine ⟨2*bits.length+1,by omega,cfg .reject [] (List.replicate bits.length true) [] [],?_,rfl⟩
    rw [initial_cfg]
    conv_lhs => rw [hb]
    simpa using header_unterminated bits.length [] [] []
  | some p =>
    rcases p with ⟨n,remaining⟩
    have hn : remaining.length<n := by
      unfold decodeRawNat at h
      simp only [hu,bind,Option.bind] at h
      split_ifs at h with hn <;> simp_all <;> omega
    have hh := header_count n remaining [] [] []
    have hc := consume_short remaining [] [] n hn
    simp only [List.append_nil] at hh hc
    have hr := hh.trans hc
    have hb := unary_sound bits remaining n hu
    have hl : bits.length=n+1+remaining.length := by simp [hb]; omega
    refine ⟨(2*n+1)+(3*remaining.length+2),by omega,
      cfg .reject [] (List.replicate (n-remaining.length-1) true) remaining.reverse [],?_,rfl⟩
    rw [initial_cfg,hb]
    exact hr

end BalancedAssortments.NPStackField
