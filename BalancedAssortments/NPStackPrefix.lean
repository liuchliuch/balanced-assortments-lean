import BalancedAssortments.NPStackLift

namespace BalancedAssortments.NPStack
variable {K Q : Type*} [DecidableEq K]

def DeterministicAt (P : Program K Q) (c : Config K Q) : Prop :=
  ∀ d e,Step P c d → Step P c e → d=e

lemma deterministic_nonChoice (P : Program K Q) (c : Config K Q)
    (h : ∀ q r,P.code c.pc≠.choice q r) : DeterministicAt P c := by
  intro d e hd he
  cases hc : P.code c.pc with
  | halt b => simp [Step,successors,hc] at hd
  | jump q => simp [Step,successors,hc] at hd he; exact hd.trans he.symm
  | push k b q => simp [Step,successors,hc] at hd he; exact hd.trans he.symm
  | pop k qe qf qt =>
    cases hs : c.stk k <;> simp [Step,successors,hc,hs] at hd he <;> exact hd.trans he.symm
  | choice q r => exact (h q r hc).elim

/-- A concrete deterministic nonaccepting prefix, not a semantic oracle. -/
inductive SafePrefix (P : Program K Q) : Config K Q → Config K Q → Prop
  | done (c) : SafePrefix P c c
  | step {c d e} : ¬accepts P c → DeterministicAt P c → Step P c d →
      SafePrefix P d e → SafePrefix P c e

lemma SafePrefix.strip {P : Program K Q} {c e : Config K Q} (h : SafePrefix P c e)
    {T : ℕ} {d : Config K Q} (hr : Run P T c d) (ha : accepts P d) :
    ∃ t,Run P t e d := by
  induction h generalizing T with
  | done => exact ⟨T,hr⟩
  | @step c c' e hn hdet hs hp ih =>
    cases hr with
    | zero => exact (hn ha).elim
    | @succ t _ d' _ hs' hr' =>
      have he := hdet c' d' hs hs'
      subst d'
      exact ih hr'

end BalancedAssortments.NPStack

namespace BalancedAssortments.NPStack.TapeInitialize
variable {K Q : Type*} [Fintype K] [Fintype Q] [DecidableEq K]

lemma reverse_safe_prefix (P : Program K Q) (xs ys : List Bool) :
    SafePrefix (liftedProgram P) ⟨.inl .read,reversingStacks P xs ys⟩
      ⟨.inr P.start,reversingStacks P [] (xs.reverse++ys)⟩ := by
  induction xs generalizing ys with
  | nil =>
    refine SafePrefix.step ?_ ?_ ?_ (.done _)
    · simp [accepts,liftedProgram]
    · apply deterministic_nonChoice; intro q r; simp [liftedProgram]
    · simp [Step,successors,liftedProgram,reversingStacks]
  | cons b xs ih =>
    have hpop : Step (liftedProgram P) ⟨.inl .read,reversingStacks P (b::xs) ys⟩
        ⟨.inl (if b then .pushTrue else .pushFalse),reversingStacks P xs ys⟩ := by
      have hu : Function.update (reversingStacks P (b::xs) ys) none xs = reversingStacks P xs ys := by
        funext k; cases k <;> simp [reversingStacks]
      cases b <;> simp [Step,successors,liftedProgram,reversingStacks,←hu]
    have hpush : Step (liftedProgram P)
        ⟨.inl (if b then .pushTrue else .pushFalse),reversingStacks P xs ys⟩
        ⟨.inl .read,reversingStacks P xs (b::ys)⟩ := by
      have hu : Function.update (reversingStacks P xs ys) (some P.inputStack) (b::ys) =
          reversingStacks P xs (b::ys) := by
        funext k; cases k with
        | none => simp [reversingStacks]
        | some k => by_cases hk : k=P.inputStack <;> simp [reversingStacks,Function.update_apply,hk]
      cases b <;> simp [Step,successors,liftedProgram,reversingStacks,←hu]
    have ht := ih (b::ys)
    have hp := SafePrefix.step (P := liftedProgram P)
      (c := ⟨.inl (if b then .pushTrue else .pushFalse),reversingStacks P xs ys⟩)
      (by cases b <;> simp [accepts,liftedProgram])
      (by apply deterministic_nonChoice; intro q r; cases b <;> simp [liftedProgram]) hpush ht
    have hh := SafePrefix.step (by simp [accepts,liftedProgram])
      (by apply deterministic_nonChoice; intro q r; simp [liftedProgram]) hpop hp
    simpa [List.reverse_cons,List.append_assoc] using hh

lemma reverse_accepting_strip (P : Program K Q) (word : List Bool)
    {T : ℕ} {d : Config (Option K) (ReverseState ⊕ Q)}
    (hr : Run (liftedProgram P) T ⟨.inl .read,reversingStacks P word.reverse []⟩ d)
    (ha : accepts (liftedProgram P) d) :
    ∃ t e,Run P t (initial P word) e ∧ accepts P e := by
  obtain ⟨t,ht⟩ := (reverse_safe_prefix P word.reverse []).strip hr ha
  have he : reversingStacks P [] (word.reverse.reverse++[]) = extendedStacks (initial P word).stk := by
    funext k
    cases k with
    | none => rfl
    | some k => by_cases hk : k=P.inputStack <;> simp [reversingStacks,extendedStacks,initial,Function.update_apply,hk]
  rw [he] at ht
  change Run (liftedProgram P) t (liftConfig (initial P word)) d at ht
  obtain ⟨e,rfl,hsrc⟩ := lift_run_decode ht
  exact ⟨t,e,hsrc,(lift_accepts P e).1 ha⟩

end BalancedAssortments.NPStack.TapeInitialize
