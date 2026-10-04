import BalancedAssortments.NPStackTapeInitialize

namespace BalancedAssortments.NPStack.TapeInitialize
variable {K Q : Type*} [Fintype K] [Fintype Q] [DecidableEq K]

def liftConfig (c : Config K Q) : Config (Option K) (ReverseState ⊕ Q) :=
  ⟨.inr c.pc,extendedStacks c.stk⟩

lemma extendedStacks_update (stk : K → List Bool) (k : K) (bs : List Bool) :
    extendedStacks (Function.update stk k bs)=Function.update (extendedStacks stk) (some k) bs := by
  funext j
  cases j with
  | none => simp [extendedStacks]
  | some j => by_cases hj : j=k <;> simp [extendedStacks,Function.update_apply,hj]

lemma liftConfig_injective : Function.Injective (liftConfig : Config K Q → _) := by
  intro c d he
  have hp := congrArg Config.pc he
  have hs := congrArg Config.stk he
  have hp' : c.pc=d.pc := by simpa [liftConfig] using hp
  have hs' : c.stk=d.stk := by
    funext k
    exact congrFun hs (some k)
  cases c; cases d
  simp_all

lemma successors_lift (P : Program K Q) (c : Config K Q) :
    successors (liftedProgram P) (liftConfig c)=(successors P c).map liftConfig := by
  cases hc : P.code c.pc with
  | halt b => simp [successors,liftedProgram,liftConfig,liftInstr,hc]
  | jump q => simp [successors,liftedProgram,liftConfig,liftInstr,hc]
  | push k b q => simp [successors,liftedProgram,liftConfig,liftInstr,hc,extendedStacks,extendedStacks_update]
  | choice q r => simp [successors,liftedProgram,liftConfig,liftInstr,hc]
  | pop k qe qf qt =>
    cases hk : c.stk k with
    | nil => simp [successors,liftedProgram,liftConfig,liftInstr,hc,extendedStacks,hk]
    | cons b bs =>
      cases b <;> simp [successors,liftedProgram,liftConfig,liftInstr,hc,extendedStacks,hk,extendedStacks_update]

lemma lift_step {P : Program K Q} {c d : Config K Q} (h : Step P c d) :
    Step (liftedProgram P) (liftConfig c) (liftConfig d) := by
  unfold Step at *
  rw [successors_lift]
  exact List.mem_map.mpr ⟨d,h,rfl⟩

lemma lift_step_decode {P : Program K Q} {c : Config K Q} {d : Config (Option K) (ReverseState ⊕ Q)}
    (h : Step (liftedProgram P) (liftConfig c) d) : ∃ e,d=liftConfig e ∧ Step P c e := by
  unfold Step at h
  rw [successors_lift] at h
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
  exact ⟨e,rfl,he⟩

lemma lift_run {P : Program K Q} {t : ℕ} {c d : Config K Q} (h : Run P t c d) :
    Run (liftedProgram P) t (liftConfig c) (liftConfig d) := by
  induction h with
  | zero => exact .zero _
  | succ hs hr ih => exact .succ (lift_step hs) ih

lemma lift_run_decode {P : Program K Q} {t : ℕ} {c : Config K Q}
    {d : Config (Option K) (ReverseState ⊕ Q)}
    (h : Run (liftedProgram P) t (liftConfig c) d) :
    ∃ e,d=liftConfig e ∧ Run P t c e := by
  generalize he : liftConfig c=c' at h
  induction h generalizing c with
  | zero => exact ⟨c,he.symm,.zero _⟩
  | @succ t c' d e hs hr ih =>
    rw [← he] at hs
    obtain ⟨d',hd,hstep⟩ := lift_step_decode hs
    obtain ⟨e',he',hrest⟩ := ih hd.symm
    exact ⟨e',he',.succ hstep hrest⟩

lemma lift_accepts (P : Program K Q) (c : Config K Q) :
    accepts (liftedProgram P) (liftConfig c) ↔ accepts P c := by
  unfold accepts
  cases h : P.code c.pc <;> simp [liftedProgram,liftConfig,liftInstr,h]

end BalancedAssortments.NPStack.TapeInitialize
