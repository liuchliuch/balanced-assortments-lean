import BalancedAssortments.NPStackTimeout

namespace BalancedAssortments.NPStack.Timeout
open NPStack
variable {K Q : Type*} [DecidableEq K]

lemma nonhalting_step_exists (P : Program K Q) (c : Config K Q) (hn : ∀ b,P.code c.pc≠.halt b) :
    ∃ d,Step P c d := by
  cases hi : P.code c.pc with
  | halt b => exact False.elim (hn b hi)
  | jump q => exact ⟨⟨q,c.stk⟩,by simp [Step,successors,hi]⟩
  | push k b q => exact ⟨⟨q,Function.update c.stk k (b::c.stk k)⟩,by simp [Step,successors,hi]⟩
  | pop k qe qf qt =>
    cases hs : c.stk k with
    | nil => exact ⟨⟨qe,c.stk⟩,by simp [Step,successors,hi,hs]⟩
    | cons b bs => exact ⟨⟨if b then qt else qf,Function.update c.stk k bs⟩,by simp [Step,successors,hi,hs]⟩
  | choice q r => exact ⟨⟨q,c.stk⟩,by simp [Step,successors,hi]⟩

/-- Every prepared input has an actual halting execution within twice the
physical fuel length plus one. A true exit always comes from a genuine source
accepting run with identical source-stack contents. -/
theorem bounded_halt (P : Program K Q) (c : Config K Q) (fuel : List Bool) :
    ∃ t≤2*fuel.length+1,∃ e,∃ b,
      Run (program P) t (start c fuel) e ∧ (program P).code e.pc=.halt b ∧
      (b=true → ∃ u≤fuel.length,∃ d,Run P u c d ∧ accepts P d ∧
        ∀ k,e.stk (.inl k)=d.stk k) := by
  induction fuel generalizing c with
  | nil =>
    by_cases hh : ∃ b,P.code c.pc=.halt b
    · obtain ⟨b,hb⟩ := hh
      refine ⟨0,by omega,start c [],b,.zero _,?_,?_⟩
      · simp [start,cfg,program,hb]
      · intro htrue
        refine ⟨0,by simp,c,.zero _,?_,fun _ => rfl⟩
        change P.code c.pc=.halt true
        rw [hb,htrue]
    · have hn : ∀ b,P.code c.pc≠.halt b := fun b h => hh ⟨b,h⟩
      refine ⟨1,by simp,cfg .expired c [],false,.one (tick_empty P c hn),rfl,?_⟩
      intro h;cases h
  | cons bit fuel ih =>
    by_cases hh : ∃ b,P.code c.pc=.halt b
    · obtain ⟨b,hb⟩ := hh
      refine ⟨0,by omega,start c (bit::fuel),b,.zero _,?_,?_⟩
      · simp [start,cfg,program,hb]
      · intro htrue
        refine ⟨0,by simp,c,.zero _,?_,fun _ => rfl⟩
        change P.code c.pc=.halt true
        rw [hb,htrue]
    · have hn : ∀ b,P.code c.pc≠.halt b := fun b h => hh ⟨b,h⟩
      obtain ⟨d,hs⟩ := nonhalting_step_exists P c hn
      obtain ⟨t,ht,e,b,hr,hcode,hsound⟩ := ih d
      refine ⟨2+t,by simp only [List.length_cons];omega,e,b,(source_step hs bit fuel).trans hr,hcode,?_⟩
      intro hb
      obtain ⟨u,hu,last,hpath,ha,hout⟩ := hsound hb
      exact ⟨u+1,by simp only [List.length_cons];omega,last,.succ hs hpath,ha,hout⟩

/-- No deterministic run can evade the timeout or produce spurious true
acceptance. This statement concerns every real halting execution. -/
theorem halted_bound_sound {P : Program K Q} (hn : NoChoice P) (c : Config K Q) (fuel : List Bool)
    {t : ℕ} {e : Config (Stack K) (State Q)} {b : Bool}
    (hr : Run (program P) t (start c fuel) e) (hb : (program P).code e.pc=.halt b) :
    t≤2*fuel.length+1 ∧
      (b=true → ∃ u≤fuel.length,∃ d,Run P u c d ∧ accepts P d ∧
        ∀ k,e.stk (.inl k)=d.stk k) := by
  obtain ⟨s,hs,d,v,hknown,hd,hsource⟩ := bounded_halt P c fuel
  have he := hr.halted_unique (noChoice_deterministic (program_noChoice hn)) hknown hb hd
  refine ⟨he.1 ▸ hs,?_⟩
  intro ht
  have hv : v=true := by
    rw [he.2] at hb
    rw [hb] at hd
    have h := Instr.halt.inj hd
    exact h.symm.trans ht
  rw [he.2]
  exact hsource hv

/-- A valid source computation fitting in the fuel is never truncated. -/
theorem accepts_complete {P : Program K Q} {u : ℕ} {c d : Config K Q}
    (hr : Run P u c d) (ha : accepts P d) (fuel : List Bool) (hu : u≤fuel.length) :
    Run (program P) (2*u) (start c fuel) (start d (fuel.drop u)) ∧
      accepts (program P) (start d (fuel.drop u)) :=
  ⟨run_complete hr fuel hu,accepts_start _ ha⟩

end BalancedAssortments.NPStack.Timeout
