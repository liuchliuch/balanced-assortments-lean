import BalancedAssortments.NPStackTapeBackward

noncomputable section
namespace BalancedAssortments.NPStack.TapeMachine
open NPMachine NPMachine.FiniteBridge
variable {K Q : Type*} [Fintype K] [Fintype Q] [DecidableEq K]

lemma boundary_next (P : NPStack.Program K Q) (c : NPStack.Config K Q)
    (tape : Tape K) (hrep : Represents c.stk tape)
    (d : Configuration (Control K Q) (Cell K))
    (hs : FiniteBridge.Step (core P) (cfgAt tape (.normal c.pc) 0) d) :
    ∃ e,NPStack.Step P c e ∧ ∃ tape',Represents e.stk tape' ∧
      UntilBoundary P d (cfgAt tape' (.normal e.pc) 0) := by
  rcases c with ⟨q,stk⟩
  dsimp only at hrep
  obtain ⟨x,hx,hd⟩ := (table_step _ _ _ _ _).1 hs
  change x ∈ actions P (.normal q) (tape 0) at hx
  cases hq : P.code q with
  | halt b => simp [actions,hq] at hx
  | jump q' =>
    simp only [actions,hq,List.mem_singleton] at hx
    subst x
    have he : d=cfgAt tape (.normal q') 0 := by simpa [cfgAt,Move.displacement] using hd
    rw [he]
    exact ⟨⟨q',stk⟩,by simp [NPStack.Step,successors,hq],tape,hrep,.done _⟩
  | push k b q' =>
    simp only [actions,hq,List.mem_singleton] at hx
    subst x
    have he : d=cfgAt tape (.seekPush k b q') 0 := by simpa [cfgAt,Move.displacement] using hd
    rw [he]
    obtain ⟨tape',hr,hu⟩ := push_until P tape stk hrep q' k b
    exact ⟨⟨q',Function.update stk k (b::stk k)⟩,by simp [NPStack.Step,successors,hq],tape',hr,hu⟩
  | pop k qe qf qt =>
    simp only [actions,hq,List.mem_singleton] at hx
    subst x
    have he : d=cfgAt tape (.seekPop k qe qf qt) 0 := by simpa [cfgAt,Move.displacement] using hd
    rw [he]
    cases hk : stk k with
    | nil => exact ⟨⟨qe,stk⟩,by simp [NPStack.Step,successors,hq,hk],tape,hrep,
        pop_empty_until P tape stk hrep qe qf qt k hk⟩
    | cons b bs =>
      obtain ⟨tape',hr,hu⟩ := pop_cons_until P tape stk hrep qe qf qt k b bs hk
      exact ⟨⟨if b then qt else qf,Function.update stk k bs⟩,
        by simp [NPStack.Step,successors,hq,hk],tape',hr,hu⟩
  | choice q' q'' =>
    simp [actions,hq] at hx
    rcases hx with rfl | rfl
    · have he : d=cfgAt tape (.normal q') 0 := by simpa [cfgAt,Move.displacement] using hd
      rw [he]
      exact ⟨⟨q',stk⟩,by simp [NPStack.Step,successors,hq],tape,hrep,.done _⟩
    · have he : d=cfgAt tape (.normal q'') 0 := by simpa [cfgAt,Move.displacement] using hd
      rw [he]
      exact ⟨⟨q'',stk⟩,by simp [NPStack.Step,successors,hq],tape,hrep,.done _⟩

/-- Every reachable microstate is on a deterministic finite path to a source
configuration that is itself reachable. Committing the source step at the
beginning of its simulation is safe because intermediate phases cannot accept. -/
def ReachInvariant (P : NPStack.Program K Q) (start : NPStack.Config K Q)
    (c : Configuration (Control K Q) (Cell K)) : Prop :=
  ∃ n e,NPStack.Run P n start e ∧ ∃ tape,Represents e.stk tape ∧
    UntilBoundary P c (cfgAt tape (.normal e.pc) 0)

lemma invariant_step (P : NPStack.Program K Q) (start : NPStack.Config K Q)
    {c d : Configuration (Control K Q) (Cell K)}
    (h : ReachInvariant P start c) (hs : FiniteBridge.Step (core P) c d) :
    ReachInvariant P start d := by
  obtain ⟨n,e,hr,tape,hrep,hu⟩ := h
  by_cases he : c=cfgAt tape (.normal e.pc) 0
  · subst c
    obtain ⟨e',hs',tape',hrep',hu'⟩ := boundary_next P e tape hrep d hs
    exact ⟨n+1,e',hr.trans (NPStack.Run.one hs'),tape',hrep',hu'⟩
  · exact ⟨n,e,hr,tape,hrep,hu.next he hs⟩

lemma invariant_run (P : NPStack.Program K Q) (start : NPStack.Config K Q)
    {T : ℕ} {c d : Configuration (Control K Q) (Cell K)}
    (h : ReachInvariant P start c) (hr : FiniteBridge.Run (core P) T c d) :
    ReachInvariant P start d := by
  induction hr with
  | zero => exact h
  | succ hs hr ih => exact ih (invariant_step P start h hs)

/-- Soundness for every concrete simulator execution, with no externally
supplied tableau, macro-step decomposition, or source clock premise. -/
theorem accepting_run_sound (P : NPStack.Program K Q) (start : NPStack.Config K Q)
    (tape : Tape K) (hrep : Represents start.stk tape)
    {T : ℕ} {d : Configuration (Control K Q) (Cell K)}
    (hr : FiniteBridge.Run (core P) T (cfgAt tape (.normal start.pc) 0) d)
    (ha : (core P).accepting d.state=true) :
    ∃ t e,NPStack.Run P t start e ∧ NPStack.accepts P e := by
  have hinit : ReachInvariant P start (cfgAt tape (.normal start.pc) 0) :=
    ⟨0,start,.zero _,tape,hrep,.done _⟩
  obtain ⟨t,e,he,tape',hrep',hu⟩ := invariant_run P start hinit hr
  have hn : ∃ q,d.state=.normal q := by
    cases hd : d.state <;> simp [core,tableProgram,accepting,hd] at ha
    exact ⟨_,rfl⟩
  obtain ⟨q,hq⟩ := hn
  have hd := hu.normal_eq hq
  subst d
  refine ⟨t,e,he,?_⟩
  change accepting P (.normal e.pc)=true at ha
  unfold NPStack.accepts
  cases hc : P.code e.pc <;> simp [accepting,hc] at ha
  simp_all

end BalancedAssortments.NPStack.TapeMachine
