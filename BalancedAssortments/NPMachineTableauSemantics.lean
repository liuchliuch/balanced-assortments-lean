import BalancedAssortments.NPMachineWindow

/-! Exact finite-window tableau semantics for polynomial-clock computations. -/
noncomputable section
namespace BalancedAssortments.NPMachine

lemma PaddedRun.exists_trace {M : Machine} {T : ℕ} {c d : Config M} (h : PaddedRun M T c d) :
    ∃ f : Fin (T+1) → Config M, f 0=c ∧ f (Fin.last T)=d ∧
      ∀ i : Fin T, PaddedStep M (f i.castSucc) (f i.succ) := by
  induction h with
  | zero c => exact ⟨fun _ => c,rfl,rfl,fun i => Fin.elim0 i⟩
  | @succ t c d e hs hr ih =>
    obtain ⟨f,hf0,hfl,hsteps⟩ := ih
    let g : Fin (t+1+1) → Config M := Fin.cases c f
    refine ⟨g,rfl,?_,?_⟩
    · change f (Fin.last t)=e
      exact hfl
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change PaddedStep M c (f 0)
        rw [hf0]
        exact hs
      · change PaddedStep M (f j.castSucc) (f j.succ)
        exact hsteps j

lemma paddedRun_of_trace (M : Machine) (T : ℕ) (f : Fin (T+1) → Config M)
    (hs : ∀ i : Fin T,PaddedStep M (f i.castSucc) (f i.succ)) :
    PaddedRun M T (f 0) (f (Fin.last T)) := by
  induction T with
  | zero => exact PaddedRun.zero (f 0)
  | succ T ih =>
    have ht : ∀ i : Fin T, PaddedStep M (f i.castSucc.succ) (f i.succ.succ) := by
      intro i
      simpa only [Fin.castSucc_fin_succ] using hs i.succ
    have hr := ih (fun i => f i.succ) ht
    exact PaddedRun.succ (hs 0) hr

lemma trace_prefix (M : Machine) (T : ℕ) (f : Fin (T+1) → Config M)
    (hs : ∀ i : Fin T,PaddedStep M (f i.castSucc) (f i.succ))
    (k : ℕ) (hk : k ≤ T) :
    PaddedRun M k (f 0) (f ⟨k,by omega⟩) := by
  induction k with
  | zero => exact PaddedRun.zero (f 0)
  | succ k ih =>
    have hp := ih (by omega)
    have hstep := hs ⟨k,by omega⟩
    exact hp.trans (PaddedRun.succ hstep (PaddedRun.zero _))

def AcceptingWindowTableau (M : Machine) (word : List Bool) (T : ℕ) : Prop :=
  ∃ f : Fin (T+1) → WindowConfig M (windowWidth word T),
    f 0=windowInitial M word T ∧
    (∀ i : Fin T,WindowPaddedStep M (f i.castSucc) (f i.succ)) ∧
    WindowAccepts M (f (Fin.last T))

/-- Every bounded accepting run fits the explicitly constructed finite window.
No tape-bound or tableau-existence assumption is supplied by the caller. -/
theorem acceptsWithin_to_window (M : Machine) (word : List Bool) (T : ℕ)
    (ha : AcceptsWithin M word T) : AcceptingWindowTableau M word T := by
  obtain ⟨c,hc,haccept⟩ := (acceptsWithin_iff_padded M word T).1 ha
  obtain ⟨f,hf0,hfl,hsteps⟩ := hc.exists_trace
  have hheads : ∀ i : Fin (T+1), ∃ j : Fin (windowWidth word T),position T j=(f i).head := by
    intro i
    have hpre := trace_prefix M T f hsteps i.val (by omega)
    have hhead := hpre.head_bound
    rw [hf0] at hhead
    change |(f i).head-0| ≤ (i.val : ℤ) at hhead
    rw [sub_zero] at hhead
    obtain ⟨hlo,hhi⟩ := abs_le.mp hhead
    apply (position_range T (windowWidth word T) (f i).head).2
    have hi : i.val ≤ T := by omega
    unfold windowWidth
    push_cast
    constructor <;> omega
  let g : Fin (T+1) → WindowConfig M (windowWidth word T) :=
    fun i => projectWindow M T (windowWidth word T) (f i) (hheads i)
  refine ⟨g,?_,?_,?_⟩
  · apply WindowConfig.ext
    · change (f 0).state=M.start
      rw [hf0]
      rfl
    · apply position_injective T (windowWidth word T)
      change position T (projectWindow M T (windowWidth word T) (f 0) (hheads 0)).head =
        position T (windowInitial M word T).head
      rw [projectWindow_head,hf0]
      simp [initial,windowInitial,position]
    · funext j
      change (f 0).tape (position T j)=inputTape M word (position T j)
      rw [hf0]
      rfl
  · intro i
    exact paddedStep_projects M T _ (hheads i.castSucc) (hheads i.succ) (hsteps i)
  · change accepts M (f (Fin.last T))
    rw [hfl]
    exact haccept

/-- A finite valid tableau lifts to a genuine integer-tape accepting run. -/
theorem window_to_acceptsWithin (M : Machine) (word : List Bool) (T : ℕ)
    (h : AcceptingWindowTableau M word T) : AcceptsWithin M word T := by
  obtain ⟨f,hf0,hs,ha⟩ := h
  let g : Fin (T+1) → Config M := fun i => liftWindow M T (f i)
  have hg : ∀ i : Fin T,PaddedStep M (g i.castSucc) (g i.succ) :=
    fun i => windowPaddedStep_lifts M T (hs i)
  have hr := paddedRun_of_trace M T g hg
  have hg0 : g 0=initial M word := by
    dsimp [g]
    rw [hf0,lift_windowInitial]
  rw [hg0] at hr
  apply (acceptsWithin_iff_padded M word T).2
  exact ⟨g (Fin.last T),hr,ha⟩

/-- Exact bounded-computation/tableau correspondence for the concrete machine. -/
theorem bounded_acceptance_iff_window_tableau (M : Machine) (word : List Bool) (T : ℕ) :
    AcceptsWithin M word T ↔ AcceptingWindowTableau M word T :=
  ⟨acceptsWithin_to_window M word T,window_to_acceptsWithin M word T⟩

end BalancedAssortments.NPMachine
