import BalancedAssortments.NPStackTapeRepresentation

noncomputable section
namespace BalancedAssortments.NPStack.TapeMachine
open NPMachine NPMachine.FiniteBridge
variable {K Q : Type*} [Fintype K] [Fintype Q] [DecidableEq K]

lemma push_simulates (P : NPStack.Program K Q) (tape : Tape K) (stk : K → List Bool)
    (h : Represents stk tape) (q q' : Q) (k : K) (b : Bool) (hq : P.code q=.push k b q') :
    ∃ tape',Represents (Function.update stk k (b::stk k)) tape' ∧
      FiniteBridge.Run (core P) (2*(stk k).length+3)
        (cfgAt tape (.normal q) 0) (cfgAt tape' (.normal q') 0) := by
  let tape' := Function.update tape (stk k).length (writeTrack (tape (stk k).length) k (some b))
  have hrep := push_represents stk tape h k b
  have hstart : FiniteBridge.Step (core P) (cfgAt tape (.normal q) 0)
      (cfgAt tape (.seekPush k b q') 0) := by
    have hh := unchanged_step P tape (.normal q) (.seekPush k b q') 0 .stay (by simp [actions,hq])
    simpa [Move.displacement] using hh
  have hscan := push_scan P tape stk h k b q'
  have hend : (readCell (tape (stk k).length)).2 k=none := by
    rw [represents_at stk tape h k (stk k).length]
    simp
  have hwrite : FiniteBridge.Step (core P) (cfgAt tape (.seekPush k b q') (stk k).length)
      (cfgAt tape' (.back q') (stk k).length) := by
    have hh := action_step P tape (.seekPush k b q') (.back q') (stk k).length
      (writeTrack (tape (stk k).length) k (some b)) .stay (by simp [actions,hend])
    simpa [Move.displacement,tape'] using hh
  have hback := back_run P tape' q' (represents_bottom _ tape' hrep) (stk k).length
  refine ⟨tape',hrep,?_⟩
  have hr := (FiniteBridge.Run.one hstart).trans (hscan.trans ((FiniteBridge.Run.one hwrite).trans hback))
  convert hr using 1 <;> omega

lemma pop_scan (P : NPStack.Program K Q) (tape : Tape K) (stk : K → List Bool)
    (h : Represents stk tape) (k : K) (qe qf qt : Q) :
    FiniteBridge.Run (core P) (stk k).length (cfgAt tape (.seekPop k qe qf qt) 0)
      (cfgAt tape (.seekPop k qe qf qt) (stk k).length) := by
  apply scan_run
  intro i hi
  have hi' : i < (stk k).reverse.length := by simpa using hi
  have hz := List.getElem?_eq_getElem hi'
  simp [actions,represents_at stk tape h k i,hz]

lemma pop_empty_simulates (P : NPStack.Program K Q) (tape : Tape K) (stk : K → List Bool)
    (h : Represents stk tape) (q qe qf qt : Q) (k : K)
    (hq : P.code q=.pop k qe qf qt) (hk : stk k=[]) :
    FiniteBridge.Run (core P) 2 (cfgAt tape (.normal q) 0) (cfgAt tape (.normal qe) 0) := by
  have hstart : FiniteBridge.Step (core P) (cfgAt tape (.normal q) 0)
      (cfgAt tape (.seekPop k qe qf qt) 0) := by
    have hh := unchanged_step P tape (.normal q) (.seekPop k qe qf qt) 0 .stay (by simp [actions,hq])
    simpa [Move.displacement] using hh
  have hempty : (readCell (tape 0)).2 k=none := by simpa [hk] using represents_at stk tape h k 0
  have hbottom : (readCell (tape 0)).1=true := by simpa using represents_bottom stk tape h 0
  have hend : FiniteBridge.Step (core P) (cfgAt tape (.seekPop k qe qf qt) 0)
      (cfgAt tape (.normal qe) 0) := by
    have hh := unchanged_step P tape (.seekPop k qe qf qt) (.normal qe) 0 .stay
      (by simp [actions,hempty,hbottom])
    simpa [Move.displacement] using hh
  exact FiniteBridge.Run.succ hstart (FiniteBridge.Run.one hend)

lemma pop_cons_simulates (P : NPStack.Program K Q) (tape : Tape K) (stk : K → List Bool)
    (h : Represents stk tape) (q qe qf qt : Q) (k : K) (b : Bool) (bs : List Bool)
    (hq : P.code q=.pop k qe qf qt) (hk : stk k=b::bs) :
    ∃ tape',Represents (Function.update stk k bs) tape' ∧
      FiniteBridge.Run (core P) (2*(stk k).length+3)
        (cfgAt tape (.normal q) 0) (cfgAt tape' (.normal (if b then qt else qf)) 0) := by
  let tape' := Function.update tape bs.length (writeTrack (tape bs.length) k none)
  have hrep := pop_represents stk tape h k b bs hk
  have hstart : FiniteBridge.Step (core P) (cfgAt tape (.normal q) 0)
      (cfgAt tape (.seekPop k qe qf qt) 0) := by
    have hh := unchanged_step P tape (.normal q) (.seekPop k qe qf qt) 0 .stay (by simp [actions,hq])
    simpa [Move.displacement] using hh
  have hscan := pop_scan P tape stk h k qe qf qt
  have hend : (readCell (tape (stk k).length)).2 k=none := by
    rw [represents_at stk tape h k (stk k).length]; simp
  have hbottom : (readCell (tape (stk k).length)).1=false := by
    simpa [hk] using represents_bottom stk tape h (stk k).length
  have hleft : FiniteBridge.Step (core P) (cfgAt tape (.seekPop k qe qf qt) (stk k).length)
      (cfgAt tape (.popAt k qf qt) bs.length) := by
    have hh := unchanged_step P tape (.seekPop k qe qf qt) (.popAt k qf qt) (stk k).length .left
      (by simp [actions,hend,hbottom])
    simpa [Move.displacement,hk] using hh
  have htop : (readCell (tape bs.length)).2 k=some b := by
    rw [represents_at stk tape h k bs.length,hk]
    simpa only [List.reverse_cons,List.length_reverse] using (List.getElem?_concat_length (l := bs.reverse) (a := b))
  have hwrite : FiniteBridge.Step (core P) (cfgAt tape (.popAt k qf qt) bs.length)
      (cfgAt tape' (.back (if b then qt else qf)) bs.length) := by
    have hh := action_step P tape (.popAt k qf qt) (.back (if b then qt else qf)) bs.length
      (writeTrack (tape bs.length) k none) .stay (by simp [actions,htop])
    simpa [Move.displacement,tape'] using hh
  have hback := back_run P tape' (if b then qt else qf) (represents_bottom _ tape' hrep) bs.length
  refine ⟨tape',hrep,?_⟩
  have hr := (FiniteBridge.Run.one hstart).trans (hscan.trans ((FiniteBridge.Run.one hleft).trans
    ((FiniteBridge.Run.one hwrite).trans hback)))
  convert hr using 1 <;> simp [hk] <;> omega

/-- Every actual source transition has an explicitly counted one-tape path.
The tape alphabet and every control phase are finite. -/
theorem step_simulates (P : NPStack.Program K Q) (c d : NPStack.Config K Q)
    (tape : Tape K) (hrep : Represents c.stk tape) (H : ℕ)
    (hH : ∀ k,(c.stk k).length≤H) (hs : NPStack.Step P c d) :
    ∃ t≤2*H+3,∃ tape',Represents d.stk tape' ∧
      FiniteBridge.Run (core P) t (cfgAt tape (.normal c.pc) 0) (cfgAt tape' (.normal d.pc) 0) := by
  rcases c with ⟨q,stk⟩
  dsimp only at hrep hH
  cases hq : P.code q with
  | halt b => simp [NPStack.Step,successors,hq] at hs
  | jump q' =>
    simp only [NPStack.Step,successors,hq,List.mem_singleton] at hs
    subst d
    have hh := unchanged_step P tape (.normal q) (.normal q') 0 .stay (by simp [actions,hq])
    refine ⟨1,by omega,tape,hrep,FiniteBridge.Run.one ?_⟩
    simpa [Move.displacement] using hh
  | push k b q' =>
    simp only [NPStack.Step,successors,hq,List.mem_singleton] at hs
    subst d
    obtain ⟨tape',hr,hs⟩ := push_simulates P tape stk hrep q q' k b hq
    exact ⟨2*(stk k).length+3,by have := hH k;omega,tape',hr,hs⟩
  | pop k qe qf qt =>
    cases hk : stk k with
    | nil =>
      simp only [NPStack.Step,successors,hq,hk,List.mem_singleton] at hs
      subst d
      exact ⟨2,by omega,tape,hrep,pop_empty_simulates P tape stk hrep q qe qf qt k hq hk⟩
    | cons b bs =>
      simp only [NPStack.Step,successors,hq,hk,List.mem_singleton] at hs
      subst d
      obtain ⟨tape',hr,hs⟩ := pop_cons_simulates P tape stk hrep q qe qf qt k b bs hq hk
      exact ⟨2*(stk k).length+3,by have := hH k;omega,tape',hr,hs⟩
  | choice q' q'' =>
    simp [NPStack.Step,successors,hq] at hs
    rcases hs with rfl | rfl
    · have hh := unchanged_step P tape (.normal q) (.normal q') 0 .stay (by simp [actions,hq])
      refine ⟨1,by omega,tape,hrep,FiniteBridge.Run.one ?_⟩
      simpa [Move.displacement] using hh
    · have hh := unchanged_step P tape (.normal q) (.normal q'') 0 .stay (by simp [actions,hq])
      refine ⟨1,by omega,tape,hrep,FiniteBridge.Run.one ?_⟩
      simpa [Move.displacement] using hh

/-- A T-step stack run is simulated in at most T*(2*(H+T)+3)
actual one-cell one-tape transitions, starting from represented stacks of
height at most H. No arbitrary cost oracle occurs in this bound. -/
theorem run_simulates {P : NPStack.Program K Q} {T : ℕ} {c d : NPStack.Config K Q}
    (hr : NPStack.Run P T c d) (tape : Tape K) (hrep : Represents c.stk tape)
    (H : ℕ) (hH : ∀ k,(c.stk k).length≤H) :
    ∃ t≤T*(2*(H+T)+3),∃ tape',Represents d.stk tape' ∧
      FiniteBridge.Run (core P) t (cfgAt tape (.normal c.pc) 0) (cfgAt tape' (.normal d.pc) 0) := by
  induction hr generalizing tape H with
  | zero c => exact ⟨0,by simp,tape,hrep,FiniteBridge.Run.zero _⟩
  | @succ T c d e hs hr ih =>
    obtain ⟨s,hsb,tape',hrep',hpath⟩ := step_simulates P c d tape hrep H hH hs
    have hH' : ∀ k,(d.stk k).length≤H+1 := by
      intro k
      have hh := hs.stack_length k
      have hk := hH k
      omega
    obtain ⟨t,htb,tape'',hrep'',hrest⟩ := ih tape' hrep' (H+1) hH'
    refine ⟨s+t,?_,tape'',hrep'',hpath.trans hrest⟩
    nlinarith

/-- The same quantitative theorem for the exact finite numbered NPMachine
used by the language-theoretic source definition. -/
theorem run_simulates_machine {P : NPStack.Program K Q} {T : ℕ} {c d : NPStack.Config K Q}
    (hr : NPStack.Run P T c d) (tape : Tape K) (hrep : Represents c.stk tape)
    (H : ℕ) (hH : ∀ k,(c.stk k).length≤H) :
    ∃ t≤T*(2*(H+T)+3),∃ tape',Represents d.stk tape' ∧
      NPMachine.Run (machine P) t (configCode (core P) (cfgAt tape (.normal c.pc) 0))
        (configCode (core P) (cfgAt tape' (.normal d.pc) 0)) := by
  obtain ⟨t,ht,tape',hrep',hpath⟩ := run_simulates hr tape hrep H hH
  exact ⟨t,ht,tape',hrep',FiniteBridge.run_code hpath⟩

end BalancedAssortments.NPStack.TapeMachine
