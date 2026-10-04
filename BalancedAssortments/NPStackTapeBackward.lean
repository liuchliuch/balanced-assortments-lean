import BalancedAssortments.NPStackTapeSimulation

noncomputable section
namespace BalancedAssortments.NPStack.TapeMachine
open NPMachine NPMachine.FiniteBridge
variable {K Q : Type*} [Fintype K] [Fintype Q] [DecidableEq K]

def NonNormal (q : Control K Q) : Prop := ∀ pc,q≠.normal pc

lemma nonNormal_actions_unique (P : NPStack.Program K Q) (q : Control K Q)
    (a : Symbol (Cell K)) (hn : NonNormal q) (x y : Action (Control K Q) (Cell K))
    (hx : x ∈ actions P q a) (hy : y ∈ actions P q a) : x=y := by
  cases q with
  | normal q => exact (hn q rfl).elim
  | seekPush k b q =>
    cases he : (readCell a).2 k <;> simp [actions,he] at hx hy <;> exact hx.trans hy.symm
  | seekPop k qe qf qt =>
    cases he : (readCell a).2 k with
    | none => cases hb : (readCell a).1 <;> simp [actions,he,hb] at hx hy <;> exact hx.trans hy.symm
    | some b => simp [actions,he] at hx hy; exact hx.trans hy.symm
  | popAt k qf qt =>
    cases he : (readCell a).2 k with
    | none => simp [actions,he] at hx
    | some b => simp [actions,he] at hx hy; exact hx.trans hy.symm
  | back q => cases hb : (readCell a).1 <;> simp [actions,hb] at hx hy <;> exact hx.trans hy.symm

lemma nonNormal_step_unique (P : NPStack.Program K Q)
    (c d e : Configuration (Control K Q) (Cell K)) (hn : NonNormal c.state)
    (hd : FiniteBridge.Step (core P) c d) (he : FiniteBridge.Step (core P) c e) : d=e := by
  obtain ⟨x,hx,rfl⟩ := (table_step _ _ _ _ _).1 hd
  obtain ⟨y,hy,rfl⟩ := (table_step _ _ _ _ _).1 he
  rw [nonNormal_actions_unique P c.state (c.tape c.head) hn x y hx hy]

/-- A finite execution segment whose strict intermediate configurations are
not source-instruction boundaries. -/
inductive UntilBoundary (P : NPStack.Program K Q) :
    Configuration (Control K Q) (Cell K) → Configuration (Control K Q) (Cell K) → Prop
  | done (c) : UntilBoundary P c c
  | step {c d e} : NonNormal c.state → FiniteBridge.Step (core P) c d →
      UntilBoundary P d e → UntilBoundary P c e

lemma UntilBoundary.next {P : NPStack.Program K Q} {c d e : Configuration (Control K Q) (Cell K)}
    (h : UntilBoundary P c e) (hne : c≠e) (hs : FiniteBridge.Step (core P) c d) :
    UntilBoundary P d e := by
  cases h with
  | done => exact (hne rfl).elim
  | @step c d' e hn hs' hr =>
    have he := nonNormal_step_unique P c d d' hn hs hs'
    simpa only [he] using hr

lemma UntilBoundary.normal_eq {P : NPStack.Program K Q} {c d : Configuration (Control K Q) (Cell K)}
    (h : UntilBoundary P c d) {q : Q} (hn : c.state=.normal q) : c=d := by
  cases h with
  | done => rfl
  | step hnon => exact (hnon q hn).elim

lemma back_until (P : NPStack.Program K Q) (tape : Tape K) (q : Q)
    (bottom : ∀ j : ℕ,(readCell (tape j)).1=decide (j=0)) (j : ℕ) :
    UntilBoundary P (cfgAt tape (.back q) j) (cfgAt tape (.normal q) 0) := by
  induction j with
  | zero =>
    have h0 : (readCell (tape 0)).1=true := by simpa using bottom 0
    have hh := unchanged_step P tape (.back q) (.normal q) 0 .stay (by simp [actions,h0])
    refine .step (by intro pc h;cases h) ?_ (.done _)
    simpa [Move.displacement] using hh
  | succ j ih =>
    have hb : (readCell (tape (j+1))).1=false := by simpa using bottom (j+1)
    have hh := unchanged_step P tape (.back q) (.back q) (j+1) .left (by simp [actions,hb])
    refine .step (by intro pc h;cases h) ?_ ih
    simpa [Move.displacement] using hh

lemma scan_until (P : NPStack.Program K Q) (tape : Tape K) (q : Control K Q)
    (hn : NonNormal q) (j count : ℕ) (endCfg : Configuration (Control K Q) (Cell K))
    (ha : ∀ (i : ℕ), j ≤ i → i < j+count → (q,tape i,Move.right) ∈ actions P q (tape i))
    (hend : UntilBoundary P (cfgAt tape q (j+count)) endCfg) :
    UntilBoundary P (cfgAt tape q j) endCfg := by
  induction count generalizing j with
  | zero => simpa using hend
  | succ count ih =>
    have hh := unchanged_step P tape q q j .right (ha j le_rfl (by omega))
    have hs : FiniteBridge.Step (core P) (cfgAt tape q j) (cfgAt tape q (j+1)) := by
      simpa [Move.displacement] using hh
    apply UntilBoundary.step hn hs
    apply ih (j+1)
    · intro i hi hi'; exact ha i (by omega) (by omega)
    · convert hend using 1 <;> congr 1 <;> omega

lemma push_until (P : NPStack.Program K Q) (tape : Tape K) (stk : K → List Bool)
    (h : Represents stk tape) (q' : Q) (k : K) (b : Bool) :
    ∃ tape',Represents (Function.update stk k (b::stk k)) tape' ∧
      UntilBoundary P (cfgAt tape (.seekPush k b q') 0) (cfgAt tape' (.normal q') 0) := by
  let tape' := Function.update tape (stk k).length (writeTrack (tape (stk k).length) k (some b))
  have hrep := push_represents stk tape h k b
  have hend : (readCell (tape (stk k).length)).2 k=none := by
    rw [represents_at stk tape h k (stk k).length]
    simp
  have hwrite : FiniteBridge.Step (core P) (cfgAt tape (.seekPush k b q') (stk k).length)
      (cfgAt tape' (.back q') (stk k).length) := by
    have hh := action_step P tape (.seekPush k b q') (.back q') (stk k).length
      (writeTrack (tape (stk k).length) k (some b)) .stay (by simp [actions,hend])
    simpa [Move.displacement,tape'] using hh
  have hback := back_until P tape' q' (represents_bottom _ tape' hrep) (stk k).length
  refine ⟨tape',hrep,?_⟩
  apply scan_until P tape (.seekPush k b q') (by intro pc hh;cases hh) 0 (stk k).length
  · intro i hi hi'
    have hil : i < (stk k).reverse.length := by simpa using hi'
    simp [actions,represents_at stk tape h k i,List.getElem?_eq_getElem hil]
  · simpa using (UntilBoundary.step (by intro pc hh;cases hh) hwrite hback)

lemma pop_cons_until (P : NPStack.Program K Q) (tape : Tape K) (stk : K → List Bool)
    (h : Represents stk tape) (qe qf qt : Q) (k : K) (b : Bool) (bs : List Bool)
    (hk : stk k=b::bs) :
    ∃ tape',Represents (Function.update stk k bs) tape' ∧
      UntilBoundary P (cfgAt tape (.seekPop k qe qf qt) 0) (cfgAt tape' (.normal (if b then qt else qf)) 0) := by
  let tape' := Function.update tape bs.length (writeTrack (tape bs.length) k none)
  have hrep := pop_represents stk tape h k b bs hk
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
  have hback := back_until P tape' (if b then qt else qf) (represents_bottom _ tape' hrep) bs.length
  refine ⟨tape',hrep,?_⟩
  apply scan_until P tape (.seekPop k qe qf qt) (by intro pc hh;cases hh) 0 (stk k).length
  · intro i hi hi'
    have hil : i < (stk k).reverse.length := by simpa using hi'
    simp [actions,represents_at stk tape h k i,List.getElem?_eq_getElem hil]
  · simpa using (UntilBoundary.step (by intro pc hh;cases hh) hleft (UntilBoundary.step (by intro pc hh;cases hh) hwrite hback))

lemma pop_empty_until (P : NPStack.Program K Q) (tape : Tape K) (stk : K → List Bool)
    (h : Represents stk tape) (qe qf qt : Q) (k : K) (hk : stk k=[]) :
    UntilBoundary P (cfgAt tape (.seekPop k qe qf qt) 0) (cfgAt tape (.normal qe) 0) := by
  have hempty : (readCell (tape 0)).2 k=none := by simpa [hk] using represents_at stk tape h k 0
  have hbottom : (readCell (tape 0)).1=true := by simpa using represents_bottom stk tape h 0
  have hh := unchanged_step P tape (.seekPop k qe qf qt) (.normal qe) 0 .stay
    (by simp [actions,hempty,hbottom])
  refine .step (by intro pc hh;cases hh) ?_ (.done _)
  simpa [Move.displacement] using hh

end BalancedAssortments.NPStack.TapeMachine
