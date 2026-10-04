import BalancedAssortments.NPStackTapeInitialize

noncomputable section
namespace BalancedAssortments.NPStack.TapeInitialize
open NPMachine NPMachine.FiniteBridge TapeMachine
variable {K Q : Type*} [Fintype K] [Fintype Q] [DecidableEq K]

def Scanning (q : InitControl K Q) : Prop := ∀ r,q≠.run r

inductive ScanPrefix (P : NPStack.Program K Q) :
    Configuration (InitControl K Q) (InitCell K) → Configuration (InitControl K Q) (InitCell K) → Prop
  | done (c) : ScanPrefix P c c
  | step {c d e} : Scanning c.state → FiniteBridge.Step (initialized P) c d →
      ScanPrefix P d e → ScanPrefix P c e

lemma ScanPrefix.trans {P : NPStack.Program K Q} {c d e}
    (h : ScanPrefix P c d) (g : ScanPrefix P d e) : ScanPrefix P c e := by
  induction h with
  | done => exact g
  | step hn hs hr ih => exact .step hn hs (ih g)

lemma scanning_unique (P : NPStack.Program K Q) (q : InitControl K Q)
    (a : Symbol (InitCell K)) (h : Scanning q) (x y : Action (InitControl K Q) (InitCell K))
    (hx : x∈initActions P q a) (hy : y∈initActions P q a) : x=y := by
  cases q with
  | run q => exact (h q rfl).elim
  | scan first =>
    cases a <;> cases first <;> simp [initActions] at hx hy <;> exact hx.trans hy.symm
  | back =>
    cases hb : (readCell a).1 <;> simp [initActions,hb] at hx hy <;> exact hx.trans hy.symm

lemma scanning_step_unique (P : NPStack.Program K Q) {c d e}
    (h : Scanning c.state) (hd : FiniteBridge.Step (initialized P) c d)
    (he : FiniteBridge.Step (initialized P) c e) : d=e := by
  obtain ⟨x,hx,rfl⟩ := (table_step _ _ _ _ _).1 hd
  obtain ⟨y,hy,rfl⟩ := (table_step _ _ _ _ _).1 he
  rw [scanning_unique P c.state (c.tape c.head) h x y hx hy]

lemma scanning_not_accepting (P : NPStack.Program K Q) {q : InitControl K Q} (h : Scanning q) :
    (initialized P).accepting q=false := by
  cases q with
  | run q => exact (h q rfl).elim
  | scan first => rfl
  | back => rfl

lemma ScanPrefix.factor {P : NPStack.Program K Q} {c e}
    (h : ScanPrefix P c e) {T : ℕ} {d}
    (hr : FiniteBridge.Run (initialized P) T c d)
    (ha : (initialized P).accepting d.state=true) :
    ∃ u,FiniteBridge.Run (initialized P) u e d := by
  induction h generalizing T with
  | done => exact ⟨T,hr⟩
  | @step c b e hn hs hp ih =>
    cases hr with
    | zero => rw [scanning_not_accepting P hn] at ha; cases ha
    | @succ t c b' d hs' hr =>
      have he := scanning_step_unique P hn hs hs'
      subst b'
      exact ih hr

lemma scan_prefix (P : NPStack.Program K Q) (word : List Bool) (j : ℕ) (hj : j≤word.length) :
    ScanPrefix P (cfg (rawTape word) (.scan true) 0)
      (cfg (scannedTape word j) (.scan (decide (j=0))) j) := by
  induction j with
  | zero =>
    simpa [scanned_zero] using (ScanPrefix.done (P:=P)
      (cfg (rawTape (K:=K) word) (InitControl.scan true : InitControl K Q) 0))
  | succ j ih =>
    have hlt : j<word.length := by omega
    have hs := init_action P (scannedTape word j) (.scan (decide (j=0))) (.scan false) j
      (scanCell (decide (j=0)) (some word[j])) .right
      (by rw [scanned_at word j hlt];simp [initActions])
    rw [scanned_succ word j hlt] at hs
    have hs' : FiniteBridge.Step (initialized P)
        (cfg (scannedTape word j) (.scan (decide (j=0))) j)
        (cfg (scannedTape word (j+1)) (.scan (decide (j+1=0))) (j+1)) := by
      simpa [Move.displacement] using hs
    exact (ih (by omega)).trans (.step (by intro r h;cases h) hs' (.done _))

lemma back_prefix (P : NPStack.Program K Q) (t : Tape (Option K))
    (hb : ∀ j : ℕ,(readCell (t j)).1=decide (j=0)) (j : ℕ) :
    ScanPrefix P (cfg t .back j) (cfg t (.run (.normal (.inl .read))) 0) := by
  induction j with
  | zero =>
    have hh := init_action P t .back (.run (.normal (.inl .read))) 0 (t 0) .stay
      (by simp [initActions,show (readCell (t 0)).1=true by simpa using hb 0])
    refine .step (by intro r h;cases h) ?_ (.done _)
    simpa [Move.displacement,Function.update_eq_self] using hh
  | succ j ih =>
    have hh := init_action P t .back .back (j+1) (t (j+1)) .left
      (by simp [initActions,show (readCell (t (j+1))).1=false by simpa using hb (j+1)])
    refine .step (by intro r h;cases h) ?_ ih
    simpa [Move.displacement,Function.update_eq_self] using hh

lemma scan_complete_prefix (P : NPStack.Program K Q) (word : List Bool) :
    ∃ t,Represents (reversingStacks P word.reverse []) t ∧
      ScanPrefix P (FiniteBridge.initial (initialized P) word)
        (cfg t (.run (.normal (.inl .read))) 0) := by
  by_cases hw : word=[]
  · subst word
    let t : Tape (Option K) := Function.update (rawTape []) 0 (scanCell true none)
    have hr : Represents (reversingStacks P [].reverse []) t := by
      constructor
      · intro p
        by_cases hp : p=0
        · subst p; simp [t,scanCell,readCell]
        · simp [t,rawTape,readCell,hp]
      · intro k p
        by_cases hp : p=0
        · subst p; cases k <;> simp [t,scanCell,readCell,reversingStacks]
        · cases k <;> simp [t,Function.update_of_ne hp,rawTape,readCell,reversingStacks]
    refine ⟨t,hr,.step (by intro r h;cases h) ?_ (.done _)⟩
    have hh := init_action P (rawTape []) (.scan true) (.run (.normal (.inl .read))) 0
      (scanCell true none) .stay (by simp [rawTape,initActions])
    change FiniteBridge.Step (initialized P) (cfg (rawTape []) (.scan true) 0) (cfg t (.run (.normal (.inl .read))) 0)
    simpa only [Move.displacement,add_zero] using hh
  · have hl : 0<word.length := List.length_pos_iff.mpr hw
    let n := word.length
    let t := scannedTape (K:=K) word n
    have hr := scanned_represents P word hw
    have hend : t (n:ℤ)=.blank := by simp [t,n,scannedTape,rawTape]
    have hs := scan_prefix P word n (by rfl)
    have hh := init_action P t (.scan false) .back n .blank .left
      (by rw [hend];simp [initActions])
    have htupdate : Function.update t (n:ℤ) .blank=t := by rw [←hend]; exact Function.update_eq_self _ _
    rw [htupdate] at hh
    have hb := back_prefix P t (represents_bottom _ _ hr) (n-1)
    have hh' : FiniteBridge.Step (initialized P) (cfg t (.scan (decide (n=0))) n)
        (cfg t .back (n-1:ℕ)) := by
      have hn : n≠0 := by dsimp [n];omega
      have he : (n:ℤ)+Move.left.displacement=((n-1:ℕ):ℤ) := by simp [Move.displacement]; dsimp [n];omega
      simpa [hn,he] using hh
    refine ⟨t,hr,?_⟩
    exact hs.trans (.step (by intro r h;cases h) hh' hb)

lemma embedded_step_extract (P : NPStack.Program K Q) {c d}
    (h : FiniteBridge.Step (initialized P) (embed c) d) :
    ∃ e,d=embed e ∧ FiniteBridge.Step (core (liftedProgram P)) c e := by
  obtain ⟨x,hx,rfl⟩ := (table_step _ _ _ _ _).1 h
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  refine ⟨⟨y.1,c.head+y.2.2.displacement,Function.update c.tape c.head y.2.1⟩,rfl,?_⟩
  exact (table_step _ _ _ _ _).2 ⟨y,hy,rfl⟩

lemma embedded_run_extract (P : NPStack.Program K Q) {T : ℕ} {c d}
    (h : FiniteBridge.Run (initialized P) T (embed c) d) :
    ∃ e,d=embed e ∧ FiniteBridge.Run (core (liftedProgram P)) T c e := by
  generalize hc : embed c = a at h
  induction h generalizing c with
  | zero => exact ⟨c,hc.symm,.zero _⟩
  | succ hs hr ih =>
    rw [←hc] at hs
    obtain ⟨b,rfl,hb⟩ := embedded_step_extract P hs
    obtain ⟨e,he,hrest⟩ := ih rfl
    exact ⟨e,he,.succ hb hrest⟩

/-- Any accepting execution must finish the literal-input scan, then execute
only the lifted stack core. No alternative initialization behavior can accept. -/
theorem initialized_accepting_core (P : NPStack.Program K Q) (word : List Bool)
    {T : ℕ} {d} (h : FiniteBridge.Run (initialized P) T (FiniteBridge.initial (initialized P) word) d)
    (ha : (initialized P).accepting d.state=true) :
    ∃ t,Represents (reversingStacks P word.reverse []) t ∧ ∃ u e,
      FiniteBridge.Run (core (liftedProgram P)) u (cfgAt t (.normal (.inl .read)) 0) e ∧
      (core (liftedProgram P)).accepting e.state=true := by
  obtain ⟨t,hrep,hprefix⟩ := scan_complete_prefix P word
  obtain ⟨u,hu⟩ := hprefix.factor h ha
  obtain ⟨e,he,hr⟩ := embedded_run_extract P (c := cfgAt t (.normal (.inl .read)) 0) hu
  refine ⟨t,hrep,u,e,hr,?_⟩
  subst d
  exact ha

end BalancedAssortments.NPStack.TapeInitialize
