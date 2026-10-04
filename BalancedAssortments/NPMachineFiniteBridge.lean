import BalancedAssortments.NPMachineModel

/-! Exact, step-count-preserving compilation of a finite symbolic one-tape
machine to the concrete numbered machine used by the NP language definition.
Input bits and blank have reserved distinct symbols; every work symbol and
control state is finite. This is a compilation component, not a stack simulation. -/
noncomputable section
namespace BalancedAssortments.NPMachine.FiniteBridge

inductive Symbol (A : Type*)
  | bit : Bool → Symbol A
  | blank : Symbol A
  | work : A → Symbol A
  deriving DecidableEq, Fintype

structure Transition (Q A : Type*) where
  source : Q
  read : Symbol A
  target : Q
  write : Symbol A
  move : Move

structure Program (Q A : Type*) where
  start : Q
  accepting : Q → Bool
  rules : List (Transition Q A)

structure Configuration (Q A : Type*) where
  state : Q
  head : ℤ
  tape : ℤ → Symbol A

variable {Q A : Type*} [Fintype Q] [Fintype A]

def stateCode (q : Q) : Fin (Fintype.card Q+1) :=
  ⟨(Fintype.equivFin Q q).val,by have := (Fintype.equivFin Q q).isLt; omega⟩

def symbolCode : Symbol A → Fin (Fintype.card A+3)
  | .bit false => ⟨0,by omega⟩
  | .bit true => ⟨1,by omega⟩
  | .blank => ⟨2,by omega⟩
  | .work a => ⟨(Fintype.equivFin A a).val+3,by have := (Fintype.equivFin A a).isLt;omega⟩

lemma stateCode_injective : Function.Injective (stateCode : Q → _) := by
  intro a b h
  apply (Fintype.equivFin Q).injective
  apply Fin.ext
  exact congrArg (fun x : Fin (Fintype.card Q+1) => x.val) h

lemma symbolCode_injective : Function.Injective (symbolCode : Symbol A → _) := by
  intro a b h
  cases a with
  | bit x => cases x <;> cases b with
    | bit y => cases y <;> simp_all [symbolCode]
    | blank => simp_all [symbolCode]
    | work z => have hh := congrArg Fin.val h; simp only [symbolCode] at hh; omega
  | blank => cases b with
    | bit y => cases y <;> simp_all [symbolCode]
    | blank => rfl
    | work z => have hh := congrArg Fin.val h; simp only [symbolCode] at hh; omega
  | work x => cases b with
    | bit y => cases y <;> have hh := congrArg Fin.val h <;> simp only [symbolCode] at hh <;> omega
    | blank => have hh := congrArg Fin.val h; simp only [symbolCode] at hh; omega
    | work y =>
      congr 1
      apply (Fintype.equivFin A).injective
      apply Fin.ext
      have hh := congrArg Fin.val h
      simp only [symbolCode] at hh
      omega

def transitionCode (r : Transition Q A) : Rule (Fintype.card Q) (Fintype.card A) :=
  ⟨stateCode r.source,symbolCode r.read,stateCode r.target,symbolCode r.write,r.move⟩

def compile (P : Program Q A) : Machine where
  stateExtra := Fintype.card Q
  symbolExtra := Fintype.card A
  start := stateCode P.start
  accepting := fun q => if h : q.val < Fintype.card Q then
    P.accepting ((Fintype.equivFin Q).symm ⟨q.val,h⟩) else false
  rules := P.rules.map transitionCode

def configCode (P : Program Q A) (c : Configuration Q A) : Config (compile P) :=
  ⟨stateCode c.state,c.head,fun k => symbolCode (c.tape k)⟩

def execute (c : Configuration Q A) (r : Transition Q A) : Configuration Q A :=
  ⟨r.target,c.head+r.move.displacement,Function.update c.tape c.head r.write⟩

def Step (P : Program Q A) (c d : Configuration Q A) : Prop :=
  ∃ r ∈ P.rules,c.state=r.source ∧ c.tape c.head=r.read ∧ d=execute c r

lemma execute_code (P : Program Q A) (c : Configuration Q A) (r : Transition Q A) :
    configCode P (execute c r)=NPMachine.execute (configCode P c) (transitionCode r) := by
  unfold configCode execute NPMachine.execute transitionCode
  congr 1
  funext k
  by_cases hk : k=c.head <;> simp [Function.update_apply,hk]

lemma configCode_injective (P : Program Q A) : Function.Injective (configCode P) := by
  intro c d h
  have hs := congrArg Config.state h
  have hh := congrArg Config.head h
  have ht := congrArg Config.tape h
  have hs' : c.state=d.state := stateCode_injective hs
  have ht' : c.tape=d.tape := by
    funext k
    exact symbolCode_injective (congrFun ht k)
  cases c; cases d
  simp_all [configCode]

 theorem step_iff (P : Program Q A) (c d : Configuration Q A) :
    NPMachine.Step (compile P) (configCode P c) (configCode P d) ↔ Step P c d := by
  constructor
  · rintro ⟨r,hr,hs,hd⟩
    change r ∈ P.rules.map transitionCode at hr
    obtain ⟨s,hsMem,hcode⟩ := List.mem_map.mp hr
    subst r
    refine ⟨s,hsMem,stateCode_injective hs.1,symbolCode_injective hs.2,?_⟩
    apply configCode_injective P
    rw [execute_code]
    exact hd
  · rintro ⟨r,hr,hs,ht,rfl⟩
    refine ⟨transitionCode r,List.mem_map.mpr ⟨r,hr,rfl⟩,?_,execute_code P c r⟩
    exact ⟨congrArg stateCode hs,congrArg symbolCode ht⟩

lemma step_decode (P : Program Q A) (c : Configuration Q A) (d : Config (compile P))
    (h : NPMachine.Step (compile P) (configCode P c) d) :
    ∃ e, d=configCode P e ∧ Step P c e := by
  obtain ⟨r,hr,hs,rfl⟩ := h
  change r ∈ P.rules.map transitionCode at hr
  obtain ⟨s,hsMem,hcode⟩ := List.mem_map.mp hr
  subst r
  refine ⟨execute c s,(execute_code P c s).symm,s,hsMem,
    stateCode_injective hs.1,symbolCode_injective hs.2,rfl⟩

inductive Run (P : Program Q A) : ℕ → Configuration Q A → Configuration Q A → Prop
  | zero (c) : Run P 0 c c
  | succ {t c d e} : Step P c d → Run P t d e → Run P (t+1) c e

lemma run_code {P : Program Q A} {t : ℕ} {c d : Configuration Q A} (h : Run P t c d) :
    NPMachine.Run (compile P) t (configCode P c) (configCode P d) := by
  induction h with
  | zero => exact NPMachine.Run.zero _
  | succ hs _ ih => exact NPMachine.Run.succ ((step_iff _ _ _).2 hs) ih

lemma run_decode {P : Program Q A} {t : ℕ} {c : Configuration Q A} {d : Config (compile P)}
    (h : NPMachine.Run (compile P) t (configCode P c) d) :
    ∃ e,d=configCode P e ∧ Run P t c e := by
  generalize he : configCode P c = c' at h
  induction h generalizing c with
  | zero c' => exact ⟨c,he.symm,Run.zero _⟩
  | @succ t c' d e hs hr ih =>
    rw [← he] at hs
    obtain ⟨d',hd,hstep⟩ := step_decode P c d hs
    obtain ⟨e',he',hrest⟩ := ih hd.symm
    exact ⟨e',he',Run.succ hstep hrest⟩

lemma run_iff (P : Program Q A) (t : ℕ) (c d : Configuration Q A) :
    NPMachine.Run (compile P) t (configCode P c) (configCode P d) ↔ Run P t c d := by
  constructor
  · intro h
    obtain ⟨e,he,hr⟩ := run_decode h
    have hed := configCode_injective P he
    simpa only [← hed] using hr
  · exact run_code

lemma accepts_code (P : Program Q A) (c : Configuration Q A) :
    NPMachine.accepts (compile P) (configCode P c) ↔ P.accepting c.state=true := by
  unfold NPMachine.accepts compile configCode stateCode
  dsimp only
  rw [dif_pos (Fintype.equivFin Q c.state).isLt]
  rw [Equiv.symm_apply_apply]

def initial (P : Program Q A) (word : List Bool) : Configuration Q A :=
  ⟨P.start,0,fun k => if 0≤k then
    match word[k.toNat]? with | some b => .bit b | none => .blank
    else .blank⟩

lemma initial_code (P : Program Q A) (word : List Bool) :
    configCode P (initial P word)=NPMachine.initial (compile P) word := by
  unfold configCode initial NPMachine.initial NPMachine.inputTape
  congr 1
  funext k
  by_cases hk : 0≤k
  · simp only [if_pos hk]
    cases hh : word[k.toNat]? with
    | none => rfl
    | some b => cases b <;> rfl
  · simp only [if_neg hk]
    rfl

def AcceptsWithin (P : Program Q A) (word : List Bool) (T : ℕ) : Prop :=
  ∃ t≤T,∃ c,Run P t (initial P word) c ∧ P.accepting c.state=true

theorem acceptsWithin_iff (P : Program Q A) (word : List Bool) (T : ℕ) :
    NPMachine.AcceptsWithin (compile P) word T ↔ AcceptsWithin P word T := by
  constructor
  · rintro ⟨t,ht,c,hr,ha⟩
    rw [← initial_code] at hr
    obtain ⟨d,rfl,hd⟩ := run_decode hr
    exact ⟨t,ht,d,hd,(accepts_code P d).1 ha⟩
  · rintro ⟨t,ht,c,hr,ha⟩
    refine ⟨t,ht,configCode P c,?_,(accepts_code P c).2 ha⟩
    rw [← initial_code]
    exact run_code hr

end BalancedAssortments.NPMachine.FiniteBridge
