import BalancedAssortments.NPStackGuess
import BalancedAssortments.NPStackCompile

namespace BalancedAssortments.NPStack.Guess
open NPStack
variable {K Q : Type*} [DecidableEq K]

inductive Phase | guess | choose | push (b : Bool)

def phaseState : Phase → State Q
  | .guess => .guess | .choose => .choose | .push b => .push b

/-- Every reachable configuration either still builds a literal candidate
word, or follows a genuine run of the supplied finite verifier. -/
def Reach (P : Program K Q) (certificate : K) (word : List Bool) (c : Config K (State Q)) : Prop :=
  (∃ candidate phase,c=cfg P certificate (phaseState phase) word candidate) ∨
  ∃ candidate t e,Run P t (twoInput P certificate word candidate) e ∧ c=⟨.body e.pc,e.stk⟩

lemma reach_step (P : Program K Q) (certificate : K) (word : List Bool) {c d : Config K (State Q)}
    (hc : Reach P certificate word c) (hs : Step (program P certificate) c d) : Reach P certificate word d := by
  rcases hc with ⟨candidate,phase,rfl⟩ | ⟨candidate,t,e,hr,rfl⟩
  · cases phase with
    | guess =>
      simp only [Step,successors,program,cfg,phaseState,List.mem_cons,List.mem_nil_iff,or_false] at hs
      rcases hs with rfl|rfl
      · exact Or.inr ⟨candidate,0,twoInput P certificate word candidate,.zero _,rfl⟩
      · exact Or.inl ⟨candidate,.choose,rfl⟩
    | choose =>
      simp only [Step,successors,program,cfg,phaseState,List.mem_cons,List.mem_nil_iff,or_false] at hs
      rcases hs with rfl|rfl
      · exact Or.inl ⟨candidate,.push false,rfl⟩
      · exact Or.inl ⟨candidate,.push true,rfl⟩
    | push b =>
      have he : d=cfg P certificate .guess word (b::candidate) := by
        simpa [Step,successors,program,cfg,twoInput,phaseState,Function.update_idem] using hs
      exact Or.inl ⟨b::candidate,.guess,he⟩
  · obtain ⟨e',he',hrel,_⟩ := (Run.one hs).reflect id State.body Function.injective_id (body_code P certificate)
      (c:=e) ⟨rfl,fun _ => rfl⟩
    refine Or.inr ⟨candidate,t+1,e',hr.trans he',?_⟩
    rcases d with ⟨q,s⟩
    have hp : q=.body e'.pc := hrel.1
    have hstk : s=e'.stk := funext hrel.2
    simp only [hp,hstk]

lemma reach_run (P : Program K Q) (certificate : K) (word : List Bool) {T : ℕ}
    {c d : Config K (State Q)} (hc : Reach P certificate word c) (hr : Run (program P certificate) T c d) :
    Reach P certificate word d := by
  induction hr with
  | zero => exact hc
  | succ hs hr ih => exact ih (reach_step P certificate word hc hs)

/-- Every accepting branch guesses an actual finite bit string and then runs
only the literal supplied verifier. No length cap or semantic verifier oracle
is assumed by this all-run soundness statement. -/
theorem accepting_candidate (P : Program K Q) (certificate : K) (hne : certificate≠P.inputStack)
    (word : List Bool) {T : ℕ} {d : Config K (State Q)}
    (hr : Run (program P certificate) T (initial (program P certificate) word) d)
    (ha : accepts (program P certificate) d) :
    ∃ candidate t e,Run P t (twoInput P certificate word candidate) e ∧ accepts P e := by
  rw [initial_cfg P certificate hne word] at hr
  have hinit : Reach P certificate word (cfg P certificate .guess word []) := Or.inl ⟨[],.guess,rfl⟩
  rcases reach_run P certificate word hinit hr with ⟨candidate,phase,rfl⟩ | ⟨candidate,t,e,he,rfl⟩
  · cases phase <;> simp [accepts,program,cfg,phaseState] at ha
  · exact ⟨candidate,t,e,he,accepts_reflect id State.body (body_code P certificate) ⟨rfl,fun _ => rfl⟩ ha⟩

theorem candidate_complete (P : Program K Q) (certificate : K) (hne : certificate≠P.inputStack)
    (word candidate : List Bool) {T : ℕ} {d : Config K Q}
    (hr : Run P T (twoInput P certificate word candidate) d) (ha : accepts P d) :
    Run (program P certificate) (3*candidate.length+1+T) (initial (program P certificate) word)
      ⟨.body d.pc,d.stk⟩ ∧ accepts (program P certificate) ⟨.body d.pc,d.stk⟩ := by
  constructor
  · rw [initial_cfg P certificate hne word]
    exact (guess_run P certificate word candidate).trans (body_run P certificate hr)
  · change (P.code d.pc).rename id State.body=.halt true
    rw [ha]
    rfl

/-- Operational NP membership from a polynomial-sized guessed word and an
actual polynomial-time two-input finite Boolean-stack verifier. -/
theorem recognition_inNP [Fintype K] [Fintype Q]
    (P : Program K Q) (certificate : K) (hne : certificate≠P.inputStack)
    (candidateClock verifierClock : Polynomial ℕ) (L : Set (List Bool))
    (sound : ∀ word candidate t e,Run P t (twoInput P certificate word candidate) e → accepts P e → word∈L)
    (complete : ∀ word,word∈L → ∃ candidate,candidate.length ≤ candidateClock.eval word.length ∧
      ∃ t ≤ verifierClock.eval word.length,∃ e,Run P t (twoInput P certificate word candidate) e ∧ accepts P e) :
    NPMachine.InNP L := by
  apply Compile.recognition_inNP (program P certificate) (3*candidateClock+1+verifierClock) L
  · intro word t e hr ha
    obtain ⟨candidate,u,d,hd,hh⟩ := accepting_candidate P certificate hne word hr ha
    exact sound word candidate u d hd hh
  · intro word hw
    obtain ⟨candidate,hcandidate,t,ht,e,hr,ha⟩ := complete word hw
    obtain ⟨hfull,haccept⟩ := candidate_complete P certificate hne word candidate hr ha
    refine ⟨3*candidate.length+1+t,?_,_,hfull,haccept⟩
    simp
    omega

end BalancedAssortments.NPStack.Guess
