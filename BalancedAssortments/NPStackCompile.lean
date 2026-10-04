import BalancedAssortments.NPStackPrefix
import BalancedAssortments.NPStackTapeInitializeSound
import BalancedAssortments.NPStackLift
import BalancedAssortments.NPStackTapeAcceptance

/-! Quantitative raw-input compilation of finite Boolean-stack bytecode to the
concrete finite one-tape model. The initialization and each tape step are real
operational transitions; no decoded arithmetic is a primitive. -/
noncomputable section
namespace BalancedAssortments.NPStack.Compile
open NPMachine NPMachine.FiniteBridge TapeMachine TapeInitialize
variable {K Q : Type*} [Fintype K] [Fintype Q] [DecidableEq K]

def machine (P : NPStack.Program K Q) : NPMachine.Machine := FiniteBridge.compile (initialized P)
def timeBound (n T : ℕ) : ℕ := initCost n+T*(2*(n+T)+3)

theorem run_complete (P : NPStack.Program K Q) (word : List Bool)
    {T : ℕ} {d : NPStack.Config K Q} (hr : NPStack.Run P T (NPStack.initial P word) d)
    (ha : NPStack.accepts P d) : NPMachine.AcceptsWithin (machine P) word (timeBound word.length T) := by
  obtain ⟨s,hs,tape,hrep,hinit⟩ := initialized_run P word
  have hlift := lift_run hr
  have hheight : ∀ k,((liftConfig (NPStack.initial P word)).stk k).length≤word.length := by
    intro k
    cases k with
    | none => simp [liftConfig,extendedStacks]
    | some k => by_cases hk : k=P.inputStack <;> simp [liftConfig,extendedStacks,NPStack.initial,Function.update_apply,hk]
  obtain ⟨u,hu,tape',hrep',hcore⟩ := run_simulates hlift tape hrep word.length hheight
  have hall := hinit.trans (embed_run P hcore)
  have hacc : (initialized P).accepting (embed (cfgAt tape' (.normal (liftConfig d).pc) 0)).state=true := by
    change accepting (liftedProgram P) (.normal (.inr d.pc))=true
    have hh := (lift_accepts P d).2 ha
    change (liftedProgram P).code (.inr d.pc)=.halt true at hh
    simp [accepting,hh]
  refine ⟨s+u,by unfold timeBound;omega,
    configCode (initialized P) (embed (cfgAt tape' (.normal (liftConfig d).pc) 0)),?_,?_⟩
  · have hrun := FiniteBridge.run_code hall
    rw [initial_code] at hrun
    exact hrun
  · exact (accepts_code _ _).2 hacc

lemma timeBound_mono {n T U : ℕ} (h : T≤U) : timeBound n T≤timeBound n U := by
  unfold timeBound
  gcongr

/-- An explicit ordinary natural-coefficient polynomial for the compiler's
quadratic initialization and stack-height-dependent simulation overhead. -/
def clockPolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  2*Polynomial.X+2+(2*Polynomial.X+1)*(2*(Polynomial.X+(2*Polynomial.X+1))+3)+
    p*(2*(Polynomial.X+p)+3)

lemma clockPolynomial_eval (p : Polynomial ℕ) (n : ℕ) :
    (clockPolynomial p).eval n=timeBound n (p.eval n) := by
  simp [clockPolynomial,timeBound,initCost]

/-- Every accepting compiled execution corresponds to an actual accepting
source execution, irrespective of the supplied target time bound. -/
theorem run_sound (P : NPStack.Program K Q) (word : List Bool) {T : ℕ}
    (ha : NPMachine.AcceptsWithin (machine P) word T) :
    ∃ t e,NPStack.Run P t (NPStack.initial P word) e ∧ NPStack.accepts P e := by
  obtain ⟨t,ht,c,hr,hacc⟩ := ha
  dsimp only [machine] at hr hacc
  rw [← initial_code] at hr
  obtain ⟨d,rfl,hsource⟩ := FiniteBridge.run_decode hr
  have hd := (accepts_code (initialized P) d).1 hacc
  obtain ⟨tape,hrep,u,e,hcore,haccept⟩ := initialized_accepting_core P word hsource hd
  obtain ⟨v,f,hstack,hf⟩ := accepting_run_sound (liftedProgram P)
    ⟨.inl .read,reversingStacks P word.reverse []⟩ tape hrep hcore haccept
  exact reverse_accepting_strip P word hstack hf

/-- An actual finite Boolean-stack recognizer with polynomially bounded
accepting executions compiles into the project's concrete one-tape NP model.
Soundness quantifies ALL source accepting executions, preventing late spurious
acceptance from being hidden by a clock predicate. -/
theorem recognition_inNP (P : NPStack.Program K Q) (p : Polynomial ℕ) (L : Set (List Bool))
    (sound : ∀ word t c,NPStack.Run P t (NPStack.initial P word) c → NPStack.accepts P c → word∈L)
    (complete : ∀ word,word∈L → ∃ t≤p.eval word.length,∃ c,
      NPStack.Run P t (NPStack.initial P word) c ∧ NPStack.accepts P c) : NPMachine.InNP L := by
  refine ⟨machine P,clockPolynomial p,?_⟩
  intro word
  rw [clockPolynomial_eval]
  constructor
  · intro hw
    obtain ⟨t,ht,c,hr,ha⟩ := complete word hw
    obtain ⟨u,hu,d,hd,haccept⟩ := run_complete P word hr ha
    exact ⟨u,hu.trans (timeBound_mono ht),d,hd,haccept⟩
  · intro ha
    obtain ⟨t,c,hr,hc⟩ := run_sound P word ha
    exact sound word t c hr hc

end BalancedAssortments.NPStack.Compile
