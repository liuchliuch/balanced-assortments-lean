import BalancedAssortments.NPPolynomialPrograms

/-! Exact output-track preservation for polynomial Boolean-stack transducers.
The output remains encoded bottom-to-top on its designated finite tape track.
This module does not claim a cleanup into a standalone plain-output tape. -/
noncomputable section
namespace BalancedAssortments.NPStack.Compile
open NPMachine NPMachine.FiniteBridge TapeMachine TapeInitialize
variable {K Q : Type*} [Fintype K] [Fintype Q] [DecidableEq K]

/-- A proof-side observation of one finite-alphabet symbol. The inverse is a
fixed finite table, not a runtime primitive or an input-dependent oracle. -/
def decodedSymbol {A : Type*} [Fintype A] (z : Fin (Fintype.card A+3)) : Symbol A :=
  letI : Nonempty (Symbol A) := ⟨.blank⟩
  Function.invFun symbolCode z

lemma decodedSymbol_code {A : Type*} [Fintype A] (a : Symbol A) : decodedSymbol (symbolCode a)=a := by
  letI : Nonempty (Symbol A) := ⟨.blank⟩
  exact Function.leftInverse_invFun symbolCode_injective a

/-- The designated output track of the actual numbered one-tape configuration.
Index zero is the stack bottom, so its cells encode the reversed output list. -/
def outputTrack (P : NPStack.Program K Q) (c : NPMachine.Config (machine P)) (j : ℕ) : Option Bool :=
  (readCell (decodedSymbol (A := InitCell K) (c.tape (j:ℤ)))).2 (some P.outputStack)

lemma outputTrack_configCode (P : NPStack.Program K Q) (tape : Tape (Option K))
    (q : InitControl K Q) (head : ℤ) (j : ℕ) :
    outputTrack P (configCode (initialized P) (cfg tape q head)) j=
      (readCell (tape (j:ℤ))).2 (some P.outputStack) := by
  simp only [outputTrack,configCode,cfg,decodedSymbol_code]

/-- Every actual accepting output computation has a counted concrete one-tape
execution from the original unencoded input bits, preserving the whole output
track exactly. Initialization and every simulated primitive are charged. -/
theorem run_output_complete (P : NPStack.Program K Q) (word : List Bool)
    {T : ℕ} {d : NPStack.Config K Q} (hr : NPStack.Run P T (NPStack.initial P word) d)
    (ha : NPStack.accepts P d) :
    ∃t ≤ timeBound word.length T,∃c : NPMachine.Config (machine P),
      NPMachine.Run (machine P) t (NPMachine.initial (machine P) word) c ∧
      NPMachine.accepts (machine P) c ∧ c.head=0 ∧
      ∀j,outputTrack P c j=(d.stk P.outputStack).reverse[j]? := by
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
    configCode (initialized P) (embed (cfgAt tape' (.normal (liftConfig d).pc) 0)),?_,?_,rfl,?_⟩
  · have hrun := FiniteBridge.run_code hall
    rw [initial_code] at hrun
    exact hrun
  · exact (accepts_code _ _).2 hacc
  · intro j
    have hcell := represents_at _ tape' hrep' (some P.outputStack) j
    simpa only [outputTrack,configCode,embed,cfgAt,decodedSymbol_code,liftConfig,extendedStacks] using hcell

end BalancedAssortments.NPStack.Compile

namespace BalancedAssortments.NPStack

/-- A named end-to-end polynomial-time output simulation, not merely an
acceptance simulation. The actual numbered one-tape machine starts on the raw
input and finishes with exactly `f bits` on its designated encoded track. -/
theorem PolynomialProgram.one_tape_output {f : List Bool → List Bool} (p : PolynomialProgram f)
    (bits : List Bool) :
    ∃t ≤ (Compile.clockPolynomial p.clock).eval bits.length,
      ∃c : NPMachine.Config (Compile.machine p.code.program),
        NPMachine.Run (Compile.machine p.code.program) t (NPMachine.initial (Compile.machine p.code.program) bits) c ∧
        NPMachine.accepts (Compile.machine p.code.program) c ∧ c.head=0 ∧
        ∀j,Compile.outputTrack p.code.program c j=(f bits).reverse[j]? := by
  obtain ⟨T,hT,d,hr,ha,hout⟩ := p.computes bits
  obtain ⟨t,ht,c,hc,hacc,hhead,htrack⟩ := Compile.run_output_complete p.code.program bits hr ha
  refine ⟨t,?_,c,hc,hacc,hhead,?_⟩
  · rw [Compile.clockPolynomial_eval]
    exact ht.trans (Compile.timeBound_mono hT)
  · simpa only [hout] using htrack

end BalancedAssortments.NPStack
