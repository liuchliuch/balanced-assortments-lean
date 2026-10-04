import BalancedAssortments.NPPolynomialOutputSimulation

/-! Determinism of the concrete numbered one-tape simulation. NoChoice source
programs produce at most one local action for every control/symbol pair,
including initialization and all microstates, not only reachable states. -/
noncomputable section
namespace BalancedAssortments.NPMachine

def Deterministic (M : Machine) : Prop :=
  ∀c d e,Step M c d → Step M c e → d=e

namespace FiniteBridge
variable {Q A : Type*} [Fintype Q] [Fintype A]

lemma eq_of_mem_length_le_one {α : Type*} {xs : List α} {a b : α}
    (h : xs.length≤1) (ha : a∈xs) (hb : b∈xs) : a=b := by
  cases xs with
  | nil => simp at ha
  | cons x xs =>
    have hz : xs=[] := List.length_eq_zero_iff.mp (by simpa using h)
    subst xs
    simp only [List.mem_singleton] at ha hb
    exact ha.trans hb.symm

/-- Global determinism follows directly from the finite local transition table.
No reachable-configuration or accepted-run premise is needed. -/
theorem table_machine_deterministic (start : Q) (accept : Q → Bool)
    (next : Q → Symbol A → List (Action Q A))
    (hn : ∀q a,(next q a).length≤1) : Deterministic (compile (tableProgram start accept next)) := by
  intro c d e hd he
  obtain ⟨r,hr,hra,rfl⟩ := hd
  obtain ⟨s,hs,hsa,rfl⟩ := he
  change r∈(tableRules next).map transitionCode at hr
  change s∈(tableRules next).map transitionCode at hs
  obtain ⟨ar,ar_mem,rfl⟩ := List.mem_map.mp hr
  obtain ⟨br,br_mem,rfl⟩ := List.mem_map.mp hs
  have hsource : ar.source=br.source := stateCode_injective (hra.1.symm.trans hsa.1)
  have hread : ar.read=br.read := symbolCode_injective (hra.2.symm.trans hsa.2)
  have ha := (mem_tableRules next ar).mp ar_mem
  have hb := (mem_tableRules next br).mp br_mem
  rw [← hsource,← hread] at hb
  have heq := eq_of_mem_length_le_one (hn ar.source ar.read) ha hb
  have hrs : ar=br := by
    cases ar;cases br
    simp_all
  rw [hrs]

end FiniteBridge
end BalancedAssortments.NPMachine

namespace BalancedAssortments.NPStack.Compile
open NPMachine NPMachine.FiniteBridge TapeMachine TapeInitialize
variable {K Q : Type*} [Fintype K] [Fintype Q] [DecidableEq K]

lemma lifted_noChoice (P : NPStack.Program K Q) (hn : NoChoice P) : NoChoice (liftedProgram P) := by
  intro q a b
  cases q with
  | inl q => cases q <;> simp [liftedProgram]
  | inr q =>
    cases h : P.code q <;> simp [liftedProgram,liftInstr,h]
    exact False.elim (hn _ _ _ h)

lemma actions_length_le_one (P : NPStack.Program K Q) (hn : NoChoice P)
    (q : TapeMachine.Control K Q) (a : Symbol (TapeMachine.Cell K)) :
    (TapeMachine.actions P q a).length≤1 := by
  cases q with
  | normal q =>
    cases h : P.code q <;> simp [TapeMachine.actions,h]
    exact False.elim (hn _ _ _ h)
  | seekPush k b q =>
    cases h : (readCell a).2 k <;> simp [TapeMachine.actions,h]
  | seekPop k qe qf qt =>
    cases h : (readCell a).2 k
    · cases hb : (readCell a).1 <;> simp [TapeMachine.actions,h,hb]
    · simp [TapeMachine.actions,h]
  | popAt k qf qt => cases h : (readCell a).2 k <;> simp [TapeMachine.actions,h]
  | back q => cases h : (readCell a).1 <;> simp [TapeMachine.actions,h]

lemma initActions_length_le_one (P : NPStack.Program K Q) (hn : NoChoice P)
    (q : InitControl K Q) (a : Symbol (InitCell K)) :
    (initActions P q a).length≤1 := by
  cases q with
  | scan first => cases a <;> cases first <;> simp [initActions]
  | back => cases h : (readCell a).1 <;> simp [initActions,h]
  | run q =>
    simp only [initActions,List.length_map]
    exact actions_length_le_one (liftedProgram P) (lifted_noChoice P hn) q a

/-- The same compiled one-tape machine used by the output and NP simulation
is globally deterministic whenever the source contains no choice instruction. -/
theorem machine_deterministic (P : NPStack.Program K Q) (hn : NoChoice P) :
    NPMachine.Deterministic (machine P) :=
  table_machine_deterministic _ _ _ (initActions_length_le_one P hn)

end BalancedAssortments.NPStack.Compile

namespace BalancedAssortments.NPStack

theorem PolynomialProgram.one_tape_deterministic {f : List Bool → List Bool} (p : PolynomialProgram f) :
    NPMachine.Deterministic (Compile.machine p.code.program) :=
  Compile.machine_deterministic p.code.program p.noChoice

end BalancedAssortments.NPStack
