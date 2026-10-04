import BalancedAssortments.NPStackEmbeddingDeterministic

/-! A real finite-step timeout. Every simulated nonhalting source instruction
is preceded by one primitive fuel pop. Fuel exhaustion returns false; no
mathematical clock predicate is substituted for execution. -/
namespace BalancedAssortments.NPStack.Timeout
open NPStack
variable {K Q : Type*} [DecidableEq K]

abbrev Stack (K : Type*) := Sum K Unit
inductive State (Q : Type*) | tick (q : Q) | execute (q : Q) | expired
  deriving DecidableEq, Fintype

def program (P : Program K Q) : Program (Stack K) (State Q) where
  code
    | .tick q => match P.code q with
      | .halt b => .halt b
      | _ => .pop (.inr ()) .expired (.execute q) (.execute q)
    | .execute q => (P.code q).rename Sum.inl State.tick
    | .expired => .halt false
  start := .tick P.start
  inputStack := .inl P.inputStack
  outputStack := .inl P.outputStack

def liftStore (s : K→List Bool) (fuel : List Bool) : Stack K→List Bool
  | .inl k => s k
  | .inr _ => fuel

def cfg (q : State Q) (c : Config K Q) (fuel : List Bool) : Config (Stack K) (State Q) :=
  ⟨q,liftStore c.stk fuel⟩
def start (c : Config K Q) (fuel : List Bool) : Config (Stack K) (State Q) := cfg (.tick c.pc) c fuel

lemma lift_update (s : K→List Bool) (fuel xs : List Bool) (k : K) :
    Function.update (liftStore s fuel) (.inl k) xs=liftStore (Function.update s k xs) fuel := by
  funext j
  cases j with
  | inl j => simp [liftStore,Function.update]
  | inr u => simp [liftStore,Function.update]
lemma lift_fuel_update (s : K→List Bool) (fuel rest : List Bool) :
    Function.update (liftStore s fuel) (.inr ()) rest=liftStore s rest := by
  funext j
  cases j with
  | inl j => simp [liftStore,Function.update]
  | inr u => cases u;simp [liftStore,Function.update]

lemma tick_nonempty (P : Program K Q) (c : Config K Q) (b : Bool) (fuel : List Bool)
    (hn : ∀ v,P.code c.pc≠.halt v) :
    Step (program P) (start c (b::fuel)) (cfg (.execute c.pc) c fuel) := by
  cases hi : P.code c.pc <;> simp [Step,successors,program,start,cfg,hi,liftStore,lift_fuel_update]
  rename_i v
  exact False.elim (hn v hi)

lemma tick_empty (P : Program K Q) (c : Config K Q) (hn : ∀ v,P.code c.pc≠.halt v) :
    Step (program P) (start c []) (cfg .expired c []) := by
  cases hi : P.code c.pc <;> simp [Step,successors,program,start,cfg,hi,liftStore]
  rename_i v
  exact False.elim (hn v hi)

lemma execute_step {P : Program K Q} {c d : Config K Q} (hs : Step P c d) (fuel : List Bool) :
    Step (program P) (cfg (.execute c.pc) c fuel) (start d fuel) := by
  unfold Step successors at hs
  cases hi : P.code c.pc with
  | halt b => simp [hi] at hs
  | jump q =>
    simp only [hi,List.mem_singleton] at hs;subst d
    simp [Step,successors,program,cfg,start,hi,Instr.rename]
  | push k b q =>
    simp only [hi,List.mem_singleton] at hs;subst d
    simp [Step,successors,program,cfg,start,hi,Instr.rename,liftStore,lift_update]
  | pop k qe qf qt =>
    cases hh : c.stk k with
    | nil =>
      simp only [hi,hh,List.mem_singleton] at hs;subst d
      simp [Step,successors,program,cfg,start,hi,hh,Instr.rename,liftStore]
    | cons b bs =>
      simp only [hi,hh,List.mem_singleton] at hs;subst d
      cases b <;> simp [Step,successors,program,cfg,start,hi,hh,Instr.rename,liftStore,lift_update]
  | choice q r =>
    simp only [hi,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hs
    rcases hs with rfl | rfl <;> simp [Step,successors,program,cfg,start,hi,Instr.rename]

lemma source_step {P : Program K Q} {c d : Config K Q} (hs : Step P c d) (b : Bool) (fuel : List Bool) :
    Run (program P) 2 (start c (b::fuel)) (start d fuel) := by
  have hn : ∀ v,P.code c.pc≠.halt v := fun v h => halted_no_step h hs
  exact .succ (tick_nonempty P c b fuel hn) (.one (execute_step hs fuel))

/-- A source path fitting in the physically supplied fuel executes exactly,
with two real target transitions per source transition. -/
theorem run_complete {P : Program K Q} {t : ℕ} {c d : Config K Q}
    (h : Run P t c d) (fuel : List Bool) (ht : t≤fuel.length) :
    Run (program P) (2*t) (start c fuel) (start d (fuel.drop t)) := by
  induction h generalizing fuel with
  | zero c => simpa using Run.zero (start c fuel)
  | @succ t c d e hs hr ih =>
    cases fuel with
    | nil => simp at ht
    | cons b fuel =>
      have hh := (source_step hs b fuel).trans (ih fuel (by simpa using ht))
      simpa [Nat.mul_add,Nat.add_comm] using hh

lemma accepts_start {P : Program K Q} {c : Config K Q} (fuel : List Bool) (h : accepts P c) :
    accepts (program P) (start c fuel) := by
  change P.code c.pc=.halt true at h
  simp [accepts,start,cfg,program,h]

lemma program_noChoice {P : Program K Q} (h : NoChoice P) : NoChoice (program P) := by
  intro q a b
  cases q with
  | tick q => cases hi : P.code q <;> simp [program,hi]
  | execute q => exact Instr.rename_no_choice _ (h q) _ _ a b
  | expired => simp [program]

end BalancedAssortments.NPStack.Timeout
