import Mathlib

/-! Explicit finite-control Boolean-stack bytecode. Instructions can inspect or
modify only one Boolean stack cell per transition. There are no unbounded
registers, decoded arithmetic instructions, or semantic callback oracles. -/
namespace BalancedAssortments.NPStack

inductive Instr (K Q : Type*)
  | halt (accept : Bool)
  | jump (next : Q)
  | push (stack : K) (bit : Bool) (next : Q)
  | pop (stack : K) (empty onFalse onTrue : Q)
  | choice (left right : Q)
  deriving DecidableEq

structure Config (K Q : Type*) where
  pc : Q
  stk : K → List Bool

structure Program (K Q : Type*) where
  code : Q → Instr K Q
  start : Q
  inputStack : K
  outputStack : K

variable {K Q : Type*} [DecidableEq K]

def successors (P : Program K Q) (c : Config K Q) : List (Config K Q) :=
  match P.code c.pc with
  | .halt _ => []
  | .jump q => [⟨q,c.stk⟩]
  | .push k b q => [⟨q,Function.update c.stk k (b::c.stk k)⟩]
  | .pop k qe qf qt =>
    match c.stk k with
    | [] => [⟨qe,c.stk⟩]
    | b::bs => [⟨if b then qt else qf,Function.update c.stk k bs⟩]
  | .choice q r => [⟨q,c.stk⟩,⟨r,c.stk⟩]

def Step (P : Program K Q) (c d : Config K Q) : Prop := d ∈ successors P c

inductive Run (P : Program K Q) : ℕ → Config K Q → Config K Q → Prop
  | zero (c) : Run P 0 c c
  | succ {t c d e} : Step P c d → Run P t d e → Run P (t+1) c e

def initial (P : Program K Q) (input : List Bool) : Config K Q :=
  ⟨P.start,Function.update (fun _ => []) P.inputStack input⟩

def accepts (P : Program K Q) (c : Config K Q) : Prop := P.code c.pc = .halt true

def OutputsIn (P : Program K Q) (input output : List Bool) (T : ℕ) : Prop :=
  ∃ t≤T,∃ c,Run P t (initial P input) c ∧ accepts P c ∧ c.stk P.outputStack=output

lemma Run.trans {P : Program K Q} {a b : ℕ} {c d e : Config K Q}
    (h : Run P a c d) (g : Run P b d e) : Run P (a+b) c e := by
  induction h with
  | zero => simpa using g
  | succ hs hr ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Run.succ hs (ih g)

lemma Run.one {P : Program K Q} {c d : Config K Q} (h : Step P c d) : Run P 1 c d :=
  .succ h (.zero d)

lemma halted_no_step {P : Program K Q} {c d : Config K Q} {b : Bool}
    (h : P.code c.pc = .halt b) : ¬ Step P c d := by simp [Step,successors,h]

lemma successors_length (P : Program K Q) (c : Config K Q) : (successors P c).length≤2 := by
  unfold successors
  cases P.code c.pc <;> simp
  split <;> simp

lemma Step.stack_length {P : Program K Q} {c d : Config K Q} (h : Step P c d) (k : K) :
    (d.stk k).length ≤ (c.stk k).length+1 := by
  unfold Step successors at h
  cases hi : P.code c.pc with
  | halt b => simp [hi] at h
  | jump q => simp only [hi,List.mem_singleton] at h; subst d; simp
  | push j b q =>
    simp only [hi,List.mem_singleton] at h
    subst d
    by_cases hk : k=j <;> simp [Function.update,hk]
  | pop j qe qf qt =>
    simp only [hi] at h
    cases he : c.stk j with
    | nil => simp only [he,List.mem_singleton] at h; subst d; simp
    | cons b bs =>
      simp only [he,List.mem_singleton] at h
      subst d
      by_cases hk : k=j
      · subst k; simp [Function.update,he]; omega
      · simp [Function.update,hk]
  | choice q r =>
    simp only [hi,List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with rfl | rfl <;> simp

lemma Run.stack_length {P : Program K Q} {t : ℕ} {c d : Config K Q}
    (h : Run P t c d) (k : K) : (d.stk k).length≤(c.stk k).length+t := by
  induction h with
  | zero => simp
  | succ hs hr ih => have hh := hs.stack_length k; omega

/-- Finiteness is an explicit property of the operational program used in
machine compilation. Every stack alphabet is Boolean, not merely the input one. -/
structure FiniteProgram where
  K : Type
  Q : Type
  [stackFinite : Fintype K]
  [controlFinite : Fintype Q]
  [stackDecidable : DecidableEq K]
  program : Program K Q

attribute [instance] FiniteProgram.stackFinite FiniteProgram.controlFinite FiniteProgram.stackDecidable

end BalancedAssortments.NPStack
