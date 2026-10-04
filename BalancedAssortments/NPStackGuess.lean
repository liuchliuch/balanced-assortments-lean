import BalancedAssortments.NPStackEmbeddingReflect
import BalancedAssortments.NPStackEmbeddingDeterministic

namespace BalancedAssortments.NPStack.Guess
open NPStack
variable {K Q : Type*} [DecidableEq K]

inductive State (Q : Type*) | guess | choose | push (bit : Bool) | body (q : Q)
  deriving DecidableEq, Fintype

def program (P : Program K Q) (certificate : K) : Program K (State Q) where
  code
    | .guess => .choice (.body P.start) .choose
    | .choose => .choice (.push false) (.push true)
    | .push b => .push certificate b .guess
    | .body q => (P.code q).rename id State.body
  start := .guess
  inputStack := P.inputStack
  outputStack := P.outputStack

def twoInput (P : Program K Q) (certificate : K) (word candidate : List Bool) : Config K Q :=
  ⟨P.start,Function.update (initial P word).stk certificate candidate⟩
def cfg (P : Program K Q) (certificate : K) (q : State Q) (word candidate : List Bool) : Config K (State Q) :=
  ⟨q,(twoInput P certificate word candidate).stk⟩

lemma initial_cfg (P : Program K Q) (certificate : K) (hne : certificate≠P.inputStack) (word : List Bool) :
    initial (program P certificate) word=cfg P certificate .guess word [] := by
  unfold initial program cfg twoInput
  congr 1
  funext k
  by_cases hk : k=certificate
  · subst k;simp [Function.update,hne]
  · simp [Function.update,hk,initial]

lemma push_step (P : Program K Q) (certificate : K) (b : Bool) (word candidate : List Bool) :
    Step (program P certificate) (cfg P certificate (.push b) word candidate)
      (cfg P certificate .guess word (b::candidate)) := by
  simp [Step,successors,program,cfg,twoInput,Function.update_idem]

lemma guess_bit (P : Program K Q) (certificate : K) (b : Bool) (word candidate : List Bool) :
    Run (program P certificate) 3 (cfg P certificate .guess word candidate)
      (cfg P certificate .guess word (b::candidate)) := by
  apply Run.succ (d := cfg P certificate .choose word candidate)
  · simp [Step,successors,program,cfg]
  · apply Run.succ (d := cfg P certificate (.push b) word candidate)
    · cases b <;> simp [Step,successors,program,cfg]
    · exact Run.one (push_step P certificate b word candidate)

lemma guess_bits (P : Program K Q) (certificate : K) (bits word candidate : List Bool) :
    Run (program P certificate) (3*bits.length) (cfg P certificate .guess word candidate)
      (cfg P certificate .guess word (bits.reverse++candidate)) := by
  induction bits generalizing candidate with
  | nil => simpa using Run.zero (cfg P certificate .guess word candidate)
  | cons b bs ih =>
    have h := (guess_bit P certificate b word candidate).trans (ih (b::candidate))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_comm] using h

lemma stop_step (P : Program K Q) (certificate : K) (word candidate : List Bool) :
    Step (program P certificate) (cfg P certificate .guess word candidate)
      (cfg P certificate (.body P.start) word candidate) := by
  simp [Step,successors,program,cfg]

/-- Any desired candidate word is guessed in exactly three primitive steps
per bit plus one stop choice. There is no numeric guess-limit oracle. -/
theorem guess_run (P : Program K Q) (certificate : K) (word candidate : List Bool) :
    Run (program P certificate) (3*candidate.length+1) (cfg P certificate .guess word [])
      (cfg P certificate (.body P.start) word candidate) := by
  have hg := guess_bits P certificate candidate.reverse word []
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hg
  exact hg.trans (Run.one (stop_step P certificate word candidate))

lemma body_code (P : Program K Q) (certificate : K) (q : Q) :
    (program P certificate).code (.body q)=(P.code q).rename id State.body := rfl

/-- The literal verifier run is embedded after the nondeterministic phase. -/
lemma body_run (P : Program K Q) (certificate : K) {t : ℕ} {c d : Config K Q}
    (h : Run P t c d) :
    Run (program P certificate) t ⟨.body c.pc,c.stk⟩ ⟨.body d.pc,d.stk⟩ := by
  apply h.relocate_exact id State.body Function.injective_id (fun q _ => rfl)
  · exact ⟨rfl,fun _ => rfl⟩
  · exact ⟨rfl,fun _ => rfl⟩
  · intro k hk;exact False.elim (hk k rfl)

end BalancedAssortments.NPStack.Guess
