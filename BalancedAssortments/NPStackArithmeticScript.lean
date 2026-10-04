import BalancedAssortments.NPStackEmbedding
import BalancedAssortments.NPStackDeterministic
import BalancedAssortments.DirectVerifierRegisters

/-! A fixed straight-line script is compiled to nested finite control sums.
Each arithmetic assignment is an explicit supplied finite Program; its actual
instructions are copied into the result. No evaluator is a machine opcode. -/
namespace BalancedAssortments.NPStack.ArithmeticScript
open NPStack DirectVerifier ComplexityTimeVerifier

variable {K Q : Type} [DecidableEq K] [DecidableEq Q]

def State (Q : Type) : List ArithmeticAssignment→Type
  | [] => Unit
  | _::ops => Sum Q (State Q ops)

instance stateDecidable (ops : List ArithmeticAssignment) : DecidableEq (State Q ops) := by
  induction ops with
  | nil => exact inferInstanceAs (DecidableEq Unit)
  | cons op ops ih => exact inferInstanceAs (DecidableEq (Sum Q (State Q ops)))
instance stateFinite [Fintype Q] (ops : List ArithmeticAssignment) : Fintype (State Q ops) := by
  induction ops with
  | nil => exact inferInstanceAs (Fintype Unit)
  | cons op ops ih => exact inferInstanceAs (Fintype (Sum Q (State Q ops)))

def start (P : ArithmeticAssignment→Program K Q) : (ops : List ArithmeticAssignment)→State Q ops
  | [] => ()
  | op::_ => .inl (P op).start

def done : (ops : List ArithmeticAssignment)→State Q ops
  | [] => ()
  | _::ops => .inr (done ops)

def code (P : ArithmeticAssignment→Program K Q) (exit : ArithmeticAssignment→Q) :
    (ops : List ArithmeticAssignment)→State Q ops→Instr K (State Q ops)
  | [],_ => .halt true
  | op::ops,.inl q => if q=exit op then .jump (.inr (start P ops))
      else ((P op).code q).rename id Sum.inl
  | _::ops,.inr q => (code P exit ops q).rename id Sum.inr

def program (P : ArithmeticAssignment→Program K Q) (exit : ArithmeticAssignment→Q)
    (input output : K) (ops : List ArithmeticAssignment) : Program K (State Q ops) :=
  ⟨code P exit ops,start P ops,input,output⟩

lemma done_halts (P : ArithmeticAssignment→Program K Q) (exit : ArithmeticAssignment→Q)
    (input output : K) (ops : List ArithmeticAssignment) :
    (program P exit input output ops).code (done ops)=.halt true := by
  induction ops with
  | nil => rfl
  | cons op ops ih => simpa only [program,done,code,Instr.rename] using congrArg (Instr.rename id Sum.inr) ih

lemma head_extends (P : ArithmeticAssignment→Program K Q) (exit : ArithmeticAssignment→Q)
    (input output : K) (ops : List ArithmeticAssignment) (op : ArithmeticAssignment)
    (hexit : (P op).code (exit op)=.halt true) :
    CodeExtends (P op) (program P exit input output (op::ops)) id Sum.inl := by
  intro q h
  have hn : q≠exit op := by intro he;subst q;exact h true hexit
  simp only [program,code,hn,if_false]
lemma tail_extends (P : ArithmeticAssignment→Program K Q) (exit : ArithmeticAssignment→Q)
    (input output : K) (ops : List ArithmeticAssignment) (op : ArithmeticAssignment) :
    CodeExtends (program P exit input output ops) (program P exit input output (op::ops)) id Sum.inr := by
  intro q h;rfl

def budget (T : ArithmeticAssignment→(RowReg→ZBits)→ℕ) :
    List ArithmeticAssignment→(RowReg→ZBits)→ℕ
  | [],_ => 0
  | op::ops,s => T op s+1+budget T ops (evalAssignment op s)

/-- Composition counts real primitive subroutine transitions and one real
return jump per assignment. This theorem is instantiated with the proved
copying signed-add/multiply assignment programs. -/
theorem run_script (P : ArithmeticAssignment→Program K Q) (exit : ArithmeticAssignment→Q)
    (input output : K) (encode : (RowReg→ZBits)→K→List Bool)
    (T : ArithmeticAssignment→(RowReg→ZBits)→ℕ)
    (hexit : ∀ op,(P op).code (exit op)=.halt true)
    (hop : ∀ op s,∃ t≤T op s,Run (P op) t ⟨(P op).start,encode s⟩
      ⟨exit op,encode (evalAssignment op s)⟩)
    (ops : List ArithmeticAssignment) (s : RowReg→ZBits) :
    ∃ t≤budget T ops s,Run (program P exit input output ops) t ⟨start P ops,encode s⟩
      ⟨done ops,encode (evalAssignments ops s)⟩ := by
  induction ops generalizing s with
  | nil => exact ⟨0,le_rfl,Run.zero _⟩
  | cons op ops ih =>
    obtain ⟨t,ht,hr⟩ := hop op s
    obtain ⟨u,hu,hs⟩ := ih (evalAssignment op s)
    have hhead : Run (program P exit input output (op::ops)) t
        ⟨.inl (P op).start,encode s⟩ ⟨.inl (exit op),encode (evalAssignment op s)⟩ := by
      apply hr.relocate_exact id Sum.inl Function.injective_id
        (head_extends P exit input output ops op (hexit op))
      · exact ⟨rfl,fun _ => rfl⟩
      · exact ⟨rfl,fun _ => rfl⟩
      · intro k hk;exact False.elim (hk k rfl)
    have htail : Run (program P exit input output (op::ops)) u
        ⟨.inr (start P ops),encode (evalAssignment op s)⟩
        ⟨.inr (done ops),encode (evalAssignments ops (evalAssignment op s))⟩ := by
      apply hs.relocate_exact id Sum.inr Function.injective_id (tail_extends P exit input output ops op)
      · exact ⟨rfl,fun _ => rfl⟩
      · exact ⟨rfl,fun _ => rfl⟩
      · intro k hk;exact False.elim (hk k rfl)
    have hj : Step (program P exit input output (op::ops))
        ⟨.inl (exit op),encode (evalAssignment op s)⟩
        ⟨.inr (start P ops),encode (evalAssignment op s)⟩ := by
      simp [Step,successors,program,code]
    refine ⟨t+1+u,by dsimp only [budget];omega,?_⟩
    exact (hhead.trans (Run.one hj)).trans htail

private lemma rename_noChoice {K Q K' Q' : Type} (i : Instr K Q) (fk : K→K') (fq : Q→Q')
    (h : ∀ a b,i≠.choice a b) (a b : Q') : i.rename fk fq≠.choice a b := by
  cases i <;> simp_all [Instr.rename]

theorem program_noChoice (P : ArithmeticAssignment→Program K Q) (exit : ArithmeticAssignment→Q)
    (input output : K) (hn : ∀ op,NoChoice (P op)) (ops : List ArithmeticAssignment) :
    NoChoice (program P exit input output ops) := by
  induction ops with
  | nil => intro q a b;simp [program,code]
  | cons op ops ih =>
    intro q a b
    cases q with
    | inl q =>
      by_cases he : q=exit op
      · simp [program,code,he]
      · exact (by simpa only [program,code,he,if_false] using
          rename_noChoice ((P op).code q) id Sum.inl (hn op q) a b)
    | inr q => exact rename_noChoice _ id Sum.inr (ih q) a b

theorem halted_result (P : ArithmeticAssignment→Program K Q) (exit : ArithmeticAssignment→Q)
    (input output : K) (encode : (RowReg→ZBits)→K→List Bool)
    (T : ArithmeticAssignment→(RowReg→ZBits)→ℕ)
    (hexit : ∀ op,(P op).code (exit op)=.halt true)
    (hop : ∀ op s,∃ t≤T op s,Run (P op) t ⟨(P op).start,encode s⟩
      ⟨exit op,encode (evalAssignment op s)⟩)
    (hn : ∀ op,NoChoice (P op)) (ops : List ArithmeticAssignment) (s : RowReg→ZBits)
    {t : ℕ} {c : Config K (State Q ops)} {b : Bool}
    (hr : Run (program P exit input output ops) t ⟨start P ops,encode s⟩ c)
    (hc : (program P exit input output ops).code c.pc=.halt b) :
    t≤budget T ops s ∧ c=⟨done ops,encode (evalAssignments ops s)⟩ := by
  obtain ⟨u,hu,hh⟩ := run_script P exit input output encode T hexit hop ops s
  have he := hr.halted_unique (noChoice_deterministic (program_noChoice P exit input output hn ops))
    hh hc (done_halts P exit input output ops)
  exact ⟨he.1 ▸ hu,he.2⟩

end BalancedAssortments.NPStack.ArithmeticScript
