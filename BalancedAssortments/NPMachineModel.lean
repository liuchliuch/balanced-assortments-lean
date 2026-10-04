import Mathlib

/-! Concrete polynomial-clock nondeterministic one-tape Turing machines.
States and symbols are finite, choices are a finite list of transition records,
and the tape is indexed by the integers. No input-dependent verifier oracle or
unbounded transition function occurs in the machine description. -/
namespace BalancedAssortments.NPMachine

inductive Move | left | stay | right deriving DecidableEq, Fintype

def Move.displacement : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

lemma Move.displacement_bound (m : Move) : |m.displacement| ≤ 1 := by
  cases m <;> norm_num [Move.displacement]

structure Rule (q g : ℕ) where
  source : Fin (q+1)
  read : Fin (g+3)
  target : Fin (q+1)
  write : Fin (g+3)
  move : Move
  deriving DecidableEq

/-- Symbols 0,1 encode input bits and symbol 2 is blank; the remaining finite
alphabet and control states are specified by the machine. -/
structure Machine where
  stateExtra : ℕ
  symbolExtra : ℕ
  start : Fin (stateExtra+1)
  accepting : Fin (stateExtra+1) → Bool
  rules : List (Rule stateExtra symbolExtra)

structure Config (M : Machine) where
  state : Fin (M.stateExtra+1)
  head : ℤ
  tape : ℤ → Fin (M.symbolExtra+3)

def bitSymbol (M : Machine) (b : Bool) : Fin (M.symbolExtra+3) :=
  if b then ⟨1,by omega⟩ else ⟨0,by omega⟩
def blank (M : Machine) : Fin (M.symbolExtra+3) := ⟨2,by omega⟩

def inputTape (M : Machine) (word : List Bool) (k : ℤ) : Fin (M.symbolExtra+3) :=
  if 0 ≤ k then
    match word[k.toNat]? with
    | some b => bitSymbol M b
    | none => blank M
  else blank M

def initial (M : Machine) (word : List Bool) : Config M := ⟨M.start,0,inputTape M word⟩
def accepts (M : Machine) (c : Config M) : Prop := M.accepting c.state = true

def applicable {M : Machine} (c : Config M) (r : Rule M.stateExtra M.symbolExtra) : Prop :=
  c.state = r.source ∧ c.tape c.head = r.read

instance {M : Machine} (c : Config M) (r : Rule M.stateExtra M.symbolExtra) : Decidable (applicable c r) := by
  unfold applicable
  infer_instance

def execute {M : Machine} (c : Config M) (r : Rule M.stateExtra M.symbolExtra) : Config M :=
  ⟨r.target,c.head+r.move.displacement,Function.update c.tape c.head r.write⟩

/-- A step chooses one global transition record, used for its source state,
read symbol, write symbol, next state and head motion together. -/
def Step (M : Machine) (c d : Config M) : Prop :=
  ∃ r ∈ M.rules, applicable c r ∧ d = execute c r

inductive Run (M : Machine) : ℕ → Config M → Config M → Prop
  | zero (c) : Run M 0 c c
  | succ {t c d e} : Step M c d → Run M t d e → Run M (t+1) c e

/-- Ordinary accepting computation within a numerical step bound. -/
def AcceptsWithin (M : Machine) (word : List Bool) (T : ℕ) : Prop :=
  ∃ t ≤ T, ∃ c, Run M t (initial M word) c ∧ accepts M c

/-- Conventional polynomial-clock nondeterministic-machine language class.
The machine is fixed and finite; only input length controls the polynomial
clock. This definition has no arbitrary verifier predicate as a premise. -/
def InNP (L : Set (List Bool)) : Prop :=
  ∃ M : Machine, ∃ p : Polynomial ℕ, ∀ word,
    word ∈ L ↔ AcceptsWithin M word (p.eval word.length)

lemma Step.head_bound {M : Machine} {c d : Config M} (h : Step M c d) : |d.head-c.head| ≤ 1 := by
  obtain ⟨r,_,_,rfl⟩ := h
  simpa [execute] using r.move.displacement_bound

lemma Run.head_bound {M : Machine} {T : ℕ} {c d : Config M} (h : Run M T c d) :
    |d.head-c.head| ≤ (T : ℤ) := by
  induction h with
  | zero c => simp
  | @succ t c d e hs hr ih =>
    have hstep := hs.head_bound
    calc |e.head-c.head| = |(e.head-d.head)+(d.head-c.head)| := by congr 1; ring
         _ ≤ |e.head-d.head|+|d.head-c.head| := abs_add_le _ _
         _ ≤ (t : ℤ)+1 := add_le_add ih hstep
         _ = ((t+1 : ℕ) : ℤ) := by simp

lemma Run.trans {M : Machine} {s t : ℕ} {a b c : Config M}
    (h : Run M s a b) (k : Run M t b c) : Run M (s+t) a c := by
  induction h with
  | zero a => simpa using k
  | @succ s a b d hab hbd ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Run.succ hab (ih k)

/-- Accepting configurations may stutter to pad the tableau to its clock length.
This is a logical simulation convenience, not an extra computational oracle. -/
def PaddedStep (M : Machine) (c d : Config M) : Prop := Step M c d ∨ (accepts M c ∧ d=c)

inductive PaddedRun (M : Machine) : ℕ → Config M → Config M → Prop
  | zero (c) : PaddedRun M 0 c c
  | succ {t c d e} : PaddedStep M c d → PaddedRun M t d e → PaddedRun M (t+1) c e

lemma Run.padded {M : Machine} {t : ℕ} {c d : Config M} (h : Run M t c d) : PaddedRun M t c d := by
  induction h with
  | zero c => exact PaddedRun.zero c
  | succ hstep _ ih => exact PaddedRun.succ (Or.inl hstep) ih

lemma PaddedRun.trans {M : Machine} {s t : ℕ} {a b c : Config M}
    (h : PaddedRun M s a b) (k : PaddedRun M t b c) : PaddedRun M (s+t) a c := by
  induction h with
  | zero a => simpa using k
  | @succ s a b d hab hbd ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using PaddedRun.succ hab (ih k)

lemma PaddedRun.stutter {M : Machine} (c : Config M) (hc : accepts M c) (t : ℕ) : PaddedRun M t c c := by
  induction t with
  | zero => exact PaddedRun.zero c
  | succ t ih => exact PaddedRun.succ (Or.inr ⟨hc,rfl⟩) ih

lemma PaddedRun.accepting_prefix {M : Machine} {T : ℕ} {c d : Config M}
    (h : PaddedRun M T c d) (hd : accepts M d) :
    ∃ t ≤ T, ∃ e, Run M t c e ∧ accepts M e := by
  induction h with
  | zero c => exact ⟨0,le_rfl,c,Run.zero c,hd⟩
  | @succ t c d e hs hr ih =>
    rcases hs with hs | ⟨hc,_⟩
    · obtain ⟨u,hu,f,hf,hfa⟩ := ih hd
      exact ⟨u+1,by omega,f,Run.succ hs hf,hfa⟩
    · exact ⟨0,by omega,c,Run.zero c,hc⟩

/-- Padding gives exactly the original bounded-acceptance semantics. -/
theorem acceptsWithin_iff_padded (M : Machine) (word : List Bool) (T : ℕ) :
    AcceptsWithin M word T ↔ ∃ c, PaddedRun M T (initial M word) c ∧ accepts M c := by
  constructor
  · rintro ⟨t,ht,c,hc,ha⟩
    refine ⟨c,?_,ha⟩
    have h := hc.padded.trans (PaddedRun.stutter c ha (T-t))
    simpa [Nat.add_sub_of_le ht] using h
  · rintro ⟨c,hc,ha⟩
    exact hc.accepting_prefix ha

lemma PaddedStep.head_bound {M : Machine} {c d : Config M} (h : PaddedStep M c d) : |d.head-c.head| ≤ 1 := by
  rcases h with h | ⟨_,rfl⟩
  · exact h.head_bound
  · simp

lemma PaddedRun.head_bound {M : Machine} {T : ℕ} {c d : Config M} (h : PaddedRun M T c d) :
    |d.head-c.head| ≤ (T : ℤ) := by
  induction h with
  | zero c => simp
  | @succ t c d e hs hr ih =>
    have hstep := hs.head_bound
    calc |e.head-c.head| = |(e.head-d.head)+(d.head-c.head)| := by congr 1; ring
         _ ≤ |e.head-d.head|+|d.head-c.head| := abs_add_le _ _
         _ ≤ (t : ℤ)+1 := add_le_add ih hstep
         _ = ((t+1 : ℕ) : ℤ) := by simp

end BalancedAssortments.NPMachine
