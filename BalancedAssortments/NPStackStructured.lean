import BalancedAssortments.NPStackEmbedding
import BalancedAssortments.NPStackDeterministic

/-! Finite structured stack programs. Structured loops compile to real finite
pop/jump control graphs; there is no semantic callback or recursive instruction
in the target bytecode. -/
namespace BalancedAssortments.NPStack.Structured
open NPStack

/-- An atom is a complete explicit finite primitive instruction table. Its proof
field certifies an exit label; it does not contain a semantic function oracle. -/
structure Atom (K : Type*) where
  states : ℕ
  instructions : Fin states → Instr K (Fin states)
  start : Fin states
  exit : Fin states
  halted : instructions exit=.halt true
  noChoice : ∀ q a b,instructions q≠.choice a b

inductive Block (K : Type*)
  | skip
  | atom (program : Atom K)
  | push (stack : K) (bit : Bool)
  | seq (first second : Block K)
  | branch (stack : K) (empty onFalse onTrue : Block K)
  | loop (stack : K) (onFalse onTrue : Block K)

variable {K : Type*}

def Control : Block K → Type
  | .skip => Bool
  | .atom p => Fin p.states
  | .push _ _ => Bool
  | .seq a b => Control a ⊕ Control b
  | .branch _ e f t => Bool ⊕ (Control e ⊕ (Control f ⊕ Control t))
  | .loop _ f t => Bool ⊕ (Control f ⊕ Control t)

def controlDecidable : (b : Block K) → DecidableEq (Control b)
  | .skip => inferInstanceAs (DecidableEq Bool)
  | .atom p => inferInstanceAs (DecidableEq (Fin p.states))
  | .push _ _ => inferInstanceAs (DecidableEq Bool)
  | .seq a b =>
    letI := controlDecidable a
    letI := controlDecidable b
    inferInstanceAs (DecidableEq (Control a ⊕ Control b))
  | .branch _ e f t =>
    letI := controlDecidable e
    letI := controlDecidable f
    letI := controlDecidable t
    inferInstanceAs (DecidableEq (Bool ⊕ (Control e ⊕ (Control f ⊕ Control t))))
  | .loop _ f t =>
    letI := controlDecidable f
    letI := controlDecidable t
    inferInstanceAs (DecidableEq (Bool ⊕ (Control f ⊕ Control t)))
instance (b : Block K) : DecidableEq (Control b) := controlDecidable b

def controlFinite : (b : Block K) → Fintype (Control b)
  | .skip => inferInstanceAs (Fintype Bool)
  | .atom p => inferInstanceAs (Fintype (Fin p.states))
  | .push _ _ => inferInstanceAs (Fintype Bool)
  | .seq a b =>
    letI := controlFinite a
    letI := controlFinite b
    inferInstanceAs (Fintype (Control a ⊕ Control b))
  | .branch _ e f t =>
    letI := controlFinite e
    letI := controlFinite f
    letI := controlFinite t
    inferInstanceAs (Fintype (Bool ⊕ (Control e ⊕ (Control f ⊕ Control t))))
  | .loop _ f t =>
    letI := controlFinite f
    letI := controlFinite t
    inferInstanceAs (Fintype (Bool ⊕ (Control f ⊕ Control t)))
instance (b : Block K) : Fintype (Control b) := controlFinite b

def entry : (b : Block K) → Control b
  | .skip => false
  | .atom p => p.start
  | .push _ _ => false
  | .seq a _ => .inl (entry a)
  | .branch _ _ _ _ => .inl false
  | .loop _ _ _ => .inl false

def finish : (b : Block K) → Control b
  | .skip => true
  | .atom p => p.exit
  | .push _ _ => true
  | .seq _ b => .inr (finish b)
  | .branch _ _ _ _ => .inl true
  | .loop _ _ _ => .inl true

def code : (b : Block K) → Control b → Instr K (Control b)
  | .atom p,q => p.instructions q
  | .skip,false => .jump true
  | .skip,true => .halt true
  | .push k b,false => .push k b true
  | .push _ _,true => .halt true
  | .seq a b,.inl q => if q=finish a then .jump (.inr (entry b)) else (code a q).rename id Sum.inl
  | .seq a b,.inr q => (code b q).rename id Sum.inr
  | .branch k e f t,.inl false => .pop k (.inr (.inl (entry e))) (.inr (.inr (.inl (entry f)))) (.inr (.inr (.inr (entry t))))
  | .branch _ _ _ _,.inl true => .halt true
  | .branch k e f t,.inr (.inl q) =>
    if q=finish e then .jump (.inl true) else (code e q).rename id (fun x => .inr (.inl x))
  | .branch k e f t,.inr (.inr (.inl q)) =>
    if q=finish f then .jump (.inl true) else (code f q).rename id (fun x => .inr (.inr (.inl x)))
  | .branch k e f t,.inr (.inr (.inr q)) =>
    if q=finish t then .jump (.inl true) else (code t q).rename id (fun x => .inr (.inr (.inr x)))
  | .loop k f t,.inl false => .pop k (.inl true) (.inr (.inl (entry f))) (.inr (.inr (entry t)))
  | .loop _ _ _,.inl true => .halt true
  | .loop k f t,.inr (.inl q) =>
    if q=finish f then .jump (.inl false) else (code f q).rename id (fun x => .inr (.inl x))
  | .loop k f t,.inr (.inr q) =>
    if q=finish t then .jump (.inl false) else (code t q).rename id (fun x => .inr (.inr x))

lemma code_finish (b : Block K) : code b (finish b)=.halt true := by
  induction b <;> simp_all [code,finish,Instr.rename,Atom.halted]

def program (b : Block K) (input output : K) : Program K (Control b) :=
  ⟨code b,entry b,input,output⟩

lemma code_noChoice (b : Block K) (q : Control b) (x y : Control b) : code b q≠.choice x y := by
  induction b with
  | skip => cases q <;> simp [code]
  | atom p => exact p.noChoice q x y
  | push k v => cases q <;> simp [code]
  | seq a b ha hb =>
    cases q with
    | inl q =>
      simp only [code]
      split
      · simp
      · cases he : code a q <;> simp [Instr.rename]
        exact False.elim (ha q _ _ he)
    | inr q =>
      simp only [code]
      cases he : code b q <;> simp [Instr.rename]
      exact False.elim (hb q _ _ he)
  | branch k e f t he hf ht =>
    rcases q with (v | (q | (q | q)))
    · cases v <;> simp [code]
    all_goals
      simp only [code]
      split
      · simp
      · first
        | cases hh : code e q <;> simp [Instr.rename]; exact False.elim (he q _ _ hh)
        | cases hh : code f q <;> simp [Instr.rename]; exact False.elim (hf q _ _ hh)
        | cases hh : code t q <;> simp [Instr.rename]; exact False.elim (ht q _ _ hh)
  | loop k f t hf ht =>
    rcases q with (v | (q | q))
    · cases v <;> simp [code]
    all_goals
      simp only [code]
      split
      · simp
      · first
        | cases hh : code f q <;> simp [Instr.rename]; exact False.elim (hf q _ _ hh)
        | cases hh : code t q <;> simp [Instr.rename]; exact False.elim (ht q _ _ hh)

lemma program_noChoice (b : Block K) (input output : K) : NoChoice (program b input output) := code_noChoice b

end BalancedAssortments.NPStack.Structured
