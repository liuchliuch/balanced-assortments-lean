import BalancedAssortments.NPPolynomialPrograms
import BalancedAssortments.NPStackEmbedding
import BalancedAssortments.NPStackReverse

/-! Composition of actual finite Boolean-stack transducers. Output transfer
is two real finite reversal routines; no function-call or copying oracle is
introduced into the operational instruction set. -/
namespace BalancedAssortments.NPStack.Composition
open NPStack
variable {K₁ Q₁ K₂ Q₂ : Type*}

abbrev Stack (K₁ K₂ : Type*) := Sum K₁ (Sum K₂ Unit)
inductive Label (Q₁ Q₂ : Type*)
  | first (q : Q₁) | transfer (stage : Bool) (q : ReverseState) | second (q : Q₂)
  deriving DecidableEq, Fintype

def firstStack : K₁ → Stack K₁ K₂ := Sum.inl
def secondStack (k : K₂) : Stack K₁ K₂ := .inr (.inl k)
def scratch : Stack K₁ K₂ := .inr (.inr ())

def transferStack (P : Program K₁ Q₁) (R : Program K₂ Q₂) (stage : Bool) : Bool → Stack K₁ K₂ :=
  if stage then fun b => if b then secondStack R.inputStack else scratch
  else fun b => if b then scratch else firstStack P.outputStack

lemma transferStack_injective (P : Program K₁ Q₁) (R : Program K₂ Q₂) (stage : Bool) :
    Function.Injective (transferStack P R stage) := by
  intro a b h
  cases stage <;> cases a <;> cases b <;> simp_all [transferStack,firstStack,secondStack,scratch]

def program (P : Program K₁ Q₁) (R : Program K₂ Q₂) : Program (Stack K₁ K₂) (Label Q₁ Q₂) where
  code
    | .first q => match P.code q with
      | .halt true => .jump (.transfer false .read)
      | i => i.rename firstStack Label.first
    | .transfer stage .done => if stage then .jump (.second R.start) else .jump (.transfer true .read)
    | .transfer stage q => (reverseProgram.code q).rename (transferStack P R stage) (.transfer stage)
    | .second q => (R.code q).rename secondStack Label.second
  start := .first P.start
  inputStack := firstStack P.inputStack
  outputStack := secondStack R.outputStack

lemma first_extends (P : Program K₁ Q₁) (R : Program K₂ Q₂) :
    CodeExtends P (program P R) firstStack Label.first := by
  intro q hn
  cases hp : P.code q <;> simp [program,hp]
  rename_i b
  exact False.elim (hn b hp)

lemma second_extends (P : Program K₁ Q₁) (R : Program K₂ Q₂) :
    CodeExtends R (program P R) secondStack Label.second := by
  intro q _
  rfl

lemma transfer_extends (P : Program K₁ Q₁) (R : Program K₂ Q₂) (stage : Bool) :
    CodeExtends reverseProgram (program P R) (transferStack P R stage) (.transfer stage) := by
  intro q hn
  cases q <;> simp [program,reverseProgram]
  exact False.elim (hn true rfl)

lemma noChoice {P : Program K₁ Q₁} {R : Program K₂ Q₂} (hp : NoChoice P) (hr : NoChoice R) :
    NoChoice (program P R) := by
  intro q a b
  cases q with
  | first q =>
    cases hq : P.code q <;> simp [program,hq,Instr.rename]
    · rename_i c
      cases c <;> simp [Instr.rename]
    · rename_i x y
      exact False.elim (hp q x y hq)
  | second q =>
    cases hq : R.code q <;> simp [program,hq,Instr.rename]
    rename_i x y
    exact False.elim (hr q x y hq)
  | transfer stage q => cases stage <;> cases q <;> simp [program,reverseProgram,Instr.rename]

end BalancedAssortments.NPStack.Composition
