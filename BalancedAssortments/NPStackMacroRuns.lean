import BalancedAssortments.NPStackMacros
import BalancedAssortments.NPStackCompareNormalizeSound
import BalancedAssortments.NPStackFieldDataCorrect

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace BalancedAssortments.NPStack.Macros
open NPStack

variable {K Q : Type*} [DecidableEq K]

lemma rename_not_choice {A B C D : Type*} (instr : Instr A B) (fk : A → C) (fq : B → D)
    (hn : ∀ a b,instr≠.choice a b) (a b : D) : instr.rename fk fq≠.choice a b := by
  cases instr <;> simp [Instr.rename]
  exact False.elim (hn _ _ rfl)

@[simp] lemma rename_multiply_not_choice (fk : MulStack → K) (fq : MulState → Q) (st : MulState) (a b : Q) :
    (multiplyProgram.code st).rename fk fq≠.choice a b :=
  rename_not_choice _ _ _ (multiply_noChoice st) _ _
@[simp] lemma rename_signedCompare_not_choice (fk : SignedCompareStack → K) (fq : SignedCompareState → Q)
    (st : SignedCompareState) (a b : Q) : (signedCompareProgram.code st).rename fk fq≠.choice a b :=
  rename_not_choice _ _ _ (signedCompare_noChoice st) _ _

@[simp] lemma rename_signedAdd_not_choice (fk : SignedAddStack → K) (fq : SignedAddState → Q)
    (st : SignedAddState) (a b : Q) : (signedAddProgram.code st).rename fk fq≠.choice a b :=
  rename_not_choice _ _ _ (signedAdd_noChoice st) _ _
@[simp] lemma rename_signedMultiply_not_choice (fk : SignedMulStack → K) (fq : SignedMulState → Q)
    (st : SignedMulState) (a b : Q) : (signedMultiplyProgram.code st).rename fk fq≠.choice a b :=
  rename_not_choice _ _ _ (signedMultiply_noChoice st) _ _

lemma return_not_choice {A B C D : Type*} (instr : Instr A B) (fk : A → C) (fq : B → D)
    (yes no : D) (hn : ∀ a b,instr≠.choice a b) (a b : D) : returnCode fk fq yes no instr≠.choice a b := by
  cases instr <;> simp [returnCode,Instr.rename]
  exact False.elim (hn _ _ rfl)

lemma compile_noChoice (m : Q → Macro K Q) (start : Q) (input output : K) :
    NoChoice (compile m start input output) := by
  intro state a b
  cases state with
  | main q => cases hm : m q <;> simp [compile,code,hm]
  | «local» q st =>
    cases st with
    | copy st =>
      cases hm : m q <;> simp [compile,code,hm]
      exact return_not_choice _ _ _ _ _ (copy_noChoice st) _ _
    | add st =>
      cases hm : m q <;> simp [compile,code,hm]
      exact return_not_choice _ _ _ _ _ (add_noChoice st) _ _
    | normalize st =>
      cases hm : m q <;> simp [compile,code,hm]
      exact return_not_choice _ _ _ _ _ (normalize_noChoice st) _ _
    | read st =>
      cases hm : m q <;> simp [compile,code,hm]
      exact return_not_choice _ _ _ _ _ (NPStackField.program_noChoice st) _ _
    | encode st =>
      cases hm : m q <;> simp [compile,code,hm]
      apply return_not_choice
      intro c d
      cases st <;> simp [NPStackFieldEncode.program]
    | taggedRead st =>
      cases hm : m q <;> simp [compile,code,hm]
      apply return_not_choice
      intro c d
      cases st <;> simp [NPStackFieldData.readProgram]
    | taggedEmit st =>
      cases hm : m q <;> simp [compile,code,hm]
      apply return_not_choice
      intro c d
      cases st <;> simp [NPStackFieldData.emitProgram]
    | compare st =>
      cases hm : m q <;> simp [compile,code,hm]
      exact return_not_choice _ _ _ _ _ (compare_noChoice st) _ _
    | multiply st =>
      cases hm : m q <;> simp [compile,code,hm]
      exact return_not_choice _ _ _ _ _ (multiply_noChoice st) _ _
    | signedCompare st =>
      cases hm : m q <;> simp [compile,code,hm]
      exact return_not_choice _ _ _ _ _ (signedCompare_noChoice st) _ _
    | signedAdd st =>
      cases hm : m q <;> simp [compile,code,hm]
      exact return_not_choice _ _ _ _ _ (signedAdd_noChoice st) _ _
    | signedMultiply st =>
      cases hm : m q <;> simp [compile,code,hm]
      exact return_not_choice _ _ _ _ _ (signedMultiply_noChoice st) _ _

/-- Exact whole-call rule: a real entry jump, the expanded primitive run, and a
real return jump. Data/frame premises are the usual subroutine pre/postconditions. -/
theorem call_run {A B : Type*} [DecidableEq A] {P : Program A B}
    {R : Program K Q} (fk : A → K) (fq : B → Q) (hinj : Function.Injective fk)
    (hcode : CodeExtends P R fk fq) {t : ℕ} {c d : Config A B}
    (hr : Run P t c d) (entry exit : Q) (before after : K → List Bool)
    (hentry : R.code entry=.jump (fq c.pc)) (hexit : R.code (fq d.pc)=.jump exit)
    (hbefore : ∀ k,before (fk k)=c.stk k) (hafter : ∀ k,after (fk k)=d.stk k)
    (hframe : ∀ k,(∀ old,fk old≠k) → after k=before k) :
    Run R (t+2) ⟨entry,before⟩ ⟨exit,after⟩ := by
  have hsub := hr.relocate_exact fk fq hinj hcode (c' := ⟨fq c.pc,before⟩) (d' := ⟨fq d.pc,after⟩)
    ⟨rfl,hbefore⟩ ⟨rfl,hafter⟩ hframe
  have h1 : Step R ⟨entry,before⟩ ⟨fq c.pc,before⟩ := by simp [Step,successors,hentry]
  have h2 : Step R ⟨fq d.pc,after⟩ ⟨exit,after⟩ := by simp [Step,successors,hexit]
  convert Run.succ h1 (hsub.trans (Run.one h2)) using 1 <;> omega

end BalancedAssortments.NPStack.Macros
