import BalancedAssortments.NPStackSourceVerifierStore
import BalancedAssortments.NPStackClearRows
import BalancedAssortments.NPStackFieldData

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier

abbrev FalseGuard := VerifierControl.State VerifierCommands.Control (VerifierCommands.rowCommand false)
abbrev TrueGuard := VerifierControl.State VerifierCommands.Control (VerifierCommands.rowCommand true)
inductive EmitPart | negative | positive | mask deriving DecidableEq, Fintype
inductive InnerState
  | mask (q : NPStackMask.State)
  | choose
  | guardFalse (q : FalseGuard)
  | guardTrue (q : TrueGuard)
  | emit (active : Bool) (part : EmitPart) (q : NPStackFieldData.EmitState)
  | pushMask (active : Bool)
  | done | reject
  deriving DecidableEq, Fintype

def guardLabel : (active : Bool)→VerifierControl.State VerifierCommands.Control (VerifierCommands.rowCommand active)→InnerState
  | false,q => .guardFalse q | true,q => .guardTrue q

def emitSource : EmitPart→BodyStack
  | .negative => .inl 8 | .positive => .inl 7 | .mask => .inr (.inr .maskPayload)
def emitMap (part : EmitPart) : NPStackFieldData.Stack→BodyStack
  | .input => emitSource part
  | .scratch => .inr (.inr .emitScratch)
  | .output => .inr (.inr .balance)
def emitNext (active : Bool) : EmitPart→InnerState
  | .negative => .emit active .positive .reverse
  | .positive => .pushMask active
  | .mask => .done

def guardReturn {A : Type} (f : A→InnerState) (active : Bool)
    (i : Instr VerifierControl.Stack A) : Instr BodyStack InnerState :=
  match i with
  | .halt true => .jump (.emit active .negative .reverse)
  | .halt false => .halt false
  | instr => instr.rename arithmeticMap f

/-- The literal first-pass row body: parse padded mask, run the certified
arithmetic guards/updates, save only mask and numerator fields for balance. -/
def innerProgram : Program BodyStack InnerState where
  code
    | .mask .accept => .jump .choose
    | .mask .reject => .halt false
    | .mask q => (NPStackMask.program.code q).rename maskMap InnerState.mask
    | .choose => .pop (.inr (.inr .maskFlag)) .reject
        (.guardFalse (VerifierControl.start VerifierCommands.comparisons (VerifierCommands.rowCommand false)))
        (.guardTrue (VerifierControl.start VerifierCommands.comparisons (VerifierCommands.rowCommand true)))
    | .guardFalse q => guardReturn InnerState.guardFalse false
        ((VerifierCommands.program (VerifierCommands.rowCommand false)).code q)
    | .guardTrue q => guardReturn InnerState.guardTrue true
        ((VerifierCommands.program (VerifierCommands.rowCommand true)).code q)
    | .emit active part .accept => .jump (emitNext active part)
    | .emit active part q => (NPStackFieldData.emitProgram.code q).rename (emitMap part) (.emit active part)
    | .pushMask active => .push (.inr (.inr .maskPayload)) active (.emit active .mask .reverse)
    | .done => .halt true
    | .reject => .halt false
  start := .mask .head
  inputStack := .inl 6
  outputStack := .inr (.inr .balance)

/-- Every successful inner return passes through nine real pop loops. -/
def bodyProgram := ClearRows.finishProgram innerProgram ClearRows.rowKeys

theorem body_clearsRows : NPStackSourcePairing.ClearsRows bodyProgram := ClearRows.finish_clearsRows innerProgram

lemma mask_extends : CodeExtends NPStackMask.program innerProgram maskMap InnerState.mask := by
  intro q h;cases q <;> simp_all [innerProgram,NPStackMask.program]
lemma emitMap_injective (part : EmitPart) : Function.Injective (emitMap part) := by
  intro a b h;cases part <;> cases a <;> cases b <;> simp_all [emitMap,emitSource]
lemma emit_extends (active : Bool) (part : EmitPart) :
    CodeExtends NPStackFieldData.emitProgram innerProgram (emitMap part) (.emit active part) := by
  intro q h;cases q <;> simp_all [innerProgram,NPStackFieldData.emitProgram]

lemma guard_extends (active : Bool) :
    CodeExtends (VerifierCommands.program (VerifierCommands.rowCommand active)) innerProgram
      arithmeticMap (guardLabel active) := by
  cases active <;> intro q h <;> dsimp only [innerProgram,guardLabel,guardReturn]
  all_goals
    cases he : (VerifierCommands.program _).code q with
    | halt b => exact (h b he).elim
    | jump q => rfl
    | push k b q => rfl
    | pop k e f t => rfl
    | choice l r => rfl

private lemma guardReturn_noChoice {A : Type} (f : A→InnerState) (active : Bool)
    (i : Instr VerifierControl.Stack A) (h : ∀ a b,i≠.choice a b) (x y : InnerState) :
    guardReturn f active i≠.choice x y := by
  cases i <;> simp_all [guardReturn,Instr.rename]
  rename_i b;cases b <;> simp

theorem inner_noChoice : NoChoice innerProgram := by
  intro q x y
  cases q with
  | mask q => cases q <;> simp [innerProgram,NPStackMask.program,Instr.rename]
  | choose => simp [innerProgram]
  | guardFalse q => exact guardReturn_noChoice _ _ _ (VerifierCommands.command_noChoice _ q) x y
  | guardTrue q => exact guardReturn_noChoice _ _ _ (VerifierCommands.command_noChoice _ q) x y
  | emit active part q => cases q <;> simp [innerProgram,NPStackFieldData.emitProgram,Instr.rename]
  | pushMask active => simp [innerProgram]
  | done | reject => simp [innerProgram]

end BalancedAssortments.NPStack.SourceVerifier
