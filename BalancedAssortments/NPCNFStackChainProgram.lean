import BalancedAssortments.NPCNFStackGate
import BalancedAssortments.NPStackMacros

/-! Primitive-expanded finite bytecode for the OR-chain body. It operates on
an already validated clause suffix in tagged-field form; the full raw reduction
must separately validate the original catalogue and formula grammar. The input
suffix is consumed through its empty sign-field terminator. -/
namespace BalancedAssortments.NPCNF.StackChain
open NPStack NPStack.Macros StackTemplate StackGate

inductive Register
  | input | left | right | fresh | nextFresh | one | output | savedOutput
  | allocated | scratchRead | scratchCopy | scratchAdd | temporary | tag
  deriving DecidableEq,Fintype

inductive Block | gate (leftSign rightSign : Bool) | unit (sign : Bool)
  deriving DecidableEq,Fintype

def blockSpecs : Block → List (FieldSpec StackGate.Register)
  | .gate sa sb => gateSpecs sa sb
  | .unit sa => [.constant [true],.constant [sa],.reg .left,.constant []]

def blockJobs (b : Block) := fieldsJobs (blockSpecs b)

def labelRegister : StackGate.Register → Register
  | .left => .left | .right => .right | .fresh => .fresh

inductive State
  | readSign (leftSign : Bool)
  | inspectSign (leftSign : Bool)
  | checkSignEnd (leftSign rightSign : Bool)
  | readRight (leftSign rightSign : Bool)
  | saveOutput (block : Block)
  | saveOutputBit (block : Block) (bit : Bool)
  | emit (block : Block) (pc : Fin 41)
  | emitField (block : Block) (pc : Fin 41)
  | restoreOutput (block : Block)
  | restoreOutputBit (block : Block) (bit : Bool)
  | clearLeft | copyFreshLeft | copyFreshCatalog | emitFreshCatalog
  | clearRight | makeOne | increment | installFresh | clearNextFresh
  | accept | reject
  deriving DecidableEq,Fintype

def nextJob (i : Fin 41) : Fin 41 := ⟨min (i.val+1) 40,by omega⟩

def macroCode : State → Macro Register State
  | .readSign sa => .taggedRead .input .scratchRead .tag (.inspectSign sa) .reject
  | .inspectSign sa => .pop .tag (.saveOutput (.unit sa)) (.checkSignEnd sa false) (.checkSignEnd sa true)
  | .checkSignEnd sa sb => .pop .tag (.readRight sa sb) .reject .reject
  | .readRight sa sb => .taggedRead .input .scratchRead .right (.saveOutput (.gate sa sb)) .reject
  | .saveOutput b => .pop .output (.emit b 0) (.saveOutputBit b false) (.saveOutputBit b true)
  | .saveOutputBit b bit => .push .savedOutput bit (.saveOutput b)
  | .emit block pc => match (blockJobs block)[pc.val]? with
    | none => .jump (.restoreOutput block)
    | some (.bit b) => .push .output b (.emit block (nextJob pc))
    | some (.field k) => .copy (labelRegister k) .scratchCopy .temporary (.emitField block pc)
  | .emitField block pc => .taggedEmit .temporary .scratchRead .output (.emit block (nextJob pc))
  | .restoreOutput b => .pop .savedOutput
      (match b with | .unit _ => .accept | .gate _ _ => .clearLeft)
      (.restoreOutputBit b false) (.restoreOutputBit b true)
  | .restoreOutputBit b bit => .push .output bit (.restoreOutput b)
  | .clearLeft => .pop .left .copyFreshLeft .clearLeft .clearLeft
  | .copyFreshLeft => .copy .fresh .scratchCopy .left .copyFreshCatalog
  | .copyFreshCatalog => .copy .fresh .scratchCopy .temporary .emitFreshCatalog
  | .emitFreshCatalog => .taggedEmit .temporary .scratchRead .allocated .clearRight
  | .clearRight => .pop .right .makeOne .clearRight .clearRight
  | .makeOne => .push .one true .increment
  | .increment => .add .fresh .one .scratchAdd .nextFresh false .installFresh
  | .installFresh => .copy .nextFresh .scratchCopy .fresh .clearNextFresh
  | .clearNextFresh => .pop .nextFresh (.readSign true) .clearNextFresh .clearNextFresh
  | .accept => .halt true
  | .reject => .halt false

/-- An actual finite Boolean-stack program. There is no unbounded label,
formula, arithmetic, parser or output callback in its instruction set. -/
def program (leftSign : Bool) : NPStack.Program Register (Label State) :=
  Macros.compile macroCode (.readSign leftSign) .input .output

lemma blockJobs_length (block : Block) : (blockJobs block).length≤40 := by
  cases block with
  | gate sa sb => simp [blockJobs,blockSpecs,gate_job_count]
  | unit sa => simp [blockJobs,blockSpecs,fieldsJobs,fieldJobs,NPStackFields.tagBits]

lemma job_advances (block : Block) (pc : Fin 41) (job : Job StackGate.Register)
    (h : (blockJobs block)[pc.val]?=some job) : (nextJob pc).val=pc.val+1 := by
  obtain ⟨hp,_⟩ := List.getElem?_eq_some_iff.mp h
  have hl := blockJobs_length block
  dsimp only [nextJob]
  omega

end BalancedAssortments.NPCNF.StackChain
