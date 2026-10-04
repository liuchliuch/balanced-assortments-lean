import BalancedAssortments.NPCNFStackTransformSound
import BalancedAssortments.NPCNFStackValidateProgram
import BalancedAssortments.NPStackFieldsCorrect

/-! Concrete raw-bit reduction control graph: parse framing, validate/prepare
CNF, transfer the three prepared registers, transform, serialize. Every rejecting
subroutine exit is routed to a fixed valid unsatisfiable three-CNF output. -/
namespace BalancedAssortments.NPCNF.StackReduction
open NPStack NPStack.Macros Encoding
abbrev Register := NPStackFields.Stack ⊕ (StackValidate.Register ⊕ StackTransform.Register)

def parserMap : NPStackFields.Stack → Register := Sum.inl
def validatorMap : StackValidate.Register → Register := fun k=>.inr (.inl k)
def transformMap : StackTransform.Register → Register := fun k=>.inr (.inr k)
def output : Register := transformMap (.inl .input)
def scratch : Register := transformMap (.inl .scratchCopy)

inductive Transfer | parsed | formula | fresh | catalogue deriving DecidableEq,Fintype

def transferSource : Transfer → Register
  | .parsed => parserMap NPStackFields.output
  | .formula => validatorMap StackValidate.original
  | .fresh => validatorMap StackValidate.fresh
  | .catalogue => validatorMap StackValidate.catalogue

def transferTarget : Transfer → Register
  | .parsed => validatorMap StackValidate.input
  | .formula => transformMap (.inl .input)
  | .fresh => transformMap (.inl .fresh)
  | .catalogue => transformMap (.inr ())

def transferMap (t : Transfer) : CopyStack → Register := copyMap (transferSource t) scratch (transferTarget t)

def failureBits : List Bool := encode unsatRaw

inductive State
  | parse (q : NPStackFields.State)
  | validate (q : StackValidate.State)
  | transform (q : StackTransform.State)
  | transfer (t : Transfer) (q : CopyState)
  | failureClear
  | failureEmit (pc : Fin (failureBits.length+1))
  | accept
  deriving DecidableEq,Fintype

def afterTransfer : Transfer → State
  | .parsed => .validate StackValidate.program.start
  | .formula => .transfer .fresh .readSource
  | .fresh => .transfer .catalogue .readSource
  | .catalogue => .transform StackTransform.program.start

def nextFailure (pc : Fin (failureBits.length+1)) : Fin (failureBits.length+1) :=
  ⟨min (pc.val+1) failureBits.length,by omega⟩

def code : State → Instr Register State
  | .parse q => returnCode parserMap State.parse (.transfer .parsed .readSource) .failureClear (NPStackFields.program.code q)
  | .validate q => returnCode validatorMap State.validate (.transfer .formula .readSource) .failureClear (StackValidate.program.code q)
  | .transform q => returnCode transformMap State.transform .accept .failureClear (StackTransform.program.code q)
  | .transfer t q => returnCode (transferMap t) (.transfer t) (afterTransfer t) .failureClear (copyProgram.code q)
  | .failureClear => .pop output (.failureEmit 0) .failureClear .failureClear
  | .failureEmit pc => match failureBits.reverse[pc.val]? with
    | none => .jump .accept
    | some b => .push output b (.failureEmit (nextFailure pc))
  | .accept => .halt true

def program : Program Register State := ⟨code,.parse NPStackFields.program.start,parserMap NPStackFields.input,output⟩

lemma parser_extends : CodeExtends NPStackFields.program program parserMap State.parse := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma validator_extends : CodeExtends StackValidate.program program validatorMap State.validate := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma transform_extends : CodeExtends StackTransform.program program transformMap State.transform := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma transfer_extends (t : Transfer) : CodeExtends copyProgram program (transferMap t) (.transfer t) := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h

lemma parser_injective : Function.Injective parserMap := Sum.inl_injective
lemma validator_injective : Function.Injective validatorMap := fun _ _ h=>Sum.inl_injective (Sum.inr_injective h)
lemma transform_injective : Function.Injective transformMap := fun _ _ h=>Sum.inr_injective (Sum.inr_injective h)
lemma transfer_injective (t : Transfer) : Function.Injective (transferMap t) := by
  intro a b h;cases t <;> cases a <;> cases b <;>
    simp_all [transferMap,copyMap,transferSource,transferTarget,scratch,parserMap,validatorMap,transformMap,
      NPStackFields.output,StackValidate.input,StackValidate.original,StackValidate.fresh,StackValidate.catalogue]

end BalancedAssortments.NPCNF.StackReduction
