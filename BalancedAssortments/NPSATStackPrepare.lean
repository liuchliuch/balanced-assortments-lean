import BalancedAssortments.NPSATStackThreeCheck
import BalancedAssortments.NPCNFStackValidateTotal
import BalancedAssortments.NPCNFStackValidateBounds
import BalancedAssortments.NPStackFieldsCorrect

namespace BalancedAssortments.NPSATStackPrepare
open NPStack NPStack.Macros NPCNF.Encoding
abbrev Register := NPStackFields.Stack ⊕ (NPCNF.StackValidate.Register ⊕ Bool)

def parserMap : NPStackFields.Stack → Register := Sum.inl
def validatorMap : NPCNF.StackValidate.Register → Register := fun k=>.inr (.inl k)
def checkMap : Unit → Register := fun _=>.inr (.inr false)
def scratch : Register := .inr (.inr true)

def original : Register := validatorMap NPCNF.StackValidate.original
def catalog : Register := validatorMap NPCNF.StackValidate.catalogue

inductive Transfer where | parsed | formula deriving DecidableEq,Fintype

def transferSource : Transfer → Register
  | .parsed => parserMap NPStackFields.output
  | .formula => original

def transferTarget : Transfer → Register
  | .parsed => validatorMap NPCNF.StackValidate.input
  | .formula => checkMap ()

def transferMap (t : Transfer) : CopyStack → Register := copyMap (transferSource t) scratch (transferTarget t)

inductive State where
  | parse (q : NPStackFields.State)
  | validate (q : NPCNF.StackValidate.State)
  | check (q : NPSATStackThreeCheck.State)
  | transfer (t : Transfer) (q : CopyState)
  | accept | reject
  deriving DecidableEq,Fintype

def afterTransfer : Transfer → State
  | .parsed => .validate NPCNF.StackValidate.program.start
  | .formula => .check .formulaTag

def code : State → Instr Register State
  | .parse q => returnCode parserMap State.parse (.transfer .parsed .readSource) .reject (NPStackFields.program.code q)
  | .validate q => returnCode validatorMap State.validate (.transfer .formula .readSource) .reject (NPCNF.StackValidate.program.code q)
  | .check q => returnCode checkMap State.check .accept .reject (NPSATStackThreeCheck.program.code q)
  | .transfer t q => returnCode (transferMap t) (.transfer t) (afterTransfer t) .reject (copyProgram.code q)
  | .accept => .halt true
  | .reject => .halt false

def program : Program Register State := ⟨code,.parse .probe,parserMap NPStackFields.input,original⟩

lemma parser_extends : CodeExtends NPStackFields.program program parserMap State.parse := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma validator_extends : CodeExtends NPCNF.StackValidate.program program validatorMap State.validate := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma check_extends : CodeExtends NPSATStackThreeCheck.program program checkMap State.check := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma transfer_extends (t : Transfer) : CodeExtends copyProgram program (transferMap t) (.transfer t) := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma parser_injective : Function.Injective parserMap := Sum.inl_injective
lemma validator_injective : Function.Injective validatorMap := fun _ _ h=>Sum.inl_injective (Sum.inr_injective h)
lemma check_injective : Function.Injective checkMap := by intro a b h;cases a;cases b;rfl
lemma transfer_injective (t : Transfer) : Function.Injective (transferMap t) := by
  intro a b h;cases t <;> cases a <;> cases b <;>
    simp_all [transferMap,copyMap,transferSource,transferTarget,scratch,parserMap,validatorMap,checkMap,original,
      NPStackFields.output,NPCNF.StackValidate.input,NPCNF.StackValidate.original]

lemma noChoice : NoChoice program := by
  intro q a b
  cases q with
  | parse q => exact return_not_choice _ _ _ _ _ (NPStackFields.program_noChoice q) _ _
  | validate q => exact return_not_choice _ _ _ _ _ (NPCNF.StackValidate.program_noChoice q) _ _
  | check q => exact return_not_choice _ _ _ _ _ (NPSATStackThreeCheck.noChoice q) _ _
  | transfer t q => exact return_not_choice _ _ _ _ _ (copy_noChoice q) _ _
  | accept => simp [program,code]
  | reject => simp [program,code]

def combined (p : NPStackFields.Stack → List Bool) (v : NPCNF.StackValidate.Register → List Bool)
    (check work : List Bool) : Register → List Bool
  | .inl k => p k | .inr (.inl k) => v k | .inr (.inr false) => check | .inr (.inr true) => work

lemma transfer_run (t : Transfer) (s : Register → List Bool) (hs : s scratch=[])
    (ht : s (transferTarget t)=[]) :
    Run program (5*(s (transferSource t)).length+3) ⟨.transfer t .readSource,s⟩
      ⟨afterTransfer t,Function.update s (transferTarget t) (s (transferSource t))⟩ := by
  have hr := copy_run (s (transferSource t)) []
  have hne : transferSource t≠transferTarget t := by cases t <;> decide
  have hsw : scratch≠transferTarget t := by cases t <;> decide
  have hh := hr.relocate_exact (transferMap t) (State.transfer t) (transfer_injective t) (transfer_extends t)
    (c' := ⟨.transfer t .readSource,s⟩)
    (d' := ⟨.transfer t .done,Function.update s (transferTarget t) (s (transferSource t))⟩)
    (by constructor;rfl;intro k;cases k <;> simp [transferMap,copyMap,copyConfig,copyStacks,hs,ht])
    (by constructor;rfl;intro k;cases k <;> simp [transferMap,copyMap,copyConfig,copyStacks,hs,ht,hne,hsw,Function.update])
    (by intro k hk;exact Function.update_of_ne (Ne.symm (hk .target)) _ _)
  have hreturn : Step program
      ⟨.transfer t .done,Function.update s (transferTarget t) (s (transferSource t))⟩
      ⟨afterTransfer t,Function.update s (transferTarget t) (s (transferSource t))⟩ := by
    simp [Step,successors,program,code,copyProgram,returnCode]
  convert hh.trans (Run.one hreturn) using 1 <;> omega

end BalancedAssortments.NPSATStackPrepare
