import BalancedAssortments.NPSATStackPrepareCorrect
import BalancedAssortments.NPSATStackGadgetComplete

set_option synthInstance.maxSize 10000
set_option maxRecDepth 4096
noncomputable section
namespace BalancedAssortments.NPSATStackReduction
open NPStack NPStack.Macros
abbrev Reg := NPSATStackPrepare.Register ⊕ NPSATStackGadget.Reg
instance : DecidableEq Reg := inferInstanceAs (DecidableEq (NPSATStackPrepare.Register ⊕ NPSATStackGadget.Reg))
instance : Fintype Reg := inferInstanceAs (Fintype (NPSATStackPrepare.Register ⊕ NPSATStackGadget.Reg))

def prepareMap : NPSATStackPrepare.Register → Reg := Sum.inl
def gadgetMap : NPSATStackGadget.Reg → Reg := Sum.inr
def output : Reg := gadgetMap NPSATStackGadget.output
def scratch : Reg := gadgetMap NPSATStackGadget.scratch

inductive Transfer where | catalog | formula | fresh deriving DecidableEq,Fintype

def transferSource : Transfer → Reg
  | .catalog => prepareMap NPSATStackPrepare.catalog
  | .formula => prepareMap NPSATStackPrepare.original
  | .fresh => prepareMap (NPSATStackPrepare.validatorMap NPCNF.StackValidate.fresh)
def transferTarget : Transfer → Reg
  | .catalog => gadgetMap NPSATStackGadget.catalog
  | .formula => gadgetMap NPSATStackGadget.formula
  | .fresh => gadgetMap NPSATStackGadget.fresh

def transferMap (t : Transfer) : CopyStack → Reg := copyMap (transferSource t) scratch (transferTarget t)

inductive State where
  | prepare (q : NPSATStackPrepare.State)
  | transfer (t : Transfer) (q : CopyState)
  | construct (q : Structured.Control NPSATStackGadget.complete)
  | accept | reject
  deriving DecidableEq,Fintype

def afterTransfer : Transfer → State
  | .catalog => .transfer .formula .readSource
  | .formula => .transfer .fresh .readSource
  | .fresh => .construct (Structured.entry NPSATStackGadget.complete)

def code : State → Instr Reg State
  | .prepare q => returnCode prepareMap State.prepare (.transfer .catalog .readSource) .reject (NPSATStackPrepare.program.code q)
  | .transfer t q => returnCode (transferMap t) (.transfer t) (afterTransfer t) .reject (copyProgram.code q)
  | .construct q => returnCode gadgetMap State.construct .accept .reject (NPSATStackGadget.program.code q)
  | .accept => .halt true
  | .reject => .halt false

def program : Program Reg State := ⟨code,.prepare NPSATStackPrepare.program.start,prepareMap NPSATStackPrepare.program.inputStack,output⟩

lemma prepare_extends : CodeExtends NPSATStackPrepare.program program prepareMap State.prepare := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma gadget_extends : CodeExtends NPSATStackGadget.program program gadgetMap State.construct := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma transfer_extends (t : Transfer) : CodeExtends copyProgram program (transferMap t) (.transfer t) := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma transfer_injective (t : Transfer) : Function.Injective (transferMap t) := by
  intro a b h;cases t <;> cases a <;> cases b <;>
    simp_all [transferMap,copyMap,transferSource,transferTarget,scratch,prepareMap,gadgetMap,
      NPSATStackGadget.catalog,NPSATStackGadget.formula,NPSATStackGadget.fresh,NPSATStackGadget.scratch]
lemma noChoice : NoChoice program := by
  intro q a b
  cases q with
  | prepare q => exact return_not_choice _ _ _ _ _ (NPSATStackPrepare.noChoice q) _ _
  | construct q => exact return_not_choice _ _ _ _ _ (NPSATStackGadget.noChoice q) _ _
  | transfer t q => exact return_not_choice _ _ _ _ _ (copy_noChoice q) _ _
  | accept => simp [program,code]
  | reject => simp [program,code]

def combined (p : NPSATStackPrepare.Register → List Bool) (g : NPSATStackGadget.Reg → List Bool) : Reg → List Bool
  | .inl k => p k | .inr k => g k

@[simp] lemma combined_update_right (p : NPSATStackPrepare.Register → List Bool) (g : NPSATStackGadget.Reg → List Bool)
    (k : NPSATStackGadget.Reg) (v : List Bool) :
    Function.update (combined p g) (.inr k) v=combined p (Function.update g k v) := by
  funext j;rcases j with j|j <;> simp [combined,Function.update]

lemma initial_combined (bits : List Bool) : initial program bits=
    ⟨.prepare NPSATStackPrepare.program.start,combined (initial NPSATStackPrepare.program bits).stk (fun _=>[])⟩ := by
  unfold initial
  congr 1
  funext k;rcases k with k|k <;> simp [program,prepareMap,combined,Function.update]

lemma transfer_run (t : Transfer) (s : Reg → List Bool) (hs : s scratch=[])
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
    (by constructor;rfl;intro k;cases k <;> simp [transferMap,copyMap,copyConfig,copyStacks,hs,hne,hsw,Function.update])
    (by intro k hk;exact Function.update_of_ne (Ne.symm (hk .target)) _ _)
  have hreturn : Step program
      ⟨.transfer t .done,Function.update s (transferTarget t) (s (transferSource t))⟩
      ⟨afterTransfer t,Function.update s (transferTarget t) (s (transferSource t))⟩ := by
    simp [Step,successors,program,code,copyProgram,returnCode]
  convert hh.trans (Run.one hreturn) using 1 <;> omega

end BalancedAssortments.NPSATStackReduction
