import BalancedAssortments.NPCNFStackChainSound

/-! The finite whole-formula loop around the proved OR-chain subroutine.
Catalogue validation and fresh-start preparation are separate preceding passes. -/
namespace BalancedAssortments.NPCNF.StackFormula
open NPStack NPStack.Macros
abbrev Register := StackChain.Register

inductive ConstantBlock | emptyClause | formulaEnd deriving DecidableEq,Fintype

def blockBits : ConstantBlock → List Bool
  | .emptyClause => [true,true,false,false]
  | .formulaEnd => [true,false,false]

inductive Main
  | readHeader | inspectHeader | checkHeaderEnd (clause : Bool)
  | readFirstSign | inspectFirstSign | checkFirstSignEnd (sign : Bool)
  | readFirstLabel (sign : Bool) | invoke (sign : Bool) | clearLeft
  | checkInputEnd
  | saveOutput (block : ConstantBlock) | saveOutputBit (block : ConstantBlock) (bit : Bool)
  | emitConstant (block : ConstantBlock) (pc : Fin 5)
  | restoreOutput (block : ConstantBlock) | restoreOutputBit (block : ConstantBlock) (bit : Bool)
  | accept | reject
  deriving DecidableEq,Fintype

inductive State | outer (q : Label Main) | chain (q : Label StackChain.State)
  deriving DecidableEq,Fintype

def nextConstant (i : Fin 5) : Fin 5 := ⟨min (i.val+1) 4,by omega⟩

def macroCode : Main → Macro Register Main
  | .readHeader => .taggedRead .input .scratchRead .tag .inspectHeader .reject
  | .inspectHeader => .pop .tag .reject (.checkHeaderEnd false) (.checkHeaderEnd true)
  | .checkHeaderEnd clause => .pop .tag (if clause then .readFirstSign else .checkInputEnd) .reject .reject
  | .readFirstSign => .taggedRead .input .scratchRead .tag .inspectFirstSign .reject
  | .inspectFirstSign => .pop .tag (.saveOutput .emptyClause) (.checkFirstSignEnd false) (.checkFirstSignEnd true)
  | .checkFirstSignEnd sign => .pop .tag (.readFirstLabel sign) .reject .reject
  | .readFirstLabel sign => .taggedRead .input .scratchRead .left (.invoke sign) .reject
  | .invoke _ => .halt false -- patched by code below to the finite chain entry
  | .clearLeft => .pop .left .readHeader .clearLeft .clearLeft
  | .checkInputEnd => .pop .input (.saveOutput .formulaEnd) .reject .reject
  | .saveOutput b => .pop .output (.emitConstant b 0) (.saveOutputBit b false) (.saveOutputBit b true)
  | .saveOutputBit b bit => .push .savedOutput bit (.saveOutput b)
  | .emitConstant b pc => match (blockBits b).reverse[pc.val]? with
    | none => .jump (.restoreOutput b)
    | some bit => .push .output bit (.emitConstant b (nextConstant pc))
  | .restoreOutput b => .pop .savedOutput (match b with | .emptyClause => .readHeader | .formulaEnd => .accept)
      (.restoreOutputBit b false) (.restoreOutputBit b true)
  | .restoreOutputBit b bit => .push .output bit (.restoreOutput b)
  | .accept => .halt true
  | .reject => .halt false

def code : State → Instr Register State
  | .outer (.main (.invoke sign)) => .jump (.chain (.main (.readSign sign)))
  | .outer q => (Macros.code macroCode q).rename id State.outer
  | .chain (.main .accept) => .jump (.outer (.main .clearLeft))
  | .chain q => ((StackChain.program false).code q).rename id State.chain

def program : NPStack.Program Register State :=
  ⟨code,.outer (.main .readHeader),.input,.output⟩

def cfg (q : Main) (s : Register → List Bool) : Config Register State := ⟨.outer (.main q),s⟩

lemma chain_extends : CodeExtends (StackChain.program false) program id State.chain := by
  intro q h
  cases q with
  | main q => cases q <;> first | exact False.elim (h true rfl) | rfl
  | «local» q st => rfl

lemma outer_extends : CodeExtends (Macros.compile macroCode .readHeader StackChain.Register.input StackChain.Register.output)
    program id State.outer := by
  intro q h
  cases q with
  | main q => cases q <;> first | exact False.elim (h false rfl) | rfl
  | «local» q st => rfl

end BalancedAssortments.NPCNF.StackFormula
