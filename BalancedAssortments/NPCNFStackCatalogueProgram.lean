import BalancedAssortments.NPStackCatalogueMemberCorrect
import BalancedAssortments.NPStackMacroLoops
import BalancedAssortments.NPCNFThreeCatalogued

namespace BalancedAssortments.NPCNF.StackCatalogue
open NPStack NPStack.Macros

inductive Extra | input | tag | maximum | fresh deriving DecidableEq,Fintype
abbrev Register := NPStackCatalogueMember.Register ⊕ Extra

def input : Register := .inr .input
def tag : Register := .inr .tag
def maximum : Register := .inr .maximum
def fresh : Register := .inr .fresh
def query : Register := .inl .query
def catalogue : Register := .inl .catalogue
def left : Register := .inl .left
def right : Register := .inl .right
def scratch : Register := .inl .scratch
def result : Register := .inl .output

inductive Main | readTag | inspectTag | checkTagEnd (more : Bool) | readLabel |
  invokeMember | inspectMember | copyQuery | copyMaximum | compare | inspectOrder |
  clearMaximum | replaceMaximum | emitLabel | makeFresh | accept | reject
  deriving DecidableEq,Fintype
inductive State | outer (q : Label Main) | member (q : NPStackCatalogueMember.State)
  deriving DecidableEq,Fintype

def macroCode : Main → Macro Register Main
  | .readTag => .taggedRead input scratch tag .inspectTag .reject
  | .inspectTag => .pop tag .reject (.checkTagEnd false) (.checkTagEnd true)
  | .checkTagEnd more => .pop tag (if more then .readLabel else .makeFresh) .reject .reject
  | .readLabel => .taggedRead input scratch query .invokeMember .reject
  | .invokeMember => .halt false
  | .inspectMember => .pop result .reject .copyQuery .reject
  | .copyQuery => .copy query scratch left .copyMaximum
  | .copyMaximum => .copy maximum scratch right .compare
  | .compare => .compare left right result .inspectOrder
  | .inspectOrder => .pop result .reject .clearMaximum .emitLabel
  | .clearMaximum => .pop maximum .replaceMaximum .clearMaximum .clearMaximum
  | .replaceMaximum => .copy query scratch maximum .emitLabel
  | .emitLabel => .taggedEmit query scratch catalogue .readTag
  | .makeFresh => .add maximum right scratch fresh true .accept
  | .accept => .halt true
  | .reject => .halt false

def code : State → Instr Register State
  | .outer (.main .invokeMember) => .jump (.member (.outer (.main (.probe false))))
  | .outer q => (Macros.code macroCode q).rename id State.outer
  | .member (.outer (.main .accept)) => .jump (.outer (.main .inspectMember))
  | .member q => (NPStackCatalogueMember.program.code q).rename Sum.inl State.member

def program : NPStack.Program Register State := ⟨code,.outer (.main .readTag),input,fresh⟩

def cfg (q : Main) (s : Register → List Bool) : Config Register State := ⟨.outer (.main q),s⟩

def store (i m f q t c l r answer : List Bool) : Register → List Bool
  | .inr .input => i | .inr .maximum => m | .inr .fresh => f | .inr .tag => t
  | .inl .query => q | .inl .catalogue => c | .inl .left => l | .inl .right => r | .inl .output => answer
  | _ => []

lemma outer_extends : CodeExtends (Macros.compile macroCode .readTag input fresh) program id State.outer := by
  intro q h
  cases q with
  | main q => cases q <;> first | exact False.elim (h false rfl) | rfl
  | «local» q st => rfl

lemma member_extends : CodeExtends NPStackCatalogueMember.program program Sum.inl State.member := by
  intro q h
  cases q with
  | outer q =>
    cases q with
    | main q => cases q <;> first | exact False.elim (h true rfl) | rfl
    | «local» q st => rfl
  | equal f q => rfl

lemma outer_run {t : ℕ} {q q' : Label Main} {s s' : Register → List Bool}
    (h : Run (Macros.compile macroCode .readTag input fresh) t ⟨q,s⟩ ⟨q',s'⟩) :
    Run program t ⟨.outer q,s⟩ ⟨.outer q',s'⟩ :=
  h.relocate_exact id State.outer (fun _ _ h=>h) outer_extends
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩ (fun k hk=>False.elim (hk k rfl))

end BalancedAssortments.NPCNF.StackCatalogue
