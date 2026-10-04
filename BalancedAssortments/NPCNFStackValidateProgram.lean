import BalancedAssortments.NPCNFStackCatalogueGrammar

namespace BalancedAssortments.NPCNF.StackValidate
open NPStack NPStack.Macros

inductive Extra | input | tag | maximum | fresh | original deriving DecidableEq,Fintype
abbrev Register := NPStackCatalogueMember.Register ⊕ Extra

def input : Register := .inr .input
def tag : Register := .inr .tag
def fresh : Register := .inr .fresh
def original : Register := .inr .original
def query : Register := .inl .query
def catalogue : Register := .inl .catalogue
def scratch : Register := .inl .scratch
def result : Register := .inl .output

def headerMap : StackCatalogue.Register → Register
  | .inl r => .inl r
  | .inr .input => .inr .input
  | .inr .tag => .inr .tag
  | .inr .maximum => .inr .maximum
  | .inr .fresh => .inr .fresh

inductive Main | saveFormula | readHeader | inspectHeader | checkHeaderEnd (more : Bool) |
  readSign | inspectSign | checkSignEnd | readLiteral | invokeMember | inspectMember |
  clearQuery | checkEnd | accept | reject
  deriving DecidableEq,Fintype
inductive State | header (q : StackCatalogue.State) | outer (q : Label Main) | member (q : NPStackCatalogueMember.State)
  deriving DecidableEq,Fintype

def macroCode : Main → Macro Register Main
  | .saveFormula => .copy input scratch original .readHeader
  | .readHeader => .taggedRead input scratch tag .inspectHeader .reject
  | .inspectHeader => .pop tag .reject (.checkHeaderEnd false) (.checkHeaderEnd true)
  | .checkHeaderEnd more => .pop tag (if more then .readSign else .checkEnd) .reject .reject
  | .readSign => .taggedRead input scratch tag .inspectSign .reject
  | .inspectSign => .pop tag .readHeader .checkSignEnd .checkSignEnd
  | .checkSignEnd => .pop tag .readLiteral .reject .reject
  | .readLiteral => .taggedRead input scratch query .invokeMember .reject
  | .invokeMember => .halt false
  | .inspectMember => .pop result .reject .reject .clearQuery
  | .clearQuery => .pop query .readSign .clearQuery .clearQuery
  | .checkEnd => .pop input .accept .reject .reject
  | .accept => .halt true
  | .reject => .halt false

def code : State → Instr Register State
  | .header (.outer (.main .accept)) => .jump (.outer (.main .saveFormula))
  | .header q => (StackCatalogue.program.code q).rename headerMap State.header
  | .outer (.main .invokeMember) => .jump (.member (.outer (.main (.probe false))))
  | .outer q => (Macros.code macroCode q).rename id State.outer
  | .member (.outer (.main .accept)) => .jump (.outer (.main .inspectMember))
  | .member q => (NPStackCatalogueMember.program.code q).rename Sum.inl State.member

def program : NPStack.Program Register State :=
  ⟨code,.header (.outer (.main .readTag)),input,original⟩

def cfg (q : Main) (s : Register → List Bool) : Config Register State := ⟨.outer (.main q),s⟩

def store (i o f c q t answer : List Bool) : Register → List Bool
  | .inr .input => i | .inr .original => o | .inr .fresh => f | .inr .tag => t
  | .inl .catalogue => c | .inl .query => q | .inl .output => answer
  | _ => []

lemma headerMap_injective : Function.Injective headerMap := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => simp_all [headerMap]
    | inr b => cases b <;> simp_all [headerMap]
  | inr a => cases b with
    | inl b => simp_all [headerMap];cases a <;> contradiction
    | inr b => cases a <;> cases b <;> simp_all [headerMap]

lemma header_extends : CodeExtends StackCatalogue.program program headerMap State.header := by
  intro q h
  cases q with
  | outer q =>
    cases q with
    | main q => cases q <;> first | exact False.elim (h true rfl) | rfl
    | «local» q st => rfl
  | member q => rfl

lemma outer_extends : CodeExtends (Macros.compile macroCode .saveFormula input original) program id State.outer := by
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
    (h : Run (Macros.compile macroCode .saveFormula input original) t ⟨q,s⟩ ⟨q',s'⟩) :
    Run program t ⟨.outer q,s⟩ ⟨.outer q',s'⟩ :=
  h.relocate_exact id State.outer (fun _ _ h=>h) outer_extends
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩ (fun k hk=>False.elim (hk k rfl))

end BalancedAssortments.NPCNF.StackValidate
