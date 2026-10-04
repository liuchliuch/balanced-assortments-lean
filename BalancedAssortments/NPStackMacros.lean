import BalancedAssortments.NPStackArithmeticSound
import BalancedAssortments.NPStackNormalize
import BalancedAssortments.NPStackFieldCorrect
import BalancedAssortments.NPStackFieldEncode
import BalancedAssortments.NPStackFieldData
import BalancedAssortments.NPStackSignedFractionSound
import BalancedAssortments.NPStackSignedMultiplySound

/-! Finite macro assembly. Every call is expanded into the already proved
primitive Boolean-stack instructions; no macro remains in operational semantics. -/
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace BalancedAssortments.NPStack.Macros
open NPStack

inductive Macro (K Q : Type*)
  | halt (accepted : Bool)
  | jump (next : Q)
  | push (k : K) (b : Bool) (next : Q)
  | pop (k : K) (empty onFalse onTrue : Q)
  | copy (source scratch target : K) (next : Q)
  | add (left right scratch target : K) (carry : Bool) (next : Q)
  | normalize (source scratch target : K) (next : Q)
  | read (input count reversed output : K) (success failure : Q)
  | encode (input reversed count output : K) (next : Q)
  | taggedRead (input scratch output : K) (success failure : Q)
  | taggedEmit (input scratch output : K) (next : Q)
  | compare (left right output : K) (next : Q)
  | multiply (registers : MulStack → K) (next : Q)
  | signedCompare (registers : SignedCompareStack → K) (next : Q)
  | signedAdd (registers : SignedAddStack → K) (next : Q)
  | signedMultiply (registers : SignedMulStack → K) (next : Q)

inductive Local
  | copy (q : CopyState)
  | add (q : AddState)
  | normalize (q : NormalizeState)
  | read (q : NPStackField.State)
  | encode (q : NPStackFieldEncode.State)
  | taggedRead (q : NPStackFieldData.ReadState)
  | taggedEmit (q : NPStackFieldData.EmitState)
  | compare (q : CompareState)
  | multiply (q : MulState)
  | signedCompare (q : SignedCompareState)
  | signedAdd (q : SignedAddState)
  | signedMultiply (q : SignedMulState)
  deriving DecidableEq, Fintype

inductive Label (Q : Type*) | main (q : Q) | local (caller : Q) (state : Local)
  deriving DecidableEq, Fintype

def copyMap {K : Type*} (source scratch target : K) : CopyStack → K
  | .source => source | .scratch => scratch | .target => target

def addMap {K : Type*} (left right scratch target : K) : AddStack → K
  | .left => left | .right => right | .scratch => scratch | .output => target

def normalizeMap {K : Type*} (source scratch target : K) : CompareStack → K
  | .left => source | .right => scratch | .result => target

def readMap {K : Type*} (input count reversed output : K) : NPStackField.Stack → K
  | .input => input | .count => count | .reversed => reversed | .output => output

def encodeMap {K : Type*} (input reversed count output : K) : NPStackFieldEncode.Stack → K
  | .input => input | .reversed => reversed | .count => count | .output => output

def dataMap {K : Type*} (input scratch output : K) : NPStackFieldData.Stack → K
  | .input => input | .scratch => scratch | .output => output

def returnCode {A B K Q : Type*} (fk : A → K) (fq : B → Q) (yes no : Q) : Instr A B → Instr K Q
  | .halt b => .jump (if b then yes else no)
  | other => other.rename fk fq

lemma returnCode_of_nonhalt {A B K Q : Type*} (fk : A → K) (fq : B → Q) (yes no : Q)
    (i : Instr A B) (h : ∀ b,i≠.halt b) : returnCode fk fq yes no i=i.rename fk fq := by
  cases i <;> try rfl
  exact False.elim (h _ rfl)

def code {K Q : Type*} (m : Q → Macro K Q) : Label Q → Instr K (Label Q)
  | .main q => match m q with
    | .halt b => .halt b
    | .jump next => .jump (.main next)
    | .push k b next => .push k b (.main next)
    | .pop k qe qf qt => .pop k (.main qe) (.main qf) (.main qt)
    | .copy s w t next => .jump (.local q (.copy .readSource))
    | .add a b w t carry next => .jump (.local q (.add (.readX carry)))
    | .normalize s w t next => .jump (.local q (.normalize .sourceRead))
    | .read i c r o yes no => .jump (.local q (.read .header))
    | .encode i r c o next => .jump (.local q (.encode .scan))
    | .taggedRead i w o yes no => .jump (.local q (.taggedRead .tag))
    | .taggedEmit i w o next => .jump (.local q (.taggedEmit .reverse))
    | .compare a b o next => .jump (.local q (.compare (.readLeft .eq)))
    | .multiply regs next => .jump (.local q (.multiply (.initial .read)))
    | .signedCompare regs next => .jump (.local q (.signedCompare (.addLeft (.readX false))))
    | .signedAdd regs next => .jump (.local q (.signedAdd (.positive (.readX false))))
    | .signedMultiply regs next => .jump (.local q (.signedMultiply (.copy false .readSource)))
  | .local q state => match m q,state with
    | .copy s w t next,.copy st => returnCode (copyMap s w t) (fun st => Label.local q (.copy st)) (.main next) (.main next) (copyProgram.code st)
    | .add a b w t carry next,.add st => returnCode (addMap a b w t) (fun st => Label.local q (.add st)) (.main next) (.main next) (addProgram.code st)
    | .normalize s w t next,.normalize st => returnCode (normalizeMap s w t) (fun st => Label.local q (.normalize st)) (.main next) (.main next) (normalizeProgram.code st)
    | .read i c r o yes no,.read st => returnCode (readMap i c r o) (fun st => Label.local q (.read st)) (.main yes) (.main no) (NPStackField.program.code st)
    | .encode i r c o next,.encode st => returnCode (encodeMap i r c o) (fun st => Label.local q (.encode st)) (.main next) (.main next) (NPStackFieldEncode.program.code st)
    | .taggedRead i w o yes no,.taggedRead st => returnCode (dataMap i w o) (fun st => Label.local q (.taggedRead st)) (.main yes) (.main no) (NPStackFieldData.readProgram.code st)
    | .taggedEmit i w o next,.taggedEmit st => returnCode (dataMap i w o) (fun st => Label.local q (.taggedEmit st)) (.main next) (.main next) (NPStackFieldData.emitProgram.code st)
    | .compare a b o next,.compare st => returnCode (normalizeMap a b o) (fun st => Label.local q (.compare st)) (.main next) (.main next) (compareProgram.code st)
    | .multiply regs next,.multiply st => returnCode (regs) (fun st => Label.local q (.multiply st)) (.main next) (.main next) (multiplyProgram.code st)
    | .signedCompare regs next,.signedCompare st => returnCode (regs) (fun st => Label.local q (.signedCompare st)) (.main next) (.main next) (signedCompareProgram.code st)
    | .signedAdd regs next,.signedAdd st => returnCode (regs) (fun st => Label.local q (.signedAdd st)) (.main next) (.main next) (signedAddProgram.code st)
    | .signedMultiply regs next,.signedMultiply st => returnCode (regs) (fun st => Label.local q (.signedMultiply st)) (.main next) (.main next) (signedMultiplyProgram.code st)
    | _,_ => .halt false

def compile {K Q : Type*} (m : Q → Macro K Q) (start : Q) (input output : K) : Program K (Label Q) :=
  ⟨code m,.main start,input,output⟩

variable {K Q : Type*} [DecidableEq K] (m : Q → Macro K Q) (start : Q) (input output : K)

set_option maxHeartbeats 0 in
lemma copy_extends {q next : Q} {s w t : K} (h : m q=.copy s w t next) :
    CodeExtends copyProgram (compile m start input output) (copyMap s w t) (fun st => Label.local q (.copy st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn
lemma add_extends {q next : Q} {a b w t : K} {carry : Bool} (h : m q=.add a b w t carry next) :
    CodeExtends addProgram (compile m start input output) (addMap a b w t) (fun st => Label.local q (.add st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn
lemma normalize_extends {q next : Q} {s w t : K} (h : m q=.normalize s w t next) :
    CodeExtends normalizeProgram (compile m start input output) (normalizeMap s w t) (fun st => Label.local q (.normalize st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn
lemma read_extends {q yes no : Q} {i c r o : K} (h : m q=.read i c r o yes no) :
    CodeExtends NPStackField.program (compile m start input output) (readMap i c r o) (fun st => Label.local q (.read st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn
lemma encode_extends {q next : Q} {i r c o : K} (h : m q=.encode i r c o next) :
    CodeExtends NPStackFieldEncode.program (compile m start input output) (encodeMap i r c o) (fun st => Label.local q (.encode st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn
lemma taggedRead_extends {q yes no : Q} {i w o : K} (h : m q=.taggedRead i w o yes no) :
    CodeExtends NPStackFieldData.readProgram (compile m start input output) (dataMap i w o) (fun st => Label.local q (.taggedRead st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn
lemma taggedEmit_extends {q next : Q} {i w o : K} (h : m q=.taggedEmit i w o next) :
    CodeExtends NPStackFieldData.emitProgram (compile m start input output) (dataMap i w o) (fun st => Label.local q (.taggedEmit st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn
lemma compare_extends {q next : Q} {a b o : K} (h : m q=.compare a b o next) :
    CodeExtends compareProgram (compile m start input output) (normalizeMap a b o) (fun st => Label.local q (.compare st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn
lemma multiply_extends {q next : Q} {regs : MulStack → K} (h : m q=.multiply regs next) :
    CodeExtends multiplyProgram (compile m start input output) (regs) (fun st => Label.local q (.multiply st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn
lemma signedCompare_extends {q next : Q} {regs : SignedCompareStack → K} (h : m q=.signedCompare regs next) :
    CodeExtends signedCompareProgram (compile m start input output) (regs) (fun st => Label.local q (.signedCompare st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn
lemma signedAdd_extends {q next : Q} {regs : SignedAddStack → K} (h : m q=.signedAdd regs next) :
    CodeExtends signedAddProgram (compile m start input output) (regs) (fun st => Label.local q (.signedAdd st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn
lemma signedMultiply_extends {q next : Q} {regs : SignedMulStack → K} (h : m q=.signedMultiply regs next) :
    CodeExtends signedMultiplyProgram (compile m start input output) (regs) (fun st => Label.local q (.signedMultiply st)) := by
  intro st hn
  simp only [compile,code,h]
  exact returnCode_of_nonhalt _ _ _ _ _ hn

end BalancedAssortments.NPStack.Macros
