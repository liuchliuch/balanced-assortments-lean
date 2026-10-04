import BalancedAssortments.NPStackTimeoutTotal
import BalancedAssortments.NPStackMacroRuns
import BalancedAssortments.CookLevinStackClockProgram

/-! Actual finite raw-input clock/fuel wiring. Original input is copied before
clock generation, so no preservation oracle is required from the clock program.
All source instructions are executed through the physical-fuel timeout. -/
namespace BalancedAssortments.NPStack.Clocked
open NPStack NPStack.Macros

abbrev Stack (K CK : Type*) := CK ⊕ (Timeout.Stack K ⊕ Unit)
inductive Label (CQ Q : Type*) (n : ℕ)
  | copyWord (q : CopyState) | clock (q : CQ) | copyFuel (q : CopyState)
  | timed (q : Timeout.State Q) | clear | emit (pc : Fin (n+1)) | accept
  deriving DecidableEq,Fintype

def clockStack {K CK : Type*} : CK → Stack K CK := Sum.inl
def timedStack {K CK : Type*} (k : Timeout.Stack K) : Stack K CK := .inr (.inl k)
def scratch {K CK : Type*} : Stack K CK := .inr (.inr ())

def wordMap (P C : FiniteProgram) : CopyStack → Stack P.K C.K
  | .source => clockStack C.program.inputStack
  | .scratch => scratch
  | .target => timedStack (.inl P.program.inputStack)
def fuelMap (P C : FiniteProgram) : CopyStack → Stack P.K C.K
  | .source => clockStack C.program.outputStack
  | .scratch => scratch
  | .target => timedStack (.inr ())
def output (P C : FiniteProgram) : Stack P.K C.K := timedStack (.inl P.program.outputStack)

def nextIndex {n : ℕ} (pc : Fin (n+1)) : Fin (n+1) := ⟨min (pc.val+1) n,by omega⟩

def code (P C : FiniteProgram) (fallback : List Bool) :
    Label C.Q P.Q fallback.length → Instr (Stack P.K C.K) (Label C.Q P.Q fallback.length)
  | .copyWord q => returnCode (wordMap P C) Label.copyWord (.clock C.program.start) .clear (copyProgram.code q)
  | .clock q => returnCode clockStack Label.clock (.copyFuel .readSource) .clear (C.program.code q)
  | .copyFuel q => returnCode (fuelMap P C) Label.copyFuel (.timed (.tick P.program.start)) .clear (copyProgram.code q)
  | .timed q => returnCode timedStack Label.timed .accept .clear ((Timeout.program P.program).code q)
  | .clear => .pop (output P C) (.emit 0) .clear .clear
  | .emit pc => match fallback.reverse[pc.val]? with
    | none => .jump .accept
    | some b => .push (output P C) b (.emit (nextIndex pc))
  | .accept => .halt true

def program (P C : FiniteProgram) (fallback : List Bool) :
    Program (Stack P.K C.K) (Label C.Q P.Q fallback.length) :=
  ⟨code P C fallback,.copyWord .readSource,clockStack C.program.inputStack,output P C⟩

def finiteProgram (P C : FiniteProgram) (fallback : List Bool) : FiniteProgram :=
  ⟨Stack P.K C.K,Label C.Q P.Q fallback.length,program P C fallback⟩

lemma wordMap_injective (P C : FiniteProgram) : Function.Injective (wordMap P C) := by
  intro a b h;cases a <;> cases b <;> simp_all [wordMap,clockStack,timedStack,scratch]
lemma fuelMap_injective (P C : FiniteProgram) : Function.Injective (fuelMap P C) := by
  intro a b h;cases a <;> cases b <;> simp_all [fuelMap,clockStack,timedStack,scratch]
lemma timedStack_injective {K CK : Type*} : Function.Injective (@timedStack K CK) := by
  intro a b h;exact Sum.inl_injective (Sum.inr_injective h)

lemma word_extends (P C : FiniteProgram) (fallback : List Bool) :
    CodeExtends copyProgram (program P C fallback) (wordMap P C) Label.copyWord := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma clock_extends (P C : FiniteProgram) (fallback : List Bool) :
    CodeExtends C.program (program P C fallback) clockStack Label.clock := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma fuel_extends (P C : FiniteProgram) (fallback : List Bool) :
    CodeExtends copyProgram (program P C fallback) (fuelMap P C) Label.copyFuel := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h
lemma timed_extends (P C : FiniteProgram) (fallback : List Bool) :
    CodeExtends (Timeout.program P.program) (program P C fallback) timedStack Label.timed := by
  intro q h;exact returnCode_of_nonhalt _ _ _ _ _ h

lemma program_noChoice (P C : FiniteProgram) (fallback : List Bool) (hp : NoChoice P.program) (hc : NoChoice C.program) :
    NoChoice (program P C fallback) := by
  intro q a b
  cases q with
  | copyWord q => exact return_not_choice _ _ _ _ _ (copy_noChoice q) _ _
  | clock q => exact return_not_choice _ _ _ _ _ (hc q) _ _
  | copyFuel q => exact return_not_choice _ _ _ _ _ (copy_noChoice q) _ _
  | timed q => exact return_not_choice _ _ _ _ _ (Timeout.program_noChoice hp q) _ _
  | clear => simp [program,code]
  | emit pc => simp only [program,code];split <;> simp
  | accept => simp [program,code]

end BalancedAssortments.NPStack.Clocked
