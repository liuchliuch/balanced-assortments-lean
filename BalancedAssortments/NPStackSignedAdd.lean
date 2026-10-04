import BalancedAssortments.NPStackSignedCompare
import BalancedAssortments.NPStackArithmeticSound

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary ComplexityTimeVerifier

inductive SignedAddStack | ap | an | bp | bn | scratch | positive | negative
  deriving DecidableEq, Fintype
inductive SignedAddState | positive (q : AddState) | negative (q : AddState)
  deriving DecidableEq, Fintype

def signedAddMap (negative : Bool) : AddStack→SignedAddStack
  | .left => if negative then .an else .ap
  | .right => if negative then .bn else .bp
  | .scratch => .scratch
  | .output => if negative then .negative else .positive

def signedAddProgram : Program SignedAddStack SignedAddState where
  code
    | .positive .done => .jump (.negative (.readX false))
    | .positive q => (addProgram.code q).rename (signedAddMap false) SignedAddState.positive
    | .negative q => (addProgram.code q).rename (signedAddMap true) SignedAddState.negative
  start := .positive (.readX false)
  inputStack := .ap
  outputStack := .positive

def signedAddStacks (ap an bp bn pos neg : List Bool) : SignedAddStack→List Bool
  | .ap => ap | .an => an | .bp => bp | .bn => bn
  | .positive => pos | .negative => neg | .scratch => []

def signedAddConfig (q : SignedAddState) (ap an bp bn pos neg : List Bool) :
    Config SignedAddStack SignedAddState := ⟨q,signedAddStacks ap an bp bn pos neg⟩

lemma signedAddMap_injective (b : Bool) : Function.Injective (signedAddMap b) := by
  intro a c h;cases b <;> cases a <;> cases c <;> simp_all [signedAddMap]
lemma signedAdd_positive_code : CodeExtends addProgram signedAddProgram (signedAddMap false) SignedAddState.positive := by
  intro q h;cases q <;> simp_all [signedAddProgram,addProgram]
lemma signedAdd_negative_code : CodeExtends addProgram signedAddProgram (signedAddMap true) SignedAddState.negative := by
  intro q h;rfl

def signedAddTime (x y : ZBits) : ℕ := 5*max x.1.length y.1.length+6+1+5*max x.2.length y.2.length+6

theorem signedAdd_run (x y : ZBits) :
    Run signedAddProgram (signedAddTime x y)
      (signedAddConfig (.positive (.readX false)) x.1 x.2 y.1 y.2 [] [])
      (signedAddConfig (.negative .done) [] [] [] [] (zadd x y).1.1 (zadd x y).1.2) := by
  have hp : Run signedAddProgram (5*max x.1.length y.1.length+6)
      (signedAddConfig (.positive (.readX false)) x.1 x.2 y.1 y.2 [] [])
      (signedAddConfig (.positive .done) [] x.2 [] y.2 (addCarry x.1 y.1 false).1 []) := by
    apply (add_run x.1 y.1 false).relocate_exact (signedAddMap false) SignedAddState.positive
      (signedAddMap_injective false) signedAdd_positive_code
    · constructor; rfl; intro k;cases k <;> rfl
    · constructor; rfl; intro k;cases k <;> rfl
    · intro k hk
      have h1:=hk .left;have h2:=hk .right;have h3:=hk .scratch;have h4:=hk .output
      cases k <;> simp_all [signedAddMap,signedAddConfig,signedAddStacks]
  have hn : Run signedAddProgram (5*max x.2.length y.2.length+6)
      (signedAddConfig (.negative (.readX false)) [] x.2 [] y.2 (addCarry x.1 y.1 false).1 [])
      (signedAddConfig (.negative .done) [] [] [] [] (addCarry x.1 y.1 false).1 (addCarry x.2 y.2 false).1) := by
    apply (add_run x.2 y.2 false).relocate_exact (signedAddMap true) SignedAddState.negative
      (signedAddMap_injective true) signedAdd_negative_code
    · constructor; rfl; intro k;cases k <;> rfl
    · constructor; rfl; intro k;cases k <;> rfl
    · intro k hk
      have h1:=hk .left;have h2:=hk .right;have h3:=hk .scratch;have h4:=hk .output
      cases k <;> simp_all [signedAddMap,signedAddConfig,signedAddStacks]
  have hj : Step signedAddProgram
      (signedAddConfig (.positive .done) [] x.2 [] y.2 (addCarry x.1 y.1 false).1 [])
      (signedAddConfig (.negative (.readX false)) [] x.2 [] y.2 (addCarry x.1 y.1 false).1 []) := by
    simp [Step,successors,signedAddProgram,signedAddConfig]
  simpa only [signedAddTime,zadd,Nat.add_assoc] using (hp.trans (Run.one hj)).trans hn

theorem signedAddTime_bound (x y : ZBits) : signedAddTime x y≤10*max (width x) (width y)+13 := by
  simp only [signedAddTime,width]
  omega

theorem signedAdd_noChoice : NoChoice signedAddProgram := by
  intro q a b
  cases q with
  | positive q => cases q <;> simp [signedAddProgram,addProgram,Instr.rename]
  | negative q => cases q <;> simp [signedAddProgram,addProgram,Instr.rename]

def finiteSignedAdd : FiniteProgram where
  K := SignedAddStack
  Q := SignedAddState
  program := signedAddProgram

end BalancedAssortments.NPStack
