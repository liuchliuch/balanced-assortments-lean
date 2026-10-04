import BalancedAssortments.NPStackSignedAdd
import BalancedAssortments.NPStackMultiplyCorrect

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary ComplexityTimeVerifier

inductive SignedMulPhase | pp | nn | pn | np deriving DecidableEq, Fintype
inductive SignedMulStack
  | xp | xn | yp | yn | duplicate (negative : Bool) | product (phase : SignedMulPhase)
  | work (k : MulStack) | copyScratch | addScratch | positive | negative
  deriving DecidableEq, Fintype
inductive SignedMulState
  | copy (negative : Bool) (q : CopyState) | multiply (phase : SignedMulPhase) (q : MulState)
  | add (q : SignedAddState)
  deriving DecidableEq, Fintype

def signedMulCopyMap (negative : Bool) : CopyStack → SignedMulStack
  | .source => if negative then .xn else .xp
  | .scratch => .copyScratch
  | .target => .duplicate negative

def signedMulInput : SignedMulPhase → SignedMulStack
  | .pp => .duplicate false | .nn => .duplicate true | .pn => .xp | .np => .xn

def signedMulFactor : SignedMulPhase → SignedMulStack
  | .pp | .np => .yp | .nn | .pn => .yn

def signedMulMap (p : SignedMulPhase) : MulStack → SignedMulStack
  | .input => signedMulInput p
  | .factor => signedMulFactor p
  | .output => .product p
  | k => .work k

def signedMulAddMap : SignedAddStack → SignedMulStack
  | .ap => .product .pp | .an => .product .pn | .bp => .product .nn | .bn => .product .np
  | .scratch => .addScratch | .positive => .positive | .negative => .negative

def signedMulNext : SignedMulPhase → SignedMulState
  | .pp => .multiply .nn (.initial .read)
  | .nn => .multiply .pn (.initial .read)
  | .pn => .multiply .np (.initial .read)
  | .np => .add (.positive (.readX false))

def signedMultiplyProgram : Program SignedMulStack SignedMulState where
  code
    | .copy false .done => .jump (.copy true .readSource)
    | .copy true .done => .jump (.multiply .pp (.initial .read))
    | .copy b q => (copyProgram.code q).rename (signedMulCopyMap b) (.copy b)
    | .multiply p .done => .jump (signedMulNext p)
    | .multiply p q => (multiplyProgram.code q).rename (signedMulMap p) (.multiply p)
    | .add q => (signedAddProgram.code q).rename signedMulAddMap SignedMulState.add
  start := .copy false .readSource
  inputStack := .xp
  outputStack := .positive

lemma signedMulCopyMap_injective (b : Bool) : Function.Injective (signedMulCopyMap b) := by
  intro a c h; cases b <;> cases a <;> cases c <;> simp_all [signedMulCopyMap]
lemma signedMulMap_injective (p : SignedMulPhase) : Function.Injective (signedMulMap p) := by
  intro a b h; cases p <;> cases a <;> cases b <;> simp_all [signedMulMap,signedMulInput,signedMulFactor]
lemma signedMulAddMap_injective : Function.Injective signedMulAddMap := by
  intro a b h; cases a <;> cases b <;> simp_all [signedMulAddMap]

lemma signedMul_copy_code (b : Bool) : CodeExtends copyProgram signedMultiplyProgram
    (signedMulCopyMap b) (.copy b) := by
  intro q h; cases b <;> cases q <;> simp_all [signedMultiplyProgram,copyProgram]
lemma signedMul_multiply_code (p : SignedMulPhase) : CodeExtends multiplyProgram signedMultiplyProgram
    (signedMulMap p) (.multiply p) := by
  intro q h; cases q <;> simp_all [signedMultiplyProgram,multiplyProgram]
lemma signedMul_add_code : CodeExtends signedAddProgram signedMultiplyProgram
    signedMulAddMap SignedMulState.add := by intro q h; rfl

def signedMulUpdate (s : SignedMulStack → List Bool) (p : SignedMulPhase) (result : List Bool) :
    SignedMulStack → List Bool := Function.update (Function.update s (signedMulInput p) []) (.product p) result

lemma signedMul_copy_run (b : Bool) (xs : List Bool) (s : SignedMulStack → List Bool)
    (hs : ∀ k,s (signedMulCopyMap b k)=copyStacks xs [] [] k) :
    Run signedMultiplyProgram (5*xs.length+2) ⟨.copy b .readSource,s⟩
      ⟨.copy b .done,Function.update s (.duplicate b) xs⟩ := by
  apply (copy_run xs []).relocate_exact (signedMulCopyMap b) (.copy b)
    (signedMulCopyMap_injective b) (signedMul_copy_code b) ⟨rfl,hs⟩
  · refine ⟨rfl,?_⟩
    have hh := update_relocated (signedMulCopyMap b) (signedMulCopyMap_injective b)
      (copyStacks xs [] []) s hs .target xs
    intro k
    change (Function.update s (signedMulCopyMap b .target) xs) (signedMulCopyMap b k)=_
    rw [hh]
    cases k <;> simp [copyConfig,copyStacks,Function.update]
  · intro k hk
    exact Function.update_of_ne (Ne.symm (hk .target)) _ _

lemma signedMul_multiply_run (p : SignedMulPhase) (xs factor : List Bool) (s : SignedMulStack → List Bool)
    (hs : ∀ k,s (signedMulMap p k)=(multiplicationInput xs factor).stk k) :
    ∃ t ≤ multiplicationBudget xs.length factor.length,
      Run signedMultiplyProgram t ⟨.multiply p (.initial .read),s⟩
        ⟨.multiply p .done,signedMulUpdate s p (mulBits xs factor).1⟩ := by
  obtain ⟨t,ht,hr⟩ := multiplication_run xs factor
  refine ⟨t,ht,hr.relocate_exact (signedMulMap p) (.multiply p)
    (signedMulMap_injective p) (signedMul_multiply_code p) ⟨rfl,hs⟩ ?_ ?_⟩
  · refine ⟨rfl,?_⟩
    have h1 := update_relocated (signedMulMap p) (signedMulMap_injective p)
      (multiplicationInput xs factor).stk s hs .input []
    have h2 := update_relocated (signedMulMap p) (signedMulMap_injective p)
      (Function.update (multiplicationInput xs factor).stk .input [])
      (Function.update s (signedMulMap p .input) []) h1 .output (mulBits xs factor).1
    intro k
    change (Function.update (Function.update s (signedMulMap p .input) [])
      (signedMulMap p .output) (mulBits xs factor).1) (signedMulMap p k)=_
    rw [h2]
    cases k <;> simp [multiplicationInput,multiplicationOutput,mulStacks,Function.update]
  · intro k hk
    exact (Function.update_of_ne (Ne.symm (hk .output)) _ _).trans
      (Function.update_of_ne (Ne.symm (hk .input)) _ _)

end BalancedAssortments.NPStack
