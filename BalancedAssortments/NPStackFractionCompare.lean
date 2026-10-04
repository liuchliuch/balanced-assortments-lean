import BalancedAssortments.NPStackSignedCompare
import BalancedAssortments.NPStackMultiplyCorrect
import BalancedAssortments.FixedSupportCostRational

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary ComplexityTimeVerifier

inductive FractionPhase | ap | an | bp | bn deriving DecidableEq, Fintype
inductive FractionCompareStack
  | numerator (p : FractionPhase)
  | denominator (right : Bool)
  | product (p : FractionPhase)
  | work (k : MulStack)
  | leftSum | rightSum | scratch | output
  deriving DecidableEq, Fintype
inductive FractionCompareState
  | multiply (p : FractionPhase) (q : MulState)
  | compare (q : SignedCompareState)
  deriving DecidableEq, Fintype

def fractionFactor : FractionPhase→Bool | .ap | .an => true | .bp | .bn => false

def fractionMulMap (p : FractionPhase) : MulStack→FractionCompareStack
  | .input => .numerator p
  | .factor => .denominator (fractionFactor p)
  | .output => .product p
  | k => .work k

def fractionSignedMap : SignedCompareStack→FractionCompareStack
  | .ap => .product .ap | .an => .product .an | .bp => .product .bp | .bn => .product .bn
  | .leftSum => .leftSum | .rightSum => .rightSum | .scratch => .scratch | .output => .output

def fractionNext : FractionPhase→FractionCompareState
  | .ap => .multiply .an (.initial .read)
  | .an => .multiply .bp (.initial .read)
  | .bp => .multiply .bn (.initial .read)
  | .bn => .compare (.addLeft (.readX false))

def fractionCompareProgram : Program FractionCompareStack FractionCompareState where
  code
    | .multiply p .done => .jump (fractionNext p)
    | .multiply p q => (multiplyProgram.code q).rename (fractionMulMap p) (FractionCompareState.multiply p)
    | .compare q => (signedCompareProgram.code q).rename fractionSignedMap FractionCompareState.compare
  start := .multiply .ap (.initial .read)
  inputStack := .numerator .ap
  outputStack := .output

lemma fractionMulMap_injective (p : FractionPhase) : Function.Injective (fractionMulMap p) := by
  intro a b h;cases a <;> cases b <;> simp_all [fractionMulMap]
lemma fractionSignedMap_injective : Function.Injective fractionSignedMap := by
  intro a b h;cases a <;> cases b <;> simp_all [fractionSignedMap]

lemma fractionMul_code (p : FractionPhase) : CodeExtends multiplyProgram fractionCompareProgram
    (fractionMulMap p) (FractionCompareState.multiply p) := by
  intro q h;cases q <;> simp_all [fractionCompareProgram,multiplyProgram]
lemma fractionSigned_code : CodeExtends signedCompareProgram fractionCompareProgram
    fractionSignedMap FractionCompareState.compare := by intro q h;rfl

def fractionUpdate (s : FractionCompareStack→List Bool) (p : FractionPhase) (result : List Bool) :
    FractionCompareStack→List Bool :=
  Function.update (Function.update s (.numerator p) []) (.product p) result

/-- A real multiplication subroutine embedded in the fraction comparator.
All stacks outside its finite allocation are preserved. -/
theorem fraction_multiply_run (p : FractionPhase) (xs factor : List Bool)
    (s : FractionCompareStack→List Bool)
    (hs : ∀ k,s (fractionMulMap p k)=(multiplicationInput xs factor).stk k) :
    ∃ t ≤ multiplicationBudget xs.length factor.length,
      Run fractionCompareProgram t ⟨.multiply p (.initial .read),s⟩
        ⟨.multiply p .done,fractionUpdate s p (mulBits xs factor).1⟩ := by
  obtain ⟨t,ht,hr⟩ := multiplication_run xs factor
  refine ⟨t,ht,hr.relocate_exact (fractionMulMap p) (FractionCompareState.multiply p)
    (fractionMulMap_injective p) (fractionMul_code p) ⟨rfl,hs⟩ ?_ ?_⟩
  · constructor
    · rfl
    · have h1 := update_relocated (fractionMulMap p) (fractionMulMap_injective p)
        (multiplicationInput xs factor).stk s hs .input []
      have h2 := update_relocated (fractionMulMap p) (fractionMulMap_injective p)
        (Function.update (multiplicationInput xs factor).stk .input [])
        (Function.update s (fractionMulMap p .input) []) h1 .output (mulBits xs factor).1
      intro k
      change (Function.update (Function.update s (fractionMulMap p .input) [])
        (fractionMulMap p .output) (mulBits xs factor).1) (fractionMulMap p k)=_
      rw [h2]
      cases k <;> simp [multiplicationInput,multiplicationOutput,mulStacks,Function.update]
  · intro k hk
    have h1 := hk .input
    have h2 := hk .output
    change FractionCompareStack.numerator p≠k at h1
    change FractionCompareStack.product p≠k at h2
    simp only [fractionUpdate,Function.update_of_ne (Ne.symm h2),
      Function.update_of_ne (Ne.symm h1)]

def fractionInitialStacks (x y : ComplexityTimeFractions.Fraction) (out : List Bool) :
    FractionCompareStack→List Bool
  | .numerator .ap => x.num.1 | .numerator .an => x.num.2
  | .numerator .bp => y.num.1 | .numerator .bn => y.num.2
  | .denominator false => x.den | .denominator true => y.den
  | .output => out | _ => []

def fractionFinalStacks (x y : ComplexityTimeFractions.Fraction) (out : List Bool) :
    FractionCompareStack→List Bool
  | .denominator false => x.den | .denominator true => y.den
  | .output => out | _ => []

def fractionCrossLeft (x y : ComplexityTimeFractions.Fraction) : ZBits :=
  ((mulBits x.num.1 y.den).1,(mulBits x.num.2 y.den).1)
def fractionCrossRight (x y : ComplexityTimeFractions.Fraction) : ZBits :=
  ((mulBits y.num.1 x.den).1,(mulBits y.num.2 x.den).1)

def fractionProductStacks (x y : ComplexityTimeFractions.Fraction) (out : List Bool) :
    FractionCompareStack→List Bool
  | .product .ap => (fractionCrossLeft x y).1
  | .product .an => (fractionCrossLeft x y).2
  | .product .bp => (fractionCrossRight x y).1
  | .product .bn => (fractionCrossRight x y).2
  | .denominator false => x.den | .denominator true => y.den
  | .output => out | _ => []

lemma fraction_return (p : FractionPhase) (s : FractionCompareStack→List Bool) :
    Step fractionCompareProgram ⟨.multiply p .done,s⟩ ⟨fractionNext p,s⟩ := by
  simp [Step,successors,fractionCompareProgram]

def fractionCompareBudget (x y : ComplexityTimeFractions.Fraction) : ℕ :=
  multiplicationBudget x.num.1.length y.den.length+
  multiplicationBudget x.num.2.length y.den.length+
  multiplicationBudget y.num.1.length x.den.length+
  multiplicationBudget y.num.2.length x.den.length+
  signedCompareTime (fractionCrossLeft x y) (fractionCrossRight x y)+4

set_option maxHeartbeats 1500000 in
theorem fractionCompare_run_raw (x y : ComplexityTimeFractions.Fraction) (out : List Bool) :
    ∃ t ≤ fractionCompareBudget x y,
      Run fractionCompareProgram t
        ⟨.multiply .ap (.initial .read),fractionInitialStacks x y out⟩
        ⟨.compare (.compare .done),fractionFinalStacks x y
          ((zle (fractionCrossLeft x y) (fractionCrossRight x y)).1::out)⟩ := by
  let s0 := fractionInitialStacks x y out
  let s1 := fractionUpdate s0 .ap (mulBits x.num.1 y.den).1
  let s2 := fractionUpdate s1 .an (mulBits x.num.2 y.den).1
  let s3 := fractionUpdate s2 .bp (mulBits y.num.1 x.den).1
  let s4 := fractionUpdate s3 .bn (mulBits y.num.2 x.den).1
  have h1i : ∀ k,s0 (fractionMulMap .ap k)=(multiplicationInput x.num.1 y.den).stk k := by
    intro k;cases k <;> simp [s0,fractionMulMap,fractionInitialStacks,fractionFactor,multiplicationInput,mulStacks]
  obtain ⟨t1,ht1,h1⟩ := fraction_multiply_run .ap x.num.1 y.den s0 h1i
  have h2i : ∀ k,s1 (fractionMulMap .an k)=(multiplicationInput x.num.2 y.den).stk k := by
    intro k;cases k <;> simp [s1,s0,fractionUpdate,fractionMulMap,fractionInitialStacks,fractionFactor,multiplicationInput,mulStacks,Function.update]
  obtain ⟨t2,ht2,h2⟩ := fraction_multiply_run .an x.num.2 y.den s1 h2i
  have h3i : ∀ k,s2 (fractionMulMap .bp k)=(multiplicationInput y.num.1 x.den).stk k := by
    intro k;cases k <;> simp [s2,s1,s0,fractionUpdate,fractionMulMap,fractionInitialStacks,fractionFactor,multiplicationInput,mulStacks,Function.update]
  obtain ⟨t3,ht3,h3⟩ := fraction_multiply_run .bp y.num.1 x.den s2 h3i
  have h4i : ∀ k,s3 (fractionMulMap .bn k)=(multiplicationInput y.num.2 x.den).stk k := by
    intro k;cases k <;> simp [s3,s2,s1,s0,fractionUpdate,fractionMulMap,fractionInitialStacks,fractionFactor,multiplicationInput,mulStacks,Function.update]
  obtain ⟨t4,ht4,h4⟩ := fraction_multiply_run .bn y.num.2 x.den s3 h4i
  have hs4 : s4=fractionProductStacks x y out := by
    funext k
    cases k with
    | numerator p => cases p <;> simp [s4,s3,s2,s1,s0,fractionUpdate,fractionInitialStacks,fractionProductStacks,Function.update]
    | denominator b => cases b <;> simp [s4,s3,s2,s1,s0,fractionUpdate,fractionInitialStacks,fractionProductStacks,Function.update]
    | product p => cases p <;> simp [s4,s3,s2,s1,s0,fractionUpdate,fractionInitialStacks,fractionProductStacks,fractionCrossLeft,fractionCrossRight,Function.update]
    | work k => simp [s4,s3,s2,s1,s0,fractionUpdate,fractionInitialStacks,fractionProductStacks,Function.update]
    | leftSum | rightSum | scratch | output => simp [s4,s3,s2,s1,s0,fractionUpdate,fractionInitialStacks,fractionProductStacks,Function.update]
  have hcmp : Run fractionCompareProgram (signedCompareTime (fractionCrossLeft x y) (fractionCrossRight x y))
      ⟨.compare (.addLeft (.readX false)),s4⟩
      ⟨.compare (.compare .done),fractionFinalStacks x y
        ((zle (fractionCrossLeft x y) (fractionCrossRight x y)).1::out)⟩ := by
    rw [hs4]
    apply (signedCompare_run (fractionCrossLeft x y) (fractionCrossRight x y) out).relocate_exact
      fractionSignedMap FractionCompareState.compare fractionSignedMap_injective fractionSigned_code
    · constructor
      · rfl
      · intro k;cases k <;> rfl
    · constructor
      · rfl
      · intro k;cases k <;> rfl
    · intro k hk
      have ha := hk .ap;have hb := hk .an;have hc := hk .bp;have hd := hk .bn
      have he := hk .leftSum;have hf := hk .rightSum;have hg := hk .scratch;have hh := hk .output
      cases k with
      | numerator p => cases p <;> rfl
      | denominator b => cases b <;> rfl
      | product p => cases p <;> simp_all [fractionSignedMap]
      | work k => rfl
      | leftSum | rightSum | scratch | output => simp_all [fractionSignedMap]
  have h12 := (h1.trans (Run.one (fraction_return .ap s1))).trans h2
  have h123 := (h12.trans (Run.one (fraction_return .an s2))).trans h3
  have h1234 := (h123.trans (Run.one (fraction_return .bp s3))).trans h4
  have hrun := (h1234.trans (Run.one (fraction_return .bn s4))).trans hcmp
  refine ⟨_,?_,hrun⟩
  unfold fractionCompareBudget
  omega

end BalancedAssortments.NPStack
