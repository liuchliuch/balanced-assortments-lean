import BalancedAssortments.NPStackSignedMultiply

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary ComplexityTimeVerifier
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def signedMulInitial (x y : ZBits) : SignedMulStack → List Bool
  | .xp => x.1 | .xn => x.2 | .yp => y.1 | .yn => y.2 | _ => []
def signedMulFinal (y z : ZBits) : SignedMulStack → List Bool
  | .yp => y.1 | .yn => y.2 | .positive => z.1 | .negative => z.2 | _ => []
def signedMulLeft (x y : ZBits) : ZBits := ((mulBits x.1 y.1).1,(mulBits x.1 y.2).1)
def signedMulRight (x y : ZBits) : ZBits := ((mulBits x.2 y.2).1,(mulBits x.2 y.1).1)
def signedMulProducts (x y : ZBits) : SignedMulStack → List Bool
  | .yp => y.1 | .yn => y.2
  | .product .pp => (mulBits x.1 y.1).1 | .product .nn => (mulBits x.2 y.2).1
  | .product .pn => (mulBits x.1 y.2).1 | .product .np => (mulBits x.2 y.1).1
  | _ => []

lemma signedMul_copy_return (b : Bool) (s : SignedMulStack → List Bool) :
    Step signedMultiplyProgram ⟨.copy b .done,s⟩
      ⟨if b then .multiply .pp (.initial .read) else .copy true .readSource,s⟩ := by
  cases b <;> simp [Step,successors,signedMultiplyProgram]
lemma signedMul_return (p : SignedMulPhase) (s : SignedMulStack → List Bool) :
    Step signedMultiplyProgram ⟨.multiply p .done,s⟩ ⟨signedMulNext p,s⟩ := by
  simp [Step,successors,signedMultiplyProgram]

def signedMultiplyBudget (x y : ZBits) : ℕ :=
  (5*x.1.length+2)+(5*x.2.length+2)+
    multiplicationBudget x.1.length y.1.length+multiplicationBudget x.2.length y.2.length+
    multiplicationBudget x.1.length y.2.length+multiplicationBudget x.2.length y.1.length+
    signedAddTime (signedMulLeft x y) (signedMulRight x y)+6

/-- The signed multiplication is four actual natural multiplication calls,
two input-preserving copies and two actual ripple additions. The fresh left
operand is consumed and the right operand is preserved. -/
theorem signedMultiply_run (x y : ZBits) :
    ∃ t ≤ signedMultiplyBudget x y,
      Run signedMultiplyProgram t ⟨.copy false .readSource,signedMulInitial x y⟩
        ⟨.add (.negative .done),signedMulFinal y (zmul x y).1⟩ := by
  let s0 := signedMulInitial x y
  let s1 := Function.update s0 (.duplicate false) x.1
  let s2 := Function.update s1 (.duplicate true) x.2
  let s3 := signedMulUpdate s2 .pp (mulBits x.1 y.1).1
  let s4 := signedMulUpdate s3 .nn (mulBits x.2 y.2).1
  let s5 := signedMulUpdate s4 .pn (mulBits x.1 y.2).1
  let s6 := signedMulUpdate s5 .np (mulBits x.2 y.1).1
  have hc1i : ∀ k,s0 (signedMulCopyMap false k)=copyStacks x.1 [] [] k := by
    intro k;cases k <;> simp [s0,signedMulCopyMap,signedMulInitial,copyStacks]
  have hc1 := signedMul_copy_run false x.1 s0 hc1i
  have hc2i : ∀ k,s1 (signedMulCopyMap true k)=copyStacks x.2 [] [] k := by
    intro k;cases k <;> simp [s1,s0,signedMulCopyMap,signedMulInitial,copyStacks,Function.update]
  have hc2 := signedMul_copy_run true x.2 s1 hc2i
  have h1i : ∀ k,s2 (signedMulMap .pp k)=(multiplicationInput x.1 y.1).stk k := by
    intro k;cases k <;> simp [s2,s1,s0,signedMulMap,signedMulInput,signedMulFactor,signedMulInitial,multiplicationInput,mulStacks,Function.update]
  obtain ⟨t1,ht1,h1⟩ := signedMul_multiply_run .pp x.1 y.1 s2 h1i
  have h2i : ∀ k,s3 (signedMulMap .nn k)=(multiplicationInput x.2 y.2).stk k := by
    intro k;cases k <;> simp [s3,s2,s1,s0,signedMulUpdate,signedMulMap,signedMulInput,signedMulFactor,signedMulInitial,multiplicationInput,mulStacks,Function.update]
  obtain ⟨t2,ht2,h2⟩ := signedMul_multiply_run .nn x.2 y.2 s3 h2i
  have h3i : ∀ k,s4 (signedMulMap .pn k)=(multiplicationInput x.1 y.2).stk k := by
    intro k;cases k <;> simp [s4,s3,s2,s1,s0,signedMulUpdate,signedMulMap,signedMulInput,signedMulFactor,signedMulInitial,multiplicationInput,mulStacks,Function.update]
  obtain ⟨t3,ht3,h3⟩ := signedMul_multiply_run .pn x.1 y.2 s4 h3i
  have h4i : ∀ k,s5 (signedMulMap .np k)=(multiplicationInput x.2 y.1).stk k := by
    intro k;cases k <;> simp [s5,s4,s3,s2,s1,s0,signedMulUpdate,signedMulMap,signedMulInput,signedMulFactor,signedMulInitial,multiplicationInput,mulStacks,Function.update]
  obtain ⟨t4,ht4,h4⟩ := signedMul_multiply_run .np x.2 y.1 s5 h4i
  have hs6 : s6=signedMulProducts x y := by
    funext k
    cases k with
    | duplicate b => cases b <;> simp [s6,s5,s4,s3,s2,s1,s0,signedMulUpdate,signedMulInput,signedMulInitial,signedMulProducts,Function.update]
    | product p => cases p <;> simp [s6,s5,s4,s3,s2,s1,s0,signedMulUpdate,signedMulInput,signedMulInitial,signedMulProducts,Function.update]
    | work k => simp [s6,s5,s4,s3,s2,s1,s0,signedMulUpdate,signedMulInput,signedMulInitial,signedMulProducts,Function.update]
    | xp | xn | yp | yn | copyScratch | addScratch | positive | negative =>
      simp [s6,s5,s4,s3,s2,s1,s0,signedMulUpdate,signedMulInput,signedMulInitial,signedMulProducts,Function.update]
  have hsum : Run signedMultiplyProgram (signedAddTime (signedMulLeft x y) (signedMulRight x y))
      ⟨.add (.positive (.readX false)),s6⟩
      ⟨.add (.negative .done),signedMulFinal y (zmul x y).1⟩ := by
    rw [hs6]
    apply (signedAdd_run (signedMulLeft x y) (signedMulRight x y)).relocate_exact
      signedMulAddMap SignedMulState.add signedMulAddMap_injective signedMul_add_code
    · refine ⟨rfl,?_⟩
      intro k;cases k <;> rfl
    · refine ⟨rfl,?_⟩
      intro k;cases k <;> rfl
    · intro k hk
      have ha:=hk .ap;have hb:=hk .an;have hc:=hk .bp;have hd:=hk .bn
      have he:=hk .scratch;have hf:=hk .positive;have hg:=hk .negative
      cases k with
      | product p => cases p <;> simp_all [signedMulAddMap]
      | addScratch | positive | negative => simp_all [signedMulAddMap]
      | duplicate b => rfl
      | work k => rfl
      | xp | xn | yp | yn | copyScratch => rfl
  have hcopy := (hc1.trans (Run.one (signedMul_copy_return false s1))).trans hc2
  have ha := (hcopy.trans (Run.one (signedMul_copy_return true s2))).trans h1
  have hab := (ha.trans (Run.one (signedMul_return .pp s3))).trans h2
  have habc := (hab.trans (Run.one (signedMul_return .nn s4))).trans h3
  have habcd := (habc.trans (Run.one (signedMul_return .pn s5))).trans h4
  have hall := (habcd.trans (Run.one (signedMul_return .np s6))).trans hsum
  refine ⟨_,?_,hall⟩
  unfold signedMultiplyBudget
  omega

end BalancedAssortments.NPStack
