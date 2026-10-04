import BalancedAssortments.NPStackSignedMultiplyCorrect

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary ComplexityTimeVerifier

lemma signedMultiplyBudget_bound (x y : ZBits) {W : ℕ} (hx : width x≤W) (hy : width y≤W) :
    signedMultiplyBudget x y≤120*W^2+144*W+51 := by
  have hxp : x.1.length≤W := by unfold width at hx;omega
  have hxn : x.2.length≤W := by unfold width at hx;omega
  have hyp : y.1.length≤W := by unfold width at hy;omega
  have hyn : y.2.length≤W := by unfold width at hy;omega
  have hb {a b : ℕ} (ha : a≤W) (hb : b≤W) : multiplicationBudget a b ≤ multiplicationBudget W W := by
    unfold multiplicationBudget
    gcongr
  have h1 := hb hxp hyp
  have h2 := hb hxn hyn
  have h3 := hb hxp hyn
  have h4 := hb hxn hyp
  have hl : width (signedMulLeft x y)≤3*W := by
    have hp := mulBits_length x.1 y.1
    have hn := mulBits_length x.1 y.2
    dsimp only [width,signedMulLeft]
    omega
  have hr : width (signedMulRight x y)≤3*W := by
    have hp := mulBits_length x.2 y.2
    have hn := mulBits_length x.2 y.1
    dsimp only [width,signedMulRight]
    omega
  have hc := signedAddTime_bound (signedMulLeft x y) (signedMulRight x y)
  have hc' : signedAddTime (signedMulLeft x y) (signedMulRight x y)≤30*W+13 := by omega
  unfold signedMultiplyBudget multiplicationBudget
  unfold multiplicationBudget at h1 h2 h3 h4
  nlinarith only [h1,h2,h3,h4,hc',hxp,hxn]

/-- Genuine finite-stack operational refinement, fresh orientation preserved:
the right operand survives, left operand/workspace are consumed, and exact
raw signed output is produced in a quadratic number of real transitions. -/
theorem signedMultiply_refines (x y : ZBits) {W : ℕ} (hx : width x≤W) (hy : width y≤W) :
    ∃ t≤120*W^2+144*W+51,
      Run signedMultiplyProgram t ⟨.copy false .readSource,signedMulInitial x y⟩
        ⟨.add (.negative .done),signedMulFinal y (zmul x y).1⟩ ∧
      zvalue (zmul x y).1=zvalue x*zvalue y ∧
      width (zmul x y).1≤2*width x+width y+1 := by
  obtain ⟨t,ht,hr⟩ := signedMultiply_run x y
  exact ⟨t,ht.trans (signedMultiplyBudget_bound x y hx hy),hr,zmul_value x y,zmul_width x y⟩

def finiteSignedMultiply : FiniteProgram where
  K := SignedMulStack
  Q := SignedMulState
  program := signedMultiplyProgram

end BalancedAssortments.NPStack
