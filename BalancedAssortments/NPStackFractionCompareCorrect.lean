import BalancedAssortments.NPStackFractionCompare

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary ComplexityTimeVerifier
open ComplexityTimeFractions (Fraction decode Valid)

lemma fractionCross_values (x y : Fraction) :
    zvalue (fractionCrossLeft x y)=zvalue x.num*(value y.den : ℤ) ∧
      zvalue (fractionCrossRight x y)=zvalue y.num*(value x.den : ℤ) := by
  simp only [fractionCrossLeft,fractionCrossRight,zvalue,mulBits_value,Nat.cast_mul]
  constructor <;> ring

lemma fractionCross_compare (x y : Fraction) (hx : Valid x) (hy : Valid y) :
    (zle (fractionCrossLeft x y) (fractionCrossRight x y)).1=decide (decode x≤decode y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,zle_correct,(fractionCross_values x y).1,(fractionCross_values x y).2]
  have hxq : (0 : ℚ)<value x.den := by exact_mod_cast hx
  have hyq : (0 : ℚ)<value y.den := by exact_mod_cast hy
  unfold decode
  rw [div_le_div_iff₀ hxq hyq]
  constructor <;> intro h <;> exact_mod_cast h

theorem fractionCompareBudget_bound (x y : Fraction) {W : ℕ}
    (hx : ComplexityTimeFractions.width x≤W) (hy : ComplexityTimeFractions.width y≤W) :
    fractionCompareBudget x y≤120*W^2+140*W+51 := by
  have hxp : x.num.1.length≤W := by unfold ComplexityTimeFractions.width width at hx;omega
  have hxn : x.num.2.length≤W := by unfold ComplexityTimeFractions.width width at hx;omega
  have hxd : x.den.length≤W := by unfold ComplexityTimeFractions.width at hx;omega
  have hyp : y.num.1.length≤W := by unfold ComplexityTimeFractions.width width at hy;omega
  have hyn : y.num.2.length≤W := by unfold ComplexityTimeFractions.width width at hy;omega
  have hyd : y.den.length≤W := by unfold ComplexityTimeFractions.width at hy;omega
  have hb {a b : ℕ} (ha : a≤W) (hb : b≤W) : multiplicationBudget a b≤ multiplicationBudget W W := by
    unfold multiplicationBudget
    gcongr
  have h1 := hb hxp hyd
  have h2 := hb hxn hyd
  have h3 := hb hyp hxd
  have h4 := hb hyn hxd
  have hw1 : width (fractionCrossLeft x y)≤3*W := by
    have hp := mulBits_length x.num.1 y.den
    have hn := mulBits_length x.num.2 y.den
    dsimp only [width,fractionCrossLeft]
    omega
  have hw2 : width (fractionCrossRight x y)≤3*W := by
    have hp := mulBits_length y.num.1 x.den
    have hn := mulBits_length y.num.2 x.den
    dsimp only [width,fractionCrossRight]
    omega
  have hc := signedCompareTime_bound (fractionCrossLeft x y) (fractionCrossRight x y)
  have hc' : signedCompareTime (fractionCrossLeft x y) (fractionCrossRight x y)≤36*W+19 := by omega
  unfold fractionCompareBudget
  unfold multiplicationBudget at h1 h2 h3 h4 ⊢
  nlinarith only [h1,h2,h3,h4,hc']

/-- A finite Boolean-stack program computing comparison of arbitrary unreduced
signed fractions. Denominators and output suffix are preserved; numerator and
all work stacks are consumed. The bound counts concrete transitions. -/
theorem fractionCompare_run (x y : Fraction) (out : List Bool) {W : ℕ}
    (hx : Valid x) (hy : Valid y)
    (hxw : ComplexityTimeFractions.width x≤W) (hyw : ComplexityTimeFractions.width y≤W) :
    ∃ t≤120*W^2+140*W+51,
      Run fractionCompareProgram t
        ⟨.multiply .ap (.initial .read),fractionInitialStacks x y out⟩
        ⟨.compare (.compare .done),fractionFinalStacks x y (decide (decode x≤decode y)::out)⟩ := by
  obtain ⟨t,ht,hr⟩ := fractionCompare_run_raw x y out
  refine ⟨t,ht.trans (fractionCompareBudget_bound x y hxw hyw),?_⟩
  simpa only [fractionCross_compare x y hx hy] using hr

/-- Operational realization agrees with the earlier raw signed-fraction
comparison routine, including noncanonical numerator/denominator encodings. -/
theorem fractionCompare_refines (x y : Fraction) (out : List Bool) {W : ℕ}
    (hx : Valid x) (hy : Valid y)
    (hxw : ComplexityTimeFractions.width x≤W) (hyw : ComplexityTimeFractions.width y≤W) :
    ∃ t≤120*W^2+140*W+51,
      Run fractionCompareProgram t
        ⟨.multiply .ap (.initial .read),fractionInitialStacks x y out⟩
        ⟨.compare (.compare .done),fractionFinalStacks x y ((FixedSupportCostRational.le x y).1::out)⟩ := by
  have he : (FixedSupportCostRational.le x y).1=decide (decode x≤decode y) := by
    apply Bool.eq_iff_iff.mpr
    simpa using FixedSupportCostRational.le_correct x y hx hy
  rw [he]
  exact fractionCompare_run x y out hx hy hxw hyw

def finiteFractionCompare : FiniteProgram where
  K := FractionCompareStack
  Q := FractionCompareState
  program := fractionCompareProgram

end BalancedAssortments.NPStack
