import BalancedAssortments.FPTASCostCodecBound

namespace BalancedAssortments.FPTASCostCodec.FlatPolynomial
open FPTASCostComplete.PolicyBudgetPolynomial
variable {T : Type*} [CommSemiring T]
def width (I Q : T) : T :=
  let a := outputWidth I I Q
  let W := a+I+4*(2*I*(a+2*I))+1
  W+4*displayWidth I W

def budget (I Q : T) : T :=
  100*(I+1)^2+completeBudget I I Q+(8*(I+1)+12*((I+1)*(2*width I Q+I+3))+6)+8

def outputLength (I Q : T) : T := 2*((I+1)*(2*width I Q+I+3))

lemma map_width {S : Type*} [CommSemiring S] (f : T →+* S) (I Q : T) :
    f (width I Q)=width (f I) (f Q) := by
  simp only [width,outputWidth,displayWidth,FPTASCostProgram.BudgetPolynomial.sumWidth,
    FPTASCostProgram.BudgetPolynomial.gridWidth,FPTASCostProgram.BudgetPolynomial.gridQuota,
    FPTASCostProgram.BudgetPolynomial.kernelWidth,FPTASCostProgram.BudgetPolynomial.groupWidth,
    map_add,map_mul,map_ofNat,map_one]

lemma map_budget {S : Type*} [CommSemiring S] (f : T →+* S) (I Q : T) :
    f (budget I Q)=budget (f I) (f Q) := by
  simp only [budget,map_completeBudget,map_width,map_add,map_mul,map_pow,map_ofNat,map_one]

end BalancedAssortments.FPTASCostCodec.FlatPolynomial

namespace BalancedAssortments.FPTASCostCodec
noncomputable def flatPolynomial : MvPolynomial (Fin 2) ℕ :=
  FlatPolynomial.budget (MvPolynomial.X 0) (MvPolynomial.X 1)

lemma width_eq (I Q : ℕ) : FlatPolynomial.width I Q=flatWidth I Q := by
  dsimp only [FlatPolynomial.width,flatWidth,FPTASCostComplete.finishWidth,
    FPTASCostOutput.reverseWidth]
  have ho : FPTASCostComplete.PolicyBudgetPolynomial.outputWidth I I Q = FPTASCostProgram.salesOutputWidth I I Q := rfl
  rw [ho]
  change _+4*FPTASCostOutput.displayWidth I _ = _+2*FPTASCostOutput.displayWidth I _+2*FPTASCostOutput.displayWidth I _
  omega

theorem flatPolynomial_eval (I Q : ℕ) :
    MvPolynomial.eval ![I,Q] flatPolynomial=flatBudget I Q := by
  rw [flatPolynomial,FlatPolynomial.map_budget]
  simp only [MvPolynomial.eval_X,Matrix.cons_val_zero,Matrix.cons_val_one,
    FlatPolynomial.budget,width_eq]
  rfl
open ComplexityTimeBinary KnapsackCostRational FPTASCostSeeds FPTASCostProgram

theorem run_polynomial {n : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (alpha epsilon : Fraction) (ks : List Bool) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i)
    (bits : List Bool)
    (hparse : (parse bits).1 = some ⟨alpha,epsilon,ks,sourceProducts rv⟩) :
    (run bits).2 ≤ MvPolynomial.eval ![bits.length,⌈10/ε⌉₊] flatPolynomial := by
  rw [flatPolynomial_eval]
  exact (run_bounds d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec bits hparse).1

end BalancedAssortments.FPTASCostCodec
