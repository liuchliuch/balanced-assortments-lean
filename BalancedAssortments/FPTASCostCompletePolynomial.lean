import BalancedAssortments.FPTASCostCompleteBound
import BalancedAssortments.FPTASCostPolynomial

namespace BalancedAssortments.FPTASCostComplete.PolicyBudgetPolynomial
open FPTASCostProgram.BudgetPolynomial
variable {T : Type*} [CommSemiring T]

def displayWidth (n b : T) : T := sumWidth n b+3
def displayBudget (n b : T) : T := 4*n+1+sumBudget n b+256*(sumWidth n b+2)^2+4
def reverseBudget (n b c : T) : T := displayBudget n b +
  256*(b+displayWidth n b+1)^2+6+256*(b+2*displayWidth n b+c+1)^2+8+4
def normalizerBudget (n b : T) : T := sumBudget n b+256*(sumWidth n b+2)^2+4
def policyBudget (n b m : T) : T := normalizerBudget n b+(4*m+1)+
  (m*(reverseBudget n b (displayWidth n b)+4)+1)+8

def outputWidth (b n Q : T) : T :=
  let G := gridWidth (7*(b+n+9)+4) Q
  G+kernelWidth n (groupWidth (4*G*(Q+1)) G)+1

def finishBudget (n a b k : T) : T :=
  let M := a+2*b
  let L := 2*n*M
  let W := a+b+4*L+1
  n*(256*(a+b+1)^2+12)+1+
    (8192*(n+1)^2*(L+1)^2+3*n+4*k+2)+policyBudget n W (n+1)+2*n+8

def completeBudget (b n Q : T) : T :=
  salesBudget b n Q+finishBudget n (outputWidth b n Q) b b+n+6

theorem map_completeBudget {S : Type*} [CommSemiring S] (f : T →+* S) (b n q : T) :
    f (completeBudget b n q) = completeBudget (f b) (f n) (f q) := by
  simp only [completeBudget,finishBudget,outputWidth,policyBudget,normalizerBudget,
    reverseBudget,displayBudget,displayWidth,sumBudget,sumWidth,gridWidth,gridQuota,kernelWidth,groupWidth,
    map_salesBudget,map_add,map_mul,map_pow,map_ofNat,map_one,map_zero]

end BalancedAssortments.FPTASCostComplete.PolicyBudgetPolynomial

namespace BalancedAssortments.FPTASCostComplete
open ComplexityTimeBinary KnapsackCostRational FPTASCostSeeds FPTASCostOutput FPTASCostPolicy
open FPTASCostProgram FPTASCostGrid

noncomputable def policyPolynomial : MvPolynomial (Fin 3) ℕ :=
  PolicyBudgetPolynomial.completeBudget (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

theorem policyPolynomial_eval (b n q : ℕ) :
    MvPolynomial.eval ![b,n,q] policyPolynomial = runPolicyBudget b n q := by
  rw [policyPolynomial,PolicyBudgetPolynomial.map_completeBudget]
  simp only [MvPolynomial.eval_X,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rfl

private theorem outputWidth_mono {b b' n n' q q' : ℕ} (hb : b≤b') (hn : n≤n') (hq : q≤q') :
    salesOutputWidth b n q ≤ salesOutputWidth b' n' q' := by
  dsimp only [salesOutputWidth,gridWidth,gridQuota,FPTASCostKernel.kernelWidth,FPTASCostOptions.groupWidth]
  gcongr

private theorem finishBudget_mono {n n' a a' b b' k k' : ℕ}
    (hn : n≤n') (ha : a≤a') (hb : b≤b') (hk : k≤k') :
    finishBudget n a b k ≤ finishBudget n' a' b' k' := by
  dsimp only [finishBudget,policyBudget,normalizerBudget,reverseBudget,displayBudget,displayWidth,
    FPTASCostOutput.sumBudget,FPTASCostOutput.sumWidth]
  gcongr

theorem runPolicyBudget_mono {b b' n n' q q' : ℕ} (hb : b≤b') (hn : n≤n') (hq : q≤q') :
    runPolicyBudget b n q ≤ runPolicyBudget b' n' q' := by
  have hs := salesBudget_mono hb hn hq
  have hf := finishBudget_mono hn (outputWidth_mono hb hn hq) hb hb
  dsimp only [runPolicyBudget]
  omega

/-- Literal multivariate-polynomial bound in ORIGINAL serialized input length
and reciprocal accuracy, including sparse policy recovery and reverse tilt. -/
theorem runPolicyBits_serialized_polynomial {n : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (alpha epsilon : Fraction) (ks : List Bool) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i) :
    let I := (serializeInput alpha epsilon (⟨ks,[true]⟩ : Fraction) (sourceProducts rv)).length
    (runPolicyBits alpha epsilon ks (sourceProducts rv)).2 ≤
      MvPolynomial.eval ![I,I,⌈10/ε⌉₊] policyPolynomial := by
  let capacity : Fraction := ⟨ks,[true]⟩
  obtain ⟨hb,hN,haw,hew,hkw,hpw⟩ := inputSize_bounds alpha epsilon capacity (sourceProducts rv)
  have hh := runPolicyBits_cost d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec
    hb haw hew hkw.1 (fun i => hpw (rv i) (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
  have hI := inputSize_le_serialized alpha epsilon capacity (sourceProducts rv)
  have hNI : n+1 ≤ (serializeInput alpha epsilon capacity (sourceProducts rv)).length := by
    have hp : (sourceProducts rv).length=n+1 := by simp [sourceProducts]
    rw [hp] at hN
    exact hN.trans hI
  dsimp only
  rw [policyPolynomial_eval]
  exact hh.trans (runPolicyBudget_mono hI hNI le_rfl)

end BalancedAssortments.FPTASCostComplete
