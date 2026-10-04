import BalancedAssortments.FPTASCostSerialization

/-! A literal multivariate polynomial for the certified binary sales runtime.
This avoids relying on an informal reading of the arithmetic bound expression. -/
namespace BalancedAssortments.FPTASCostProgram.BudgetPolynomial
variable {T : Type*} [CommSemiring T]

def gridQuota (b Q : T) : T := 2*b*(Q+1)+1

def gridWidth (b Q : T) : T := b+2*b*gridQuota b Q

def gridBudget (b Q : T) : T :=
  (4096*(b+1)^2+48*b+21)+(Q+1)*(2*b+6)+4*(3*b+1)+10*b+14 +
    gridQuota b Q*(2048*(b+2*b*gridQuota b Q+b+b+2)^2+20)+5

def sumWidth (n b : T) : T := 1+n*(2*b+1)

def sumBudget (n b : T) : T := n*(256*(2+n*(2*b+1)+b)^2+4)+1

def revenueWidth (n b : T) : T := sumWidth n (3*b)+2*(sumWidth n b+3)

def revenueBudget (n b : T) : T :=
  (n*(256*(2*b+1)^2+10)+1) + sumBudget n (3*b) + sumBudget n b +
  256*(sumWidth n b+2)^2 + 256*(sumWidth n (3*b)+(sumWidth n b+3)+1)^2 + 20

def groupCost (h b : T) : T :=
  512*(b+1)^2 + (256*(2*b+1)^2+8) + (512*(3*b+1)^2+6) +
    ((h+1)*(2048*(b+2*b*(h+1)+b+3*b+2)^2+20)+1) + 1024*(b+1)^2 +
    ((h+1)*(512*(b+2*b*(h+1)+3*b+1)^2+22)+1) + 12

def groupWidth (h b : T) : T := b+2*b*(h+1)+6*b+1

def autoGroupCost (b Q : T) : T :=
  (256*(2*b+1)^2+8)+(512*(3*b+1)^2+6)+
    (4096*(b+1)^2+100*b+50+Q*(4*b+6))+groupCost (4*b*Q) b+8

def rowCost (R M S W N : T) : T :=
  R * (M * (2048*(W+1)^2+N+10) + 5) + S * (R*M*(1024*(W+1)^2)+5) + 6

def solverBudget (N M S b : T) : T :=
  let W := 1+N*(6*b+1)+2*(S+1)+3*b
  N*(M*(4096*(b+1)^2+8)+5) + 64*(S+1)*(2*(S+1)+1) +
    N*(rowCost (S+1) M (S+1) W N+4) + (S+1)*(16*W+9)+20

def coreCost (N M B b : T) : T :=
  N*M*(512*(b+2)^2+12)+N+5 + 512*(b+2)^2 + 8192*(b+2)^2+32 +
    solverBudget N M B (5*(b+1)) + 8

def kernelWidth (N b : T) : T := 1+N*(30*(b+1)+1)

def candidateCoreCost (N M B b : T) : T :=
  coreCost N M B b +512*(kernelWidth N b+b+1)^2+10

def autoCandidateCost (B N b Q : T) : T :=
  let H := 4*b*(Q+1)
  N*(autoGroupCost b (Q+1)+4)+1 + candidateCoreCost N (H+2) B (groupWidth H b)+4

def seedCost (m b : T) : T :=
  3*(m*(512*(b+1)^2+10)+1) +
  (m*(32768*(b+1)^2+36)+m*(512*(7*b+5)^2+10)+6) +
  (8192*(b+1)^2+32)+(256*(b+b+1)^2+6)+256*(1+b+1)^2+16*m+32

def updateBudget (N b : T) : T :=
  2*revenueBudget N b+512*(revenueWidth N b+1)^2+10

def salesBudget (b N Q : T) : T :=
  let B := b+N+9
  let S := 7*B+4
  let k := gridQuota S Q
  let G := gridWidth S Q
  let C := autoCandidateCost (N^2*Q) N G Q
  let W := G+kernelWidth N (groupWidth (4*G*(Q+1)) G)+1
  (256*(b+5)^2+8+64*(N+1)^2+3+seedCost N B+4) +
    64*(N+1)^2+1 + (16384*(B+1)^2+2*(N^2*Q)+4*(5*B+2)+5) +
    2*gridBudget S Q + (k*(k*(C+5)+5)+1) +
    (8*N^2+8*N+1)+(4*N+1)+((N+k^2)*updateBudget N W+1)+3*N+k^2+20

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem map_salesBudget {S : Type*} [CommSemiring S] (f : T →+* S) (b n q : T) :
    f (salesBudget b n q) = salesBudget (f b) (f n) (f q) := by
  simp only [gridQuota, gridWidth, gridBudget, sumWidth, sumBudget, revenueWidth, revenueBudget, groupCost, groupWidth, autoGroupCost, rowCost, solverBudget, coreCost, kernelWidth, candidateCoreCost, autoCandidateCost, seedCost, updateBudget, salesBudget, map_add, map_mul, map_pow, map_ofNat, map_one, map_zero]

end BalancedAssortments.FPTASCostProgram.BudgetPolynomial

namespace BalancedAssortments.FPTASCostProgram

noncomputable def salesPolynomial : MvPolynomial (Fin 3) ℕ :=
  BudgetPolynomial.salesBudget (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem salesPolynomial_eval (b n q : ℕ) :
    MvPolynomial.eval ![b,n,q] salesPolynomial = salesBudget b n q := by
  rw [salesPolynomial,BudgetPolynomial.map_salesBudget]
  simp only [MvPolynomial.eval_X,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rfl

theorem binary_sales_polynomial_bound (alpha epsilon capacity : KnapsackCostRational.Fraction)
    (products : List FPTASCostSeeds.Product)
    (hav : alpha.Valid) (hev : epsilon.Valid) (hep : 0 < epsilon.decode)
    (hprodv : ∀ p ∈ products,p.1.Valid ∧ p.2.Valid) (hne : products ≠ []) :
    let I := (serializeInput alpha epsilon capacity products).length
    (runSalesBits alpha epsilon capacity products).2 ≤
      MvPolynomial.eval ![I,I,⌈10/epsilon.decode⌉₊] salesPolynomial := by
  dsimp only
  rw [salesPolynomial_eval]
  exact runSalesBits_serialized_cost alpha epsilon capacity products hav hev hep hprodv hne

end BalancedAssortments.FPTASCostProgram
