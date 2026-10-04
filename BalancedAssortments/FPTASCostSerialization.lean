import BalancedAssortments.FPTASCostProgramBound

/-! A concrete self-delimiting raw binary input serialization and an input-size
specialization of the complete sales program's polynomial cost. -/
namespace BalancedAssortments.FPTASCostProgram
open KnapsackCostRational FPTASCostSeeds FPTASCostGrid

def fractionSize (x : Fraction) : ℕ := x.numerator.length+x.denominator.length

def inputSize (alpha epsilon capacity : Fraction) (products : List Product) : ℕ :=
  1+products.length+fractionSize alpha+fractionSize epsilon+fractionSize capacity+
    (products.map (fun rv => fractionSize rv.1+fractionSize rv.2)).sum

lemma nat_member_le_sum {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hh := ih hx
      simp only [List.sum_cons]
      omega

lemma inputSize_bounds (alpha epsilon capacity : Fraction) (products : List Product) :
    1 ≤ inputSize alpha epsilon capacity products ∧
    products.length ≤ inputSize alpha epsilon capacity products ∧
    alpha.Width (inputSize alpha epsilon capacity products) ∧
    epsilon.Width (inputSize alpha epsilon capacity products) ∧
    capacity.Width (inputSize alpha epsilon capacity products) ∧
    ∀ p ∈ products,p.1.Width (inputSize alpha epsilon capacity products) ∧
      p.2.Width (inputSize alpha epsilon capacity products) := by
  have hs : ∀ p ∈ products,fractionSize p.1+fractionSize p.2 ≤
      (products.map (fun rv => fractionSize rv.1+fractionSize rv.2)).sum := by
    intro p hp
    exact nat_member_le_sum (List.mem_map.mpr ⟨p,hp,rfl⟩)
  refine ⟨by unfold inputSize;omega,by unfold inputSize;omega,?_,?_,?_,?_⟩
  · constructor <;> unfold inputSize fractionSize <;> omega
  · constructor <;> unfold inputSize fractionSize <;> omega
  · constructor <;> unfold inputSize fractionSize <;> omega
  · intro p hp
    have hh := hs p hp
    dsimp only [fractionSize] at hh
    constructor <;> constructor <;> unfold inputSize fractionSize <;> omega

/-- Unary length prefix followed by the raw bit string. This is injectively
parsable without an externally supplied word size. -/
def serializeBits (xs : List Bool) : List Bool := List.replicate xs.length true ++ false::xs

def serializeFraction (x : Fraction) : List Bool := serializeBits x.numerator ++ serializeBits x.denominator

def serializeProducts : List Product → List Bool
  | [] => [false]
  | p::ps => true::(serializeFraction p.1 ++ serializeFraction p.2 ++ serializeProducts ps)

def serializeInput (alpha epsilon capacity : Fraction) (products : List Product) : List Bool :=
  serializeFraction alpha ++ serializeFraction epsilon ++ serializeFraction capacity ++ serializeProducts products

lemma serializeBits_length (xs : List Bool) : (serializeBits xs).length = 2*xs.length+1 := by
  simp [serializeBits]; omega
lemma serializeFraction_length (x : Fraction) : (serializeFraction x).length = 2*fractionSize x+2 := by
  simp only [serializeFraction,List.length_append,serializeBits_length,fractionSize]
  omega
lemma serializeProducts_length (products : List Product) :
    (serializeProducts products).length =
      2*(products.map (fun rv => fractionSize rv.1+fractionSize rv.2)).sum+5*products.length+1 := by
  induction products with
  | nil => rfl
  | cons p ps ih =>
    simp only [serializeProducts,List.length_cons,List.length_append,serializeFraction_length,
      List.map_cons,List.sum_cons,ih]
    omega
lemma inputSize_le_serialized (alpha epsilon capacity : Fraction) (products : List Product) :
    inputSize alpha epsilon capacity products ≤ (serializeInput alpha epsilon capacity products).length := by
  simp only [serializeInput,List.length_append,serializeFraction_length,serializeProducts_length,inputSize]
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
lemma salesBudget_mono {b b' N N' Q Q' : ℕ} (hb : b ≤ b') (hn : N ≤ N') (hq : Q ≤ Q') :
    salesBudget b N Q ≤ salesBudget b' N' Q' := by
  dsimp only [salesBudget,gridQuota,gridWidth,gridBudget,FPTASCostCandidate.autoCandidateCost,
    FPTASCostCandidate.candidateCoreCost,FPTASCostKernel.coreCost,FPTASCost.solverBudget,
    KnapsackCostState.rowCost,FPTASCostKernel.kernelWidth,FPTASCostOptions.groupWidth,
    FPTASCostOptions.autoGroupCost,FPTASCostOptions.groupCost,seedCost,updateBudget,
    FPTASCostOutput.revenueBudget,FPTASCostOutput.revenueWidth,FPTASCostOutput.sumWidth,
    FPTASCostOutput.sumBudget]
  gcongr

/-- Complete original-input bit-complexity theorem. I is the length of the
explicit self-delimiting serialization above; no intermediate arithmetic bounds
or operation counts appear as hypotheses. -/
theorem runSalesBits_serialized_cost (alpha epsilon capacity : Fraction) (products : List Product)
    (hav : alpha.Valid) (hev : epsilon.Valid) (hep : 0 < epsilon.decode)
    (hprodv : ∀ p ∈ products,p.1.Valid ∧ p.2.Valid) (hne : products ≠ []) :
    let I := (serializeInput alpha epsilon capacity products).length
    (runSalesBits alpha epsilon capacity products).2 ≤ salesBudget I I ⌈10/epsilon.decode⌉₊ := by
  obtain ⟨hb,hN,ha,he,hk,hp⟩ := inputSize_bounds alpha epsilon capacity products
  have hh := runSalesBits_cost alpha epsilon capacity products hb ha he hk hp hav hev hep hprodv hne
  have hI := inputSize_le_serialized alpha epsilon capacity products
  exact hh.trans (salesBudget_mono hI (hN.trans hI) le_rfl)

end BalancedAssortments.FPTASCostProgram
