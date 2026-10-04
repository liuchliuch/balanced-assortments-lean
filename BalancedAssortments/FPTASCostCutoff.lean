import BalancedAssortments.FPTASCostCandidate
import BalancedAssortments.ComplexityTimeCeil
import BalancedAssortments.DecompositionCostRank

/-! Charged construction and structural consumption of the DP state-index quota.
No decoded unbounded Nat arithmetic is executed by these routines. -/
namespace BalancedAssortments.FPTASCostCutoff
open ComplexityTimeBinary KnapsackCostRational

def cutoffFuel (count : List Bool) (δ : Fraction) : List Unit × ℕ :=
  let bits := ComplexityTimeCeil.cutoff count δ
  let fuel := Decomposition.CostMachine.rankTokens bits.1
  (fuel.1,bits.2+fuel.2+4)

theorem cutoffFuel_length (count : List Bool) {δ : Fraction} (hd : 0 < δ.decode) :
    (cutoffFuel count δ).1.length = value count * ⌈(value count:ℚ)/δ.decode⌉₊ := by
  simp only [cutoffFuel,Decomposition.CostMachine.rankTokens_length,ComplexityTimeCeil.cutoff_value count hd]

theorem cutoff_length {count : List Bool} {δ : Fraction} {b : ℕ}
    (hn : count.length ≤ b) (hb : 1 ≤ b) (hd : δ.Width b) :
    (ComplexityTimeCeil.cutoff count δ).1.length ≤ 5*b+2 := by
  have hc : (⟨count,[true]⟩ : Fraction).Width b := ⟨hn,by simpa using hb⟩
  have hh := ComplexityTimeCeil.ceilRatio_length hc hd
  have hm := mulBits_length count (ComplexityTimeCeil.ceilRatio ⟨count,[true]⟩ δ).1
  dsimp only [ComplexityTimeCeil.cutoff]
  omega

theorem cutoffFuel_cost {count : List Bool} {δ : Fraction} {b : ℕ}
    (hn : count.length ≤ b) (hb : 1 ≤ b) (hd : δ.Width b) (hdp : 0 < δ.decode) :
    (cutoffFuel count δ).2 ≤ 16384*(b+1)^2 +
      2*(value count*⌈(value count:ℚ)/δ.decode⌉₊)+4*(5*b+2)+5 := by
  have hc := ComplexityTimeCeil.cutoff_cost hn hb hd
  have ht := Decomposition.CostMachine.rankTokens_cost (ComplexityTimeCeil.cutoff count δ).1
  have hl := cutoff_length hn hb hd
  rw [ComplexityTimeCeil.cutoff_value count hdp] at ht
  simp only [cutoffFuel]
  omega

/-- Counter generation consumes unary quota tokens, incrementing binary counter
contents using the certified ripple-carry routine. -/
def scoreTokens : List Unit → List Bool → List (List Bool) × ℕ
  | [], _ => ([],1)
  | _::fuel, x =>
      let next := addCarry x [true] false
      let rest := scoreTokens fuel next.1
      (x::rest.1,next.2+rest.2+4)

theorem scoreTokens_eq (fuel : List Unit) (x : List Bool) :
    scoreTokens fuel x = KnapsackCostRange.rangeFrom fuel.length x := by
  induction fuel generalizing x with
  | nil => rfl
  | cons u fuel ih => simp only [scoreTokens,List.length_cons,KnapsackCostRange.rangeFrom,ih]

def tableTokens (cap : Fraction) (cutoff : List Unit) (groups : List (List KnapsackCostState.Item)) :
    List KnapsackCostState.State × ℕ :=
  let scores := scoreTokens (()::cutoff) []
  let rows := KnapsackCostState.runRows cap scores.1 [KnapsackCostState.initial] groups
  (rows.1,scores.2+rows.2+8)

theorem tableTokens_eq (cap : Fraction) (cutoff : List Unit) (groups : List (List KnapsackCostState.Item)) :
    tableTokens cap cutoff groups = KnapsackCostState.table cap cutoff.length groups := by
  simp only [tableTokens,scoreTokens_eq,List.length_cons,KnapsackCostState.table,KnapsackCostRange.scoreRange]

def solveTokens (cap : Fraction) (cutoff : List Unit) (groups : List (List KnapsackCostState.Item)) :
    Option KnapsackCostState.State × ℕ :=
  let rows := tableTokens cap cutoff groups
  let result := KnapsackCostState.selectMax rows.1 none
  (result.1,rows.2+result.2+4)

theorem solveTokens_eq (cap : Fraction) (cutoff : List Unit) (groups : List (List KnapsackCostState.Item)) :
    solveTokens cap cutoff groups = KnapsackCostState.solve cap cutoff.length groups := by
  simp only [solveTokens,tableTokens_eq,KnapsackCostState.solve]

def scaledSolveTokens (θ cap : Fraction) (cutoff : List Unit) (groups : List (List KnapsackCostState.Item)) :
    Option KnapsackCostState.State × ℕ :=
  let prep := KnapsackCostState.prepareGroups θ groups
  let result := solveTokens cap cutoff prep.1
  (result.1,prep.2+result.2+4)

theorem scaledSolveTokens_eq (θ cap : Fraction) (cutoff : List Unit) (groups : List (List KnapsackCostState.Item)) :
    scaledSolveTokens θ cap cutoff groups = KnapsackCostState.scaledSolve θ cap cutoff.length groups := by
  simp only [scaledSolveTokens,solveTokens_eq,KnapsackCostState.scaledSolve]

def coreTokens (δ count cap : Fraction) (cutoff : List Unit) (groups : List (List KnapsackCostState.Item)) :
    Option KnapsackCostState.State × ℕ :=
  let maximum := FPTASCostKernel.maxProfitBits groups
  let test := compare FPTASCostKernel.zero maximum.1
  if test.1 = .lt then
    let θ := FPTASCostSeeds.scaleBase δ maximum.1 count
    let result := scaledSolveTokens θ.1 cap cutoff groups
    (result.1,maximum.2+test.2+θ.2+result.2+8)
  else (none,maximum.2+test.2+4)

theorem coreTokens_eq (δ count cap : Fraction) (cutoff : List Unit) (groups : List (List KnapsackCostState.Item)) :
    coreTokens δ count cap cutoff groups = FPTASCostKernel.core δ count cap cutoff.length groups := by
  simp only [coreTokens,scaledSolveTokens_eq,FPTASCostKernel.core]

end BalancedAssortments.FPTASCostCutoff
