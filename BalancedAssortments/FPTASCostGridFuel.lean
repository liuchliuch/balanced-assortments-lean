import BalancedAssortments.FPTASCostRawHorizon
import BalancedAssortments.DecompositionCostRank

/-! Fully charged unary loop-fuel construction from binary accuracy data and
raw bitstrings. The executable path never decodes an unbounded integer into a
free loop count, and never performs uncharged Nat multiplication to build a grid. -/
namespace BalancedAssortments.FPTASCostGrid
open ComplexityTimeBinary KnapsackCostRational

/-- Construct one token per raw bit by an explicit list traversal. -/
def bitTokens : List Bool → List Unit × ℕ
  | [] => ([],1)
  | _::xs => let r := bitTokens xs; (()::r.1,r.2+4)

lemma bitTokens_length (xs : List Bool) : (bitTokens xs).1.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [bitTokens, ih]

lemma bitTokens_cost (xs : List Bool) : (bitTokens xs).2 = 4*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [bitTokens, ih]; omega

/-- Cartesian replication materializes the entire loop quota and charges every
copied unit-token cell. -/
def multiplyTokens : List Unit → List Unit → List Unit × ℕ
  | [], _ => ([],1)
  | _::xs, ys =>
      let r := multiplyTokens xs ys
      (ys++r.1,r.2+ys.length+4)

lemma multiplyTokens_length (xs ys : List Unit) :
    (multiplyTokens xs ys).1.length = xs.length*ys.length := by
  induction xs with
  | nil => simp [multiplyTokens]
  | cons x xs ih => simp [multiplyTokens, ih]; ring

lemma multiplyTokens_cost (xs ys : List Unit) :
    (multiplyTokens xs ys).2 = xs.length*(ys.length+4)+1 := by
  induction xs with
  | nil => simp [multiplyTokens]
  | cons x xs ih => simp [multiplyTokens, ih]; ring

/-- The actual grid loop consumes tokens directly. -/
def gridTokens : List Unit → Fraction → Fraction → Fraction → List Fraction × ℕ
  | [], _, _, _ => ([],1)
  | _::fuel, current, ratio, cap =>
      let cmp := compare current cap
      let nxt := multiplyFresh current ratio
      let rest := gridTokens fuel nxt.1 ratio cap
      (if cmp.1 = Ordering.gt then rest.1 else current::rest.1,
        cmp.2+nxt.2+rest.2+8)

/-- Refinement includes the running cost, not only the decoded answer. -/
lemma gridTokens_eq (fuel : List Unit) (current ratio cap : Fraction) :
    gridTokens fuel current ratio cap = gridBits fuel.length current ratio cap := by
  induction fuel generalizing current with
  | nil => rfl
  | cons u fuel ih => simp only [gridTokens, List.length_cons, gridBits, ih]

/-- Real fuel construction for the safe raw horizon, including its final endpoint. -/
def rawGridFuel (base delta cap : Fraction) : List Unit × ℕ :=
  let q := reciprocalCeilingBits delta
  let qt := Decomposition.CostMachine.rankTokens q.1
  let bt := bitTokens base.denominator
  let ct := bitTokens cap.numerator
  let widths := bt.1++ct.1
  let result := multiplyTokens qt.1 widths
  (()::result.1, q.2+qt.2+bt.2+ct.2+bt.1.length+result.2+10)

lemma rawGridFuel_length (base delta cap : Fraction) :
    (rawGridFuel base delta cap).1.length = rawHorizon base delta cap+1 := by
  simp [rawGridFuel, multiplyTokens_length, bitTokens_length,
    Decomposition.CostMachine.rankTokens_length, rawHorizon]

/-- The costs for bit-to-token conversion, list copying and replication are all
charged explicitly; Q may scale like inverse epsilon, as an FPTAS allows. -/
theorem rawGridFuel_cost (base delta cap : Fraction) :
    let Q := value (reciprocalCeilingBits delta).1
    let L := base.denominator.length+cap.numerator.length
    (rawGridFuel base delta cap).2 ≤
      (reciprocalCeilingBits delta).2 + Q*(L+6) +
        4*(reciprocalCeilingBits delta).1.length+5*L+14 := by
  have hq := Decomposition.CostMachine.rankTokens_cost (reciprocalCeilingBits delta).1
  simp only [rawGridFuel, bitTokens_cost, bitTokens_length, multiplyTokens_cost,
    List.length_append, Decomposition.CostMachine.rankTokens_length]
  nlinarith

def rawGrid (base delta ratio cap : Fraction) : List Fraction × ℕ :=
  let fuel := rawGridFuel base delta cap
  let result := gridTokens fuel.1 base ratio cap
  (result.1, fuel.2+result.2+4)

/-- End-to-end raw binary grid refinement, including actual charged construction
of the potentially inverse-epsilon-sized iteration list. -/
theorem rawGrid_refines (base delta ratio cap : Fraction)
    (hb : base.Valid) (hd : delta.Valid) (hr : ratio.Valid) (hc : cap.Valid)
    (ha : 0 < base.decode) (hδ : 0 < delta.decode) (hcap : 0 < cap.decode)
    (hRatio : ratio.decode = 1+delta.decode) :
    (rawGrid base delta ratio cap).1.map Fraction.decode =
      Grids.geometricGrid base.decode delta.decode cap.decode
        (GridBounds.gridHorizon base.decode delta.decode cap.decode) := by
  simp only [rawGrid, gridTokens_eq, rawGridFuel_length]
  exact gridBits_raw_refines base delta ratio cap hb hd hr hc ha hδ hcap hRatio

/-- Complete cost for raw-grid construction and evaluation. Every expression on
the right is polynomial in reciprocal accuracy, raw bit lengths and input widths. -/
theorem rawGrid_cost (base delta ratio cap : Fraction) {a b c : ℕ}
    (hb : base.Width a) (hr : ratio.Width b) (hc : cap.Width c) :
    let Q := value (reciprocalCeilingBits delta).1
    let L := base.denominator.length+cap.numerator.length
    let k := Q*L+1
    (rawGrid base delta ratio cap).2 ≤
      (reciprocalCeilingBits delta).2 + Q*(L+6) +
        4*(reciprocalCeilingBits delta).1.length+5*L+14 +
        k*(2048*(a+2*b*k+b+c+2)^2+20)+5 := by
  have hf := rawGridFuel_cost base delta cap
  have hg := gridBits_cost (rawHorizon base delta cap+1) base ratio cap hb hr hc
  simp only [rawGrid, gridTokens_eq, rawGridFuel_length]
  dsimp only at hf ⊢
  unfold rawHorizon at hg ⊢
  omega

end BalancedAssortments.FPTASCostGrid
