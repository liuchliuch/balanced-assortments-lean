import BalancedAssortments.FixedSupportCostScaleList
import BalancedAssortments.FixedSupportCostEvaluate
import BalancedAssortments.FixedSupportCostMax

namespace BalancedAssortments.FixedSupportCostProgram
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational FixedSupportCostLists FixedSupportCostPoints
open FixedSupportCostOrder FixedSupportCostScaleList FixedSupportCostEvaluate FixedSupportCostMax

/-- Evaluate all rational scale candidates for one sampled score pattern. -/
def pattern {I : Type*} (α K : Fraction) (ps : List (I × Product)) (ρ : Fraction) :
    List (Result I) × ℕ :=
  let rows := ordered ps ρ
  let vs := rows.1.map (fun r => r.product.2)
  let scales := scalePoints α K vs
  let evaluations := mapCost (fun t => evaluateOrdered α K t rows.1) scales.1
  (evaluations.1,rows.2+scales.2+evaluations.2+4*rows.1.length+4)

/-- All candidates, built from actual raw score and scale grids. -/
def candidates {I : Type*} (α K : Fraction) (ps : List (I × Product)) : List (Result I) × ℕ :=
  let scores := scorePoints (ps.map Prod.snd)
  let results := flatMapCost (pattern α K ps) scores.1
  (results.1,scores.2+results.2+4*ps.length+4)

/-- Complete executable exact-support search on raw signed bit fractions.
Canonical rational decoding occurs only in the refinement theorems. -/
def runBits {I : Type*} (α K : Fraction) (ps : List (I × Product)) : Option (Result I) × ℕ :=
  let all := candidates α K ps
  let selected := best all.1
  (selected.1,all.2+selected.2+4)

@[simp] theorem pattern_member {I : Type*} (α K : Fraction) (ps : List (I × Product)) (ρ : Fraction)
    (out : Result I) : out ∈ (pattern α K ps ρ).1 ↔
      ∃ t ∈ (scalePoints α K ((ordered ps ρ).1.map (fun r => r.product.2))).1,
        (evaluateOrdered α K t (ordered ps ρ).1).1 = out := by
  simp [pattern,mapCost_value]

@[simp] theorem candidates_member {I : Type*} (α K : Fraction) (ps : List (I × Product))
    (out : Result I) : out ∈ (candidates α K ps).1 ↔
      ∃ ρ ∈ (scorePoints (ps.map Prod.snd)).1, out ∈ (pattern α K ps ρ).1 := by
  simp only [candidates,flatMapCost_value,List.mem_flatMap]

theorem runBits_member {I : Type*} (α K : Fraction) (ps : List (I × Product))
    {out : Result I} (h : (runBits α K ps).1=some out) : out ∈ (candidates α K ps).1 :=
  best_member _ h

theorem runBits_dominates {I : Type*} (α K : Fraction) (ps : List (I × Product))
    (hv : ∀ out ∈ (candidates α K ps).1,Valid out.2)
    {out : Result I} (h : (runBits α K ps).1=some out) :
    ∀ z ∈ (candidates α K ps).1,decode z.2≤decode out.2 := best_dominates _ hv h

end BalancedAssortments.FixedSupportCostProgram
