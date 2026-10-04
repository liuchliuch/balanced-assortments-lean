import BalancedAssortments.FixedSupportCostProgramBounds
import BalancedAssortments.FixedSupportCostProgramCorrect

namespace BalancedAssortments.FixedSupportCostProgram
open ComplexityTimeFractions (Fraction decode)

/-- Test input construction and presentation are outside the charged program. -/
private def fraction (a b : ℕ) : Fraction := ⟨(a.bits,[]),b.bits⟩

private def testProducts : List (Fin 2 × FixedSupportCostPoints.Product) :=
  [(0,(fraction 4 1,fraction 2 1)),(1,(fraction 1 1,fraction 1 1))]

/-- These expected values follow directly from the model: for alpha=1/2,
(1,1/2) exhausts rank one and has revenue (4+1/2)/(1+1+1/2)=9/5.
For alpha=1, equal shares force (2/3,2/3), with revenue 10/7. -/
private def checkOutput (alpha : Fraction) (w₀ w₁ revenue : ℚ) : IO Unit := do
  let result := runBits alpha (fraction 1 1) testProducts
  let shown := result.1.map (fun out => (out.1.map (fun p => (p.1,decode p.2)),decode out.2))
  IO.println s!"{shown}; charged cost={result.2}"
  let ok := shown.any fun out => out.1.length==2 && out.1.contains (0,w₀) &&
    out.1.contains (1,w₁) && out.2==revenue
  unless ok do throw (IO.userError "fixed-support vector/revenue regression failed")

#eval checkOutput (fraction 1 2) 1 (1/2) (9/5)
#eval checkOutput (fraction 1 1) (2/3) (2/3) (10/7)

#print axioms runBits_cost
#print axioms runBits_width
#print axioms runBits_exact_support

end BalancedAssortments.FixedSupportCostProgram
