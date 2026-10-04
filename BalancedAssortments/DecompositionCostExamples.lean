import BalancedAssortments.DecompositionCostRank
import BalancedAssortments.DecompositionCostSelection

namespace BalancedAssortments.Decomposition.CostMachine
open ComplexityTimeBinary

/-- Test decoding is outside the binary execution; it presents its exact output
as ordinary rational atoms for inspection and the existing certificate checker. -/
def inspectBinaryOutput {n : ℕ} (out : Bits × List BitAtom × ℕ) : List (Atom n) :=
  out.2.1.map fun a => ((value a.1 : ℚ) / value out.1, maskSet a.2)

private def testZ : Fin 4 → ℚ := ![9/10, 3/5, 3/10, 1/5]

#eval let r := binaryGreedyRank (2 : ℕ).bits (encodedNumerators testZ) (encodedDenominators testZ)
  (inspectBinaryOutput (n := 4) r, r.2.2)

#guard decide (ValidDecomposition 2 testZ
  (inspectBinaryOutput (binaryGreedyRank (2 : ℕ).bits (encodedNumerators testZ) (encodedDenominators testZ))))

#guard decide (ValidDecomposition 0 (fun _ : Fin 3 => (0 : ℚ))
  (inspectBinaryOutput (binaryGreedyRank (0 : ℕ).bits
    (encodedNumerators (fun _ : Fin 3 => (0 : ℚ)))
    (encodedDenominators (fun _ : Fin 3 => (0 : ℚ))))))

#guard decide (ValidDecomposition 0 (fun _ : Fin 0 => (0 : ℚ))
  (inspectBinaryOutput (binaryGreedyRank (0 : ℕ).bits [] [])))

end BalancedAssortments.Decomposition.CostMachine
