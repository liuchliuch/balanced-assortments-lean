import BalancedAssortments.DecompositionCostRefinement
import BalancedAssortments.DecompositionCostRank

namespace BalancedAssortments.Decomposition.CostMachine
open ComplexityTimeBinary

/-- The raw binary-rank entrypoint has exactly the same mathematical output as
the previously certified rational algorithm. -/
theorem encoded_binaryGreedyRank_eq_greedy {n : ℕ} (ks : Bits) {z : Fin n → ℚ}
    (h : Feasible (value ks) z) :
    let out := binaryGreedyRank ks (encodedNumerators z) (encodedDenominators z)
    interpretGrid (value out.1) (interpretBitAtoms (n := n) out.2.1) = greedy (value ks) z := by
  simpa only [binaryGreedyRank, rankTokens_length] using encoded_binaryGreedy_eq_greedy h

/-- End-to-end sparse decomposition with an actual binary-encoded rank:
exact marginals, strictly positive rational probabilities, legal support sets,
linear support, and polynomial charged bit/list running time. No convex-hull
membership, decomposition certificate, or arithmetic-cost oracle is assumed. -/
theorem binary_sparse_decomposition {n : ℕ} (ks : Bits) {z : Fin n → ℚ}
    (h : Feasible (value ks) z) (hK : value ks ≤ n) :
    let out := binaryGreedyRank ks (encodedNumerators z) (encodedDenominators z)
    let p := interpretGrid (value out.1) (interpretBitAtoms (n := n) out.2.1)
    ValidDecomposition (value ks) z p ∧
      (∀ a ∈ p, 0 < a.1 ∧ a.2.card ≤ value ks) ∧
      out.2.1.length ≤ n + 1 ∧
      out.2.2 ≤ 8192 * (n + 1)^2 * (inputRationalBits z + 1)^2 +
        3 * n + 4 * ks.length + 2 := by
  have he := encoded_binaryGreedyRank_eq_greedy ks h
  refine ⟨?_, ?_, ?_, encoded_binaryGreedyRank_bit_cost ks z hK⟩
  · rw [he]
    exact (greedy_correct h).1
  · rw [he]
    intro a ha
    exact ⟨greedy_positive h a ha, greedy_legal h a ha⟩
  · have hl := (greedy_correct h).2
    rw [← he] at hl
    simpa [interpretGrid, interpretBitAtoms] using hl

end BalancedAssortments.Decomposition.CostMachine
