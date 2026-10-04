import BalancedAssortments.DecompositionCostInput

namespace BalancedAssortments.Decomposition.CostMachine
open ComplexityTimeBinary

/-- Convert a raw little-endian binary rank to unary quota tokens. This expands
only the rank, not any probability numerator or denominator. The assumption
`K≤n` bounds the output token list by the number of input coordinates. -/
def rankTokens : Bits → List Unit × ℕ
  | [] => ([], 1)
  | b :: bs =>
      let r := rankTokens bs
      let q := r.1 ++ r.1
      (if b then () :: q else q, r.2 + r.1.length + 4)

@[simp] theorem rankTokens_length (ks : Bits) : (rankTokens ks).1.length = value ks := by
  induction ks with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [rankTokens, value, ih] <;> omega

/-- Cost charges every copied unary list cell in each doubling and every binary
input bit inspection. Large unary expansion is never assumed constant time. -/
theorem rankTokens_cost (ks : Bits) :
    (rankTokens ks).2 ≤ 2 * value ks + 4 * ks.length + 1 := by
  induction ks with
  | nil => simp [rankTokens, value]
  | cons b bs ih =>
    cases b <;> simp only [rankTokens, rankTokens_length, value, Bool.toNat_false,
      Bool.toNat_true, List.length_cons] <;> omega

def binaryGreedyRank (ks : Bits) (nums dens : List Bits) : Bits × List BitAtom × ℕ :=
  let q := rankTokens ks
  let p := binaryGreedy q.1.length nums dens
  (p.1, p.2.1, q.2 + q.1.length + p.2.2 + 1)

/-- Raw binary rank parsing preserves both the denominator and the entire output
policy; only the accounted running cost changes. -/
theorem binaryGreedyRank_output (ks : Bits) (nums dens : List Bits) :
    (binaryGreedyRank ks nums dens).1 = (binaryGreedy (value ks) nums dens).1 ∧
    (binaryGreedyRank ks nums dens).2.1 = (binaryGreedy (value ks) nums dens).2.1 := by
  simp [binaryGreedyRank]

/-- Complete running-time bound including rank's binary-to-unary conversion.
All probability arithmetic stays in binary throughout execution. -/
theorem binaryGreedyRank_bit_cost {n L : ℕ} (ks : Bits) (nums dens : List Bits)
    (hn : nums.length = n) (hd : dens.length = n) (hK : value ks ≤ n)
    (hL : bitVolume nums + bitVolume dens ≤ L) :
    (binaryGreedyRank ks nums dens).2.2 ≤
      8192 * (n + 1) ^ 2 * (L + 1) ^ 2 + 3 * n + 4 * ks.length + 2 := by
  have hr := rankTokens_cost ks
  have hp := binaryGreedy_bit_cost (value ks) nums dens hn hd hK hL
  simp only [binaryGreedyRank, rankTokens_length]
  omega

theorem encoded_binaryGreedyRank_bit_cost {n : ℕ} (ks : Bits) (z : Fin n → ℚ)
    (hK : value ks ≤ n) :
    (binaryGreedyRank ks (encodedNumerators z) (encodedDenominators z)).2.2 ≤
      8192 * (n + 1) ^ 2 * (inputRationalBits z + 1) ^ 2 + 3 * n + 4 * ks.length + 2 :=
  binaryGreedyRank_bit_cost ks _ _ (by simp) (by simp) hK (by rfl)

end BalancedAssortments.Decomposition.CostMachine
