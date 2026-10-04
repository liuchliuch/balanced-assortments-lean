import BalancedAssortments.FPTASCostInput

/-! Exact list/count bounds for the actual FPTAS loops and DP cutoffs. -/
namespace BalancedAssortments.FPTASCost
open FPTAS

lemma flatMap_length_bound {α β : Type*} (xs : List α) (f : α → List β) (C : ℕ)
    (hf : ∀ x ∈ xs, (f x).length ≤ C) : (xs.flatMap f).length ≤ xs.length*C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (by simp)
    have hi := ih (fun y hy => hf y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

theorem groups_total_options {n B : ℕ} (d : Input n) (δ : ℚ) (h : InputBitBound d δ B)
    {τ ρ : ℚ} (hτ : τ ∈ scales d δ) (hρ : ρ ∈ revenues d δ) :
    (groups d δ τ ρ).flatten.length ≤ (n+1)*(innerHorizon B (GridBounds.blockLength δ)+2) := by
  unfold groups
  change ((List.finRange (n+1)).flatMap (group d δ τ ρ)).length ≤ _
  apply (flatMap_length_bound _ _ _ (fun i _ => (group_bounds d δ h hτ hρ i).1)).trans_eq
  simp

theorem rawCandidates_length {n B : ℕ} (d : Input n) (ε : ℚ)
    (h : InputBitBound d (ε/10) B) :
    (rawCandidates d ε).length ≤ n+1+(outerHorizon B (GridBounds.blockLength (ε/10))+1)^2 := by
  have ht := (scales_bound d (ε/10) h).1
  have hr := (revenues_bound d (ε/10) h).1
  have hf : ∀ τ ∈ scales d (ε/10),
      ((revenues d (ε/10)).filterMap fun ρ => candidateAt d (ε/10) τ ρ).length ≤
        outerHorizon B (GridBounds.blockLength (ε/10))+1 := by
    intro τ _
    exact (List.length_filterMap_le _ _).trans hr
  have hh := flatMap_length_bound (scales d (ε/10)) _ _ hf
  have hm := Nat.mul_le_mul_right (outerHorizon B (GridBounds.blockLength (ε/10))+1) ht
  simp only [rawCandidates, List.length_append, List.length_map, List.length_finRange]
  rw [pow_two]
  omega

/-- The actual profit-state cutoff grows quadratically in product count and
linearly in the reciprocal-accuracy ceiling. -/
theorem state_cutoff_bound (N : ℕ) (δ : ℚ) :
    N * ⌈(N : ℚ) / δ⌉₊ ≤ N^2 * GridBounds.blockLength δ := by
  have hh : ⌈(N : ℚ) / δ⌉₊ ≤ N * GridBounds.blockLength δ := by
    apply Nat.ceil_le.mpr
    have hc := Nat.le_ceil (1/δ)
    have hm := mul_le_mul_of_nonneg_left hc (show (0:ℚ) ≤ N by positivity)
    simpa [GridBounds.blockLength, Nat.cast_mul, mul_div_assoc] using hm
  have hm := Nat.mul_le_mul_left N hh
  simpa [pow_two, Nat.mul_assoc] using hm

/-- All actual candidate-loop counts are polynomial in input bits and 1/epsilon. -/
theorem actual_candidate_count {n : ℕ} (d : Input n) (ε : ℚ) :
    (rawCandidates d ε).length ≤ inputBits d ε+
      (outerHorizon (inputBits d ε+4) ⌈10/ε⌉₊+1)^2 := by
  have h := rawCandidates_length d ε (actual_input_bound d ε)
  rw [precision_parameter] at h
  exact h.trans (Nat.add_le_add_right (product_count_le_inputBits d ε) _)

end BalancedAssortments.FPTASCost
