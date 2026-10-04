import BalancedAssortments.FixedSupportAlgorithm
import BalancedAssortments.FixedSupportAlgorithmRealSamples

namespace BalancedAssortments.FixedSupportAlgorithm

theorem scoreOrder_perm {n : ℕ} (r v : Fin n → ℚ) (ρ : ℚ) :
    List.Perm (scoreOrder r v ρ) (List.finRange n) := List.mergeSort_perm _ _

theorem scoreOrder_nodup {n : ℕ} (r v : Fin n → ℚ) (ρ : ℚ) :
    (scoreOrder r v ρ).Nodup := (scoreOrder_perm r v ρ).nodup_iff.mpr (List.nodup_finRange n)

@[simp] theorem mem_scoreOrder {n : ℕ} (r v : Fin n → ℚ) (ρ : ℚ) (i : Fin n) :
    i ∈ scoreOrder r v ρ := (scoreOrder_perm r v ρ).mem_iff.mpr (List.mem_finRange i)

theorem scoreOrder_sorted {n : ℕ} (r v : Fin n → ℚ) (ρ : ℚ) :
    (scoreOrder r v ρ).Pairwise (fun i j => score r v ρ j ≤ score r v ρ i) := by
  simpa only [scoreOrder, decide_eq_true_eq] using
    (List.sorted_mergeSort (le := fun i j => decide (score r v ρ j ≤ score r v ρ i))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at *
        exact hbc.trans hab)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _) (List.finRange n))

theorem knapsackItems_sorted {n : ℕ} (r v : Fin n → ℚ) (α ρ t : ℚ) :
    (knapsackItems r v α ρ t).Pairwise (fun a b => b.score ≤ a.score) := by
  simpa [knapsackItems, List.pairwise_map] using scoreOrder_sorted r v ρ

noncomputable def realScore {n : ℕ} (r v : Fin n → ℚ) (ρ : ℝ) (i : Fin n) : ℝ :=
  ((r i : ℝ) - ρ) * (v i : ℝ)

/-- Exactly the information a sampled order must preserve at the true real
revenue target: strict positivity and weak pairwise score comparisons. -/
def ScoreCompatible {n : ℕ} (r v : Fin n → ℚ) (ρ : ℝ) (q : ℚ) : Prop :=
  (∀ i, 0 < realScore r v ρ i ↔ 0 < score r v q i) ∧
    ∀ i j, realScore r v ρ i ≤ realScore r v ρ j ↔ score r v q i ≤ score r v q j

/-- Actual real optima, including score ties and zero scores, have a compatible
sample in the executable rational arrangement. -/
theorem scoreSamples_cover_real {n : ℕ} (r v : Fin n → ℚ) {ρ : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ ≤ (revenueUpper r : ℝ)) :
    ∃ q ∈ scoreSamples r v, ScoreCompatible r v ρ q := by
  obtain ⟨q, hq, _, _, hs⟩ := rational_samples_cover_real (revenueUpper_nonneg r)
    (scoreLines r v) (x := ρ) (by simpa only [Rat.cast_zero] using hρ)
  refine ⟨q, hq, ?_, ?_⟩
  · intro i
    have hf : scoreLine r v i ∈ scoreLines r v :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have hh := (hs _ hf).1
    have he : affineValue (((scoreLine r v i).1 : ℝ), ((scoreLine r v i).2 : ℝ)) ρ =
        realScore r v ρ i := by simp [affineValue, scoreLine, realScore]; ring
    rw [he, scoreLine_value] at hh
    simpa only [not_le, Rat.cast_pos] using not_congr hh
  · intro i j
    have hf : scoreDifference r v (i, j) ∈ scoreLines r v :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    have hh := (hs _ hf).1
    have he : affineValue (((scoreDifference r v (i, j)).1 : ℝ),
        ((scoreDifference r v (i, j)).2 : ℝ)) ρ = realScore r v ρ i - realScore r v ρ j := by
      simp [affineValue, scoreDifference, realScore]; ring
    rw [he, scoreDifference_value] at hh
    simpa only [Rat.cast_nonpos, sub_nonpos] using hh

theorem scoreOrder_real_sorted {n : ℕ} (r v : Fin n → ℚ) {ρ : ℝ} {q : ℚ}
    (hq : ScoreCompatible r v ρ q) :
    (scoreOrder r v q).Pairwise (fun i j => realScore r v ρ j ≤ realScore r v ρ i) :=
  (scoreOrder_sorted r v q).imp (fun {i j} hij => (hq.2 j i).mpr hij)

end BalancedAssortments.FixedSupportAlgorithm
