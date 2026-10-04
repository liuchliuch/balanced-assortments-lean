import BalancedAssortments.FixedSupportCandidateReal
import BalancedAssortments.FixedSupportAlgorithmPrefixPieces

noncomputable section
namespace BalancedAssortments.FixedSupportAlgorithm
open scoped BigOperators

theorem orderedLabel_ofFn {n : ℕ} (r v : Fin n → ℚ) (q : ℚ) :
    List.ofFn (orderedLabel r v q) = scoreOrder r v q := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [orderedLabel]

theorem sum_orderedLabel {n : ℕ} (r v : Fin n → ℚ) (q : ℚ) (f : Fin n → ℝ) :
    (∑ i, f i) = ∑ k, f (orderedLabel r v q k) := by
  rw [← sum_order_real (scoreOrder r v q) (scoreOrder_perm r v q)]
  rw [← orderedLabel_ofFn r v q, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Prefix caps of the executed list agree with the selected label finset. -/
theorem realItems_prefix_cap_sum {n : ℕ} (r v : Fin n → ℚ) (α q : ℚ) (t : ℝ) (k : ℕ) :
    (((realKnapsackItems r v α q t).take k).map ContinuousKnapsackReal.Item.cap).sum =
      ∑ i ∈ orderedPrefix r v q k,
        FixedSupportKnapsack.cap (fun j => (v j : ℝ)) (α : ℝ) t i := by
  have hn : ((scoreOrder r v q).take k).Nodup := (scoreOrder_nodup r v q).take
  have hh := (List.sum_toFinset
    (FixedSupportKnapsack.cap (fun j => (v j : ℝ)) (α : ℝ) t)
    hn).symm
  simpa [realKnapsackItems, orderedPrefix, List.map_map, Function.comp_def] using hh

/-- Actual greedy coordinates are the exact clipped prefix-budget expressions. -/
theorem realCandidate_increment_prefix {n : ℕ} (r v : Fin n → ℚ) (α K q : ℚ) (t : ℝ)
    (hv : ∀ i, 0 < v i) (hα : 0 < α) (hα1 : α ≤ 1)
    (hdom : FixedSupportKnapsack.ScaleDomain (fun i => (v i : ℝ)) (K : ℝ) t) (k : Fin n) :
    realCandidateIncrements r v α K q t (orderedLabel r v q k) =
      if 0 < score r v q (orderedLabel r v q k) then
        min (FixedSupportKnapsack.cap (fun i => (v i : ℝ)) (α : ℝ) t (orderedLabel r v q k))
          (max (FixedSupportKnapsack.budget (fun i => (v i : ℝ)) (K : ℝ) t -
            ∑ i ∈ orderedPrefix r v q k.val,
              FixedSupportKnapsack.cap (fun j => (v j : ℝ)) (α : ℝ) t i) 0)
      else 0 := by
  have hvR : ∀ i, (0 : ℝ) < (v i : ℝ) := fun i => by exact_mod_cast hv i
  have hαR : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hαR1 : (α : ℝ) ≤ 1 := by exact_mod_cast hα1
  have hc : ∀ item ∈ realKnapsackItems r v α q t, 0 ≤ item.cap := by
    intro item hi
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hi
    exact FixedSupportKnapsack.cap_nonneg _ hvR hαR hαR1 hdom.1 hdom.2.1 i
  have hs : (realKnapsackItems r v α q t).Pairwise (fun i j => j.score ≤ i.score) := by
    have hh := scoreOrder_sorted r v q
    simpa [realKnapsackItems, List.pairwise_map] using hh
  have hk : k.val < (realKnapsackItems r v α q t).length := by
    simpa [realKnapsackItems] using k.isLt
  have hg := ContinuousKnapsackReal.solve_getElem
    (FixedSupportKnapsack.budget (fun i => (v i : ℝ)) (K : ℝ) t)
    (realKnapsackItems r v α q t) hdom.2.2 hc hs k.val hk
  have hidx : (scoreOrder r v q).idxOf (orderedLabel r v q k) = k.val := by
    exact List.idxOf_getElem (scoreOrder_nodup r v q) k.val (by simpa using k.isLt)
  have hit : (realKnapsackItems r v α q t)[k.val] =
      (⟨(score r v q (orderedLabel r v q k) : ℝ),
        FixedSupportKnapsack.cap (fun j => (v j : ℝ)) (α : ℝ) t
          (orderedLabel r v q k)⟩ : ContinuousKnapsackReal.Item) := by
    simp [realKnapsackItems, orderedLabel]
  rw [hit, realItems_prefix_cap_sum] at hg
  simpa only [realCandidateIncrements, recoverReal, hidx, Rat.cast_pos] using hg

/-- The endpoint-analysis objective is exactly the transformed profit of the
executed labeled allocation at every feasible real scale. -/
theorem prefixObjective_eq_candidate {n : ℕ} (r v : Fin n → ℚ) (α K q : ℚ) (ρ t : ℝ)
    (hv : ∀ i, 0 < v i) (hα : 0 < α) (hα1 : α ≤ 1)
    (hdom : FixedSupportKnapsack.ScaleDomain (fun i => (v i : ℝ)) (K : ℝ) t) :
    prefixObjective r v α K q ρ t =
      ∑ i, ((r i : ℝ)-ρ)*realCandidateVector r v α K q t i := by
  unfold realCandidateVector
  rw [FixedSupportKnapsack.transformed_profit_identity]
  change prefixObjective r v α K q ρ t =
    t*(∑ i, ((r i : ℝ)-ρ)) + ∑ i, realScore r v ρ i*realCandidateIncrements r v α K q t i
  rw [sum_orderedLabel r v q (fun i => realScore r v ρ i*realCandidateIncrements r v α K q t i)]
  unfold prefixObjective
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [realCandidate_increment_prefix r v α K q t hv hα hα1 hdom k]

end BalancedAssortments.FixedSupportAlgorithm
