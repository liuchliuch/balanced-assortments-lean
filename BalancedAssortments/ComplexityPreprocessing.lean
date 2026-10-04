import BalancedAssortments.ComplexityReal

/-! End-to-end semantic preprocessing: use exactly the retained item type,
so the K=2 constructed instance is legal in the nonempty branch. -/
namespace BalancedAssortments.ComplexityReal
open scoped BigOperators
variable {I : Type*} [DecidableEq I]

/-- A finite instance on a subset is exactly the corresponding full instance
on its subtype, including the subset-sum certificate. -/
theorem subtype_subsetSum_iff (s : Finset I) (a : I → ℕ) (B : ℕ) :
    SubsetSum s a B ↔ SubsetSum Finset.univ (fun i : s => a i.val) B := by
  constructor
  · rintro ⟨T, hT, hsum⟩
    refine ⟨T.subtype (· ∈ s), Finset.subset_univ _, ?_⟩
    rw [Finset.sum_subtype_of_mem a (fun i hi => hT hi)]
    exact hsum
  · rintro ⟨T, _, hsum⟩
    refine ⟨T.map (Function.Embedding.subtype (· ∈ s)), ?_, ?_⟩
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact j.property
    · simpa only [Finset.sum_map, Function.Embedding.subtype_apply] using hsum

/-- The reduction's logical equivalence after actual deletion of oversized items.
There is no assumption that the original items already satisfy aᵢ≤B. -/
theorem preprocessed_compact_reduction_iff (s : Finset I) (a : I → ℕ) (B : ℕ)
    (hB : 0 < B) (ha : ∀ i ∈ s, 0 < a i) :
    SubsetSum s a B ↔ ∃ w : Option (retained s a B) → ℝ,
      CompactDecision (fun i : retained s a B => a i.val) B w := by
  rw [preprocessing, subtype_subsetSum_iff]
  apply compact_reduction_iff _ _ hB
  intro i
  exact ha i.val (Finset.mem_filter.mp i.property).1

/-- All parameters and the K=2 display limit satisfy the source model in the
nonempty preprocessing branch. -/
theorem preprocessed_parameters_legal (s : Finset I) (a : I → ℕ) (B : ℕ)
    (hB : 0 < B) (ha : ∀ i ∈ s, 0 < a i) (hn : (retained s a B).Nonempty) :
    (∀ i : Option (retained s a B),
      0 < attractiveness (fun j : retained s a B => a j.val) B i) ∧
    (∀ i : Option (retained s a B),
      0 < price (fun j : retained s a B => a j.val) B i) ∧
    2 ≤ Fintype.card (Option (retained s a B)) := by
  have hi : ∀ j : retained s a B, 0 < a j.val := fun j =>
    ha j.val (Finset.mem_filter.mp j.property).1
  have hp := constructed_parameters_positive (fun j : retained s a B => a j.val) B hi hB
  haveI : Nonempty (retained s a B) := hn.to_subtype
  exact ⟨hp.1, hp.2, constructed_cardinality_legal⟩

/-- The exact compact problem of the preprocessed model, with its actual revenues,
attractions and balance condition. -/
theorem preprocessed_sales_reduction_iff (s : Finset I) (a : I → ℕ) (B : ℕ)
    (hB : 0 < B) (ha : ∀ i ∈ s, 0 < a i) :
    SubsetSum s a B ↔ ∃ w : Option (retained s a B) → ℝ,
      Sales.CompactFeasible (attractiveness (fun j : retained s a B => a j.val) B) w 2 ∧
      Sales.Balanced 1 w ∧
      3 * (B : ℝ) ≤ Sales.objective (price (fun j : retained s a B => a j.val) B) w := by
  rw [preprocessed_compact_reduction_iff s a B hB ha]
  exact exists_congr (fun w => compactDecision_iff_sales _ _ w)

end BalancedAssortments.ComplexityReal
