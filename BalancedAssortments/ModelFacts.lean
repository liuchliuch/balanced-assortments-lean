import BalancedAssortments.Sales

namespace BalancedAssortments.Sales
open Finset
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I]

theorem balanced_iff_max_coordinate (α : ℝ) (hα : 0 ≤ α) (x : I → ℝ)
    (k : I) (hk : ∀ j, x j ≤ x k) :
    Balanced α x ↔ ∀ i, x i = 0 ∨ α * x k ≤ x i := by
  constructor
  · intro h i
    exact (h i).imp_right (fun hi => hi k)
  · intro h i
    exact (h i).imp_right (fun hi j => (mul_le_mul_of_nonneg_left (hk j) hα).trans hi)

/-- The active purchase catalog is exactly the union of positively weighted
assortments. Positivity of product attractiveness is essential. -/
theorem active_catalog_iff (v : I → ℝ) (hv : ∀ i, 0 < v i)
    (S : A → Finset I) (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) (i : I) :
    0 < sales v S q i ↔ ∃ a, 0 < q a ∧ i ∈ S a := by
  have hd : ∀ a, 0 < denominator v S a := denominator_pos v (fun i => (hv i).le) S
  have hnon : ∀ a, 0 ≤ (if i ∈ S a then q a * v i / denominator v S a else 0) := by
    intro a
    split_ifs
    · exact div_nonneg (mul_nonneg (hq a) (hv i).le) (hd a).le
    · exact le_rfl
  unfold sales
  constructor
  · intro h
    obtain ⟨a, _, ha⟩ := (sum_pos_iff_of_nonneg (fun a _ => hnon a)).mp h
    by_cases hi : i ∈ S a
    · have ha' : 0 < q a * v i := (div_pos_iff_of_pos_right (hd a)).mp (by simpa [hi] using ha)
      exact ⟨a, (mul_pos_iff_of_pos_right (hv i)).mp ha', hi⟩
    · simp [hi] at ha
  · rintro ⟨a, ha, hi⟩
    apply (sum_pos_iff_of_nonneg (fun a _ => hnon a)).mpr
    refine ⟨a, mem_univ a, ?_⟩
    simpa [hi] using div_pos (mul_pos ha (hv i)) (hd a)
end BalancedAssortments.Sales
