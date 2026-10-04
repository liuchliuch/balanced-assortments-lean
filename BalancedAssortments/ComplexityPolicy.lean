import BalancedAssortments.ComplexityReal

noncomputable section
namespace BalancedAssortments.ComplexityReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairs (T : Finset ι) (i : T) : Finset (Option ι) := {none, some i.val}
def pairPolicy (a : ι → ℕ) (B : ℕ) (T : Finset ι) (i : T) : ℝ :=
  pairProbability a B T i.val

theorem pairs_cardinality (T : Finset ι) (i : T) : (pairs T i).card = 2 := by
  exact Finset.card_pair (by simp)

theorem pairPolicy_distribution (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (he : ∑ i ∈ T, a i = B) : Sales.Distribution (pairPolicy a B T) := by
  refine ⟨fun i => (pair_probability_positive a B T hB i.val).le, ?_⟩
  unfold pairPolicy
  rw [Finset.sum_coe_sort]
  exact pair_probabilities_sum a B T hB he

theorem pair_denominator (a : ι → ℕ) (B : ℕ) (T : Finset ι) (i : T) :
    Sales.denominator (attractiveness a B) (pairs T) i = 2 + (B : ℝ)/a i.val := by
  simp [Sales.denominator, pairs, attractiveness]
  ring

theorem pairPolicy_anchor_sales (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (ha : ∀ i ∈ T, 0 < a i) (he : ∑ i ∈ T, a i = B) :
    Sales.sales (attractiveness a B) (pairs T) (pairPolicy a B T) none =
      1 / (T.card + 2) := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : (∑ i ∈ T, (a i : ℝ)) = B := by exact_mod_cast he
  simp only [Sales.sales, pairs, Finset.mem_insert, Finset.mem_singleton, true_or,
    if_true, attractiveness, mul_one, pair_denominator]
  change (∑ i : T, pairPolicy a B T i / (2 + (B : ℝ) / a i.val)) = _
  have hx : ∀ i : T, pairPolicy a B T i / (2 + (B : ℝ) / a i.val) =
      (a i.val : ℝ) / (B * (T.card + 2)) := by
    intro i
    have hi : (0 : ℝ) < a i.val := by exact_mod_cast ha i.val i.property
    simpa [pairPolicy, pairProbability, div_eq_mul_inv] using
      pair_anchor_sales B (a i.val) T.card hb hi (Nat.cast_nonneg _)
  simp_rw [hx]
  rw [← Finset.sum_div, Finset.sum_coe_sort T (fun i => (a i : ℝ)), hs]
  field_simp

theorem pairPolicy_item_sales (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (ha : ∀ i ∈ T, 0 < a i) (j : T) :
    Sales.sales (attractiveness a B) (pairs T) (pairPolicy a B T) (some j.val) =
      1 / (T.card + 2) := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hj : (0 : ℝ) < a j.val := by exact_mod_cast ha j.val j.property
  unfold Sales.sales
  rw [Finset.sum_eq_single j]
  · simp only [pairs, Finset.mem_insert, Finset.mem_singleton, Option.some.injEq,
      or_true, if_true, attractiveness, pair_denominator, pairPolicy, pairProbability]
    simpa only [mul_div_assoc] using pair_item_sales B (a j.val) T.card hb hj (Nat.cast_nonneg _)
  · intro i _ hij
    have hi : j.val ≠ i.val := by
      intro he
      exact hij (Subtype.ext he.symm)
    simp [pairs, hi]
  · simp

theorem pairPolicy_inactive_sales (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (j : ι) (hj : j ∉ T) :
    Sales.sales (attractiveness a B) (pairs T) (pairPolicy a B T) (some j) = 0 := by
  unfold Sales.sales
  apply Finset.sum_eq_zero
  intro i _
  have hi : j ≠ i.val := by intro he; exact hj (he.symm ▸ i.property)
  simp [pairs, hi]

theorem pairPolicy_sales_vector (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (ha : ∀ i ∈ T, 0 < a i) (he : ∑ i ∈ T, a i = B) :
    Sales.sales (attractiveness a B) (pairs T) (pairPolicy a B T) =
      selectedVector T true (1 / (T.card + 2)) := by
  funext i
  cases i with
  | none => simpa [selectedVector, indicator] using pairPolicy_anchor_sales a B T hB ha he
  | some i =>
    by_cases hi : i ∈ T
    · simpa [selectedVector, hi] using pairPolicy_item_sales a B T hB ha ⟨i, hi⟩
    · simpa [selectedVector, hi] using pairPolicy_inactive_sales a B T i hi

theorem pairPolicy_outside_sales (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (ha : ∀ i ∈ T, 0 < a i) (he : ∑ i ∈ T, a i = B) :
    Sales.outside (attractiveness a B) (pairs T) (pairPolicy a B T) =
      1 / (T.card + 2) := by
  have h := pairPolicy_anchor_sales a B T hB ha he
  simpa [Sales.outside, Sales.sales, pairs, attractiveness] using h

theorem pairPolicy_revenue (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (ha : ∀ i ∈ T, 0 < a i) (he : ∑ i ∈ T, a i = B) :
    Sales.revenue (price a B)
      (Sales.sales (attractiveness a B) (pairs T) (pairPolicy a B T)) = 3 * B := by
  rw [pairPolicy_sales_vector a B T hB ha he]
  unfold Sales.revenue
  rw [selected_numerator]
  have hs : itemSum a T = B := by unfold itemSum; exact_mod_cast he
  simp only [indicator, ↓reduceIte, mul_one, hs]
  have hc : (T.card : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem pairPolicy_balance (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (ha : ∀ i ∈ T, 0 < a i) (he : ∑ i ∈ T, a i = B) :
    Sales.Balanced 1 (Sales.sales (attractiveness a B) (pairs T) (pairPolicy a B T)) := by
  rw [pairPolicy_sales_vector a B T hB ha he]
  have ht : (0 : ℝ) ≤ 1 / (T.card + 2) := by positivity
  have hh : ∀ i, selectedVector T true (1 / (T.card + 2)) i = 0 ∨
      selectedVector T true (1 / (T.card + 2)) i = 1 / (T.card + 2) := by
    intro i
    cases i with
    | none => simp [selectedVector, indicator]
    | some i => by_cases hi : i ∈ T <;> simp [selectedVector, hi]
  intro i
  rcases hh i with hi | hi
  · exact Or.inl hi
  · right
    intro j
    rcases hh j with hj | hj <;> simp only [one_mul, hi, hj] <;> linarith

/-- The displayed probabilities really define a feasible MNL policy attaining
exactly the target, with every displayed assortment of cardinality two. -/
theorem explicit_policy_witness (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (ha : ∀ i ∈ T, 0 < a i) (he : ∑ i ∈ T, a i = B) :
    Sales.Distribution (pairPolicy a B T) ∧
    (∀ i : T, (pairs T i).card ≤ 2) ∧
    Sales.Balanced 1 (Sales.sales (attractiveness a B) (pairs T) (pairPolicy a B T)) ∧
    Sales.revenue (price a B)
      (Sales.sales (attractiveness a B) (pairs T) (pairPolicy a B T)) = 3 * B := by
  exact ⟨pairPolicy_distribution a B T hB he,
    fun i => (pairs_cardinality T i).le,
    pairPolicy_balance a B T hB ha he,
    pairPolicy_revenue a B T hB ha he⟩

/-- Reverse soundness holds for an arbitrary randomized assortment policy, not
only for the explicit pair policies used by the forward reduction. -/
theorem arbitrary_policy_sound {A : Type*} [Fintype A]
    (a : ι → ℕ) (B : ℕ) (hB : 0 < B) (ha : ∀ i, 0 < a i)
    (S : A → Finset (Option ι)) (q : A → ℝ)
    (hq : Sales.Distribution q) (hK : ∀ j, (S j).card ≤ 2)
    (hb : Sales.Balanced 1 (Sales.sales (attractiveness a B) S q))
    (hr : 3 * (B : ℝ) ≤ Sales.revenue (price a B) (Sales.sales (attractiveness a B) S q)) :
    SubsetSum Finset.univ a B := by
  have hv := (constructed_parameters_positive a B ha hB).1
  obtain ⟨w, hw, hs⟩ := Sales.policy_to_compact (attractiveness a B) hv S hq 2 hK
  apply (compact_reduction_iff a B hB ha).mpr
  refine ⟨w, (compactDecision_iff_sales a B w).mpr ⟨hw, ?_, ?_⟩⟩
  · rw [hs] at hb
    exact (Sales.compact_balance 1 w (fun i => (hw.1 i).1)).mp hb
  · rw [hs, Sales.compact_revenue] at hr
    exact hr

end BalancedAssortments.ComplexityReal

namespace BalancedAssortments.ComplexityReal

/-- The fixed two-product branch is a no-instance in the original policy model,
regardless of which legal assortments its distribution uses. -/
theorem fixed_no_policy {A : Type*} [Fintype A]
    (S : A → Finset (Fin 2)) (q : A → ℝ) (hq : Sales.Distribution q) :
    Sales.revenue (fun _ : Fin 2 => 1) (Sales.sales (fun _ : Fin 2 => 1) S q) < 2 := by
  have ht := Sales.sales_total_probability (fun _ : Fin 2 => (1 : ℝ))
    (fun _ => by norm_num) S hq
  have hp := Sales.outside_pos (fun _ : Fin 2 => (1 : ℝ))
    (fun _ => by norm_num) S hq
  simp only [Sales.revenue, one_mul]
  linarith

end BalancedAssortments.ComplexityReal
