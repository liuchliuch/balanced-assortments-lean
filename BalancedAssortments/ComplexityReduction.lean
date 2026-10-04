import Mathlib

namespace BalancedAssortments.ComplexityReduction

variable {ι : Type*} [DecidableEq ι]

/-- Positive-integer Subset Sum, before preprocessing. -/
def SubsetSum (s : Finset ι) (a : ι → ℕ) (B : ℕ) : Prop :=
  ∃ T ⊆ s, ∑ i ∈ T, a i = B

def retained (s : Finset ι) (a : ι → ℕ) (B : ℕ) : Finset ι :=
  s.filter (fun i => a i ≤ B)

theorem preprocessing (s : Finset ι) (a : ι → ℕ) (B : ℕ) :
    SubsetSum s a B ↔ SubsetSum (retained s a B) a B := by
  constructor
  · rintro ⟨T, hT, he⟩
    refine ⟨T, ?_, he⟩
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨hT hi, ?_⟩
    rw [← he]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hi
  · rintro ⟨T, hT, he⟩
    exact ⟨T, fun i hi => (Finset.mem_filter.mp (hT hi)).1, he⟩

theorem empty_retained_no (s : Finset ι) (a : ι → ℕ) (B : ℕ)
    (hB : 0 < B) (he : retained s a B = ∅) : ¬ SubsetSum s a B := by
  rw [preprocessing, he]
  rintro ⟨T, hT, hsum⟩
  have : T = ∅ := Finset.subset_empty.mp hT
  simp [this] at hsum
  omega

/-- The fixed two-product legal no-instance has revenue strictly below 2. -/
theorem fixed_no_instance (w₁ w₂ : ℚ) (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂) :
    (w₁+w₂)/(1+w₁+w₂) < 2 := by
  have hd : 0 < 1+w₁+w₂ := by linarith
  apply (div_lt_iff₀ hd).mpr
  linarith

/-- Indicator used for the anchor. -/
def indicator (anchor : Bool) : ℚ := if anchor then 1 else 0

def itemSum (a : ι → ℕ) (T : Finset ι) : ℚ := ∑ i ∈ T, (a i : ℚ)

/-- Actual attractiveness and revenue of products in the reduction. -/
def attractiveness (a : ι → ℕ) (B : ℕ) : Option ι → ℚ
  | none => 1
  | some i => (B : ℚ) / a i

def price (a : ι → ℕ) (B : ℕ) : Option ι → ℚ
  | none => 5 * B
  | some i => 3 * B + a i

/-- An equal-sales witness for the constructed instance; objective is the actual
fractional revenue on the selected item set and optional anchor. -/
def ReductionWitness (a : ι → ℕ) (B : ℕ) (s T : Finset ι)
    (anchor : Bool) (t : ℚ) : Prop :=
  T ⊆ s ∧ 0 ≤ t ∧ (anchor = true → t ≤ 1) ∧
  (∀ i ∈ T, t ≤ (B : ℚ) / a i) ∧
  t * (indicator anchor + itemSum a T / B) ≤ 2 ∧
  3 * (B : ℚ) ≤
    t * (5 * B * indicator anchor + 3 * B * T.card + itemSum a T) /
      (1 + t * (indicator anchor + T.card))

theorem objective_test (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (anchor : Bool) (t : ℚ) (ht : 0 ≤ t) :
    (3 * (B : ℚ) ≤
      t * (5 * B * indicator anchor + 3 * B * T.card + itemSum a T) /
        (1 + t * (indicator anchor + T.card))) ↔
      3 * (B : ℚ) ≤ t * (2 * B * indicator anchor + itemSum a T) := by
  have hi : 0 ≤ indicator anchor := by cases anchor <;> norm_num [indicator]
  have hc : (0 : ℚ) ≤ T.card := Nat.cast_nonneg _
  have hd : 0 < 1 + t * (indicator anchor + T.card) := by positivity
  rw [le_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- No anchor can reach the revenue threshold under the rank budget. -/
theorem anchor_required (B S t : ℚ) (hB : 0 < B)
    (hk : t * (S/B) ≤ 2) (hr : 3*B ≤ t*S) : False := by
  have h := (div_le_iff₀ hB).mp (show t*S/B ≤ 2 by simpa [mul_div_assoc] using hk)
  nlinarith

/-- Sharp reverse soundness: rank, anchor cap, and revenue force the exact target. -/
theorem sharp_soundness (B S t : ℚ) (hB : 0 < B) (hS : 0 ≤ S)
    (ht : 0 ≤ t) (hc : t ≤ 1)
    (hk : t * (1 + S/B) ≤ 2) (hr : 3*B ≤ t*(2*B+S)) :
    S = B ∧ t = 1 := by
  have hkb : t * (B+S) ≤ 2*B := by
    have he : t*(1+S/B) = t*(B+S)/B := by field_simp
    rw [he] at hk
    exact (div_le_iff₀ hB).mp hk
  have htB : B ≤ t*B := by nlinarith
  have ht1 : 1 ≤ t := by nlinarith
  have he : t = 1 := le_antisymm hc ht1
  subst t
  constructor <;> nlinarith

theorem reduction_sound (a : ι → ℕ) (B : ℕ) (s T : Finset ι)
    (hB : 0 < B) (anchor : Bool) (t : ℚ)
    (h : ReductionWitness a B s T anchor t) : ∑ i ∈ T, a i = B := by
  rcases h with ⟨_, ht, hc, _, hk, hr⟩
  have hb : (0 : ℚ) < B := by exact_mod_cast hB
  have hs : 0 ≤ itemSum a T := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hr' := (objective_test a B T anchor t ht).mp hr
  have he : itemSum a T = B := by
    cases anchor
    · simp [indicator] at hk hr'
      exact False.elim (anchor_required B (itemSum a T) t hb hk hr')
    · simp [indicator] at hk hr'
      exact (sharp_soundness B (itemSum a T) t hb hs ht (hc rfl) hk hr').1
  unfold itemSum at he
  exact_mod_cast he

theorem reduction_complete (a : ι → ℕ) (B : ℕ) (s T : Finset ι)
    (hB : 0 < B) (ha : ∀ i ∈ s, 0 < a i) (hT : T ⊆ s)
    (he : ∑ i ∈ T, a i = B) : ReductionWitness a B s T true 1 := by
  have hb : (0 : ℚ) < B := by exact_mod_cast hB
  have hs : itemSum a T = B := by unfold itemSum; exact_mod_cast he
  refine ⟨hT, by norm_num, by simp, ?_, ?_, ?_⟩
  · intro i hi
    have hai : (0 : ℚ) < a i := by exact_mod_cast ha i (hT hi)
    apply (le_div_iff₀ hai).mpr
    have hle : a i ≤ B := by
      rw [← he]; exact Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
    norm_num
    exact_mod_cast hle
  · simp only [indicator, Bool.true_eq, ↓reduceIte, one_mul, hs]
    rw [div_self (ne_of_gt hb)]
    norm_num
  · apply (objective_test a B T true 1 (by norm_num)).mpr
    simp [indicator, hs]
    ring_nf
    rfl

theorem reduction_iff (a : ι → ℕ) (B : ℕ) (s : Finset ι)
    (hB : 0 < B) (ha : ∀ i ∈ s, 0 < a i) :
    SubsetSum s a B ↔ ∃ T anchor t, ReductionWitness a B (retained s a B) T anchor t := by
  rw [preprocessing]
  constructor
  · rintro ⟨T, hT, he⟩
    exact ⟨T, true, 1, reduction_complete a B (retained s a B) T hB
      (fun i hi => ha i (Finset.mem_filter.mp hi).1) hT he⟩
  · rintro ⟨T, anchor, t, h⟩
    exact ⟨T, h.1, reduction_sound a B (retained s a B) T hB anchor t h⟩

/-- Rational probabilities of the explicit pair-assortment policy. -/
def pairProbability (a : ι → ℕ) (B : ℕ) (T : Finset ι) (i : ι) : ℚ :=
  ((B : ℚ) + 2 * a i) / (B * (T.card + 2))

theorem pair_probability_positive (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (i : ι) : 0 < pairProbability a B T i := by
  unfold pairProbability
  have hb : (0 : ℚ) < B := by exact_mod_cast hB
  positivity

theorem pair_probabilities_sum (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (he : ∑ i ∈ T, a i = B) :
    ∑ i ∈ T, pairProbability a B T i = 1 := by
  have hb : (B : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hc : (T.card : ℚ) + 2 ≠ 0 := by positivity
  have hs : ∑ i ∈ T, (a i : ℚ) = (B : ℚ) := by exact_mod_cast he
  simp only [pairProbability, ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hs]
  field_simp

/-- Each pair's conditional item sales times its policy mass. -/
theorem pair_item_sales (B a k : ℚ) (hB : 0 < B) (ha : 0 < a) (hk : 0 ≤ k) :
    ((B+2*a)/(B*(k+2))) * ((B/a)/(2+B/a)) = 1/(k+2) := by
  have h₁ : B ≠ 0 := ne_of_gt hB
  have h₂ : a ≠ 0 := ne_of_gt ha
  have h₃ : k+2 ≠ 0 := by positivity
  have h₄ : 2*a+B ≠ 0 := by positivity
  field_simp
  ring

/-- Each pair's outside/anchor sales times its policy mass. -/
theorem pair_anchor_sales (B a k : ℚ) (hB : 0 < B) (ha : 0 < a) (hk : 0 ≤ k) :
    ((B+2*a)/(B*(k+2))) * (1/(2+B/a)) = a/(B*(k+2)) := by
  have h₁ : B ≠ 0 := ne_of_gt hB
  have h₂ : a ≠ 0 := ne_of_gt ha
  have h₃ : k+2 ≠ 0 := by positivity
  have h₄ : 2*a+B ≠ 0 := by positivity
  field_simp
  ring

end BalancedAssortments.ComplexityReduction
