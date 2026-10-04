import Mathlib
import BalancedAssortments.Sales

noncomputable section

namespace BalancedAssortments.ComplexityReal

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
theorem fixed_no_instance (w₁ w₂ : ℝ) (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂) :
    (w₁+w₂)/(1+w₁+w₂) < 2 := by
  have hd : 0 < 1+w₁+w₂ := by linarith
  apply (div_lt_iff₀ hd).mpr
  linarith

/-- Indicator used for the anchor. -/
def indicator (anchor : Bool) : ℝ := if anchor then 1 else 0

def itemSum (a : ι → ℕ) (T : Finset ι) : ℝ := ∑ i ∈ T, (a i : ℝ)

/-- Actual attractiveness and revenue of products in the reduction. -/
def attractiveness (a : ι → ℕ) (B : ℕ) : Option ι → ℝ
  | none => 1
  | some i => (B : ℝ) / a i

def price (a : ι → ℕ) (B : ℕ) : Option ι → ℝ
  | none => 5 * B
  | some i => 3 * B + a i

/-- An equal-sales witness for the constructed instance; objective is the actual
fractional revenue on the selected item set and optional anchor. -/
def ReductionWitness (a : ι → ℕ) (B : ℕ) (s T : Finset ι)
    (anchor : Bool) (t : ℝ) : Prop :=
  T ⊆ s ∧ 0 ≤ t ∧ (anchor = true → t ≤ 1) ∧
  (∀ i ∈ T, t ≤ (B : ℝ) / a i) ∧
  t * (indicator anchor + itemSum a T / B) ≤ 2 ∧
  3 * (B : ℝ) ≤
    t * (5 * B * indicator anchor + 3 * B * T.card + itemSum a T) /
      (1 + t * (indicator anchor + T.card))

theorem objective_test (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (anchor : Bool) (t : ℝ) (ht : 0 ≤ t) :
    (3 * (B : ℝ) ≤
      t * (5 * B * indicator anchor + 3 * B * T.card + itemSum a T) /
        (1 + t * (indicator anchor + T.card))) ↔
      3 * (B : ℝ) ≤ t * (2 * B * indicator anchor + itemSum a T) := by
  have hi : 0 ≤ indicator anchor := by cases anchor <;> norm_num [indicator]
  have hc : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hd : 0 < 1 + t * (indicator anchor + T.card) := by positivity
  rw [le_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- No anchor can reach the revenue threshold under the rank budget. -/
theorem anchor_required (B S t : ℝ) (hB : 0 < B)
    (hk : t * (S/B) ≤ 2) (hr : 3*B ≤ t*S) : False := by
  have h := (div_le_iff₀ hB).mp (show t*S/B ≤ 2 by simpa [mul_div_assoc] using hk)
  nlinarith

/-- Sharp reverse soundness: rank, anchor cap, and revenue force the exact target. -/
theorem sharp_soundness (B S t : ℝ) (hB : 0 < B) (hS : 0 ≤ S)
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
    (hB : 0 < B) (anchor : Bool) (t : ℝ)
    (h : ReductionWitness a B s T anchor t) : ∑ i ∈ T, a i = B := by
  rcases h with ⟨_, ht, hc, _, hk, hr⟩
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
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
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : itemSum a T = B := by unfold itemSum; exact_mod_cast he
  refine ⟨hT, by norm_num, by simp, ?_, ?_, ?_⟩
  · intro i hi
    have hai : (0 : ℝ) < a i := by exact_mod_cast ha i (hT hi)
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
def pairProbability (a : ι → ℕ) (B : ℕ) (T : Finset ι) (i : ι) : ℝ :=
  ((B : ℝ) + 2 * a i) / (B * (T.card + 2))

theorem pair_probability_positive (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (i : ι) : 0 < pairProbability a B T i := by
  unfold pairProbability
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  positivity

theorem pair_probabilities_sum (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (hB : 0 < B) (he : ∑ i ∈ T, a i = B) :
    ∑ i ∈ T, pairProbability a B T i = 1 := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hc : (T.card : ℝ) + 2 ≠ 0 := by positivity
  have hs : ∑ i ∈ T, (a i : ℝ) = (B : ℝ) := by exact_mod_cast he
  simp only [pairProbability, ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hs]
  field_simp

/-- Each pair's conditional item sales times its policy mass. -/
theorem pair_item_sales (B a k : ℝ) (hB : 0 < B) (ha : 0 < a) (hk : 0 ≤ k) :
    ((B+2*a)/(B*(k+2))) * ((B/a)/(2+B/a)) = 1/(k+2) := by
  have h₁ : B ≠ 0 := ne_of_gt hB
  have h₂ : a ≠ 0 := ne_of_gt ha
  have h₃ : k+2 ≠ 0 := by positivity
  have h₄ : 2*a+B ≠ 0 := by positivity
  field_simp
  ring

/-- Each pair's outside/anchor sales times its policy mass. -/
theorem pair_anchor_sales (B a k : ℝ) (hB : 0 < B) (ha : 0 < a) (hk : 0 ≤ k) :
    ((B+2*a)/(B*(k+2))) * (1/(2+B/a)) = a/(B*(k+2)) := by
  have h₁ : B ≠ 0 := ne_of_gt hB
  have h₂ : a ≠ 0 := ne_of_gt ha
  have h₃ : k+2 ≠ 0 := by positivity
  have h₄ : 2*a+B ≠ 0 := by positivity
  field_simp
  ring

end BalancedAssortments.ComplexityReal


namespace BalancedAssortments.ComplexityReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def selectedVector (T : Finset ι) (anchor : Bool) (t : ℝ) : Option ι → ℝ
  | none => indicator anchor * t
  | some i => if i ∈ T then t else 0

/-- The compact decision problem, on the actual products of the reduction. -/
def CompactDecision (a : ι → ℕ) (B : ℕ) (w : Option ι → ℝ) : Prop :=
  (∀ i, 0 ≤ w i ∧ w i ≤ attractiveness a B i) ∧
  (∑ i, w i / attractiveness a B i) ≤ 2 ∧
  (∀ i, w i = 0 ∨ ∀ j, w j ≤ w i) ∧
  3 * (B : ℝ) ≤ (∑ i, price a B i * w i) / (1 + ∑ i, w i)

theorem selected_mass (T : Finset ι) (anchor : Bool) (t : ℝ) :
    (∑ i, selectedVector T anchor t i) = t * (indicator anchor + T.card) := by
  rw [Fintype.sum_option]
  simp [selectedVector, Finset.sum_ite_mem]
  ring

theorem selected_rank (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (anchor : Bool) (t : ℝ) :
    (∑ i, selectedVector T anchor t i / attractiveness a B i) =
      t * (indicator anchor + itemSum a T / B) := by
  rw [Fintype.sum_option]
  simp only [selectedVector, attractiveness, div_one, ite_div, zero_div]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]
  have he : (∑ i ∈ T, t / ((B : ℝ) / a i)) = t * (itemSum a T / B) := by
    simp only [itemSum, div_div_eq_mul_div, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

theorem selected_numerator (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (anchor : Bool) (t : ℝ) :
    (∑ i, price a B i * selectedVector T anchor t i) =
      t * (5 * B * indicator anchor + 3 * B * T.card + itemSum a T) := by
  rw [Fintype.sum_option]
  simp only [selectedVector, price, mul_ite, mul_zero]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.sum_mul, itemSum]
  ring

theorem selected_decision (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (ha : ∀ i, 0 < a i) (hB : 0 < B) (anchor : Bool) (t : ℝ)
    (h : ReductionWitness a B Finset.univ T anchor t) :
    CompactDecision a B (selectedVector T anchor t) := by
  rcases h with ⟨_, ht, hc, hi, hk, hr⟩
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | none => cases anchor <;> simp [selectedVector, indicator, attractiveness, ht, hc]
    | some i =>
      have hai : (0 : ℝ) < a i := by exact_mod_cast ha i
      by_cases hm : i ∈ T
      · simpa [selectedVector, attractiveness, hm] using And.intro ht (hi i hm)
      · simp [selectedVector, attractiveness, hm, le_of_lt (div_pos hb hai)]
  · simpa only [selected_rank] using hk
  · intro i
    have hv : ∀ j, selectedVector T anchor t j = 0 ∨ selectedVector T anchor t j = t := by
      intro j
      cases j with
      | none => cases anchor <;> simp [selectedVector, indicator]
      | some j => by_cases hj : j ∈ T <;> simp [selectedVector, hj]
    rcases hv i with hi | hi
    · exact Or.inl hi
    · right
      intro j
      rcases hv j with hj | hj <;> simp [hi, hj, ht]
  · simpa only [selected_numerator, selected_mass] using hr

/-- Alpha-one balance genuinely entails a common positive value; no support
shape is assumed by the reduction soundness argument. -/
theorem common_value_of_balance (w : Option ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hb : ∀ i, w i = 0 ∨ ∀ j, w j ≤ w i)
    (hn : ∃ i, w i ≠ 0) : ∃ t > 0, ∀ i, w i = 0 ∨ w i = t := by
  obtain ⟨j, hj⟩ := hn
  refine ⟨w j, lt_of_le_of_ne (hw j) (Ne.symm hj), ?_⟩
  have hjb := (hb j).resolve_left hj
  intro i
  rcases hb i with hi | hi
  · exact Or.inl hi
  · by_cases hz : w i = 0
    · exact Or.inl hz
    · exact Or.inr (le_antisymm (hjb i) (hi j))

theorem decision_has_selected_form (a : ι → ℕ) (B : ℕ) (w : Option ι → ℝ)
    (hB : 0 < B) (h : CompactDecision a B w) :
    ∃ T anchor t, 0 < t ∧ w = selectedVector T anchor t := by
  have hn : ∃ i, w i ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hr := h.2.2.2
    simp [hn] at hr
    have hb : (0 : ℝ) < B := by exact_mod_cast hB
    linarith
  obtain ⟨t, ht, he⟩ := common_value_of_balance w (fun i => (h.1 i).1) h.2.2.1 hn
  let T : Finset ι := Finset.univ.filter (fun i => w (some i) ≠ 0)
  let anchor : Bool := decide (w none ≠ 0)
  refine ⟨T, anchor, t, ht, ?_⟩
  funext i
  cases i with
  | none =>
    by_cases hi : w none = 0
    · simp [selectedVector, indicator, anchor, hi]
    · have hh := (he none).resolve_left hi
      simp [selectedVector, indicator, anchor, hi, hh]
  | some i =>
    by_cases hi : w (some i) = 0
    · simp [selectedVector, T, hi]
    · have hh := (he (some i)).resolve_left hi
      simp [selectedVector, T, hi, hh]

theorem selected_implies_witness (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (anchor : Bool) (t : ℝ) (ht : 0 ≤ t)
    (h : CompactDecision a B (selectedVector T anchor t)) :
    ReductionWitness a B Finset.univ T anchor t := by
  refine ⟨Finset.subset_univ T, ht, ?_, ?_, ?_, ?_⟩
  · intro ha
    simpa [selectedVector, indicator, attractiveness, ha] using (h.1 none).2
  · intro i hi
    simpa [selectedVector, attractiveness, hi] using (h.1 (some i)).2
  · simpa only [selected_rank] using h.2.1
  · simpa only [selected_numerator, selected_mass] using h.2.2.2

/-- The unrestricted compact-vector decision problem is exactly Subset Sum;
this theorem does not assume a common-value or prescribed-support witness. -/
theorem compact_reduction_iff (a : ι → ℕ) (B : ℕ)
    (hB : 0 < B) (ha : ∀ i, 0 < a i) :
    SubsetSum Finset.univ a B ↔ ∃ w, CompactDecision a B w := by
  constructor
  · rintro ⟨T, hT, he⟩
    exact ⟨selectedVector T true 1, selected_decision a B T ha hB true 1
      (reduction_complete a B Finset.univ T hB (fun i _ => ha i) hT he)⟩
  · rintro ⟨w, hw⟩
    obtain ⟨T, anchor, t, ht, he⟩ := decision_has_selected_form a B w hB hw
    rw [he] at hw
    have hwit := selected_implies_witness a B T anchor t ht.le hw
    exact ⟨T, Finset.subset_univ T, reduction_sound a B Finset.univ T hB anchor t hwit⟩

end BalancedAssortments.ComplexityReal

namespace BalancedAssortments.ComplexityReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem compactDecision_iff_sales (a : ι → ℕ) (B : ℕ) (w : Option ι → ℝ) :
    CompactDecision a B w ↔
      Sales.CompactFeasible (attractiveness a B) w 2 ∧
      Sales.Balanced 1 w ∧ 3 * (B : ℝ) ≤ Sales.objective (price a B) w := by
  simp only [CompactDecision, Sales.CompactFeasible, Sales.Balanced, Sales.objective,
    Nat.cast_ofNat, one_mul]
  tauto

theorem constructed_parameters_positive (a : ι → ℕ) (B : ℕ)
    (ha : ∀ i, 0 < a i) (hB : 0 < B) :
    (∀ i, 0 < attractiveness a B i) ∧ (∀ i, 0 < price a B i) := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  constructor <;> intro i <;> cases i with
  | none => simp [attractiveness, price] <;> positivity
  | some i =>
    have hi : (0 : ℝ) < a i := by exact_mod_cast ha i
    simp only [attractiveness, price]
    positivity

theorem constructed_cardinality_legal [Nonempty ι] : 2 ≤ Fintype.card (Option ι) := by
  rw [Fintype.card_option]
  have := Fintype.card_pos (α := ι)
  omega

end BalancedAssortments.ComplexityReal
