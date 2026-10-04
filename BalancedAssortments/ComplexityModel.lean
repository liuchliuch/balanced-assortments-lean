import BalancedAssortments.ComplexityReduction

namespace BalancedAssortments.ComplexityReduction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def selectedVector (T : Finset ι) (anchor : Bool) (t : ℚ) : Option ι → ℚ
  | none => indicator anchor * t
  | some i => if i ∈ T then t else 0

/-- The compact decision problem, on the actual products of the reduction. -/
def CompactDecision (a : ι → ℕ) (B : ℕ) (w : Option ι → ℚ) : Prop :=
  (∀ i, 0 ≤ w i ∧ w i ≤ attractiveness a B i) ∧
  (∑ i, w i / attractiveness a B i) ≤ 2 ∧
  (∀ i, w i = 0 ∨ ∀ j, w j ≤ w i) ∧
  3 * (B : ℚ) ≤ (∑ i, price a B i * w i) / (1 + ∑ i, w i)

theorem selected_mass (T : Finset ι) (anchor : Bool) (t : ℚ) :
    (∑ i, selectedVector T anchor t i) = t * (indicator anchor + T.card) := by
  rw [Fintype.sum_option]
  simp [selectedVector, Finset.sum_ite_mem]
  ring

theorem selected_rank (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (anchor : Bool) (t : ℚ) :
    (∑ i, selectedVector T anchor t i / attractiveness a B i) =
      t * (indicator anchor + itemSum a T / B) := by
  rw [Fintype.sum_option]
  simp only [selectedVector, attractiveness, div_one, ite_div, zero_div]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]
  have he : (∑ i ∈ T, t / ((B : ℚ) / a i)) = t * (itemSum a T / B) := by
    simp only [itemSum, div_div_eq_mul_div, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

theorem selected_numerator (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (anchor : Bool) (t : ℚ) :
    (∑ i, price a B i * selectedVector T anchor t i) =
      t * (5 * B * indicator anchor + 3 * B * T.card + itemSum a T) := by
  rw [Fintype.sum_option]
  simp only [selectedVector, price, mul_ite, mul_zero]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.sum_mul, itemSum]
  ring

theorem selected_decision (a : ι → ℕ) (B : ℕ) (T : Finset ι)
    (ha : ∀ i, 0 < a i) (hB : 0 < B) (anchor : Bool) (t : ℚ)
    (h : ReductionWitness a B Finset.univ T anchor t) :
    CompactDecision a B (selectedVector T anchor t) := by
  rcases h with ⟨_, ht, hc, hi, hk, hr⟩
  have hb : (0 : ℚ) < B := by exact_mod_cast hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | none => cases anchor <;> simp [selectedVector, indicator, attractiveness, ht, hc]
    | some i =>
      have hai : (0 : ℚ) < a i := by exact_mod_cast ha i
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
theorem common_value_of_balance (w : Option ι → ℚ)
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

theorem decision_has_selected_form (a : ι → ℕ) (B : ℕ) (w : Option ι → ℚ)
    (hB : 0 < B) (h : CompactDecision a B w) :
    ∃ T anchor t, 0 < t ∧ w = selectedVector T anchor t := by
  have hn : ∃ i, w i ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hr := h.2.2.2
    simp [hn] at hr
    have hb : (0 : ℚ) < B := by exact_mod_cast hB
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
    (anchor : Bool) (t : ℚ) (ht : 0 ≤ t)
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

end BalancedAssortments.ComplexityReduction
