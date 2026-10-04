import Mathlib

namespace BalancedAssortments.FixedSupport

variable {ι : Type*} [Fintype ι]

/-- The closed fixed-support polytope, including its zero point. -/
def Feasible (v : ι → ℚ) (α K : ℚ) (w : ι → ℚ) : Prop :=
  (∀ i, 0 ≤ w i ∧ w i ≤ v i) ∧
  (∑ i, w i / v i) ≤ K ∧ (∀ i j, α * w j ≤ w i)

/-- The paper's explicit Charnes--Cooper linear system. -/
def LPFeasible (v : ι → ℚ) (α K : ℚ) (s : ℚ) (y : ι → ℚ) : Prop :=
  s + ∑ i, y i = 1 ∧ (∀ i, 0 ≤ y i ∧ y i ≤ v i * s) ∧
  (∑ i, y i / v i) ≤ K * s ∧ (∀ i j, α * y j ≤ y i) ∧ 0 ≤ s

def revenue (r w : ι → ℚ) : ℚ := (∑ i, r i * w i) / (1 + ∑ i, w i)

theorem denominator_pos (w : ι → ℚ) (h : ∀ i, 0 ≤ w i) :
    0 < 1 + ∑ i, w i := by
  have : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => h i)
  linarith

theorem forward (v w : ι → ℚ) (α K : ℚ) (h : Feasible v α K w) :
    LPFeasible v α K (1 / (1 + ∑ i, w i))
      (fun i => w i / (1 + ∑ i, w i)) := by
  rcases h with ⟨hc, hk, hb⟩
  have hd := denominator_pos w (fun i => (hc i).1)
  refine ⟨?_, ?_, ?_, ?_, le_of_lt (one_div_pos.mpr hd)⟩
  · rw [← Finset.sum_div]
    field_simp
  · intro i
    constructor
    · exact div_nonneg (hc i).1 hd.le
    · simpa [div_eq_mul_inv] using (div_le_div_of_nonneg_right (hc i).2 hd.le)
  · have he : (∑ i, (w i / (1 + ∑ j, w j)) / v i) =
        (∑ i, w i / v i) / (1 + ∑ j, w j) := by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; ring
    rw [he]
    simpa [div_eq_mul_inv] using div_le_div_of_nonneg_right hk hd.le
  · intro i j
    simpa [mul_div_assoc] using div_le_div_of_nonneg_right (hb i j) hd.le

theorem lp_scale_pos (v y : ι → ℚ) (α K s : ℚ)
    (h : LPFeasible v α K s y) : 0 < s := by
  rcases h with ⟨he, hc, _, _, hs⟩
  by_contra hn
  have hz : s = 0 := le_antisymm (le_of_not_gt hn) hs
  have hy : ∀ i, y i = 0 := by
    intro i; have := hc i; simp [hz] at this; linarith
  simp [hz, hy] at he

theorem reverse (v y : ι → ℚ) (α K s : ℚ)
    (h : LPFeasible v α K s y) : Feasible v α K (fun i => y i / s) := by
  have hs := lp_scale_pos v y α K s h
  rcases h with ⟨_, hc, hk, hb, _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨div_nonneg (hc i).1 hs.le, (div_le_iff₀ hs).mpr (hc i).2⟩
  · have he : (∑ i, (y i / s) / v i) = (∑ i, y i / v i) / s := by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; ring
    rw [he]; exact (div_le_iff₀ hs).mpr hk
  · intro i j
    simpa [mul_div_assoc] using div_le_div_of_nonneg_right (hb i j) hs.le

theorem forward_objective (r w : ι → ℚ) :
    (∑ i, r i * (w i / (1 + ∑ j, w j))) = revenue r w := by
  simp [revenue, Finset.sum_div, mul_div_assoc]

theorem reverse_objective (v r y : ι → ℚ) (α K s : ℚ)
    (h : LPFeasible v α K s y) : revenue r (fun i => y i / s) = ∑ i, r i * y i := by
  have hs := lp_scale_pos v y α K s h
  have he := h.1
  change (∑ i, r i * (y i / s)) / (1 + ∑ i, y i / s) = _
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← Finset.sum_div]
  field_simp
  rw [he]
  ring

/-- Positive objective and positive balance force exact support, including at any optimizer. -/
theorem positive_objective_exact_support (r y : ι → ℚ) (α : ℚ)
    (hα : 0 < α) (hy : ∀ i, 0 ≤ y i)
    (hb : ∀ i j, α * y j ≤ y i) (hr : 0 < ∑ i, r i * y i) :
    ∀ i, 0 < y i := by
  have hex : ∃ j, 0 < y j := by
    by_contra hn
    push_neg at hn
    have hz : ∀ j, y j = 0 := fun j => le_antisymm (hn j) (hy j)
    simp [hz] at hr
  obtain ⟨j, hj⟩ := hex
  intro i
  exact lt_of_lt_of_le (mul_pos hα hj) (hb i j)

theorem alpha_one_equal (w : ι → ℚ) (hb : ∀ i j, (1 : ℚ) * w j ≤ w i) :
    ∀ i j, w i = w j := by
  intro i j
  exact le_antisymm (by simpa using hb j i) (by simpa using hb i j)

/-- Algebraic monotonicity underlying the closed-form alpha-one optimum. -/
theorem common_revenue_monotone (R n t u : ℚ) (hR : 0 ≤ R) (hn : 0 ≤ n)
    (ht : 0 ≤ t) (htu : t ≤ u) : t * R / (1 + n*t) ≤ u * R / (1 + n*u) := by
  have hu : 0 ≤ u := le_trans ht htu
  have hd : 0 < 1 + n*t := by positivity
  have he : 0 < 1 + n*u := by positivity
  apply (div_le_div_iff₀ hd he).mpr
  nlinarith [mul_nonneg hR (sub_nonneg.mpr htu)]

/-- The exact common-value cap, with `m` the minimum coordinate attractiveness. -/
theorem common_value_cap (t m K D : ℚ) (hD : 0 < D) :
    (t ≤ m ∧ t * D ≤ K) ↔ t ≤ min m (K / D) := by
  rw [le_min_iff, le_div_iff₀ hD]

/-- Substituting the largest common value proves the displayed formula is optimal. -/
theorem alpha_one_value_optimal (R n m K D t : ℚ)
    (hR : 0 ≤ R) (hn : 0 ≤ n) (hD : 0 < D) (ht : 0 ≤ t)
    (hm : t ≤ m) (hk : t * D ≤ K) :
    t * R / (1 + n*t) ≤
      min m (K/D) * R / (1 + n * min m (K/D)) := by
  apply common_revenue_monotone R n t (min m (K/D)) hR hn ht
  exact (common_value_cap t m K D hD).mp ⟨hm, hk⟩

theorem constant_feasible_iff (v : ι → ℚ) (α K t : ℚ)
    (ht : 0 ≤ t) (hα : α ≤ 1) :
    Feasible v α K (fun _ => t) ↔
      (∀ i, t ≤ v i) ∧ t * (∑ i, 1 / v i) ≤ K := by
  have he : (∑ i, t / v i) = t * (∑ i, 1 / v i) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  constructor
  · rintro ⟨hc, hk, _⟩
    exact ⟨fun i => (hc i).2, by simpa only [he] using hk⟩
  · rintro ⟨hc, hk⟩
    refine ⟨fun i => ⟨ht, hc i⟩, ?_, ?_⟩
    · simpa only [he] using hk
    · intro i j
      nlinarith

theorem constant_revenue (r : ι → ℚ) (t : ℚ) :
    revenue r (fun _ => t) = t * (∑ i, r i) / (1 + Fintype.card ι * t) := by
  unfold revenue
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  ring

/-- A concrete strictly positive rational point of every legal prescribed support. -/
theorem small_positive_feasible (v : ι → ℚ) (α K : ℚ)
    (hv : ∀ i, 0 < v i) (hα : α ≤ 1) (hK : 1 ≤ K) :
    let t := 1 / (1 + ∑ i, 1 / v i)
    0 < t ∧ Feasible v α K (fun _ => t) := by
  dsimp
  have hD : 0 ≤ ∑ i, 1 / v i := Finset.sum_nonneg (fun i _ => le_of_lt (one_div_pos.mpr (hv i)))
  have hd : 0 < 1 + ∑ i, 1 / v i := by linarith
  have ht : 0 < 1 / (1 + ∑ i, 1 / v i) := one_div_pos.mpr hd
  refine ⟨ht, (constant_feasible_iff v α K _ ht.le hα).mpr ⟨?_, ?_⟩⟩
  · intro i
    have hi : 1 / v i ≤ ∑ j, 1 / v j := Finset.single_le_sum
      (fun j _ => le_of_lt (one_div_pos.mpr (hv j))) (Finset.mem_univ i)
    have hmul : 1 ≤ (∑ j, 1 / v j) * v i := (div_le_iff₀ (hv i)).mp hi
    apply (div_le_iff₀ hd).mpr
    nlinarith [hv i]
  · apply le_trans _ hK
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ hd).mpr
    linarith

theorem constant_positive_revenue [Nonempty ι] (r : ι → ℚ) (t : ℚ)
    (hr : ∀ i, 0 < r i) (ht : 0 < t) : 0 < revenue r (fun _ => t) := by
  rw [constant_revenue]
  have hsum : 0 < ∑ i, r i := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have hc : (0 : ℚ) ≤ Fintype.card ι := Nat.cast_nonneg _
  positivity

end BalancedAssortments.FixedSupport

namespace BalancedAssortments.FixedSupport
variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def minimumAttractiveness (v : ι → ℚ) : ℚ :=
  (Finset.univ.image v).min' (Finset.univ_nonempty.image v)

noncomputable def commonOptimum (v : ι → ℚ) (K : ℚ) : ℚ :=
  min (minimumAttractiveness v) (K / ∑ i, 1 / v i)

theorem minimumAttractiveness_le (v : ι → ℚ) (i : ι) : minimumAttractiveness v ≤ v i := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

theorem le_minimumAttractiveness (v : ι → ℚ) (t : ℚ) (h : ∀ i, t ≤ v i) :
    t ≤ minimumAttractiveness v := by
  apply Finset.le_min'
  intro y hy
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
  exact h i

theorem commonOptimum_positive (v : ι → ℚ) (K : ℚ)
    (hv : ∀ i, 0 < v i) (hK : 0 < K) : 0 < commonOptimum v K := by
  unfold commonOptimum
  apply lt_min
  · apply (Finset.lt_min'_iff _ _).mpr
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hv i
  · apply div_pos hK
    exact Finset.sum_pos (fun i _ => one_div_pos.mpr (hv i)) Finset.univ_nonempty

theorem commonOptimum_feasible (v : ι → ℚ) (K : ℚ)
    (hv : ∀ i, 0 < v i) (hK : 0 < K) :
    Feasible v 1 K (fun _ => commonOptimum v K) := by
  have ht := commonOptimum_positive v K hv hK
  apply (constant_feasible_iff v 1 K _ ht.le le_rfl).mpr
  constructor
  · intro i
    exact le_trans (min_le_left _ _) (minimumAttractiveness_le v i)
  · have hd : 0 < ∑ i, 1/v i :=
      Finset.sum_pos (fun i _ => one_div_pos.mpr (hv i)) Finset.univ_nonempty
    exact (le_div_iff₀ hd).mp (min_le_right _ _)

/-- Full fixed-support alpha-one formula: an explicit feasible positive maximizer,
not merely an upper bound conditional on the formula. -/
theorem alpha_one_exact_maximum (v r : ι → ℚ) (K : ℚ)
    (hv : ∀ i, 0 < v i) (hr : ∀ i, 0 ≤ r i) (hK : 0 < K) :
    Feasible v 1 K (fun _ => commonOptimum v K) ∧
    (∀ i : ι, 0 < commonOptimum v K) ∧
    ∀ w, Feasible v 1 K w →
      revenue r w ≤ commonOptimum v K * (∑ i, r i) /
        (1 + Fintype.card ι * commonOptimum v K) := by
  refine ⟨commonOptimum_feasible v K hv hK, fun _ => commonOptimum_positive v K hv hK, ?_⟩
  intro w hw
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  have he : w = fun _ => w i := by
    funext j
    exact alpha_one_equal w hw.2.2 j i
  rw [he, constant_revenue]
  have hf := (constant_feasible_iff v 1 K (w i) (hw.1 i).1 le_rfl).mp (he ▸ hw)
  apply common_revenue_monotone _ _ _ _
    (Finset.sum_nonneg (fun j _ => hr j)) (Nat.cast_nonneg _) (hw.1 i).1
  apply (common_value_cap _ _ _ _
    (Finset.sum_pos (fun j _ => one_div_pos.mpr (hv j)) Finset.univ_nonempty)).mp
  exact ⟨le_minimumAttractiveness v (w i) hf.1, hf.2⟩

end BalancedAssortments.FixedSupport

namespace BalancedAssortments.FixedSupport
variable {ι : Type*} [Fintype ι]

theorem inverse_scale (v y : ι → ℚ) (α K s : ℚ)
    (h : LPFeasible v α K s y) :
    1 / (1 + ∑ i, y i / s) = s := by
  have hs := lp_scale_pos v y α K s h
  have he := h.1
  rw [← Finset.sum_div]
  apply (div_eq_iff (by
    have hn : 0 ≤ (∑ i, y i) / s := div_nonneg
      (Finset.sum_nonneg (fun i _ => (h.2.1 i).1)) hs.le
    linarith : 1 + (∑ i, y i) / s ≠ 0)).mpr
  field_simp
  linarith

theorem inverse_coordinates (v y : ι → ℚ) (α K s : ℚ)
    (h : LPFeasible v α K s y) :
    ∀ i, (y i / s) / (1 + ∑ j, y j / s) = y i := by
  have hs := lp_scale_pos v y α K s h
  have he := inverse_scale v y α K s h
  intro i
  rw [div_eq_mul_one_div, he]
  exact div_mul_cancel₀ _ (ne_of_gt hs)

end BalancedAssortments.FixedSupport
