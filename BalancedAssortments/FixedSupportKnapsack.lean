import BalancedAssortments.FixedSupportReal

/-! Exact one-scale continuous-knapsack formulation of prescribed-support
optimization. This is a building block for the direct specialized solver;
no general polynomial LP algorithm is assumed. -/
namespace BalancedAssortments.FixedSupportKnapsack
noncomputable section
open Finset
variable {I : Type*} [Fintype I]

def cap (v : I → ℝ) (α t : ℝ) (i : I) : ℝ := min 1 (t / (α * v i)) - t / v i
def budget (v : I → ℝ) (K t : ℝ) : ℝ := K - t * ∑ i, 1 / v i
def reconstruct (v : I → ℝ) (t : ℝ) (y : I → ℝ) : I → ℝ := fun i => t + v i * y i
def increments (v w : I → ℝ) (t : ℝ) : I → ℝ := fun i => (w i - t) / v i

def ScaleFeasible (v : I → ℝ) (α K t : ℝ) (y : I → ℝ) : Prop :=
  0 ≤ t ∧ (∀ i, 0 ≤ y i ∧ y i ≤ cap v α t i) ∧ (∑ i, y i) ≤ budget v K t

/-- Inverse formulas do not use positivity or a solution oracle. -/
theorem reconstruct_increments (v w : I → ℝ) (hv : ∀ i, v i ≠ 0) (t : ℝ) :
    reconstruct v t (increments v w t) = w := by
  funext i
  dsimp [reconstruct, increments]
  field_simp [hv i]
  <;> ring

theorem increments_reconstruct (v y : I → ℝ) (hv : ∀ i, v i ≠ 0) (t : ℝ) :
    increments v (reconstruct v t y) t = y := by
  funext i
  simp [reconstruct, increments, hv i]

theorem cap_identity {α t v : ℝ} (hα : 0 < α) (hv : 0 < v) :
    t + v * (min 1 (t / (α*v)) - t/v) = min v (t/α) := by
  have hm : v * min 1 (t / (α*v)) = min v (t/α) := by
    rw [mul_min_of_nonneg _ _ hv.le]
    congr 1
    · ring
    · field_simp
  calc t + v * (min 1 (t/(α*v)) - t/v) = v * min 1 (t/(α*v)) := by field_simp; ring
       _ = _ := hm

theorem coordinate_iff (v : I → ℝ) (hv : ∀ i, 0 < v i) {α t : ℝ}
    (hα : 0 < α) (y : I → ℝ) (i : I) :
    (0 ≤ y i ∧ y i ≤ cap v α t i) ↔
      t ≤ reconstruct v t y i ∧ reconstruct v t y i ≤ min (v i) (t/α) := by
  have hi := cap_identity (t := t) hα (hv i)
  unfold cap reconstruct
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · nlinarith [mul_nonneg (hv i).le hl]
    · have hm := mul_le_mul_of_nonneg_left hu (hv i).le
      linarith
  · rintro ⟨hl, hu⟩
    constructor
    · nlinarith [hv i]
    · have hm : v i * y i ≤ v i * (min 1 (t/(α*v i)) - t/v i) := by linarith
      exact (mul_le_mul_iff_right₀ (hv i)).mp hm

theorem rank_identity (v y : I → ℝ) (hv : ∀ i, v i ≠ 0) (t : ℝ) :
    (∑ i, reconstruct v t y i / v i) = t * (∑ i, 1/v i) + ∑ i, y i := by
  simp only [reconstruct, add_div, mul_div_cancel_left₀ _ (hv _), Finset.sum_add_distrib]
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

theorem scale_feasible_iff (v : I → ℝ) (hv : ∀ i, 0 < v i) {α K t : ℝ}
    (hα : 0 < α) (y : I → ℝ) :
    ScaleFeasible v α K t y ↔
      0 ≤ t ∧ (∀ i, t ≤ reconstruct v t y i ∧ reconstruct v t y i ≤ min (v i) (t/α)) ∧
      (∑ i, reconstruct v t y i / v i) ≤ K := by
  unfold ScaleFeasible budget
  rw [rank_identity v y (fun i => (hv i).ne') t]
  constructor
  · rintro ⟨ht, hy, hk⟩
    exact ⟨ht, fun i => (coordinate_iff v hv hα y i).mp (hy i), by linarith⟩
  · rintro ⟨ht, hy, hk⟩
    exact ⟨ht, fun i => (coordinate_iff v hv hα y i).mpr (hy i), by linarith⟩

theorem scale_to_fixed (v : I → ℝ) (hv : ∀ i, 0 < v i) {α K t : ℝ}
    (hα : 0 < α) {y : I → ℝ} (hy : ScaleFeasible v α K t y) :
    FixedSupportReal.Feasible v α K (reconstruct v t y) := by
  obtain ⟨ht, hb, hk⟩ := (scale_feasible_iff v hv hα y).mp hy
  refine ⟨fun i => ⟨ht.trans (hb i).1, (le_min_iff.mp (hb i).2).1⟩, hk, ?_⟩
  intro i j
  have hu := (le_div_iff₀ hα).mp (le_min_iff.mp (hb j).2).2
  nlinarith [(hb i).1]

/-- Every closed fixed-support feasible vector has an actual common-scale
continuous-knapsack representation. -/
theorem fixed_to_scale [Nonempty I] (v w : I → ℝ) (hv : ∀ i, 0 < v i)
    {α K : ℝ} (hα : 0 < α) (hw : FixedSupportReal.Feasible v α K w) :
    ∃ t y, ScaleFeasible v α K t y ∧ reconstruct v t y = w := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  let t := α * w j
  let y := increments v w t
  have he : reconstruct v t y = w := reconstruct_increments v w (fun i => (hv i).ne') t
  refine ⟨t, y, ?_, he⟩
  apply (scale_feasible_iff v hv hα y).mpr
  rw [he]
  refine ⟨mul_nonneg hα.le (hw.1 j).1, ?_, hw.2.1⟩
  intro i
  refine ⟨hw.2.2 i j, le_min (hw.1 i).2 ?_⟩
  have het : t / α = w j := by dsimp [t]; field_simp
  rw [het]
  exact hj i (mem_univ i)

/-- Target-revenue profit decomposes into a scale baseline and continuous
knapsack profits with the exact source affine score (r_i-rho)v_i. -/
theorem transformed_profit_identity (r v y : I → ℝ) (ρ t : ℝ) :
    (∑ i, (r i - ρ) * reconstruct v t y i) =
      t * (∑ i, (r i - ρ)) + ∑ i, ((r i - ρ)*v i)*y i := by
  simp only [reconstruct, mul_add, sum_add_distrib, mul_sum]
  congr 1
  · apply sum_congr rfl; intro i _; ring
  · apply sum_congr rfl; intro i _; ring

def ScaleDomain (v : I → ℝ) (K t : ℝ) : Prop :=
  0 ≤ t ∧ (∀ i, t ≤ v i) ∧ 0 ≤ budget v K t

theorem cap_nonneg (v : I → ℝ) (hv : ∀ i, 0 < v i) {α t : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 ≤ t) (htv : ∀ i, t ≤ v i) (i : I) :
    0 ≤ cap v α t i := by
  unfold cap
  apply sub_nonneg.mpr
  apply le_min
  · exact (div_le_one (hv i)).mpr (htv i)
  · apply div_le_div_of_nonneg_left ht (mul_pos hα (hv i))
    nlinarith [hv i]

theorem domain_zero_feasible (v : I → ℝ) (hv : ∀ i, 0 < v i) {α K t : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (ht : ScaleDomain v K t) :
    ScaleFeasible v α K t (fun _ => 0) := by
  exact ⟨ht.1, fun i => ⟨le_rfl, cap_nonneg v hv hα hα1 ht.1 ht.2.1 i⟩, by simpa using ht.2.2⟩

theorem scaleFeasible_domain (v : I → ℝ) (hv : ∀ i, 0 < v i) {α K t : ℝ}
    (hα : 0 < α) {y : I → ℝ} (hy : ScaleFeasible v α K t y) : ScaleDomain v K t := by
  have hb := (scale_feasible_iff v hv hα y).mp hy
  refine ⟨hy.1, fun i => (hb.2.1 i).1.trans ((le_min_iff.mp (hb.2.1 i).2).1), ?_⟩
  exact (sum_nonneg fun i _ => (hy.2.1 i).1).trans hy.2.2

theorem zero_scale_vector (v : I → ℝ) (hv : ∀ i, 0 < v i) {α K : ℝ}
    (hα : 0 < α) {y : I → ℝ} (hy : ScaleFeasible v α K 0 y) :
    reconstruct v 0 y = fun _ => 0 := by
  have hb := (scale_feasible_iff v hv hα y).mp hy
  funext i
  have hi := hb.2.1 i
  have hu := (le_min_iff.mp hi.2).2
  simp only [zero_div] at hu
  exact le_antisymm hu hi.1

theorem cap_capped (v : I → ℝ) (hv : ∀ i, 0 < v i) {α t : ℝ}
    (hα : 0 < α) (i : I) (hi : α*v i ≤ t) : cap v α t i = 1 - t/v i := by
  unfold cap
  rw [min_eq_left ((one_le_div (mul_pos hα (hv i))).mpr hi)]

theorem cap_uncapped (v : I → ℝ) (hv : ∀ i, 0 < v i) {α t : ℝ}
    (hα : 0 < α) (i : I) (hi : t ≤ α*v i) :
    cap v α t i = (t/α - t) * (1/v i) := by
  unfold cap
  rw [min_eq_right ((div_le_one (mul_pos hα (hv i))).mpr hi)]
  field_simp

/-- Exact affine prefix-budget residual within any cap regime. -/
theorem prefix_residual_affine [DecidableEq I] (v : I → ℝ) (hv : ∀ i, 0 < v i)
    {α K t : ℝ} (hα : 0 < α) (P C : Finset I) (hCP : C ⊆ P)
    (hC : ∀ i ∈ C, α*v i ≤ t) (hU : ∀ i ∈ P \ C, t ≤ α*v i) :
    budget v K t - (∑ i ∈ P, cap v α t i) =
      K - C.card - t * ((∑ i ∈ Pᶜ, 1/v i) + (1/α)*(∑ i ∈ P \ C, 1/v i)) := by
  have hc : (∑ i ∈ C, cap v α t i) = C.card - t*(∑ i ∈ C, 1/v i) := by
    calc (∑ i ∈ C, cap v α t i) = ∑ i ∈ C, (1 - t/v i) :=
      sum_congr rfl (fun i hi => cap_capped v hv hα i (hC i hi))
      _ = _ := by rw [sum_sub_distrib]; simp only [sum_const, nsmul_eq_mul, mul_one, mul_sum]; congr 1; apply sum_congr rfl; intro i _; ring
  have hu : (∑ i ∈ P \ C, cap v α t i) = (t/α-t)*(∑ i ∈ P \ C, 1/v i) := by
    rw [mul_sum]
    exact sum_congr rfl (fun i hi => cap_uncapped v hv hα i (hU i hi))
  have hp := Finset.sum_sdiff (f := fun i => cap v α t i) hCP
  have hvp := Finset.sum_sdiff (f := fun i => 1/v i) hCP
  have hall := Finset.sum_add_sum_compl P (fun i => 1/v i)
  unfold budget
  rw [← hp, hc, hu, ← hall, ← hvp]
  ring

theorem prefix_slope_nonneg [DecidableEq I] (v : I → ℝ) (hv : ∀ i, 0 < v i)
    {α : ℝ} (hα : 0 < α) (P C : Finset I) :
    0 ≤ (∑ i ∈ Pᶜ, 1/v i) + (1/α)*(∑ i ∈ P \ C, 1/v i) := by
  apply add_nonneg
  · exact sum_nonneg fun i _ => (one_div_pos.mpr (hv i)).le
  · apply mul_nonneg (one_div_pos.mpr hα).le
    exact sum_nonneg fun i _ => (one_div_pos.mpr (hv i)).le
end
end BalancedAssortments.FixedSupportKnapsack
