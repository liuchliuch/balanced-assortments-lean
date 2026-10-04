import Mathlib

/-! Exact finite MNL denominator tilting. The existence of a marginal decomposition
is deliberately a separate hypothesis, so no polyhedral completeness is assumed. -/
noncomputable section
namespace BalancedAssortments.Sales
open scoped BigOperators
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]

def Distribution (q : A → ℝ) : Prop := (∀ a, 0 ≤ q a) ∧ ∑ a, q a = 1

def marginal (S : A → Finset I) (p : A → ℝ) (i : I) : ℝ :=
  ∑ a, if i ∈ S a then p a else 0

def denominator (v : I → ℝ) (S : A → Finset I) (a : A) : ℝ :=
  1 + ∑ i ∈ S a, v i

def sales (v : I → ℝ) (S : A → Finset I) (q : A → ℝ) (i : I) : ℝ :=
  ∑ a, if i ∈ S a then q a * v i / denominator v S a else 0

def outside (v : I → ℝ) (S : A → Finset I) (q : A → ℝ) : ℝ :=
  ∑ a, q a / denominator v S a

def tilt (v : I → ℝ) (S : A → Finset I) (q : A → ℝ) (a : A) : ℝ :=
  q a / denominator v S a / outside v S q

def compactSales (w : I → ℝ) (i : I) : ℝ := w i / (1 + ∑ j, w j)
def revenue (r x : I → ℝ) : ℝ := ∑ i, r i * x i
def objective (r w : I → ℝ) : ℝ := (∑ i, r i * w i) / (1 + ∑ i, w i)
/-- Pairwise formulation includes zero coordinates on the right. -/
def Balanced (α : ℝ) (x : I → ℝ) : Prop := ∀ i, x i = 0 ∨ ∀ j, α * x j ≤ x i

theorem denominator_pos (v : I → ℝ) (hv : ∀ i, 0 ≤ v i) (S : A → Finset I) (a : A) :
    0 < denominator v S a := by
  unfold denominator
  have hn := Finset.sum_nonneg (s := S a) (fun i _ => hv i)
  linarith

theorem marginal_nonneg (S : A → Finset I) {p : A → ℝ} (hp : Distribution p) (i : I) :
    0 ≤ marginal S p i := by
  exact Finset.sum_nonneg (fun a _ => by split_ifs <;> simp_all [Distribution])

theorem marginal_le_one (S : A → Finset I) {p : A → ℝ} (hp : Distribution p) (i : I) :
    marginal S p i ≤ 1 := by
  rw [← hp.2]
  exact Finset.sum_le_sum (fun a _ => by split_ifs <;> simp_all [Distribution])

theorem sum_marginal (S : A → Finset I) (p : A → ℝ) :
    ∑ i, marginal S p i = ∑ a, p a * (S a).card := by
  unfold marginal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [Finset.sum_ite_mem, mul_comm]

theorem marginal_rank (S : A → Finset I) {p : A → ℝ} (hp : Distribution p)
    (K : ℕ) (hK : ∀ a, (S a).card ≤ K) : ∑ i, marginal S p i ≤ K := by
  rw [sum_marginal]
  calc
    ∑ a, p a * ((S a).card : ℝ) ≤ ∑ a, p a * (K : ℝ) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (by exact_mod_cast hK a) (hp.1 a))
    _ = K := by rw [← Finset.sum_mul, hp.2]; ring

theorem weighted_marginal (v : I → ℝ) (S : A → Finset I) (p : A → ℝ) :
    ∑ i, v i * marginal S p i = ∑ a, p a * ∑ i ∈ S a, v i := by
  simp only [marginal, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_ite, mul_zero]
  simp [Finset.sum_ite_mem, mul_comm]

theorem mean_denominator (v : I → ℝ) (S : A → Finset I) {p : A → ℝ}
    (hp : Distribution p) :
    ∑ a, p a * denominator v S a = 1 + ∑ i, v i * marginal S p i := by
  simp only [denominator, mul_add, mul_one, Finset.sum_add_distrib]
  rw [hp.2, weighted_marginal]

theorem outside_pos (v : I → ℝ) (hv : ∀ i, 0 ≤ v i) (S : A → Finset I)
    {q : A → ℝ} (hq : Distribution q) : 0 < outside v S q := by
  have hex : ∃ a, 0 < q a := by
    by_contra! h
    have hz : ∀ a, q a = 0 := fun a => le_antisymm (h a) (hq.1 a)
    have := hq.2
    simp [hz] at this
  obtain ⟨a, ha⟩ := hex
  exact Finset.sum_pos' (fun b _ => div_nonneg (hq.1 b) (denominator_pos v hv S b).le)
    ⟨a, Finset.mem_univ a, div_pos ha (denominator_pos v hv S a)⟩

theorem tilt_distribution (v : I → ℝ) (hv : ∀ i, 0 ≤ v i) (S : A → Finset I)
    {q : A → ℝ} (hq : Distribution q) : Distribution (tilt v S q) := by
  have ht := outside_pos v hv S hq
  constructor
  · intro a
    exact div_nonneg (div_nonneg (hq.1 a) (denominator_pos v hv S a).le) ht.le
  · simp only [tilt, ← Finset.sum_div]
    change outside v S q / outside v S q = 1
    exact div_self ht.ne'

theorem tilted_sales (v : I → ℝ) (S : A → Finset I) (q : A → ℝ) (i : I) :
    v i * marginal S (tilt v S q) i = sales v S q i / outside v S q := by
  simp only [marginal, sales, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp [tilt] <;> ring

/-- Reverse tilt for an arbitrary finite marginal representation. -/
def reverseTilt (v : I → ℝ) (S : A → Finset I) (p : A → ℝ) (a : A) : ℝ :=
  p a * denominator v S a / (1 + ∑ i, v i * marginal S p i)

theorem reverse_denominator_pos (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) {p : A → ℝ} (hp : Distribution p) :
    0 < 1 + ∑ i, v i * marginal S p i := by
  have hn := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => mul_nonneg (hv i) (marginal_nonneg S hp i))
  linarith

theorem reverse_distribution (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) {p : A → ℝ} (hp : Distribution p) :
    Distribution (reverseTilt v S p) := by
  have hd := reverse_denominator_pos v hv S hp
  constructor
  · intro a
    exact div_nonneg (mul_nonneg (hp.1 a) (denominator_pos v hv S a).le) hd.le
  · simp only [reverseTilt, ← Finset.sum_div, mean_denominator v S hp]
    exact div_self hd.ne'

theorem reverse_sales (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) (p : A → ℝ) (i : I) :
    sales v S (reverseTilt v S p) i = compactSales (fun j => v j * marginal S p j) i := by
  unfold sales compactSales marginal
  dsimp only
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs with hi
  · unfold reverseTilt
    have hd := (denominator_pos v hv S a).ne'
    field_simp
    rfl
  · simp

theorem compact_revenue (r w : I → ℝ) : revenue r (compactSales w) = objective r w := by
  simp [revenue, compactSales, objective, mul_div_assoc, Finset.sum_div]

theorem balanced_div_iff (α : ℝ) (x : I → ℝ) {c : ℝ} (hc : 0 < c) :
    Balanced α (fun i => x i / c) ↔ Balanced α x := by
  simp only [Balanced, div_eq_zero_iff, hc.ne', or_false, ← mul_div_assoc,
    div_le_div_iff_of_pos_right hc]


theorem tilt_mean_denominator (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) {q : A → ℝ} (hq : Distribution q) :
    1 + ∑ i, v i * marginal S (tilt v S q) i = 1 / outside v S q := by
  rw [← mean_denominator v S (tilt_distribution v hv S hq)]
  calc
    ∑ a, tilt v S q a * denominator v S a = ∑ a, q a / outside v S q := by
      apply Finset.sum_congr rfl
      intro a _
      unfold tilt
      have hd := (denominator_pos v hv S a).ne'
      field_simp
    _ = _ := by rw [← Finset.sum_div, hq.2]

theorem forward_sales (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) {q : A → ℝ} (hq : Distribution q) (i : I) :
    sales v S q i = compactSales (fun j => v j * marginal S (tilt v S q) j) i := by
  unfold compactSales
  dsimp only
  rw [tilt_mean_denominator v hv S hq, tilted_sales]
  have ht := (outside_pos v hv S hq).ne'
  field_simp

/-- The compact feasible region without balance. -/
def CompactFeasible (v w : I → ℝ) (K : ℕ) : Prop :=
  (∀ i, 0 ≤ w i ∧ w i ≤ v i) ∧ ∑ i, w i / v i ≤ K

theorem marginals_feasible (v : I → ℝ) (hv : ∀ i, 0 < v i)
    (S : A → Finset I) {p : A → ℝ} (hp : Distribution p)
    (K : ℕ) (hK : ∀ a, (S a).card ≤ K) :
    CompactFeasible v (fun i => v i * marginal S p i) K := by
  constructor
  · intro i
    constructor
    · exact mul_nonneg (hv i).le (marginal_nonneg S hp i)
    · simpa using mul_le_mul_of_nonneg_left (marginal_le_one S hp i) (hv i).le
  · simpa [mul_div_cancel_left₀, (hv _).ne'] using marginal_rank S hp K hK

/-- Forward policy-to-compact mapping, preserving every coordinate exactly. -/
theorem policy_to_compact (v : I → ℝ) (hv : ∀ i, 0 < v i)
    (S : A → Finset I) {q : A → ℝ} (hq : Distribution q)
    (K : ℕ) (hK : ∀ a, (S a).card ≤ K) :
    ∃ w, CompactFeasible v w K ∧ sales v S q = compactSales w := by
  refine ⟨fun i => v i * marginal S (tilt v S q) i,
    marginals_feasible v hv S (tilt_distribution v (fun i => (hv i).le) S hq) K hK, ?_⟩
  funext i
  exact forward_sales v (fun i => (hv i).le) S hq i

/-- Reverse mapping assumes a genuine marginal representation; it does not
assume or assert a general uniform-matroid decomposition theorem. -/
theorem implement_marginals (v w : I → ℝ) (hv : ∀ i, 0 < v i)
    (S : A → Finset I) {p : A → ℝ} (hp : Distribution p)
    (hm : ∀ i, marginal S p i = w i / v i) :
    ∃ q, Distribution q ∧ sales v S q = compactSales w := by
  have hw : (fun i => v i * marginal S p i) = w := by
    funext i
    rw [hm i]
    field_simp [(hv i).ne']
  refine ⟨reverseTilt v S p, reverse_distribution v (fun i => (hv i).le) S hp, ?_⟩
  funext i
  rw [reverse_sales v (fun i => (hv i).le), hw]

theorem compact_balance (α : ℝ) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Balanced α (compactSales w) ↔ Balanced α w := by
  apply balanced_div_iff
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hw i)
  linarith


theorem reverse_tilt_inverse (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) {q : A → ℝ} (hq : Distribution q) :
    reverseTilt v S (tilt v S q) = q := by
  funext a
  unfold reverseTilt
  rw [tilt_mean_denominator v hv S hq]
  unfold tilt
  have hd := (denominator_pos v hv S a).ne'
  have ht := (outside_pos v hv S hq).ne'
  field_simp

theorem reverse_outside (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) {p : A → ℝ} (hp : Distribution p) :
    outside v S (reverseTilt v S p) = 1 / (1 + ∑ i, v i * marginal S p i) := by
  unfold outside
  calc
    ∑ a, reverseTilt v S p a / denominator v S a =
        ∑ a, p a / (1 + ∑ i, v i * marginal S p i) := by
      apply Finset.sum_congr rfl
      intro a _
      unfold reverseTilt
      have hd := (denominator_pos v hv S a).ne'
      field_simp
    _ = _ := by rw [← Finset.sum_div, hp.2]

theorem tilt_reverse_inverse (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) {p : A → ℝ} (hp : Distribution p) :
    tilt v S (reverseTilt v S p) = p := by
  funext a
  unfold tilt
  rw [reverse_outside v hv S hp]
  unfold reverseTilt
  have hd := (denominator_pos v hv S a).ne'
  have ht := (reverse_denominator_pos v hv S hp).ne'
  field_simp

theorem reverse_support (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) {p : A → ℝ} (hp : Distribution p) (a : A) :
    reverseTilt v S p a ≠ 0 ↔ p a ≠ 0 := by
  simp [reverseTilt, div_ne_zero_iff, mul_ne_zero_iff,
    (denominator_pos v hv S a).ne', (reverse_denominator_pos v hv S hp).ne']

theorem tilt_support (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) {q : A → ℝ} (hq : Distribution q) (a : A) :
    tilt v S q a ≠ 0 ↔ q a ≠ 0 := by
  simp [tilt, div_ne_zero_iff, (denominator_pos v hv S a).ne', (outside_pos v hv S hq).ne']

/-- Reverse existence, conditional only on the separately stated completeness
of the given finite marginal family. -/
theorem compact_to_policy_given_decomposition (v w : I → ℝ) (hv : ∀ i, 0 < v i)
    (S : A → Finset I) (K : ℕ) (hK : ∀ a, (S a).card ≤ K)
    (complete : ∀ u, CompactFeasible v u K →
      ∃ p, Distribution p ∧ ∀ i, marginal S p i = u i / v i) :
    CompactFeasible v w K → ∃ q, Distribution q ∧ sales v S q = compactSales w := by
  intro hw
  obtain ⟨p, hp, hm⟩ := complete w hw
  exact implement_marginals v w hv S hp hm


/-- Full finite attainability equivalence. The uniform-matroid decomposition
result is an explicit premise, not an axiom hidden inside this theorem. -/
theorem exact_attainable_of_decomposition_complete (v x : I → ℝ) (hv : ∀ i, 0 < v i)
    (S : A → Finset I) (K : ℕ) (hK : ∀ a, (S a).card ≤ K)
    (complete : ∀ u, CompactFeasible v u K →
      ∃ p, Distribution p ∧ ∀ i, marginal S p i = u i / v i) :
    (∃ q, Distribution q ∧ sales v S q = x) ↔
      ∃ w, CompactFeasible v w K ∧ compactSales w = x := by
  constructor
  · rintro ⟨q, hq, hx⟩
    obtain ⟨w, hw, hs⟩ := policy_to_compact v hv S hq K hK
    exact ⟨w, hw, hs.symm.trans hx⟩
  · rintro ⟨w, hw, hx⟩
    obtain ⟨q, hq, hs⟩ := compact_to_policy_given_decomposition v w hv S K hK complete hw
    exact ⟨q, hq, hs.trans hx⟩

/-- Balance and the fractional revenue are simultaneously preserved. -/
theorem balance_revenue_preserved (α : ℝ) (r w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (Balanced α (compactSales w) ↔ Balanced α w) ∧
      revenue r (compactSales w) = objective r w :=
  ⟨compact_balance α w hw, compact_revenue r w⟩

/-- Positive and zero product supports are unchanged by compact scaling. -/
theorem compact_support (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (i : I) :
    compactSales w i > 0 ↔ w i > 0 := by
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hw i)
  have hd : 0 < 1 + ∑ i, w i := by linarith
  exact div_pos_iff_of_pos_right hd


/-- The exact rescaled variables used in the paper satisfy caps and rank. -/
theorem sales_ratio_feasible (v : I → ℝ) (hv : ∀ i, 0 < v i)
    (S : A → Finset I) {q : A → ℝ} (hq : Distribution q)
    (K : ℕ) (hK : ∀ a, (S a).card ≤ K) :
    CompactFeasible v (fun i => sales v S q i / outside v S q) K := by
  have heq : (fun i => sales v S q i / outside v S q) =
      (fun i => v i * marginal S (tilt v S q) i) := by
    funext i
    exact (tilted_sales v S q i).symm
  rw [heq]
  exact marginals_feasible v hv S (tilt_distribution v (fun i => (hv i).le) S hq) K hK

theorem outside_recovery (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) {q : A → ℝ} (hq : Distribution q) :
    outside v S q = 1 / (1 + ∑ i, sales v S q i / outside v S q) := by
  have ht := tilt_mean_denominator v hv S hq
  simp only [tilted_sales] at ht
  rw [ht]
  simp

theorem sales_total_probability (v : I → ℝ) (hv : ∀ i, 0 ≤ v i)
    (S : A → Finset I) {q : A → ℝ} (hq : Distribution q) :
    outside v S q + ∑ i, sales v S q i = 1 := by
  have ht := tilt_mean_denominator v hv S hq
  simp only [tilted_sales, ← Finset.sum_div] at ht
  have hx := (outside_pos v hv S hq).ne'
  field_simp at ht
  linarith

end BalancedAssortments.Sales
