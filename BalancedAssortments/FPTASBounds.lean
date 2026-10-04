import BalancedAssortments.FPTAS

namespace BalancedAssortments.FPTAS
open Finset

lemma fold_max_le (xs : List ℚ) {a b : ℚ} (ha : a ≤ b)
    (hx : ∀ x ∈ xs, x ≤ b) : xs.foldl max a ≤ b := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih (max_le ha (hx x (by simp)))
    intro y hy; exact hx y (by simp [hy])

lemma le_fold_max_initial (xs : List ℚ) (a : ℚ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

lemma le_fold_max_member (xs : List ℚ) {x : ℚ} (hx : x ∈ xs) (a : ℚ) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hm
    · exact (le_max_right a x).trans (le_fold_max_initial ys (max a x))
    · exact ih hm (max a y)

lemma fold_min_le_initial (xs : List ℚ) (a : ℚ) : xs.foldl min a ≤ a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (ih (min a x)).trans (min_le_left a x)

lemma fold_min_le_member (xs : List ℚ) {x : ℚ} (hx : x ∈ xs) (a : ℚ) :
    xs.foldl min a ≤ x := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hm
    · exact (fold_min_le_initial ys (min a x)).trans (min_le_right a x)
    · exact ih hm (min a y)

lemma fold_min_positive (xs : List ℚ) {a : ℚ} (ha : 0 < a)
    (hx : ∀ x ∈ xs, 0 < x) : 0 < xs.foldl min a := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih (lt_min ha (hx x (by simp)))
    intro y hy; exact hx y (by simp [hy])

theorem vmin_pos {n : ℕ} (d : Input n) (hv : ∀ i, 0 < d.v i) : 0 < vmin d := by
  apply fold_min_positive _ (hv 0)
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact hv i

theorem vmin_le {n : ℕ} (d : Input n) (i : Fin (n+1)) : vmin d ≤ d.v i :=
  fold_min_le_member _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩) _

theorem le_vmax {n : ℕ} (d : Input n) (i : Fin (n+1)) : d.v i ≤ vmax d :=
  le_fold_max_member _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩) _

theorem le_rmax {n : ℕ} (d : Input n) (i : Fin (n+1)) : d.r i ≤ rmax d :=
  le_fold_max_member _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩) _

theorem rmax_nonneg {n : ℕ} (d : Input n) : 0 ≤ rmax d :=
  le_fold_max_initial _ _

theorem singleton_revenue {n : ℕ} (d : Input n) (i : Fin (n+1)) :
    revenue d (singleton d i) = d.r i * d.v i / (1 + d.v i) := by
  simp [revenue, singleton, mul_ite, Finset.sum_ite_eq']

theorem singleton_revenue_le {n : ℕ} (d : Input n) (i : Fin (n+1)) :
    revenue d (singleton d i) ≤ singletonValue d :=
  le_fold_max_member _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩) _

theorem singletonValue_pos {n : ℕ} (d : Input n) (hv : ∀ i, 0 < d.r i ∧ 0 < d.v i) :
    0 < singletonValue d := by
  apply lt_of_lt_of_le _ (singleton_revenue_le d 0)
  rw [singleton_revenue]
  exact div_pos (mul_pos (hv 0).1 (hv 0).2) (by linarith [(hv 0).2])

theorem revenue_le_rmax {n : ℕ} (d : Input n) (w : Fin (n+1) → ℚ)
    (hw : ∀ i, 0 ≤ w i) : revenue d w ≤ rmax d := by
  have hs : 0 ≤ ∑ i, w i := sum_nonneg fun i _ => hw i
  have hnum : (∑ i, d.r i * w i) ≤ rmax d * ∑ i, w i := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (le_rmax d i) (hw i)
  unfold revenue
  apply (div_le_iff₀ (by linarith : 0 < 1 + ∑ i, w i)).2
  nlinarith [rmax_nonneg d]

theorem singleton_feasible {n : ℕ} (d : Input n) (hd : Valid d) (j : Fin (n+1)) :
    Feasible d (singleton d j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold singleton
    split_ifs with hi
    · subst i; exact ⟨(hd.1 j).2.le, le_rfl⟩
    · exact ⟨le_rfl, (hd.1 i).2.le⟩
  · simpa [singleton, ite_div, Finset.sum_ite_eq', (hd.1 j).2.ne'] using
      (show (1 : ℚ) ≤ d.K by exact_mod_cast hd.2.2.2.1)
  · intro i
    by_cases hi : i = j
    · subst i; right; intro k
      simp only [singleton, ite_true]
      split_ifs
      · nlinarith [hd.2.2.1, (hd.1 j).2]
      · simp; exact (hd.1 j).2.le
    · left; simp [singleton, hi]

theorem runSales_dominates_singletons {n : ℕ} (d : Input n) (hd : Valid d) (ε : ℚ)
    (i : Fin (n+1)) : revenue d (singleton d i) ≤ revenue d (runSales d ε) := by
  apply runSales_dominates d ε _ (singleton_feasible d hd i)
  simp only [rawCandidates, List.mem_append, List.mem_map]
  exact Or.inl ⟨i, List.mem_finRange i, rfl⟩

theorem runSales_ge_singletonValue {n : ℕ} (d : Input n) (hd : Valid d) (ε : ℚ) :
    singletonValue d ≤ revenue d (runSales d ε) := by
  apply fold_max_le
  · have hp : 0 < revenue d (singleton d 0) := by
      rw [singleton_revenue]
      exact div_pos (mul_pos (hd.1 0).1 (hd.1 0).2) (by linarith [(hd.1 0).2])
    exact hp.le.trans (runSales_dominates_singletons d hd ε 0)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact runSales_dominates_singletons d hd ε i

lemma fold_max_initial_or_mem (xs : List ℚ) (a : ℚ) :
    xs.foldl max a = a ∨ xs.foldl max a ∈ xs := by
  induction xs generalizing a with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    rcases ih (max a x) with he | hm
    · by_cases hax : a ≤ x
      · right; simp only [List.foldl_cons]; rw [he, max_eq_right hax]; simp
      · left; simp only [List.foldl_cons]; rw [he, max_eq_left (le_of_not_ge hax)]
    · right; exact List.mem_cons_of_mem _ hm

theorem maxList_nonneg (xs : List ℚ) : 0 ≤ maxList xs := le_fold_max_initial xs 0

theorem le_maxList {xs : List ℚ} {x : ℚ} (hx : x ∈ xs) : x ≤ maxList xs :=
  le_fold_max_member xs hx 0

theorem maxList_mem {xs : List ℚ} (h : 0 < maxList xs) : maxList xs ∈ xs := by
  rcases fold_max_initial_or_mem xs 0 with he | hm
  · have hz : maxList xs = 0 := he
    linarith
  · exact hm

theorem maxProfit_bound {n : ℕ} (d : Input n) (δ τ ρ : ℚ)
    {g : List Knapsack.Item} (hg : g ∈ groups d δ τ ρ)
    {item : Knapsack.Item} (hi : item ∈ g) :
    item.profit ≤ maxList (((groups d δ τ ρ).flatten).map Knapsack.Item.profit) := by
  apply le_maxList
  exact List.mem_map.mpr ⟨item, List.mem_flatten.mpr ⟨g, hg, hi⟩, rfl⟩

theorem maxProfit_attained {n : ℕ} (d : Input n) (δ τ ρ : ℚ)
    (h : 0 < maxList (((groups d δ τ ρ).flatten).map Knapsack.Item.profit)) :
    ∃ g ∈ groups d δ τ ρ, ∃ item ∈ g,
      item.profit = maxList (((groups d δ τ ρ).flatten).map Knapsack.Item.profit) := by
  obtain ⟨item, hm, he⟩ := List.mem_map.mp (maxList_mem h)
  obtain ⟨g, hg, hi⟩ := List.mem_flatten.mp hm
  exact ⟨g, hg, item, hi, he⟩
end BalancedAssortments.FPTAS
