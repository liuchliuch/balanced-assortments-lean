import Mathlib

/-! Executable exact continuous-knapsack greedy optimization over rational
inputs, with a proved dual certificate. Equal and nonpositive scores are allowed. -/
namespace BalancedAssortments.ContinuousKnapsack

structure Item where
  score : ℚ
  cap : ℚ
  deriving DecidableEq, Repr

def Feasible (B : ℚ) (items : List Item) (y : List ℚ) : Prop :=
  List.Forall₂ (fun i q => 0 ≤ q ∧ q ≤ i.cap) items y ∧ y.sum ≤ B

def profit (items : List Item) (y : List ℚ) : ℚ :=
  (List.zipWith (fun i q => i.score*q) items y).sum

def penalty (items : List Item) (price : ℚ) : ℚ :=
  (items.map fun i => i.cap * max (i.score-price) 0).sum

/-- The second component is a dual price. The first positive item exhausting
the budget sets that price; a nonpositive tail is assigned zero allocation. -/
def solve (B : ℚ) : List Item → List ℚ × ℚ
  | [] => ([], 0)
  | i :: items =>
      if 0 < i.score then
        if B ≤ i.cap then (B :: List.replicate items.length 0, i.score)
        else let s := solve (B-i.cap) items; (i.cap :: s.1, s.2)
      else (List.replicate (items.length+1) 0, 0)

@[simp] theorem solve_length (B : ℚ) (items : List Item) :
    (solve B items).1.length = items.length := by
  induction items generalizing B with
  | nil => rfl
  | cons i items ih => simp only [solve]; split_ifs <;> simp [ih]

@[simp] theorem profit_zero (items : List Item) :
    profit items (List.replicate items.length 0) = 0 := by
  induction items with
  | nil => rfl
  | cons i items ih => simp [profit, List.replicate_succ, profit] at *; exact ih

private theorem zero_caps (items : List Item) (hc : ∀ i ∈ items, 0 ≤ i.cap) :
    List.Forall₂ (fun i q => 0 ≤ q ∧ q ≤ i.cap) items (List.replicate items.length 0) := by
  induction items with
  | nil => exact List.Forall₂.nil
  | cons i items ih =>
    simp only [List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons ⟨le_rfl, hc i (by simp)⟩ (ih (fun j hj => hc j (by simp [hj])))

theorem solve_dual_nonneg (B : ℚ) (items : List Item) : 0 ≤ (solve B items).2 := by
  induction items generalizing B with
  | nil => exact le_rfl
  | cons i items ih =>
    simp only [solve]
    split_ifs with hi hb
    · exact hi.le
    · exact ih _
    · exact le_rfl

theorem solve_dual_le (B : ℚ) (items : List Item) {M : ℚ} (hM : 0 ≤ M)
    (hs : ∀ i ∈ items, i.score ≤ M) : (solve B items).2 ≤ M := by
  induction items generalizing B with
  | nil => exact hM
  | cons i items ih =>
    simp only [solve]
    split_ifs
    · exact hs i (by simp)
    · exact ih _ (fun j hj => hs j (by simp [hj]))
    · exact hM

theorem solve_feasible (B : ℚ) (items : List Item) (hB : 0 ≤ B)
    (hc : ∀ i ∈ items, 0 ≤ i.cap) : Feasible B items (solve B items).1 := by
  induction items generalizing B with
  | nil => exact ⟨List.Forall₂.nil, hB⟩
  | cons i items ih =>
    have hic := hc i (by simp)
    have htc : ∀ j ∈ items, 0 ≤ j.cap := fun j hj => hc j (by simp [hj])
    simp only [solve]
    split_ifs with hi hb
    · constructor
      · exact List.Forall₂.cons ⟨hB, hb⟩ (zero_caps items htc)
      · simp
    · have ht := ih (B-i.cap) (by linarith) htc
      exact ⟨List.Forall₂.cons ⟨hic, le_rfl⟩ ht.1, by have hh := ht.2; change i.cap + (solve (B-i.cap) items).1.sum ≤ B; linarith⟩
    · exact ⟨by simpa using zero_caps (i::items) hc, by simpa using hB⟩

private theorem penalty_zero (items : List Item) (price : ℚ)
    (hs : ∀ i ∈ items, i.score ≤ price) : penalty items price = 0 := by
  unfold penalty
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [max_eq_right (sub_nonpos.mpr (hs i hi)), mul_zero]

/-- Exact primal=dual identity for the actual returned allocation. -/
theorem solve_duality (B : ℚ) (items : List Item) (hB : 0 ≤ B)
    (hc : ∀ i ∈ items, 0 ≤ i.cap)
    (hs : items.Pairwise (fun i j => j.score ≤ i.score)) :
    profit items (solve B items).1 = (solve B items).2 * B + penalty items (solve B items).2 := by
  induction items generalizing B with
  | nil => simp [solve, profit, penalty]
  | cons i items ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    have hic := hc i (by simp)
    have htc : ∀ j ∈ items, 0 ≤ j.cap := fun j hj => hc j (by simp [hj])
    simp only [solve]
    split_ifs with hi hb
    · have hp := penalty_zero items i.score hhead
      simp only [profit, List.zipWith_cons_cons, List.sum_cons]
      have hz := profit_zero items
      unfold profit at hz
      rw [hz]
      simp only [penalty, List.map_cons, List.sum_cons, sub_self, max_self, mul_zero, zero_add]
      unfold penalty at hp
      linarith
    · have ht := ih (B-i.cap) (by linarith) htc htail
      have hprice := solve_dual_le (B-i.cap) items hi.le hhead
      change i.score*i.cap + profit items (solve (B-i.cap) items).1 =
        (solve (B-i.cap) items).2 * B +
          (i.cap*max (i.score-(solve (B-i.cap) items).2) 0 + penalty items (solve (B-i.cap) items).2)
      rw [ht, max_eq_left (sub_nonneg.mpr hprice)]
      ring
    · have hall : ∀ j ∈ i::items, j.score ≤ 0 := by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact le_of_not_gt hi
        · exact (hhead j hj).trans (le_of_not_gt hi)
      have hp := penalty_zero (i::items) 0 hall
      change profit (i::items) (List.replicate (i::items).length 0) = 0*B + penalty (i::items) 0
      rw [profit_zero, hp]
      ring

private theorem profit_le_dual_sum (items : List Item) (y : List ℚ) (price : ℚ)
    (hf : List.Forall₂ (fun i q => 0 ≤ q ∧ q ≤ i.cap) items y) :
    profit items y ≤ price*y.sum + penalty items price := by
  induction hf with
  | nil => simp [profit, penalty]
  | @cons i q items y hi ht ih =>
    have h₁ := mul_le_mul_of_nonneg_right (le_max_left (i.score-price) 0) hi.1
    have h₂ := mul_le_mul_of_nonneg_left hi.2 (le_max_right (i.score-price) 0)
    change i.score*q + profit items y ≤ price*(q+y.sum) +
      (i.cap*max (i.score-price) 0 + penalty items price)
    nlinarith

theorem weak_duality (B : ℚ) (items : List Item) (y : List ℚ) (price : ℚ)
    (hprice : 0 ≤ price) (hf : Feasible B items y) :
    profit items y ≤ price*B + penalty items price := by
  have hh := profit_le_dual_sum items y price hf.1
  have hb := mul_le_mul_of_nonneg_left hf.2 hprice
  linarith

/-- Actual greedy allocation is optimal, including ties, zero scores, negative
scores, zero capacities, empty item lists, and unused budget. -/
theorem solve_optimal (B : ℚ) (items : List Item) (hB : 0 ≤ B)
    (hc : ∀ i ∈ items, 0 ≤ i.cap)
    (hs : items.Pairwise (fun i j => j.score ≤ i.score)) :
    Feasible B items (solve B items).1 ∧
      ∀ y, Feasible B items y → profit items y ≤ profit items (solve B items).1 := by
  refine ⟨solve_feasible B items hB hc, ?_⟩
  intro y hy
  rw [solve_duality B items hB hc hs]
  exact weak_duality B items y _ (solve_dual_nonneg B items) hy

end BalancedAssortments.ContinuousKnapsack
