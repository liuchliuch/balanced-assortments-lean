import BalancedAssortments.ContinuousKnapsackReal

namespace BalancedAssortments.ContinuousKnapsack

private theorem prefix_cap_nonneg (items : List Item) (hc : ∀ i ∈ items, 0 ≤ i.cap) (k : ℕ) :
    0 ≤ ((items.take k).map Item.cap).sum := by
  apply List.sum_nonneg
  intro c hc'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc'
  exact hc i (List.mem_of_mem_take hi)

/-- Exact prefix formula for every coordinate of the actual greedy solver. -/
theorem solve_getElem (B : ℚ) (items : List Item) (hB : 0 ≤ B)
    (hc : ∀ i ∈ items, 0 ≤ i.cap)
    (hs : items.Pairwise (fun i j => j.score ≤ i.score)) (k : ℕ) (hk : k < items.length) :
    (solve B items).1[k]?.getD 0 =
      if 0 < (items[k]).score then
        min (items[k]).cap (max (B - ((items.take k).map Item.cap).sum) 0) else 0 := by
  induction items generalizing B k with
  | nil => simp at hk
  | cons i items ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    have hic := hc i (by simp)
    have htc : ∀ j ∈ items, 0 ≤ j.cap := fun j hj => hc j (by simp [hj])
    cases k with
    | zero =>
      by_cases hi : 0 < i.score
      · by_cases hb : B ≤ i.cap
        · simp [solve, hi, hb, max_eq_left hB, min_eq_right hb]
        · simp [solve, hi, hb, max_eq_left hB, min_eq_left (le_of_not_ge hb)]
      · simp [solve, hi]
    | succ k =>
      have hkt : k < items.length := by simpa using hk
      have hp := prefix_cap_nonneg items htc k
      have hmem : items[k] ∈ items := List.getElem_mem hkt
      by_cases hi : 0 < i.score
      · by_cases hb : B ≤ i.cap
        · have hz : B - (i.cap + ((items.take k).map Item.cap).sum) ≤ 0 := by linarith
          simp only [solve, if_pos hi, if_pos hb, List.getElem?_cons_succ,
            List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
          have hzero : (List.replicate items.length (0 : ℚ))[k]?.getD 0 = 0 := by simp
          rw [hzero, max_eq_right hz, min_eq_right (htc _ hmem)]
          simp
        · simp only [solve, if_pos hi, if_neg hb, List.getElem?_cons_succ,
            List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
          rw [ih (B-i.cap) (by linarith) htc htail k hkt]
          have he : B-i.cap-((items.take k).map Item.cap).sum =
              B-(i.cap+((items.take k).map Item.cap).sum) := by ring
          rw [he]
      · have hj : ¬ 0 < (items[k]).score := by
          have hh := hhead _ hmem
          linarith
        simp [solve, hi, hj]


/-- Allocations depend only on capacities and the strict-positive score pattern;
actual score magnitudes determine the sorted order, but not the fill operation. -/
theorem solve_alloc_same_pattern (B : ℚ) (xs ys : List Item)
    (h : List.Forall₂ (fun i j => i.cap = j.cap ∧ (0 < i.score ↔ 0 < j.score)) xs ys) :
    (solve B xs).1 = (solve B ys).1 := by
  induction h generalizing B with
  | nil => rfl
  | @cons i j xs ys hij ht ih =>
    have hlen := ht.length_eq
    by_cases hi : 0 < i.score
    · have hj : 0 < j.score := hij.2.mp hi
      simp only [solve, if_pos hi, if_pos hj]
      rw [← hij.1]
      by_cases hb : B ≤ i.cap
      · simp [hb, hlen]
      · simp [hb, ih]
    · have hj : ¬0 < j.score := fun h => hi (hij.2.mpr h)
      simp [solve, hi, hj, hlen]

end BalancedAssortments.ContinuousKnapsack

namespace BalancedAssortments.ContinuousKnapsackReal

private theorem prefix_cap_nonneg (items : List Item) (hc : ∀ i ∈ items, 0 ≤ i.cap) (k : ℕ) :
    0 ≤ ((items.take k).map Item.cap).sum := by
  apply List.sum_nonneg
  intro c hc'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc'
  exact hc i (List.mem_of_mem_take hi)

/-- Exact prefix formula for every coordinate of the actual greedy solver. -/
theorem solve_getElem (B : ℝ) (items : List Item) (hB : 0 ≤ B)
    (hc : ∀ i ∈ items, 0 ≤ i.cap)
    (hs : items.Pairwise (fun i j => j.score ≤ i.score)) (k : ℕ) (hk : k < items.length) :
    (solve B items).1[k]?.getD 0 =
      if 0 < (items[k]).score then
        min (items[k]).cap (max (B - ((items.take k).map Item.cap).sum) 0) else 0 := by
  induction items generalizing B k with
  | nil => simp at hk
  | cons i items ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    have hic := hc i (by simp)
    have htc : ∀ j ∈ items, 0 ≤ j.cap := fun j hj => hc j (by simp [hj])
    cases k with
    | zero =>
      by_cases hi : 0 < i.score
      · by_cases hb : B ≤ i.cap
        · simp [solve, hi, hb, max_eq_left hB, min_eq_right hb]
        · simp [solve, hi, hb, max_eq_left hB, min_eq_left (le_of_not_ge hb)]
      · simp [solve, hi]
    | succ k =>
      have hkt : k < items.length := by simpa using hk
      have hp := prefix_cap_nonneg items htc k
      have hmem : items[k] ∈ items := List.getElem_mem hkt
      by_cases hi : 0 < i.score
      · by_cases hb : B ≤ i.cap
        · have hz : B - (i.cap + ((items.take k).map Item.cap).sum) ≤ 0 := by linarith
          simp only [solve, if_pos hi, if_pos hb, List.getElem?_cons_succ,
            List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
          have hzero : (List.replicate items.length (0 : ℝ))[k]?.getD 0 = 0 := by simp
          rw [hzero, max_eq_right hz, min_eq_right (htc _ hmem)]
          simp
        · simp only [solve, if_pos hi, if_neg hb, List.getElem?_cons_succ,
            List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
          rw [ih (B-i.cap) (by linarith) htc htail k hkt]
          have he : B-i.cap-((items.take k).map Item.cap).sum =
              B-(i.cap+((items.take k).map Item.cap).sum) := by ring
          rw [he]
      · have hj : ¬ 0 < (items[k]).score := by
          have hh := hhead _ hmem
          linarith
        simp [solve, hi, hj]


/-- Allocations depend only on capacities and the strict-positive score pattern;
actual score magnitudes determine the sorted order, but not the fill operation. -/
theorem solve_alloc_same_pattern (B : ℝ) (xs ys : List Item)
    (h : List.Forall₂ (fun i j => i.cap = j.cap ∧ (0 < i.score ↔ 0 < j.score)) xs ys) :
    (solve B xs).1 = (solve B ys).1 := by
  induction h generalizing B with
  | nil => rfl
  | @cons i j xs ys hij ht ih =>
    have hlen := ht.length_eq
    by_cases hi : 0 < i.score
    · have hj : 0 < j.score := hij.2.mp hi
      simp only [solve, if_pos hi, if_pos hj]
      rw [← hij.1]
      by_cases hb : B ≤ i.cap
      · simp [hb, hlen]
      · simp [hb, ih]
    · have hj : ¬0 < j.score := fun h => hi (hij.2.mpr h)
      simp [solve, hi, hj, hlen]

end BalancedAssortments.ContinuousKnapsackReal
