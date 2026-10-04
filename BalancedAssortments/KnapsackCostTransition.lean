import BalancedAssortments.KnapsackCostCompression
import BalancedAssortments.KnapsackCostRange

namespace BalancedAssortments.KnapsackCostState
open ComplexityTimeBinary KnapsackCostRational

theorem compare_fraction_le {x y : Fraction} (hx : x.Valid) (hy : y.Valid) :
    (KnapsackCostRational.compare x y).1 ≠ .gt ↔ x.decode ≤ y.decode := by
  have h := KnapsackCostRational.compare_correct hx hy
  cases he : (KnapsackCostRational.compare x y).1 <;>
    simp only [he, rationalMeaning] at h <;> simp <;> linarith

/-- Generate and check the options extending one prior state. -/
def candidatesFor : Fraction → State → List Item → List State × ℕ
  | _, _, [] => ([], 1)
  | cap, s, i :: is =>
      let ext := extend s i
      let cmp := KnapsackCostRational.compare ext.1.weight cap
      let rest := candidatesFor cap s is
      (if cmp.1 ≠ .gt then ext.1 :: rest.1 else rest.1,
        ext.2 + cmp.2 + rest.2 + 8)

theorem candidatesFor_member {cap : Fraction} {s t : State} {items : List Item}
    (ht : t ∈ (candidatesFor cap s items).1) : ∃ i ∈ items, t = (extend s i).1 := by
  induction items with
  | nil => simp [candidatesFor] at ht
  | cons i is ih =>
    simp only [candidatesFor] at ht
    split_ifs at ht
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨i, by simp, rfl⟩
      · obtain ⟨j,hj,he⟩ := ih ht; exact ⟨j,by simp [hj],he⟩
    · obtain ⟨j,hj,he⟩ := ih ht; exact ⟨j,by simp [hj],he⟩

theorem candidatesFor_length (cap : Fraction) (s : State) (items : List Item) :
    (candidatesFor cap s items).1.length ≤ items.length := by
  induction items with
  | nil => simp [candidatesFor]
  | cons i is ih => simp only [candidatesFor, List.length_cons]; split_ifs <;> simp_all <;> omega

theorem candidatesFor_decode {cap : Fraction} {s : State} {items : List Item} {θ : ℚ}
    (hc : cap.Valid) (hs : s.Valid)
    (hi : ∀ i ∈ items, i.Valid ∧ value i.scaled = Knapsack.scaledProfit θ i.decode) :
    (candidatesFor cap s items).1.map State.decode =
      ((items.map Item.decode).map (Knapsack.extend θ s.decode)).filter
        (fun t => t.weight ≤ cap.decode) := by
  induction items with
  | nil => rfl
  | cons i is ih =>
    have hv := (hi i (by simp)).1
    have hk := (hi i (by simp)).2
    have he := extend_decode hs hv hk
    have hle := compare_fraction_le (extend_valid hs hv).1 hc
    have ht := ih (fun j hj => hi j (by simp [hj]))
    simp only [candidatesFor, List.map_cons, List.filter_cons]
    by_cases h : (extend s i).1.weight.decode ≤ cap.decode
    · have hh := hle.mpr h
      have hd : (Knapsack.extend θ s.decode i.decode).weight ≤ cap.decode := by
        rw [← he]; exact h
      simp [hh, hd, he, ht]
    · have hh : ¬ (KnapsackCostRational.compare (extend s i).1.weight cap).1 ≠ .gt :=
        fun hh => h (hle.mp hh)
      have hd : ¬ (Knapsack.extend θ s.decode i.decode).weight ≤ cap.decode := by
        rw [← he]; exact h
      simp [hh, ht, hd]

theorem candidatesFor_cost {cap : Fraction} {s : State} {items : List Item} {a b w : ℕ}
    (hs : s.Width a) (hi : ∀ i ∈ items, i.Width b)
    (hc : cap.Width w) (hw : a+2*b+1 ≤ w) :
    (candidatesFor cap s items).2 ≤
      items.length * (2048*(w+1)^2 + s.choices.length + 8) + 1 := by
  induction items with
  | nil => simp [candidatesFor]
  | cons i is ih =>
    have hitem := hi i (by simp)
    have he := extend_cost hs hitem
    have ew := (extend_width hs hitem).1
    have hm := compare_cost (Fraction.width_mono ew hw) hc
    have ht := ih (fun j hj => hi j (by simp [hj]))
    have hp : (a+b+1)^2 ≤ (w+1)^2 := Nat.pow_le_pow_left (by omega) 2
    simp only [candidatesFor, List.length_cons]
    nlinarith

/-- Generate all candidates, charging the list append as well as arithmetic. -/
def expand : Fraction → List State → List Item → List State × ℕ
  | _, [], _ => ([], 1)
  | cap, s :: ss, items =>
      let head := candidatesFor cap s items
      let tail := expand cap ss items
      (head.1 ++ tail.1, head.2 + tail.2 + head.1.length + 4)

theorem expand_member {cap : Fraction} {states : List State} {items : List Item} {t : State}
    (ht : t ∈ (expand cap states items).1) :
    ∃ s ∈ states, ∃ i ∈ items, t = (extend s i).1 := by
  induction states with
  | nil => simp [expand] at ht
  | cons s ss ih =>
    simp only [expand, List.mem_append] at ht
    rcases ht with hh | ht
    · obtain ⟨i,hi,he⟩ := candidatesFor_member hh
      exact ⟨s,by simp,i,hi,he⟩
    · obtain ⟨t',ht',i,hi,he⟩ := ih ht
      exact ⟨t',by simp [ht'],i,hi,he⟩

theorem expand_length (cap : Fraction) (states : List State) (items : List Item) :
    (expand cap states items).1.length ≤ states.length * items.length := by
  induction states with
  | nil => simp [expand]
  | cons s ss ih =>
    have hh := candidatesFor_length cap s items
    simp only [expand, List.length_append, List.length_cons]
    nlinarith

theorem expand_decode {cap : Fraction} {states : List State} {items : List Item} {θ : ℚ}
    (hc : cap.Valid) (hs : ∀ s ∈ states, s.Valid)
    (hi : ∀ i ∈ items, i.Valid ∧ value i.scaled = Knapsack.scaledProfit θ i.decode) :
    (expand cap states items).1.map State.decode =
      ((states.map State.decode).flatMap fun s => (items.map Item.decode).map
        (Knapsack.extend θ s)).filter (fun s => s.weight ≤ cap.decode) := by
  induction states with
  | nil => rfl
  | cons s ss ih =>
    have hh := candidatesFor_decode hc (hs s (by simp)) hi
    have ht := ih (fun t ht => hs t (by simp [ht]))
    simp only [expand, List.map_append, List.map_cons, List.flatMap_cons, List.filter_append]
    rw [hh, ht]

theorem expand_cost {cap : Fraction} {states : List State} {items : List Item} {a b w n : ℕ}
    (hs : ∀ s ∈ states, s.Width a ∧ s.choices.length ≤ n)
    (hi : ∀ i ∈ items, i.Width b) (hc : cap.Width w) (hw : a+2*b+1 ≤ w) :
    (expand cap states items).2 ≤
      states.length * (items.length * (2048*(w+1)^2+n+10) + 5) + 1 := by
  induction states with
  | nil => simp [expand]
  | cons s ss ih =>
    have hstate := hs s (by simp)
    have hh := candidatesFor_cost hstate.1 hi hc hw
    have hl := candidatesFor_length cap s items
    have ht := ih (fun t ht => hs t (by simp [ht]))
    simp only [expand, List.length_cons]
    nlinarith

end BalancedAssortments.KnapsackCostState
