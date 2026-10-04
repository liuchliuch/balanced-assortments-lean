import BalancedAssortments.KnapsackCostState

namespace BalancedAssortments.KnapsackCostState

theorem path_valid {items : List Item} {s : State} (hs : Path items s)
    (hi : ∀ i ∈ items, i.Valid) : s.Valid := by
  revert hi
  induction hs with
  | nil => intro _; exact initial_valid
  | @snoc items s i hp ih =>
    intro hi
    exact extend_valid (ih (fun j hj => hi j (by simp [hj]))) (hi i (by simp))

/-- Every state of the certified rational DP admits an unreduced bit-list
representation whose width is linear in the number of selected items. The
encoding map supplies preprocessed option representations and scaled scores. -/
theorem selection_bit_representation {θ : ℚ} {groups : List (List Knapsack.Item)}
    {s : Knapsack.State} {b : ℕ} (enc : Knapsack.Item → Item)
    (hsel : Knapsack.Selection θ groups s)
    (henc : ∀ group ∈ groups, ∀ item ∈ group,
      (enc item).Valid ∧ (enc item).Width b ∧ (enc item).decode = item ∧
      ComplexityTimeBinary.value (enc item).scaled = Knapsack.scaledProfit θ item) :
    ∃ bs : State, bs.Valid ∧ bs.decode = s ∧ bs.Width (1 + groups.length * (2*b+1)) ∧
      bs.choices.length = groups.length := by
  revert henc
  induction hsel with
  | nil =>
    intro _
    refine ⟨initial, initial_valid, initial_decode, ?_, rfl⟩
    simpa using initial_width
  | @snoc groups prev group item hp hi ih =>
    intro henc
    have he := henc group (by simp) item hi
    obtain ⟨bs, hbs, hbseq, hbw, hbl⟩ := ih (fun g hg it hit => henc g (by simp [hg]) it hit)
    refine ⟨(extend bs (enc item)).1, extend_valid hbs he.1, ?_, ?_, ?_⟩
    · rw [extend_decode hbs he.1 (by simpa [he.2.2.1] using he.2.2.2), hbseq, he.2.2.1]
    · have hh := extend_width hbw he.2.1
      convert hh using 1 <;> simp [Nat.add_mul] <;> omega
    · simp [extend, hbl]

/-- The width invariant applies to every actual DP table entry. -/
theorem table_bit_representation {θ capacity : ℚ} {bound : ℕ}
    {groups : List (List Knapsack.Item)} {s : Knapsack.State} {b : ℕ}
    (enc : Knapsack.Item → Item)
    (hs : s ∈ Knapsack.table θ capacity bound groups)
    (henc : ∀ group ∈ groups, ∀ item ∈ group,
      (enc item).Valid ∧ (enc item).Width b ∧ (enc item).decode = item ∧
      ComplexityTimeBinary.value (enc item).scaled = Knapsack.scaledProfit θ item) :
    ∃ bs : State, bs.Valid ∧ bs.decode = s ∧ bs.Width (1 + groups.length * (2*b+1)) ∧
      bs.choices.length = groups.length :=
  selection_bit_representation enc (Knapsack.reachable_selection (Knapsack.table_sound hs)) henc

end BalancedAssortments.KnapsackCostState
