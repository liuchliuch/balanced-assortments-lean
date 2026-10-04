import BalancedAssortments.KnapsackCostDP

namespace BalancedAssortments.KnapsackCostState
open ComplexityTimeBinary KnapsackCostRational

def chooseMax (old : Option State) (candidate : State) : Option State × ℕ :=
  match old with
  | none => (some candidate, 2)
  | some s =>
      let cmp := compareBits s.scaled candidate.scaled
      (if cmp.1 = .lt then some candidate else some s, cmp.2 + 4)

theorem chooseMax_member {old : Option State} {candidate s : State}
    (hs : (chooseMax old candidate).1 = some s) : s = candidate ∨ old = some s := by
  cases old with
  | none => simp [chooseMax] at hs; exact Or.inl hs.symm
  | some o => simp only [chooseMax] at hs; split_ifs at hs <;> simp_all

theorem compare_score_lt (x y : List Bool) :
    (compareBits x y).1 = .lt ↔ value x < value y := by
  have h := compareBits_correct x y
  cases he : (compareBits x y).1 <;>
    simp only [he, comparisonMeaning] at h <;> simp <;> omega

theorem chooseMax_decode (old : Option State) (candidate : State) :
    (chooseMax old candidate).1.map State.decode =
      List.argAux (fun a b : Knapsack.State => b.scaled < a.scaled)
        (old.map State.decode) candidate.decode := by
  cases old with
  | none => rfl
  | some s =>
    simp only [chooseMax, List.argAux, Option.map_some]
    by_cases h : value s.scaled < value candidate.scaled
    · simp [((compare_score_lt _ _).mpr h), State.decode, h]
    · have hh : (compareBits s.scaled candidate.scaled).1 ≠ .lt :=
        fun hh => h ((compare_score_lt _ _).mp hh)
      simp [hh, State.decode, h]

def selectMax : List State → Option State → Option State × ℕ
  | [], old => (old, 1)
  | s :: ss, old =>
      let chosen := chooseMax old s
      let rest := selectMax ss chosen.1
      (rest.1, chosen.2 + rest.2 + 4)

theorem selectMax_decode (states : List State) (old : Option State) :
    (selectMax states old).1.map State.decode =
      (states.map State.decode).foldl
        (List.argAux (fun a b : Knapsack.State => b.scaled < a.scaled)) (old.map State.decode) := by
  induction states generalizing old with
  | nil => rfl
  | cons s ss ih => simp only [selectMax, List.map_cons, List.foldl_cons, ih, chooseMax_decode]

theorem selectMax_cost {states : List State} {old : Option State} {b : ℕ}
    (ho : ∀ s, old = some s → s.scaled.length ≤ b)
    (hs : ∀ s ∈ states, s.scaled.length ≤ b) :
    (selectMax states old).2 ≤ states.length * (16*b+9) + 1 := by
  induction states generalizing old with
  | nil => simp [selectMax]
  | cons s ss ih =>
    have hc : (chooseMax old s).2 ≤ 16*b+5 := by
      cases old with
      | none => simp [chooseMax]
      | some t =>
        have hmax : max t.scaled.length s.scaled.length ≤ b :=
          max_le (ho t rfl) (hs s (by simp))
        simp only [chooseMax, compareBits_cost]
        omega
    have hcw : ∀ t, (chooseMax old s).1 = some t → t.scaled.length ≤ b := by
      intro t ht
      rcases chooseMax_member ht with rfl | ht
      · exact hs t (by simp)
      · exact ho t ht
    have ht := ih hcw (fun t ht => hs t (by simp [ht]))
    simp only [selectMax, List.length_cons]
    nlinarith

theorem runRows_length (cap : Fraction) (scores : List (List Bool)) (states : List State)
    (groups : List (List Item)) (h : states.length ≤ scores.length) :
    (runRows cap scores states groups).1.length ≤ scores.length := by
  induction groups generalizing states with
  | nil => exact h
  | cons g gs ih => exact ih _ (advance_length cap scores states g)

theorem runRows_width {cap : Fraction} {scores : List (List Bool)} {states : List State}
    {groups : List (List Item)} {a b depth : ℕ}
    (hs : ∀ s ∈ states, s.Width a ∧ s.choices.length ≤ depth)
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Width b) :
    ∀ s ∈ (runRows cap scores states groups).1,
      s.Width (a+groups.length*(2*b+1)) ∧ s.choices.length ≤ depth+groups.length := by
  induction groups generalizing states a depth with
  | nil => simpa using hs
  | cons g gs ih =>
    have hh := advance_width (cap := cap) (scores := scores) hs (hi g (by simp))
    have ht := ih hh (fun g hg i hi' => hi g (by simp [hg]) i hi')
    simp only [runRows, List.length_cons]
    simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ht

def solve (cap : Fraction) (bound : ℕ) (groups : List (List Item)) : Option State × ℕ :=
  let rows := table cap bound groups
  let result := selectMax rows.1 none
  (result.1, rows.2 + result.2 + 4)

/-- End-to-end exact refinement of the certified rational knapsack solver. -/
theorem solve_decode {cap : Fraction} {bound : ℕ} {groups : List (List Item)} {θ : ℚ}
    (hc : cap.Valid)
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Valid ∧ value i.scaled = Knapsack.scaledProfit θ i.decode) :
    (solve cap bound groups).1.map State.decode =
      Knapsack.solve θ cap.decode bound (groups.map (List.map Item.decode)) := by
  simp only [solve, selectMax_decode, table_decode hc hi, Knapsack.solve, List.argmax,
    Option.map_none]

/-- Full polynomial bit/list-operation bound for the preprocessed binary solver,
including score generation, all row comparisons, reconstruction and final maximization. -/
theorem solve_cost {cap : Fraction} {bound : ℕ} {groups : List (List Item)} {b M : ℕ}
    (hc : cap.Width b)
    (hi : ∀ g ∈ groups, g.length ≤ M ∧ ∀ i ∈ g, i.Width b) :
    let W := 1 + groups.length*(2*b+1) + 2*(bound+1) + b
    (solve cap bound groups).2 ≤
      64*(bound+1)*(2*(bound+1)+1) +
        groups.length * (rowCost (bound+1) M (bound+1) W groups.length + 4) +
        (bound+1)*(16*W+9) + 15 := by
  let W := 1 + groups.length*(2*b+1) + 2*(bound+1) + b
  have ht := table_cost (bound := bound) hc hi
  have hlen : (table cap bound groups).1.length ≤ bound+1 := by
    have hh := runRows_length cap (KnapsackCostRange.scoreRange bound).1 [initial] groups
      (by simp [KnapsackCostRange.scoreRange, KnapsackCostRange.rangeFrom_length])
    simpa only [table, KnapsackCostRange.scoreRange, KnapsackCostRange.rangeFrom_length] using hh
  have hw := runRows_width (cap := cap) (scores := (KnapsackCostRange.scoreRange bound).1)
    (states := [initial]) (a := 1) (depth := 0)
    (by intro s hs; simp only [List.mem_singleton] at hs; subst s; exact ⟨initial_width, by simp [initial]⟩)
    (fun g hg => (hi g hg).2)
  have hs : ∀ s ∈ (table cap bound groups).1, s.scaled.length ≤ W := by
    intro s hs
    have hh := (hw s hs).1.2.2.1
    exact hh.trans (by dsimp [W]; omega)
  have hm := selectMax_cost (old := none) (by simp) hs
  have hm' := Nat.mul_le_mul_right (16*W+9) hlen
  simp only [solve]
  dsimp only [W] at *
  omega

theorem selectMax_member {states : List State} {old : Option State} {s : State}
    (hs : (selectMax states old).1 = some s) : s ∈ states ∨ old = some s := by
  induction states generalizing old with
  | nil => exact Or.inr hs
  | cons t ts ih =>
    rcases ih hs with hm | hm
    · exact Or.inl (List.mem_cons_of_mem _ hm)
    · rcases chooseMax_member hm with rfl | hm
      · exact Or.inl (by simp)
      · exact Or.inr hm

theorem runRows_valid {cap : Fraction} {scores : List (List Bool)} {states : List State}
    {groups : List (List Item)} (hs : ∀ s ∈ states, s.Valid)
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Valid) :
    ∀ s ∈ (runRows cap scores states groups).1, s.Valid := by
  induction groups generalizing states with
  | nil => exact hs
  | cons g gs ih =>
    exact ih (advance_valid hs (hi g (by simp))) (fun g hg i hi' => hi g (by simp [hg]) i hi')

theorem solve_valid {cap : Fraction} {bound : ℕ} {groups : List (List Item)}
    {s : State} (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Valid)
    (hs : (solve cap bound groups).1 = some s) : s.Valid := by
  have hm : s ∈ (table cap bound groups).1 :=
    (selectMax_member hs).resolve_right (by simp)
  exact runRows_valid (by intro s hs; simp only [List.mem_singleton] at hs; subst s; exact initial_valid) hi s hm

end BalancedAssortments.KnapsackCostState
