import BalancedAssortments.KnapsackCostTransition

namespace BalancedAssortments.KnapsackCostState
open ComplexityTimeBinary KnapsackCostRational

def advance (cap : Fraction) (scores : List (List Bool)) (states : List State)
    (items : List Item) : List State × ℕ :=
  let expanded := expand cap states items
  let compressed := compress expanded.1 scores
  (compressed.1, expanded.2 + compressed.2 + 4)

theorem State.width_mono {s : State} {a b : ℕ} (hs : s.Width a) (hab : a ≤ b) : s.Width b :=
  ⟨Fraction.width_mono hs.1 hab, Fraction.width_mono hs.2.1 hab, hs.2.2.1.trans hab,
    fun q hq => Fraction.width_mono (hs.2.2.2 q hq) hab⟩

theorem advance_member {cap : Fraction} {scores : List (List Bool)} {states : List State}
    {items : List Item} {t : State} (ht : t ∈ (advance cap scores states items).1) :
    ∃ s ∈ states, ∃ i ∈ items, t = (extend s i).1 :=
  expand_member (compress_member ht)

theorem advance_length (cap : Fraction) (scores : List (List Bool)) (states : List State)
    (items : List Item) : (advance cap scores states items).1.length ≤ scores.length :=
  compress_length _ _

theorem advance_valid {cap : Fraction} {scores : List (List Bool)} {states : List State}
    {items : List Item} (hs : ∀ s ∈ states, s.Valid) (hi : ∀ i ∈ items, i.Valid) :
    ∀ t ∈ (advance cap scores states items).1, t.Valid := by
  intro t ht
  obtain ⟨s,hs',i,hi',rfl⟩ := advance_member ht
  exact extend_valid (hs s hs') (hi i hi')

theorem advance_width {cap : Fraction} {scores : List (List Bool)} {states : List State}
    {items : List Item} {a b n : ℕ}
    (hs : ∀ s ∈ states, s.Width a ∧ s.choices.length ≤ n)
    (hi : ∀ i ∈ items, i.Width b) :
    ∀ t ∈ (advance cap scores states items).1,
      t.Width (a+2*b+1) ∧ t.choices.length ≤ n+1 := by
  intro t ht
  obtain ⟨s,hs',i,hi',rfl⟩ := advance_member ht
  refine ⟨extend_width (hs s hs').1 (hi i hi'), ?_⟩
  simp only [extend, List.length_append, List.length_singleton]
  exact Nat.add_le_add_right (hs s hs').2 1

/-- One complete binary row is extension/filter/compression of exactly the same
states as the certified rational DP, with every score index supplied in order. -/
theorem advance_decode {cap : Fraction} {scores : List (List Bool)} {states : List State}
    {items : List Item} {θ : ℚ} {bound : ℕ}
    (hc : cap.Valid) (hs : ∀ s ∈ states, s.Valid)
    (hi : ∀ i ∈ items, i.Valid ∧ value i.scaled = Knapsack.scaledProfit θ i.decode)
    (hp : scores.map value = List.range (bound+1)) :
    (advance cap scores states items).1.map State.decode =
      Knapsack.advance θ cap.decode bound (states.map State.decode) (items.map Item.decode) := by
  have hev : ∀ t ∈ (expand cap states items).1, t.Valid := by
    intro t ht
    obtain ⟨s,hs',i,hi',rfl⟩ := expand_member ht
    exact extend_valid (hs s hs') (hi i hi').1
  have hh := compress_decode scores hev
  rw [expand_decode hc hs hi] at hh
  change _ = _ at hh
  unfold advance
  rw [hh]
  unfold Knapsack.advance
  rw [← hp, List.filterMap_map]
  rfl

/-- Explicit polynomial for a complete row, in row length, options, score
indices, bit width, and reconstruction length. -/
def rowCost (R M S W N : ℕ) : ℕ :=
  R * (M * (2048*(W+1)^2+N+10) + 5) + S * (R*M*(1024*(W+1)^2)+5) + 6

theorem advance_cost {cap : Fraction} {scores : List (List Bool)} {states : List State}
    {items : List Item} {a b w n : ℕ}
    (hs : ∀ s ∈ states, s.Width a ∧ s.choices.length ≤ n)
    (hi : ∀ i ∈ items, i.Width b) (hc : cap.Width w)
    (hw : a+2*b+1 ≤ w) (hp : ∀ p ∈ scores, p.length ≤ w) :
    (advance cap scores states items).2 ≤ rowCost states.length items.length scores.length w n := by
  have he := expand_cost hs hi hc hw
  have hl := expand_length cap states items
  have hew : ∀ s ∈ (expand cap states items).1, s.Width w := by
    intro t ht
    obtain ⟨s,hs',i,hi',rfl⟩ := expand_member ht
    exact State.width_mono (extend_width (hs s hs').1 (hi i hi')) hw
  have hc' := compress_cost hp hew
  have hm := Nat.mul_le_mul_right (1024*(w+1)^2) hl
  have hm' := Nat.mul_le_mul_left scores.length hm
  simp only [advance, rowCost]
  nlinarith

def runRows : Fraction → List (List Bool) → List State → List (List Item) → List State × ℕ
  | _, _, states, [] => (states, 1)
  | cap, scores, states, items :: rest =>
      let row := advance cap scores states items
      let tail := runRows cap scores row.1 rest
      (tail.1, row.2 + tail.2 + 4)

theorem runRows_decode {cap : Fraction} {scores : List (List Bool)} {states : List State}
    {groups : List (List Item)} {θ : ℚ} {bound : ℕ}
    (hc : cap.Valid) (hs : ∀ s ∈ states, s.Valid)
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Valid ∧ value i.scaled = Knapsack.scaledProfit θ i.decode)
    (hp : scores.map value = List.range (bound+1)) :
    (runRows cap scores states groups).1.map State.decode =
      (groups.map (List.map Item.decode)).foldl (Knapsack.advance θ cap.decode bound)
        (states.map State.decode) := by
  induction groups generalizing states with
  | nil => rfl
  | cons g gs ih =>
    have hg := hi g (by simp)
    have ht : ∀ g ∈ gs, ∀ i ∈ g, i.Valid ∧ value i.scaled = Knapsack.scaledProfit θ i.decode :=
      fun g hg i hi' => hi g (by simp [hg]) i hi'
    have hh := ih (advance_valid (cap := cap) (scores := scores) hs (fun i hi' => (hg i hi').1)) ht
    simp only [runRows, List.map_cons, List.foldl_cons]
    rw [hh, advance_decode hc hs hg hp]

theorem rowCost_mono {R R' M M' S W N N' : ℕ}
    (hR : R ≤ R') (hM : M ≤ M') (hN : N ≤ N') :
    rowCost R M S W N ≤ rowCost R' M' S W N' := by
  unfold rowCost
  gcongr

theorem runRows_cost {cap : Fraction} {scores : List (List Bool)} {states : List State}
    {groups : List (List Item)} {a b W depth N M : ℕ}
    (hc : cap.Width W) (hp : ∀ p ∈ scores, p.length ≤ W)
    (hslen : states.length ≤ scores.length)
    (hs : ∀ s ∈ states, s.Width a ∧ s.choices.length ≤ depth)
    (hi : ∀ g ∈ groups, g.length ≤ M ∧ ∀ i ∈ g, i.Width b)
    (hw : a + groups.length * (2*b+1) ≤ W)
    (hn : depth + groups.length ≤ N) :
    (runRows cap scores states groups).2 ≤
      groups.length * (rowCost scores.length M scores.length W N + 4) + 1 := by
  induction groups generalizing states a depth with
  | nil => simp [runRows]
  | cons g gs ih =>
    have hg := hi g (by simp)
    have ht : ∀ g ∈ gs, g.length ≤ M ∧ ∀ i ∈ g, i.Width b :=
      fun g hg => hi g (by simp [hg])
    have hwstep : a+2*b+1 ≤ W := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hw
      omega
    have hcost := advance_cost hs hg.2 hc hwstep hp
    have hmono := rowCost_mono (S := scores.length) (W := W) hslen hg.1 (show depth ≤ N by omega)
    have hs' := advance_width (cap := cap) (scores := scores) hs hg.2
    have hw' : a+2*b+1 + gs.length*(2*b+1) ≤ W := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hw
      omega
    have htCost := ih (advance_length cap scores states g) hs' ht hw' (by simp only [List.length_cons] at hn; omega)
    simp only [runRows, List.length_cons]
    nlinarith

def table (cap : Fraction) (bound : ℕ) (groups : List (List Item)) : List State × ℕ :=
  let range := KnapsackCostRange.scoreRange bound
  let rows := runRows cap range.1 [initial] groups
  (rows.1, range.2 + rows.2 + 8)

/-- Complete table refinement, including binary enumeration of scaled-score indices. -/
theorem table_decode {cap : Fraction} {bound : ℕ} {groups : List (List Item)} {θ : ℚ}
    (hc : cap.Valid)
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Valid ∧ value i.scaled = Knapsack.scaledProfit θ i.decode) :
    (table cap bound groups).1.map State.decode =
      Knapsack.table θ cap.decode bound (groups.map (List.map Item.decode)) := by
  have hh := runRows_decode hc (states := [initial])
    (by intro s hs; simp only [List.mem_singleton] at hs; subst s; exact initial_valid)
    hi (KnapsackCostRange.scoreRange_values bound)
  simpa only [table, Knapsack.table, List.map_singleton, initial_decode] using hh

/-- A concrete polynomial bit/list cost for the entire preprocessed knapsack
table. This is charged binary arithmetic and list traversal, not a state count. -/
theorem table_cost {cap : Fraction} {bound : ℕ} {groups : List (List Item)} {b M : ℕ}
    (hc : cap.Width b)
    (hi : ∀ g ∈ groups, g.length ≤ M ∧ ∀ i ∈ g, i.Width b) :
    let W := 1 + groups.length*(2*b+1) + 2*(bound+1) + b
    (table cap bound groups).2 ≤
      64*(bound+1)*(2*(bound+1)+1) +
        groups.length * (rowCost (bound+1) M (bound+1) W groups.length + 4) + 10 := by
  let W := 1 + groups.length*(2*b+1) + 2*(bound+1) + b
  have hp : ∀ p ∈ (KnapsackCostRange.scoreRange bound).1, p.length ≤ W := by
    intro p hp
    have hh := KnapsackCostRange.rangeFrom_width (bound+1) [] p hp
    simp only [List.length_nil, Nat.zero_add] at hh
    exact hh.trans (by dsimp [W]; omega)
  have hrlen : (KnapsackCostRange.scoreRange bound).1.length = bound+1 :=
    KnapsackCostRange.rangeFrom_length _ _
  have hrows := runRows_cost (a := 1) (depth := 0) (N := groups.length)
    (Fraction.width_mono hc (show b ≤ W by dsimp [W]; omega)) hp
    (states := [initial]) (by simp [hrlen])
    (by intro s hs; simp only [List.mem_singleton] at hs; subst s; exact ⟨initial_width, by simp [initial]⟩)
    hi (show 1 + groups.length*(2*b+1) ≤ W by dsimp [W]; omega) (by omega)
  have hrange := KnapsackCostRange.rangeFrom_cost (bound+1) []
  simp only [List.length_nil, Nat.zero_add] at hrange
  rw [hrlen] at hrows
  simp only [table]
  dsimp only [KnapsackCostRange.scoreRange, W] at *
  omega

end BalancedAssortments.KnapsackCostState
