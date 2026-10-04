import BalancedAssortments.KnapsackCostSolve

/-! Profit-scaling preprocessing on already supplied binary fractions. Only
long division/cross multiplication is used; there is no rational arithmetic oracle. -/
namespace BalancedAssortments.KnapsackCostState
open ComplexityTimeBinary KnapsackCostRational

/-- Existing score bits are ignored and replaced with floor(profit/θ). -/
def rescale (θ : Fraction) (i : Item) : Item × ℕ :=
  let k := floorRatio i.profit θ
  (⟨i.value, i.weight, i.profit, k.1⟩, k.2+4)

@[simp] theorem rescale_decode (θ : Fraction) (i : Item) : (rescale θ i).1.decode = i.decode := rfl

theorem rescale_valid (θ : Fraction) {i : Item} (hi : i.Valid) : (rescale θ i).1.Valid := hi

theorem rescale_correct {θ : Fraction} {i : Item}
    (ht : θ.Valid) (htp : 0 < θ.decode) (hi : i.Valid) :
    value (rescale θ i).1.scaled = Knapsack.scaledProfit θ.decode i.decode :=
  floorRatio_correct hi.2.2 ht htp

theorem rescale_width {θ : Fraction} {i : Item} {b : ℕ}
    (ht : θ.Width b) (hi : i.value.Width b ∧ i.weight.Width b ∧ i.profit.Width b) :
    (rescale θ i).1.Width (3*b) :=
  ⟨Fraction.width_mono hi.1 (by omega), Fraction.width_mono hi.2.1 (by omega),
    Fraction.width_mono hi.2.2 (by omega), floorRatio_width hi.2.2 ht⟩

def prepareGroup : Fraction → List Item → List Item × ℕ
  | _, [] => ([],1)
  | θ, i :: is =>
      let head := rescale θ i
      let tail := prepareGroup θ is
      (head.1 :: tail.1, head.2 + tail.2 + 4)

theorem prepareGroup_eq (θ : Fraction) (items : List Item) :
    (prepareGroup θ items).1 = items.map (fun i => (rescale θ i).1) := by
  induction items with
  | nil => rfl
  | cons i is ih => simp [prepareGroup, ih]

theorem prepareGroup_cost {θ : Fraction} {items : List Item} {b : ℕ}
    (ht : θ.Width b) (hi : ∀ i ∈ items, i.profit.Width b) :
    (prepareGroup θ items).2 ≤ items.length * (4096*(b+1)^2+8) + 1 := by
  induction items with
  | nil => simp [prepareGroup]
  | cons i is ih =>
    have hh := floorRatio_cost (hi i (by simp)) ht
    have ht' := ih (fun j hj => hi j (by simp [hj]))
    simp only [prepareGroup, rescale, List.length_cons]
    nlinarith

def prepareGroups : Fraction → List (List Item) → List (List Item) × ℕ
  | _, [] => ([],1)
  | θ, g :: gs =>
      let head := prepareGroup θ g
      let tail := prepareGroups θ gs
      (head.1 :: tail.1, head.2 + tail.2 + 4)

theorem prepareGroups_eq (θ : Fraction) (groups : List (List Item)) :
    (prepareGroups θ groups).1 = groups.map (List.map fun i => (rescale θ i).1) := by
  induction groups with
  | nil => rfl
  | cons g gs ih => simp [prepareGroups, prepareGroup_eq, ih]

theorem prepareGroups_cost {θ : Fraction} {groups : List (List Item)} {b M : ℕ}
    (ht : θ.Width b) (hi : ∀ g ∈ groups, g.length ≤ M ∧ ∀ i ∈ g, i.profit.Width b) :
    (prepareGroups θ groups).2 ≤ groups.length * (M*(4096*(b+1)^2+8)+5) + 1 := by
  induction groups with
  | nil => simp [prepareGroups]
  | cons g gs ih =>
    have hg := hi g (by simp)
    have hh := prepareGroup_cost ht hg.2
    have hm := Nat.mul_le_mul_right (4096*(b+1)^2+8) hg.1
    have ht' := ih (fun g hg => hi g (by simp [hg]))
    simp only [prepareGroups, List.length_cons]
    nlinarith

def scaledSolve (θ cap : Fraction) (bound : ℕ) (groups : List (List Item)) : Option State × ℕ :=
  let prep := prepareGroups θ groups
  let sol := solve cap bound prep.1
  (sol.1, prep.2 + sol.2 + 4)

/-- The complete scaled solver, including floor preprocessing, refines the
rational solver on the same source items with no assumption on their old score bits. -/
theorem scaledSolve_decode {θ cap : Fraction} {bound : ℕ} {groups : List (List Item)}
    (ht : θ.Valid) (htp : 0 < θ.decode) (hc : cap.Valid)
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Valid) :
    (scaledSolve θ cap bound groups).1.map State.decode =
      Knapsack.solve θ.decode cap.decode bound (groups.map (List.map Item.decode)) := by
  have hp : ∀ g ∈ (prepareGroups θ groups).1, ∀ i ∈ g,
      i.Valid ∧ value i.scaled = Knapsack.scaledProfit θ.decode i.decode := by
    intro g hg i hig
    rw [prepareGroups_eq] at hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    obtain ⟨i',hi',rfl⟩ := List.mem_map.mp hig
    exact ⟨rescale_valid θ (hi g' hg' i' hi'), rescale_correct ht htp (hi g' hg' i' hi')⟩
  have he := solve_decode (bound := bound) hc hp
  have hgroups : (prepareGroups θ groups).1.map (List.map Item.decode) =
      groups.map (List.map Item.decode) := by
    rw [prepareGroups_eq, List.map_map]
    apply List.map_congr_left
    intro g _
    simp only [Function.comp_apply, List.map_map]
    rfl
  simpa only [scaledSolve, hgroups] using he

/-- End-to-end binary cost with explicit scaled-profit preprocessing. -/
theorem scaledSolve_cost {θ cap : Fraction} {bound : ℕ} {groups : List (List Item)} {b M : ℕ}
    (ht : θ.Width b) (hc : cap.Width b)
    (hi : ∀ g ∈ groups, g.length ≤ M ∧ ∀ i ∈ g,
      i.value.Width b ∧ i.weight.Width b ∧ i.profit.Width b) :
    let N := groups.length
    let W := 1 + N*(6*b+1) + 2*(bound+1) + 3*b
    (scaledSolve θ cap bound groups).2 ≤
      N*(M*(4096*(b+1)^2+8)+5) +
      64*(bound+1)*(2*(bound+1)+1) +
      N*(rowCost (bound+1) M (bound+1) W N+4) +
      (bound+1)*(16*W+9)+20 := by
  have hp : ∀ g ∈ (prepareGroups θ groups).1, g.length ≤ M ∧ ∀ i ∈ g, i.Width (3*b) := by
    intro g hg
    rw [prepareGroups_eq] at hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    refine ⟨by simpa using (hi g' hg').1, ?_⟩
    intro i hig
    obtain ⟨i',hi',rfl⟩ := List.mem_map.mp hig
    exact rescale_width ht ((hi g' hg').2 i' hi')
  have hs := solve_cost (bound := bound) (Fraction.width_mono hc (show b ≤ 3*b by omega)) hp
  have hpc := prepareGroups_cost ht (fun g hg => ⟨(hi g hg).1, fun i hi' => ((hi g hg).2 i hi').2.2⟩)
  have hlen : (prepareGroups θ groups).1.length = groups.length := by simp [prepareGroups_eq]
  simp only [hlen, show 2*(3*b)+1 = 6*b+1 by omega] at hs
  simp only [scaledSolve]
  omega

theorem scaledSolve_valid {θ cap : Fraction} {bound : ℕ} {groups : List (List Item)}
    {s : State} (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Valid)
    (hs : (scaledSolve θ cap bound groups).1 = some s) : s.Valid := by
  apply solve_valid (groups := (prepareGroups θ groups).1) ?_ hs
  intro g hg i hig
  rw [prepareGroups_eq] at hg
  obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
  obtain ⟨i',hi',rfl⟩ := List.mem_map.mp hig
  exact rescale_valid θ (hi g' hg' i' hi')

theorem scaledSolve_width {θ cap : Fraction} {bound : ℕ} {groups : List (List Item)}
    {s : State} {b : ℕ} (ht : θ.Width b)
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.value.Width b ∧ i.weight.Width b ∧ i.profit.Width b)
    (hs : (scaledSolve θ cap bound groups).1 = some s) :
    s.Width (1+groups.length*(6*b+1)) ∧ s.choices.length ≤ groups.length := by
  have hp : ∀ g ∈ (prepareGroups θ groups).1, ∀ i ∈ g, i.Width (3*b) := by
    intro g hg i hig
    rw [prepareGroups_eq] at hg
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
    obtain ⟨i',hi',rfl⟩ := List.mem_map.mp hig
    exact rescale_width ht (hi g' hg' i' hi')
  have hm : s ∈ (table cap bound (prepareGroups θ groups).1).1 :=
    (selectMax_member hs).resolve_right (by simp)
  have hh := runRows_width (cap := cap) (scores := (KnapsackCostRange.scoreRange bound).1)
    (states := [initial]) (a := 1) (depth := 0)
    (by intro s hs; simp only [List.mem_singleton] at hs; subst s; exact ⟨initial_width, by simp [initial]⟩)
    hp s hm
  simpa only [prepareGroups_eq,List.length_map,Nat.zero_add,show 2*(3*b)+1=6*b+1 by omega] using hh

end BalancedAssortments.KnapsackCostState
