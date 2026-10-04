import Mathlib

/-!
# Rational multiple-choice profit-scaling dynamic program

`solve` is executable. It retains exact rational weights, one representative per
scaled-profit total, and full reconstruction lists. The recurrence is proved sound and scaled-score optimal. Its additive and
relative profit guarantees are certified. A concrete polynomial state-bound
instantiation, the outer assortment reduction, and bit-cost model are separate.
-/
namespace BalancedAssortments.Knapsack

structure Item where
  value : ℚ
  weight : ℚ
  profit : ℚ
  deriving DecidableEq, Repr

/-- All arithmetic used by the executable routine is rational or integer. -/
def scaledProfit (θ : ℚ) (item : Item) : ℕ := ⌊item.profit / θ⌋₊

structure State where
  weight : ℚ
  profit : ℚ
  scaled : ℕ
  choices : List ℚ
  deriving DecidableEq, Repr

def initial : State := ⟨0, 0, 0, []⟩

def extend (θ : ℚ) (s : State) (item : Item) : State :=
  ⟨s.weight + item.weight, s.profit + item.profit,
    s.scaled + scaledProfit θ item, s.choices ++ [item.value]⟩

/-- Choose a minimum exact weight, with deterministic first-encountered tie breaking. -/
def lighter (a b : Option State) : Option State :=
  match a, b with
  | none, x => x
  | x, none => x
  | some x, some y => if x.weight ≤ y.weight then some x else some y

def bestAt (states : List State) (profit : ℕ) : Option State :=
  (states.filter (fun s => s.scaled = profit)).argmin State.weight

/-- One multiple-choice transition followed by compression to one state per score. -/
def advance (θ capacity : ℚ) (bound : ℕ) (row : List State) (group : List Item) :
    List State :=
  let candidates := (row.flatMap fun s => group.map (extend θ s)).filter
    (fun s => s.weight ≤ capacity)
  (List.range (bound + 1)).filterMap (bestAt candidates)

/-- Each group must contain its zero item; bound is the maximum total scaled profit. -/
def table (θ capacity : ℚ) (bound : ℕ) (groups : List (List Item)) : List State :=
  groups.foldl (advance θ capacity bound) [initial]

def betterScore (a b : Option State) : Option State :=
  match a, b with
  | none, x => x
  | x, none => x
  | some x, some y => if y.scaled ≤ x.scaled then some x else some y

/-- The returned state contains the rational values and exact original profit. -/
def solve (θ capacity : ℚ) (bound : ℕ) (groups : List (List Item)) : Option State :=
  (table θ capacity bound groups).argmax State.scaled

theorem extend_weight (θ : ℚ) (s : State) (item : Item) :
    (extend θ s item).weight = s.weight + item.weight := rfl

theorem extend_profit (θ : ℚ) (s : State) (item : Item) :
    (extend θ s item).profit = s.profit + item.profit := rfl

theorem extend_choices_length (θ : ℚ) (s : State) (item : Item) :
    (extend θ s item).choices.length = s.choices.length + 1 := by
  simp [extend]

/-- Score compression selects an actual candidate with the requested score. -/
theorem bestAt_mem {states : List State} {p : ℕ} {s : State}
    (h : bestAt states p = some s) : s ∈ states ∧ s.scaled = p := by
  have := List.argmin_mem h
  simpa [bestAt, List.mem_filter] using this

/-- Score compression preserves a candidate of minimum exact weight. -/
theorem bestAt_dominates {states : List State} {p : ℕ} {s t : State}
    (hs : bestAt states p = some s) (ht : t ∈ states) (hp : t.scaled = p) :
    s.weight ≤ t.weight := by
  apply List.le_of_mem_argmin (f := State.weight) _ hs
  simp [List.mem_filter, ht, hp]

theorem bestAt_exists {states : List State} {t : State} (ht : t ∈ states) :
    ∃ s, bestAt states t.scaled = some s := by
  cases h : bestAt states t.scaled with
  | some s => exact ⟨s, rfl⟩
  | none =>
    have he := List.argmin_eq_none.mp h
    have hm : t ∈ states.filter (fun s => s.scaled = t.scaled) := by simp [ht]
    rw [he] at hm
    simp at hm

/-- Every retained row state arises from a legal group transition and meets capacity. -/
theorem mem_advance {θ capacity : ℚ} {bound : ℕ} {row : List State}
    {group : List Item} {s : State} (hs : s ∈ advance θ capacity bound row group) :
    ∃ prev ∈ row, ∃ item ∈ group, s = extend θ prev item ∧
      s.weight ≤ capacity ∧ s.scaled ≤ bound := by
  unfold advance at hs
  obtain ⟨p, hp, hps⟩ := List.mem_filterMap.mp hs
  obtain ⟨hc, heq⟩ := bestAt_mem hps
  simp only [List.mem_filter, decide_eq_true_eq, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨⟨prev, hprev, item, hitem, he⟩, hw⟩ := hc
  exact ⟨prev, hprev, item, hitem, he.symm, hw,
    by have := List.mem_range.mp hp; omega⟩

/-- A feasible transition with an in-range score is represented with no larger weight. -/
theorem advance_dominates {θ capacity : ℚ} {bound : ℕ} {row : List State}
    {group : List Item} {prev : State} {item : Item}
    (hp : prev ∈ row) (hi : item ∈ group)
    (hw : (extend θ prev item).weight ≤ capacity)
    (hb : (extend θ prev item).scaled ≤ bound) :
    ∃ s ∈ advance θ capacity bound row group,
      s.scaled = (extend θ prev item).scaled ∧
      s.weight ≤ (extend θ prev item).weight := by
  let candidates := (row.flatMap fun s => group.map (extend θ s)).filter
    (fun s => s.weight ≤ capacity)
  have ht : extend θ prev item ∈ candidates := by
    simp only [candidates, List.mem_filter, decide_eq_true_eq, List.mem_flatMap,
      List.mem_map]
    exact ⟨⟨prev, hp, item, hi, rfl⟩, hw⟩
  obtain ⟨s, hs⟩ := bestAt_exists ht
  refine ⟨s, ?_, (bestAt_mem hs).2, bestAt_dominates hs ht rfl⟩
  apply List.mem_filterMap.mpr
  exact ⟨(extend θ prev item).scaled, List.mem_range.mpr (by omega), hs⟩

/-- Final selection has maximum scaled score among all retained row states. -/
theorem solve_maximizes_row {θ capacity : ℚ} {bound : ℕ} {groups : List (List Item)}
    {s t : State} (hs : solve θ capacity bound groups = some s)
    (ht : t ∈ table θ capacity bound groups) : t.scaled ≤ s.scaled :=
  List.le_of_mem_argmax ht hs

/-- Compression stores at most one state per permitted integer score. -/
theorem advance_length (θ capacity : ℚ) (bound : ℕ) (row : List State) (group : List Item) :
    (advance θ capacity bound row group).length ≤ bound + 1 := by
  unfold advance
  exact (List.length_filterMap_le _ _).trans_eq (List.length_range)

theorem table_length (θ capacity : ℚ) (bound : ℕ) (groups : List (List Item)) :
    (table θ capacity bound groups).length ≤ bound + 1 := by
  induction groups using List.reverseRecOn with
  | nil => simp [table]
  | append_singleton gs g _ =>
    simp only [table, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact advance_length _ _ _ _ _

/-- Reference semantics: one option per group, with exact feasibility at every prefix. -/
inductive Reachable (θ capacity : ℚ) (bound : ℕ) : List (List Item) → State → Prop
  | nil : Reachable θ capacity bound [] initial
  | snoc {groups : List (List Item)} {prev : State} {group : List Item} {item : Item}
      (prior : Reachable θ capacity bound groups prev)
      (member : item ∈ group)
      (weight : (extend θ prev item).weight ≤ capacity)
      (score : (extend θ prev item).scaled ≤ bound) :
      Reachable θ capacity bound (groups ++ [group]) (extend θ prev item)

theorem table_append_singleton (θ capacity : ℚ) (bound : ℕ)
    (groups : List (List Item)) (group : List Item) :
    table θ capacity bound (groups ++ [group]) =
      advance θ capacity bound (table θ capacity bound groups) group := by
  simp [table, List.foldl_append]

/-- Every table state has a genuine, exactly feasible multiple-choice reconstruction. -/
theorem table_sound {θ capacity : ℚ} {bound : ℕ} {groups : List (List Item)}
    {s : State} (hs : s ∈ table θ capacity bound groups) :
    Reachable θ capacity bound groups s := by
  induction groups using List.reverseRecOn generalizing s with
  | nil =>
    simp only [table, List.foldl_nil, List.mem_singleton] at hs
    subst s
    exact Reachable.nil
  | append_singleton groups group ih =>
    rw [table_append_singleton] at hs
    obtain ⟨prev, hp, item, hi, rfl, hw, hb⟩ := mem_advance hs
    exact Reachable.snoc (ih hp) hi hw hb

/-- Compression preserves every reachable score using a no-heavier representative. -/
theorem table_complete {θ capacity : ℚ} {bound : ℕ} {groups : List (List Item)}
    {s : State} (hs : Reachable θ capacity bound groups s) :
    ∃ t ∈ table θ capacity bound groups, t.scaled = s.scaled ∧ t.weight ≤ s.weight := by
  induction hs with
  | nil => exact ⟨initial, by simp [table], rfl, le_rfl⟩
  | @snoc groups prev group item hprev hi hw hb ih =>
    obtain ⟨t, ht, hscore, hweight⟩ := ih
    have he : (extend θ t item).scaled = (extend θ prev item).scaled := by
      simp [extend, hscore]
    have hw' : (extend θ t item).weight ≤ capacity := by
      simp only [extend] at hw ⊢
      linarith
    obtain ⟨u, hu, hus, huw⟩ := advance_dominates (bound := bound) ht hi hw' (by omega)
    refine ⟨u, ?_, hus.trans he, ?_⟩
    · rw [table_append_singleton]
      exact hu
    · simp only [extend] at huw ⊢
      linarith

/-- The executable DP is an exact optimizer of scaled score over the bounded-prefix semantics. -/
theorem solve_optimal {θ capacity : ℚ} {bound : ℕ} {groups : List (List Item)}
    {s t : State} (hs : solve θ capacity bound groups = some s)
    (ht : Reachable θ capacity bound groups t) : t.scaled ≤ s.scaled := by
  obtain ⟨u, hu, he, _⟩ := table_complete ht
  have := solve_maximizes_row hs hu
  omega

theorem solve_sound {θ capacity : ℚ} {bound : ℕ} {groups : List (List Item)}
    {s : State} (hs : solve θ capacity bound groups = some s) :
    Reachable θ capacity bound groups s := table_sound (List.argmax_mem hs)

/-- Any reachable candidate ensures the DP returns a reconstructed state. -/
theorem solve_exists {θ capacity : ℚ} {bound : ℕ} {groups : List (List Item)}
    {t : State} (ht : Reachable θ capacity bound groups t) :
    ∃ s, solve θ capacity bound groups = some s := by
  obtain ⟨u, hu, _, _⟩ := table_complete ht
  cases h : solve θ capacity bound groups with
  | some s => exact ⟨s, rfl⟩
  | none =>
    have he := List.argmax_eq_none.mp h
    rw [he] at hu
    simp at hu

/-- Every reconstructed result obeys exact rational capacity and the state bound. -/
theorem reachable_feasible {θ capacity : ℚ} {bound : ℕ}
    {groups : List (List Item)} {s : State} (hc : 0 ≤ capacity)
    (hs : Reachable θ capacity bound groups s) :
    s.weight ≤ capacity ∧ s.scaled ≤ bound ∧ s.choices.length = groups.length := by
  induction hs with
  | nil => simp [initial, hc]
  | snoc _ _ hw hb ih =>
    exact ⟨hw, hb, by simp [extend, ih.2.2]⟩

theorem solve_feasible {θ capacity : ℚ} {bound : ℕ}
    {groups : List (List Item)} {s : State} (hc : 0 ≤ capacity)
    (hs : solve θ capacity bound groups = some s) :
    s.weight ≤ capacity ∧ s.scaled ≤ bound ∧ s.choices.length = groups.length :=
  reachable_feasible hc (solve_sound hs)

/-- Unpruned multiple-choice semantics: no capacity or state-bound assumptions. -/
inductive Selection (θ : ℚ) : List (List Item) → State → Prop
  | nil : Selection θ [] initial
  | snoc {groups : List (List Item)} {prev : State} {group : List Item} {item : Item}
      (prior : Selection θ groups prev) (member : item ∈ group) :
      Selection θ (groups ++ [group]) (extend θ prev item)

/-- Every reachable bounded selection also has the ordinary unpruned semantics. -/
theorem reachable_selection {θ capacity : ℚ} {bound : ℕ}
    {groups : List (List Item)} {s : State} (hs : Reachable θ capacity bound groups s) :
    Selection θ groups s := by
  induction hs with
  | nil => exact Selection.nil
  | snoc _ hi _ _ ih => exact Selection.snoc ih hi

/-- Complete reconstruction invariant: the stored coordinates and both exact
objectives are the maps/sums of one genuine item from each input group. -/
theorem selection_reconstruction {θ : ℚ} {groups : List (List Item)} {s : State}
    (hs : Selection θ groups s) :
    ∃ items : List Item,
      List.Forall₂ (fun item group => item ∈ group) items groups ∧
      s.choices = items.map Item.value ∧
      s.weight = (items.map Item.weight).sum ∧
      s.profit = (items.map Item.profit).sum ∧
      s.scaled = (items.map (scaledProfit θ)).sum := by
  induction hs with
  | nil => exact ⟨[], List.Forall₂.nil, rfl, rfl, rfl, rfl⟩
  | @snoc groups prev group item hprev hi ih =>
    obtain ⟨items, hitems, hc, hw, hp, hs⟩ := ih
    refine ⟨items ++ [item], List.rel_append hitems (List.Forall₂.cons hi List.Forall₂.nil), ?_⟩
    simp [extend, List.map_append, hc, hw, hp, hs]

/-- The executable solver's coordinate reconstruction has the same certified invariant. -/
theorem solve_reconstruction {θ capacity : ℚ} {bound : ℕ}
    {groups : List (List Item)} {s : State}
    (hs : solve θ capacity bound groups = some s) :
    ∃ items : List Item,
      List.Forall₂ (fun item group => item ∈ group) items groups ∧
      s.choices = items.map Item.value ∧
      s.weight = (items.map Item.weight).sum ∧
      s.profit = (items.map Item.profit).sum ∧
      s.scaled = (items.map (scaledProfit θ)).sum :=
  selection_reconstruction (reachable_selection (solve_sound hs))

/-- Build a comparison selection from a concrete option choice at each index. -/
def chooseState {ι : Type*} (θ : ℚ) (indices : List ι) (item : ι → Item) : State :=
  indices.foldl (fun s i => extend θ s (item i)) initial

theorem chooseState_selection {ι : Type*} (θ : ℚ) (indices : List ι)
    (item : ι → Item) (group : ι → List Item)
    (hm : ∀ i ∈ indices, item i ∈ group i) :
    Selection θ (indices.map group) (chooseState θ indices item) := by
  induction indices using List.reverseRecOn with
  | nil => exact Selection.nil
  | append_singleton is i ih =>
    have hp : ∀ j ∈ is, item j ∈ group j := fun j hj => hm j (by simp [hj])
    simpa only [chooseState, List.map_append, List.map_singleton, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using Selection.snoc (ih hp) (hm i (by simp))

theorem chooseState_sums {ι : Type*} (θ : ℚ) (indices : List ι) (item : ι → Item) :
    (chooseState θ indices item).choices = indices.map (fun i => (item i).value) ∧
    (chooseState θ indices item).weight = (indices.map (fun i => (item i).weight)).sum ∧
    (chooseState θ indices item).profit = (indices.map (fun i => (item i).profit)).sum := by
  induction indices using List.reverseRecOn with
  | nil => simp [chooseState, initial]
  | append_singleton is i ih =>
    simpa only [chooseState, List.foldl_append, List.foldl_cons, List.foldl_nil,
      extend, List.map_append, List.map_singleton, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero] using
      And.intro (congrArg (· ++ [(item i).value]) ih.1)
        (And.intro (congrArg (· + (item i).weight) ih.2.1)
          (congrArg (· + (item i).profit) ih.2.2))

/-- With nonnegative weights, a feasible final selection has feasible prefixes.
Natural scaled profits similarly ensure that score truncation preserves it. -/
theorem selection_reachable {θ capacity : ℚ} {bound : ℕ}
    {groups : List (List Item)} {s : State}
    (hs : Selection θ groups s)
    (hweights : ∀ group ∈ groups, ∀ item ∈ group, 0 ≤ item.weight)
    (hw : s.weight ≤ capacity) (hb : s.scaled ≤ bound) :
    Reachable θ capacity bound groups s := by
  revert hweights hw hb
  induction hs with
  | nil => intros; exact Reachable.nil
  | @snoc groups prev group item hprev hi ih =>
    intro hweights hw hb
    have hwitem : 0 ≤ item.weight := hweights group (by simp) item hi
    have hwprev : prev.weight ≤ capacity := by simp only [extend] at hw; linarith
    have hbprev : prev.scaled ≤ bound := by simp only [extend] at hb; omega
    apply Reachable.snoc (ih ?_ hwprev hbprev) hi hw hb
    intro g hg it hit
    exact hweights g (by simp [hg]) it hit

/-- A uniform per-option score bound gives the advertised linear total-score bound. -/
theorem selection_score_bound {θ : ℚ} {perGroup : ℕ}
    {groups : List (List Item)} {s : State} (hs : Selection θ groups s)
    (hb : ∀ group ∈ groups, ∀ item ∈ group, scaledProfit θ item ≤ perGroup) :
    s.scaled ≤ groups.length * perGroup := by
  revert hb
  induction hs with
  | nil => intro _; simp [initial]
  | @snoc groups prev group item hprev hi ih =>
    intro hb
    have hi' := hb group (by simp) item hi
    have hp : prev.scaled ≤ groups.length * perGroup := by
      apply ih
      intro g hg it hit
      exact hb g (by simp [hg]) it hit
    simp only [extend, List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    omega

/-- Exact scaled-profit optimality for all feasible selections, once the uniform
per-option bound is provided. There is no prefix-feasibility premise here. -/
theorem solve_optimal_all_selections {θ capacity : ℚ} {perGroup : ℕ}
    {groups : List (List Item)} {s t : State}
    (hs : solve θ capacity (groups.length * perGroup) groups = some s)
    (ht : Selection θ groups t)
    (hweights : ∀ group ∈ groups, ∀ item ∈ group, 0 ≤ item.weight)
    (hbound : ∀ group ∈ groups, ∀ item ∈ group, scaledProfit θ item ≤ perGroup)
    (hw : t.weight ≤ capacity) : t.scaled ≤ s.scaled := by
  exact solve_optimal hs (selection_reachable ht hweights hw (selection_score_bound ht hbound))

/-- Local floor bounds, including the important nonnegative-profit premise. -/
theorem scaledProfit_bounds {θ : ℚ} {item : Item} (hθ : 0 < θ)
    (hp : 0 ≤ item.profit) :
    θ * (scaledProfit θ item : ℚ) ≤ item.profit ∧
      item.profit < θ * (scaledProfit θ item + 1 : ℚ) := by
  have hnon : 0 ≤ item.profit / θ := div_nonneg hp hθ.le
  have hlo := Nat.floor_le hnon
  have hhi := Nat.lt_floor_add_one (item.profit / θ)
  unfold scaledProfit
  constructor
  · have := (le_div_iff₀ hθ).mp hlo
    nlinarith
  · have := (div_lt_iff₀ hθ).mp hhi
    nlinarith

/-- A computable uniform bound for the scaled score of every retained option. -/
theorem scaledProfit_le_ceiling {θ maxProfit : ℚ} {item : Item}
    (hθ : 0 < θ) (hp : 0 ≤ item.profit) (hmax : item.profit ≤ maxProfit) :
    scaledProfit θ item ≤ ⌈maxProfit / θ⌉₊ := by
  have hf : ((scaledProfit θ item : ℕ) : ℚ) ≤ item.profit / θ :=
    Nat.floor_le (div_nonneg hp hθ.le)
  have hd := div_le_div_of_nonneg_right hmax hθ.le
  have hc := Nat.le_ceil (maxProfit / θ)
  have h : ((scaledProfit θ item : ℕ) : ℚ) ≤ (⌈maxProfit / θ⌉₊ : ℕ) :=
    hf.trans (hd.trans hc)
  exact_mod_cast h

/-- The score bound is n·ceil(n/δ), hence quadratic in n and inverse accuracy. -/
theorem scaling_ceiling_identity {δ maxProfit : ℚ} {n : ℕ}
    (hδ : 0 < δ) (hm : 0 < maxProfit) (hn : 0 < n) :
    ⌈maxProfit / (δ * maxProfit / n)⌉₊ = ⌈(n : ℚ) / δ⌉₊ := by
  congr 1
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

/-- Reconstruction has one coordinate per group, and original profit lies between
its scaled score and that score plus one rounding unit per group. -/
theorem reachable_profit_bounds {θ capacity : ℚ} {bound : ℕ}
    {groups : List (List Item)} {s : State} (hθ : 0 < θ)
    (hs : Reachable θ capacity bound groups s)
    (hprofits : ∀ group ∈ groups, ∀ item ∈ group, 0 ≤ item.profit) :
    s.choices.length = groups.length ∧
    θ * (s.scaled : ℚ) ≤ s.profit ∧
    s.profit ≤ θ * (s.scaled : ℚ) + groups.length * θ := by
  revert hprofits
  induction hs with
  | nil => intro _; simp [initial]
  | @snoc groups prev group item hprev hi hw hb ih =>
    intro hprofits
    have hpr : ∀ g ∈ groups, ∀ it ∈ g, 0 ≤ it.profit := by
      intro g hg it hit
      exact hprofits g (by simp [hg]) it hit
    obtain ⟨hlen, hlo, hhi⟩ := ih hpr
    have hp : 0 ≤ item.profit := hprofits group (by simp) item hi
    obtain ⟨hlo', hhi'⟩ := scaledProfit_bounds hθ hp
    simp only [extend, List.length_append, List.length_singleton, Nat.cast_add,
      Nat.cast_one]
    refine ⟨by omega, ?_, ?_⟩ <;> nlinarith

/-- Certified additive approximation for the actual executable DP. The comparison
candidate is explicit and all its prefixes must fit the supplied score bound. -/
theorem solve_additive_approximation {θ capacity : ℚ} {bound : ℕ}
    {groups : List (List Item)} {s t : State} (hθ : 0 < θ)
    (hs : solve θ capacity bound groups = some s)
    (ht : Reachable θ capacity bound groups t)
    (hprofits : ∀ group ∈ groups, ∀ item ∈ group, 0 ≤ item.profit) :
    t.profit - groups.length * θ ≤ s.profit := by
  obtain ⟨_, hslo, _⟩ := reachable_profit_bounds hθ (solve_sound hs) hprofits
  obtain ⟨_, _, hthi⟩ := reachable_profit_bounds hθ ht hprofits
  have hn : (t.scaled : ℚ) ≤ s.scaled := by exact_mod_cast solve_optimal hs ht
  have := mul_le_mul_of_nonneg_left hn hθ.le
  linarith

/-- Certified relative approximation for the executable DP, with scale and
individual-option feasibility summarized by their exact arithmetic consequences. -/
theorem solve_relative_approximation {θ capacity δ maxProfit : ℚ} {bound : ℕ}
    {groups : List (List Item)} {s t : State} (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (hs : solve θ capacity bound groups = some s)
    (ht : Reachable θ capacity bound groups t)
    (hprofits : ∀ group ∈ groups, ∀ item ∈ group, 0 ≤ item.profit)
    (hscale : (groups.length : ℚ) * θ = δ * maxProfit)
    (hmax : maxProfit ≤ t.profit) : (1 - δ) * t.profit ≤ s.profit := by
  have h := solve_additive_approximation hθ hs ht hprofits
  have := mul_le_mul_of_nonneg_left hmax hδ
  nlinarith

/-- Full profit-scaling guarantee against every feasible unpruned selection of
profit at least maxProfit. All implementation bounds are instantiated explicitly. -/
theorem solve_relative_all_selections {δ maxProfit capacity : ℚ}
    {groups : List (List Item)} {s t : State}
    (hδ : 0 < δ) (hm : 0 < maxProfit) (hn : 0 < groups.length)
    (hs : solve (δ * maxProfit / groups.length) capacity
      (groups.length * ⌈(groups.length : ℚ) / δ⌉₊) groups = some s)
    (ht : Selection (δ * maxProfit / groups.length) groups t)
    (hweights : ∀ group ∈ groups, ∀ item ∈ group, 0 ≤ item.weight)
    (hprofits : ∀ group ∈ groups, ∀ item ∈ group, 0 ≤ item.profit ∧ item.profit ≤ maxProfit)
    (hw : t.weight ≤ capacity) (hmax : maxProfit ≤ t.profit) :
    (1 - δ) * t.profit ≤ s.profit := by
  let θ := δ * maxProfit / (groups.length : ℚ)
  have hn' : (0 : ℚ) < groups.length := by exact_mod_cast hn
  have hθ : 0 < θ := div_pos (mul_pos hδ hm) hn'
  have hb : ∀ group ∈ groups, ∀ item ∈ group, scaledProfit θ item ≤
      ⌈(groups.length : ℚ) / δ⌉₊ := by
    intro g hg it hi
    have hh := scaledProfit_le_ceiling hθ (hprofits g hg it hi).1 (hprofits g hg it hi).2
    dsimp [θ] at hh
    rwa [scaling_ceiling_identity hδ hm hn] at hh
  have hr := selection_reachable ht hweights hw (selection_score_bound ht hb)
  apply solve_relative_approximation (maxProfit := maxProfit) hθ hδ.le hs hr
  · intro g hg it hi; exact (hprofits g hg it hi).1
  · dsimp [θ]
    field_simp
  · exact hmax

/-- A profitable feasible comparison and an individually-feasible maximum-profit
option suffice to make the implemented DP pass a target with multiplicative slack. -/
theorem solve_passes_target {δ maxProfit capacity ρ : ℚ}
    {groups : List (List Item)} {comparison maximum : State}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hρ : 0 ≤ ρ)
    (hm : 0 < maxProfit) (hn : 0 < groups.length)
    (hweights : ∀ group ∈ groups, ∀ item ∈ group, 0 ≤ item.weight)
    (hprofits : ∀ group ∈ groups, ∀ item ∈ group, 0 ≤ item.profit ∧ item.profit ≤ maxProfit)
    (hc : Selection (δ * maxProfit / groups.length) groups comparison)
    (hcw : comparison.weight ≤ capacity)
    (hcp : (1 + 2 * δ) * ρ ≤ comparison.profit)
    (hmx : Selection (δ * maxProfit / groups.length) groups maximum)
    (hmw : maximum.weight ≤ capacity) (hmp : maxProfit ≤ maximum.profit) :
    ∃ s, solve (δ * maxProfit / groups.length) capacity
      (groups.length * ⌈(groups.length : ℚ) / δ⌉₊) groups = some s ∧ ρ ≤ s.profit := by
  have hex : ∃ t, Selection (δ * maxProfit / groups.length) groups t ∧
      t.weight ≤ capacity ∧ maxProfit ≤ t.profit ∧ (1 + 2 * δ) * ρ ≤ t.profit := by
    by_cases hh : maxProfit ≤ comparison.profit
    · exact ⟨comparison, hc, hcw, hh, hcp⟩
    · have hh' : comparison.profit ≤ maxProfit := by linarith
      exact ⟨maximum, hmx, hmw, hmp, hcp.trans (hh'.trans hmp)⟩
  obtain ⟨t, ht, htw, htm, htp⟩ := hex
  have hθ : 0 < δ * maxProfit / (groups.length : ℚ) := by positivity
  have hb : ∀ group ∈ groups, ∀ item ∈ group,
      scaledProfit (δ * maxProfit / groups.length) item ≤ ⌈(groups.length : ℚ) / δ⌉₊ := by
    intro g hg it hi
    have hh := scaledProfit_le_ceiling hθ (hprofits g hg it hi).1 (hprofits g hg it hi).2
    rwa [scaling_ceiling_identity hδ hm hn] at hh
  obtain ⟨s, hs⟩ := solve_exists (selection_reachable ht hweights htw (selection_score_bound ht hb))
  have hrel := solve_relative_all_selections hδ hm hn hs ht hweights hprofits htw htm
  refine ⟨s, hs, ?_⟩
  have hδone : 0 ≤ 1 - δ := by linarith
  have hh := mul_le_mul_of_nonneg_left htp hδone
  have hslack : 0 ≤ δ * (1 - 2 * δ) * ρ := by
    have : 0 ≤ 1 - 2 * δ := by linarith
    positivity
  nlinarith

/-- The additive loss bound underlying multiple-choice profit scaling.
`score` is supplied by an optimizer; its optimality is an explicit hypothesis. -/
theorem additive_rounding_loss {n : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    (original returned : Fin n → ℝ) (scoreOriginal scoreReturned : Fin n → ℕ)
    (hupper : ∀ i, original i ≤ θ * (scoreOriginal i + 1 : ℝ))
    (hlower : ∀ i, θ * (scoreReturned i : ℝ) ≤ returned i)
    (hscore : (∑ i, scoreOriginal i) ≤ ∑ i, scoreReturned i) :
    (∑ i, original i) - n * θ ≤ ∑ i, returned i := by
  have h₁ := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hupper i)
  have h₂ := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlower i)
  have hs : (∑ i, (scoreOriginal i : ℝ)) ≤ ∑ i, (scoreReturned i : ℝ) := by
    exact_mod_cast hscore
  have hm := mul_le_mul_of_nonneg_left hs hθ
  simp only [mul_add, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h₁ h₂
  nlinarith

/-- The additive loss becomes relative when the largest option is individually feasible. -/
theorem multiplicative_rounding_loss {n : ℕ} {θ δ maxProfit optimum returned : ℝ}
    (hδ : 0 ≤ δ) (hmax : maxProfit ≤ optimum)
    (hscale : (n : ℝ) * θ = δ * maxProfit)
    (hloss : optimum - n * θ ≤ returned) :
    (1 - δ) * optimum ≤ returned := by
  have := mul_le_mul_of_nonneg_left hmax hδ
  nlinarith

end BalancedAssortments.Knapsack
