import BalancedAssortments.Knapsack
import BalancedAssortments.KnapsackCostRational

/-! Bit-represented states and an instrumented refinement of the actual DP extension.
All arithmetic uses explicit bit/list primitives. The initial scaled item profits
are inputs here; their division/floor preprocessing is a separate algorithm. -/
namespace BalancedAssortments.KnapsackCostState
open ComplexityTimeBinary KnapsackCostRational

structure Item where
  value : Fraction
  weight : Fraction
  profit : Fraction
  scaled : List Bool

structure State where
  weight : Fraction
  profit : Fraction
  scaled : List Bool
  choices : List Fraction

def Item.decode (i : Item) : Knapsack.Item :=
  ⟨i.value.decode, i.weight.decode, i.profit.decode⟩
def State.decode (s : State) : Knapsack.State :=
  ⟨s.weight.decode, s.profit.decode, value s.scaled, s.choices.map Fraction.decode⟩
def Item.Valid (i : Item) : Prop := i.value.Valid ∧ i.weight.Valid ∧ i.profit.Valid
def State.Valid (s : State) : Prop :=
  s.weight.Valid ∧ s.profit.Valid ∧ ∀ q ∈ s.choices, q.Valid

def Item.Width (i : Item) (b : ℕ) : Prop :=
  i.value.Width b ∧ i.weight.Width b ∧ i.profit.Width b ∧ i.scaled.length ≤ b

def State.Width (s : State) (b : ℕ) : Prop :=
  s.weight.Width b ∧ s.profit.Width b ∧ s.scaled.length ≤ b ∧
    ∀ q ∈ s.choices, q.Width b

def zero : Fraction := ⟨[], [true]⟩
def initial : State := ⟨zero, zero, [], []⟩

def extend (s : State) (i : Item) : State × ℕ :=
  let w := KnapsackCostRational.add s.weight i.weight
  let p := KnapsackCostRational.add s.profit i.profit
  let k := addCarry s.scaled i.scaled false
  (⟨w.1, p.1, k.1, s.choices ++ [i.value]⟩,
    w.2 + p.2 + k.2 + s.choices.length + 20)

theorem initial_valid : initial.Valid := by
  simp [State.Valid, initial, Fraction.Valid, zero, value]

theorem initial_width : initial.Width 1 := by
  simp [State.Width, initial, Fraction.Width, zero]

theorem initial_decode : initial.decode = Knapsack.initial := by
  simp [State.decode, initial, Fraction.decode, zero, value, Knapsack.initial]

theorem extend_valid {s : State} {i : Item} (hs : s.Valid) (hi : i.Valid) :
    (extend s i).1.Valid := by
  refine ⟨add_valid hs.1 hi.2.1, add_valid hs.2.1 hi.2.2, ?_⟩
  intro q hq
  simp only [extend, List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hs.2.2 q hq
  · exact hi.1

/-- Exact semantic refinement of the DP's rational extension. -/
theorem extend_decode {s : State} {i : Item} {θ : ℚ}
    (hs : s.Valid) (hi : i.Valid)
    (hscaled : value i.scaled = Knapsack.scaledProfit θ i.decode) :
    (extend s i).1.decode = Knapsack.extend θ s.decode i.decode := by
  simp only [extend, State.decode, Knapsack.extend, Item.decode, List.map_append,
    List.map_singleton, addCarry_value, Bool.toNat_false, Nat.add_zero]
  rw [add_decode hs.1 hi.2.1, add_decode hs.2.1 hi.2.2, hscaled]
  rfl

theorem Fraction.width_mono {q : Fraction} {a b : ℕ} (h : q.Width a) (hab : a ≤ b) :
    q.Width b := ⟨h.1.trans hab, h.2.trans hab⟩

theorem extend_width {s : State} {i : Item} {a b : ℕ}
    (hs : s.Width a) (hi : i.Width b) : (extend s i).1.Width (a + 2*b + 1) := by
  refine ⟨add_width hs.1 hi.2.1, add_width hs.2.1 hi.2.2.1, ?_, ?_⟩
  · simp only [extend, addCarry_length]
    have h₁ := hs.2.2.1; have h₂ := hi.2.2.2
    omega
  · intro q hq
    simp only [extend, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact Fraction.width_mono (hs.2.2.2 q hq) (by omega)
    · exact Fraction.width_mono hi.1 (by omega)

theorem extend_cost {s : State} {i : Item} {a b : ℕ}
    (hs : s.Width a) (hi : i.Width b) :
    (extend s i).2 ≤ 1024 * (a + b + 1)^2 + s.choices.length := by
  have hw := add_cost hs.1 hi.2.1
  have hp := add_cost hs.2.1 hi.2.2.1
  have hl : max s.scaled.length i.scaled.length ≤ a+b := by
    have h₁ := hs.2.2.1; have h₂ := hi.2.2.2
    omega
  simp only [extend, addCarry_cost]
  nlinarith

/-- An encoded path mirrors a path of ordinary multiple-choice transitions. -/
inductive Path : List Item → State → Prop
  | nil : Path [] initial
  | snoc {items : List Item} {s : State} {i : Item}
      (prior : Path items s) : Path (items ++ [i]) (extend s i).1

theorem path_length {items : List Item} {s : State} (hs : Path items s) :
    s.choices.length = items.length := by
  induction hs with
  | nil => rfl
  | snoc _ ih => simpa [extend] using ih

/-- Explicit linear bound for every numerator, denominator and score bit list
along any n-option DP path, including unreduced intermediate states. -/
theorem path_width {items : List Item} {s : State} {b : ℕ}
    (hs : Path items s) (hitems : ∀ i ∈ items, i.Width b) :
    s.Width (1 + items.length * (2*b + 1)) := by
  revert hitems
  induction hs with
  | nil => intro _; simpa using initial_width
  | @snoc items s i hp ih =>
    intro hi
    have hs' := ih (fun j hj => hi j (by simp [hj]))
    have h := extend_width hs' (hi i (by simp))
    convert h using 1 <;> simp [Nat.add_mul] <;> omega

/-- Summed actual bit-operation cost along a selected path. -/
def pathCost : State → List Item → ℕ
  | _, [] => 0
  | s, i :: is => (extend s i).2 + pathCost (extend s i).1 is

end BalancedAssortments.KnapsackCostState
