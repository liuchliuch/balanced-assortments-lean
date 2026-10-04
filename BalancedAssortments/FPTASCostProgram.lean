import BalancedAssortments.FPTASCostAutoCandidate
import BalancedAssortments.FPTASCostSingletons
import BalancedAssortments.FPTASCostInputSeeds
import BalancedAssortments.FPTASCostGridFuel

/-! The executable binary sales-vector algorithm. It consumes raw binary
fractions, constructs all seeds, both grids, all option families, scaling
parameters and DP quotas itself, and returns the best rational sales vector.
The cost field is ghost instrumentation; no decoded rational/Nat arithmetic is
used to decide the executable result. -/
namespace BalancedAssortments.FPTASCostProgram
open KnapsackCostRational FPTASCostSeeds FPTASCostGrid FPTASCostLoops
open FPTASCostCandidate FPTASCostSingletons FPTASCostCutoff

/-- Binary cardinality fraction from an already counted product list. -/
def countAsFraction (bits : List Bool) : Fraction := ⟨bits,[true]⟩

/-- Full binary FPTAS sales program. All grids use charged unary-token fuel,
all rational arithmetic uses unreduced bit-list primitives, and every list scan
and candidate callback is charged. -/
def runSalesBits (alpha epsilon capacity : Fraction) (products : List Product) : List Fraction × ℕ :=
  let prepared := prepareSeeds alpha epsilon products
  let δ := prepared.1.1
  let seeds := prepared.1.2
  let counted := countBits products
  let count := countAsFraction counted.1
  let cutoff := cutoffFuel counted.1 δ
  let scales := rawGrid seeds.scaleBase δ seeds.ratio seeds.scaleCap
  let revenues := rawGrid seeds.revenueBase δ seeds.ratio seeds.revenueCap
  let candidates := cross
    (fun τ ρ => autoCandidate δ count capacity τ seeds.ratio alpha ρ cutoff.1 products)
    scales.1 revenues.1
  let values := products.map Prod.snd
  let prices := products.map Prod.fst
  let singleton := singletons values
  let empty := zeroes values
  let vectors := candidates.1.map KnapsackCostState.State.choices
  let result := improveAll prices empty.1 (singleton.1++vectors)
  (result.1,prepared.2+counted.2+cutoff.2+scales.2+revenues.2+candidates.2+
    singleton.2+empty.2+result.2+2*products.length+candidates.1.length+singleton.1.length+20)

lemma cross_length {α β γ : Type*} (f : α → β → Option γ × ℕ) (xs : List α) (ys : List β) :
    (cross f xs ys).1.length ≤ xs.length*ys.length := by
  rw [cross_eq]
  exact FPTASCost.flatMap_length_bound xs _ ys.length (fun _ _ => List.length_filterMap_le _ _)

lemma cross_member {α β γ : Type*} {f : α → β → Option γ × ℕ} {xs : List α} {ys : List β} {z : γ}
    (hz : z ∈ (cross f xs ys).1) : ∃ x ∈ xs, ∃ y ∈ ys, (f x y).1 = some z := by
  rw [cross_eq] at hz
  obtain ⟨x,hx,hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨y,hy,he⟩ := List.mem_filterMap.mp hz
  exact ⟨x,hx,y,hy,he⟩

lemma collect_refinement {α β γ δ : Type*} (f : α → Option β × ℕ)
    (input : α → γ) (output : β → δ) (g : γ → Option δ) (xs : List α)
    (hf : ∀ x ∈ xs, (f x).1.map output = g (input x)) :
    (collect f xs).1.map output = (xs.map input).filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [collect,List.map_cons,List.filterMap_cons]
    rw [← hh]
    cases he : (f x).1 <;> simp [he,ht]

lemma cross_refinement {α β γ α' β' γ' : Type*} (f : α → β → Option γ × ℕ)
    (dx : α → α') (dy : β → β') (dz : γ → γ') (g : α' → β' → Option γ')
    (xs : List α) (ys : List β)
    (hf : ∀ x ∈ xs, ∀ y ∈ ys, (f x y).1.map dz = g (dx x) (dy y)) :
    (cross f xs ys).1.map dz = (xs.map dx).flatMap (fun x => (ys.map dy).filterMap (g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh := collect_refinement (f x) dy dz (g (dx x)) ys (hf x (by simp))
    have ht := ih (fun x hx y hy => hf x (by simp [hx]) y hy)
    simp only [cross,List.map_append,List.map_cons,List.flatMap_cons]
    rw [hh,ht]

end BalancedAssortments.FPTASCostProgram
