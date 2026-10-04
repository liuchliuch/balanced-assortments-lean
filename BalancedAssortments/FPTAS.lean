import BalancedAssortments.GridBounds
import BalancedAssortments.Knapsack
import BalancedAssortments.DecompositionAlgorithm

/-! Executable rational outer grid/knapsack algorithm and policy output.
The feasibility validation is exact and polynomial-size; the end-to-end
approximation and bit-operation proof are separate obligations. -/
namespace BalancedAssortments.FPTAS
open Finset

structure Input (n : ℕ) where
  r : Fin (n + 1) → ℚ
  v : Fin (n + 1) → ℚ
  α : ℚ
  K : ℕ

def Valid {n : ℕ} (d : Input n) : Prop :=
  (∀ i, 0 < d.r i ∧ 0 < d.v i) ∧ 0 < d.α ∧ d.α ≤ 1 ∧ 1 ≤ d.K ∧ d.K ≤ n+1

def revenue {n : ℕ} (d : Input n) (w : Fin (n+1) → ℚ) : ℚ :=
  (∑ i, d.r i * w i) / (1 + ∑ i, w i)

def Feasible {n : ℕ} (d : Input n) (w : Fin (n+1) → ℚ) : Prop :=
  (∀ i, 0 ≤ w i ∧ w i ≤ d.v i) ∧ (∑ i, w i / d.v i) ≤ d.K ∧
    ∀ i, w i = 0 ∨ ∀ j, d.α * w j ≤ w i

instance {n : ℕ} (d : Input n) (w : Fin (n+1) → ℚ) : Decidable (Feasible d w) := by
  unfold Feasible; infer_instance

def singleton {n : ℕ} (d : Input n) (j : Fin (n+1)) : Fin (n+1) → ℚ :=
  fun i => if i = j then d.v j else 0

def maxList (xs : List ℚ) : ℚ := xs.foldl max 0

def vmin {n : ℕ} (d : Input n) : ℚ := ((List.finRange (n+1)).map d.v).foldl min (d.v 0)
def vmax {n : ℕ} (d : Input n) : ℚ := maxList ((List.finRange (n+1)).map d.v)
def rmax {n : ℕ} (d : Input n) : ℚ := maxList ((List.finRange (n+1)).map d.r)
def singletonValue {n : ℕ} (d : Input n) : ℚ :=
  maxList ((List.finRange (n+1)).map fun i => revenue d (singleton d i))

def scales {n : ℕ} (d : Input n) (δ : ℚ) : List ℚ :=
  let a := d.α * vmin d / (n+1)
  let cap := d.α * vmax d
  Grids.geometricGrid a δ cap (GridBounds.gridHorizon a δ cap)

def revenues {n : ℕ} (d : Input n) (δ : ℚ) : List ℚ :=
  Grids.geometricGrid (singletonValue d) δ (rmax d)
    (GridBounds.gridHorizon (singletonValue d) δ (rmax d))

def group {n : ℕ} (d : Input n) (δ τ ρ : ℚ) (i : Fin (n+1)) : List Knapsack.Item :=
  ⟨0, 0, 0⟩ :: (((Grids.geometricGrid τ δ (min (d.v i) (τ/d.α))
    (GridBounds.gridHorizon τ δ (min (d.v i) (τ/d.α)))).filter
      fun u => 0 < (d.r i - ρ) * u).map
        fun u => ⟨u, u/d.v i, (d.r i-ρ)*u⟩)

def groups {n : ℕ} (d : Input n) (δ τ ρ : ℚ) : List (List Knapsack.Item) :=
  (List.finRange (n+1)).map (group d δ τ ρ)

def stateVector {n : ℕ} (s : Knapsack.State) : Fin (n+1) → ℚ :=
  fun i => s.choices[i.val]?.getD 0

def candidateAt {n : ℕ} (d : Input n) (δ τ ρ : ℚ) : Option (Fin (n+1) → ℚ) :=
  let gs := groups d δ τ ρ
  let pmax := maxList ((gs.flatten).map Knapsack.Item.profit)
  if pmax ≤ 0 then none else
    let θ := δ * pmax / (n+1)
    let bound := (n+1) * ⌈(n+1 : ℚ) / δ⌉₊
    match Knapsack.solve θ d.K bound gs with
    | none => none
    | some s => if ρ ≤ s.profit then some (stateVector s) else none

def rawCandidates {n : ℕ} (d : Input n) (ε : ℚ) : List (Fin (n+1) → ℚ) :=
  let δ := ε / 10
  ((List.finRange (n+1)).map (singleton d)) ++
    ((scales d δ).flatMap fun τ => (revenues d δ).filterMap fun ρ => candidateAt d δ τ ρ)

def admissibleCandidates {n : ℕ} (d : Input n) (ε : ℚ) : List (Fin (n+1) → ℚ) :=
  (rawCandidates d ε).filter fun w => Feasible d w

def runSales {n : ℕ} (d : Input n) (ε : ℚ) : Fin (n+1) → ℚ :=
  ((admissibleCandidates d ε).argmax (revenue d)).getD (fun _ => 0)

/-- Final rational reverse tilt. The output contains at most n+2 atoms for n+1 products. -/
def runPolicy {n : ℕ} (d : Input n) (ε : ℚ) : List (Decomposition.Atom (n+1)) :=
  let w := runSales d ε
  (Decomposition.greedy d.K (fun i => w i / d.v i)).map fun a =>
    (a.1 * (1 + ∑ i ∈ a.2, d.v i) / (1 + ∑ i, w i), a.2)

theorem zero_feasible {n : ℕ} (d : Input n) (hv : ∀ i, 0 ≤ d.v i) :
    Feasible d (fun _ => 0) := by
  refine ⟨fun i => ⟨le_rfl, hv i⟩, ?_, fun _ => Or.inl rfl⟩
  simp

theorem runSales_feasible {n : ℕ} (d : Input n) (ε : ℚ)
    (hv : ∀ i, 0 ≤ d.v i) : Feasible d (runSales d ε) := by
  unfold runSales
  cases h : (admissibleCandidates d ε).argmax (revenue d) with
  | none => exact zero_feasible d hv
  | some w =>
    have hw := List.argmax_mem h
    exact (List.mem_filter.mp hw).2 |> of_decide_eq_true

theorem runSales_dominates {n : ℕ} (d : Input n) (ε : ℚ)
    {w : Fin (n+1) → ℚ} (hw : w ∈ rawCandidates d ε) (hf : Feasible d w) :
    revenue d w ≤ revenue d (runSales d ε) := by
  have hm : w ∈ admissibleCandidates d ε := by simp [admissibleCandidates, hw, hf]
  unfold runSales
  cases h : (admissibleCandidates d ε).argmax (revenue d) with
  | none =>
    have he := List.argmax_eq_none.mp h
    rw [he] at hm
    simp at hm
  | some u => exact List.le_of_mem_argmax hm h
end BalancedAssortments.FPTAS
