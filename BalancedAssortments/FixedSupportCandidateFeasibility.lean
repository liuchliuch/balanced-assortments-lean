import BalancedAssortments.FixedSupportAlgorithmOrder
import BalancedAssortments.FixedSupportKnapsack
import BalancedAssortments.ContinuousKnapsackPrefix

namespace BalancedAssortments.FixedSupportAlgorithm
open scoped BigOperators

/-- Recover a coordinate after an ordered allocation. -/
def recover {n : ℕ} (order : List (Fin n)) (y : List ℚ) (i : Fin n) : ℚ :=
  y[order.idxOf i]?.getD 0

theorem recover_map {n : ℕ} (order : List (Fin n)) (y : List ℚ)
    (ho : order.Nodup) (hy : y.length = order.length) :
    order.map (recover order y) = y := by
  apply List.ext_getElem
  · simp [hy]
  · intro k hk hk'
    have hko : k < order.length := by simpa using hk
    simp only [List.getElem_map, recover, List.idxOf_getElem ho k hko]
    simp [hk']

theorem sum_order {n : ℕ} (order : List (Fin n)) (ho : List.Perm order (List.finRange n))
    (f : Fin n → ℚ) : (order.map f).sum = ∑ i, f i := by
  rw [(ho.map f).sum_eq]
  simp [← List.ofFn_eq_map, List.sum_ofFn]

theorem recover_sum {n : ℕ} (order : List (Fin n)) (y : List ℚ)
    (ho : List.Perm order (List.finRange n)) (hy : y.length = order.length) :
    (∑ i, recover order y i) = y.sum := by
  rw [← sum_order order ho, recover_map order y (ho.nodup_iff.mpr (List.nodup_finRange n)) hy]

private theorem profit_map {n : ℕ} (order : List (Fin n))
    (f : Fin n → ContinuousKnapsack.Item) (g : Fin n → ℚ) :
    ContinuousKnapsack.profit (order.map f) (order.map g) =
      (order.map (fun i => (f i).score*g i)).sum := by
  induction order with
  | nil => rfl
  | cons i order ih => simpa only [ContinuousKnapsack.profit, List.map_cons,
      List.zipWith_cons_cons, List.sum_cons] using congrArg ((f i).score*g i + ·) ih

theorem recover_profit {n : ℕ} (order : List (Fin n)) (y : List ℚ)
    (ho : List.Perm order (List.finRange n)) (hy : y.length = order.length)
    (f : Fin n → ContinuousKnapsack.Item) :
    ContinuousKnapsack.profit (order.map f) y = ∑ i, (f i).score*recover order y i := by
  have hh := recover_map order y (ho.nodup_iff.mpr (List.nodup_finRange n)) hy
  calc ContinuousKnapsack.profit (order.map f) y =
      ContinuousKnapsack.profit (order.map f) (order.map (recover order y)) := by rw [hh]
    _ = _ := (profit_map order f _).trans (sum_order order ho _)

theorem scaleUpper_le_cap {n : ℕ} (v : Fin n → ℚ) (K : ℚ) (i : Fin n) :
    scaleUpper v K ≤ v i :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

theorem scaleUpper_le_rank {n : ℕ} (v : Fin n → ℚ) (K : ℚ) :
    scaleUpper v K ≤ K/inverseSum v := Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem rationalBudget_nonneg {n : ℕ} (v : Fin n → ℚ) (hv : ∀ i, 0 < v i)
    {K t : ℚ} (hK : 0 ≤ K) (ht : t ≤ scaleUpper v K) : 0 ≤ rationalBudget v K t := by
  have hi : 0 ≤ inverseSum v := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hv i)).le)
  have hh := ht.trans (scaleUpper_le_rank v K)
  by_cases hz : inverseSum v = 0
  · simpa [rationalBudget, hz] using hK
  · have hp : 0 < inverseSum v := lt_of_le_of_ne hi (Ne.symm hz)
    have he := (le_div_iff₀ hp).1 hh
    exact sub_nonneg.mpr he

theorem rationalCap_nonneg {n : ℕ} (v : Fin n → ℚ) (hv : ∀ i, 0 < v i)
    {α K t : ℚ} (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 ≤ t)
    (htu : t ≤ scaleUpper v K) (i : Fin n) : 0 ≤ rationalCap v α t i := by
  apply sub_nonneg.mpr
  apply le_min
  · exact (div_le_one (hv i)).2 (htu.trans (scaleUpper_le_cap v K i))
  · apply div_le_div_of_nonneg_left ht (mul_pos hα (hv i))
    nlinarith [hv i]

def candidateIncrements {n : ℕ} (r v : Fin n → ℚ) (α K ρ t : ℚ) : Fin n → ℚ :=
  recover (scoreOrder r v ρ)
    (ContinuousKnapsack.solve (rationalBudget v K t) (knapsackItems r v α ρ t)).1

/-- Coordinate recovery preserves every continuous-knapsack constraint. -/
theorem candidateIncrements_feasible {n : ℕ} (r v : Fin n → ℚ) (hv : ∀ i, 0 < v i)
    {α K ρ t : ℚ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (ht : 0 ≤ t) (htu : t ≤ scaleUpper v K) :
    (∀ i, 0 ≤ candidateIncrements r v α K ρ t i ∧
      candidateIncrements r v α K ρ t i ≤ rationalCap v α t i) ∧
      (∑ i, candidateIncrements r v α K ρ t i) ≤ rationalBudget v K t := by
  let order := scoreOrder r v ρ
  let items := knapsackItems r v α ρ t
  let y := (ContinuousKnapsack.solve (rationalBudget v K t) items).1
  have hcaps : ∀ item ∈ items, 0 ≤ item.cap := by
    intro item hi
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hi
    exact rationalCap_nonneg v hv hα hα1 ht htu i
  have hy := ContinuousKnapsack.solve_feasible (rationalBudget v K t) items
    (rationalBudget_nonneg v hv hK htu) hcaps
  have hlen : y.length = order.length := by simp [y, items, knapsackItems, order]
  constructor
  · intro i
    have hm : i ∈ order := mem_scoreOrder r v ρ i
    have hidx := List.idxOf_lt_length_iff.mpr hm
    have hli : order.idxOf i < items.length := by simpa [items, knapsackItems, order] using hidx
    have hly : order.idxOf i < y.length := by omega
    have hh := hy.1.get hli hly
    have hlab : order[order.idxOf i] = i := List.getElem_idxOf hidx
    change 0 ≤ y[order.idxOf i]?.getD 0 ∧ y[order.idxOf i]?.getD 0 ≤ rationalCap v α t i
    change 0 ≤ y[order.idxOf i]'hly ∧ y[order.idxOf i]'hly ≤ (items[order.idxOf i]'hli).cap at hh
    have hitem : (items[order.idxOf i]'hli).cap = rationalCap v α t i := by
      change ((order.map (fun j => (⟨score r v ρ j, rationalCap v α t j⟩ : ContinuousKnapsack.Item)))[order.idxOf i]).cap = _
      simp only [List.getElem_map, hlab]
    rw [hitem] at hh
    simpa only [List.getElem?_eq_getElem hly, Option.getD_some] using hh
  · change (∑ i, recover order y i) ≤ rationalBudget v K t
    rw [recover_sum order y (scoreOrder_perm r v ρ) hlen]
    exact hy.2

/-- Actual executable candidate reconstruction is feasible for the real source
closed prescribed-support polytope, not merely for a surrogate model. -/
theorem candidateVector_feasible {n : ℕ} (r v : Fin n → ℚ) (hv : ∀ i, 0 < v i)
    {α K ρ t : ℚ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (ht : 0 ≤ t) (htu : t ≤ scaleUpper v K) :
    FixedSupportReal.Feasible (fun i => (v i : ℝ)) (α : ℝ) (K : ℝ)
      (fun i => (candidateVector r v α K (ρ,t) i : ℝ)) := by
  have hy := candidateIncrements_feasible r v hv hα hα1 hK ht htu (ρ := ρ)
  have hvR : ∀ i, (0 : ℝ) < (v i : ℝ) := fun i => by exact_mod_cast hv i
  have hαR : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hs : FixedSupportKnapsack.ScaleFeasible (fun i => (v i : ℝ)) (α : ℝ) (K : ℝ) (t : ℝ)
      (fun i => (candidateIncrements r v α K ρ t i : ℝ)) := by
    refine ⟨by exact_mod_cast ht, ?_, ?_⟩
    · intro i
      have hh := hy.1 i
      unfold FixedSupportKnapsack.cap
      have he : ((rationalCap v α t i : ℚ) : ℝ) =
          min 1 ((t : ℝ)/((α : ℝ)*(v i : ℝ))) - (t : ℝ)/(v i : ℝ) := by
        simp [rationalCap]
      constructor
      · dsimp only; exact_mod_cast hh.1
      · rw [← he]
        dsimp only
        exact_mod_cast hh.2
    · have hh := hy.2
      unfold FixedSupportKnapsack.budget
      unfold rationalBudget inverseSum at hh
      dsimp only
      exact_mod_cast hh
  have hf := FixedSupportKnapsack.scale_to_fixed (fun i => (v i : ℝ)) hvR hαR hs
  have he : FixedSupportKnapsack.reconstruct (fun i => (v i : ℝ)) (t : ℝ)
      (fun i => (candidateIncrements r v α K ρ t i : ℝ)) =
      (fun i => (candidateVector r v α K (ρ,t) i : ℝ)) := by
    funext i
    simp [FixedSupportKnapsack.reconstruct, candidateVector, candidateIncrements, recover]
  rwa [he] at hf


/-- The recovered labeled allocation maximizes the exact transformed score
among all increments satisfying the same cap and rank budget. -/
theorem candidateIncrements_optimal {n : ℕ} (r v : Fin n → ℚ) (hv : ∀ i, 0 < v i)
    {α K ρ t : ℚ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (ht : 0 ≤ t) (htu : t ≤ scaleUpper v K) (z : Fin n → ℚ)
    (hzc : ∀ i, 0 ≤ z i ∧ z i ≤ rationalCap v α t i)
    (hzb : (∑ i, z i) ≤ rationalBudget v K t) :
    (∑ i, score r v ρ i*z i) ≤ ∑ i, score r v ρ i*candidateIncrements r v α K ρ t i := by
  let order := scoreOrder r v ρ
  let f : Fin n → ContinuousKnapsack.Item := fun i => ⟨score r v ρ i, rationalCap v α t i⟩
  let items := knapsackItems r v α ρ t
  let y := (ContinuousKnapsack.solve (rationalBudget v K t) items).1
  have hitems : items = order.map f := rfl
  have hcaps : ∀ item ∈ items, 0 ≤ item.cap := by
    intro item hi
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hi
    exact rationalCap_nonneg v hv hα hα1 ht htu i
  have hforall (o : List (Fin n)) : List.Forall₂
      (fun item q => 0 ≤ q ∧ q ≤ item.cap) (o.map f) (o.map z) := by
    induction o with
    | nil => exact List.Forall₂.nil
    | cons i o ih => exact List.Forall₂.cons (hzc i) ih
  have hcomp : ContinuousKnapsack.Feasible (rationalBudget v K t) items (order.map z) := by
    refine ⟨hforall order, ?_⟩
    rw [sum_order order (scoreOrder_perm r v ρ) z]
    exact hzb
  have hh := (ContinuousKnapsack.solve_optimal (rationalBudget v K t) items
    (rationalBudget_nonneg v hv hK htu) hcaps (knapsackItems_sorted r v α ρ t)).2 (order.map z) hcomp
  have hlen : y.length = order.length := by simp [y, items, knapsackItems, order]
  change ContinuousKnapsack.profit (order.map f) (order.map z) ≤
    ContinuousKnapsack.profit (order.map f) y at hh
  rw [profit_map, sum_order order (scoreOrder_perm r v ρ),
    recover_profit order y (scoreOrder_perm r v ρ) hlen f] at hh
  exact hh

/-- Exact relation between the candidate's labeled increments and the source
linearized objective at the sampled revenue threshold. -/
theorem candidate_transformed_profit {n : ℕ} (r v : Fin n → ℚ) (α K ρ t : ℚ) :
    (∑ i, (r i-ρ)*candidateVector r v α K (ρ,t) i) =
      t*(∑ i, (r i-ρ)) + ∑ i, score r v ρ i*candidateIncrements r v α K ρ t i := by
  simp only [candidateVector, candidateIncrements, recover, score, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; ring
  · apply Finset.sum_congr rfl; intro i _; ring

end BalancedAssortments.FixedSupportAlgorithm
