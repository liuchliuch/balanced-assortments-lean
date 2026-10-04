import BalancedAssortments.FixedSupportCandidateFeasibility

noncomputable section
namespace BalancedAssortments.FixedSupportAlgorithm
open scoped BigOperators

/-- Recover a coordinate after an ordered allocation. -/
def recoverReal {n : ℕ} (order : List (Fin n)) (y : List ℝ) (i : Fin n) : ℝ :=
  y[order.idxOf i]?.getD 0

theorem recoverReal_map {n : ℕ} (order : List (Fin n)) (y : List ℝ)
    (ho : order.Nodup) (hy : y.length = order.length) :
    order.map (recoverReal order y) = y := by
  apply List.ext_getElem
  · simp [hy]
  · intro k hk hk'
    have hko : k < order.length := by simpa using hk
    simp only [List.getElem_map, recoverReal, List.idxOf_getElem ho k hko]
    simp [hk']

theorem sum_order_real {n : ℕ} (order : List (Fin n)) (ho : List.Perm order (List.finRange n))
    (f : Fin n → ℝ) : (order.map f).sum = ∑ i, f i := by
  rw [(ho.map f).sum_eq]
  simp [← List.ofFn_eq_map, List.sum_ofFn]

theorem recoverReal_sum {n : ℕ} (order : List (Fin n)) (y : List ℝ)
    (ho : List.Perm order (List.finRange n)) (hy : y.length = order.length) :
    (∑ i, recoverReal order y i) = y.sum := by
  rw [← sum_order_real order ho, recoverReal_map order y (ho.nodup_iff.mpr (List.nodup_finRange n)) hy]

private theorem profit_map_real {n : ℕ} (order : List (Fin n))
    (f : Fin n → ContinuousKnapsackReal.Item) (g : Fin n → ℝ) :
    ContinuousKnapsackReal.profit (order.map f) (order.map g) =
      (order.map (fun i => (f i).score*g i)).sum := by
  induction order with
  | nil => rfl
  | cons i order ih => simpa only [ContinuousKnapsackReal.profit, List.map_cons,
      List.zipWith_cons_cons, List.sum_cons] using congrArg ((f i).score*g i + ·) ih

theorem recoverReal_profit {n : ℕ} (order : List (Fin n)) (y : List ℝ)
    (ho : List.Perm order (List.finRange n)) (hy : y.length = order.length)
    (f : Fin n → ContinuousKnapsackReal.Item) :
    ContinuousKnapsackReal.profit (order.map f) y = ∑ i, (f i).score*recoverReal order y i := by
  have hh := recoverReal_map order y (ho.nodup_iff.mpr (List.nodup_finRange n)) hy
  calc ContinuousKnapsackReal.profit (order.map f) y =
      ContinuousKnapsackReal.profit (order.map f) (order.map (recoverReal order y)) := by rw [hh]
    _ = _ := (profit_map_real order f _).trans (sum_order_real order ho _)

def realKnapsackItems {n : ℕ} (r v : Fin n → ℚ) (α q : ℚ) (t : ℝ) :
    List ContinuousKnapsackReal.Item :=
  (scoreOrder r v q).map fun i => ⟨(score r v q i : ℝ),
    FixedSupportKnapsack.cap (fun j => (v j : ℝ)) (α : ℝ) t i⟩

def realCandidateIncrements {n : ℕ} (r v : Fin n → ℚ) (α K q : ℚ) (t : ℝ) : Fin n → ℝ :=
  recoverReal (scoreOrder r v q)
    (ContinuousKnapsackReal.solve
      (FixedSupportKnapsack.budget (fun i => (v i : ℝ)) (K : ℝ) t)
      (realKnapsackItems r v α q t)).1

def realCandidateVector {n : ℕ} (r v : Fin n → ℚ) (α K q : ℚ) (t : ℝ) : Fin n → ℝ :=
  FixedSupportKnapsack.reconstruct (fun i => (v i : ℝ)) t (realCandidateIncrements r v α K q t)

theorem recover_cast {n : ℕ} (order : List (Fin n)) (y : List ℚ) (i : Fin n) :
    recoverReal order (y.map (fun (q : ℚ) => (q : ℝ))) i = (recover order y i : ℝ) := by
  unfold recoverReal recover
  cases h : y[order.idxOf i]? <;> simp [List.getElem?_map, h]

theorem realCandidateVector_cast {n : ℕ} (r v : Fin n → ℚ) (α K q t : ℚ) :
    realCandidateVector r v α K q (t : ℝ) = fun i => (candidateVector r v α K (q,t) i : ℝ) := by
  have hb : (rationalBudget v K t : ℝ) =
      FixedSupportKnapsack.budget (fun i => (v i : ℝ)) (K : ℝ) (t : ℝ) := by
    simp [rationalBudget, inverseSum, FixedSupportKnapsack.budget]
  have hc : (knapsackItems r v α q t).map ContinuousKnapsackReal.castItem =
      realKnapsackItems r v α q (t : ℝ) := by
    simp [knapsackItems, realKnapsackItems, ContinuousKnapsackReal.castItem,
      List.map_map, Function.comp_def, rationalCap, FixedSupportKnapsack.cap]
  have hs := ContinuousKnapsackReal.solve_cast (rationalBudget v K t) (knapsackItems r v α q t)
  rw [hb, hc] at hs
  have hy := congrArg Prod.fst hs
  dsimp only at hy
  funext i
  unfold realCandidateVector FixedSupportKnapsack.reconstruct realCandidateIncrements
  rw [hy, recover_cast]
  simp [candidateVector, recover]

/-- A compatible sampled score regime produces an allocation optimal for the
actual real target at every real scale, including irrational scales. -/
theorem realCandidateIncrements_optimal {n : ℕ} (r v : Fin n → ℚ) (α K q : ℚ)
    (ρ t : ℝ) (hq : ScoreCompatible r v ρ q) (z : Fin n → ℝ)
    (hz : FixedSupportKnapsack.ScaleFeasible (fun i => (v i : ℝ)) (α : ℝ) (K : ℝ) t z) :
    (∑ i, realScore r v ρ i*z i) ≤
      ∑ i, realScore r v ρ i*realCandidateIncrements r v α K q t i := by
  let order := scoreOrder r v q
  let cap := FixedSupportKnapsack.cap (fun i => (v i : ℝ)) (α : ℝ) t
  let B := FixedSupportKnapsack.budget (fun i => (v i : ℝ)) (K : ℝ) t
  let f : Fin n → ContinuousKnapsackReal.Item := fun i => ⟨realScore r v ρ i, cap i⟩
  let g : Fin n → ContinuousKnapsackReal.Item := fun i => ⟨(score r v q i : ℝ), cap i⟩
  have hB : 0 ≤ B := (Finset.sum_nonneg (fun i _ => (hz.2.1 i).1)).trans hz.2.2
  have hcaps : ∀ item ∈ order.map f, 0 ≤ item.cap := by
    intro item hi
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hi
    exact (hz.2.1 i).1.trans (hz.2.1 i).2
  have hsorted : (order.map f).Pairwise (fun i j => j.score ≤ i.score) := by
    simpa [f, List.pairwise_map] using scoreOrder_real_sorted r v hq
  have hpattern (o : List (Fin n)) : List.Forall₂
      (fun i j : ContinuousKnapsackReal.Item => i.cap = j.cap ∧ (0 < i.score ↔ 0 < j.score))
      (o.map f) (o.map g) := by
    induction o with
    | nil => exact List.Forall₂.nil
    | cons i o ih =>
      apply List.Forall₂.cons _ ih
      exact ⟨rfl, by simpa [f, g] using hq.1 i⟩
  have halloc := ContinuousKnapsackReal.solve_alloc_same_pattern B (order.map f) (order.map g) (hpattern order)
  have hforall (o : List (Fin n)) : List.Forall₂
      (fun item q => 0 ≤ q ∧ q ≤ item.cap) (o.map f) (o.map z) := by
    induction o with
    | nil => exact List.Forall₂.nil
    | cons i o ih => exact List.Forall₂.cons (hz.2.1 i) ih
  have hcomp : ContinuousKnapsackReal.Feasible B (order.map f) (order.map z) := by
    refine ⟨hforall order, ?_⟩
    rw [sum_order_real order (scoreOrder_perm r v q) z]
    exact hz.2.2
  have hh := (ContinuousKnapsackReal.solve_optimal B (order.map f) hB hcaps hsorted).2 (order.map z) hcomp
  rw [halloc] at hh
  let y := (ContinuousKnapsackReal.solve B (order.map g)).1
  have hlen : y.length = order.length := by simp [y]
  change ContinuousKnapsackReal.profit (order.map f) (order.map z) ≤
    ContinuousKnapsackReal.profit (order.map f) y at hh
  rw [profit_map_real, sum_order_real order (scoreOrder_perm r v q),
    recoverReal_profit order y (scoreOrder_perm r v q) hlen f] at hh
  exact hh

/-- The labeled reconstruction therefore cannot reduce transformed profit. -/
theorem realCandidate_transformed_optimal {n : ℕ} (r v : Fin n → ℚ) (α K q : ℚ)
    (ρ t : ℝ) (hq : ScoreCompatible r v ρ q) (z : Fin n → ℝ)
    (hz : FixedSupportKnapsack.ScaleFeasible (fun i => (v i : ℝ)) (α : ℝ) (K : ℝ) t z) :
    (∑ i, ((r i : ℝ)-ρ)*FixedSupportKnapsack.reconstruct (fun j => (v j : ℝ)) t z i) ≤
      ∑ i, ((r i : ℝ)-ρ)*realCandidateVector r v α K q t i := by
  unfold realCandidateVector
  rw [FixedSupportKnapsack.transformed_profit_identity,
    FixedSupportKnapsack.transformed_profit_identity]
  exact add_le_add_left (realCandidateIncrements_optimal r v α K q ρ t hq z hz) _

end BalancedAssortments.FixedSupportAlgorithm
