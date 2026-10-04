import BalancedAssortments.DecompositionBitBounds

namespace BalancedAssortments.Decomposition

/-- A non-integral rank-two point, using the general certified algorithm. -/
example : ValidDecomposition 2 ![(1/2 : ℚ), 1/2, 1/2]
    (greedy 2 ![(1/2 : ℚ), 1/2, 1/2]) := (greedy_correct (by norm_num [Feasible, Fin.forall_fin_succ, Fin.sum_univ_succ])).1

/-- A rank-one rational distribution with three different denominators. -/
example : ValidDecomposition 1 ![(1/2 : ℚ), 1/3, 1/6]
    (greedy 1 ![(1/2 : ℚ), 1/3, 1/6]) := (greedy_correct (by norm_num [Feasible, Fin.forall_fin_succ, Fin.sum_univ_succ])).1

/-- Full-rank boundary: every point in the unit box is implementable. -/
example : ValidDecomposition 4 ![(9/10 : ℚ), 3/5, 3/10, 1/5]
    (greedy 4 ![(9/10 : ℚ), 3/5, 3/10, 1/5]) := (greedy_correct (by norm_num [Feasible, Fin.forall_fin_succ, Fin.sum_univ_succ])).1

/-- Tight rank inequality with multiple greedy rounds. -/
example : ValidDecomposition 2 ![(9/10 : ℚ), 3/5, 3/10, 1/5]
    (greedy 2 ![(9/10 : ℚ), 3/5, 3/10, 1/5]) := (greedy_correct (by norm_num [Feasible, Fin.forall_fin_succ, Fin.sum_univ_succ])).1

example : greedy 0 (fun _ : Fin 4 => (0 : ℚ)) = [(1, ∅)] := by decide

example : greedy 2 ![(1 : ℚ), 0, 1, 0] = [(1, {0, 2})] := by decide

example : (greedy 2 ![(9/10 : ℚ), 3/5, 3/10, 1/5]).length ≤ 5 :=
  (greedy_correct (by norm_num [Feasible, Fin.forall_fin_succ, Fin.sum_univ_succ])).2

#guard decide (ValidDecomposition 2 ![(9/10 : ℚ), 3/5, 3/10, 1/5]
  (greedy 2 ![(9/10 : ℚ), 3/5, 3/10, 1/5]))

#eval greedy 2 ![(9/10 : ℚ), 3/5, 3/10, 1/5]

end BalancedAssortments.Decomposition
