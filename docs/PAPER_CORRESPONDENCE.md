# Paper correspondence

Source: [arXiv:2609.35802v1](https://arxiv.org/abs/2609.35802v1). All names below begin with `BalancedAssortments.`. The nine numbered claims have fixed interfaces in [`Audit/Statements.lean`](../Audit/Statements.lean); [`targets.json`](../Audit/targets.json) includes their supporting endpoints.

| Paper result | Principal Lean endpoints | Interpretation |
|---|---|---|
| Theorem 1 | `Sales.exact_attainable`, `compact_sparse_policy`, `rational_sparse_policy`; `Decomposition.CostMachine.raw_binary_sparse_decomposition` | Exact attainable-sales equivalence; at most n+1 legal policy atoms; rational reconstruction and bit/list cost. |
| Theorem 2 | `PaperTheoremTwo.fixed_policy_npComplete`, `policy_npComplete` | Original policy threshold language is NP-complete, also with alpha=1 and K=2. Actual membership and reduction programs are composed. |
| Theorem 3 | `FPTASCostCodec.flat_policy_fptas` | Executed flat parser/program/emitter returns a sparse rational policy, exact balance/cardinality feasibility, a (1-epsilon) guarantee against every real feasible competitor and a polynomial cost bound. |
| Proposition 4 | `FixedSupportAmbient.ambient_prescribed_support_serialized`, `runAmbient_original_policy` | Actual catalogue/support preprocessing and specialized solver; exact prescribed support, real global optimum, original policy meaning and polynomial original-input cost. |
| Corollary 5 | `FixedSupportReal.alpha_one_exact_maximum`; rational `FixedSupport.alpha_one_exact_maximum` | Explicit minimum-cap/rank common scale, feasible positive maximizer and exact maximum revenue. |
| Proposition 6 | `Counterexample.shared_global_optimum`, `shared_unique_optimizer`, `original_policy_bound`, `appendix_table_attainment`, `optimal_support_not_rectangle` | Exact three-product instance, all support maxima, unique optimum and rectangle obstruction in the shared model. |
| Lemma 7 | `Optimization.scale_range` | Actual optimum and lower/upper scale range from the original positivity and budget assumptions. |
| Lemma 8 | `ApproximationDiscretization.scale_discretization`; `FPTAS.discrete_candidate_exists` | Concrete finite grids, downward rounding, exact feasibility and the two-factor revenue bound. |
| Lemma 9 | `Knapsack.solve_relative_all_selections`; `KnapsackCostState.solve_decode`, `solve_cost` | Executed profit-scaled DP, exact capacity, reconstruction, approximation and cost. |

Model identities include `Sales.sales_total_probability`, `outside_pos`, `active_catalog_iff` and `balanced_iff_max_coordinate`. The optimum exists and is positive in the paper's nonempty positive domain. See [MODEL.md](MODEL.md) for the domain, codec and computation-model boundaries.

The appendix instance has prices `(65,80,64)`, attractions `(3,2,14)`, alpha `1/6` and K=2. Its optimum is `(0,2,12)` with revenue `928/15`; the explicit policy assigns `34/35` to products 2 and 3, and `1/35` to product 2 alone. Competing support bounds and the full-support dual certificate are proved with exact rational arithmetic.
