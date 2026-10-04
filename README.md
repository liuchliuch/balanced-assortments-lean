# Balanced assortments in Lean

Lean 4 formalization of Xiaotie Deng, Hanyu Li and Chenghua Liu,
[*Cardinality-Constrained Randomized Assortments with Balanced Market Share*](https://arxiv.org/abs/2609.35802v1).

All nine numbered source claims have compiled, source-reviewed proofs. The
recorded final release compiled all 599 project modules, including the aggregate,
from fresh outputs with trust level zero and passed its complete origin-based
transitive axiom audit. Historical partial runs are excluded from this repository.

## Build and verify

Install [Elan](https://github.com/leanprover/elan), Python 3 and Git, then run:

```sh
lake exe cache get
python3 scripts/verify_publication.py
```

Lean 4.24.0 and all nine dependency revisions are pinned. The verifier checks the
unchanged mathematical inputs, cleans this project only, builds every proof,
audits all originating declarations with trust level zero and runs the hard
regression assertions. Only `propext`, `Classical.choice` and `Quot.sound` are
permitted axioms. See [verification notes](docs/PUBLICATION_VERIFICATION.md),
[claim ledger](docs/CLAIM_LEDGER.md) and [bit model](docs/BIT_MODEL_REVIEW.md).

No software license has been selected for this release.

## Input domains and computational contracts

The paper's algorithmic model has a nonempty product set, positive rational
revenues and attractions, `1 ≤ K ≤ N`, and `0 < alpha ≤ 1`. Revenue thresholds
may be signed rationals. The FPTAS accuracy input is rational `0 < epsilon < 1`.
Its codecs preserve padded/unreduced valid fraction encodings; malformed
framing and mathematical input validity are separate, explicitly stated checks.

Proposition 4 assumes a nonempty prescribed support. Empty assortments remain
legal in all policy theorems. Theorem 1's abstract finite-vector equivalence also
covers empty product types; the paper's positive-domain optimization and NP
languages do not silently extend their claims to `N=0` or `K=0`.

Some finite-machine control enumerations use classical finite equivalences.
Their finite transition relations, output tracks and polynomial Runs are
kernel-proved. Regression evidence distinguishes direct executable assertions
from proved actual-Run witnesses; no unavailable native-VM trace is claimed.

## Principal theorem entry points

All names below are inside `BalancedAssortments`.

- Theorem 1: `Sales.exact_attainable`, `Sales.compact_sparse_policy`,
  `Sales.rational_sparse_policy` in `SalesIntegration.lean`. The decomposition
  implementation and binary-operation bounds are in `DecompositionCost*`.
- Theorem 3: `FPTASCostCodec.flat_policy_fptas` in
  `FPTASCostFlatGuarantee.lean` combines the original-input parser, actual
  geometric-grid/knapsack program, sparse rational policy output, exact
  feasibility, approximation against every real feasible competitor, and
  polynomial bit/list cost.
- Proposition 4: `FixedSupportAmbient.ambient_prescribed_support_serialized`
  in `FixedSupportAmbientEndToEnd.lean` includes actual ambient-record/support-mask
  preprocessing, exact support/global optimality and polynomial cost in the
  original serialized input. `runAmbient_original_policy` links the same output
  to the original randomized MNL model. The raw solver core is
  `FixedSupportCostProgram.binary_fixed_support_solver`; its alternative to
  the paper's LP proof is explained in `docs/FIXED_SUPPORT_ALTERNATIVE.md`.
- Corollary 5: `FixedSupportReal.alpha_one_exact_maximum` in
  `FixedSupportReal.lean` (with a rational counterpart in `FixedSupport.lean`).
- Proposition 6: `Counterexample.shared_unique_optimizer`,
  `Counterexample.rectangle_obstruction`, and original-policy bounds in
  `CounterexampleModel.lean` / `Counterexample.lean`.
- Theorem 2: `PaperTheoremTwo.fixed_policy_npComplete` and
  `PaperTheoremTwo.policy_npComplete` in `PaperTheoremTwo.lean` prove
  conventional NP-completeness of the original randomized MNL policy
  threshold language, including the numeric K=2, alpha=1 restriction.
  The full actual Cook–Levin→3CNF→positive Subset Sum→source chain and
  finite nondeterministic membership verifier are instantiated. The named
  `PolynomialProgram.one_tape_output` corollary in
  `NPPolynomialOutputSimulation.lean` makes polynomial one-tape execution
  and designated-output-track preservation explicit.
  `PolynomialProgram.one_tape_deterministic` additionally proves global
  step determinism of that same numbered one-tape machine. Some finite control
  enumerations use classical finite equivalences; no native-VM execution of
  those composed programs is claimed.

FPTAS and exact prescribed-support runtime theorems use explicitly
instrumented Boolean/list programs with costs erased from their outputs.
Conventional NP-class assertions use finite primitive Boolean-stack programs
and the proved quantitative finite one-tape compiler. These are distinct,
explicit contracts; no polynomial annotation substitutes for machine code.

