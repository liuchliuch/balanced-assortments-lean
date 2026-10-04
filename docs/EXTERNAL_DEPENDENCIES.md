# External mathematical dependencies and read-only investigation

## Current dependency status — 2026-10-03 17:32 UTC

- **No imported polynomial LP oracle is needed.** Proposition 4 is implemented
  by a specialized finite score-regime/scale-breakpoint solver. Its actual raw
  binary program has global optimality over the real prescribed-support
  polytope, strict positive output, width bounds and a closed polynomial
  bit/list cost. The paper's Charnes–Cooper equivalence is also proved, but the
  classical assertion that general rational LP is polynomial-time is not used
  as an unproved Lean axiom.
- **Conventional NP foundations are proved internally.** The project has
  concrete finite-alphabet/state one-tape nondeterministic machine semantics,
  polynomial-clock `InNP`, finite Boolean-stack instruction programs, exact
  operational execution, quantitative tape simulation and real polynomial
  transducer composition. These are definitions and kernel-checked constructions,
  not an external library's advertised complexity-class theorem.
- **Cook–Levin's complete operational gap is closed locally.**
  `CookLevin.StackTableau.np_to_cnf` composes the real original-input initializer,
  unary clock/window/catalog tokens, finite clause builder, bit framing,
  unconditional catalogue legality, and exact tableau satisfiability. It yields
  a genuine `PolyManyOne` for every language in the concrete `InNP` definition.
  Its targeted axiom audit reports only the standard Lean/mathlib axioms.
- **The complete conventional T2 chain now composes.**
  `PaperTheoremTwo.fixed_policy_npComplete` and `policy_npComplete` target the
  actual total original randomized-policy languages, with explicit numeric
  alpha=1, K=2 and signed revenue thresholds. Actual finite-program membership,
  Cook–Levin, CNF→3CNF, 3CNF→positive Subset Sum and source-gadget reductions are
  all instantiated and composed. Two independent exact-statement/source reviews
  accepted the endpoint; targeted transitive axioms are standard-only. Final
  frozen-source validation remains a separate release requirement.
- **Algorithm-cost scope is explicit.** The sparse decomposition, exact-support
  solver and FPTAS have reviewed immutable Boolean/list operation accounting.
  This is not an assertion about the external Lean compiler's wall-clock runtime.
  The FPTAS additionally has a complete flat input/parser/output/emitter theorem.
  P4's core theorem takes an indexed raw product list and a uniform width B;
  its cost is a closed polynomial in n and B. A named total-input-volume
  specialization now compiles in FixedSupportCostInputSize/SerializedInput; the
  actual ambient mask selection/reindexing and whole-wrapper serialized-input
  polynomial bound now compile too. The final exact ambient/source-policy
  composition has passed independent review. This value-solver entry point is
  structured raw input; it does not claim to execute the flat framing parser.
- **Mathematical dependencies:** ordinary finite sums, ordered fields,
  compactness/continuity, and the mathlib extreme-point theorem underpin the
  mathematical and short-certificate layers. Rational LP certificate bounds
  are proved by active basis selection, denominator clearing and Cramer bounds.
  Standard `Classical.choice` is used for mathematical existence/proof indexing,
  not as an executable LP/DP or transition-selection oracle.
- **Release evidence remains separate.** Individual compilation and targeted
  axiom checks do not replace the pending coherent full-source build,
  complete-origin transitive axiom audit, trust-zero replay and pinned hashes.

## Historical external-source investigation — inspected, not imported

On 2026-10-03, read-only web/source inspection found TankTechnology/CLRS-Lean:
- https://tanktechnology.github.io/CLRS-Lean/CLRSLean/FourthEdition/Chapter_34/
- https://github.com/TankTechnology/CLRS-Lean

Its rendered Chapter34 exposes SUBSETSUM_npComplete over serialized indexed nonnegative-integer inputs, using a stated concrete-machine Cook–Levin and 3-CNF reduction chain. Those website claims have NOT been independently kernel-audited in this project. The current raw lean-toolchain file pins Lean4.32.0-rc1, whereas this project pins Lean4.24.0. Any adoption requires compatibility work, an exact language/model bridge, license/provenance review and full transitive proof/trust review. No third-party build script or source code was executed/imported.

Its Chapter29 page explicitly limits the certified LP solver to classical real-valued simplex completeness, without a polynomial runtime claim:
https://tanktechnology.github.io/CLRS-Lean/CLRSLean/FourthEdition/Chapter_29/
It therefore does not close this project's polynomial LP dependency.

Raw toolchain metadata is retained in paper/external-investigation solely as evidence of the inspected version, not a project dependency.
