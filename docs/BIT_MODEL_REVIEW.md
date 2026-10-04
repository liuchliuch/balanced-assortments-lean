# Independent bit/list model review

Reviewed 2026-10-03, approximately 12:19 UTC. This is a source-level review of the sparse decomposition and FPTAS/knapsack layers, not of the reviewer's own `ComplexityTime*` implementations. New outer-composition files may supersede the integration gaps below.

## Model scope

The implemented algorithms operate on immutable Boolean lists and records. Instrumented natural counters charge Boolean arithmetic routines, list traversal/copying, and constant record/dispatch work. Existing immutable fraction records can be shared: copying a choice-list spine does not deep-copy the bit strings inside its entries. This is an explicit bit/list cost model, not a proved compiler simulation into Lean's runtime, a heap machine, or a Turing machine. Allocation, garbage collection and reference-count implementation costs have not been mechanized. Bounded loop indices/fuel are natural control counters, not unit-cost arithmetic on unbounded input rational values.

The implementation uses return-value/counter pairs, not a deep-embedded instruction language with an independent step evaluator. Kernel checking proves inequalities about those second projections. Correspondence between each increment and primitive work is validated here by source inspection; it is not enforced by a formal interpreter or compiler theorem. Thus a small counter attached to an arbitrary Lean function would not by itself establish runtime, and none of the source/NP conclusions should be presented that way.

`*_decode`, `*_refines`, `interpretGrid`, and similar functions used only in theorem statements describe mathematical meaning. They are not automatically included in charged execution. The proved counters must not be promoted to a machine-defined NP-class theorem without a model/representation bridge. The separate source NP-completeness dependency remains open.

## Sparse decomposition: checked chain

Files reviewed include `DecompositionCostInput`, `Rank`, `Machine`, `Execution`, `Refinement`, `Certified`, and `Raw`.

- Initialization multiplies supplied binary denominators and, for each numerator, the other denominators. It does not divide, normalize rationals, or invoke gcd.
- `productBits` places the fresh input operand first, preventing exponentially growing padding in repeated multiplication. Width/cost statements use actual stored bit volume.
- Rank parsing is concrete: `rankTokens` creates unary quota cells, charges append copies, and has cost bounded by `2*K + 4*input_bit_length + 1`. The final polynomial theorem explicitly assumes the legal `K <= n` bound.
- Classification, minimum boundary selection, subtraction and residual updates use concrete bit comparisons/subtraction. Selection operates on unary quota cells, and its construction is charged at every call.
- `raw_binaryGreedy_eq_greedy` and `raw_binary_sparse_decomposition` cover arbitrary unreduced positive-denominator inputs, closing the otherwise missing canonicalization bridge.
- Output is a shared binary denominator plus binary numerator/mask atoms. This is a meaningful rational-policy representation. The theorem proves exact marginals, positive masses, cardinality and linear support for its interpretation.

No arithmetic or output-refinement mismatch was found in this chain. Byte-level serialization of the output record format is a distinct boundary; the mathematical interpretation itself is not an executed gcd/conversion step.

## Knapsack and grid kernels: checked chain

Files reviewed include `KnapsackCostRational`, `State`, `Scaling`, `Preprocess`, `Range`, `Compression`, `Transition`, `DP`, `Solve`, and the `FPTASCostSeeds`, `SeedLists`, `OuterSeeds`, `SeedRefinement`, `Grid`, `Options`, `Groups`, `Kernel`, and `Output` families.

- Unreduced rational addition, comparison, multiplication and floor-ratio scaling are implemented by explicit bit routines. The floor-ratio theorem requires positive scale and valid denominators; the kernel's positive-profit branch provides these conditions.
- Incremental rational accumulation uses the fresh bounded-width factor first. State numerators/denominators have derived linear-in-depth width bounds rather than an assumed canonical-rational bound.
- `groupBits` checks `rho < r` before saturating subtraction, so the retained positive-profit branch refines ordinary subtraction. Zero options and the no-positive-profit branch are explicitly handled.
- `scoreRange` constructs binary score contents using ripple addition. Compression scans states, checks exact scores, and chooses the minimum-weight representative. Semantic refinement theorems preserve the rational solver's tie behavior.
- State extension charges choice-spine append; expansion charges list concatenation; row iteration, compression and final maximization have polynomial counters.
- `outerSeeds` actually computes extrema, singleton values, scale base/cap and the ratio from raw fractions. Its exact-source refinement and output-width/cost lemmas are substantive, not assumptions of their conclusions.
- `gridBits` executes each requested exponent and filters via exact cross-products. Its polynomial counter includes the multiplication and comparison at every step. A covering horizon is a real refinement premise, discharged mathematically by the raw-horizon lemmas when used with valid positive inputs.

No arithmetic-semantic mismatch was found in these reviewed kernels.

## Concrete integration gaps at review time

1. **Raw horizon execution.** `FPTASCostRawHorizon.rawHorizon` decodes `reciprocalCeilingBits` with `value` and performs natural multiplication by raw bit lengths. The reciprocal ceiling has a charged bit implementation; horizon magnitude/refinement is proved. Conversion to actual unary loop fuel and multiplication of those counts were not yet charged by this definition. Reusing the existing `rankTokens` conversion and explicit list repetition would close this, with allowed polynomial dependence on `1/delta`.
2. **DP cutoff construction.** The kernel takes a natural `bound` and proves cost polynomial in that bound. The outer caller still needs a charged construction and a connection to the required `n*ceil(n/delta)` cutoff. A supplied-bound theorem is not the whole FPTAS runtime theorem.
3. **Count and accuracy preprocessing.** Seed-refinement statements accept a raw fraction for product count and a raw `delta`, with semantic equalities. The complete caller must compute count and `epsilon/10` from the actual input or explicitly include their generation cost.
4. **Legacy canonical wrapper.** `FPTASCostSolve.binaryCall` directly computes rational groups, maximum profit, theta, a rational ceiling and `encode` wrappers, then returns only `scaledSolve`'s counter. `KnapsackCostEncoding.prepareItem` likewise takes canonical mathematical items. These are useful semantic/testing wrappers, but their counters alone do not cover those front-end computations. The new raw `groupsBits`/`core` path is the appropriate replacement.
5. **Final policy conversion.** At review time `FPTASCostOutput` supplied comparison/revenue and an assortment-denominator helper, but a complete charged mapping of decomposition masses through reverse tilt, with exact output refinement and serialization, was not yet present in the files reviewed. It must be included before claiming a fully costed policy-producing FPTAS.
6. **Outer program composition.** Individual polynomial counts and refinements must be connected to one actual program whose returned output is the output used by the approximation/feasibility theorem. Merely listing kernel bounds is insufficient.

These are integration boundaries, not counterexamples to the proved kernel theorems. They were reported immediately to the coordinating worker and the affected implementers.

## Source snapshot hashes

- `BalancedAssortments/DecompositionCostInput.lean`: `bad11d35c4a8168148c0a4dddf3f76deaaf331e41b9b202f0249fd1b137f3370`
- `BalancedAssortments/DecompositionCostRank.lean`: `df8220d196159a9a6606a3cb4634736183bebdb11990af90d51b2ee582b5c43d`
- `BalancedAssortments/DecompositionCostRaw.lean`: `705280c4c662e0c264716e9224a6c5b4304b3d480a872a7725f9b1ed4a75391f`
- `BalancedAssortments/DecompositionCostExecution.lean`: `7673b1e960115b6fcd4d1ac049472d4003ce1d5dd57fd2189c8489322f97b726`
- `BalancedAssortments/KnapsackCostRational.lean`: `0a84cdac758cc9bf30de709a24dfa9eff2bbe5ddf13583d6efe655ccd1163474`
- `BalancedAssortments/KnapsackCostScaling.lean`: `cf2dd00e29557e17d7a52d92db5a5a69f7d336a67a7b2edae1c5de1ba6588fcf`
- `BalancedAssortments/KnapsackCostState.lean`: `25de8fc0fa9a6329d929504f3c338eb236ab9d1d15fa76f62606f7c69d81e209`
- `BalancedAssortments/KnapsackCostDP.lean`: `945c829de38b3371a4757ed3049f0da27dcb67e00d8106b181763a5c99aed14f`
- `BalancedAssortments/KnapsackCostSolve.lean`: `a5af6d91a502b8c25f9a25f1082a5dd9cee36f38d37cb0c2f114cfbcbaff91bc`
- `BalancedAssortments/FPTASCostOuterSeeds.lean`: `a486ecad61823e46f9cbba2e823529e93229efb5b9e1ec44b9eda8159e8dc968`
- `BalancedAssortments/FPTASCostGrid.lean`: `8aa93fce0db679e2a611479faf93fd9f8cc334169419883a50198b23a16900e2`
- `BalancedAssortments/FPTASCostRawHorizon.lean`: `f248e235b1de2033d9604c2ebdbe8b78b757a8f8b0f146bed251f1e30eada223`
- `BalancedAssortments/FPTASCostOptions.lean`: `890f155468656cc67d439d2b708078e27348e37bb648c1e3181b1c4a3f8e6943`
- `BalancedAssortments/FPTASCostKernel.lean`: `07cf47e71f3ee36d93b5a9f7db533fed1332e61174a294bc4c35fc8cca74c8b5`
- `BalancedAssortments/FPTASCostSolve.lean`: `37a65f63d0c4da9cbe6255bfe3090f3941204662765f723e242087e7a4de143b`
- `BalancedAssortments/FPTASCostOutput.lean`: `5cfb54067ff0773bad45f4887576c0b870c8441af1d23da535c8e3bec88c4b72`

## Follow-up review: charged grid fuel (12:28 UTC)

`FPTASCostGridFuel.lean` closes the component-level raw-horizon execution gap. `reciprocalCeilingBits` is followed by the existing charged binary-to-unary `rankTokens`; `bitTokens` constructs one cell per base-denominator/cap-numerator bit; `multiplyTokens` materializes the Cartesian quota and charges every copied list cell. `gridTokens` consumes that quota structurally and is proved equal to `gridBits` as an entire output/counter pair. `rawGrid_refines` and `rawGrid_cost` compose fuel construction with grid execution. No uncharged decoded integer controls this executable path. The final outer caller must use this path rather than the old numeric-horizon specification.

`FPTASCostAutoGroups.lean` was subsequently implemented by this reviewer, so it is explicitly excluded from this independent audit and requires another worker's review. It contains cap/fuel/group composition and exact/cost refinements; this note does not independently certify its accounting.

Fuel source snapshot: `efa64e3cdaafeefcadf87c65f63611548708fc9c17f5e2b660ce505a7258e047`.

## Source-verifier domain boundary (12:33 UTC)

This paragraph records the source-checker API scope; its arithmetic was authored by this reviewer and reviewed separately by another worker.

`ComplexityTimeSourcePipeline.verifySource` takes already structured lists of raw fractions, an accuracy/balance field, a revenue target, binary K, a support mask, and raw integer certificate records. It is **not** a total parser-and-validator for a serialized NP language.

- It does not reject malformed source schemas or mismatched attraction/revenue list lengths as a front-end validation step.
- It does not reject zero raw denominators, nonpositive revenue/attraction values, alpha outside `(0,1]`, or K outside the model's legal range. Such conditions are hypotheses of the semantic/refinement theorems or restrictions of the original model.
- It does check positivity of the shared certificate denominator and equality of each generated coefficient-row length with the supplied numerator-list length.
- The source-facing soundness/completeness composition currently states its certificate using `encodedNumerators p` and `zencode q`. The generic integer checker has representation-level correctness, but a separate source-facing arbitrary-raw-certificate adapter is still needed before quantifying over all parsed certificate strings.
- The cost theorem assumes the documented source list-length bounds (revenue/support lists no longer than the attraction list). It proves a polynomial in total stored raw source/certificate bits on that domain.
- `certificateBits` gives a real signed/self-delimiting serialization and a polynomial length bound. A source/certificate parser with explicit invalid-format rejection and a refinement to the checker has not been composed here.

Consequently `source_polynomial_certificate_verifier` is a substantive legal-instance verifier/certificate theorem in the explicit bit/list cost model. It must not be restated as a completed, total, machine-defined NP-language membership theorem. The parser/domain-validation bridge, the operational-machine bridge, and the source NP-completeness foundation are distinct remaining obligations.

## Total source language bridge closed (13:07 UTC)

The preceding 12:33 scope statement remains accurate for the old `verifySource`
entry point alone. The new `ComplexityTimeSourceParsing`, `SourceValidation`,
`CertificateParsing`, `TotalVerifier`, `ParsingBounds`, `TotalBounds`, and
`TotalCertificates` modules close the identified domain/parser integration gap.

`totalVerify` accepts two arbitrary Boolean strings, executes the structural
self-delimiting parsers, rejects incomplete records, checks the declared product
count against the actual parsed list, validates all denominators and positive
prices/attractions, enforces `0 < alpha <= 1` and `1 <= K <= n`, validates mask
fields, checks certificate dimensions, and requires a positive represented
certificate denominator. Revenue target may be positive, zero, or negative.
Numeric header values never allocate lists or supply uncharged iteration fuel.
Certificates may use arbitrary noncanonical signed-difference bit records;
`SourceRawCorrect` supplies the representation-independent semantic bridge.

`source_language_iff_short_accepted` characterizes the independently defined
serialized real-feasibility language by actual accepted certificate strings of
an explicit polynomial length. `totalVerify_polynomial_cost` bounds execution's
charged counter by an explicit polynomial in the sum of the two input string
lengths, with no source-domain or certificate-domain hypotheses. Malformed
inputs are included in that bound.

This is still the explicitly described Boolean/list primitive accounting model.
A proved interpreter/compiler or Turing-machine simulation of these functions
is a separate foundation obligation. These additions do not by themselves
assert membership in a separately defined machine-based NP class, or establish
source NP-completeness. They were authored by this reviewer and require another
worker's independent charge-accounting review.

## Independent final FPTAS composition review (13:15 UTC)

Reviewed `FPTASCostProgramCorrect`, `Complete`, `CompleteBound`,
`CompleteShape`, `CompletePolynomial`, and `CompleteGuarantee` against the
actual `runSalesBits` / `runPolicyBits` definitions and source Theorem 3.
The reviewer did not author these modules. The automatic group component was
previously authored by this reviewer; its accounting still requires the other
worker's independent review.

The composed executable path now closes the previously listed integration
boundaries:

- `prepareSeeds` computes the binary product count, epsilon/10, extrema and
  singleton revenue seeds. `programSeedFacts` derives all seed identities,
  positivity, coverage and actual cutoff-token length from legal inputs.
- Both outer grids execute `rawGrid`, including charged quota construction.
  Each actual callback invokes `autoCandidate`, automatic group generation,
  scaling, the structural-token DP, and acceptance. The legacy `binaryCall`
  specification is not used by this executable path.
- Returned candidate lengths and fraction validity are proved before the
  incumbent comparison. `runSalesBits_semantics` proves feasibility of the
  actual returned list and objective domination of the mathematical algorithm.
- `finishPolicy` computes w/v on the unreduced output, runs the actual binary
  sparse decomposition with its charged rank conversion, then executes the
  exact reverse denominator tilt. Its premises follow from the just-proved
  sales feasibility. The tilt's common normalizer is computed once.
- `binary_policy_fptas` concerns exactly the returned raw policy. It includes
  normalization, cardinality, balance, linear support, positive raw denominators,
  one mask bit per original product, approximation against every feasible real
  compact vector, and a literal multivariate natural-coefficient polynomial
  counter bound. `binary_policy_approximates_original` gives the original MNL
  policy comparison directly through the proved compact equivalence.
- Input-width/product-count substitutions use the length of a concrete
  self-delimiting serialization. No supplied horizon, supplied grid, hidden
  normalization, numerical cutoff oracle, or unspecified LP/knapsack oracle
  remains in the composed execution theorem.

No result/refinement mismatch or uncharged decoded rational/Nat arithmetic in
the result-producing path was found. This accepts the claim in the documented
immutable Boolean/list primitive accounting model. Cost-only counter arithmetic
is ghost instrumentation. These proofs do not establish compiled Lean wall-clock
cost or a separately defined Turing-machine simulation.

The FPTAS entry point takes legal raw fraction/list records. Its size parameter
is their concrete serialized length; the theorem does not claim that this
particular entry point parses arbitrary malformed input bitstrings or emits a
flat serialized output bitstring. It returns already-bit-represented raw policy
records. This interface scope is distinct from the fully serialized decision
verifier above.

Reviewed source snapshots:
- Program: `ea19d3948678ddb04d83b6700bbf43ee12de2ace58bf12df6988e3835dd2f48a`
- ProgramCorrect: `44af016ce8cea80c67037a22273014f6bc40d473f8ea61613a3e0dfee3d1d84a`
- Complete: `c34b85c2daf501b8666fc567ed24c2f1078715502201b971e170c7df8c5b60bb`
- CompleteBound: `73f128df0d00aa3708f8547c0db644d591e2092785fb3aa60fd9bb80914be104`
- CompleteShape: `3b161858513f3cda29556646d9c87209c836d4cd9ad616a016985fdde3939b29`
- CompletePolynomial: `96c1f6133b0729129b531cc9c9d3fa006bc8d0515b247a6d400cb324370bc826`

## Operational arithmetic and hardness-link update (15:31 UTC)

The former ghost-counter boundary has now been crossed for several concrete
components. `NPStackReverse`, `Copy`, `Add`, `MultiplyCorrect`, and the comparison
modules give actual runs of finite primitive push/pop/jump control tables.
`NPStackEmbedding` preserves exact transition counts under finite subroutine
relocation and preserves every unused work stack. `NPStackMacros` expands calls
into those primitive instructions; no semantic callback remains in its target.
`NPStackSourcePolynomial` uses that infrastructure for the complete total
positive-Subset-Sum-to-signed-BMS transducer and proves a cubic actual transition
clock. These statements concern genuine bytecode runs, independently of earlier
functional cost counters. The separately proved finite-stack/tape compiler
connects this model to the concrete finite one-tape machine foundation.

These new modules were authored by this reviewer, so their semantic and
accounting review must be performed independently. They do not by themselves
supply operational lowering of the complete FPTAS or of every NP-chain component.

### 2026-10-03 17:09: completed operational lowering of the 3CNF gadget

The earlier erased-cost-only boundary is closed for the 3CNF → positive Subset Sum link by `NPSATStackPolynomialReduction.three_cnf_reduces_positiveSubsetSum`. Its `PolynomialProgram` comes from the concrete finite Boolean-stack instruction graph and `NPStack.Clocked.polyComputable`; the timeout clock itself is physically generated, copied, consumed, and followed by an actual fixed-output emitter. No decoded variable label or declared count drives an uncharged loop. Dimensions are obtained by scanning actual records, and the zero-column tokens used by slack/target loops are generated by real fresh-query label/formula scans.

The operational proof covers all source bits. Valid inputs finish within `validClock`; malformed/invalid inputs have actual rejecting executions, while every accepting run is characterized without any time-bound premise. The finite wrapper totalizes these paths. Numeric refinement explicitly accounts for reversed catalogues/items and noncanonical integer fields. This statement is a finite-machine-backed many-one reduction under the repository's proved Boolean-stack-to-one-tape bridge; it is no longer merely a functional ghost-counter estimate.

Authorship boundary: the main complexity worker authored this new lowering and therefore does not count this entry as its independent review. Separate workers are reviewing the final semantic edge cases and control/clock composition. Axiom prints are in `certificates/three-sat-operational-axioms.log`.
