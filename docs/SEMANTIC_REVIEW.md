# Independent source-semantic review

## Scope and standard

The source is the official TeX archive listed in CLAIM_LEDGER.md. A result is counted only for its actual Lean statement, including all hypotheses. In particular, an assumed optimization oracle, a checked partial constructor, an existential runtime bound with no cost model, or arithmetic on real numbers cannot stand in for the paper's algorithmic complexity theorems.

## Current review conclusion — 2026-10-03 17:32 UTC

The current status and complete numbered inventory are in CLAIM_LEDGER.md.
Its nine-row status table supersedes historical notes in this report. **All nine
numbered source claims now have accepted exact statements and stated runtime
contracts.** T2's original-policy and numeric fixed-parameter endpoints passed
two independent reviews and a standard-only transitive endpoint axiom audit.
P4's actual full ambient catalogue/mask preprocessing, source interpretation,
real optimality and original-serialized-input polynomial bound have also passed
independent review. Full-paper release still requires the coherent frozen-source
build, complete-origin transitive axiom audit, trust-zero replay and pins/hashes;
none of those final global checks is asserted to have passed here.

Important changes since the earlier reviews below:

- P4 now has an actual specialized raw-bit exact solver with real global
  optimality, strict active support, output-width and closed polynomial bit/list
  cost theorems. It does not rely on an unproved general LP oracle. Its public
  theorem is on all-active `Fin n`. New InputSize/SerializedInput wrappers now
  eliminate B and provide a literal polynomial in original payload/serialized
  bit length. The named ambient-A adapter and actual structural support-mask
  preprocessing now compose into ambient_prescribed_support_serialized, with
  original-policy optimal-value meaning in runAmbient_original_policy.
- T3 now has `flat_policy_fptas`, including actual input parsing and flat output
  serialization, not only already-structured raw records. The source theorem is
  on legal encoded inputs; arbitrary malformed-input optimality is not needed.
- The actual finite-stack Cook–Levin construction now includes its physical
  clock/fuel generation, binary scalar setup, guarded global transitions,
  serialized full catalogue and exact CNF semantics. `np_to_cnf` is a genuine
  operational `PolyManyOne` from the concrete one-tape `InNP` class. This removes
  the earlier bit/list-to-machine gap for this reduction, but not automatically
  for other algorithms. The other NP links have their separately proved
  operational implementations and now compose in PaperTheoremTwo.
- Typed one-hot shape equivalence, all generated label bounds, and unconditional
  `raw_valid` now compile. Targeted axiom audits of compiler, initializer,
  transducer, shape, raw validity/satisfiability and `np_to_cnf` report only the
  standard three axioms. Independent review of this reviewer's own compiler
  development was completed by the CNF worker.

The source model and degeneracies were rechecked: n>=1, positive r/v,
0<alpha<=1, integer 1<=K<=n, signed H, rational 0<epsilon<1, legal empty display,
nonempty prescribed support, K possibly larger than that support, zero-profit
DP branches, ties and unreduced/padded binary fractions. No new semantic
counterexample was found in this pass. The fixed-parameter T2 packaging has now passed its independent acceptance gate.

### Final P4 interface and independence notes

The final runtime theorem consumes already structured raw bit records and an
explicit Boolean support mask, counts the original full self-delimiting input,
and includes actual selection/reindexing work. It does not silently substitute
selected-instance size for ambient size. It does not claim that this entry point
executes a flat malformed-input parser. Its positive-support theorem is used
only after nonempty A yields a positive selected count. Mismatched lengths and
all-false masks are explicit errors; the separate preparation pass can represent
an empty selected list without invoking the optimizer. The original-policy
adapter proves existence/optimal value and exact aggregate BMS/display legality;
it is not presented as policy emission by the value solver.

This reviewer authored the determinant/certificate, several raw arithmetic,
Cook–Levin compiler and final input/preprocessing cost components. Other workers
independently reviewed those components and the final endpoints. This reviewer
independently inspected the separately authored ambient source/policy bridge and
T2 packaging. The review is not self-certification of those development files.

### Frozen-release gate

No further mathematical source gap was found. Final acceptance for delivery is
conditional only on the forthcoming coherent frozen-source verification process,
not on an assumed theorem inside any accepted Lean statement. Targeted endpoint
audits use only propext, Classical.choice and Quot.sound; this does not replace
complete-origin audit of every declaration or trust-zero replay of the final
successfully built closure.

## Historical review record

The dated sections below retain evidence and earlier limitations. They describe
their stated checkpoint only; they do not override the current conclusion.

## Certified independent counterexample

`BalancedAssortments/Counterexample.lean` was independently compiled with Lean 4.24.0 using this project's mathlib. It uses no `sorry`, custom axiom, or conditional LP certificate oracle.

- `Feasible a b c` spells out the exact caps `(3,2,14)`, rank bound 2, nonnegativity, and zero-or-pairwise BMS with factor 6, equivalent to α=1/6. Self-comparisons follow from nonnegativity; the omitted self-comparisons therefore do not weaken source feasibility.
- `global_bound` proves every such real vector has revenue at most 928/15.
- `optimum_feasible` and `optimum_value` prove attainment at `(0,2,12)`.
- `unique_optimizer` proves equality forces that exact vector, stronger than the proposition's unique active support.
- `optimal_support_not_rectangle` proves no northeast revenue/attraction rectangle equals that support.
- `full_support_certificate` and `full_support_bound` prove the source's exact dual bound 11989/195; the proof actually applies whenever product 1 is positive, regardless of products 2 and 3. `full_support_attains` proves the stated full-support optimizer is feasible and attains it.
- Five additional support upper bounds plus `appendix_table_attainment` verify all other entries of the appendix table; the sixth entry follows from the global optimum.
- `policy_mass` and `policy_sales` verify the two rational policy weights and their exact MNL sales, with explicit source denominators. The assortments `{2,3}` and `{2}` are encoded in those arithmetic expressions, not yet linked by a theorem to the generic finite-set policy datatype.

This establishes the mathematical compact-model Proposition 6 and every numerical appendix certificate. `CounterexampleModel.lean` now compiles the exact equivalence with the shared Sales compact model, shared unique optimizer, and the revenue upper bound for arbitrary original MNL policies. No runtime claim is needed here.

## Current independent review (2026-10-03, 11:05 UTC)

### Theorem 1: mathematical statement accepted

`SalesIntegration.lean` was independently recompiled successfully. The former decomposition premise is now discharged:

- `Sales.exact_attainable` gives unconditional equivalence between finite legal MNL policies and the real compact feasible set.
- `Sales.compact_sparse_policy` supplies at most `n+1` indexed assortments, each satisfying the display limit (zero-probability illegal sets are replaced with the empty set).
- `Sales.optimization_sparse_policy` also transfers exact BMS and revenue.
- `Sales.rational_sparse_policy` constructs actual rational probabilities for rational inputs, not merely real-valued probabilities. Its nonzero-probability assortments are legal, exactly as the paper requires.
- `RealDecomposition.exists_linear_decomposition` proves completeness by legal boundary peeling with strictly decreasing fractional-coordinate count, exact residual feasibility, and exact probability/marginal reconstruction. No convex-hull membership or decomposition oracle is assumed.
- `DecompositionGreedy` supplies the analogous rational mathematical construction; `DecompositionAlgorithm` gives an executable algorithm.

The original partial circular checker still has its documented limitation, but it is no longer the proof of completeness: a different, fully proved greedy construction supplies the required theorem. This is an admissible proof replacement. Repeated assortment labels cause no model discrepancy: they are separate mixture atoms and can denote the same displayed set. At most `n+1` indexed atoms in particular bounds the number of distinct positive-support assortments.

This accepts Theorem 1's exact mathematical feasibility/objective equivalence and rational linear-support guarantee. It does **not** independently certify a bit-operation runtime bound. `DecompositionBitBounds.greedy_probability_bit_bound` now supplies a real advance: the canonical numerator/denominator sizes of the tilted greedy probabilities are bounded by one plus the sum of input denominator bit lengths. A bound for intermediate values, reverse-tilt output encoding, and total computation remains distinct.

### Other evolving components

- **FixedSupport:** rational Charnes–Cooper algebra, exact-support implications, and the new finite-support `alpha_one_exact_maximum` go beyond scalar inequalities. Polynomial LP optimization and real-to-rational optimality for general alpha remain different obligations.
- **Optimization:** compact attainment, positive singleton lower bound, and the direct scaling proof of the lower scale range are mathematically meaningful and accurately separated from runtime.
- **GridBounds:** now removes the supplied-horizon gap. `explicit_grid_round` uses a computed `ceil(1/δ) * ratioBits` horizon, with proved coverage. `RationalGridEncoding` gives genuine rational power representation bounds. These supersede the earlier conditional-only horizon status.
- **Knapsack:** an executable finite DP with minimum-weight pruning now has soundness, completeness, predecessor-choice reconstruction and optimal scaled-profit theorems. `solve_relative_all_selections` gives relative profit against every feasible unpruned selection satisfying the standard scaling assumptions. It is stronger than the older scalar rounding lemmas. Applying it to the actual revenue-test groups, constructing a comparison selection attaining sufficiently high profit, and handling all branches is still an outer-algorithm obligation.
- **FPTAS:** actual rational grids, candidate generation, an executable DP call, incumbent selection and reverse-tilt policy output are implemented. `runSales_feasible` and `runSales_dominates` are verified exact statements. They do not yet prove the full approximation guarantee for `runSales` against a global real optimum, nor a bit-operation complexity bound.
- **ComplexityReal:** the reduction is now expressed over real vectors and bridges to the actual Sales compact feasibility/BMS/objective definitions. Full NP-completeness is still absent: the Subset Sum complexity foundation, encoded end-to-end reduction, verifier and time proofs remain separate.

### Certificate and encoding infrastructure developed by this reviewer

These are new development contributions, not an independent review of someone else's proof. The sales worker independently confirmed the exact determinant/encoding bounds and their limited scope; the complexity worker independently reviewed the encoding, determinant and clearing files and found their stated boundaries accurate.

- **ComplexityEncoding:** actual self-delimiting natural-number bit lists and rational product fields; exact product-field decoding; complete output including the empty-preprocessing fixed no-instance; bound `(9+4L)(2L+7)` in serialized input length `L`. No parser-correctness, machine-time, or many-one language theorem is claimed.
- **CertificateBounds:** Leibniz determinant bound, binary size `n(B+n)+1`, and exact Cramer numerators/shared denominator for an integer nonsingular system. A nonsingular basis is an explicit input hypothesis, not silently obtained from LP feasibility.
- **RationalClearing:** compiled exact common-denominator identities, inequality equivalence, canonical rational instantiation, and integer coefficient magnitude bound `2^(B*row-card)`. This removes denominator clearing as an algebraic gap, and the basis/vertex existence theorem has subsequently been supplied by PolyhedralBasis as described below.
- **ComplexityPreprocessing:** independently compiled with a direct single-thread check at 11:11 UTC. `preprocessed_sales_reduction_iff` composes the original Subset Sum instance through the exact retained subtype and into the real Sales compact model. `preprocessed_parameters_legal` proves model positivity and `K=2≤n` when retained items are nonempty. This closes the mathematical subtype/preprocessing gap; it does not supply a binary parser or a machine-time reduction theorem.


### Bounded rational LP certificates (11:24 UTC update)

The former general vertex/certificate gap is now substantially closed by compiled theorems, not a stronger assumption:

- `PolyhedralBasis.two_sided_feasible` constructs a strictly positive feasible perturbation in both signs for every direction annihilating the active rows, using all finite slack ratios.
- `active_kernel_trivial` derives the absence of nonzero such directions at an extreme point.
- `extreme_has_active_basis` selects `n` distinct actual active input rows with nonzero determinant, using the derived full row span and linear independence.
- `compact_has_active_basis` obtains that extreme point from mathlib's Krein–Milman lemma. `polyhedron_compact` derives compactness from closed linear inequalities and explicit coordinate bounds.
- `PolyhedralBasisCertificates.bounded_integer_polyhedron_certificate` applies real Cramer's rule to that selected subsystem and produces an actual rational feasible point for the original real polyhedron, with per-coordinate raw numerator/shared denominator bit bound `n(B+n)+1`.
- `PolyhedralBasisRational.bounded_rational_polyhedron_certificate` performs exact row denominator clearing first, giving the complete bound `n*(B*(n+1)+n)+1` for `B`-bit canonical rational coefficients. It assumes nonempty feasible set and coordinate boundedness, not a preexisting rational point, basis, vertex, or certificate.

The sales worker independently reviewed the active-basis argument and accepted its semantics; the later rational certificate wrappers remain development contributions pending additional independent review. These statements are genuine general LP feasibility-certificate existence results. They are not a polynomial-time LP optimization algorithm or, by themselves, a full NP-membership theorem for an encoded language. The actual assortment threshold rows, coefficient-size connection to original inputs, executable verifier, binary parser and operation-cost proofs must also be composed.

### Actual FPTAS approximation guarantee (11:32 UTC independent review)

The mathematical end-to-end approximation gap is now closed. This reviewer inspected the public statements and underlying candidate/grid/DP composition, and independently compiled `FPTASGuarantee.lean` successfully.

- `runSales_approximation` quantifies over **every real feasible vector** under the original input's caps, rank and BMS, and compares it to the actual executable rational `runSales` output. No optimal-vector, discretization-oracle, good-candidate or assumed-DP-optimality premise is exposed.
- `runPolicy_approximation` quantifies over **every original finite randomized MNL policy** satisfying its per-display cardinality and aggregate BMS constraints. It proves the `(1-ε)` factor for the actual `runPolicy` list's sales.
- `FPTASPolicy.runPolicy_valid` proves exact probability mass/nonnegativity, display legality and linear output support; `runPolicy_balance_revenue` proves exact BMS and revenue realization.
- The proof covers the singleton-incumbent branch, actual revenue-grid predecessor, construction/deletion of nonpositive-profit options, positive maximum-option branch, DP reconstruction and acceptance.

Accordingly the mathematical approximation, rational implementation and exact feasibility parts of Theorem 3 are accepted. The word **fully polynomial** still needs the actual bit-operation runtime theorem for a bit implementation refining the rational algorithm. Current bit-list primitive and instrumented cost modules are progress toward it, not a reason to omit that final distinction.

### Actual source rational certificates (11:32 UTC development update)

`DecisionCertificates.lean` compiled successfully. `source_short_rational_certificate` composes the actual guessed-support row matrix, exact source objective/feasibility equivalence, row coefficient bounds, and general bounded-rational-polyhedron theorem. Every actual real yes-instance now has an actual rational source-feasible vector represented by integer numerators/shared nonzero denominator, each of bit size at most `n*((2B+1)*(n+1)+n)+1`, where `B` bounds canonical binary magnitudes of the original data. Positivity of the denominator can be enforced without increasing sizes. This closes the source LP witness-existence/size gap, while encoded-language NP membership, binary verifier refinement and runtime still need explicit composition.

### Concrete FPTAS size and bit-operation infrastructure (12:00 UTC)

Compiled `FPTASCostBounds`, `FPTASCostItems`, `FPTASCostInput` and `FPTASCostCounts` now remove externally supplied field-size assumptions for actual calls. `actual_call_field_widths` derives the initial encoded theta/value/weight/profit widths from the sum of canonical original input bit lengths and `ceil(10/epsilon)`. Product count is bounded by this input length. Scale/revenue/option lengths, total candidate count and the actual DP profit cutoff have explicit polynomial bounds.

`FPTASCostGrid.gridBits` is an actual Boolean-list/fraction implementation, with successive schoolbook multiplication and cross-product comparison. Its decoded output equals the exact mathematical geometric grid; its instrumented binary/list cost is bounded polynomially in exponent horizon and input widths. Its API explicitly receives the binary base, ratio and cap. `FPTASCostSeeds` supplies binary min/max, reciprocal/division, singleton revenue and scale-base construction with correctness, width and cost proofs. These are development contributions pending full independent cost review. They substantially advance the runtime proof but do not, individually, constitute an assembled whole-FPTAS runtime theorem.

### Outer binary implementation refinements (12:18 UTC)

`FPTASCostOuterSeeds` and `FPTASCostSeedRefinement` now implement and verify the complete five-field outer seed computation on arbitrary valid padded/unreduced binary fractions: exact vmin/vmax/rmax folds, all singleton revenues and their maximum, scale base/cap and growth ratio. The output fields match the actual FPTAS definitions, with explicit polynomial bit/list costs and width bounds.

An independent parent review correctly identified that the earlier semantic `rawHorizon` used decoded natural values and multiplication as an uncharged execution control step. `FPTASCostGridFuel` closes this specific gap: the executable `rawGrid` now uses charged binary reciprocal rounding, binary-to-unary quota expansion, bit-to-token traversals, charged Cartesian token replication, and a structural token-consuming loop. It refines the exact canonical grid and its cost includes this entire fuel construction. The earlier natural-valued horizon remains only a semantic specification. This distinction must be preserved when describing the assembled runtime result.

### Charged source count/accuracy preparation (12:26 UTC)

`FPTASCostInputSeeds.prepareSeeds` now takes only the raw alpha, epsilon and product-list fractions. It computes product count by a binary-increment scan, computes epsilon/10 by binary division with a literal ten fraction, picks the first attraction in constant work, and constructs all five grid seeds. `prepareSeeds_actual` gives the exact original-input field interpretation; validity, raw width and complete polynomial preparation-cost theorems are compiled.

The sales worker independently reviewed the grid-fuel and input-seed layers: it found no remaining uncharged scalar/count/seed-oracle step in these layers. Its review explicitly limits that conclusion to the stated **erased-cost bit/list computation model**, rather than claiming a theorem about the external Lean compiler's wall-clock machine time. A conventional Turing-machine or equivalent simulation, if used for complexity-class statements, must be made explicit rather than silently inferred from compilation.

The appendix now also has `CounterexampleModel.shared_unique_optimizer` and `original_policy_bound`, compiled adapters to the actual shared compact and original MNL policy semantics.

### Independent integration review (12:34 UTC)

- `FPTASCostAutoGroups` was inspected and independently recompiled. Accepted contracts: actual cap construction and charged automatic list fuel; exact source option-list decoding; no caller-supplied covering-horizon premise; polynomial raw widths/counts/costs. The repeated cap computation is included in the cost. Initial unscaled item score fields are correctly outside the later profit-scaling step.
- `FPTASCostOutput` and `FPTASCostPolicy` were inspected and independently recompiled. Accepted contracts: exact unrounded revenue comparison, transformed-profit acceptance, mask-based display denominator, rational reverse tilt, output widths/count/cost and validity under the stated actual decomposition certificate. The generic revenue routine deliberately uses `zip`; its source-model use needs equal-length price/candidate lists, which the top-level pipeline must discharge. Mask length/serialization must come from the actual sparse decomposition, not from the generic reverse-tilt theorem alone.
- `ComplexityTimeSourcePipeline` genuinely builds rational source rows from raw signed fractions, clears denominators with bit algorithms and checks integer cross-product certificates; source dimension is read from the attraction list. Its polynomial cost theorem is in stored bit input plus certificate size. Current source correctness theorems require valid source fractions and canonical `encodedNumerators p`/`zencode q` certificate encodings; current cost statements also expose shape bounds. The executable entry point does not yet itself reject every malformed source encoding or validate all legal-model conditions. The author confirmed this boundary and is documenting it. Therefore the current package must not promote this to a complete encoded-language NP-membership/completeness theorem without the remaining domain/parser/raw-certificate bridge.

A small additional mathematical optimizer lemma in `PolyhedralBasisOptimization` is compiled: a compact integer polyhedron has a polynomial-size rational maximizing point for any linear objective, derived through its exposed maximizing face and the proved active basis. It is not a polynomial-time LP algorithm and is not counted as completing Proposition 4.

### Complete binary-policy theorem (13:18 UTC independent review)

This reviewer inspected `FPTASCostCompleteGuarantee`, `FPTASCostComplete`, and `FPTASCostCompletePolynomial`, and independently recompiled the final guarantee module. The stated complete contract is accepted **in the explicit erased-cost bit/list computation model**:

- `binary_policy_fptas` concerns the actual raw `runPolicyBits` program, including source preparation, sales computation, marginal division, raw binary sparse decomposition and exact reverse tilt.
- All remaining hypotheses are legal source inputs and their raw binary representations; no good candidate, supplied cutoff, sparse decomposition, horizon or polynomial runtime is assumed.
- It proves exact normalized policy feasibility and BMS, at most `N+1` atoms, positive raw denominators and `N`-bit masks, approximation against every real feasible sales vector, and a literal multivariate polynomial cost in the original serialized input length and `ceil(10/epsilon)`.
- `binary_policy_approximates_original` also supplies the original randomized-policy comparison.
- The formerly exposed candidate-list length and decomposition premises are discharged by the actual sales-program semantics and raw decomposition correctness in the complete pipeline.

This does not prove a statement about wall-clock execution of the external Lean compiler or provide a simulation/compiler into the new concrete `NPMachine` model. It must not be silently reused as such a simulation for conventional NP-class statements. The whole paper remains incomplete while the genuine source NP foundation, exact-support bit pipeline and final aggregate audit remain open.

## Prohibited completion shortcuts

- Do not identify a polynomial number of DP states with bit-polynomial runtime unless transitions, options, arithmetic sizes and predecessor recovery are bounded.
- Do not identify a correct Subset Sum instance equivalence with NP-completeness without encoded languages, polynomial reduction, NP-hard source, and NP certificate proof.
- Do not identify rational executable output validation with unconditional successful rational reconstruction.
- Do not report “full paper formalized” on the basis of module compilation or a `sorry`/axiom scan.

## Historical open obligations at 13:18 UTC

At this checkpoint T2, P4 computational composition and machine-model bridges were still open. Later sections and the current conclusion supersede this historical list. These were source coverage gaps, not admitted Lean proofs.

### 2026-10-03 13:35 UTC: concrete machine tableau checkpoint

`NPMachineModel`, `NPMachineWindow`, `NPMachineTableauSemantics`,
`CookLevinEncoding`, `CookLevinTableau`, `CookLevinStepSemantics`, and
`CookLevinCorrect` compile. `tableau_satisfiable_iff_acceptsWithin` is an
unconditional equivalence between satisfiability of the generated ordinary CNF
and bounded acceptance by a fixed finite-state, finite-alphabet nondeterministic
one-tape machine. A global one-hot transition choice controls the entire row;
accepting padding preserves the full configuration. The tape-window restriction
is derived from the stepwise head bound, including the zero-step case.

The CNF/3CNF worker independently audited these modules and found no semantic
mismatch. This author developed these modules and does not self-certify their
independent review. `CookLevinSize` now proves an explicit polynomial bound on the
actual clause count; `CookLevinLabels` proves an explicit polynomial label range.
These size facts do not yet prove a polynomial-time generator. Charged binary
emission and the simulation/compiler bridge into the concrete clocked machine
class remain open. Consequently no source NP-completeness conclusion is accepted
at this checkpoint.

## 13:43 total 3CNF-to-positive-Subset-Sum review
The coordinator independently checked the exact total-language statement and
actual constructor/parser/normalizer/emitter path. Invalid framing, semantic
catalog errors and clauses longer than three map to a fixed positive no-instance;
the zero-dimensional valid formula maps to a fixed positive yes-instance. Item
multiplicity uses indexed list-subset semantics. All variable loops traverse
actual catalog/occurrence records; binary label magnitudes are never expanded
as unary structural bounds. The explicit polynomial bounds are accepted for
the stated erased-cost Boolean/list contract. Concrete-machine realization is
still open and this is not an NP-completeness acceptance. Source hashes and
scope are in `certificates/np-reduction-semantic-review.json`.

### 2026-10-03 14:30 UTC: raw machine-to-CNF construction

The complete raw constructor and polynomial-clock fuel front-end have compiled
semantic refinement. `CookLevinRawCorrect.constructBits_correct` and
`CookLevinClockFuel.np_has_explicit_cnf_map` take only the original word and fixed
machine/program constants. `CookLevinRawBudget.constructBits_cost` includes
binary enumeration, all address operations, all clause families, initial tape
padding, global choices, catalog deduplication, and actual self-delimiting output.
Its explicit budget is a polynomial arithmetic expression; formal polynomial
reification is in progress.

Independent CNF-worker review accepted the executable boundary, with the precise
qualification that persistent immutable bit-list sharing is constant-cost in this
source model. Stack/tape lowering must explicitly implement copying and charge
its polynomial overhead. That bridge is not assumed by any accepted theorem.

### 2026-10-03 14:36 UTC: full functional Cook–Levin cost closure

The natural polynomial budget is now formally represented by `Polynomial ℕ`.
`CookLevinPolynomialCost.reduceMachine_polynomial_cost` and
`np_has_polynomial_bit_cnf_map` compile, discharging all raw generator and clock
fuel cost premises. The machine constants are fixed per NP language, while the
only variable input is the original Boolean word. The complete source program
still needs an operational lowering theorem before its cost can be asserted in
the concrete tape-machine complexity class. This boundary is explicit in the
final theorem comments and ledger.

The CNF worker independently reviewed `CookLevinClockFuel` and
`CookLevinPolynomialCost` after final compilation and accepted their stated
bit/list contract, including the original-input clock scan and complete cost
composition. The new operational `StackClock` compiler is developed by this
reviewer and awaits a separate independent audit; its type is an actual finite
`NPStack.PolynomialProgram`, not the earlier instrumented-function interface.

### 2026-10-03 16:38 UTC: genuine operational Cook–Levin constructor

`CookLevinStackBuilderCorrect.compile_exec` now proves actual primitive
Boolean-stack execution for every fixed streaming schema. Lexical index loops
save and restore scalar bindings and private registers. Arithmetic expressions
invoke existing binary stack programs, and output field framing is charged by
actual encoder runs. `CookLevinStackInitializeProgram.initialize_exec` starts
with the original input alone and constructs all clock/window/catalog tokens
and scalar fields with actual loops. `CookLevinStackProgram` proves a fixed
natural-polynomial bound in original input length and restricts the fixed
register set to a genuine finite type. `CookLevinStackTableauProgram` specializes
this to the full concrete machine-specific tableau schema with no input/layout
premises. These files have compiled individually.

The concrete schema was independently sanity-checked against the previous
mathematical tableau: global rule selection, guarded boundary moves, accepting
stutter, all unaffected tape cells, full initial tape partition, and framing
match. Exact typed-schema CNF equivalence and catalogue validity are still
being proved by the parent and this reviewer. Thus this checkpoint establishes
the operational constructor, not yet the complete Cook–Levin reduction theorem.
The compiler and initializer were authored by this reviewer; their independent
review has been requested from the CNF worker. No source NP-completeness label
is justified solely by the operational constructor without its semantic bridge.
