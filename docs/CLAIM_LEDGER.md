# Source claim ledger

Source: `paper/75-Cardinality-Constrained_Randomized_Assortments_with_Balanced_Market_Share.tex`, official v1 archive retained alongside SHA256SUMS. Numbers follow the shared theorem counter. This ledger distinguishes a mathematical core, an algorithm, and a complexity theorem; none implies the next without the stated additional obligations.

## Model and supporting claims

- **M1 (lines 122–166):** finite, nonempty product set; strictly positive revenues and attractions; normalized outside attraction 1; integer `1 ≤ K ≤ n`; `0 < α ≤ 1`. Complexity inputs are binary-encoded rationals. Empty assortments are legal.
- **M2:** probability mass and nonnegativity, `x₀ + Σxᵢ = 1`, strict `x₀ > 0`; active purchase set equals union of positive-probability assortments. This equality relies on positive attractions and probabilities.
- **M3:** BMS is zero-or-relative-to-maximum, equivalently zero-or-pairwise inequalities. It constrains aggregate purchase probabilities, not display marginals. The active set may have more than K elements.
- **M4:** existence of a global optimum; nonzero optimum and positive singleton lower bound; `OPT ≤ rmax`. Needed by scale and FPTAS arguments.

## Numbered claims and exact dependencies

| Source claim | Mathematical obligations | Algorithmic / external obligations |
|---|---|---|
| **Theorem 1, Exact sales-space formulation** (79–88; proof 167–197) | denominator tilt forward and reverse; caps; rank; BMS and objective equivalence; true feasible-set surjectivity | A constructive decomposition of every rational uniform-matroid point into O(n) legal sets, rational probabilities, and polynomial bit/operation bounds. Assuming a decomposition does not prove this theorem. |
| **Theorem 2, Exact complexity** (92–94; proof 276–316) | exact positive-integer Subset Sum reduction; removal of items larger than B; explicit fixed no-instance if none remain; both directions including no-anchor case; optional explicit pair policy | A specified encoding and decision language; Subset Sum NP-completeness; polynomial-time many-one reduction; polynomial-size rational LP certificates (or another verifier proof); actual NP and NP-hardness definitions. A reduction-equivalence lemma alone is not NP-completeness. |
| **Theorem 3, Exact-feasibility FPTAS** (98–100; proof 419–446) | optimum, singleton incumbent, Lemmas 7–9, revenue test, no-positive-profit branch, deleting nonpositive coordinates, acceptance slack, approximation ratio, exact BMS/rank and policy reconstruction | Actual rational grids, rounding and finite DP with reconstruction, polynomial count AND bit lengths of rational arithmetic, `poly(input bits,1/ε)` bound, output policy complexity. An oracle returning a good candidate is not an FPTAS. |
| **Proposition 4, Prescribed-support optimization** (205–232) | Charnes–Cooper equivalence, inverse `s>0`, feasible positive exact support, nonzero optimum, positivity forced by α>0 | The source uses polynomial LP optimization; the implemented alternative proves a specialized polynomial candidate solver instead. Existence of an LP optimum alone would not suffice. |
| **Corollary 5, α=1 fixed-support formula** (234–256) | equal coordinates; positive reciprocal sum; minimum cap and rank bound; strict revenue monotonicity; attainment at stated t | finite computation with exact rational min/sum/division; readily bit-polynomial once encodings established |
| **Proposition 6, Nonrectangular optimal support** (261–273; Appendix 537–581) | exact three-product instance; candidate feasibility/value; all competing supports bounded strictly; uniqueness of support; rectangle obstruction | No external algorithm needed: rational primal/dual certificates suffice. |
| **Lemma 7, Scale range** (330–342) | optimum existence; positive objective; scaling improvement; a cap or rank tight; maximum bounded below by vmin/n and above by vmax | No complexity theorem in lemma itself |
| **Lemma 8, Discretization** (361–369) | existence of predecessor scale grid point; exact downward rounding; options nonempty on active coordinates; coordinate and revenue losses; exact band/cap/rank preservation | finite grid termination, length and rational bit bounds are separate obligations |
| **Lemma 9, MCKP approximation** (384–390) | positive options individually feasible since weight≤1≤K; πmax≤P*; scaled optimum; at most n floors lose nθ; exact capacity | Actual DP recurrence, minimum exact rational weight and predecessors, recovery correctness, state bound O(n²/δ), bit complexity |

## Appendix certificate ledger

- Candidate compact vector `(0,2,12)`, value `928/15`.
- Rational policy: probabilities `34/35` on `{2,3}` and `1/35` on `{2}`; outside sale `1/15`, product sales `0,2/15,12/15`.
- Singleton optima: `195/4`, `160/3`, `896/15`.
- Two-product optima: `355/6`, `1091/18`, `928/15`.
- Full-support optimum `11989/195` at `(21/16,2,63/8)`.
- Dual certificate: `4767*rank + (301/2)*(w3−6w1) + (2455/2)*w2 ≤ 9534+2455`, yielding `686w1+3611w2+491w3 ≤11989`.
- Every northeast rectangle containing products 2 and 3 contains product 1; the optimal support is therefore not such a rectangle.

## Bit-complexity dependencies not hidden by algebraic proofs

1. Binary integer/rational encoding and input-length definition, with ordinary arithmetic operation cost.
2. Rational LP feasibility/optimization and polynomial-bit basic-feasible-point certificates.
3. A formal NP-completeness theorem for positive-integer Subset Sum (or a complete reduction chain).
4. Polynomial-time finite geometric-grid generation: dependence on logarithmic data ratios and `1/δ`, including `log(1/α)`.
5. Products/powers on those grids have polynomial binary length; repeated rational additions/comparisons in DP retain polynomial length.
6. Polynomial-bit sparse probability reconstruction, not merely existence by real convex geometry.

## Current certification status — 2026-10-03 17:32 UTC

This section supersedes every historical checkpoint below. **All nine numbered claims now have accepted source-level statements and
stated computational contracts after independent review.** This is a claim inventory,
not a completion percentage. A coherent final source freeze, whole-project
build and complete-origin axiom/trust audit are still required. Source acceptance
is not a claim that this final release validation has already passed.

| Claim | Current exact Lean evidence | Acceptance and remaining boundary |
|---|---|---|
| **T1** | `Sales.exact_attainable`, `optimization_sparse_policy`, `rational_sparse_policy`; `Decomposition.CostMachine.raw_binary_sparse_decomposition` | Accepted. Real feasible-set/objective/BMS equivalence is unconditional; rational data have actual rational probabilities and at most n+1 atoms. The constructive implementation also has an independently reviewed bit/list polynomial cost. |
| **T2** | `PaperTheoremTwo.fixed_policy_npComplete` and `policy_npComplete` | **Source-accepted after two independent reviews at 17:13 UTC.** The total original randomized-MNL policy language is NP-complete, including numeric alpha=1, K=2. Membership is concrete one-tape NP; hardness uses actual finite deterministic polynomial-clock programs and paid composition. Signed H, malformed rejection and redundant encodings are covered. Targeted endpoint axioms are standard-only; frozen-source whole-project audit is still required. |
| **T3** | `FPTAS.runPolicy_approximation` (FPTASGuarantee.lean); `FPTASCostComplete.binary_policy_fptas`; `FPTASCostCodec.flat_policy_fptas` | Accepted in the explicitly instrumented immutable Boolean/list model. One actual program constructs all grids/fuel, DP, sparse policy and reverse tilt; the flat wrapper includes parsing and emission. Exact feasibility, rational output, linear support, comparison with every real feasible policy, and a literal polynomial in original bit length and ceil(10/epsilon) refer to that same returned output. |
| **P4** | `FixedSupportAmbient.ambient_prescribed_support_serialized` and `runAmbient_original_policy`; underlying `binary_fixed_support_solver` | **Accepted.** Actual ambient catalogue/mask traversal, shape checking, selection, positional labels and raw optimization have one literal polynomial bound in original serialized input length. The same returned value has exact ambient support, real global optimality and original MNL policy meaning. Source A is nonempty; K may exceed its cardinality. Cost model is explicit Boolean/list accounting, not an assumed LP oracle. |
| **C5** | `FixedSupportReal.alpha_one_exact_maximum`, rational `FixedSupport.alpha_one_exact_maximum` | Accepted. Equal coordinates, positive denominator, exact minimum-cap/rank formula and attainment; source strictly positive data and nonempty active set retained. |
| **P6** | `Counterexample.global_bound`, `unique_optimizer`, `appendix_table_attainment`, `optimal_support_not_rectangle`; shared-model adapters | Accepted. All seven nonempty support maxima and explicit rational policy arithmetic are exact; every original legal MNL policy is bounded through the actual shared compact model. |
| **L7** | `Optimization.scale_range` | Accepted. Obtains an actual real optimum and the source lower/upper scale range from positive data, alpha in (0,1] and K>=1; does not assume tightness or an optimizer. |
| **L8** | `ApproximationDiscretization.scale_discretization`; `FPTAS.discrete_candidate_exists` | Accepted. Actual finite rational grids with proved horizons, downward rounding, exact band/caps/rank and two-factor revenue bound; source optimum/discrete comparison is composed, not an assumed good grid point. |
| **L9** | `Knapsack.solve_relative_all_selections`; actual `KnapsackCostSolve.solve_decode`/`solve_cost`; FPTAS candidate integration | Accepted. Executed minimum-weight scaled-profit DP with reconstruction; individual option feasibility and max-profit lower bound are discharged by the actual groups. All-zero/nonpositive-profit cases are explicit. |

### Supporting claims and model scope, checked currently

- `Sales.sales_total_probability`, `outside_pos`, `Sales.active_catalog_iff` (ModelFacts.lean)
  and `balanced_iff_max_coordinate` cover the source aggregate-sales identities,
  active-union equality and pairwise/max BMS interpretation. Display cardinality
  is checked per mixture atom; the union may exceed K.
- `Optimization.optimum_exists`/`optimum_positive`, singleton feasibility/value
  and maximum-price bounds supply the optimizer/revenue-grid dependencies.
- Products are nonempty and r_i,v_i positive. K is an integer in [1,n], and
  alpha is in (0,1]. Empty assortments remain legal. Positive output support may
  use repeated assortment labels, which does not increase distinct support.
- P4 explicitly quantifies **nonempty** prescribed A (source lines 205–207).
  Reindexing its active coordinates does not impose K<=|A|: the implemented
  support solver only needs K>0 and therefore covers this source boundary.
- T3's epsilon is rational and strictly between zero and one. Its polynomial
  includes accuracy encoding length and ceil(10/epsilon); it is not polynomial
  only in the numerical data or only in the number of DP states.
- T2 permits an arbitrary signed rational threshold H. Its total language must
  reject malformed data; valid source parameters and fixed alpha/K are separate
  from arbitrary raw certificate soundness and bounded witness existence.

### Empty-domain and support boundaries

- The source product universe is nonempty: K belongs to [n]. `LegalSource`
  requires a positive product count and 1<=K<=n, so domain validation and the
  total decision verifier exclude N=0. The structural `parseSource` function
  may still return such a record; it fails `LegalSource`. This is a domain check,
  not an unproved assumption of a malformed-input theorem.
- The mathematical T1 sales-equivalence and sparse-decomposition statements
  themselves permit n=0. Their zero-dimensional point is implemented by the
  empty display, with zero product sales/revenue and outside probability one.
- P4 expressly assumes nonempty A. The ambient mask preprocessor distinguishes
  empty selection from malformed shape: equal-length all-false masks successfully
  produce an empty selected list, while unequal lengths fail. `runAmbient`
  explicitly rejects empty selected support before calling the positive-support
  backend; its N=0/all-false/mismatch behavior has named theorems. No n>0
  optimality theorem is invoked for n=0. An empty-support optimization convenience
  result would be zero revenue, but it is outside P4's stated quantified domain.
- T3 uses Fin(n+1), hence exactly the source's nonempty universe. Arbitrary
  malformed or zero-product input optimality is not claimed by its legal-input
  FPTAS theorem; all actual parsing/size costs are still included by the flat
  wrapper for inputs satisfying its domain hypotheses.

### Computational-model and trust boundary

The FPTAS, prescribed-support algorithm and decomposition have reviewed explicit
Boolean/list operation counters and concrete raw encodings. These are not
claimed to be external Lean wall-clock bounds, nor silently identified with
`NPMachine.InNP`. The conventional NP chain instead uses real finite
push/pop/jump/choice stack programs, actual transition-count `Run` proofs,
quantitative stack-to-one-tape simulation, and a real composition compiler.

The complete operational Cook–Levin constructor and exact grammar/catalogue/
source-tableau semantics now compose in `StackTableau.np_to_cnf`. Targeted audits
of its compiler, initializer, output program, shape, raw validity and raw
satisfiability use only `propext`, `Classical.choice`, and `Quot.sound`. This
reviewer authored substantial compiler/certificate code; independent review of
that development is delegated to other workers and is not self-certified here.

The prescribed-support final packaging has likewise passed independent review:
its structured raw-input algorithm consumes the actual full catalogue and mask;
its self-delimiting serialization supplies the original size measure. It does
not itself execute a flat malformed-input parser, and that unclaimed interface
must not be inferred from the length bound. Empty support is an explicit error
outside P4's source domain. A separate theorem identifies the returned optimum
with a legal original MNL policy; that policy-existence adapter is not charged
as if the value solver had emitted a complete policy.

No numbered source coverage gap remains at this checkpoint. The open release
obligations are the coherent complete build, frozen-source independent audit,
complete-origin transitive axiom verification, trust-zero replay and hashes.
The historical notes below record earlier states and must not be read as the
current open-obligation list.

### Concrete NP foundation checkpoint (2026-10-03 13:35 UTC)

- Compiled: concrete finite NDTM polynomial-clock definition; exact finite-window
  tableau equivalence; explicit ordinary CNF with one global transition choice
  per time; unconditional `CookLevinCorrect.tableau_satisfiable_iff_acceptsWithin`.
- Independently audited by the CNF/3CNF worker: no weakening in tape, head,
  transition, initial-state, accepting-padding, or zero-time semantics.
- Compiled size infrastructure: actual polynomial clause count and variable-label
  range. This is not yet a polynomial-time reduction theorem.
- Still open for Theorem 2: charged Cook–Levin generation/serialization, generic
  computation-to-machine simulation, and composition with the source decision
  encoding. Full source NP-completeness remains unaccepted.

### 2026-10-03 14:30 UTC: executable Cook–Levin map

The actual raw binary constructor now has unconditional correctness:
`CookLevinRawCorrect.constructBits_correct`. Binary address circuits and
structural lists construct every CNF clause; no decoded-natural loop bound is
used. `CookLevinClockFuel` constructs the polynomial clock fuel by an actual
finite unary-list expression, scanning the original input and proving exact
length and polynomial cost. `np_has_explicit_cnf_map` composes these semantics
from every concrete clocked NDTM NP language.

`CookLevinRawBudget.constructBits_cost` now includes every constructor stage,
catalog deduplication, and binary framing, with a natural arithmetic budget
containing only polynomial operations in original input length and clock length.
The final `Polynomial ℕ` representation/composition proof is currently checking.
The CNF worker independently reviewed the raw boundary: immutable list sharing
and explicit spine copying are consistent with the source cost model. Operational
lowering must still account for copying payload bits on a finite-stack or tape
machine. Source NP-completeness therefore remains open, rather than being inferred
from the instrumented functional cost model.

### 2026-10-03 14:36 UTC: polynomial Cook–Levin bit/list map compiled

`CookLevinPolynomialCost.np_has_polynomial_bit_cnf_map` now compiles. For every
language in the concrete NDTM definition `NPMachine.InNP`, it constructs a fixed
machine constant record and finite clock-expression program whose executable
`reduceMachine` takes the original Boolean input string. The theorem proves both
encoded-CNF membership equivalence and an actual `Polynomial ℕ` upper bound on the
complete instrumented cost in original input length. The earlier raw-constructor
cost and polynomial-reification gap is closed.

The still-open distinction is operational: this is a polynomial-cost persistent
bit/list program. Its lowering to finite-stack bytecode and simulation by the
concrete NDTM/tape model must be proved before the source NP-hardness and
NP-completeness labels are accepted. No new complexity class or oracle is used
as a substitute for that bridge.

### 2026-10-03 15:02 UTC: operational polynomial clock compiler

`CookLevin.StackClock.every_polynomial_clock` now returns a genuine
`NPStack.PolynomialProgram` for every natural-coefficient polynomial clock.
`NPStackStructured` lowers sequence, pop branches, and while-pop loops into
finite primitive control graphs with exact transition counts. Atomic subroutines
carry explicit finite primitive instruction tables and actual `Run` proofs.
Static natural register names are restricted to `Fin N`, with N determined by
the fixed finite code table. `compile_exec` additionally preserves the original
input and clears allocated work registers. Thus the clock front end's operational
lowering is closed; the complete Cook–Levin clause constructor lowering is still
in progress.

Source-boundary recheck requested by parent: official Proposition 4, TeX lines
205–207, explicitly quantifies prescribed **nonempty** active sets. The exact
fixed-support solver's positive support cardinality premise matches this scope.
An empty-support convenience wrapper is not a missing Proposition 4 obligation.

### 2026-10-03 15:31 UTC: operational positive Subset Sum to source BMS link

`NPStackSourceReduction.program` is a fixed finite Boolean-stack transducer.
`NPStackSourcePolynomial.polynomialReduction` packages its actual deterministic
code, all-input `Run`/output theorem, and a literal cubic `Polynomial ℕ` clock.
`positiveSubsetSum_reduces_source` is a `PolyManyOne` theorem between the total
serialized `PositiveSubsetSumLanguage` and the exact signed-field
`ComplexityTimeSourceParsing.SourceLanguage`. The quantitative stack-to-one-tape
compiler is the separately proved `NPStackCompile` dependency.

This operational reduction is a proved alternative implementation of the
paper's hardness gadget: it retains all positive integer items instead of first
deleting oversized items. `ComplexityReal.compact_reduction_iff` already proves
soundness and completeness for every positive item, without requiring a_i <= B.
`ComplexitySourceModel.model_correct` transports that exact real model to the
actual signed verifier schema and indexed product list. The original prescribed
oversized-item preprocessing/fixed-no reduction remains proved separately.
No input promise was silently strengthened or weakened: zero targets, zero
items, missing target fields, malformed framing, and empty item lists all map
to one fixed legal source no-instance. Oversized positive items remain legal.

The transducer executes raw field parsing, binary normalization/positivity tests,
3B/5B seed arithmetic, binary product counting, every item price computation,
six-field signed product serialization, fourteen header/anchor fields, and output
cleanup on failure. Prepending records reverses item order; the exact list-subset
and coordinate-reindexing proofs discharge this ordering change. The fixed no
output is the legal two-product model B=1 with item list [2].

`reductionSpec_legal` additionally proves that every emitted word parses to a
legal source instance. Full source NP-completeness still requires the remaining
operational Cook–Levin/3CNF/Subset-Sum links and source-verifier membership chain;
this one link alone does not assert that final complexity result.

### Operational NP foundation checkpoint (2026-10-03 16:38 UTC)

The Cook–Levin constructor has advanced beyond instrumented bit/list cost:
`StackTableau.tableauPolynomialProgram` is now a genuine finite, NoChoice
Boolean-stack program with proved polynomial-clock primitive execution from the
original input bit string. Physical clock/window/catalog fuel generation and
all scalar initialization are included. Exact schema-to-CNF/tableau semantic
composition and catalogue validity are the remaining local Cook–Levin boundary;
the whole source NP result additionally requires the other operational
reductions and decision verifier to compose. No conditional semantic premise is
being presented as a completed Cook–Levin or source NP-completeness theorem.

## 2026-10-03 17:09 UTC: operational 3CNF → positive Subset Sum and fixed source parameters

`NPSATStackPolynomialReduction.three_cnf_reduces_positiveSubsetSum` now compiles as an unconditional `NPStack.PolyManyOne` between the existing total serialized languages. The code is an explicit finite Boolean-stack program, followed by the proved finite clock generator, physical timeout, and fixed-no emitter. The source-time polynomial is in the original encoded input length. It includes raw field parsing, sparse catalogue validation, a finite three-literal clause guard, physical copies, actual equality comparisons, digit scans, constant-ten multiplication/addition, all item loops, target/slack generation, and wire serialization. The zero-dimensional valid input has a physical fixed-positive-yes patch. Every malformed/invalid input has a rejecting execution before timeout, and all accepting executions have the specified output.

Numeric representation differences are explicit: the prepared catalogue is reversed; emitted items are reversed; clause occurrence digits are canonical 0–3 while the older functional constructor can retain padding. `NPSATStackGadgetSemantics` proves equality of decoded target and indexed item lists with the reviewed Subset Sum gadget. Empty clauses, short clauses, repeated literals, sparse large labels, padded labels, and duplicate item values remain covered.

Key operational modules: `NPSATStackThreeCheck`, `NPSATStackPack`, `NPSATStackVariableColumns`, `NPSATStackClauseDigits`, `NPSATStackClauseColumns`, `NPSATStackItemCorrect`, `NPSATStackVariables`, `NPSATStackZeroColumns`, `NPSATStackTokens`, `NPSATStackVariableTokens`, `NPSATStackSlackLoop`, `NPSATStackSlackEmpty`, `NPSATStackGadgetComplete`, `NPSATStackPrepareCorrect`, `NPSATStackReductionSuccess`, and `NPSATStackPolynomialReduction`. The top-level semantic function is only the proved specification of the finite program; it is not an instruction or oracle in that program.

`ComplexityTimeSourceParsing.FixedSourceLanguage` now means the full legal source language with **numeric** capacity 2 and rational balance parameter 1, retaining all redundant encodings. `NPStackSourceReduction.reductionSpec_parameters` proves this parameter property and legality on every output, including malformed-input/fixed-no branches. `positiveSubsetSum_reduces_fixedSource` is the actual finite-program hardness link to this exact restricted language. The final NP-completeness composition and independent release review are separate top-level integration steps.
