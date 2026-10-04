# Final independent Theorem 3 source review

Reviewed against the vendored paper, Theorem 3, Algorithm 1, and the scale-range, discretization, and MCKP lemmas (Lemmas 7–9). Verdict: accepted on the paper's stated domain, in the explicitly instrumented binary/list operation model.

## Exact supported domain

There are N = n+1 ≥ 1 products, with positive rational revenue and attractiveness; 0 < alpha ≤ 1; integer 1 ≤ K ≤ N; rational 0 < epsilon < 1. These are precisely the model and algorithm preconditions in the paper. `FPTAS.Valid` and `flat_policy_fptas` state them explicitly. The arbitrary parsed input may use unreduced numerator/denominator bit lists and redundant high zero bits. Each denominator must decode positively. The original flat input length includes all such bits, all framing, epsilon, alpha, K, and every product.

The theorem does not cover empty product lists, zero capacity, K>N, zero/negative revenues or attractions, alpha outside (0,1], epsilon outside (0,1), or zero denominators. No extension to these cases is implicitly asserted. The parser is a framing/record parser, not a mathematical-domain validator. Malformed framing or incomplete product records returns `none`; a well-framed but mathematically invalid input can enter the total implementation, without the FPTAS guarantee or the valid-input polynomial bound.

## Mathematical chain

`Optimization.scale_range` supplies a real attained optimum and the exact alpha*vmin/N to alpha*vmax scale bounds. Positivity and K≥1 are discharged from the original valid input. `ApproximationDiscretization.scale_discretization` rounds the real scale and real coordinates to actual rational geometric options, retaining caps and rank by coordinatewise decrease and giving the squared multiplicative revenue loss. `FPTASOptimal.discrete_candidate_exists` ties these witnesses to the executable grids.

The actual profit-scaled multiple-choice solver retains zero options, removes nonpositive transformed profit, uses theta=delta*pmax/N and floor scaling, and retains minimum exact weight by scaled-profit class. Every option weighs at most one; K≥1 makes pmax individually feasible. `ApproximationCandidate.candidateAt_success` connects the solver's returned state to the exact unrounded revenue test. `FPTASGuarantee.runSales_approximation` composes both grids, the singleton alternative, the (1-delta)(1+2delta) acceptance margin, and delta=epsilon/10. Its comparison quantifies every feasible real compact-sales vector, not merely rational competitors.

## Actual input/output and bit boundary

`runSalesBits` constructs counts, delta, min/max/singleton seeds, both outer grids, every option group, maximum profit, scaling, DP cutoff, candidate acceptance, and incumbent comparison internally. Binary arithmetic uses finite bit lists and unreduced rational pairs. Grid and DP iteration consume physically constructed token lists, including charged binary-to-unary fuel construction. No user-supplied horizon, width, DP bound, or oracle for an optimum appears in `flat_policy_fptas`.

`runPolicyBits` computes marginals, runs binary sparse decomposition, and reverses the denominator tilt with exact rational arithmetic. `flat_policy_fptas` proves every returned probability denominator valid, every mask exactly N bits, a normalized nonnegative distribution with each assortment of size at most K, exact aggregate BMS, and at most N+1 atoms. Duplicate masks or zero-weight atoms do not enlarge this linear list bound or invalidate the policy. The flat emitter and decoder recover the very same raw output atoms (`run_decoded`, `emitPolicy_roundtrip`, `run_roundtrip`).

`binary_policy_approximates_original` directly compares the same output with every original legal finite randomized policy having arbitrary real probabilities. Every paper policy is finite because the product universe is finite; all legal assortments can be used as its index type. Composing this theorem with `run_decoded` gives the direct original-policy reading of the flat theorem. The flat theorem itself packages the equivalent universal real compact-sales comparison; there is no missing substantive hypothesis in this bridge.

`run_bounds` bounds parser + algorithm + emitter cost and output length by the actual flat input length and Q=ceil(10/epsilon). `flatPolynomial` is a literal fixed bivariate polynomial over natural coefficients. Since Q≤10/epsilon+1, this is polynomial in original input length and inverse accuracy, including epsilon's own bit representation. Exact rational operations are expanded into charged bit primitives; the result is not merely a count of DP states or unit-cost rational operations.

The proven cost is the explicit instrumented binary/list cost, whose cost component is ghost instrumentation. This package does not additionally instantiate the entire FPTAS as a finite one-tape `NPMachine` execution or certify Lean VM wall-clock runtime. The separately proved finite-machine reduction compiler does not silently supply that absent FPTAS-specific lowering. State the model accordingly.

## Verification

No reviewed proof modules were changed. A fresh targeted Lean axiom audit is recorded in `fptas-final-source-axioms.log`, covering the flat endpoint, original-policy comparison, flat cost/output bound and roundtrip, and the scale/discretization/candidate-success chain. Only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound` occur.
