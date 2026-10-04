# Direct polynomial prescribed-support solver

## Current status — 2026-10-03 17:32 UTC

The specialized solver is implemented and individually compiled. It is a proved
alternative to the paper's general-LP argument, not a proposed or assumed
optimization oracle. `FixedSupportAlgorithmCorrect` proves feasibility,
optimality against every real feasible vector, and strictly positive output on
the nonempty prescribed index set. `FixedSupportCostCertified` binds those
properties to the actual raw signed-bit `runBits` output and its polynomial
bit/list counter and output-width bounds.

`FixedSupportCostInputSize.runBits_polynomial_input` now derives the uniform
width from every original stored numerator/denominator bit and product record.
`FixedSupportCostSerializedInput.runBits_polynomial_serialized` bounds that same
program by one literal natural polynomial in the length of a concrete
self-delimiting signed-rational encoding. The encoding's field parser roundtrip
is proved. This is a runtime specialization for the already structured raw
solver, not a claim that `runBits` itself parses arbitrary malformed bitstreams.

The exact ambient nonempty-subset/reindexing/zero-extension and original-policy
mathematical adapters now compile in `FixedSupportAmbient*`. The actual
`FixedSupportAmbientPreprocess.runAmbient` additionally scans the full physical
catalogue and Boolean support mask, checks matching lengths, selects records,
constructs canonical positional labels, and invokes the raw solver. Selection,
reindexing and backend cost compose into one literal polynomial in the original
ambient serialized input length, including every raw fraction bit and mask bit.
The wrapper returns an explicit error for a mismatched mask or empty selected
support. It does not invoke the nonempty-support optimality theorem at n=0.

The final combined theorem `ambient_prescribed_support_serialized` and the
original-policy value theorem `runAmbient_original_policy` are compiled and
have passed independent review. The final coherent release build/audit remains
pending. Source K may exceed the prescribed support size; the
solver permits every positive K and does not add K<=|A|.

The computational contract is the reviewed explicit immutable Boolean/list
cost model. No external Lean wall-clock or machine-compiler theorem is asserted
for this solver. No general rational-LP polynomial-time theorem is imported.

## Mathematical construction and implemented alternative

The construction preserves the source's positive rational data, nonempty
prescribed support, positive alpha<=1, and positive budget (hence source K>=1).

Restrict to the m active coordinates. Introduce a common lower scale t and increments y_i by w_i=t+v_i y_i. For t in [0,T], where T=min(min_i v_i, K/sum_i(1/v_i)), feasible increments satisfy
- 0≤y_i≤c_i(t)=min(1,t/(alpha v_i))−t/v_i
- sum_i y_i≤B(t)=K−t sum_i(1/v_i).
This gives exactly the closed balanced polytope (including the zero vector). Nonzero feasible points have t>0 and hence exact prescribed support.

For a target rho, maximizing sum_i(r_i−rho)w_i becomes a baseline linear term in t plus continuous knapsack with scores a_i(rho)=(r_i−rho)v_i. The optimal increments greedily fill positive-score coordinates in descending score order. Only O(m²) order/sign changes occur as rho ranges over [0,rmax], at pairwise affine-score intersections and zeros rho=r_i. The implementation chooses feasible crossing points and midpoints of all pairs of crossing points (including 0,rmax), a polynomial superset of the adjacent-interval representatives. Every possible target has a sampled compatible weak order/sign pattern; ties and zero-score increments may be assigned either neighboring pattern without affecting the target linear objective.

For each sampled order/sign pattern and each attraction-cap interval between t=alpha v_i, every c_i(t) is affine. Greedy fill changes form only when B(t)−sum_{i in prefix}c_i(t)=0. If C is the capped part of a prefix, the residual is
K−|C|−t*(sum_{i outside prefix}1/v_i + (1/alpha)*sum_{i in prefix\C}1/v_i).
The denominator is nonnegative. Include every root with positive denominator lying in the relevant cap interval and [0,T], plus the endpoints of that interval. If the denominator is zero, the residual is constant and introduces no root. The resulting set has polynomial size. The implementation uses scoreCount=pointCount+pointCount² with pointCount=m²+m+2, and scaleCount=(m+2)², hence a conservative O(m^6) candidate bound.

For each candidate, compute the rational greedy allocation and actual fractional revenue; choose the best. For an actual optimum rho*=F(w*), choose a sampled compatible score pattern. At its original t, greedy cannot lower transformed profit. The transformed profit as a function of t is continuous piecewise affine, so one enumerated feasible endpoint attains at least that value. Its transformed profit≥rho* implies its fractional revenue≥rho*, hence it is optimal. Positive sufficiently-small all-active baseline value excludes the all-zero candidate and enforces t>0.

## Proof ledger

Items 1–6 below are implemented and individually compiled. The initial finite-endpoint argument and raw pipeline have independent reviews; item 7 now has accepted ambient packaging and independent source review, with the final frozen-source verification gate still pending.

Original proof obligations:
1. Exact scale/increment equivalence and positive-support argument.
2. Actual continuous-knapsack greedy correctness, including nonpositive scores and ties.
3. Polynomial sample construction covers all score/sign regimes, including coincident affine functions and endpoint ties.
4. Exact piecewise-affine breakpoint coverage and endpoint maximum.
5. Executable rational candidate enumeration, recovery and objective correctness.
6. Binary input/output size and actual bit-operation polynomial cost, including sorting and ratios.
7. Independent source-semantic review; no general LP oracle or unexplained finite enumeration may replace these proofs.
