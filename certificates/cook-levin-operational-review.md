# Independent operational Cook–Levin review

Reviewed the concrete finite-stack generation path, its original-input clock,
the typed CNF interpretation, and the final raw catalogue validity theorem.
No semantic or uncharged-operation gap was found in this path.

## Machine and language scope

The source is `NPMachine.Machine`: a fixed finite state set, finite alphabet
with distinct literal input symbols 0/1 and blank 2, and a finite list of
nondeterministic local transition records on an integer-indexed tape.
`AcceptsWithin` counts real transitions from the literal input tape.
Each tableau row has one global transition-choice variable. Its source/read,
write/target, head movement, and off-head preservation clauses all use that
same choice; independent cellwise nondeterministic choices are not permitted.
The extra choice zero is an accepting-state-only stutter. The separately
proved accepting-prefix theorem converts padded runs back to ordinary bounded
runs, so this does not change the recognized language.

The construction is for each fixed machine and fixed natural-coefficient
polynomial clock. Machine-specific table and alphabet loops are finite code
constants; only input-dependent loops use runtime token stacks. This is the
usual per-language Cook–Levin reduction scope, not a uniform promise about
encoding an unbounded machine description as part of the input.

## Actual execution and costs

`StackTableau.tableauPolynomialProgram` is a genuine `PolynomialProgram`.
Its code is the restricted finite-register expansion of `initializeBlock`
followed by the streaming builder compiler. Every atom contains a finite
primitive instruction table and is justified by an actual `Run`; there is no
semantic arithmetic, SAT, length, or recursive evaluation oracle instruction.

Initialization first copies and preserves the raw input, generates physical
unary clocks/window/catalogue fuels with the certified stack-clock program,
clears overwritten input storage, pushes fixed binary machine constants,
and scans real fuel stacks to compute binary scalar counters. The time bound
includes these copies, clears, counts, and all initialization handoffs.

Builder loops pop real copied fuel, increment binary counters by compiled
arithmetic, save and restore lexical indices, and restore private/work stacks.
`compile_exec` proves the whole resulting store differs only in the output
prefix. Its loop-body premises are discharged by structural induction on the
fixed builder; they are not external assumptions. `GoodFuel` prevents scalar,
output, and scratch aliasing. The exact code is restricted to a fixed `Fin N`
register type derived from its finite syntax/table. Thus every stack alphabet
is Bool and every control/register set is finite.

The fixed `timePolynomial` and initialization bound compose as literal
natural-coefficient polynomials in original input length. Output accumulation
prepends fields; no uncharged copying of the growing output is needed.

## Exact CNF and boundary semantics

`program_raw` equates the complete generated wire stream with the existing
CNF encoder of `raw M word T`, including the catalogue and terminators.
Typed clause/formula sequence reversal agrees with the physical prepend
order. `formula_holds` proves assignment-by-assignment equality of truth with
the reviewed mathematical tableau. `raw_satisfiable_iff` therefore refers to
ordinary CNF satisfiability and precisely `AcceptsWithin M word T`.

`raw_valid` is unconditional: the explicit catalogue is a duplicate-free
reversed interval and every emitted literal is bounded by that interval.
This closes the syntactic-legality dependency even for unsatisfiable outputs.
The initial tape partition covers T left blanks, every literal input bit,
and T+1 right blanks. It remains valid for empty input and T=0. The window is
always nonempty. An absent accepting state emits an empty accepting clause.
Out-of-window head movement has no target witness, hence is rejected rather
than silently saturated by natural subtraction.

Kernel-checked regressions in `CookLevinStackAudit.lean` cover empty input and
zero clock, accepting/rejecting machines with no transition rules, a mixed
Boolean input at zero clock, the literal 0/1 order and trailing blank, and the
five-variable smallest catalogue. No admitted result or executable-only test
is used in those regression proofs.

Axiom output is recorded in `operational-stack-axioms.log`; the audited
operational and semantic endpoints use only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms. The source-to-MNL reduction and MNL
membership endpoints must still be assembled separately; this review does not
replace those endpoints with a claim about the tableau generator alone.
