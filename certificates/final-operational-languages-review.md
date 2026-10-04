# Independent final operational-language review

## Reviewed endpoints

- `NPSATStackReduction.three_cnf_reduces_positiveSubsetSum`
- `NPStack.SourceVerifier.Fixed.fixedSourceLanguage_inNP`
- Their exact-language correctness, original-input clocks, bytecode composition,
  and physical timeout/guess/framing wrappers.

No missing legality premise, canonical-representation restriction, free
input-dependent iteration, or clock/body mismatch was found.

## Total 3CNF to positive Subset Sum

The source is `Encoding.ThreeCNFLanguage`: a complete framed raw CNF parse,
semantic catalogue validity, clauses of length at most three, and ordinary
satisfiability. Sparse natural labels are stored as raw binary fields; no loop
is bounded by their decoded maximum. Catalogue uniqueness is numeric, so
padded duplicate labels are rejected. Every literal must belong to the
catalogue. Empty, unit, binary, repeated-literal, and three-literal clauses
are all included in the source language.

The preprocessor's actual finite program parses framing, validates the full
catalogue and formula grammar, checks every clause length, and produces the
preserved formula, reversed catalogue, and binary fresh query. Fresh-query
scans create physical variable/clause token stacks. The gadget enumerates
actual catalogue positions, emits both truth-choice items, counts literal
occurrences with finite control, creates two slack items per clause, and
constructs target digits. Every integer is built by compiled bit-list
multiplication/addition and emitted by a real framing program. Explicit
relocations and three paid copies link preparation to construction.

`successWire_fields` proves the literal output grammar. `actualItems_value`
and `targetBits_value` transfer to the reviewed base-ten gadget. Reversing
item order preserves indexed Subset Sum; repeated equal-valued items are not
collapsed. `PositiveSubsetSumLanguage` requires a positive target, positive
items, and an indexed-list sublist whose sum is the target.

Zero variables and zero clauses produce the fixed positive yes-instance via
an actual branch/clear/emitter. A valid empty clause remains unsatisfiable.
Malformed framing, invalid catalogues, illegal formula skeletons, and clauses
longer than three have rejecting source executions and map to the fixed
positive no-instance. The total reduction uses a real generated unary clock,
physical timeout ticks, and paid clearing/fallback emission. `GoodInput` is
used only in correctness proofs, not as an instruction or decision oracle.

`successBudget_bound` uses the original raw wire length, preserving all
padding through `parse_input_eq_encode`. It includes parsing, validation,
fresh generation, token creation, all gadget arithmetic, copies, serialization,
and the empty-instance patch. `Clocked.polyComputable` additionally charges
clock generation, timeout simulation, and fallback on every binary input.
The final `PolyManyOne` matches exactly these two total serialized languages.

## Numeric fixed-parameter NP membership

`FixedSourceLanguage` is precisely `SourceLanguage` conjoined with the same
parsed input having numeric capacity 2 and rational alpha 1. It does not
require canonical bitstrings, an alpha denominator of one, or a particular
signed numerator representation. `fixedSourceLanguage_iff` identifies one
common parse for source legality, source yes semantics, and both restrictions.

The verifier appends actual signed addition and four signed comparisons after
the complete general source verifier. It constructs two as one plus one,
tests capacity equality in both directions, and tests alpha numerator equality
with its denominator in both directions. Whole-verifier legality supplies a
positive denominator, so this is exactly rational alpha=1. Stored header
values and the one-register are preserved through both passes and the scalar
checks. The all-accepting-run factorization cannot bypass the whole verifier
or the final guard.

The fixed guard clock uses actual `Run.stack_length`: its arithmetic registers
start empty, hence each output bit length is at most the preceding primitive
runtime T. The guard costs at most C*(T+1)^2, leading to the literal polynomial
P+C*(P+1)^2+1. The complete branch includes real source parsing, physical
nondeterministic certificate-bit guesses, all verifier instructions, and the
finite-stack to concrete one-tape simulation. Soundness quantifies all
accepting branches, without a hidden clock or certificate-validity premise.

## Boundary and axiom checks

`OperationalLanguageAudit.lean` supplies kernel-checked regressions for raw
empty framing, the zero-dimensional CNF yes-case, semantic duplicate labels
with distinct padded encodings, and the valid empty-clause no-case.
The separate fixed-guard regression module executes the literal arithmetic
instruction graph on padded capacity and unreduced signed alpha encodings.

`final-operational-languages-axioms.log` records the final endpoint and key
bridge axiom audit. Only the standard `propext`, `Classical.choice`, and
`Quot.sound` axioms occur. The review concerns the actual stated raw languages;
user-facing NP-completeness claims must cite the assembled source equivalence
and reduction chain in addition to these two endpoints.

## Assembled Paper Theorem 2 endpoints

The final `PaperTheoremTwo.fixed_policy_npComplete` and `policy_npComplete`
were also reviewed. For an arbitrary `NPMachine.InNP` language, the chain is
its actual Cook–Levin constructor, operational CNF-to-3CNF conversion,
operational 3CNF-to-positive-Subset-Sum conversion, and the operational
Subset-Sum-to-MNL source reduction. `PolyManyOne.trans` uses a real finite
instruction composition, whose clock includes transfer and the second
program's input growth; output length is bounded from primitive stack growth.

`SourcePolicyYes` quantifies a finite randomized distribution over actual
cardinality-feasible assortments and evaluates the original MNL sales,
aggregate balance, and revenue threshold. `sourceYes_iff_policy` is a proved
bidirectional equivalence using policy-to-compact sales and sparse policy
reconstruction under the same source legality assumptions. Consequently the
final rewrites identify entire raw languages, not only gadget instances or
canonical encodings. Both final NP-completeness statements pass this review.
Their transitive axiom closures are included in the audit log.
