# Input domains and computational models

The paper's optimization and complexity domain has a nonempty product set, strictly positive rational prices and attractions, `1 <= K <= N`, and `0 < alpha <= 1`. The outside attraction is normalized to one. BMS constrains aggregate purchase probabilities, and each displayed assortment has size at most K; the union of positively weighted assortments can be larger. Empty displayed assortments are legal.

Theorem 1's structural finite-vector equivalence also covers empty product types. The positive-domain optimization and NP languages enforce their own validity predicates. Proposition 4 requires a nonempty prescribed support; K can exceed that support's size. Its ambient preprocessor checks mask/catalogue lengths and explicitly rejects empty selected support.

Revenue thresholds may be signed rationals. The FPTAS accuracy is rational and lies strictly between zero and one. Valid padded and unreduced fractions are allowed. Framing parsers and mathematical validity predicates are separate; the end-to-end FPTAS theorem records successful parsing and valid mathematical data explicitly.

## Algorithm accounting

Sparse decomposition, prescribed-support optimization and the FPTAS use immutable Boolean lists, fraction records and explicit natural operation counters. Costs cover bit arithmetic, traversals, fuel construction, grid generation, dynamic programming, reconstruction and the applicable input/output wrapper. The FPTAS flat theorem bounds its parser, actual policy program and emitter by a polynomial in original input length and inverse accuracy. The prescribed-support theorem covers ambient mask preprocessing and the structured raw solver against the original serialized input length.

The counters are instrumented return-value/cost pairs. Source inspection connects increments to primitive Boolean/list work; these algorithms do not have a separate compiler theorem relating their counters to Lean's wall-clock runtime, heap allocation or garbage collection. Immutable records may share stored bit strings. Mathematical decoding/refinement functions in proof statements specify meaning rather than charged execution.

## NP-completeness

The decision languages are the original randomized MNL policy threshold languages, including fixed numeric `alpha=1` and `K=2`. Membership has a finite one-tape nondeterministic verifier with a polynomial clock. Hardness composes actual finite Boolean-stack programs through Cook–Levin, CNF to 3CNF, positive Subset Sum and the assortment gadget. Quantitative one-tape simulation and output-track preservation are proved within the library.

Some finite control enumerations use classical finite equivalences. The transition relations and polynomial execution witnesses are kernel-proved; a native-VM execution trace for those classical enumerations is not part of the evidence. The permitted transitive axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Prescribed-support proof

Proposition 4 is proved with a specialized polynomial solver. Its candidate enumeration derives from finite score-order changes and scale breakpoints, followed by exact rational reconstruction. Charnes–Cooper equivalence is also proved. See [FIXED_SUPPORT.md](FIXED_SUPPORT.md) for the algorithm and its relation to the paper's general linear-program argument.
