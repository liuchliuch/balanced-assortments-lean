# Independent P4 ambient adapters and one-tape output review

## Fixed-support source semantics

The source proposition explicitly prescribes a nonempty active set A. `FixedSupportAmbient.binary_ambient_solver` and `binary_indexed_ambient_solver` solve precisely this problem in an arbitrary finite ambient catalog. The selected coordinates are not confused with the ambient catalog: the indexing is a bijection onto A; `extend`/`extendIndexed` is zero outside A; `Realizes` ties the actual returned raw vector and cached objective to its candidate. Positive revenues, attractions, alpha, and capacity, with alpha≤1, ensure every coordinate in A is strictly positive. Optimality quantifies every real feasible ambient vector with exact support A, not merely rational competitors or supports contained in A.

The compact solver admits any positive rational capacity. The policy interpretation specializes to integral K, as required for per-display cardinality. `optimal_original_policy` and `certified_original_policy` use the original MNL denominator and aggregate balance, preserve exact active support and value, and compare every finite randomized original policy on A with arbitrary real probabilities. The returned compact optimum is rational; the policy theorem here packages existence of a real-valued sparse distribution. It does not itself claim that `runAmbient` emits serialized policy probabilities. Rational constructive reconstruction is a separately established sales/decomposition result.

## Actual selection, indexing, and size

`FixedSupportAmbientPreprocess.selectProducts` physically scans the product list and mask together and rejects unequal lengths. Selected records retain their original order. `labelProducts` assigns consecutive bounded positions by one structural successor per record. Its cost conservatively charges each successor by its bounded unary magnitude; the positions are at most the physical input length, not unbounded data labels. `prepared_restriction` establishes the exact bijection from generated positions to the true mask entries and identifies each selected payload with its ambient product. No free selection oracle, externally guessed correspondence, or sparse-label magnitude drives the executable loop.

`FixedSupportCostInputSize` counts both signed numerator components, every denominator, every product, and the scalar inputs. It derives all intermediate width premises rather than assuming a free B. `FixedSupportCostSerializedInput` gives exact self-delimiting bit lengths and parser roundtrip; product indices are implicit positional labels, correctly absent as arbitrary extra integer payload. `prepared_inputVolume` bounds the selected input by the full ambient payload plus mask. The actual `runAmbient` combines preparation with the unchanged raw solver and charges both. Its polynomial bound includes shape-error and empty-selection branches.

Empty ambient input, empty A/all-false masks, and mask-length mismatch are explicit `none` results in `runAmbient`. This matches the source proposition's nonempty-A scope, rather than asserting an optimum for an excluded input. Other mathematical validity hypotheses remain explicit; the wrapper is not a full semantic-domain validator.

The computational model is the charged raw signed-bit/list program, including bounded positional-label work. Neither these adapters nor the generic output simulation silently establishes a finite-stack lowering of the whole fixed-support solver. A serialized-length bound and framing roundtrip alone should not be described as a flat-input parser execution by `runAmbient`.

## Named one-tape output bridge

`NPPolynomialOutputSimulation.Compile.run_output_complete` was independently compared with the compiler's initializer and forward simulation. It physically initializes from the original raw Boolean input, restores its source order through the temporary track, lifts the actual source Run, and preserves the entire represented stack store through the core microsteps. The finite-symbol coding is injective. `decodedSymbol` is solely a proof-side inverse on a fixed finite alphabet, not a semantic runtime instruction.

`PolynomialProgram.one_tape_output` instantiates that actual numbered one-tape machine, includes initialization and simulation overhead in `clockPolynomial`, and proves an accepting Run ending with head zero and every designated output-track cell exactly `(f bits).reverse[j]?`. This is exact encoded bottom-to-top output, including the end-of-word cells. It is not only a recognizer theorem. It expressly makes no claim of cleanup into an isolated plain-output tape; that convention remains explicit and adequate for the named result.

## Verification

Reviewed proof modules remain unchanged. Targeted standard-axiom checks are recorded in `p4-ambient-output-axioms.log`. Final ambient serialized-input packaging is checked in the addendum below when its endpoint is available.

## Final ambient endpoint addendum

Accepted `FixedSupportAmbientComplete.runAmbient_correct` and `ambient_prescribed_support_polynomial`: the concrete original mask is the executed input, the selection-to-A equivalence is proved afterwards, the solver output and its cached revenue are unchanged, and all-real exact-support global optimality is retained. The single polynomial includes actual preparation plus backend cost in original ambient volume.

Accepted `FixedSupportAmbientSerialized.runAmbient_polynomial_serialized`: `serializedAmbient` frames the entire supplied mask plus alpha, capacity, and every ambient product's signed rational components. Its exact length dominates ambient volume, including unselected products and arbitrary padding. Monotonicity of natural-coefficient polynomial evaluation transfers the complete preparation/backend bound to that original concrete bit length. `serializedAmbient_parses` proves exact framing roundtrip. The statement expressly retains the structured-input runtime boundary; it does not charge an unexecuted flat parser or imply one was executed.

Fresh endpoint and boundary axiom checks passed with only standard Lean axioms. No missing packaging remains for the stated P4 structured binary/list solver on prescribed nonempty A, measured against original ambient serialization. The original-policy bridge is exact semantic interpretation, and the named one-tape transducer bridge is exact encoded-track simulation; neither expands the other theorem's interface.

## Final determinism and combined-corollary gate

Accepted `NPPolynomialDeterministicSimulation.Compile.machine_deterministic` and `PolynomialProgram.one_tape_deterministic`. `NPMachine.Deterministic` is global uniqueness of the successor configuration for two arbitrary Steps from the same configuration. The proof bounds every local action list by one, including all initializer states, lifted reversal states, push/pop traversal states, and return states, under the actual source `NoChoice` predicate. The finite-table argument uses source-state and symbol-code injectivity to identify applicable rules. It needs no reachability invariant or accepted-run assumption. The machine is definitionally the same `Compile.machine` used by `one_tape_output`; no replacement transducer or changed output convention is introduced.

Also accepted the final named P4 corollaries `FixedSupportAmbientEndToEnd.ambient_prescribed_support_serialized` and `FixedSupportAmbientOriginalPolicy.runAmbient_original_policy`. The former combines the reviewed exact returned solver result and uniform original serialized-input cost; the latter uses the very same returned cached value, with an explicit numeric equality between rational capacity and natural K, to state optimality over all original real randomized MNL policies on A. Its policy existence is explicitly mathematical interpretation of the value solver, not an assertion of uncharged emitted policy output.

Fresh type/axiom audit of all five new endpoints passed; only `propext`, `Classical.choice`, and `Quot.sound` occur. No source-module edits were made. Final gate accepted.
