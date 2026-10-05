# Cardinality-Constrained Randomized Assortments with Balanced Market Share in Lean

[![Lean verification](https://github.com/liuchliuch/balanced-assortments-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/liuchliuch/balanced-assortments-lean/actions/workflows/lean.yml)

Lean 4 formalization of the [paper by Xiaotie Deng, Hanyu Li and Chenghua Liu](https://arxiv.org/abs/2609.35802v1).
The library covers all nine numbered results, including sparse policy reconstruction, NP-completeness and the FPTAS. See the [paper correspondence](docs/PAPER_CORRESPONDENCE.md) for exact entry points and the [formal model](docs/MODEL.md) for input domains and computational scope.

## Build

Install [Elan](https://github.com/leanprover/elan), Python 3 and Git, then run:

```sh
lake exe cache get
lake build
```

Lean 4.24.0 and all mathematical dependencies are pinned. To rebuild the project, audit the transitive axioms of every originating declaration and rerun the regression checks:

```sh
python3 scripts/verify_publication.py
```

## Review statements and proofs

[`Audit/Statements.lean`](Audit/Statements.lean) fixes 36 proposition types; [`Audit/Solutions.lean`](Audit/Solutions.lean) supplies their proofs. Both use the same fixed mathematical model. The [official Lean Comparator](https://github.com/leanprover/comparator) checks the complete types, permitted axioms and a fresh Lean kernel replay. Linux CI also checks that added premises and unexpected axioms are rejected.

```sh
python3 scripts/compare.py
```

The default mode requires Linux, the pinned Landrun executable and a user systemd session. See [Comparator setup and scope](docs/COMPARATOR.md) and [verification](docs/VERIFICATION.md).

## Repository contents

- `BalancedAssortments/`: mathematical definitions, algorithms and proofs.
- `Audit/`: fixed proposition interfaces, proof witnesses and negative controls.
- `docs/`: paper correspondence, model and verification instructions.
- `paper/`: the original versioned paper and source checksums.
- `verification/`: mathematical source provenance.

Use [`CITATION.cff`](CITATION.cff) to cite the paper. A software license has not been selected.
