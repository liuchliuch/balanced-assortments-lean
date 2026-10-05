# Reproducible verification

```sh
lake exe cache get
python3 scripts/verify_publication.py
python3 scripts/compare.py --jobs 2
```

The publication verifier checks the frozen production source inventory in [`verification/library-provenance.json`](../verification/library-provenance.json), compiler and dependency revisions. It cleans only this project's outputs, builds the complete mathematical library and Comparator proof witnesses, checks all originating declarations' transitive axioms, re-elaborates regression checks and validates the original paper checksums. Existing Lean audit/regression sources are retained byte-for-byte from the mathematical baseline.

`--no-clean` is available for an incremental local recheck. The report records whether project outputs were cleaned. Reports describe the completed command; they do not confer independent mathematical interpretation of the paper.

The separate official Comparator job compares all fixed proposition types and replays the exported solutions with its negative controls. Details are in [COMPARATOR.md](COMPARATOR.md).

[GitHub Actions](https://github.com/liuchliuch/balanced-assortments-lean/actions/workflows/lean.yml) runs both jobs on Ubuntu 24.04 and retains reports and complete logs. The report's `source_snapshot` binds the tested Lean sources, scripts and pinned configurations; documentation and output logs are excluded so adding verification evidence does not change the tested mathematical inputs.

Earlier mathematical source validation is associated with the baseline commit recorded in `library-provenance.json`. Historical working notes, checkpoint scripts and duplicate prose were removed from this publication. The current commands generate fresh evidence.
