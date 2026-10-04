# Publication verification

The original mathematical source, toolchain and dependency pins are unchanged.
The final source distribution recorded complete compilation, originating-module
transitive axiom inspection and replay through the pinned Lean kernel. The
historical evidence is `certificates/final-verification.json`, its final build/regression reports and the referenced source-review reports.

Publication changes are documentation, removal of redundant intermediate logs
and snapshots, and a portable verification entry point. The original frozen
inventory is retained unchanged under `docs/release-candidate/`; it describes
the historical distribution, including its original documentation and compiler
binary. `verify_publication.py` compares every mathematical Lean file and the
three pinned configuration files to that inventory, verifies the compiler commit
and clean dependency revisions, then reruns the full build, origin audit and
regressions. It writes current results under the ignored `.lake/publication/`.
It does not replace historical failed or partial runs with a successful record.

The retained reports identify historical snapshot archives and diagnostic logs
that are omitted from this source repository. Current diagnostics are regenerated
by the verification command. Original paper and cited-source text is unmodified;
author acknowledgements in those manuscripts are part of the original source.

The kernel replay uses Lean itself and pinned dependency artifacts. The source
correspondence reports and paper ledger describe the mathematical model and
its explicit computational scope. An official Comparator run is not claimed
for this release. GitHub Actions runs the portable full verification command.

The older `snapshot.py --verify` and freeze/checkpoint helpers reproduce the
original distribution's exact machine and documentation inventory; they are
historical tooling. Use `verify_publication.py` for the published distribution.
