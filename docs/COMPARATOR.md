# Official Comparator

The repository uses [leanprover/comparator](https://github.com/leanprover/comparator), pinned to `97ef939c9fe3f8abf93e4adb654517476da7a66f` for Lean 4.24.0. The exporter, replay library and sandbox revisions are recorded in [`Audit/toolchain.json`](../Audit/toolchain.json).

## Interfaces

[`Audit/targets.json`](../Audit/targets.json) maps 36 full proposition types to the paper and proof declarations. [`Statements.lean`](../Audit/Statements.lean) contains goal specifications, with intentional `sorry` placeholders; [`Solutions.lean`](../Audit/Solutions.lean) contains proved witnesses and imports only the mathematical library. Default builds and the proof axiom audit include the solutions. Statement placeholders and deliberately invalid controls are separate targets.

The types are fixed in source and include all binders, assumptions and conclusions. Most supporting interfaces were transcribed from the reviewed source declarations; this is a check that their proof witnesses satisfy those interfaces. Paper correspondence and model interpretation still require mathematical review. The underlying models, decision languages, programs and cost definitions have their original fixed bodies and are never replaceable Comparator holes.

## Checks

The official tool compares the full statements, enforces the axiom policy (`propext`, `Classical.choice`, `Quot.sound`) and replays the exported solution in a fresh Lean 4.24.0 default kernel. This uses Lean's kernel implementation. The optional external Nanoda kernel is disabled.

Two isolated negative controls are mandatory: `NegativePremise.lean` adds a `False` premise; `NegativeAxiom.lean` uses an extra axiom. Verification succeeds only when the positive solution is accepted and both controls are rejected for their intended reasons.

The wrapper freezes all source, audit, checking-script and configuration hashes before execution and rechecks them afterward. It also verifies mathematical dependency revisions, clean tool checkouts and checking executable hashes.

## Linux sandbox

After fetching the pinned mathematical dependencies, install Go 1.24 and the pinned Landrun revision:

```sh
go install github.com/zouuup/landrun/cmd/landrun@811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
export PATH="$(go env GOPATH)/bin:$PATH"
systemctl --user is-active default.target
python3 scripts/compare.py --jobs 2
```

A functioning user systemd session is required. GitHub CI enables user lingering and starts that session. The official tool uses Landrun for child builds and exports; the outer systemd unit restricts Unix-domain sockets. Comparator and exporter binaries are built in a separate cache outside the project's writable `.lake` directory. `COMPARATOR_HOME` may select an existing clean pinned checkout there.

## Local development

```sh
python3 scripts/compare.py --local --jobs 2
```

This runs the same official type, axiom, kernel and negative-control checks with process isolation explicitly disabled. Its report identifies that mode. Linux CI is the sandboxed check.

Reports and complete child logs are written to `.lake/comparator-results/` and retained as GitHub Actions artifacts.
