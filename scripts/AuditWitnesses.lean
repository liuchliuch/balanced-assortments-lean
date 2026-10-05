import Audit.Solutions
import Lean.Util.CollectAxioms

/- Check every declaration originating in the proof-witness module. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  for (name, _) in env.constants.toList do
    let some origin ← Lean.findModuleOf? name | continue
    if origin == `Audit.Solutions then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Disallowed witness axiom {ax} in {name}"
      checked := checked + 1
  unless checked == 36 do
    throwError "Unexpected proof-witness inventory: {checked}"
  logInfo m!"PASS: {checked} Comparator witnesses; only standard axioms."
