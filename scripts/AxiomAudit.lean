import BalancedAssortments
import Lean.Util.CollectAxioms

/- Audit by originating project module, not declaration namespace. This includes
private/generated declarations and any declaration placed in another namespace.
Each declaration's full transitive axiom closure is checked. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  let mut origins : Array Name := #[]
  let mut closure : Lean.CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    let some origin ← Lean.findModuleOf? name | continue
    if (`BalancedAssortments).isPrefixOf origin then
      if !origins.contains origin then origins := origins.push origin
      -- Reuse the standard Lean visitor state across roots. Its visited set
      -- traverses the UNION of every root's full dependency closure once.
      let (_, next) := ((Lean.CollectAxioms.collect name).run env).run closure
      closure := next
      let axioms := closure.axioms
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Disallowed transitive axiom {ax} in {name}, originating in {origin}"
      logInfo m!"origin={origin}; declaration={name}; cumulative_transitive_axioms={axioms}"
      checked := checked + 1
  logInfo m!"AUDITED PROJECT MODULES: {origins}"
  logInfo m!"PASS: origin-complete audit of {checked} project declarations in {origins.size} modules; only propext, Classical.choice, Quot.sound."
