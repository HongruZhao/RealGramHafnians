import RealGramHafnians
import Lean.Util.CollectAxioms

/-!
Copyright (c) 2026 Hongru Zhao. Released under Apache 2.0; see LICENSE.

This check fails if either public theorem depends on an axiom other than
Lean's standard logical foundations. In particular, no project axiom,
admitted theorem, or native-decision oracle is permitted.
-/

open Lean Elab Command

run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``RealGramHafnians.theorem2_1, ``RealGramHafnians.theorem2_3] do
    let axioms ← Lean.collectAxioms decl
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{decl}: unexpected axioms {unexpected}"
    logInfo m!"PASS {decl}: {axioms}"

#print axioms RealGramHafnians.theorem2_1
#print axioms RealGramHafnians.theorem2_3
