import HRTorus.Fermion.Pilot.CAR
import HRTorus.Fermion.Pilot.JW
import Lean.Util.CollectAxioms

/-! The axiom check of the two pilot modules (`HRTorus.Fermion.Pilot.JW`, `HRTorus.Fermion.Pilot.CAR`). For every non-internal constant defined in the
named module (theorems, definitions, structures and their projections, instances), the axioms it
depends on, and a count of those with any axiom outside `[propext, Classical.choice, Quot.sound]`. -/

open Lean Elab Command

elab "#module_axioms " mod:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod.getId | throwError "module {mod.getId} not found"
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut names : Array Name := #[]
  for (c, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? c == some idx && !c.isInternal then
      names := names.push c
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut nonstd : Nat := 0
  let mut sorried : Nat := 0
  for c in names do
    let axs ← liftCoreM <| collectAxioms c
    unless axs.all (fun a => std.contains a) do nonstd := nonstd + 1
    if axs.contains ``sorryAx then sorried := sorried + 1
    logInfo m!"{c} : {axs.toList}"
  logInfo m!"SUMMARY {mod.getId}: {names.size} declarations; {nonstd} with an axiom outside [propext, Classical.choice, Quot.sound]; {sorried} depending on sorryAx"

#module_axioms HRTorus.Fermion.Pilot.CAR
#module_axioms HRTorus.Fermion.Pilot.JW
