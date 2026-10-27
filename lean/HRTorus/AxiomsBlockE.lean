import HRTorus.LLL.Space
import HRTorus.Assembly.Setting
import HRTorus.Assembly.Inputs
import HRTorus.Assembly.Translation
import HRTorus.Assembly.Main
import Lean.Util.CollectAxioms

/-! The axiom check of block E's five modules (`HRTorus.LLL.Space`, `HRTorus.Assembly.Setting`, `HRTorus.Assembly.Inputs`, `HRTorus.Assembly.Translation`, `HRTorus.Assembly.Main`; Sections 6–8 of the HR paper, with `HRTorus.LLL.Space`, whose last statement block E proved). Run with
`lake env lean HRTorus/AxiomsBlockE.lean` from this directory after `lake build`. For every non-internal constant defined in the named module (theorems, definitions and their auxiliary constants,
instances), the axioms it depends on; a summary line with the count of constants with an axiom outside
`[propext, Classical.choice, Quot.sound]`, the count depending on `sorryAx`, and the names of the latter. -/

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
  let mut other : Array Name := #[]
  let mut sorried : Array Name := #[]
  for c in names do
    let axs ← liftCoreM <| collectAxioms c
    unless axs.all (fun a => std.contains a) do nonstd := nonstd + 1
    if axs.contains ``sorryAx then sorried := sorried.push c
    unless axs.all (fun a => std.contains a || a == ``sorryAx) do other := other.push c
    logInfo m!"{c} : {axs.toList}"
  logInfo m!"SUMMARY {mod.getId}: {names.size} declarations; {nonstd} with an axiom outside [propext, Classical.choice, Quot.sound]; {other.size} with an axiom other than those and sorryAx {other.toList}; {sorried.size} depending on sorryAx: {sorried.toList}"

#module_axioms HRTorus.LLL.Space
#module_axioms HRTorus.Assembly.Setting
#module_axioms HRTorus.Assembly.Inputs
#module_axioms HRTorus.Assembly.Translation
#module_axioms HRTorus.Assembly.Main
