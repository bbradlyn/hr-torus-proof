import HRTorus.ZeroModes.Theta
import HRTorus.ZeroModes.Canonical
import HRTorus.ZeroModes.Explicit
import HRTorus.ZeroModes.Lower
import HRTorus.ZeroModes.Formulation
import HRTorus.ZeroModes.Spaces
import HRTorus.ZeroModes.Merge
import HRTorus.ZeroModes.Upper
import Lean.Util.CollectAxioms

/-! T-0056 stage F, blocks F1-lower and F1-upper (2026-10-26): the axiom check of the eight `HRTorus.ZeroModes.*` modules
(Appendix C of the HR paper — Theorem 2.10 — and the unconditional forms of Theorem 8.1, Corollaries 8.2 and 8.4). Run with
`lake env lean HRTorus/AxiomsBlockF.lean` from this directory after `lake build` (the method of `AxiomsBlockE.lean`, unchanged:
L11's, from L10's, L9's, L8's and L7's). For every non-internal constant defined in the named module (theorems, definitions and
their auxiliary constants, instances), the axioms it depends on; a summary line with the count of constants with an axiom
outside `[propext, Classical.choice, Quot.sound]`, the count depending on `sorryAx`, and the names of the latter. -/

open Lean Elab Command

elab "#l16_axioms " mod:ident : command => do
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

#l16_axioms HRTorus.ZeroModes.Theta
#l16_axioms HRTorus.ZeroModes.Canonical
#l16_axioms HRTorus.ZeroModes.Explicit
#l16_axioms HRTorus.ZeroModes.Lower
#l16_axioms HRTorus.ZeroModes.Formulation
#l16_axioms HRTorus.ZeroModes.Spaces
#l16_axioms HRTorus.ZeroModes.Merge
#l16_axioms HRTorus.ZeroModes.Upper
