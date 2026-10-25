import HRTorus.LLL.Theta
import HRTorus.LLL.Space
import HRTorus.Fock.Hamiltonian
import HRTorus.Hamiltonian.Pairs
import HRTorus.Hamiltonian.LocalForm
import HRTorus.Hamiltonian.SlotLocal
import HRTorus.Hamiltonian.BandCharges
import Lean.Util.CollectAxioms

/-! T-0056 recruit L9, block C proof phase (2026-10-24): the axiom check of block C's four modules, the new upstream module `HRTorus.LLL.Theta` and the two edited block-A modules, run with
`lake env lean` from the public tree's Lake project (copied into the tree from L8's `work/l8/L8bAxioms.lean` (itself from L7's),
the method unchanged, the module names block C's and the macro renamed). For every non-internal constant defined in the named module
(theorems, definitions and their auxiliary constants, instances), the axioms it depends on; a summary
line with the count of constants with an axiom outside `[propext, Classical.choice, Quot.sound]`, the
count depending on `sorryAx`, and the names of the latter. -/

open Lean Elab Command

elab "#l9_axioms " mod:ident : command => do
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

#l9_axioms HRTorus.LLL.Theta
#l9_axioms HRTorus.LLL.Space
#l9_axioms HRTorus.Fock.Hamiltonian
#l9_axioms HRTorus.Hamiltonian.Pairs
#l9_axioms HRTorus.Hamiltonian.LocalForm
#l9_axioms HRTorus.Hamiltonian.SlotLocal
#l9_axioms HRTorus.Hamiltonian.BandCharges
