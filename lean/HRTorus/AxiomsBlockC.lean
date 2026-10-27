import HRTorus.LLL.Theta
import HRTorus.LLL.Space
import HRTorus.Fock.Hamiltonian
import HRTorus.Hamiltonian.Pairs
import HRTorus.Hamiltonian.LocalForm
import HRTorus.Hamiltonian.SlotLocal
import HRTorus.Hamiltonian.BandCharges
import Lean.Util.CollectAxioms

/-! The axiom check of block C's seven modules (`HRTorus.LLL.Theta`, `HRTorus.LLL.Space`, `HRTorus.Fock.Hamiltonian`, `HRTorus.Hamiltonian.Pairs`, `HRTorus.Hamiltonian.LocalForm`, `HRTorus.Hamiltonian.SlotLocal`, `HRTorus.Hamiltonian.BandCharges`; Section 4 of the HR paper, with the upstream module `HRTorus.LLL.Theta` and the two modules of block A it completed). Run with
`lake env lean HRTorus/AxiomsBlockC.lean` from this directory after `lake build`. For every non-internal constant defined in the named module (theorems, definitions and their auxiliary constants,
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

#module_axioms HRTorus.LLL.Theta
#module_axioms HRTorus.LLL.Space
#module_axioms HRTorus.Fock.Hamiltonian
#module_axioms HRTorus.Hamiltonian.Pairs
#module_axioms HRTorus.Hamiltonian.LocalForm
#module_axioms HRTorus.Hamiltonian.SlotLocal
#module_axioms HRTorus.Hamiltonian.BandCharges
