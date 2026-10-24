#!/bin/sh
# replay.sh -- replays every module of HRTorus through Lean's kernel checker, one module at a time.
# Run it from this directory after `lake build`. `lake env leanchecker M` re-checks, in the kernel,
# every declaration defined in module M, loading M's imports from their compiled .olean files; so one
# run per module covers every declaration of the formalization. Mathlib's own declarations are loaded,
# not replayed. Exit status 0 iff every module passes.
cd "$(dirname "$0")" || exit 1
MODULES="
HRTorus.IndexCore.Statement
HRTorus.IndexCore.Spectral
HRTorus.IndexCore.KP
HRTorus.IndexCore.Clustering
HRTorus.IndexCore.ExpBounds
HRTorus.IndexCore.Commutation
HRTorus.IndexCore.Det
HRTorus.IndexCore.BBDF42
HRTorus.IndexCore.ODE
HRTorus.IndexCore.Determinant
HRTorus.IndexCore.Main
HRTorus.IndexCore.Sanity
HRTorus.IndexCore.Translation
HRTorus.IndexCore.Ring
HRTorus.SlotFrame.Analysis
HRTorus.SlotFrame.SlotFrame
HRTorus.Laughlin.GramPoisson
HRTorus.Fermion.Pilot.JW
HRTorus.Fermion.Pilot.CAR
HRTorus.LLL.Space
HRTorus.LLL.Frame
HRTorus.Fock.Physical
HRTorus.Fock.Hamiltonian
HRTorus.Fock.Slot
HRTorus.Fock.Embedding
HRTorus.Locality.Basic
"
fail=0
for m in $MODULES; do
  if lake env leanchecker "$m"; then
    echo "ok    $m"
  else
    echo "FAIL  $m"
    fail=1
  fi
done
if [ "$fail" -eq 0 ]; then echo "all modules replayed"; else echo "some module failed" >&2; fi
exit $fail
