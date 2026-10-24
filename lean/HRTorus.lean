import HRTorus.IndexCore.Statement
import HRTorus.IndexCore.Spectral
import HRTorus.IndexCore.KP
import HRTorus.IndexCore.Clustering
import HRTorus.IndexCore.ExpBounds
import HRTorus.IndexCore.Commutation
import HRTorus.IndexCore.Det
import HRTorus.IndexCore.BBDF42
import HRTorus.IndexCore.ODE
import HRTorus.IndexCore.Determinant
import HRTorus.IndexCore.Main
import HRTorus.IndexCore.Sanity
import HRTorus.IndexCore.Translation
import HRTorus.IndexCore.Ring
import HRTorus.SlotFrame.Analysis
import HRTorus.SlotFrame.SlotFrame
import HRTorus.Laughlin.GramPoisson
import HRTorus.Fermion.Pilot.JW
import HRTorus.Fermion.Pilot.CAR

/-!
# HRTorus

The Lean 4 formalization accompanying the papers in `papers/` of this repository (see `lean/README.md`):

* `HRTorus.IndexCore` — the finite-dimensional core of the index theorem of the HR paper (Section 6 and
  Appendix A; the main theorem is `HRTorus.IndexCore.index_core`, in the twelve modules `Statement` to
  `Sanity`), the divisibility corollary of its Section 7 (`Translation`), and a non-vacuity instance for
  every `N ≥ 1` (`Ring`);
* `HRTorus.SlotFrame` — Lemma 3.5 of the HR paper, the uniform localization of the slot frame;
* `HRTorus.Laughlin` — a pilot: the analytic core of Lemma 4.1 of the Laughlin paper;
* `HRTorus.Fermion.Pilot` — Lemma 5.1 of the HR paper (the conditional expectations onto the local CAR algebras)
  proved under two representations of the fermion algebra, a concrete Jordan–Wigner Fock space (`JW`) and an
  abstract CAR C*-algebra (`CAR`): a measurement pilot for the choice of representation, which is pending.

`HRTorus/Axioms.lean` (not imported here) prints the axioms of every declaration.
-/
