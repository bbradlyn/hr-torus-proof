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
import HRTorus.LLL.Space
import HRTorus.LLL.Frame
import HRTorus.Fock.Physical
import HRTorus.Fock.Hamiltonian

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
  abstract CAR C*-algebra (`CAR`): a measurement pilot for the choice of representation (the concrete one was chosen);
* `HRTorus.LLL` and `HRTorus.Fock` — the physical side of the HR paper (Sections 2.1–2.5, 3.1–3.2): the lowest Landau level
  as a space with the orbitals as its basis, the evaluation and frame vectors, the analysis map with Proposition 3.3, the
  physical Fock space with its sectors and the magnetic translation Θ (Lemma 2.6), and the hollow-core Hamiltonian H_N with
  its coefficients as the integrals of Definition 2.7. **Seven of its 98 statements remain `sorry`** (listed in `lean/README.md`).

`HRTorus/Axioms.lean` (not imported here) prints the axioms of every declaration.
-/
