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
import HRTorus.Fock.Slot
import HRTorus.Fock.Embedding
import HRTorus.Locality.Basic
import HRTorus.LLL.Theta
import HRTorus.Hamiltonian.Pairs
import HRTorus.Hamiltonian.LocalForm
import HRTorus.Hamiltonian.SlotLocal
import HRTorus.Hamiltonian.BandCharges
import HRTorus.Locality.LiebRobinson
import HRTorus.Locality.Propagation
import HRTorus.Locality.Calculus
import HRTorus.Locality.Filters

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
  its coefficients as the integrals of Definition 2.7. **One of its 98 statements remains `sorry`**, the completeness of the
  Landau-level bridge `isLLL_iff` (`lean/README.md`); the six once open were proved with Section 4, through the theta-function
  devices of `HRTorus.LLL.Theta`.
* `HRTorus.Fock.Slot`, `HRTorus.Fock.Embedding`, `HRTorus.Locality.Basic` — the slot Fock space with its local algebras and
  fattenings (Definition 3.7), **the embedding ι of the physical Fock space into it as a definition, with Lemma 3.8 in full**,
  and the slot lattice's geometry and locality vocabulary (Proposition 3.4, Lemma 3.6, Definitions 3.9 and 3.11, Lemma
  3.10): 99 statements, all proved;
* `HRTorus.Hamiltonian` — Section 4 of the HR paper: the triplet pair operators and the local terms (Definition 4.1), **the exact
  local form of the hollow-core Hamiltonian (Theorem 4.2)** with the jet lemma (4.3), the uniform size and rapid locality of the
  local terms in the slot lattice (Proposition 4.4), the covariance (Lemma 4.5), the class of slot-local covariant Hamiltonians
  (Definition 4.6) with the hollow-core Hamiltonian in it (Corollary 4.8), and the band charges (Definition 4.9, Lemmas
  4.10–4.11): 77 statements, all proved, and `H_N ≥ 0` (`HRTorus.Fock.HN_posSemidef`) proved here from Theorem 4.2(a);
* `HRTorus.Locality.LiebRobinson`, `Propagation`, `Calculus`, `Filters` — Section 5 of the HR paper with Appendix B: the
  Lieb–Robinson bound for even interactions on the slot lattice (Theorem 5.2, from Appendix B's one-step estimate), **the
  propagation bound (Theorem 5.3)** with the propagation of almost-supported operators (Lemma 5.5), the time filters and the
  commutator with the Hamiltonian (Lemmas 5.6–5.7), the generator and clustering filters (Definition 5.8, Lemmas 5.9–5.10,
  Proposition 5.11), the locality calculus (Lemma 5.12) and the bookkeeping (Lemma 5.13), and Lemma 5.1's measurability
  sentence: 85 statements, all proved.

`HRTorus/Axioms.lean` (not imported here) prints the axioms of every declaration.
-/
