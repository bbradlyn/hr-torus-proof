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
import HRTorus.Assembly.Setting
import HRTorus.Assembly.Inputs
import HRTorus.Assembly.Translation
import HRTorus.Assembly.Main
import HRTorus.ZeroModes.Theta
import HRTorus.ZeroModes.Canonical
import HRTorus.ZeroModes.Explicit
import HRTorus.ZeroModes.Lower
import HRTorus.ZeroModes.Formulation
import HRTorus.ZeroModes.Spaces
import HRTorus.ZeroModes.Merge
import HRTorus.ZeroModes.Upper
import HRTorus.ZeroModes.Twist

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
  its coefficients as the integrals of Definition 2.7: 98 statements, all proved — the six once open were proved with Section 4,
  through the theta-function devices of `HRTorus.LLL.Theta`, and the completeness of the Landau-level bridge `isLLL_iff` with
  the assembly (`lean/README.md`);
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
  sentence: 85 statements, all proved;
* `HRTorus.Assembly.Setting`, `Inputs`, `Translation`, `Main` — Sections 6–8 of the HR paper: Setting 6.1 on the physical Fock
  space with the half-tori, the currents and the ordered sector eigenvalues E_k(N), Assumption 6.3, Lemmas 6.2 and 6.6–6.8; the
  inputs of the index core from the hollow-core model (Proposition 6.10, Definition 6.11 for U = Θ, Lemmas 6.12–6.13, the
  clustering inputs, ε(N) = O(N^{−∞}) and M(N) = O(N²)) and Theorem 6.18 for Θ; Lemma 7.1 and Corollaries 7.2–7.4; **Theorem
  8.1** (`hollow_core_index`, `hollow_core_E11_tendsto` in `Main`), Corollary 8.2, Lemma 8.3 and Corollary 8.4, with the ten zero
  modes of Appendix C as named hypotheses (`HasTenZeroModes`, `HasTwoZeroModes`) where the paper uses them: 97 statements, all
  proved;
* `HRTorus.ZeroModes.Theta`, `Canonical`, `Explicit`, `Lower` — Appendix C of the HR paper, the lower bound of Theorem 2.10
  (the formalization's stage F): the theta functions `ϑ[a,b]` and `ϑ₁` with its zero set, the spaces `Θ_ℓ[a,b]` and `Θ_2[ε]`,
  Mathlib's `℘` and the `℘_ε`, the class of continuous separately entire functions and `J` (Lemma C.8); the canonical components
  of a Fock vector, the orbital pair operators identified with Definition 4.1, Lemma C.4 and Lemma C.6 in the direction
  (2) ⇒ (3) ⇒ (1); the explicit states of Proposition C.18 with their numerators, merges and independence (Lemma C.10,
  Theorem C.19(ii)–(iii)); and in `Lower` at least ten zero modes of H_N in the sector (N/2, N/2) at every even N
  (`ten_le_finrank_ker`) and at least two in each of the sectors ((N ± 1)/2, (N ∓ 1)/2) at every odd N ≥ 3
  (`two_le_finrank_ker_odd`), from which **Theorem 8.1, Corollary 8.2 and Corollary 8.4 follow unconditionally**
  (`hollow_core_index_unconditional`, `hollow_core_E11_tendsto_unconditional`, `odd_E3_tendsto_unconditional`,
  `odd_many_small_unconditional`, `uniform_E11_tendsto_unconditional`, `uniform_E11_eventually_unconditional`): 118
  statements, all proved;
* `HRTorus.ZeroModes.Formulation`, `Spaces`, `Merge`, `Upper` — Appendix C's exact count, **Theorem 2.10(i)–(iii)** (stage F,
  block F1-upper): Lemma C.6 completed, (1) ⇒ (3) from Theorem 4.2(c)'s sum of squares and (3) ⇒ (2) from Lemma C.4's
  identity, so that the kernel of H_N in the sector (n, m) is linearly equivalent to the space V_{n,m} of the functions of the
  canonical shape with (C1) and (C2) (`kerSector_equiv_V`); Definition C.11 through numerators (`Gnum`, the space of the
  J²g), Θ_2[ε] for ε ∈ μ_N², and Lemma C.12 with the count dim V_{n,m} = 2 Σ_ε dim 𝒢(n,m;ε) by the projectors
  P_jk = N⁻² Σ ω^{−jr−ks} (T_K²)^r (T_1²)^s (`finrank_V_eq`); the merging induction in numerator form — Lemmas C.13(a)–(d) and
  C.14, Propositions C.15–C.16, Corollary C.17 — over a toolkit for continuous separately entire functions (Cauchy's formula
  for the slice derivatives, division by ϑ₁(u_s − u_t)^k, Liouville one variable at a time, Baire for the generic points);
  Theorem C.19(i)–(iii) at the level of V_{n,m} for every τ (`T2_i`, `T2_ii`, `T2_iii`: V_{n,m} = 0 for |n − m| ≥ 2,
  dim V_{m+1,m} = dim V_{m,m+1} = 2, dim V_{p,p} = 10); and for the rectangular tori **Theorem 2.10(i)–(iii)**
  (`kernel_sector_eq_bot`, `finrank_kernel_odd`, `finrank_kernel_half`, `KN_le_halfSector`, `finrank_KN_odd`,
  `finrank_KN_even`), with the spanning statements (`kernel_half_eq_span`, `kernel_oddPlus_eq_span`,
  `kernel_oddMinus_eq_span`), from which the named hypotheses `HasTenZeroModes` and `HasTwoZeroModes` of the reviewed main
  theorems are discharged (`hasTenZeroModes`, `hasTwoZeroModes`): **every reviewed statement of `Assembly.Main` holds for the
  rectangular tori as stated**: 100 statements and 17 definitions, all proved. Not formalized: Lemmas C.2, C.3 and C.5 (the
  Lean reaches Lemma C.6 through Theorem 4.2's local form and Lemma C.4), Lemma C.8(b), Lemma C.13(e) and Theorem C.19(iv);
* `HRTorus.ZeroModes.Twist` — Appendix D of the HR paper, **the variational bound at fixed circumference** (stage F, block F2):
  the spin twists 𝒲_σ as diagonal unitaries in the occupation-number basis with Lemma D.3 (the paper's exponential, the
  conjugation of the annihilators, the commutation with Θ on the sectors, the second-quantized form through block A's `Ff`),
  the pair annihilators at distance d with the singlet pair, Lemma D.4 (the energy identity (D.3) and the bound (D.4) for the
  twist 𝒲_↑ and for the two-species twist 𝒲_↑𝒲_↓^*), Lemma D.5 (a zero mode twisted off the kernel, the order of the root
  of unity as Mathlib's `orderOf`), Lemma D.6 (the Gaussian sums, by the sum–integral comparison), and **Theorem D.1 for the
  rectangular tori** — a unit vector of the sector orthogonal to 𝒦_N with expectation at most the left-hand side of (D.2)
  (`twist_bound`), (D.2)'s inequality on every torus (`twistBound_le_twistBoundLy`), E_11(N) at even N and E_3(N) in both odd
  sectors below the right-hand side (`E11_le_twistBoundLy`, `E3_le_twistBoundLy`) and below the numerical form
  (`E11_le_twistBoundNum`, `E3_le_twistBoundNum`) — with **Corollary D.2 over all rectangular tori** with L_xL_y = 4πN
  (`alltori_E11_eventually`, `alltori_E11_tendsto`, the supremum bounded above at every even N by `E11_bddAbove_allTori`):
  46 statements and 15 definitions, all proved. Not formalized: the remarks of Appendix D (D.7–D.10) and the unnumbered
  commentary after Theorem D.1.

`HRTorus/Axioms.lean` (not imported here) prints the axioms of every declaration of the index core, Lemma 3.5 and the Laughlin
pilot; the pilot and the blocks of Sections 2–8 and Appendices C and D have their own files, `HRTorus/Fermion/Pilot/Axioms.lean` and
`HRTorus/AxiomsBlockA.lean`–`AxiomsBlockF.lean` (`lean/README.md`). No declaration of the project depends on `sorryAx`.
-/
