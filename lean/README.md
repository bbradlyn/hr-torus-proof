# HRTorus: the Lean 4 formalization

Lean 4.34.1 (`lean-toolchain`) against Mathlib at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`
(`lakefile.toml`, `lake-manifest.json`); every module is compiled with `autoImplicit = false`. Seventeen modules,
8,676 lines, 651 named declarations (547 theorems), no `sorry`. The papers are in `../papers/`; each module's
docstring names the paper, the section and the statements it formalizes. For the index core, the corollary of
Section 7, Lemma 3.5 and the Laughlin pilot, the Lean statements were written and compared with the paper before any
of their proofs was written.

## What is proved

### The HR paper (`../papers/hr/`)

**The finite-dimensional core of the index theorem** — `HRTorus.IndexCore`, the twelve modules `Statement`,
`Spectral`, `KP`, `Clustering`, `ExpBounds`, `Commutation`, `Det`, `BBDF42`, `ODE`, `Determinant`, `Main` and
`Sanity` (366 theorems). The main theorem, `HRTorus.IndexCore.index_core` (in `Main.lean`): for every
finite-dimensional complex inner product space `E`, every `Setting E` — the exact data and relations of Setting 6.1,
Assumptions 6.3–6.4 and Definitions 6.5 and 6.11 of the paper — and all real `ε`, `M` such that the 27 inputs of the
argument are at most `ε` ((U2), the `+` half of (U4), the 21 separated commutators of Lemma 6.13(ii), and the four
clustering commutators) and `‖T₋‖ ≤ M`, `‖K₋‖ ≤ M`, there is an integer `n` with
`‖Tr(P T₋) − n‖ ≤ 1000 · p · (M + 1) · √ε`, where `p` is the rank of `P`. With it: `index_core_400` (the same with
`400` in place of `1000`, the form Remark 6.21 of the paper states) and `Setting.SepBounds.index_core_small`
(`p · (393 M + 17) · √ε` when `ε (648π² + 8) ≤ 1`). The proof formalizes the algebra of Section 6 and Appendix A:
Lemma 6.7, Proposition 6.10(i)–(ii), Lemmas 6.13–6.17 and Lemmas A.6, A.8 and A.9 (the identity (6.7) is used as a
bound, not stated as an identity). `Sanity.lean` gives an instance on ℂ² satisfying every hypothesis with `ε = 0`;
it shows that the hypotheses can hold together, and nothing more (with `P = 1` the `ε`-parts are met trivially).

**The divisibility corollary of Section 7** — `HRTorus.IndexCore.Translation` and `HRTorus.IndexCore.Ring`
(64 theorems). The structure `Orbital` carries the orbital data of Section 7 with the algebraic properties listed in
Remark 8.7 as fields; `Orbital.toSetting` constructs the setting of Section 6 from it. Proved: Lemma 7.1(a)–(d) and
the finite clause of (e), Corollary 7.2 in quantitative form (`Orbital.translation_corollary`), Corollary 7.3
(`Orbital.four_dvd_p`) and the finite content of Corollary 7.4 (`Orbital.odd_plus`, `Orbital.odd_minus`).
`OrbitalRing.nonvacuity` is an instance of the orbital structure for every `N ≥ 1` (one particle on the ring
`ℤ_{2N}`), again with `ε = 0` and `P = 1`.

**Lemma 3.5, the uniform localization of the slot frame** — `HRTorus.SlotFrame.Analysis` and
`HRTorus.SlotFrame.SlotFrame` (108 theorems): `localization_i`, `localization_ii`, `localization_iii` and
`localization` (one constant for the three parts), with the definitions of Sections 2–3 they need (the torus and its
orbitals, the profile and the window, the slot lattice, the frame vectors) and the statements of Sections 2–3 that
the proof uses. The profile is a hypothesis (`IsProfile`), and part (iii) is stated in reduced form, as the ℓ²-norm
of `s ↦ z_s(R)` over the slots outside the ball (the module docstring lists these modelling choices).

### The Laughlin paper (`../papers/laughlin/`)

**A pilot** — `HRTorus.Laughlin.GramPoisson` (9 theorems): the analytic core of Lemma 4.1 — the Fourier transform of
`g(u) = (u² − M²/4) e^{−κ²u²/2}` in closed form (`fourier_g`), Poisson summation on the coset `c + 2ℤ`
(`coset_poisson`), and the closed form of the paper's `S_j` (`S_closed_form`). The rest of the Laughlin paper is not
formalized here.

### What is not formalized

The analytic part of the HR paper (Sections 3–5 apart from Lemma 3.5, and Appendix B), which supplies the inputs
that `index_core` takes as hypotheses; the orbital properties of the actual model, which `Orbital` takes as fields;
the kernel of Appendix C, the spin-twist bound of Appendix D, and the assembly of the main theorems of Section 8; and
the Laughlin paper apart from the pilot.

**Lemma 5.1, the conditional expectations onto the local algebras, under two representations of the fermion
algebra** — `HRTorus.Fermion.Pilot.JW` (96 theorems: the slot Fock space as a Jordan–Wigner matrix algebra on occupation
configurations, the expectation as the Hilbert–Schmidt projection — the paper's definition) and `HRTorus.Fermion.Pilot.CAR`
(234 theorems: an abstract C*-algebra carrying the anticommutation relations as fields, the expectation as a twirl over the
modes outside the region, with the paper's defining properties and its uniqueness as theorems). Both prove every clause of
Lemma 5.1 — linear, unital, positive, contractive, idempotent, *-preserving, commuting with parity and gauge, mapping even
operators into the even local algebra, and the bound ‖A − 𝔼_Y A‖ ≤ 2 inf_{A' ∈ Alg(Y)} ‖A − A'‖ — except its measurability
sentence. The two modules are a measurement pilot for the choice of representation in which Sections 3.2–5 will be
formalized; that choice is pending, and the chosen module will be renamed out of `Pilot` when it is made.

## Building

Install [elan](https://github.com/leanprover/elan), which reads `lean-toolchain` and installs Lean 4.34.1. Then, in
this directory:

    lake exe cache get    # downloads Mathlib's compiled files for the pinned commit
    lake build            # builds the seventeen modules (the default target, HRTorus)

<!-- PLACEHOLDER (to confirm): not yet run from a clean checkout. In preparing this tree, `lake build` ran against an
existing local copy of the same pinned packages: 3,207 jobs, 67 s with one worker, peak 3.7 GiB. -->

The build prints the output of the `#check` and `#print` commands at the ends of some modules, and seven
unused-variable warnings from the linter.

## The axiom check

    lake env lean HRTorus/Axioms.lean

prints, for each of the 651 named declarations, the axioms it depends on. In the build of this tree: 650 depend on
exactly `[propext, Classical.choice, Quot.sound]`, the three standard axioms of Lean's logic, and one
(`HRTorus.IndexCore.OrbitalRing.neZero_two_mul`) on `[propext, Quot.sound]`; none depends on `sorryAx`.
The pilot modules have their own check, `lake env lean HRTorus/Fermion/Pilot/Axioms.lean`: 455 declarations, 408 on the
three standard axioms, 3 on `[Quot.sound]`, 44 on none, none on `sorryAx`.

## The kernel replay

    ./replay.sh

runs `lake env leanchecker M` for each of the seventeen modules `M`, one at a time. `leanchecker M` re-checks in
Lean's kernel every declaration defined in `M`, loading `M`'s imports from their compiled files; one run per module
therefore covers every declaration of the formalization, while Mathlib's own declarations are loaded, not replayed.
In the build of this tree every module passed (exit status 0, about 4–5 s each).

## License

Apache License 2.0 (`LICENSE`, `NOTICE`).
