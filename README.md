# hr-torus-proof

Two papers and a Lean 4 formalization, by a multi-agent AI team in collaboration with Barry Bradlyn.

- `papers/hr/` — *The Haldane–Rezayi zero modes are not a gapped ground-state manifold on the torus* (99 pages; `main.pdf` included).
- `papers/laughlin/` — *An explicit uniform spectral gap for the Laughlin state parent Hamiltonian on rectangular tori* (44 pages; `main.pdf` included).
- `lean/` — the Lean 4 project `HRTorus`: the finite-dimensional core of the HR paper's index theorem, §7's divisibility corollary with an instance for every N, Lemma 3.5 (the slot frame's uniform localization), one pilot lemma of the Laughlin paper, the physical side of the HR paper (Sections 2.1–2.5 and 3.1–3.2: the Landau level, the Fock space, the magnetic translation, the Hamiltonian), and the slot Fock space with the embedding of the physical Fock space into it and the locality vocabulary of the slot lattice (Sections 3.2–3.3, Lemma 3.8 in full) — all on Lean's three standard axioms and replayed through the kernel checker, **except seven stated theorems of the physical side that are not yet proved and are listed in `lean/README.md`**.

## About this work

[THE OWNER WRITES THIS SECTION: the collaboration, the provenance of the results, and where they stand.]

## Verification status, in brief

- **No human has read the proofs.** Every proof in both papers was re-derived by at least one AI instance that did not write it (two referee readings of the HR paper, one of the Laughlin paper), with two exceptions that were followed rather than re-derived: the HR paper's Appendix C and the Laughlin paper's Remark 9.3.
- The HR paper's finite-dimensional core is machine-checked: `HRTorus.IndexCore.index_core`, 366 theorems in twelve modules, depending only on `propext`, `Classical.choice` and `Quot.sound`, every module replayed through `leanchecker`; its statement was compared with the paper's §6 by two readers, one reading blind. Of the analytic parts of the HR proof, Sections 2.1–3.3 are formalized, with seven statements of Section 2 still open (`lean/README.md` names them); Sections 4 and 5, Appendix B and the assembly of Theorem 8.1 are not yet formalized.
- The Laughlin paper's thresholds are high-precision floating-point evaluations of rigorous closed-form bounds, not interval-arithmetic certificates; OpenAI's certificate inequalities are used as data, as published.

## Relation to other work

A candidate proof of a uniform Laughlin gap on tori of every lattice shape, with an existential threshold, was posted by Hou and Wu on 16 October 2026 (github.com/certainpineapple/Laughlin-torus-gap). Our argument was obtained independently, is restricted to rectangular tori, and makes the threshold and the rate of convergence explicit; where the two overlap, the statements agree. No priority is claimed.

## Building and checking

- Papers: `cd papers/hr && ./build.sh` (three `pdflatex` passes); likewise in `papers/laughlin`.
- Lean: `cd lean && lake exe cache get && lake build` (Lean 4.34.1, Mathlib at the pinned commit), then `lake env lean HRTorus/Axioms.lean` for the axiom check of every declaration and `./replay.sh` for the kernel replays.

## License

The papers (`papers/`) and this repository's documents are licensed under the Creative Commons Attribution 4.0 International license (CC BY 4.0; see `LICENSE`). The Lean code (`lean/`) is licensed under the Apache License 2.0 (see `lean/LICENSE` and `lean/NOTICE`). © 2026 A multi-agent AI team, in collaboration with Barry Bradlyn. To cite this repository, see `CITATION.cff`.
