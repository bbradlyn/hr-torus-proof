# hr-torus-proof

Two papers and a Lean 4 formalization, by a multi-agent AI team in collaboration with Barry Bradlyn.

- `papers/hr/` — *The Haldane–Rezayi zero modes are not a gapped ground-state manifold on the torus* (99 pages; `main.pdf` included).
- `papers/laughlin/` — *An explicit uniform spectral gap for the Laughlin state parent Hamiltonian on rectangular tori* (44 pages; `main.pdf` included).
- `lean/` — the Lean 4 project `HRTorus`: the finite-dimensional core of the HR paper's index theorem, §7's divisibility corollary with an instance for every N, Lemma 3.5 (the slot frame's uniform localization), one pilot lemma of the Laughlin paper, the physical side of the HR paper (Sections 2.1–2.5 and 3.1–3.2: the Landau level, the Fock space, the magnetic translation, the Hamiltonian), the slot Fock space with the embedding of the physical Fock space into it and the locality vocabulary of the slot lattice (Sections 3.2–3.3, Lemma 3.8 in full), and the Hamiltonian in the slot frame (Section 4: the exact local form of Theorem 4.2, the slot-local class, the band charges) — all on Lean's three standard axioms and replayed through the kernel checker, **except one stated theorem of Section 2, the completeness of the Landau-level bridge, that is not yet proved and is named in `lean/README.md`**.

## About this work

This project was inspired by the appearance of OpenAI's claimed proof of a Fock space gap for the Laughlin state parent Hamiltonian on the sphere (https://github.com/openai/math/blob/main/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf). The release of these results took the theoretical physics community by surprise. Although AI labs had been releasing expansive mathematical results for some time, the scale and scope of the aforementioned release was unprecedented. Furthermore, the fact that very few of the results had undergone study by human mathematicians or physicists prior to release raises important epistemological questions. At its core, the claimed proof was a machine-verified and agent-authored set of claims rather than a communication of scientific knowledge (which is part of our human collective understanding as much as it is a collection of facts about the world). Understanding and digesting claims like this represents a new domain of investigation for physicists, similar to discovering some unknown apparatus constructed by a bygone civilization and trying to figure out what it means. 

On the surface, this is similar to how the scientific community reacts when an Einstein or a Haldane publishes a paper that only the author understands fully, and the community mobilizes to digest, internalize, and extend the results. The fundamental difference from our present situation is that human authorship carries with it the assumption that the contents are knowledge that has already been processed by humans. This is so basic that it is an unstated assumption in the way we do science: humans make discoveries and write papers to communicate those discoveries to others and disseminate scientific knowledge. Because of this, the paper has come to be a proxy marker for the existence of that knowledge, and we regard the authors of the paper as the sources of that knowledge.

That assumption is no longer tenable. OpenAI's preprints were agent-authored, and were written with minimal human input. Regardless of what the company may want, there is no human entity to whom credit can be assigned for these creations. Incorporating these claims into our corpus of scientific knowledge requires a new kind of investigation akin to archaeology.

This present project is my attempt to engage with that process. To that end, I asked the question of whether similar techniques could be used in converse to establish whether a parent Hamiltonian cannot have a gapped topological phase for its ground state. A natural first candidate to look at is the parent Hamiltonian for the Haldane-Rezayi state. Field-theoretic and numerical arguments strongly suggest that this parent Hamiltonian is gapless, even though the Haldane-Rezayi state is an exact ground state. I organized a collaboration with several AI agents under a collaborative charter that is included here as `CHARTER.md` (in the collaboration's own workspace it is the file `AGENTS.md`, which every agent session reads first). The models engaged include Anthropic's Fable 5.1 and Opus 5.5, as well as OpenAI's Astra 6. After the agents worked through the Laughlin paper and helped me understand the high-level details, we attempted to apply the same techniques to the Haldane-Rezayi parent Hamiltonian on the sphere. We eventually got stuck after reducing the problem to a statement about screening in the plasma analogy that seemed intractable to make rigorous. We then pivoted to the torus, resulting in the present work.

The core approach that the agents figured out amounts to applying a Lieb–Schultz–Mattis (LSM)-like theorem to quantum Hall systems. After finding a way to map an LSM-like index theorem of Bachmann, Bols, De Roeck, and Fraas to quantum Hall systems on a torus using a discrete lattice basis of orbitals, the agents then showed that the 10-state space of Haldane-Rezayi states cannot be energetically isolated in the thermodynamic limit. This means that the parent Hamiltonian does not realize a topological phase with these 10 states as the entire gapped ground state manifold. In terms of the Moore-Read construction these 10 states come from conformal blocks in a c=-2 conformal field theory (CFT). The fact that they cannot be the complete ground state subspace of the parent Hamiltonian supports Read's claim that the c=-2 conformal field theory does not determine a gapped topological phase in the Moore-Read construction.

Beyond understanding the intuitive core, I have not dived deep into the functional analysis that the agents used to complete the proof. While I guided the direction of the project, asked probing questions based on my physical intuition that shifted arguments and bolstered results, and helped organize the work (including the attempts at Lean formalization), the "real" work was carried out by the agent team. While I claim ownership of the work for the purposes of distribution (since AI agents cannot), I can't take credit for it. The important steps are not what I have done here, but what comes next as myself and others work to digest the proposed proof and incorporate it into our understanding of quantum Hall physics. To that end I have chosen to make the write-ups and Lean formalization public in this repository. I would encourage others to work through this, correct, extend, and comment on it.

-Barry Bradlyn

## Verification status, in brief

- **No human has read the proofs.** Every proof in both papers was re-derived by at least one AI instance that did not write it (two referee readings of the HR paper, one of the Laughlin paper), with two exceptions that were followed rather than re-derived: the HR paper's Appendix C and the Laughlin paper's Remark 9.3.
- The HR paper's finite-dimensional core is machine-checked: `HRTorus.IndexCore.index_core`, 366 theorems in twelve modules, depending only on `propext`, `Classical.choice` and `Quot.sound`, every module replayed through `leanchecker`; its statement was compared with the paper's §6 by two readers, one reading blind. Of the analytic parts of the HR proof, Sections 2–4 are formalized, with one statement of Section 2 still open (`lean/README.md` names it); Section 5, Appendix B and the assembly of Theorem 8.1 are not yet formalized.
- The Laughlin paper's thresholds are high-precision floating-point evaluations of rigorous closed-form bounds, not interval-arithmetic certificates; OpenAI's certificate inequalities are used as data, as published.

## Relation to other work

A candidate proof of a uniform Laughlin gap on tori of every lattice shape, with an existential threshold, was posted by Hou and Wu on 16 October 2026 (github.com/certainpineapple/Laughlin-torus-gap). Our argument was obtained independently, is restricted to rectangular tori, and makes the threshold and the rate of convergence explicit; where the two overlap, the statements agree. No priority is claimed.

## Building and checking

- Papers: `cd papers/hr && ./build.sh` (three `pdflatex` passes); likewise in `papers/laughlin`.
- Lean: `cd lean && lake exe cache get && lake build` (Lean 4.34.1, Mathlib at the pinned commit), then `lake env lean HRTorus/Axioms.lean` for the axiom check of every declaration and `./replay.sh` for the kernel replays.

## License

The papers (`papers/`) and this repository's documents are licensed under the Creative Commons Attribution 4.0 International license (CC BY 4.0; see `LICENSE`). The Lean code (`lean/`) is licensed under the Apache License 2.0 (see `lean/LICENSE` and `lean/NOTICE`). © 2026 A multi-agent AI team, in collaboration with Barry Bradlyn. To cite this repository, see `CITATION.cff`.

## Acknowledgments

B.B. thanks Andrey Gromov for discussions and encouragement to pursue this project
