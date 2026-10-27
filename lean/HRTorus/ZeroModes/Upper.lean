import HRTorus.ZeroModes.Merge
import HRTorus.ZeroModes.Lower

/-!
# Theorem 2.10 as stated, and the discharge of the zero-mode hypotheses (T-0056 stage F, block F1-upper, `ZeroModes.Upper`)

Written by Claude Opus 5.5 (an AI model; recruit L18), 2026-10-26. **Statement phase and proof phase (2026-10-26): the
definitions and statements were written first, every theorem that carries content `sorry`, and reviewed against the
paper before any proof; the proof phase (round three) then proved every statement, the reviewed text unchanged. The
proof devices — the declarations named `_dev`, in marked sections — are not statements of the paper. The two
discharges at the end of the module are one-line derivations through the bridges of `Assembly.Main`, written out as
a machine check that the statements connect.**
The paper: the HR paper — Theorem 2.10 `thm:kernel` (`sections/02-setting.tex`) and the paragraph after it ((2.8) and the
odd-sector sentence), proved by Theorem C.`T2` (`appendices/C-kernel.tex`, `kz:thm:T2`) (i)–(iii). Not here (not
formalized): Theorem C.T2(iv) ("`None of these statements depends on $\tau$.`" — the Lean's torus is rectangular; the
statements at the level of `V_{n,m}` below hold for every `τ`, but `V_{n,m}` is identified with the kernel only at
`τ = tauT T`), the spin remarks after Theorem 2.10 and after Theorem C.T2 (every zero mode a spin singlet at even `N`, a spin-½ doublet at odd `N`; nothing in the paper uses them), and the other remarks after Theorem C.T2.

## What the block delivers

* **Theorem C.T2(i)–(iii) at the level of `V_{n,m}`, for every `τ ∈ ℍ`** (`T2_i`, `T2_ii`, `T2_iii`): `V_{n,m} = 0` for
  `|n − m| ≥ 2`, `dim V_{m+1,m} = dim V_{m,m+1} = 2`, `dim V_{p,p} = 10` — from Lemma C.B(b) (`finrank_V_le`), Corollary
  C.bounds, Lemma C.B(a), and for the lower halves F1-lower's explicit states (which are stated for every `τ`).
* **Theorem 2.10(i)–(iii) for the rectangular torus `T`** (`τ = tauT T`, through `finrank_ker_eq_finrank_V`): the kernel in
  every `N`-electron sector with `|n_↑ − n_↓| ≥ 2` is zero; the kernel in each odd sector is two-dimensional, for every
  odd `N` (at `N = 1` the two sectors are the kernel, `𝒢(1,0;(1,1)) = ℂ`); the kernel in the sector `(N/2, N/2)` is
  ten-dimensional at even `N`, and `𝒦_N` — the kernel on the `N`-electron states, `KN T` — lies in that sector. The
  expressions are those of `ten_le_finrank_ker` and `two_le_finrank_ker_odd`, whose lower halves they complete.
* **The spanning statements**: the explicit states of F1-lower (`exists_ten_zero_modes`, `exists_two_zero_modes_plus`,
  `exists_two_zero_modes_minus`), for any independent choice of the centre-of-mass factors, span the kernel (an
  independent family of the size of the dimension).
* **The discharges** `hasTenZeroModes`, `hasTwoZeroModes`: (2.8) "`E_1(N)=\cdots=E_{10}(N)=0<E_{11}(N)`" and
  "`$E_1(N)=E_2(N)=0<E_3(N)$`" as theorems of the Lean's `H_N` (through `hasTenZeroModes_of_kernel` and
  `hasTwoZeroModes_of_kernel`), so that every reviewed main theorem of `Assembly.Main` applies to the rectangular tori
  with its hypothesis discharged.
-/

open Complex Filter Topology
open scoped Real UpperHalfPlane

noncomputable section

namespace HRTorus.ZeroModes

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian HRTorus.Assembly
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op)

/-! ## Theorem C.T2 at the level of the spaces `V_{n,m}`, for every `τ`

"`For every $\tau$ with $\operatorname{Im}\tau>0$ and every $N\ge1$, the hollow-core Hamiltonian $H$ of Section~\ref{kz:sec:ham} at $N_\phi=2N$ satisfies:`"
— through Lemma C.A, `ker H|_{n,m} = V_{n,m}` ("`By Lemma~\ref{kz:lem:A}, $\ker H|_{n,m}=V_{n,m}$.`"); in the Lean the identification
holds at `τ = tauT T` (`finrank_ker_eq_finrank_V`), and the statements below are about `V_{n,m}` at level `L = 2N`. -/

/-! ### Proof devices for Theorem C.T2 at the level of `V_{n,m}` (proof phase, round three; not statements of the paper)

Upper halves: Lemma C.B(b) in the form `finrank_V_le`, with Corollary C.bounds at the root pairs. At odd `N` only
`rootPair N (0,0) = (1,1)` survives (`rootPair_zero_dev`, `rootPair_injective`, `Gnum_odd_eq_bot`,
`finrank_Gnum_odd_pp`: `finrank_V_odd_le_dev`); at even `N` only the four sign pairs, each the root pair of exactly
one `jk` (`exists_rootPair_eps`, `exists_eps_pair_dev`, `rootPair_injective`, `Eps_pair_injective_dev`,
`Gnum_eq_bot_of_sq_ne_one`, `finrank_Gnum_even_eps`: `finrank_V_even_le_dev`) — the paper's
"`$\{\pm1\}^2\subset\mu_N^2$`". Lower halves: block F1-lower's explicit numerators, stated there for every `τ`
(`gOdd_numerator_props`, `gOddSwap_numerator_props`, `dEps_numerator_props`, `f5_numerator_props` for the membership in
`V`; `explicit_odd_linearIndependent`, `explicit_oddSwap_linearIndependent`, `explicit_even_linearIndependent` for the
independence), with two independent `F ∈ Θ_2[ε]` from L16's `exists_Θ2_pair_dev`, counted in `V` by
`card_le_finrank_fd_dev` (a copy of L16's `card_le_finrank_of_mem_dev` with the finite dimension asked of the subspace
instead of the ambient space). -/

theorem card_le_finrank_fd_dev {ι : Type*} [Fintype ι] {E : Type*} [AddCommGroup E] [Module ℂ E]
    (W : Submodule ℂ E) [FiniteDimensional ℂ W] {v : ι → E} (hv : ∀ i, v i ∈ W) (hli : LinearIndependent ℂ v) :
    Fintype.card ι ≤ Module.finrank ℂ W := by
  have hli' : LinearIndependent ℂ (fun i => (⟨v i, hv i⟩ : W)) := LinearIndependent.of_comp W.subtype hli
  exact hli'.fintype_card_le_finrank

theorem Eps_pair_injective_dev : Function.Injective Eps.pair := by
  intro e e' h
  cases e <;> cases e' <;> first | rfl | (exfalso; norm_num [Eps.pair, Eps.e1, Eps.e2, Prod.ext_iff] at h)

theorem rootPair_zero_dev {N : ℕ} (hN : 0 < N) : rootPair N (⟨0, hN⟩, ⟨0, hN⟩) = (1, 1) := by
  simp [rootPair]

theorem finrank_V_odd_le_dev (τ : ℍ) (m : ℕ) :
    (FiniteDimensional ℂ (V τ (2 * ((m + 1) + m)) (m + 1) m) ∧
        Module.finrank ℂ (V τ (2 * ((m + 1) + m)) (m + 1) m) ≤ 2) ∧
      (FiniteDimensional ℂ (V τ (2 * (m + (m + 1))) m (m + 1)) ∧
        Module.finrank ℂ (V τ (2 * (m + (m + 1))) m (m + 1)) ≤ 2) := by
  have hN : 0 < (m + 1) + m := by omega
  have hN' : 0 < m + (m + 1) := by omega
  constructor
  · have h00 := rootPair_zero_dev hN
    have hne : ∀ jk, jk ≠ ((⟨0, hN⟩, ⟨0, hN⟩) : Fin ((m + 1) + m) × Fin ((m + 1) + m)) →
        rootPair ((m + 1) + m) jk ≠ (1, 1) := fun jk hjk h => hjk (rootPair_injective _ (h.trans h00.symm))
    have hfin : ∀ jk, FiniteDimensional ℂ (Gnum τ (m + 1) m (rootPair ((m + 1) + m) jk)) := by
      intro jk
      by_cases hjk : jk = (⟨0, hN⟩, ⟨0, hN⟩)
      · rw [hjk, h00]
        exact (finrank_Gnum_odd_pp τ m).1.1
      · rw [(Gnum_odd_eq_bot τ m (hne jk hjk)).1]
        infer_instance
    obtain ⟨hfd, hle⟩ := finrank_V_le τ hN hfin
    refine ⟨hfd, hle.trans ?_⟩
    rw [Finset.sum_eq_single (⟨0, hN⟩, ⟨0, hN⟩) (fun jk _ hjk => by rw [(Gnum_odd_eq_bot τ m (hne jk hjk)).1]; simp)
      (fun h => absurd (Finset.mem_univ _) h), h00]
    have := (finrank_Gnum_odd_pp τ m).1.2
    omega
  · have h00 := rootPair_zero_dev hN'
    have hne : ∀ jk, jk ≠ ((⟨0, hN'⟩, ⟨0, hN'⟩) : Fin (m + (m + 1)) × Fin (m + (m + 1))) →
        rootPair (m + (m + 1)) jk ≠ (1, 1) := fun jk hjk h => hjk (rootPair_injective _ (h.trans h00.symm))
    have hfin : ∀ jk, FiniteDimensional ℂ (Gnum τ m (m + 1) (rootPair (m + (m + 1)) jk)) := by
      intro jk
      by_cases hjk : jk = (⟨0, hN'⟩, ⟨0, hN'⟩)
      · rw [hjk, h00]
        exact (finrank_Gnum_odd_pp τ m).2.1
      · rw [(Gnum_odd_eq_bot τ m (hne jk hjk)).2]
        infer_instance
    obtain ⟨hfd, hle⟩ := finrank_V_le τ hN' hfin
    refine ⟨hfd, hle.trans ?_⟩
    rw [Finset.sum_eq_single (⟨0, hN'⟩, ⟨0, hN'⟩) (fun jk _ hjk => by rw [(Gnum_odd_eq_bot τ m (hne jk hjk)).2]; simp)
      (fun h => absurd (Finset.mem_univ _) h), h00]
    have := (finrank_Gnum_odd_pp τ m).2.2
    omega

theorem finrank_V_even_le_dev (τ : ℍ) (q : ℕ) :
    FiniteDimensional ℂ (V τ (2 * ((q + 1) + (q + 1))) (q + 1) (q + 1)) ∧
      Module.finrank ℂ (V τ (2 * ((q + 1) + (q + 1))) (q + 1) (q + 1)) ≤ 10 := by
  have hN : 0 < (q + 1) + (q + 1) := by omega
  have heven : Even ((q + 1) + (q + 1)) := ⟨q + 1, rfl⟩
  obtain ⟨hfd, hle⟩ := finrank_V_le τ hN fun jk => (finrank_Gnum_even_le τ q _).1
  refine ⟨hfd, hle.trans ?_⟩
  choose σ hσ using fun e : Eps => exists_rootPair_eps hN heven e
  have hσinj : Function.Injective σ := by
    intro e e' h
    have h1 := hσ e
    rw [h, hσ e'] at h1
    exact Eps_pair_injective_dev h1.symm
  have hsum : ∑ jk, Module.finrank ℂ (Gnum τ (q + 1) (q + 1) (rootPair ((q + 1) + (q + 1)) jk)) =
      ∑ jk ∈ Finset.univ.image σ, Module.finrank ℂ (Gnum τ (q + 1) (q + 1) (rootPair ((q + 1) + (q + 1)) jk)) := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun jk _ hjk => ?_).symm
    have hns : ¬ ((rootPair ((q + 1) + (q + 1)) jk).1 ^ 2 = 1 ∧ (rootPair ((q + 1) + (q + 1)) jk).2 ^ 2 = 1) := by
      intro hsq
      obtain ⟨e, he⟩ := exists_eps_pair_dev hsq
      exact hjk (Finset.mem_image.2 ⟨e, Finset.mem_univ _, rootPair_injective _ ((hσ e).trans he.symm)⟩)
    rw [Gnum_eq_bot_of_sq_ne_one τ hN hns]
    simp
  rw [hsum, Finset.sum_image hσinj.injOn]
  have hb : ∀ e ∈ (Finset.univ : Finset Eps),
      Module.finrank ℂ (Gnum τ (q + 1) (q + 1) (rootPair ((q + 1) + (q + 1)) (σ e))) ≤ if e = .pp then 2 else 1 :=
    fun e _ => by rw [hσ e]; exact (finrank_Gnum_even_eps τ q e).2
  have h5 : (∑ e : Eps, (if e = .pp then 2 else 1 : ℕ)) = 5 := by decide
  have := Finset.sum_le_sum hb
  omega

/-- **Theorem C.T2(i)**: "`$\ker H\cap\{|S_z|\ge1\}=0$.`" — `V_{n,m} = 0` for `|n − m| ≥ 2` ("`(i) Corollary~\ref{kz:cor:bounds}(a), with $|n-m|=2|S_z|$.`"). -/
theorem T2_i (τ : ℍ) {n m : ℕ} (h : n + 2 ≤ m ∨ m + 2 ≤ n) : V τ (2 * (n + m)) n m = ⊥ := by
  have hN : 0 < n + m := by omega
  have hb : ∀ jk : Fin (n + m) × Fin (n + m), Gnum τ n m (rootPair (n + m) jk) = ⊥ :=
    fun jk => Gnum_eq_bot_of_imbalanced τ h _
  obtain ⟨hfd, hle⟩ := finrank_V_le τ hN fun jk => by rw [hb jk]; infer_instance
  have h0 : ∑ jk : Fin (n + m) × Fin (n + m), Module.finrank ℂ (Gnum τ n m (rootPair (n + m) jk)) = 0 :=
    Finset.sum_eq_zero fun jk _ => by rw [hb jk]; simp
  have := hfd
  exact Submodule.finrank_eq_zero.1 (by omega)

/-- **Theorem C.T2(ii)**: "`For odd $N$, $\dim\ker H|_{S_z=+1/2}=2$.`" and "`$S_z=-\tfrac12$ is the same with the species exchanged.`"
— `dim V_{m+1,m} = dim V_{m,m+1} = 2` (`N = 2m + 1`). -/
theorem T2_ii (τ : ℍ) (m : ℕ) :
    Module.finrank ℂ (V τ (2 * ((m + 1) + m)) (m + 1) m) = 2 ∧
      Module.finrank ℂ (V τ (2 * (m + (m + 1))) m (m + 1)) = 2 := by
  obtain ⟨⟨hfd1, hle1⟩, ⟨hfd2, hle2⟩⟩ := finrank_V_odd_le_dev τ m
  obtain ⟨F, hF, hFi⟩ := exists_Θ2_pair_dev τ .pp
  choose f hf using fun r => gOdd_numerator_exists τ m (hF r)
  choose g hg using fun r => gOddSwap_numerator_exists τ m (hF r)
  have := hfd1
  have := hfd2
  have h1 := card_le_finrank_fd_dev (V τ (2 * ((m + 1) + m)) (m + 1) m)
    (fun r => gOdd_numerator_props τ m (hF r) (hf r)) (explicit_odd_linearIndependent τ m F hF hFi f hf)
  have h2 := card_le_finrank_fd_dev (V τ (2 * (m + (m + 1))) m (m + 1))
    (fun r => gOddSwap_numerator_props τ m (hF r) (hg r)) (explicit_oddSwap_linearIndependent τ m F hF hFi g hg)
  rw [Fintype.card_fin] at h1 h2
  exact ⟨le_antisymm hle1 h1, le_antisymm hle2 h2⟩

/-- **Theorem C.T2(iii)**: "`For even $N=2p$, $\ker H$ lies in $S_z=0$ and has dimension $10$.`"
— `dim V_{p,p} = 10` (`p = q + 1`): "`Corollary~\ref{kz:cor:bounds}(c) and $\{\pm1\}^2\subset\mu_N^2$ give $\dim V_{p,p}\le2(2+1+1+1)=10$.`" -/
theorem T2_iii (τ : ℍ) (q : ℕ) : Module.finrank ℂ (V τ (2 * ((q + 1) + (q + 1))) (q + 1) (q + 1)) = 10 := by
  obtain ⟨hfd, hle⟩ := finrank_V_even_le_dev τ q
  choose F hF hFi using fun e : Option Eps => exists_Θ2_pair_dev τ (epsOf e)
  have hnum : ∀ i : Option Eps × Fin 2, ∃ f : (Fin ((q + 1) + (q + 1)) → ℂ) → ℂ,
      IsNumerator τ (q + 1) (q + 1) (F i.1 i.2) (gEven τ q i.1) f ∧
        f ∈ V τ (2 * ((q + 1) + (q + 1))) (q + 1) (q + 1) := by
    rintro ⟨e, r⟩
    cases e with
    | none =>
      obtain ⟨f, hf⟩ := f5_numerator_exists τ q (hF none r)
      exact ⟨f, hf, f5_numerator_props τ q (hF none r) hf⟩
    | some ε =>
      obtain ⟨f, hf⟩ := dEps_numerator_exists τ ε (q + 1) (hF (some ε) r)
      exact ⟨f, hf, dEps_numerator_props τ ε (q + 1) (hF (some ε) r) hf⟩
  choose f hf hmem using hnum
  have := hfd
  have h := card_le_finrank_fd_dev (V τ (2 * ((q + 1) + (q + 1))) (q + 1) (q + 1)) hmem
    (explicit_even_linearIndependent τ q F hF hFi f hf)
  have h4 : Fintype.card Eps = 4 := rfl
  rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, h4] at h
  omega

/-! ## Theorem 2.10 for the rectangular torus -/

/-- **Theorem 2.10**: "`let $\mathcal K_N$ be the kernel of $H_N$ restricted to the states with $N$ electrons, $\bigoplus_{n_\up+n_\dn=N}\sect{(n_\up,n_\dn)}$`"
— `𝒦_N`, the kernel of the Lean's `H_N` intersected with the sum of the sectors `(n_↑, n_↓)` with `n_↑ + n_↓ = N`. -/
def KN (T : Torus) : Submodule ℂ (FockSpace T) :=
  LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) ⊓
    ⨆ (nn : SectorLabel T) (_ : (nn.1 : ℕ) + (nn.2 : ℕ) = T.N), sector T nn

/-- **Theorem 2.10(i)** (Theorem C.T2(i)): "`$\mathcal K_N\cap\sect{(n_\up,n_\dn)}=\{0\}$ whenever $\abs{n_\up-n_\dn}\ge2$.`"
— for every `N`-electron sector (for such a sector `𝒦_N ∩ 𝓗^{(n_↑,n_↓)} = ker H_N ∩ 𝓗^{(n_↑,n_↓)}`). -/
theorem kernel_sector_eq_bot (T : Torus) (nn : SectorLabel T) (hN : (nn.1 : ℕ) + (nn.2 : ℕ) = T.N)
    (h2 : 2 ≤ |((nn.1 : ℕ) : ℤ) - ((nn.2 : ℕ) : ℤ)|) :
    LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) ⊓
      sector T nn = ⊥ := by
  obtain ⟨n, hn⟩ : ∃ n, (nn.1 : ℕ) = n := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, (nn.2 : ℕ) = m := ⟨_, rfl⟩
  rw [hn, hm] at h2 hN
  have h' : n + 2 ≤ m ∨ m + 2 ≤ n := by
    rcases le_abs.1 h2 with h | h <;> omega
  have hL : T.Nφ = 2 * (n + m) := by unfold Torus.Nφ; omega
  have hV : V (tauT T) T.Nφ n m = ⊥ := by
    rw [hL]
    exact T2_i (tauT T) h'
  have hfr := finrank_ker_eq_finrank_V T nn hn hm
  rw [hV, finrank_bot] at hfr
  exact Submodule.finrank_eq_zero.1 hfr

/-- For an `N`-electron sector, `𝒦_N ∩ 𝓗^{(n_↑,n_↓)} = ker H_N ∩ 𝓗^{(n_↑,n_↓)}` (the sector lies in the sum). -/
theorem KN_inf_sector (T : Torus) (nn : SectorLabel T) (hN : (nn.1 : ℕ) + (nn.2 : ℕ) = T.N) :
    KN T ⊓ sector T nn =
      LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) ⊓
        sector T nn := by
  have h : sector T nn ≤ ⨆ (nn' : SectorLabel T) (_ : (nn'.1 : ℕ) + (nn'.2 : ℕ) = T.N), sector T nn' :=
    le_iSup₂_of_le nn hN le_rfl
  unfold KN
  rw [inf_assoc, inf_eq_right.mpr h]

/-- **Theorem 2.10(i)**: "`$\mathcal K_N\cap\sect{(n_\up,n_\dn)}=\{0\}$ whenever $\abs{n_\up-n_\dn}\ge2$.`" — literally, with
`𝒦_N` (from `kernel_sector_eq_bot` and `KN_inf_sector`). -/
theorem KN_inf_sector_eq_bot (T : Torus) (nn : SectorLabel T) (hN : (nn.1 : ℕ) + (nn.2 : ℕ) = T.N)
    (h2 : 2 ≤ |((nn.1 : ℕ) : ℤ) - ((nn.2 : ℕ) : ℤ)|) : KN T ⊓ sector T nn = ⊥ := by
  rw [KN_inf_sector T nn hN]
  exact kernel_sector_eq_bot T nn hN h2

/-! ### Proof devices for Theorem 2.10 on `𝒦_N` (proof phase, round three; not statements of the paper)

The grading of the kernel by the sectors, componentwise in the occupation basis: `P_𝐧 = diag(1_{secOf = 𝐧})`
(`Psec_eq_diag`; `Psec_apply_dev`) commutes with `H_N` (`HN_isSectorPreserving`, `isSectorPreserving_iff_commute`), so
it maps the kernel into the kernel in the sector (`Psec_mem_ker_sector_dev`, the pattern of `toCLM_mem_sector_dev`); a
vector of the sum of the `N`-electron sectors is supported on `N`-electron configurations (`KN_support_dev`, by
`Submodule.iSup_induction`); a vector of `𝒦_N` is supported on configurations whose sector has `|n_↑ − n_↓| ≤ 1`
(`KN_support_low_dev`: otherwise its `P_𝐧`-component would be a nonzero element of `ker H_N ∩ 𝓗^{𝐧} = 0`,
`kernel_sector_eq_bot`). -/

theorem Psec_apply_dev (T : Torus) (nn : SectorLabel T) (v : FockSpace T) (c : Conf (ZMod T.Nφ)) :
    toCLM T (Psec T nn) v c = if secOf T c = nn then v c else 0 := by
  rw [Psec_eq_diag]
  by_cases h : secOf T c = nn <;> simp [toCLM, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal, secInd, h]

theorem Psec_mem_ker_sector_dev (T : Torus) (nn : SectorLabel T) {v : FockSpace T}
    (hv : v ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T))) :
    toCLM T (Psec T nn) v ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T nn := by
  have hc : Commute (HN T) (Psec T nn) :=
    (isSectorPreserving_iff_commute T (HN T)).mp (HN_isSectorPreserving T) nn
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker, toEuclideanLin_apply_dev] at hv ⊢
    rw [← mul_apply_eq_comp, ← map_mul, hc.eq, map_mul, mul_apply_eq_comp, hv, map_zero]
  · rw [mem_sector_iff]
    intro c hc'
    rw [Psec_apply_dev] at hc'
    by_contra hne
    exact hc' (ite_eq_right hne)

theorem KN_support_dev (T : Torus) {v : FockSpace T}
    (hv : v ∈ ⨆ (nn : SectorLabel T) (_ : (nn.1 : ℕ) + (nn.2 : ℕ) = T.N), sector T nn) (c : Conf (ZMod T.Nφ))
    (hc : v c ≠ 0) : ((secOf T c).1 : ℕ) + ((secOf T c).2 : ℕ) = T.N := by
  revert c
  refine Submodule.iSup_induction (motive := fun w : FockSpace T => ∀ c, w c ≠ 0 →
    ((secOf T c).1 : ℕ) + ((secOf T c).2 : ℕ) = T.N) _ hv ?_ ?_ ?_
  · intro nn w hw c hc
    by_cases hN : (nn.1 : ℕ) + (nn.2 : ℕ) = T.N
    · rw [iSup_pos hN] at hw
      rw [(mem_sector_iff T nn w).1 hw c hc]
      exact hN
    · rw [iSup_neg hN, Submodule.mem_bot] at hw
      subst hw
      simp at hc
  · intro c hc
    simp at hc
  · intro x y hx hy c hc
    by_cases hxc : x c = 0
    · refine hy c fun hyc => hc ?_
      simp [hxc, hyc]
    · exact hx c hxc

theorem KN_support_low_dev (T : Torus) {v : FockSpace T} (hv : v ∈ KN T) (c : Conf (ZMod T.Nφ)) (hc : v c ≠ 0) :
    ((secOf T c).1 : ℕ) + ((secOf T c).2 : ℕ) = T.N ∧
      |(((secOf T c).1 : ℕ) : ℤ) - (((secOf T c).2 : ℕ) : ℤ)| < 2 := by
  unfold KN at hv
  obtain ⟨hk, hs⟩ := Submodule.mem_inf.1 hv
  have hN := KN_support_dev T hs c hc
  refine ⟨hN, ?_⟩
  by_contra h2
  push Not at h2
  have hP := Psec_mem_ker_sector_dev T (secOf T c) hk
  rw [kernel_sector_eq_bot T (secOf T c) hN h2, Submodule.mem_bot] at hP
  have h1 := congrArg (fun w : FockSpace T => w c) hP
  simp [Psec_apply_dev] at h1
  exact hc h1

/-- **Theorem 2.10(ii)** (Theorem C.T2(ii)): "`If $N$ is odd, $\mathcal K_N\cap\sect{((N+1)/2,(N-1)/2)}$ and $\mathcal K_N\cap\sect{((N-1)/2,(N+1)/2)}$ are two-dimensional.`"
— for every odd `N` (at `N = 1` each odd sector is two-dimensional and is the kernel); the expressions are those of
`two_le_finrank_ker_odd` and `hasTwoZeroModes_of_kernel`. -/
theorem finrank_kernel_odd (T : Torus) (hodd : Odd T.N) :
    Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorPlus T)) = 2 ∧
      Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorMinus T)) = 2 := by
  obtain ⟨m, hm⟩ := hodd
  have hn1 : ((oddSectorPlus T).1 : ℕ) = m + 1 := by show (T.N + 1) / 2 = m + 1; omega
  have hm1 : ((oddSectorPlus T).2 : ℕ) = m := by show (T.N - 1) / 2 = m; omega
  have hn2 : ((oddSectorMinus T).1 : ℕ) = m := by show (T.N - 1) / 2 = m; omega
  have hm2 : ((oddSectorMinus T).2 : ℕ) = m + 1 := by show (T.N + 1) / 2 = m + 1; omega
  rw [finrank_ker_eq_finrank_V T (oddSectorPlus T) hn1 hm1, finrank_ker_eq_finrank_V T (oddSectorMinus T) hn2 hm2]
  have hL1 : T.Nφ = 2 * ((m + 1) + m) := by unfold Torus.Nφ; omega
  have hL2 : T.Nφ = 2 * (m + (m + 1)) := by unfold Torus.Nφ; omega
  constructor
  · rw [hL1]
    exact (T2_ii (tauT T) m).1
  · rw [hL2]
    exact (T2_ii (tauT T) m).2

/-- **Theorem C.T2(ii)**: "`So $\dim\ker H=4$.`"
— at odd `N`, `dim 𝒦_N = 4`. -/
theorem finrank_KN_odd (T : Torus) (hodd : Odd T.N) : Module.finrank ℂ (KN T) = 4 := by
  obtain ⟨m, hm⟩ := hodd
  have hNp : ((oddSectorPlus T).1 : ℕ) + ((oddSectorPlus T).2 : ℕ) = T.N := by
    show (T.N + 1) / 2 + (T.N - 1) / 2 = T.N
    omega
  have hNm : ((oddSectorMinus T).1 : ℕ) + ((oddSectorMinus T).2 : ℕ) = T.N := by
    show (T.N - 1) / 2 + (T.N + 1) / 2 = T.N
    omega
  have hpm : oddSectorPlus T ≠ oddSectorMinus T := by
    intro h
    have h1 := congrArg (fun nn : SectorLabel T => (nn.1 : ℕ)) h
    change (T.N + 1) / 2 = (T.N - 1) / 2 at h1
    omega
  have hle : KN T ≤ (LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorPlus T)) ⊔
      (LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorMinus T)) := by
    intro v hv
    have hk := (Submodule.mem_inf.1 hv).1
    have hdec : v = toCLM T (Psec T (oddSectorPlus T)) v + toCLM T (Psec T (oddSectorMinus T)) v := by
      refine PiLp.ext fun c => ?_
      rw [PiLp.add_apply, Psec_apply_dev, Psec_apply_dev]
      by_cases hc : v c = 0
      · simp [hc]
      · obtain ⟨hN, hlt⟩ := KN_support_low_dev T hv c hc
        obtain ⟨hlt1, hlt2⟩ := abs_lt.1 hlt
        rcases (by omega : (((secOf T c).1 : ℕ) = m + 1 ∧ ((secOf T c).2 : ℕ) = m) ∨
            (((secOf T c).1 : ℕ) = m ∧ ((secOf T c).2 : ℕ) = m + 1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hs : secOf T c = oddSectorPlus T := Prod.ext (Fin.ext (by
            show ((secOf T c).1 : ℕ) = (T.N + 1) / 2
            omega)) (Fin.ext (by
            show ((secOf T c).2 : ℕ) = (T.N - 1) / 2
            omega))
          rw [ite_eq_left hs, ite_eq_right (fun h => hpm (hs.symm.trans h)), add_zero]
        · have hs : secOf T c = oddSectorMinus T := Prod.ext (Fin.ext (by
            show ((secOf T c).1 : ℕ) = (T.N - 1) / 2
            omega)) (Fin.ext (by
            show ((secOf T c).2 : ℕ) = (T.N + 1) / 2
            omega))
          rw [ite_eq_right (fun h => hpm (h.symm.trans hs)), ite_eq_left hs, zero_add]
    rw [hdec]
    exact Submodule.add_mem_sup (Psec_mem_ker_sector_dev T _ hk) (Psec_mem_ker_sector_dev T _ hk)
  have hge : (LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorPlus T)) ⊔
      (LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorMinus T)) ≤ KN T := by
    refine sup_le ?_ ?_
    · rw [← KN_inf_sector T _ hNp]
      exact inf_le_left
    · rw [← KN_inf_sector T _ hNm]
      exact inf_le_left
  have hinf : (LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorPlus T)) ⊓
      (LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorMinus T)) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    have h1 := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hw).1).2
    have h2 := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hw).2).2
    refine PiLp.ext fun c => ?_
    by_contra hne
    exact hpm (((mem_sector_iff T _ w).1 h1 c hne).symm.trans ((mem_sector_iff T _ w).1 h2 c hne))
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorPlus T))
    (LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorMinus T))
  rw [hinf, finrank_bot, add_zero, (finrank_kernel_odd T ⟨m, hm⟩).1, (finrank_kernel_odd T ⟨m, hm⟩).2] at hfr
  rw [le_antisymm hle hge, hfr]

/-- **Theorem 2.10(iii)** (Theorem C.T2(iii)): "`If $N$ is even, $\mathcal K_N\subset\sect{(N/2,N/2)}$ and $\dim\mathcal K_N=10$.`"
— the dimension of the kernel in the sector `(N/2, N/2)`, in the expression of `ten_le_finrank_ker` and
`hasTenZeroModes_of_kernel`. -/
theorem finrank_kernel_half (T : Torus) (heven : Even T.N) :
    Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (halfSector T)) = 10 := by
  obtain ⟨q, hq⟩ : ∃ q, T.N = 2 * (q + 1) := by
    obtain ⟨r, hr⟩ := heven
    exact ⟨r - 1, by have := T.N_pos; omega⟩
  have hn : ((halfSector T).1 : ℕ) = q + 1 := by show T.N / 2 = q + 1; omega
  have hm : ((halfSector T).2 : ℕ) = q + 1 := by show T.N / 2 = q + 1; omega
  rw [finrank_ker_eq_finrank_V T (halfSector T) hn hm]
  have hL : T.Nφ = 2 * ((q + 1) + (q + 1)) := by unfold Torus.Nφ; omega
  rw [hL]
  exact T2_iii (tauT T) q

/-- **Theorem 2.10(iii)** (Theorem C.T2(iii)): "`If $N$ is even, $\mathcal K_N\subset\sect{(N/2,N/2)}$ and $\dim\mathcal K_N=10$.`"
— the inclusion (from (i): every other `N`-electron sector has `|n_↑ − n_↓| ≥ 2` at even `N`). -/
theorem KN_le_halfSector (T : Torus) (heven : Even T.N) : KN T ≤ sector T (halfSector T) := by
  intro v hv
  rw [mem_sector_iff]
  intro c hc
  obtain ⟨hN, hlt⟩ := KN_support_low_dev T hv c hc
  obtain ⟨hlt1, hlt2⟩ := abs_lt.1 hlt
  obtain ⟨r, hr⟩ := heven
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · show ((secOf T c).1 : ℕ) = T.N / 2
    omega
  · show ((secOf T c).2 : ℕ) = T.N / 2
    omega

/-- **Theorem 2.10(iii)** (Theorem C.T2(iii)): "`If $N$ is even, $\mathcal K_N\subset\sect{(N/2,N/2)}$ and $\dim\mathcal K_N=10$.`"
— `dim 𝒦_N = 10`. -/
theorem finrank_KN_even (T : Torus) (heven : Even T.N) : Module.finrank ℂ (KN T) = 10 := by
  have hN : ((halfSector T).1 : ℕ) + ((halfSector T).2 : ℕ) = T.N := by
    obtain ⟨r, hr⟩ := heven
    show T.N / 2 + T.N / 2 = T.N
    omega
  calc Module.finrank ℂ (KN T) = Module.finrank ℂ ↥(KN T ⊓ sector T (halfSector T)) := by
        rw [inf_eq_left.2 (KN_le_halfSector T heven)]
    _ = Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
          (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (halfSector T)) := by
        rw [KN_inf_sector T (halfSector T) hN]
    _ = 10 := finrank_kernel_half T heven

/-! ## The spanning statements -/

/-! ### Proof device for the spanning statements (proof phase, round three; not a statement of the paper): an
independent family of a finite-dimensional subspace, of the size of its dimension, spans it (Mathlib's
`finrank_span_eq_card`, `Submodule.eq_of_le_of_finrank_eq`); the membership of the given vectors in the kernel is
Lemma C.A (`lemA_HN`) with (C1), (C2) of the numerators (F1-lower's `…_numerator_props`), and their independence is
F1-lower's `explicit_…_linearIndependent` through `canon` (the route of `exists_ten_zero_modes`) -/

theorem eq_span_of_li_dev {ι : Type*} [Fintype ι] {E : Type*} [AddCommGroup E] [Module ℂ E] (W : Submodule ℂ E)
    [FiniteDimensional ℂ W] {v : ι → E} (hv : ∀ i, v i ∈ W) (hli : LinearIndependent ℂ v)
    (hcard : Fintype.card ι = Module.finrank ℂ W) : W = Submodule.span ℂ (Set.range v) := by
  have hle : Submodule.span ℂ (Set.range v) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hv i
  have hfr : Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = Module.finrank ℂ W := by
    rw [finrank_span_eq_card hli, hcard]
  exact (Submodule.eq_of_le_of_finrank_eq hle hfr).symm

/-- **Theorem 2.10(iii)** (Theorem C.T2(iii): "`It is spanned by $F(U)J^2g$ with $g\in\{d^{(p)}_\varepsilon:\varepsilon\in\{\pm1\}^2\}\cup\{f_5^{(p)}\}$ and $F\in\kzTh_2[\varepsilon]$, two for each $g$.`"):
at `N = 2p`, `p = q + 1`, any vectors of the sector `(N/2, N/2)` whose canonical components are the numerators of
`F(U) J² g`, with two independent `F ∈ Θ_2[ε]` for each of the five `g`, span the kernel in the sector (the vectors of
`exists_ten_zero_modes`). -/
theorem kernel_half_eq_span (T : Torus) (q : ℕ) (hq : T.N = 2 * (q + 1)) (F : Option Eps → Fin 2 → ℂ → ℂ)
    (hF : ∀ e r, F e r ∈ Θ2 (tauT T) (epsOf e)) (hFi : ∀ e, LinearIndependent ℂ (F e))
    (v : Option Eps × Fin 2 → FockSpace T) (hv : ∀ i, v i ∈ sector T (halfSector T))
    (hnum : ∀ i, IsNumerator (tauT T) (q + 1) (q + 1) (F i.1 i.2) (gEven (tauT T) q i.1)
      (canon T (q + 1) (q + 1) (v i))) :
    LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) ⊓
      sector T (halfSector T) = Submodule.span ℂ (Set.range v) := by
  have heven : Even T.N := ⟨q + 1, by omega⟩
  have hn : ((halfSector T).1 : ℕ) = q + 1 := by show T.N / 2 = q + 1; omega
  have hm : ((halfSector T).2 : ℕ) = q + 1 := by show T.N / 2 = q + 1; omega
  have hmem : ∀ i, v i ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (halfSector T) := by
    rintro ⟨e, r⟩
    have hC : C1 (tauT T) (q + 1) (q + 1) (canon T (q + 1) (q + 1) (v (e, r))) ∧
        C2 (q + 1) (q + 1) (canon T (q + 1) (q + 1) (v (e, r))) := by
      cases e with
      | none => exact (f5_numerator_props (tauT T) q (hF none r) (hnum (none, r))).2
      | some ε => exact (dEps_numerator_props (tauT T) ε (q + 1) (hF (some ε) r) (hnum (some ε, r))).2
    exact Submodule.mem_inf.2 ⟨lemA_HN T (halfSector T) hn hm (hv _) hC.1 hC.2, hv _⟩
  have hli : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (canon T (q + 1) (q + 1)) (explicit_even_linearIndependent (tauT T) q F hF hFi _ hnum)
  refine eq_span_of_li_dev _ hmem hli ?_
  rw [finrank_kernel_half T heven, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
  rfl

/-- **Theorem 2.10(ii)** (Theorem C.T2(ii): "`For odd $N$, $\dim\ker H|_{S_z=+1/2}=2$. The kernel is spanned by`" the two
states of `g_{2m+1}`, "`These are the two centre-of-mass partners ($T_1$ maps one to the other) of the relative state in the sector $(T_K^2,T_1^2)=(1,1)$.`"):
at `N = 2m + 1`, any two vectors of the sector `((N+1)/2, (N−1)/2)` whose canonical components are the numerators of
`F(U) J² g_{2m+1}`, `F` running over an independent pair of `Θ_2[(1,1)]` (for instance F1-lower's `ϑ[0,0](2U|2τ)`,
`ϑ[½,0](2U|2τ)`, `thetaK_linearIndependent`), span the kernel in the sector. -/
theorem kernel_oddPlus_eq_span (T : Torus) (m : ℕ) (hm : T.N = 2 * m + 1) (F : Fin 2 → ℂ → ℂ)
    (hF : ∀ r, F r ∈ Θ2 (tauT T) .pp) (hFi : LinearIndependent ℂ F) (v : Fin 2 → FockSpace T)
    (hv : ∀ r, v r ∈ sector T (oddSectorPlus T))
    (hnum : ∀ r, IsNumerator (tauT T) (m + 1) m (F r) (gOdd (tauT T) m) (canon T (m + 1) m (v r))) :
    LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) ⊓
      sector T (oddSectorPlus T) = Submodule.span ℂ (Set.range v) := by
  have hn : ((oddSectorPlus T).1 : ℕ) = m + 1 := by show (T.N + 1) / 2 = m + 1; omega
  have hm' : ((oddSectorPlus T).2 : ℕ) = m := by show (T.N - 1) / 2 = m; omega
  have hmem : ∀ r, v r ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorPlus T) := by
    intro r
    obtain ⟨-, h1, h2⟩ := gOdd_numerator_props (tauT T) m (hF r) (hnum r)
    exact Submodule.mem_inf.2 ⟨lemA_HN T (oddSectorPlus T) hn hm' (hv r) h1 h2, hv r⟩
  have hli : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (canon T (m + 1) m) (explicit_odd_linearIndependent (tauT T) m F hF hFi _ hnum)
  refine eq_span_of_li_dev _ hmem hli ?_
  rw [(finrank_kernel_odd T ⟨m, hm⟩).1, Fintype.card_fin]

/-- **Theorem 2.10(ii)** (Theorem C.T2(ii): "`$S_z=-\tfrac12$ is the same with the species exchanged.`"): the kernel in the
sector `((N−1)/2, (N+1)/2)` is spanned by the two states of `g_{2m+1}(y; x)`. -/
theorem kernel_oddMinus_eq_span (T : Torus) (m : ℕ) (hm : T.N = 2 * m + 1) (F : Fin 2 → ℂ → ℂ)
    (hF : ∀ r, F r ∈ Θ2 (tauT T) .pp) (hFi : LinearIndependent ℂ F) (v : Fin 2 → FockSpace T)
    (hv : ∀ r, v r ∈ sector T (oddSectorMinus T))
    (hnum : ∀ r, IsNumerator (tauT T) m (m + 1) (F r) (gOddSwap (tauT T) m) (canon T m (m + 1) (v r))) :
    LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) ⊓
      sector T (oddSectorMinus T) = Submodule.span ℂ (Set.range v) := by
  have hn : ((oddSectorMinus T).1 : ℕ) = m := by show (T.N - 1) / 2 = m; omega
  have hm' : ((oddSectorMinus T).2 : ℕ) = m + 1 := by show (T.N + 1) / 2 = m + 1; omega
  have hmem : ∀ r, v r ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorMinus T) := by
    intro r
    obtain ⟨-, h1, h2⟩ := gOddSwap_numerator_props (tauT T) m (hF r) (hnum r)
    exact Submodule.mem_inf.2 ⟨lemA_HN T (oddSectorMinus T) hn hm' (hv r) h1 h2, hv r⟩
  have hli : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (canon T m (m + 1)) (explicit_oddSwap_linearIndependent (tauT T) m F hF hFi _ hnum)
  refine eq_span_of_li_dev _ hmem hli ?_
  rw [(finrank_kernel_odd T ⟨m, hm⟩).2, Fintype.card_fin]

/-! ## The discharges of the named hypotheses (one-line derivations through the bridges of `Assembly.Main`) -/

/-- **Theorem 2.10(iii)** with `H_N ≥ 0`: (2.8), "`E_1(N)=\cdots=E_{10}(N)=0<E_{11}(N)`", at every even `N` — the named
hypothesis `HasTenZeroModes` of the reviewed main theorems, discharged (`hasTenZeroModes_of_kernel`). -/
theorem hasTenZeroModes (T : Torus) (heven : Even T.N) : HasTenZeroModes T :=
  hasTenZeroModes_of_kernel T heven (finrank_kernel_half T heven)

/-- **Theorem 2.10(ii)** with `H_N ≥ 0`: "`and at odd $N\ge3$ the eigenvalues in each of the sectors $((N\pm1)/2,(N\mp1)/2)$ satisfy $E_1(N)=E_2(N)=0<E_3(N)$.`"
— the named hypothesis `HasTwoZeroModes` in both odd sectors, discharged (`hasTwoZeroModes_of_kernel`). -/
theorem hasTwoZeroModes (T : Torus) (hodd : Odd T.N) (h3 : 3 ≤ T.N) :
    HasTwoZeroModes T (oddSectorPlus T) ∧ HasTwoZeroModes T (oddSectorMinus T) :=
  ⟨(hasTwoZeroModes_of_kernel T hodd h3).1 (finrank_kernel_odd T hodd).1,
    (hasTwoZeroModes_of_kernel T hodd h3).2 (finrank_kernel_odd T hodd).2⟩

end HRTorus.ZeroModes

end -- noncomputable section
