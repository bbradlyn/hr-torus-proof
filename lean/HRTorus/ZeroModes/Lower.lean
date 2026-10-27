import HRTorus.ZeroModes.Explicit
import HRTorus.Assembly.Main

/-!
# The lower bound on the zero modes and the unconditional main theorems (`ZeroModes.Lower`)

Written by Claude Opus 5.5 (an AI model), 2026-10-26. **The definitions and statements were written first
and reviewed against the paper (the statement phase, with the one-line derivations at the end of the module: the
reviewed statements of `Assembly.Main` from the strengthened ones, the unconditional theorems from the strengthened
ones and the lower bounds). The proof phase is complete: every reviewed statement of this module is proved (proof
phase round three), no theorem of this module is `sorry`, and the proof devices are marked as such, in their own
sections.**
The paper: the HR paper — Theorem 2.10 `thm:kernel` (`sections/02-setting.tex`) in the half that the explicit states
deliver (a lower bound on the dimension of the kernel), proved by Appendix C (`appendices/C-kernel.tex`, Theorem
C.`T2`(ii)–(iii) and Proposition C.`explicit`); Theorem 8.1, Corollaries 8.2 and 8.4 (`sections/08-hollow-core.tex`)
without the zero-mode hypotheses.

## What the block delivers, and why it suffices

The reviewed main theorems of `Assembly.Main` (`hollow_core_index`, `hollow_core_E11_tendsto`, `odd_E3_tendsto`,
`odd_many_small`, `uniform_E11_tendsto`, `uniform_E11_eventually`) assume `HasTenZeroModes`
("`E_1(N)=\cdots=E_{10}(N)=0<E_{11}(N)`") or `HasTwoZeroModes` ("`$E_1(N)=E_2(N)=0<E_3(N)$`"); their proofs use the
equalities only, never the strict inequality (the lower side of a limit is `H_N ≥ 0`). This module:
* states the **lower bounds** in the form of the bridges `hasTenZeroModes_of_kernel`, `hasTwoZeroModes_of_kernel`:
  `10 ≤ dim(ker H_N ∩ 𝓗^{(N/2,N/2)})` at even `N`, `2 ≤ dim(ker H_N ∩ 𝓗^{((N±1)/2,(N∓1)/2)})` at odd `N ≥ 3`
  (from the explicit states of `ZeroModes.Explicit`, the dictionary of `ZeroModes.Canonical` and Lemma C.A);
* defines the **weaker named hypotheses** `HasAtLeastTenZeroModes`, `HasAtLeastTwoZeroModes` (the equalities only) and
  proves them from the lower bounds with `H_N ≥ 0` (`zero_modes_le_dev`, a bridge like `zero_modes_dev` without the
  clause `0 < E_{p+1}`);
* states the **strengthened main theorems** (primed names) with the weaker hypotheses and otherwise verbatim the
  reviewed statements, and derives the reviewed statements from them in a line (`…_of'`), so that block E's reviewed
  97 statements stay verbatim;
* states the **unconditional theorems**, with no zero-mode hypothesis — the block's product.

The torus is block A's rectangular `Torus`; Appendix C's `τ` is `tauT T = iL_x/L_y`.
-/

open Complex Filter Topology
open scoped Real UpperHalfPlane

noncomputable section

namespace HRTorus.ZeroModes

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian HRTorus.Assembly
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op)

/-! ### Proof devices for the explicit zero modes (proof phase, round three; not statements of the paper)

Two independent vectors of the two-dimensional `Θ_2[ε]` (`exists_Θ2_pair_dev`, from `finrank_Θ2`); a function of the
shape that satisfies (C1) and (C2) is the canonical component of a vector of the sector (`canon_surj`) in the kernel of
`H_N` (Lemma C.A, `lemA_HN`) (`zero_mode_of_numerator_dev`); independence passes from the canonical components to the
vectors because `canon` is linear (`LinearIndependent.of_comp`), and independent vectors of a subspace bound its
dimension below (`card_le_finrank_of_mem_dev`). -/

theorem exists_Θ2_pair_dev (τ : ℍ) (ε : Eps) :
    ∃ F : Fin 2 → ℂ → ℂ, (∀ r, F r ∈ Θ2 τ ε) ∧ LinearIndependent ℂ F := by
  have h2 : 0 < Module.finrank ℂ (Θ2 (τ : ℂ) ε) := by rw [finrank_Θ2]; norm_num
  have : Module.Finite ℂ (Θ2 (τ : ℂ) ε) := Module.finite_of_finrank_pos h2
  let b := Module.finBasisOfFinrankEq ℂ (Θ2 (τ : ℂ) ε) (finrank_Θ2 τ ε)
  exact ⟨fun r => (b r : ℂ → ℂ), fun r => (b r).2,
    b.linearIndependent.map' (Θ2 (τ : ℂ) ε).subtype (Submodule.ker_subtype _)⟩

theorem zero_mode_of_numerator_dev (T : Torus) (nn : SectorLabel T) {n m : ℕ} (hn : (nn.1 : ℕ) = n)
    (hm : (nn.2 : ℕ) = m) {f : (Fin (n + m) → ℂ) → ℂ} (hf : IsCanonShape (tauT T) T.Nφ n m f)
    (h1 : C1 (tauT T) n m f) (h2 : C2 n m f) :
    ∃ Ψ, Ψ ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) ⊓
      sector T nn ∧ canon T n m Ψ = f := by
  obtain ⟨Ψ, hΨ, hΨf⟩ := canon_surj T nn hn hm hf
  have h1' : C1 (tauT T) n m (canon T n m Ψ) := by rw [hΨf]; exact h1
  have h2' : C2 n m (canon T n m Ψ) := by rw [hΨf]; exact h2
  exact ⟨Ψ, Submodule.mem_inf.2 ⟨lemA_HN T nn hn hm hΨ h1' h2', hΨ⟩, hΨf⟩

theorem card_le_finrank_of_mem_dev {ι : Type*} [Fintype ι] {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (W : Submodule ℂ E) {v : ι → E} (hv : ∀ i, v i ∈ W) (hli : LinearIndependent ℂ v) :
    Fintype.card ι ≤ Module.finrank ℂ W := by
  have hli' : LinearIndependent ℂ (fun i => (⟨v i, hv i⟩ : W)) := LinearIndependent.of_comp W.subtype hli
  exact hli'.fintype_card_le_finrank

/-! ## The explicit zero modes in the Fock space -/

/-- **Theorem 2.10(iii)**, the lower half (Theorem C.T2(iii): "`It is spanned by $F(U)J^2g$ with $g\in\{d^{(p)}_\varepsilon:\varepsilon\in\{\pm1\}^2\}\cup\{f_5^{(p)}\}$ and $F\in\kzTh_2[\varepsilon]$, two for each $g$.`"):
at `N = 2p`, `p = q + 1`, there are ten linearly independent vectors in `ker H_N ∩ 𝓗^{(N/2,N/2)}` whose canonical
components are the numerators of `F(U) J² g`, with two independent `F ∈ Θ_2[ε]` for each of the five `g`. -/
theorem exists_ten_zero_modes (T : Torus) (q : ℕ) (hq : T.N = 2 * (q + 1)) :
    ∃ (F : Option Eps → Fin 2 → ℂ → ℂ) (v : Option Eps × Fin 2 → FockSpace T),
      (∀ e r, F e r ∈ Θ2 (tauT T) (epsOf e)) ∧ (∀ e, LinearIndependent ℂ (F e)) ∧
      (∀ i, v i ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (halfSector T)) ∧
      (∀ i, IsNumerator (tauT T) (q + 1) (q + 1) (F i.1 i.2) (gEven (tauT T) q i.1)
        (canon T (q + 1) (q + 1) (v i))) ∧
      LinearIndependent ℂ v := by
  have hL : T.Nφ = 2 * ((q + 1) + (q + 1)) := by unfold Torus.Nφ; omega
  have hn : ((halfSector T).1 : ℕ) = q + 1 := by show T.N / 2 = q + 1; omega
  have hm : ((halfSector T).2 : ℕ) = q + 1 := by show T.N / 2 = q + 1; omega
  choose F hF hFi using fun e : Option Eps => exists_Θ2_pair_dev (tauT T) (epsOf e)
  have hnum : ∀ i : Option Eps × Fin 2, ∃ f : (Fin ((q + 1) + (q + 1)) → ℂ) → ℂ,
      IsNumerator (tauT T) (q + 1) (q + 1) (F i.1 i.2) (gEven (tauT T) q i.1) f ∧
      IsCanonShape (tauT T) T.Nφ (q + 1) (q + 1) f ∧ C1 (tauT T) (q + 1) (q + 1) f ∧ C2 (q + 1) (q + 1) f := by
    rintro ⟨e, r⟩
    cases e with
    | none =>
      obtain ⟨f, hf⟩ := f5_numerator_exists (tauT T) q (hF none r)
      obtain ⟨hs, h1, h2⟩ := f5_numerator_props (tauT T) q (hF none r) hf
      exact ⟨f, hf, by rw [hL]; exact hs, h1, h2⟩
    | some ε =>
      obtain ⟨f, hf⟩ := dEps_numerator_exists (tauT T) ε (q + 1) (hF (some ε) r)
      obtain ⟨hs, h1, h2⟩ := dEps_numerator_props (tauT T) ε (q + 1) (hF (some ε) r) hf
      exact ⟨f, hf, by rw [hL]; exact hs, h1, h2⟩
  choose f hf hfs hf1 hf2 using hnum
  choose v hvmem hvf using fun i => zero_mode_of_numerator_dev T (halfSector T) hn hm (hfs i) (hf1 i) (hf2 i)
  refine ⟨F, v, hF, hFi, hvmem, fun i => by rw [hvf i]; exact hf i, ?_⟩
  refine LinearIndependent.of_comp (canon T (q + 1) (q + 1)) ?_
  have e : ⇑(canon T (q + 1) (q + 1)) ∘ v = f := funext hvf
  rw [e]
  exact explicit_even_linearIndependent (tauT T) q F hF hFi f hf

/-- **Theorem 2.10(ii)**, the lower half in the sector `((N+1)/2, (N−1)/2)` (Theorem C.T2(ii): "`For odd $N$, $\dim\ker H|_{S_z=+1/2}=2$. The kernel is spanned by`"
the two states of `g_{2m+1}`): at `N = 2m + 1`, two linearly independent vectors of the kernel whose canonical
components are the numerators of `F(U) J² g_{2m+1}`, `F ∈ Θ_2[(1,1)]`. -/
theorem exists_two_zero_modes_plus (T : Torus) (m : ℕ) (hm : T.N = 2 * m + 1) :
    ∃ (F : Fin 2 → ℂ → ℂ) (v : Fin 2 → FockSpace T),
      (∀ r, F r ∈ Θ2 (tauT T) .pp) ∧ LinearIndependent ℂ F ∧
      (∀ r, v r ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorPlus T)) ∧
      (∀ r, IsNumerator (tauT T) (m + 1) m (F r) (gOdd (tauT T) m) (canon T (m + 1) m (v r))) ∧
      LinearIndependent ℂ v := by
  have hL : T.Nφ = 2 * ((m + 1) + m) := by unfold Torus.Nφ; omega
  have hn : ((oddSectorPlus T).1 : ℕ) = m + 1 := by show (T.N + 1) / 2 = m + 1; omega
  have hm' : ((oddSectorPlus T).2 : ℕ) = m := by show (T.N - 1) / 2 = m; omega
  obtain ⟨F, hF, hFi⟩ := exists_Θ2_pair_dev (tauT T) .pp
  have hnum : ∀ r : Fin 2, ∃ f : (Fin ((m + 1) + m) → ℂ) → ℂ,
      IsNumerator (tauT T) (m + 1) m (F r) (gOdd (tauT T) m) f ∧
      IsCanonShape (tauT T) T.Nφ (m + 1) m f ∧ C1 (tauT T) (m + 1) m f ∧ C2 (m + 1) m f := by
    intro r
    obtain ⟨f, hf⟩ := gOdd_numerator_exists (tauT T) m (hF r)
    obtain ⟨hs, h1, h2⟩ := gOdd_numerator_props (tauT T) m (hF r) hf
    exact ⟨f, hf, by rw [hL]; exact hs, h1, h2⟩
  choose f hf hfs hf1 hf2 using hnum
  choose v hvmem hvf using fun r => zero_mode_of_numerator_dev T (oddSectorPlus T) hn hm' (hfs r) (hf1 r) (hf2 r)
  refine ⟨F, v, hF, hFi, hvmem, fun r => by rw [hvf r]; exact hf r, ?_⟩
  refine LinearIndependent.of_comp (canon T (m + 1) m) ?_
  have e : ⇑(canon T (m + 1) m) ∘ v = f := funext hvf
  rw [e]
  exact explicit_odd_linearIndependent (tauT T) m F hF hFi f hf

/-- **Theorem 2.10(ii)**, the lower half in the sector `((N−1)/2, (N+1)/2)` ("`$S_z=-\tfrac12$ is the same with the species exchanged.`"). -/
theorem exists_two_zero_modes_minus (T : Torus) (m : ℕ) (hm : T.N = 2 * m + 1) :
    ∃ (F : Fin 2 → ℂ → ℂ) (v : Fin 2 → FockSpace T),
      (∀ r, F r ∈ Θ2 (tauT T) .pp) ∧ LinearIndependent ℂ F ∧
      (∀ r, v r ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorMinus T)) ∧
      (∀ r, IsNumerator (tauT T) m (m + 1) (F r) (gOddSwap (tauT T) m) (canon T m (m + 1) (v r))) ∧
      LinearIndependent ℂ v := by
  have hL : T.Nφ = 2 * (m + (m + 1)) := by unfold Torus.Nφ; omega
  have hn : ((oddSectorMinus T).1 : ℕ) = m := by show (T.N - 1) / 2 = m; omega
  have hm' : ((oddSectorMinus T).2 : ℕ) = m + 1 := by show (T.N + 1) / 2 = m + 1; omega
  obtain ⟨F, hF, hFi⟩ := exists_Θ2_pair_dev (tauT T) .pp
  have hnum : ∀ r : Fin 2, ∃ f : (Fin (m + (m + 1)) → ℂ) → ℂ,
      IsNumerator (tauT T) m (m + 1) (F r) (gOddSwap (tauT T) m) f ∧
      IsCanonShape (tauT T) T.Nφ m (m + 1) f ∧ C1 (tauT T) m (m + 1) f ∧ C2 m (m + 1) f := by
    intro r
    obtain ⟨f, hf⟩ := gOddSwap_numerator_exists (tauT T) m (hF r)
    obtain ⟨hs, h1, h2⟩ := gOddSwap_numerator_props (tauT T) m (hF r) hf
    exact ⟨f, hf, by rw [hL]; exact hs, h1, h2⟩
  choose f hf hfs hf1 hf2 using hnum
  choose v hvmem hvf using fun r => zero_mode_of_numerator_dev T (oddSectorMinus T) hn hm' (hfs r) (hf1 r) (hf2 r)
  refine ⟨F, v, hF, hFi, hvmem, fun r => by rw [hvf r]; exact hf r, ?_⟩
  refine LinearIndependent.of_comp (canon T m (m + 1)) ?_
  have e : ⇑(canon T m (m + 1)) ∘ v = f := funext hvf
  rw [e]
  exact explicit_oddSwap_linearIndependent (tauT T) m F hF hFi f hf

/-! ## The lower bounds, in the form of the bridges of `Assembly.Main` -/

/-- **Theorem 2.10(iii)**, lower half: "`If $N$ is even, $\mathcal K_N\subset\sect{(N/2,N/2)}$ and $\dim\mathcal K_N=10$.`"
— `dim(ker H_N ∩ 𝓗^{(N/2,N/2)}) ≥ 10` for every even `N` (`N > 0` is a field of `Torus`); the expression is the one of
`hasTenZeroModes_of_kernel`. -/
theorem ten_le_finrank_ker (T : Torus) (heven : Even T.N) :
    10 ≤ Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (halfSector T)) := by
  have hN := T.N_pos
  obtain ⟨r, hr⟩ := heven
  obtain ⟨_, v, -, -, hv, -, hli⟩ := exists_ten_zero_modes T (r - 1) (by omega)
  have h := card_le_finrank_of_mem_dev _ hv hli
  have h4 : Fintype.card Eps = 4 := rfl
  rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, h4] at h
  omega

/-- **Theorem 2.10(ii)**, lower half: "`If $N$ is odd, $\mathcal K_N\cap\sect{((N+1)/2,(N-1)/2)}$ and $\mathcal K_N\cap\sect{((N-1)/2,(N+1)/2)}$ are two-dimensional.`"
— at least two-dimensional, for odd `N ≥ 3`; the expressions are those of `hasTwoZeroModes_of_kernel`. -/
theorem two_le_finrank_ker_odd (T : Torus) (hodd : Odd T.N) (h3 : 3 ≤ T.N) :
    2 ≤ Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorPlus T)) ∧
      2 ≤ Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorMinus T)) := by
  have _ := h3
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨_, v, -, -, hv, -, hli⟩ := exists_two_zero_modes_plus T m hm
  obtain ⟨_, w, -, -, hw, -, hliw⟩ := exists_two_zero_modes_minus T m hm
  have h1 := card_le_finrank_of_mem_dev _ hv hli
  have h2 := card_le_finrank_of_mem_dev _ hw hliw
  rw [Fintype.card_fin] at h1 h2
  exact ⟨h1, h2⟩

/-! ## The weaker named hypotheses -/

/-- The equalities of (2.8), "`E_1(N)=\cdots=E_{10}(N)=0<E_{11}(N)`", without `0 < E_{11}`: at least ten zero modes in the
sector `(N/2, N/2)`. -/
def HasAtLeastTenZeroModes (T : Torus) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ 10 → hcEig T (halfSector T) k = 0

/-- The odd case, "`$E_1(N)=E_2(N)=0<E_3(N)$`", without `0 < E_3`: at least two zero modes in a sector. -/
def HasAtLeastTwoZeroModes (T : Torus) (nn : SectorLabel T) : Prop :=
  hcEig T nn 1 = 0 ∧ hcEig T nn 2 = 0

/-- The bridge without the strict clause (a proof device, like `zero_modes_dev`): with `H_N ≥ 0`, a kernel of dimension
at least `z` in a sector gives `E_1 = ⋯ = E_z = 0`. -/
theorem zero_modes_le_dev (T : Torus) (nn : SectorLabel T) (z : ℕ)
    (hz : z ≤ Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T nn)) :
    ∀ k, 1 ≤ k → k ≤ z → secEig T (HN T) nn k = 0 := by
  classical
  intro k hk1 hkz
  have hcard := card_secEig_eq (HN_isSelfAdjoint T) (HN_isSectorPreserving T) nn 0
  rw [Complex.ofReal_zero, Module.End.eigenspace_zero] at hcard
  have hmono := secEig_mono T (HN T) nn
  have hnn := secEig_HN_nonneg T nn
  by_contra hne
  have hk : 0 < secEig T (HN T) nn k := lt_of_le_of_ne (hnn k) (Ne.symm hne)
  have hsub : (Finset.Icc 1 (Module.finrank ℂ (sector T nn))).filter (fun k' => secEig T (HN T) nn k' = 0) ⊆
      Finset.Icc 1 (k - 1) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    rw [Finset.mem_Icc]
    refine ⟨hj.1.1, ?_⟩
    by_contra hjk
    have : secEig T (HN T) nn k ≤ secEig T (HN T) nn j := hmono (by omega)
    linarith [hj.2]
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc, hcard] at this
  omega

/-- **Theorem 2.10(iii)** with `H_N ≥ 0`: at least ten zero modes at every even `N`. -/
theorem hasAtLeastTenZeroModes (T : Torus) (heven : Even T.N) : HasAtLeastTenZeroModes T := by
  intro k h1 h2
  exact zero_modes_le_dev T (halfSector T) 10 (ten_le_finrank_ker T heven) k h1 h2

/-- **Theorem 2.10(ii)** with `H_N ≥ 0`: at least two zero modes in each odd sector at odd `N ≥ 3`. -/
theorem hasAtLeastTwoZeroModes (T : Torus) (hodd : Odd T.N) (h3 : 3 ≤ T.N) :
    HasAtLeastTwoZeroModes T (oddSectorPlus T) ∧ HasAtLeastTwoZeroModes T (oddSectorMinus T) := by
  obtain ⟨hp, hm⟩ := two_le_finrank_ker_odd T hodd h3
  exact ⟨⟨zero_modes_le_dev T _ 2 hp 1 le_rfl (by norm_num), zero_modes_le_dev T _ 2 hp 2 (by norm_num) le_rfl⟩,
    ⟨zero_modes_le_dev T _ 2 hm 1 le_rfl (by norm_num), zero_modes_le_dev T _ 2 hm 2 (by norm_num) le_rfl⟩⟩

/-- The reviewed hypothesis implies the weaker one. -/
theorem hasAtLeastTen_of_hasTen {T : Torus} (h : HasTenZeroModes T) : HasAtLeastTenZeroModes T :=
  h.1

/-- The reviewed odd hypothesis implies the weaker one. -/
theorem hasAtLeastTwo_of_hasTwo {T : Torus} {nn : SectorLabel T} (h : HasTwoZeroModes T nn) :
    HasAtLeastTwoZeroModes T nn :=
  ⟨h.1, h.2.1⟩

/-! ## The strengthened main theorems (the reviewed statements with the weaker hypotheses) -/

/-- **Theorem 8.1(i)**: "`If for some $p\in\N$, $\Delta\ge0$ and $\gamma>2\Delta$ the inequalities $E_p(N)-E_1(N)\le\Delta$ and $E_{p+1}(N)-E_p(N)\ge\gamma$ hold for infinitely many even $N$, then $p\in4\Z$ and $p\ge12$.`"
— `hollow_core_index` with `HasAtLeastTenZeroModes` for `HasTenZeroModes`. -/
theorem hollow_core_index' (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, 0 < N → Even N → HasAtLeastTenZeroModes (rectTorus lam hlam N))
    (p : ℕ) (Δ γ : ℝ) (hΔ : 0 ≤ Δ) (hγ : 2 * Δ < γ)
    (hinf : {N : ℕ | Even N ∧ evenEig lam hlam N p - evenEig lam hlam N 1 ≤ Δ ∧
      γ ≤ evenEig lam hlam N (p + 1) - evenEig lam hlam N p}.Infinite) :
    4 ∣ p ∧ 12 ≤ p := by
  have h4 := hollow_core_index_four_dvd lam hlam p Δ γ hΔ hγ hinf
  refine ⟨h4, ?_⟩
  obtain ⟨N, hN, hNpos⟩ := hinf.exists_gt 0
  obtain ⟨heven, -, hgap⟩ := hN
  have hp1 : 1 ≤ p := (one_le_p_lt_finrank (by linarith) hgap).1
  have hz : ∀ k : ℕ, 1 ≤ k → k ≤ 10 → evenEig lam hlam N k = 0 := hzero N hNpos heven
  by_contra hlt
  push Not at hlt
  have hp10 : 10 ≤ p := by
    by_contra h
    push Not at h
    rw [hz (p + 1) (by omega) (by omega), hz p hp1 (by omega)] at hgap
    linarith
  omega

/-- **Theorem 8.1(ii)**: "`$E_{11}(N)\to0$ as $N\to\infty$ through the even integers.`" — `hollow_core_E11_tendsto` with
`HasAtLeastTenZeroModes`. -/
theorem hollow_core_E11_tendsto' (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, 0 < N → Even N → HasAtLeastTenZeroModes (rectTorus lam hlam N)) :
    Tendsto (fun N => evenEig lam hlam N 11) (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 0) := by
  -- `Assembly.Main`'s proof of `hollow_core_E11_tendsto` under the weaker hypothesis; the lower half of the limit is
  -- `H_N ≥ 0` (`secEig_HN_nonneg`) instead of the clause `0 < E_{11}`
  rw [tendsto_order]
  refine ⟨fun a ha => Filter.Eventually.of_forall fun N => lt_of_lt_of_le ha (secEig_HN_nonneg _ _ 11),
    fun a ha => ?_⟩
  by_contra h
  rw [Filter.not_eventually, Filter.frequently_inf_principal, Nat.frequently_atTop_iff_infinite] at h
  have h' := h.sdiff (Set.finite_singleton 0)
  have h4 := hollow_core_index_four_dvd lam hlam 10 0 a le_rfl (by linarith) (h'.mono fun N hN => ?_)
  · omega
  · obtain ⟨⟨heven, hge⟩, hne⟩ := hN
    have hNpos : 0 < N := Nat.pos_of_ne_zero hne
    have hz : ∀ k : ℕ, 1 ≤ k → k ≤ 10 → evenEig lam hlam N k = 0 := hzero N hNpos heven
    refine ⟨heven, ?_, ?_⟩
    · rw [hz 10 (by norm_num) le_rfl, hz 1 le_rfl (by norm_num), sub_self]
    · rw [hz 10 (by norm_num) le_rfl, sub_zero]
      push Not at hge
      exact hge

/-- **Corollary 8.2(i)**: "`$E_3(N)\to0$ as $N\to\infty$ through the odd integers.`" — `odd_E3_tendsto` with
`HasAtLeastTwoZeroModes`. -/
theorem odd_E3_tendsto' (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, Odd N → 3 ≤ N →
      HasAtLeastTwoZeroModes (rectTorus lam hlam N) (oddSectorPlus (rectTorus lam hlam N)) ∧
      HasAtLeastTwoZeroModes (rectTorus lam hlam N) (oddSectorMinus (rectTorus lam hlam N))) :
    Tendsto (fun N => oddEigPlus lam hlam N 3) (atTop ⊓ 𝓟 {N : ℕ | Odd N}) (𝓝 0) ∧
      Tendsto (fun N => oddEigMinus lam hlam N 3) (atTop ⊓ 𝓟 {N : ℕ | Odd N}) (𝓝 0) := by
  obtain ⟨Nb, -, hNb⟩ := rect_threshold_dev lam hlam
  have hMi := inf_inter_ge_dev odd_ge_three_infinite_dev Nb
  have hM : ∀ N ∈ {N : ℕ | Odd N ∧ 3 ≤ N} ∩ {N | Nb ≤ N}, 0 < N ∧ (rectTorus lam hlam N).Admissible δstd :=
    fun N hN => hNb N hN.2
  have hc : 0 < Real.sqrt (4 * π * lam) := Real.sqrt_pos.2 (by positivity)
  have hLx := rectSeq_Lx_dev lam hlam _ hMi hM
  have hH2 := (hcSetting_data (rectSeq_dev lam hlam _ hMi hM) _ hc hLx).2.2
  obtain ⟨hng1, hng2⟩ := no_gap_odd isProfile_etaStd (Real.sqrt_pos.2 Real.pi_pos)
    (hcSetting (rectSeq_dev lam hlam _ hMi hM) _ hc hLx) hH2 (fun N hN => hN.1.1)
  exact ⟨odd_E3_dev lam hlam (hcSetting (rectSeq_dev lam hlam _ hMi hM) _ hc hLx).Ts.idx Nb
      (fun N h1 h2 h3 => ⟨⟨h1, h2⟩, h3⟩) oddSectorPlus (fun N h1 h2 => (hzero N h1 h2).1) hng1,
    odd_E3_dev lam hlam (hcSetting (rectSeq_dev lam hlam _ hMi hM) _ hc hLx).Ts.idx Nb
      (fun N h1 h2 h3 => ⟨⟨h1, h2⟩, h3⟩) oddSectorMinus (fun N h1 h2 => (hzero N h1 h2).2) hng2⟩

/-- **Corollary 8.2(ii)**: "`For every $D\in\N$ and $\gamma>0$, for all sufficiently large odd $N$ there are more than $D$ eigenvalues in $[0,\gamma)$.`"
— `odd_many_small` with `HasAtLeastTwoZeroModes`. -/
theorem odd_many_small' (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, Odd N → 3 ≤ N →
      HasAtLeastTwoZeroModes (rectTorus lam hlam N) (oddSectorPlus (rectTorus lam hlam N)) ∧
      HasAtLeastTwoZeroModes (rectTorus lam hlam N) (oddSectorMinus (rectTorus lam hlam N)))
    (Dc : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ N in atTop ⊓ 𝓟 {N : ℕ | Odd N},
      Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (rectTorus lam hlam N) (oddSectorPlus (rectTorus lam hlam N))))).filter
        fun k => oddEigPlus lam hlam N k ∈ Set.Ico 0 γ).card ∧
      Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (rectTorus lam hlam N) (oddSectorMinus (rectTorus lam hlam N))))).filter
        fun k => oddEigMinus lam hlam N k ∈ Set.Ico 0 γ).card := by
  obtain ⟨Nb, -, hNb⟩ := rect_threshold_dev lam hlam
  have hMi := inf_inter_ge_dev odd_ge_three_infinite_dev Nb
  have hM : ∀ N ∈ {N : ℕ | Odd N ∧ 3 ≤ N} ∩ {N | Nb ≤ N}, 0 < N ∧ (rectTorus lam hlam N).Admissible δstd :=
    fun N hN => hNb N hN.2
  have hc : 0 < Real.sqrt (4 * π * lam) := Real.sqrt_pos.2 (by positivity)
  have hLx := rectSeq_Lx_dev lam hlam _ hMi hM
  have hH2 := (hcSetting_data (rectSeq_dev lam hlam _ hMi hM) _ hc hLx).2.2
  obtain ⟨hf1, hf2⟩ := many_low_odd isProfile_etaStd (Real.sqrt_pos.2 Real.pi_pos)
    (hcSetting (rectSeq_dev lam hlam _ hMi hM) _ hc hLx) hH2 (fun N hN => hN.1.1) Dc hγ
  exact (odd_many_dev lam hlam (hcSetting (rectSeq_dev lam hlam _ hMi hM) _ hc hLx).Ts.idx Nb
      (fun N h1 h2 h3 => ⟨⟨h1, h2⟩, h3⟩) oddSectorPlus (fun N h1 h2 => (hzero N h1 h2).1) Dc hf1).and
    (odd_many_dev lam hlam (hcSetting (rectSeq_dev lam hlam _ hMi hM) _ hc hLx).Ts.idx Nb
      (fun N h1 h2 h3 => ⟨⟨h1, h2⟩, h3⟩) oddSectorMinus (fun N h1 h2 => (hzero N h1 h2).2) Dc hf2)

/-- **Corollary 8.4**: "`Then $\sup_{\Tor\in\mathcal T_N}E_{11}(N;\Tor)\to0$ as $N\to\infty$ through the even integers.`" —
`uniform_E11_tendsto` with `HasAtLeastTenZeroModes`. -/
theorem uniform_E11_tendsto'
    (hzero : ∀ T : Torus, Even T.N → L0std ≤ min T.Lx T.Ly → HasAtLeastTenZeroModes T) :
    Tendsto (fun N => sSup (E11 '' tauSet N)) (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Filter.Eventually.of_forall fun N => lt_of_lt_of_le ha ?_, fun a ha => ?_⟩
  · refine Real.sSup_nonneg fun x hx => ?_
    obtain ⟨T, -, rfl⟩ := hx
    exact secEig_HN_nonneg T (halfSector T) 11
  · filter_upwards [uniform_eventually_dev hzero (a / 2) (by linarith)] with N hN
    have h : sSup (E11 '' tauSet N) ≤ a / 2 := by
      refine Real.sSup_le (fun x hx => ?_) (by linarith)
      obtain ⟨T, hT, rfl⟩ := hx
      exact (hN T hT).le
    linarith

/-- **Corollary 8.4** without the supremum — `uniform_E11_eventually` with `HasAtLeastTenZeroModes`. -/
theorem uniform_E11_eventually'
    (hzero : ∀ T : Torus, Even T.N → L0std ≤ min T.Lx T.Ly → HasAtLeastTenZeroModes T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop ⊓ 𝓟 {N : ℕ | Even N}, ∀ T ∈ tauSet N, E11 T < ε := by
  exact uniform_eventually_dev hzero

/-! ## The reviewed statements, derived from the strengthened ones in a line -/

/-- `hollow_core_index`, verbatim, from `hollow_core_index'`. -/
theorem hollow_core_index_of' (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, 0 < N → Even N → HasTenZeroModes (rectTorus lam hlam N))
    (p : ℕ) (Δ γ : ℝ) (hΔ : 0 ≤ Δ) (hγ : 2 * Δ < γ)
    (hinf : {N : ℕ | Even N ∧ evenEig lam hlam N p - evenEig lam hlam N 1 ≤ Δ ∧
      γ ≤ evenEig lam hlam N (p + 1) - evenEig lam hlam N p}.Infinite) :
    4 ∣ p ∧ 12 ≤ p :=
  hollow_core_index' lam hlam (fun N h1 h2 => hasAtLeastTen_of_hasTen (hzero N h1 h2)) p Δ γ hΔ hγ hinf

/-- `hollow_core_E11_tendsto`, verbatim, from `hollow_core_E11_tendsto'`. -/
theorem hollow_core_E11_tendsto_of' (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, 0 < N → Even N → HasTenZeroModes (rectTorus lam hlam N)) :
    Tendsto (fun N => evenEig lam hlam N 11) (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 0) :=
  hollow_core_E11_tendsto' lam hlam fun N h1 h2 => hasAtLeastTen_of_hasTen (hzero N h1 h2)

/-- `odd_E3_tendsto`, verbatim, from `odd_E3_tendsto'`. -/
theorem odd_E3_tendsto_of' (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, Odd N → 3 ≤ N → HasTwoZeroModes (rectTorus lam hlam N) (oddSectorPlus (rectTorus lam hlam N)) ∧
      HasTwoZeroModes (rectTorus lam hlam N) (oddSectorMinus (rectTorus lam hlam N))) :
    Tendsto (fun N => oddEigPlus lam hlam N 3) (atTop ⊓ 𝓟 {N : ℕ | Odd N}) (𝓝 0) ∧
      Tendsto (fun N => oddEigMinus lam hlam N 3) (atTop ⊓ 𝓟 {N : ℕ | Odd N}) (𝓝 0) :=
  odd_E3_tendsto' lam hlam fun N h1 h2 =>
    ⟨hasAtLeastTwo_of_hasTwo (hzero N h1 h2).1, hasAtLeastTwo_of_hasTwo (hzero N h1 h2).2⟩

/-- `odd_many_small`, verbatim, from `odd_many_small'`. -/
theorem odd_many_small_of' (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, Odd N → 3 ≤ N → HasTwoZeroModes (rectTorus lam hlam N) (oddSectorPlus (rectTorus lam hlam N)) ∧
      HasTwoZeroModes (rectTorus lam hlam N) (oddSectorMinus (rectTorus lam hlam N)))
    (Dc : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ N in atTop ⊓ 𝓟 {N : ℕ | Odd N},
      Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (rectTorus lam hlam N) (oddSectorPlus (rectTorus lam hlam N))))).filter
        fun k => oddEigPlus lam hlam N k ∈ Set.Ico 0 γ).card ∧
      Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (rectTorus lam hlam N) (oddSectorMinus (rectTorus lam hlam N))))).filter
        fun k => oddEigMinus lam hlam N k ∈ Set.Ico 0 γ).card :=
  odd_many_small' lam hlam (fun N h1 h2 =>
    ⟨hasAtLeastTwo_of_hasTwo (hzero N h1 h2).1, hasAtLeastTwo_of_hasTwo (hzero N h1 h2).2⟩) Dc hγ

/-- `uniform_E11_tendsto`, verbatim, from `uniform_E11_tendsto'`. -/
theorem uniform_E11_tendsto_of'
    (hzero : ∀ T : Torus, Even T.N → L0std ≤ min T.Lx T.Ly → HasTenZeroModes T) :
    Tendsto (fun N => sSup (E11 '' tauSet N)) (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 0) :=
  uniform_E11_tendsto' fun T h1 h2 => hasAtLeastTen_of_hasTen (hzero T h1 h2)

/-- `uniform_E11_eventually`, verbatim, from `uniform_E11_eventually'`. -/
theorem uniform_E11_eventually_of'
    (hzero : ∀ T : Torus, Even T.N → L0std ≤ min T.Lx T.Ly → HasTenZeroModes T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop ⊓ 𝓟 {N : ℕ | Even N}, ∀ T ∈ tauSet N, E11 T < ε :=
  uniform_E11_eventually' fun T h1 h2 => hasAtLeastTen_of_hasTen (hzero T h1 h2)

/-! ## The unconditional main theorems -/

/-- **Theorem 8.1(i)**, unconditional: "`If for some $p\in\N$, $\Delta\ge0$ and $\gamma>2\Delta$ the inequalities $E_p(N)-E_1(N)\le\Delta$ and $E_{p+1}(N)-E_p(N)\ge\gamma$ hold for infinitely many even $N$, then $p\in4\Z$ and $p\ge12$.`" -/
theorem hollow_core_index_unconditional (lam : ℝ) (hlam : 0 < lam) (p : ℕ) (Δ γ : ℝ) (hΔ : 0 ≤ Δ) (hγ : 2 * Δ < γ)
    (hinf : {N : ℕ | Even N ∧ evenEig lam hlam N p - evenEig lam hlam N 1 ≤ Δ ∧
      γ ≤ evenEig lam hlam N (p + 1) - evenEig lam hlam N p}.Infinite) :
    4 ∣ p ∧ 12 ≤ p :=
  hollow_core_index' lam hlam
    (fun N hN he => hasAtLeastTenZeroModes _ (by rw [(rectTorus_sides lam hlam hN).1]; exact he)) p Δ γ hΔ hγ hinf

/-- **Theorem 8.1(ii)**, unconditional: "`$E_{11}(N)\to0$ as $N\to\infty$ through the even integers.`" -/
theorem hollow_core_E11_tendsto_unconditional (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun N => evenEig lam hlam N 11) (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 0) :=
  hollow_core_E11_tendsto' lam hlam
    fun N hN he => hasAtLeastTenZeroModes _ (by rw [(rectTorus_sides lam hlam hN).1]; exact he)

/-- **Corollary 8.2(i)**, unconditional: "`$E_3(N)\to0$ as $N\to\infty$ through the odd integers.`" — in both sectors. -/
theorem odd_E3_tendsto_unconditional (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun N => oddEigPlus lam hlam N 3) (atTop ⊓ 𝓟 {N : ℕ | Odd N}) (𝓝 0) ∧
      Tendsto (fun N => oddEigMinus lam hlam N 3) (atTop ⊓ 𝓟 {N : ℕ | Odd N}) (𝓝 0) :=
  odd_E3_tendsto' lam hlam fun N hodd h3 =>
    hasAtLeastTwoZeroModes _ (by rw [(rectTorus_sides lam hlam (by omega)).1]; exact hodd)
      (by rw [(rectTorus_sides lam hlam (by omega)).1]; exact h3)

/-- **Corollary 8.2(ii)**, unconditional: "`For every $D\in\N$ and $\gamma>0$, for all sufficiently large odd $N$ there are more than $D$ eigenvalues in $[0,\gamma)$.`"
— in each sector, counted with multiplicity among `E_1, …, E_d`, `d` the sector's dimension (the paper's `D` is `Dc`). -/
theorem odd_many_small_unconditional (lam : ℝ) (hlam : 0 < lam) (Dc : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ N in atTop ⊓ 𝓟 {N : ℕ | Odd N},
      Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (rectTorus lam hlam N) (oddSectorPlus (rectTorus lam hlam N))))).filter
        fun k => oddEigPlus lam hlam N k ∈ Set.Ico 0 γ).card ∧
      Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (rectTorus lam hlam N) (oddSectorMinus (rectTorus lam hlam N))))).filter
        fun k => oddEigMinus lam hlam N k ∈ Set.Ico 0 γ).card :=
  odd_many_small' lam hlam (fun N hodd h3 =>
    hasAtLeastTwoZeroModes _ (by rw [(rectTorus_sides lam hlam (by omega)).1]; exact hodd)
      (by rw [(rectTorus_sides lam hlam (by omega)).1]; exact h3)) Dc hγ

/-- **Corollary 8.4**, unconditional: "`Then $\sup_{\Tor\in\mathcal T_N}E_{11}(N;\Tor)\to0$ as $N\to\infty$ through the even integers.`" -/
theorem uniform_E11_tendsto_unconditional :
    Tendsto (fun N => sSup (E11 '' tauSet N)) (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 0) :=
  uniform_E11_tendsto' fun T he _ => hasAtLeastTenZeroModes T he

/-- **Corollary 8.4** without the supremum, unconditional: for every `ε > 0`, for all large even `N`, every torus of
`𝒯_N` has `E_{11}(N; 𝕋) < ε`. -/
theorem uniform_E11_eventually_unconditional :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop ⊓ 𝓟 {N : ℕ | Even N}, ∀ T ∈ tauSet N, E11 T < ε :=
  uniform_E11_eventually' fun T he _ => hasAtLeastTenZeroModes T he

end HRTorus.ZeroModes

end -- noncomputable section
