import HRTorus.Assembly.Translation

/-!
# The main theorem: no uniform gap above the zero modes (`Assembly.Main`)

Written by Claude Opus 5.5 (an AI model), 2026-10-25. **The definitions and statements were written first
and reviewed against the paper (the statement phase; the final theorem's statement was also read blind by a fresh
reader, a second instance working from the paper); proof phase rounds one and three added the proofs and the proof devices, each section of which is
marked as such. No theorem of this module is `sorry`.** Lemma 8.3's `H_N ↦ H'_N` (`FfR_conj`) is proved through the local
form `H_N = ∫ h_R dR` of Theorem 4.2(a) (block C's `localForm_a`), not through the paper's change of basis in the
coefficients `V_{abcd}` (the device section of `FfR_conj` says so).
The paper: the HR paper, `papers/hr/sections/08-hollow-core.tex` — Theorem 8.1 `thm:main`, Corollary 8.2 `cor:oddN`,
Lemma 8.3 `lem:exchange`, Corollary 8.4 `cor:uniform`; the zero modes of §2.5 (Theorem 2.10 `thm:kernel` and (2.8)
`eq:E11`), proved in Appendix C, enter as an explicit hypothesis.

## The model

* **The tori.** `rectTorus λ hλ N` is "the rectangular torus with `L_x/L_y = λ` and `L_xL_y = 4πN`" (block A's `Torus`,
  i.e. `SlotFrame.Torus`): `L_x = (4πλN)^{1/2}` and `L_y = 4πN/L_x = (4πN/λ)^{1/2}`, so that the field `area` holds
  exactly; for `N = 0`, where there is no such torus, it is the torus of `N = 1` (never used: every statement is about
  infinitely many `N` or a limit `N → ∞`).
* **The Hamiltonian and the eigenvalues.** `H_N` is block A's `HN` (Definition 2.7); `E_k(N)` is `secEig` of
  `Assembly.Setting` (the ordered eigenvalues with multiplicity) in the sector `(N/2, N/2)` (`halfSector`), named
  `evenEig λ hλ N k`; at odd `N` in the sectors `((N ± 1)/2, (N ∓ 1)/2)` (`oddEigPlus`, `oddEigMinus`).
* **"For infinitely many even `N`"** is `Set.Infinite {N | Even N ∧ …}`; **"as `N → ∞` through the even integers"** is
  the filter `atTop ⊓ 𝓟 {N | Even N}`.
* **The zero modes** are the named hypotheses `HasTenZeroModes T` ("`E_1(N)=\cdots=E_{10}(N)=0<E_{11}(N)`", (2.8)) and
  `HasTwoZeroModes T 𝐧` (the odd case), assumed for the tori of each statement (Theorem 8.1(i)'s `12 ≤ p`,
  `hollow_core_index`; Theorem 8.1(ii); Corollaries 8.2 and 8.4) and for nothing else; `4 ∣ p` is stated without them
  (`hollow_core_index_four_dvd`). Theorem 2.10's dimension
  statements give them (`hasTenZeroModes_of_kernel`, `hasTwoZeroModes_of_kernel`), with `H_N ≥ 0`.
* **The exchange of the sides** (Lemma 8.3): `swapTorus T` has `L'_x = L_y`, `L'_y = L_x` (and the same `N`); `𝓡` acts
  on functions as `rotFun` and on block A's abstract `𝔥_N` as the matrix `rotMat T` of the inner products
  `⟨ψ'_k, 𝓡ψ_j⟩` ("the map determined on the orbitals"; `toFun_rotLin` says it is `𝓡`); `𝔉(𝓡 ⊗ 1)` is block A's
  `secondQuant` of `rotMat T ⊗ 1`.
* **The fixed choices** of the proof: the profile `SlotFrame.etaStd` and "`$\delta_0=\sqrt\pi$`" (`δstd`), so
  `L₀ = max{4, 3π/δ₀} = 3√π` (`L0std`), the filters of `ArgData.std`.
-/

open scoped InnerProductSpace Matrix ENNReal Real ComplexConjugate Topology
open Complex (I)
open MeasureTheory Filter

noncomputable section

namespace HRTorus.Assembly

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian HRTorus.Locality
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op IsEven CAR Alg)

/-! ## The fixed choices and the tori -/

/-- Definition 3.1: "`L_0:=\max\{4,\,3\pi/\delta_0\}`" at `δ₀ = √π`. -/
def L0std : ℝ := L0 δstd

/-- **Theorem 8.1**: "`Fix $\lambda>0$. For even $N$ let $\Tor_N$ be the rectangular torus with $L_x/L_y=\lambda$ and $L_xL_y=4\pi N$`"
— `L_x = (4πλN)^{1/2}`, `L_y = 4πN/L_x` (the module docstring; `N := 1` at `N = 0`). -/
def rectTorus (lam : ℝ) (hlam : 0 < lam) (N : ℕ) : Torus where
  N := max N 1
  Lx := Real.sqrt (4 * π * lam * ((max N 1 : ℕ) : ℝ))
  Ly := 2 * π * ((2 * max N 1 : ℕ) : ℝ) / Real.sqrt (4 * π * lam * ((max N 1 : ℕ) : ℝ))
  Lx_pos := by
    have h1 : (0 : ℝ) < ((max N 1 : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.one_pos (le_max_right N 1)
    exact Real.sqrt_pos.2 (by positivity)
  Ly_pos := by
    have h1 : (0 : ℝ) < ((max N 1 : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.one_pos (le_max_right N 1)
    have h2 : (0 : ℝ) < ((2 * max N 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos two_pos (lt_of_lt_of_le Nat.one_pos (le_max_right N 1))
    have h3 : 0 < Real.sqrt (4 * π * lam * ((max N 1 : ℕ) : ℝ)) := Real.sqrt_pos.2 (by positivity)
    positivity
  area := by
    have h1 : (0 : ℝ) < ((max N 1 : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.one_pos (le_max_right N 1)
    have h3 : Real.sqrt (4 * π * lam * ((max N 1 : ℕ) : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    field_simp

/-- The hollow-core eigenvalues `E_k` of a torus in a sector: `secEig` of block A's `HN`. -/
def hcEig (T : Torus) (nn : SectorLabel T) (k : ℕ) : ℝ := secEig T (HN T) nn k

/-- **Theorem 8.1**: "`let $E_1(N)\le E_2(N)\le\cdots$ be the eigenvalues of $H_N$ in the sector $\sect{(N/2,N/2)}$, repeated according to multiplicity`". -/
def evenEig (lam : ℝ) (hlam : 0 < lam) (N k : ℕ) : ℝ :=
  hcEig (rectTorus lam hlam N) (halfSector (rectTorus lam hlam N)) k

/-- **Corollary 8.2**: "`In each of the sectors $\sect{((N\pm1)/2,(N\mp1)/2)}$ let $E_1(N)\le E_2(N)\le\cdots$ be the eigenvalues of $H_N$`"
— the sector `((N + 1)/2, (N − 1)/2)`. -/
def oddEigPlus (lam : ℝ) (hlam : 0 < lam) (N k : ℕ) : ℝ :=
  hcEig (rectTorus lam hlam N) (oddSectorPlus (rectTorus lam hlam N)) k

/-- **Corollary 8.2**: the sector `((N − 1)/2, (N + 1)/2)`. -/
def oddEigMinus (lam : ℝ) (hlam : 0 < lam) (N k : ℕ) : ℝ :=
  hcEig (rectTorus lam hlam N) (oddSectorMinus (rectTorus lam hlam N)) k

/-- **(2.8)**: "`E_1(N)=\cdots=E_{10}(N)=0<E_{11}(N)`" in the sector `(N/2, N/2)` of a torus — the zero modes as a named
hypothesis (the content of Theorem 2.10(iii) with `H_N ≥ 0`, proved in Appendix C). -/
def HasTenZeroModes (T : Torus) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k ≤ 10 → hcEig T (halfSector T) k = 0) ∧ 0 < hcEig T (halfSector T) 11

/-- The odd case: "`$E_1(N)=E_2(N)=0<E_3(N)$`" in a sector (Theorem 2.10(ii) with `H_N ≥ 0`). -/
def HasTwoZeroModes (T : Torus) (nn : SectorLabel T) : Prop :=
  hcEig T nn 1 = 0 ∧ hcEig T nn 2 = 0 ∧ 0 < hcEig T nn 3

/-! ## Lemma 8.3's objects -/

/-- **Lemma 8.3**: "`let $\Tor'_N$ be the torus of Definition~\ref{def:torus} with side lengths $L'_x:=L_y$ and $L'_y:=L_x$`". -/
def swapTorus (T : Torus) : Torus where
  N := T.N
  Lx := T.Ly
  Ly := T.Lx
  Lx_pos := T.Ly_pos
  Ly_pos := T.Lx_pos
  area := by rw [mul_comm]; exact T.area

/-- **Lemma 8.3**: "`For $f\in\hN$ let $(\mathcal Rf)(x,y):=e^{\iu xy}f(-y,x)$.`" — on functions `ℝ² → ℂ`. -/
def rotFun (f : ℝ × ℝ → ℂ) (r : ℝ × ℝ) : ℂ :=
  Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)) * f (-r.2, r.1)

/-- The matrix of `𝓡` in the orbital bases of `𝔥_N` and `𝔥'_N`: the entry `(k, j)` is `⟨ψ'_k, 𝓡ψ_j⟩` (block A's `L²`
inner product `l2inner` on the fundamental domain of `𝕋'_N`). -/
def rotMat (T : Torus) : Matrix (ZMod (swapTorus T).Nφ) (ZMod T.Nφ) ℂ :=
  Matrix.of fun k j => l2inner (swapTorus T) (psi (swapTorus T) k) (rotFun (psi T j))

/-- `𝓡 : 𝔥_N → 𝔥'_N` on block A's abstract spaces (`toFun_rotLin`). -/
def rotLin (T : Torus) : Space T →ₗ[ℂ] Space (swapTorus T) :=
  Matrix.toEuclideanLin (rotMat T)

/-- `𝓡 ⊗ 1 : 𝔨_N → 𝔨'_N` in the bases `ψ_j ⊗ σ`, `ψ'_k ⊗ σ`. -/
def rot2 (T : Torus) : Matrix (Modes (swapTorus T)) (Modes T) ℂ :=
  Matrix.kronecker (rotMat T) (1 : Matrix Spin Spin ℂ)

/-- **Lemma 8.3**: "`the unitary $\Ff(\mathcal R\otimes\one):\Fock\to\mathcal H'_N$`" — block A's second quantization of `𝓡 ⊗ 1`. -/
def FfR (T : Torus) : Matrix (Conf (ZMod (swapTorus T).Nφ)) (Conf (ZMod T.Nφ)) ℂ :=
  secondQuant (rot2 T)

/-! ## Corollary 8.4's family -/

/-- **Corollary 8.4**: "`let $\mathcal T_N$ be the set of rectangular tori with $L_xL_y=4\pi N$ and $\min\{L_x,L_y\}\ge L_0$`"
(a `Torus` with `N` electrons has `L_xL_y = 4πN`). -/
def tauSet (N : ℕ) : Set Torus :=
  {T | T.N = N ∧ L0std ≤ min T.Lx T.Ly}

/-- **Corollary 8.4**: "`let $E_{11}(N;\Tor)$ be the eleventh eigenvalue of the hollow-core Hamiltonian of $\Tor$ in the sector $(N/2,N/2)$`". -/
def E11 (T : Torus) : ℝ := hcEig T (halfSector T) 11

/-! ## Statements -/

/-! ### The tori and the zero modes -/

/-- The proof of Theorem 8.1: "`The side lengths are $L_x=(4\pi\lambda N)^{1/2}$ and $L_y=(4\pi N/\lambda)^{1/2}$.`" -/
theorem rectTorus_sides (lam : ℝ) (hlam : 0 < lam) {N : ℕ} (hN : 0 < N) :
    (rectTorus lam hlam N).N = N ∧ (rectTorus lam hlam N).Lx = Real.sqrt (4 * π * lam * N) ∧
      (rectTorus lam hlam N).Ly = Real.sqrt (4 * π * N / lam) ∧
      (rectTorus lam hlam N).Lx / (rectTorus lam hlam N).Ly = lam ∧
      (rectTorus lam hlam N).Lx * (rectTorus lam hlam N).Ly = 4 * π * N := by
  have hmax : max N 1 = N := max_eq_left hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < 4 * π * lam * N := by positivity
  have hsa := Real.sqrt_pos.2 ha
  have hLx : (rectTorus lam hlam N).Lx = Real.sqrt (4 * π * lam * N) := by
    show Real.sqrt (4 * π * lam * ((max N 1 : ℕ) : ℝ)) = _
    rw [hmax]
  have hLy' : (rectTorus lam hlam N).Ly = Real.sqrt (4 * π * lam * N) / lam := by
    show 2 * π * ((2 * max N 1 : ℕ) : ℝ) / Real.sqrt (4 * π * lam * ((max N 1 : ℕ) : ℝ)) = _
    rw [hmax, div_eq_div_iff hsa.ne' hlam.ne', Real.mul_self_sqrt ha.le]
    push_cast
    ring
  have hLy : (rectTorus lam hlam N).Ly = Real.sqrt (4 * π * N / lam) := by
    rw [hLy', show 4 * π * (N : ℝ) / lam = 4 * π * lam * N / lam ^ 2 by field_simp,
      Real.sqrt_div ha.le, Real.sqrt_sq hlam.le]
  refine ⟨hmax, hLx, hLy, ?_, ?_⟩
  · rw [hLx, hLy']
    field_simp
  · have h := (rectTorus lam hlam N).area
    rw [show (rectTorus lam hlam N).N = N from hmax] at h
    push_cast at h
    linarith

/-- The proof of Theorem 8.1: "`Both tend to infinity with $N$, so there is $N_\lambda$ such that the torus is admissible`"
"`for every $N\ge N_\lambda$. Put $c_*:=(4\pi\lambda)^{1/2}$, so that $L_x=c_*\sqrt N$.`" -/
theorem rectTorus_admissible (lam : ℝ) (hlam : 0 < lam) :
    ∃ Nl : ℕ, ∀ N : ℕ, Nl ≤ N → (rectTorus lam hlam N).Admissible δstd ∧
      (rectTorus lam hlam N).Lx = Real.sqrt (4 * π * lam) * Real.sqrt N := by
  have hπ := Real.pi_pos
  have hδ : 0 < δstd := Real.sqrt_pos.2 Real.pi_pos
  have hL0 : 0 < L0 δstd := lt_of_lt_of_le (by norm_num) (le_max_left 4 _)
  refine ⟨⌈L0 δstd ^ 2 * lam / (4 * π) + (4 * δstd + 4) ^ 2 / (4 * π * lam)⌉₊ + 1, fun N hN => ?_⟩
  have hN1 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNc : L0 δstd ^ 2 * lam / (4 * π) + (4 * δstd + 4) ^ 2 / (4 * π * lam) ≤ N := by
    have := Nat.le_ceil (L0 δstd ^ 2 * lam / (4 * π) + (4 * δstd + 4) ^ 2 / (4 * π * lam))
    have h2 : ((⌈L0 δstd ^ 2 * lam / (4 * π) + (4 * δstd + 4) ^ 2 / (4 * π * lam)⌉₊ : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (Nat.le_succ _).trans hN
    linarith
  have h1 : 0 ≤ L0 δstd ^ 2 * lam / (4 * π) := by positivity
  have h2 : 0 ≤ (4 * δstd + 4) ^ 2 / (4 * π * lam) := by positivity
  obtain ⟨-, hLx, hLy, -, -⟩ := rectTorus_sides lam hlam hN1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hLy]
    calc L0 δstd = Real.sqrt (L0 δstd ^ 2) := (Real.sqrt_sq hL0.le).symm
      _ ≤ Real.sqrt (4 * π * N / lam) := by
        apply Real.sqrt_le_sqrt
        rw [le_div_iff₀ hlam]
        have : L0 δstd ^ 2 * lam / (4 * π) ≤ N := by linarith
        rw [div_le_iff₀ (by positivity)] at this
        linarith
  · rw [hLx]
    calc 4 * δstd + 4 = Real.sqrt ((4 * δstd + 4) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (4 * π * lam * N) := by
        apply Real.sqrt_le_sqrt
        have : (4 * δstd + 4) ^ 2 / (4 * π * lam) ≤ N := by linarith
        rw [div_le_iff₀ (by positivity)] at this
        linarith
  · rw [hLx, Real.sqrt_mul (by positivity)]

/-- `L₀ = 3√π`. -/
theorem L0std_eq : L0std = 3 * Real.sqrt π := by
  unfold L0std L0 δstd
  rw [mul_div_assoc, Real.div_sqrt]
  apply max_eq_right
  have h : (4 / 3 : ℝ) ^ 2 ≤ π := by nlinarith [Real.pi_gt_three]
  have h2 : (4 / 3 : ℝ) ≤ Real.sqrt π := by
    calc (4 / 3 : ℝ) = Real.sqrt ((4 / 3) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt π := Real.sqrt_le_sqrt h
  linarith

/-! ### Proof device for the zero-mode bridges (phase (b), round one; not a statement of the paper)

With `H_N ≥ 0` (`secEig_HN_nonneg`) and the multiplicity count `card_secEig_eq` at `0`, a `z`-dimensional kernel in a
sector of dimension `> z` gives `E_1 = ⋯ = E_z = 0 < E_{z+1}` (the zero indices form an initial segment). -/

theorem zero_modes_dev (T : Torus) (nn : SectorLabel T) (z : ℕ)
    (hz : Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T nn) = z)
    (hd : z + 1 ≤ Module.finrank ℂ (sector T nn)) :
    (∀ k, 1 ≤ k → k ≤ z → secEig T (HN T) nn k = 0) ∧ 0 < secEig T (HN T) nn (z + 1) := by
  classical
  have hcard := card_secEig_eq (HN_isSelfAdjoint T) (HN_isSectorPreserving T) nn 0
  rw [Complex.ofReal_zero, Module.End.eigenspace_zero, hz] at hcard
  have hmono := secEig_mono T (HN T) nn
  have hnn := secEig_HN_nonneg T nn
  have hpos : 0 < secEig T (HN T) nn (z + 1) := by
    rcases (hnn (z + 1)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hsub : Finset.Icc 1 (z + 1) ⊆
          (Finset.Icc 1 (Module.finrank ℂ (sector T nn))).filter (fun k => secEig T (HN T) nn k = 0) := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hj.1, hj.2.trans hd⟩, le_antisymm (h ▸ hmono hj.2) (hnn j)⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc, hcard] at this
      omega
  refine ⟨fun k hk1 hkz => ?_, hpos⟩
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

/-- **Theorem 2.10(iii)** with (2.8): "`If $N$ is even, $\mathcal K_N\subset\sect{(N/2,N/2)}$ and $\dim\mathcal K_N=10$.`"
— if the kernel of `H_N` in the sector `(N/2, N/2)` has dimension ten, then `HasTenZeroModes` ("`Since $H_N\ge0$`", and
"`(The sector $(N/2,N/2)$ has dimension $\binom{2N}{N/2}^2\ge16$ for even $N\ge2$`"; the paper's parenthetical
continues with the two odd sectors' dimension, 2 at `N = 1` and at least 3 for odd `N ≥ 3`). -/
theorem hasTenZeroModes_of_kernel (T : Torus) (heven : Even T.N)
    (hker : Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (halfSector T)) = 10) :
    HasTenZeroModes T := by
  have hN := T.N_pos
  obtain ⟨r, hr⟩ := heven
  have hc : 4 ≤ T.Nφ.choose (T.N / 2) := by
    have e1 : (T.N / 2 + 3).choose (T.N / 2) = (T.N / 2 + 3).choose 3 := Nat.choose_symm_add
    have h2 : (4 : ℕ).choose 3 ≤ (T.N / 2 + 3).choose 3 := Nat.choose_le_choose 3 (by omega)
    have h3 : (T.N / 2 + 3).choose (T.N / 2) ≤ T.Nφ.choose (T.N / 2) :=
      Nat.choose_le_choose _ (by unfold Torus.Nφ; omega)
    have h4 : (4 : ℕ).choose 3 = 4 := by decide
    omega
  have hd : 10 + 1 ≤ Module.finrank ℂ (sector T (halfSector T)) := by
    rw [finrank_sector]
    show 11 ≤ T.Nφ.choose (T.N / 2) * T.Nφ.choose (T.N / 2)
    nlinarith
  obtain ⟨h1, h2⟩ := zero_modes_dev T (halfSector T) 10 hker hd
  exact ⟨h1, h2⟩

/-- **Theorem 2.10(ii)**: "`If $N$ is odd, $\mathcal K_N\cap\sect{((N+1)/2,(N-1)/2)}$ and $\mathcal K_N\cap\sect{((N-1)/2,(N+1)/2)}$ are two-dimensional.`"
— for odd `N ≥ 3` (at `N = 1` the sectors have dimension two), a two-dimensional kernel in either sector gives
`HasTwoZeroModes` there. -/
theorem hasTwoZeroModes_of_kernel (T : Torus) (hodd : Odd T.N) (h3 : 3 ≤ T.N) :
    (Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorPlus T)) = 2 → HasTwoZeroModes T (oddSectorPlus T)) ∧
    (Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T (oddSectorMinus T)) = 2 → HasTwoZeroModes T (oddSectorMinus T)) := by
  have ha : 3 ≤ T.Nφ.choose ((T.N + 1) / 2) := by
    have h1 : ((T.N + 1) / 2 + 1).choose ((T.N + 1) / 2) ≤ T.Nφ.choose ((T.N + 1) / 2) :=
      Nat.choose_le_choose _ (by unfold Torus.Nφ; omega)
    rw [Nat.choose_succ_self_right] at h1
    omega
  have hb : 1 ≤ T.Nφ.choose ((T.N - 1) / 2) := Nat.choose_pos (by unfold Torus.Nφ; omega)
  constructor
  · intro hker
    have hd : 2 + 1 ≤ Module.finrank ℂ (sector T (oddSectorPlus T)) := by
      rw [finrank_sector]
      show 3 ≤ T.Nφ.choose ((T.N + 1) / 2) * T.Nφ.choose ((T.N - 1) / 2)
      nlinarith
    obtain ⟨h1, h2⟩ := zero_modes_dev T (oddSectorPlus T) 2 hker hd
    exact ⟨h1 1 le_rfl (by norm_num), h1 2 (by norm_num) le_rfl, h2⟩
  · intro hker
    have hd : 2 + 1 ≤ Module.finrank ℂ (sector T (oddSectorMinus T)) := by
      rw [finrank_sector]
      show 3 ≤ T.Nφ.choose ((T.N - 1) / 2) * T.Nφ.choose ((T.N + 1) / 2)
      nlinarith
    obtain ⟨h1, h2⟩ := zero_modes_dev T (oddSectorMinus T) 2 hker hd
    exact ⟨h1 1 le_rfl (by norm_num), h1 2 (by norm_num) le_rfl, h2⟩

/-! ### Proof devices for Theorem 8.1 and Corollary 8.2 (phase (b), round three; not statements of the paper)

The tori `rectTorus λ N` along an infinite set `M` of `N` beyond the admissibility threshold `N_b = max{N_λ, 1}`
(`rect_threshold_dev`) as a `TorusSeq` (`rectSeq_dev`), with `L_x = c_*√N`, `c_* = (4πλ)^{1/2}` (`rectSeq_Lx_dev`);
Setting 6.1 is then round two's `hcSetting`. -/

section MainDevices

theorem rect_threshold_dev (lam : ℝ) (hlam : 0 < lam) :
    ∃ Nb : ℕ, 1 ≤ Nb ∧ ∀ N : ℕ, Nb ≤ N → 0 < N ∧ (rectTorus lam hlam N).Admissible δstd := by
  obtain ⟨Nl, hNl⟩ := rectTorus_admissible lam hlam
  exact ⟨max Nl 1, le_max_right _ _, fun N hN => ⟨by omega, (hNl N (le_trans (le_max_left _ _) hN)).1⟩⟩

theorem inf_inter_ge_dev {A : Set ℕ} (hA : A.Infinite) (Nb : ℕ) : (A ∩ {N | Nb ≤ N}).Infinite := by
  have hfin : ({N | ¬ Nb ≤ N} : Set ℕ).Finite := (Set.finite_lt_nat Nb).subset fun N hN => by
    simp only [Set.mem_ofPred_eq, not_le] at hN ⊢
    exact hN
  refine (hA.sdiff hfin).mono fun N hN => ⟨hN.1, ?_⟩
  have h := hN.2
  simp only [Set.mem_ofPred_eq, not_not] at h
  exact h

def rectSeq_dev (lam : ℝ) (hlam : 0 < lam) (M : Set ℕ) (hMi : M.Infinite)
    (hM : ∀ N ∈ M, 0 < N ∧ (rectTorus lam hlam N).Admissible δstd) : TorusSeq δstd where
  idx := M
  idx_infinite := hMi
  T := rectTorus lam hlam
  T_N := fun N hN => (rectTorus_sides lam hlam (hM N hN).1).1
  admissible := fun N hN => (hM N hN).2

theorem rectSeq_Lx_dev (lam : ℝ) (hlam : 0 < lam) (M : Set ℕ) (hMi : M.Infinite)
    (hM : ∀ N ∈ M, 0 < N ∧ (rectTorus lam hlam N).Admissible δstd) :
    ∀ N ∈ (rectSeq_dev lam hlam M hMi hM).idx,
      Real.sqrt (4 * π * lam) * Real.sqrt N ≤ ((rectSeq_dev lam hlam M hMi hM).T N).Lx := by
  intro N hN
  have hLx := (rectTorus_sides lam hlam (hM N hN).1).2.1
  show Real.sqrt (4 * π * lam) * Real.sqrt N ≤ (rectTorus lam hlam N).Lx
  rw [hLx, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 * π * lam)]

theorem odd_ge_three_infinite_dev : ({N : ℕ | Odd N ∧ 3 ≤ N}).Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨B, hB⟩ => ?_
  have h := hB (show 2 * B + 3 ∈ {N : ℕ | Odd N ∧ 3 ≤ N} from ⟨⟨B + 1, by ring⟩, by omega⟩)
  omega

/-- Corollary 8.2(i) in one sector `sec`: Corollary 7.4(i)'s negation (along `I`, which contains every odd `N ≥ 3`
beyond `N_b`) at `p = 2`, `Δ = 0`, `γ = a` against "`E_3(N) ≥ a` for infinitely many odd `N`". It takes the
equalities `E_1 = E_2 = 0` only (no `0 < E_3`): it serves `odd_E3_tendsto` and `ZeroModes.Lower`'s `odd_E3_tendsto'`. -/
theorem odd_E3_dev (lam : ℝ) (hlam : 0 < lam) (I : Set ℕ) (Nb : ℕ) (hI : ∀ N, Odd N → 3 ≤ N → Nb ≤ N → N ∈ I)
    (sec : (T : Torus) → SectorLabel T)
    (hzero : ∀ N : ℕ, Odd N → 3 ≤ N → hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) 1 = 0 ∧
      hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) 2 = 0)
    (hng : ¬ ∃ (p : ℕ) (Δ γ : ℝ), 0 ≤ Δ ∧ 2 * Δ < γ ∧ ∃ M ⊆ I, M.Infinite ∧ ∀ N ∈ M,
      hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) p -
          hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) 1 ≤ Δ ∧
        γ ≤ hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) (p + 1) -
          hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) p) :
    Tendsto (fun N => hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) 3) (atTop ⊓ 𝓟 {N : ℕ | Odd N})
      (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Filter.Eventually.of_forall fun N => lt_of_lt_of_le ha (secEig_HN_nonneg _ _ 3),
    fun a ha => ?_⟩
  by_contra h
  rw [Filter.not_eventually, Filter.frequently_inf_principal, Nat.frequently_atTop_iff_infinite] at h
  have h' := inf_inter_ge_dev h (max Nb 3)
  refine hng ⟨2, 0, a, le_rfl, by linarith, _, ?_, h', ?_⟩
  · intro N hN
    have hle : max Nb 3 ≤ N := hN.2
    exact hI N hN.1.1 (max_le_iff.mp hle).2 (max_le_iff.mp hle).1
  · intro N hN
    obtain ⟨⟨hodd, hge⟩, hle⟩ := hN
    have hle' : max Nb 3 ≤ N := hle
    obtain ⟨h1, h2⟩ := hzero N hodd (max_le_iff.mp hle').2
    refine ⟨?_, ?_⟩
    · rw [h2, h1, sub_self]
    · rw [h2, sub_zero]
      push Not at hge
      exact hge

/-- Corollary 8.2(ii) in one sector `sec`: Corollary 7.4(ii)'s finite exceptional set (along `I`) and `E_1 = 0`. It
takes the equalities `E_1 = E_2 = 0` only (no `0 < E_3`): it serves `odd_many_small` and `ZeroModes.Lower`'s
`odd_many_small'`. -/
theorem odd_many_dev (lam : ℝ) (hlam : 0 < lam) (I : Set ℕ) (Nb : ℕ) (hI : ∀ N, Odd N → 3 ≤ N → Nb ≤ N → N ∈ I)
    (sec : (T : Torus) → SectorLabel T)
    (hzero : ∀ N : ℕ, Odd N → 3 ≤ N → hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) 1 = 0 ∧
      hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) 2 = 0)
    (Dc : ℕ) {γ : ℝ}
    (hfin : {N ∈ I | ¬ Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (rectTorus lam hlam N)
        (sec (rectTorus lam hlam N))))).filter
        fun k => hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) k ∈
          Set.Ico (hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) 1)
            (hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) 1 + γ)).card}.Finite) :
    ∀ᶠ N in atTop ⊓ 𝓟 {N : ℕ | Odd N},
      Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (rectTorus lam hlam N) (sec (rectTorus lam hlam N))))).filter
        fun k => hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) k ∈ Set.Ico 0 γ).card := by
  obtain ⟨B, hB⟩ := hfin.bddAbove
  rw [Filter.eventually_inf_principal, Filter.eventually_atTop]
  refine ⟨max (max Nb 3) (B + 1), fun N hN hodd => ?_⟩
  have hN1 : Nb ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNB : B + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hmem := hI N hodd hN3 hN1
  have h1 : hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) 1 = 0 := (hzero N hodd hN3).1
  have key : Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (rectTorus lam hlam N)
        (sec (rectTorus lam hlam N))))).filter
        fun k => hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) k ∈
          Set.Ico (hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) 1)
            (hcEig (rectTorus lam hlam N) (sec (rectTorus lam hlam N)) 1 + γ)).card := by
    by_contra hc
    have := hB ⟨hmem, hc⟩
    omega
  exact lt_of_lt_of_eq key (congrArg Finset.card (Finset.filter_congr fun k _ => by rw [h1, zero_add]))

end MainDevices

/-! ### Theorem 8.1 -/

/-- **Theorem 8.1(i)**, the divisibility, without the zero modes: "`If for some $p\in\N$, $\Delta\ge0$ and $\gamma>2\Delta$ the inequalities $E_p(N)-E_1(N)\le\Delta$ and $E_{p+1}(N)-E_p(N)\ge\gamma$ hold for infinitely many even $N$, then $p\in4\Z$`". -/
theorem hollow_core_index_four_dvd (lam : ℝ) (hlam : 0 < lam) (p : ℕ) (Δ γ : ℝ) (hΔ : 0 ≤ Δ) (hγ : 2 * Δ < γ)
    (hinf : {N : ℕ | Even N ∧ evenEig lam hlam N p - evenEig lam hlam N 1 ≤ Δ ∧
      γ ≤ evenEig lam hlam N (p + 1) - evenEig lam hlam N p}.Infinite) :
    4 ∣ p := by
  obtain ⟨Nb, -, hNb⟩ := rect_threshold_dev lam hlam
  have hMi := inf_inter_ge_dev hinf Nb
  have hM : ∀ N ∈ {N : ℕ | Even N ∧ evenEig lam hlam N p - evenEig lam hlam N 1 ≤ Δ ∧
      γ ≤ evenEig lam hlam N (p + 1) - evenEig lam hlam N p} ∩ {N | Nb ≤ N},
      0 < N ∧ (rectTorus lam hlam N).Admissible δstd := fun N hN => hNb N hN.2
  have hc : 0 < Real.sqrt (4 * π * lam) := Real.sqrt_pos.2 (by positivity)
  exact four_dvd_hollowCore (rectSeq_dev lam hlam _ hMi hM) _ hc (rectSeq_Lx_dev lam hlam _ hMi hM)
    (fun N hN => hN.1.1) ⟨hΔ, hγ, fun N hN => hN.1.2.1, fun N hN => hN.1.2.2⟩

/-- **Theorem 8.1(i)**: "`If for some $p\in\N$, $\Delta\ge0$ and $\gamma>2\Delta$ the inequalities $E_p(N)-E_1(N)\le\Delta$ and $E_{p+1}(N)-E_p(N)\ge\gamma$ hold for infinitely many even $N$, then $p\in4\Z$ and $p\ge12$.`"
— with the zero modes "`$E_1(N)=\cdots=E_{10}(N)=0<E_{11}(N)$`" as the hypothesis `hzero`. -/
theorem hollow_core_index (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, 0 < N → Even N → HasTenZeroModes (rectTorus lam hlam N))
    (p : ℕ) (Δ γ : ℝ) (hΔ : 0 ≤ Δ) (hγ : 2 * Δ < γ)
    (hinf : {N : ℕ | Even N ∧ evenEig lam hlam N p - evenEig lam hlam N 1 ≤ Δ ∧
      γ ≤ evenEig lam hlam N (p + 1) - evenEig lam hlam N p}.Infinite) :
    4 ∣ p ∧ 12 ≤ p := by
  have h4 := hollow_core_index_four_dvd lam hlam p Δ γ hΔ hγ hinf
  refine ⟨h4, ?_⟩
  obtain ⟨N, hN, hNpos⟩ := hinf.exists_gt 0
  obtain ⟨heven, -, hgap⟩ := hN
  have hp1 : 1 ≤ p := (one_le_p_lt_finrank (by linarith) hgap).1
  have hz : ∀ k : ℕ, 1 ≤ k → k ≤ 10 → evenEig lam hlam N k = 0 := (hzero N hNpos heven).1
  by_contra hlt
  push Not at hlt
  have hp10 : 10 ≤ p := by
    by_contra h
    push Not at h
    rw [hz (p + 1) (by omega) (by omega), hz p hp1 (by omega)] at hgap
    linarith
  omega

/-- **Theorem 8.1(ii)**: "`$E_{11}(N)\to0$ as $N\to\infty$ through the even integers.`" — under the zero modes. -/
theorem hollow_core_E11_tendsto (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, 0 < N → Even N → HasTenZeroModes (rectTorus lam hlam N)) :
    Tendsto (fun N => evenEig lam hlam N 11) (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rw [Filter.eventually_inf_principal]
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN heven
    have h : 0 < evenEig lam hlam N 11 := (hzero N hN heven).2
    linarith
  · by_contra h
    rw [Filter.not_eventually, Filter.frequently_inf_principal, Nat.frequently_atTop_iff_infinite] at h
    have h' := h.sdiff (Set.finite_singleton 0)
    have h4 := hollow_core_index_four_dvd lam hlam 10 0 a le_rfl (by linarith) (h'.mono fun N hN => ?_)
    · omega
    · obtain ⟨⟨heven, hge⟩, hne⟩ := hN
      have hNpos : 0 < N := Nat.pos_of_ne_zero hne
      have hz : ∀ k : ℕ, 1 ≤ k → k ≤ 10 → evenEig lam hlam N k = 0 := (hzero N hNpos heven).1
      refine ⟨heven, ?_, ?_⟩
      · rw [hz 10 (by norm_num) le_rfl, hz 1 le_rfl (by norm_num), sub_self]
      · rw [hz 10 (by norm_num) le_rfl, sub_zero]
        push Not at hge
        exact hge

/-! ### Corollary 8.2 (odd `N`) -/

/-- **Corollary 8.2(i)**: "`$E_3(N)\to0$ as $N\to\infty$ through the odd integers.`" — in both sectors, under
"`$E_1(N)=E_2(N)=0<E_3(N)$`" for odd `N ≥ 3`. -/
theorem odd_E3_tendsto (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, Odd N → 3 ≤ N → HasTwoZeroModes (rectTorus lam hlam N) (oddSectorPlus (rectTorus lam hlam N)) ∧
      HasTwoZeroModes (rectTorus lam hlam N) (oddSectorMinus (rectTorus lam hlam N))) :
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
      (fun N h1 h2 h3 => ⟨⟨h1, h2⟩, h3⟩) oddSectorPlus
      (fun N h1 h2 => ⟨(hzero N h1 h2).1.1, (hzero N h1 h2).1.2.1⟩) hng1,
    odd_E3_dev lam hlam (hcSetting (rectSeq_dev lam hlam _ hMi hM) _ hc hLx).Ts.idx Nb
      (fun N h1 h2 h3 => ⟨⟨h1, h2⟩, h3⟩) oddSectorMinus
      (fun N h1 h2 => ⟨(hzero N h1 h2).2.1, (hzero N h1 h2).2.2.1⟩) hng2⟩

/-- **Corollary 8.2(ii)**: "`For every $D\in\N$ and $\gamma>0$, for all sufficiently large odd $N$ there are more than $D$ eigenvalues in $[0,\gamma)$.`"
— in each sector, counted with multiplicity among `E_1, …, E_d`, `d` the sector's dimension (the paper's `D` is `Dc`). -/
theorem odd_many_small (lam : ℝ) (hlam : 0 < lam)
    (hzero : ∀ N : ℕ, Odd N → 3 ≤ N → HasTwoZeroModes (rectTorus lam hlam N) (oddSectorPlus (rectTorus lam hlam N)) ∧
      HasTwoZeroModes (rectTorus lam hlam N) (oddSectorMinus (rectTorus lam hlam N)))
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
      (fun N h1 h2 h3 => ⟨⟨h1, h2⟩, h3⟩) oddSectorPlus
      (fun N h1 h2 => ⟨(hzero N h1 h2).1.1, (hzero N h1 h2).1.2.1⟩) Dc hf1).and
    (odd_many_dev lam hlam (hcSetting (rectSeq_dev lam hlam _ hMi hM) _ hc hLx).Ts.idx Nb
      (fun N h1 h2 h3 => ⟨⟨h1, h2⟩, h3⟩) oddSectorMinus
      (fun N h1 h2 => ⟨(hzero N h1 h2).2.1, (hzero N h1 h2).2.2.1⟩) Dc hf2)

/-! ### Proof devices for Lemma 8.3 (phase (b), round three; not statements of the paper)

The change of variables of the proof: `σ(x, y) = (L_x − y, x)` (`rotME_dev`, the rotation `ϱ` followed by the translation
by `(L_x, 0)`) is a measure-preserving bijection of `ℝ²` with `σ⁻¹((0, L_x] × [0, L_y)) = [0, L_y) × [0, L_x)`, the
fundamental domain of `𝕋'_N`; so `∫_{𝕋'_N} F∘ϱ = ∫_{𝕋_N} F` for `F` periodic in `x` with period `L_x`
(`integral_rot_dev`; the proof: "`and hence induces a measure-preserving bijection of $\Tor'_N$ onto $\Tor_N$`"). -/

section ExchangeDevices

def rotME_dev (L : ℝ) : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun r := (L - r.2, r.1)
  invFun p := (p.2, L - p.1)
  left_inv r := by simp
  right_inv p := by simp
  measurable_toFun := (measurable_const.sub measurable_snd).prodMk measurable_fst
  measurable_invFun := measurable_snd.prodMk (measurable_const.sub measurable_fst)

theorem rotME_mp_dev (L : ℝ) : MeasurePreserving (rotME_dev L) volume volume :=
  ((Measure.measurePreserving_sub_left volume L).prod (MeasurePreserving.id volume)).comp
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))

theorem integral_rot_dev (T : Torus) (F : ℝ × ℝ → ℂ) (hF : ∀ u v : ℝ, F (u + T.Lx, v) = F (u, v)) :
    ∫ r in fundDom (swapTorus T), F (-r.2, r.1) = ∫ r in fundDom T, F r := by
  have hpre : (rotME_dev T.Lx) ⁻¹' (Set.Ioc 0 T.Lx ×ˢ Set.Ico 0 T.Ly) = fundDom (swapTorus T) := by
    ext ⟨x, y⟩
    show (0 < T.Lx - y ∧ T.Lx - y ≤ T.Lx) ∧ 0 ≤ x ∧ x < T.Ly ↔ (0 ≤ x ∧ x < T.Ly) ∧ 0 ≤ y ∧ y < T.Lx
    constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have h1 : (fun r : ℝ × ℝ => F (-r.2, r.1)) = fun r => F (rotME_dev T.Lx r) := by
    funext r
    show F (-r.2, r.1) = F (T.Lx - r.2, r.1)
    rw [← hF (-r.2) r.1, neg_add_eq_sub]
  rw [h1, ← hpre, (rotME_mp_dev T.Lx).setIntegral_preimage_emb (rotME_dev T.Lx).measurableEmbedding]
  exact setIntegral_congr_set
    (Measure.set_prod_ae_eq (Ioc_ae_eq_Icc.trans Ico_ae_eq_Icc.symm) Filter.EventuallyEq.rfl)

/-- A unitary `U` that commutes with `N_↑`, `N_↓` maps each eigenspace of `H` in a sector onto the eigenspace of
`UHU^*` in the same sector, so the counting functions agree (the proof: "`So the unitary maps each sector $\sect\nn$
onto the sector of $\mathcal H'_N$ with the same label and intertwines the restrictions`"). -/
theorem countLE_conj_dev {T : Torus} {H U : FockOp T} (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hUs : IsSectorPreserving T U) (nn : SectorLabel T) (E : ℝ) :
    countLE T (U * H * Uᴴ) nn E = countLE T H nn E := by
  have e1 : ∀ w : FockSpace T, toCLM T U (toCLM T Uᴴ w) = w := fun w => by
    rw [← mul_apply_eq_comp, ← map_mul, hU2, map_one, one_apply_eq_self]
  have e2 : ∀ w : FockSpace T, toCLM T Uᴴ (toCLM T U w) = w := fun w => by
    rw [← mul_apply_eq_comp, ← map_mul, hU1, map_one, one_apply_eq_self]
  let e : FockSpace T ≃ₗ[ℂ] FockSpace T :=
    { toFun := fun w => toCLM T U w
      map_add' := fun a b => map_add _ a b
      map_smul' := fun c a => map_smul _ c a
      invFun := fun w => toCLM T Uᴴ w
      left_inv := e2
      right_inv := e1 }
  have hconj : ∀ (A : FockOp T) (c : ℂ) (v : FockSpace T),
      toCLM T A (toCLM T Uᴴ v) = c • toCLM T Uᴴ v ↔ toCLM T (U * A * Uᴴ) v = c • v := by
    intro A c v
    have e3 : toCLM T (U * A * Uᴴ) v = toCLM T U (toCLM T A (toCLM T Uᴴ v)) := by
      simp only [toCLM, map_mul, mul_apply_eq_comp]
    rw [e3]
    constructor
    · intro h
      rw [h, map_smul, e1]
    · intro h
      have h' := congrArg (toCLM T Uᴴ) h
      rwa [e2, map_smul] at h'
  have hNσ : ∀ σ : Spin, U * Nsig T σ * Uᴴ = Nsig T σ := by
    intro σ
    have hc : Commute U (Nsig T σ) := by
      cases σ
      · exact hUs.1
      · exact hUs.2
    rw [hc.eq, mul_assoc, hU2, mul_one]
  have hmap : ∀ μ : ℝ, (Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) H) (μ : ℂ) ⊓ sector T nn).map (e : FockSpace T →ₗ[ℂ] FockSpace T) =
      Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (U * H * Uᴴ)) (μ : ℂ) ⊓ sector T nn := by
    intro μ
    ext v
    rw [Submodule.mem_map_equiv]
    simp only [Submodule.mem_inf, sector, Module.End.mem_eigenspace_iff, toEuclideanLin_apply_dev]
    show (toCLM T H (toCLM T Uᴴ v) = (μ : ℂ) • toCLM T Uᴴ v ∧
        toCLM T (Nsig T .up) (toCLM T Uᴴ v) = (((nn.1 : ℕ) : ℝ) : ℂ) • toCLM T Uᴴ v ∧
        toCLM T (Nsig T .dn) (toCLM T Uᴴ v) = (((nn.2 : ℕ) : ℝ) : ℂ) • toCLM T Uᴴ v) ↔
      (toCLM T (U * H * Uᴴ) v = (μ : ℂ) • v ∧ toCLM T (Nsig T .up) v = (((nn.1 : ℕ) : ℝ) : ℂ) • v ∧
        toCLM T (Nsig T .dn) v = (((nn.2 : ℕ) : ℝ) : ℂ) • v)
    rw [hconj, hconj, hconj, hNσ, hNσ]
  have hsup : (⨆ μ ∈ Set.Iic E, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) H) (μ : ℂ) ⊓ sector T nn).map (e : FockSpace T →ₗ[ℂ] FockSpace T) =
      ⨆ μ ∈ Set.Iic E, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (U * H * Uᴴ)) (μ : ℂ) ⊓ sector T nn := by
    simp_rw [Submodule.map_iSup, hmap]
  unfold countLE
  rw [← hsup]
  exact LinearEquiv.finrank_map_eq e _

/-- Unitary invariance of the ordered eigenvalues in a sector (`countLE_conj_dev` and `secEig_eq_sInf_countLE`). -/
theorem secEig_conj_dev {T : Torus} {H U : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hUs : IsSectorPreserving T U) (nn : SectorLabel T) (k : ℕ) :
    secEig T (U * H * Uᴴ) nn k = secEig T H nn k := by
  have hUsc : ∀ σ : Spin, Commute U (Nsig T σ) := by
    intro σ
    cases σ
    · exact hUs.1
    · exact hUs.2
  have hUsc' : ∀ σ : Spin, Commute Uᴴ (Nsig T σ) := by
    intro σ
    have h := (hUsc σ).star_star
    rwa [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, Nsig_conjTranspose] at h
  have hHsc : ∀ σ : Spin, Commute H (Nsig T σ) := by
    intro σ
    cases σ
    · exact hHs.1
    · exact hHs.2
  have hH' : IsSelfAdjoint (U * H * Uᴴ) := hH.conjugate U
  have hHs' : IsSectorPreserving T (U * H * Uᴴ) :=
    ⟨((hUsc _).mul_left (hHsc _)).mul_left (hUsc' _), ((hUsc _).mul_left (hHsc _)).mul_left (hUsc' _)⟩
  rw [secEig_eq_sInf_countLE hH' hHs', secEig_eq_sInf_countLE hH hHs]
  simp_rw [countLE_conj_dev hU1 hU2 hUs]

/-- `U A U^* = A` with `U^*U = 1` gives `[U, A] = 0`. -/
theorem commute_of_conj_dev {T : Torus} {U A : FockOp T} (hU1 : Uᴴ * U = 1) (h : U * A * Uᴴ = A) : Commute U A := by
  show U * A = A * U
  calc U * A = U * A * (Uᴴ * U) := by rw [hU1, mul_one]
    _ = (U * A * Uᴴ) * U := by simp only [mul_assoc]
    _ = A * U := by rw [h]

end ExchangeDevices

/-! ### Lemma 8.3 (exchange of the sides) -/

/-- **Lemma 8.3**: `𝓡` maps the lowest Landau level of `𝕋_N` into that of `𝕋'_N` (the proof: "`which are the conditions \eqref{eq:bc} for $\Tor'_N$`",
and `(D_x + iD_y)𝓡f = 0`). -/
theorem isLLL_rotFun (T : Torus) {f : ℝ × ℝ → ℂ} (hf : IsLLL T f) : IsLLL (swapTorus T) (rotFun f) := by
  refine ⟨?_, fun x y => ?_, fun x y => ?_, fun r => ?_⟩
  · have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ × ℝ => Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) :=
      Complex.contDiff_exp.comp ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst)).mul
        (Complex.ofRealCLM.contDiff.comp contDiff_snd))
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ × ℝ => ((-r.2, r.1) : ℝ × ℝ)) :=
      contDiff_snd.neg.prodMk contDiff_fst
    exact h1.mul (hf.1.comp h2)
  · show Complex.exp (I * (x : ℂ) * ((y + T.Lx : ℝ) : ℂ)) * f (-(y + T.Lx), x) =
      Complex.exp (I * (x : ℂ) * (y : ℂ)) * f (-y, x)
    have hq : f (-y, x) = Complex.exp (I * (T.Lx : ℂ) * (x : ℂ)) * f (-(y + T.Lx), x) := by
      have h := hf.2.2.1 (-(y + T.Lx)) x
      rw [show -(y + T.Lx) + T.Lx = -y by ring] at h
      exact h
    rw [hq, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · show Complex.exp (I * ((x + T.Ly : ℝ) : ℂ) * (y : ℂ)) * f (-y, x + T.Ly) =
      Complex.exp (I * (T.Ly : ℂ) * (y : ℂ)) * (Complex.exp (I * (x : ℂ) * (y : ℂ)) * f (-y, x))
    rw [hf.2.1 (-y) x, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · obtain ⟨x, y⟩ := r
    have hEx : HasDerivAt (fun x' : ℝ => Complex.exp (I * (x' : ℂ) * (y : ℂ)))
        (Complex.exp (I * (x : ℂ) * (y : ℂ)) * (I * (y : ℂ))) x := by
      have h0 : HasDerivAt (fun w : ℂ => I * w * (y : ℂ)) (I * (y : ℂ)) (x : ℂ) := by
        simpa using ((hasDerivAt_id (x : ℂ)).const_mul I).mul_const (y : ℂ)
      exact h0.cexp.comp_ofReal
    have hEy : HasDerivAt (fun y' : ℝ => Complex.exp (I * (x : ℂ) * (y' : ℂ)))
        (Complex.exp (I * (x : ℂ) * (y : ℂ)) * (I * (x : ℂ))) y := by
      have h0 : HasDerivAt (fun w : ℂ => I * (x : ℂ) * w) (I * (x : ℂ)) (y : ℂ) := by
        simpa using (hasDerivAt_id (y : ℂ)).const_mul (I * (x : ℂ))
      exact h0.cexp.comp_ofReal
    have hfx : HasDerivAt (fun x' : ℝ => f (-y, x')) (fderiv ℝ f (-y, x) (0, 1)) x :=
      lll_hasDerivAt_y_dev hf (-y) x
    have hfy : HasDerivAt (fun y' : ℝ => f (-y', x)) (-(fderiv ℝ f (-y, x) (1, 0))) y := by
      have h := (lll_hasDerivAt_x_dev hf (-y) x).scomp y (hasDerivAt_neg y)
      rw [neg_one_smul] at h
      exact h
    have hDx : Dx (rotFun f) (x, y) = Complex.exp (I * (x : ℂ) * (y : ℂ)) * (I * (y : ℂ)) * f (-y, x) +
        Complex.exp (I * (x : ℂ) * (y : ℂ)) * fderiv ℝ f (-y, x) (0, 1) := by
      show deriv (fun x' : ℝ => Complex.exp (I * (x' : ℂ) * (y : ℂ)) * f (-y, x')) x = _
      exact (hEx.mul hfx).deriv
    have hDy : Dy (rotFun f) (x, y) = Complex.exp (I * (x : ℂ) * (y : ℂ)) * (I * (x : ℂ)) * f (-y, x) +
        Complex.exp (I * (x : ℂ) * (y : ℂ)) * (-(fderiv ℝ f (-y, x) (1, 0))) -
        I * (x : ℂ) * (Complex.exp (I * (x : ℂ) * (y : ℂ)) * f (-y, x)) := by
      show deriv (fun y' : ℝ => Complex.exp (I * (x : ℂ) * (y' : ℂ)) * f (-y', x)) y -
        I * (x : ℂ) * (Complex.exp (I * (x : ℂ) * (y : ℂ)) * f (-y, x)) = _
      rw [show deriv (fun y' : ℝ => Complex.exp (I * (x : ℂ) * (y' : ℂ)) * f (-y', x)) y = _ from
        (hEy.mul hfy).deriv]
    rw [hDx, hDy, lll_dx_eq_dev hf (-y) x]
    push_cast
    linear_combination (Complex.exp (I * (x : ℂ) * (y : ℂ)) * fderiv ℝ f (-y, x) (0, 1)) * Complex.I_sq

/-- **Lemma 8.3**: `𝓡` is isometric for the inner products of Definition 2.1 ("`so $\ip{\mathcal Rf_1}{\mathcal Rf_2}=\ip{f_1}{f_2}$ by the first paragraph`"). -/
theorem l2inner_rotFun (T : Torus) {f g : ℝ × ℝ → ℂ} (hf : IsLLL T f) (hg : IsLLL T g) :
    l2inner (swapTorus T) (rotFun f) (rotFun g) = l2inner T f g := by
  have hpt : ∀ r : ℝ × ℝ, star (rotFun f r) * rotFun g r = star (f (-r.2, r.1)) * g (-r.2, r.1) := by
    intro r
    simp only [rotFun, star_mul']
    calc star (Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) * star (f (-r.2, r.1)) *
          (Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)) * g (-r.2, r.1))
        = (star (Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) * Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) *
          (star (f (-r.2, r.1)) * g (-r.2, r.1)) := by ring
      _ = _ := by rw [star_exp_mul_self, one_mul]
  have hF : ∀ u v : ℝ, star (f (u + T.Lx, v)) * g (u + T.Lx, v) = star (f (u, v)) * g (u, v) := by
    intro u v
    rw [hf.2.2.1 u v, hg.2.2.1 u v, star_mul']
    calc star (Complex.exp (I * (T.Lx : ℂ) * (v : ℂ))) * star (f (u, v)) *
          (Complex.exp (I * (T.Lx : ℂ) * (v : ℂ)) * g (u, v))
        = (star (Complex.exp (I * (T.Lx : ℂ) * (v : ℂ))) * Complex.exp (I * (T.Lx : ℂ) * (v : ℂ))) *
          (star (f (u, v)) * g (u, v)) := by ring
      _ = _ := by rw [star_exp_mul_self, one_mul]
  unfold l2inner
  simp_rw [hpt]
  exact integral_rot_dev T (fun p => star (f p) * g p) hF

/-- **Lemma 8.3** on block A's abstract spaces: `rotLin` is `𝓡` (the function represented by `rotLin T f` is `𝓡`
of the function represented by `f`). -/
theorem toFun_rotLin (T : Torus) (f : Space T) : toFun (swapTorus T) (rotLin T f) = rotFun (toFun T f) := by
  have hpsi : ∀ (j : ZMod T.Nφ) (R : ℝ × ℝ),
      rotFun (psi T j) R = ∑ k, rotMat T k j * psi (swapTorus T) k R := by
    intro j R
    obtain ⟨c, hc⟩ := (isLLL_iff (swapTorus T) _).1 (isLLL_rotFun T (psi_isLLL T j))
    have hck : ∀ k, c k = rotMat T k j := by
      intro k
      have h := l2inner_toFun (swapTorus T) (orb (swapTorus T) k) c
      rw [toFun_orb, hc] at h
      rw [rotMat, Matrix.of_apply, h, orb, EuclideanSpace.inner_single_left]
      simp
    rw [← hc, toFun]
    exact Finset.sum_congr rfl fun k _ => by rw [hck k]
  funext R
  have hk : ∀ k : ZMod (swapTorus T).Nφ, (rotLin T f) k = ∑ j, rotMat T k j * f j := fun k => rfl
  have hR : rotFun (toFun T f) R = ∑ j, f j * rotFun (psi T j) R := by
    simp only [rotFun, toFun, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hR, toFun]
  simp_rw [hk, hpsi, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- **Lemma 8.3**: "`Then $\mathcal R$ is a unitary from $\hN$ onto $\mathfrak h'_N$`" — its matrix is unitary. -/
theorem rotMat_unitary (T : Torus) :
    ((rotMat T)ᴴ * rotMat T : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) = 1 ∧
      (rotMat T * (rotMat T)ᴴ : Matrix (ZMod (swapTorus T).Nφ) (ZMod (swapTorus T).Nφ) ℂ) = 1 := by
  have hiso : ∀ f g : Space T, ⟪rotLin T f, rotLin T g⟫_ℂ = ⟪f, g⟫_ℂ := by
    intro f g
    rw [← l2inner_toFun, ← l2inner_toFun, toFun_rotLin, toFun_rotLin]
    exact l2inner_rotFun T ((isLLL_iff T _).2 ⟨f, rfl⟩) ((isLLL_iff T _).2 ⟨g, rfl⟩)
  have hcol : ∀ i : ZMod T.Nφ, rotLin T (orb T i) = WithLp.toLp 2 ((rotMat T)ᵀ i) := by
    intro i
    show WithLp.toLp 2 (rotMat T *ᵥ Pi.single i 1) = _
    rw [Matrix.mulVec_single_one]
    rfl
  have h1 : ((rotMat T)ᴴ * rotMat T : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) = 1 := by
    ext i j
    rw [← inner_matrix_col_col, ← hcol, ← hcol, hiso]
    by_cases h : i = j
    · subst h
      simp [orb]
    · simp [orb, h, EuclideanSpace.inner_single_left]
  exact ⟨h1, mul_eq_one_comm.mp h1⟩

/-- **Lemma 8.3**: "`the unitary $\Ff(\mathcal R\otimes\one):\Fock\to\mathcal H'_N$ that fixes the vacuum and satisfies $\Ff(\mathcal R\otimes\one)\,c(f)\,\Ff(\mathcal R\otimes\one)^*=c'((\mathcal R\otimes\one)f)$ for $f\in\kN$`"
— unitary, fixing the vacuum, intertwining the annihilators. -/
theorem FfR_props (T : Torus) :
    ((FfR T)ᴴ * FfR T : Matrix (Conf (ZMod T.Nφ)) (Conf (ZMod T.Nφ)) ℂ) = 1 ∧
      (FfR T * (FfR T)ᴴ : Matrix (Conf (ZMod (swapTorus T).Nφ)) (Conf (ZMod (swapTorus T).Nφ)) ℂ) = 1 ∧
      (FfR T).mulVec (Pi.single (vac : Conf (ZMod T.Nφ)) (1 : ℂ)) =
        Pi.single (vac : Conf (ZMod (swapTorus T).Nφ)) (1 : ℂ) ∧
      ∀ f : Space2 T, FfR T * cf T f * (FfR T)ᴴ = cf (swapTorus T) (Matrix.toEuclideanLin (rot2 T) f) := by
  have hM := (rotMat_unitary T).1
  have hU : ((rot2 T)ᴴ * rot2 T : Matrix (Modes T) (Modes T) ℂ) = 1 := by
    show ((Matrix.kroneckerMap (· * ·) (rotMat T) (1 : Matrix Spin Spin ℂ))ᴴ *
      Matrix.kroneckerMap (· * ·) (rotMat T) (1 : Matrix Spin Spin ℂ) : Matrix (Modes T) (Modes T) ℂ) = 1
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hM, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.one_kronecker_one]
  have h1 : ((FfR T)ᴴ * FfR T : Matrix (Conf (ZMod T.Nφ)) (Conf (ZMod T.Nφ)) ℂ) = 1 :=
    secondQuant_conjTranspose_mul_self_rect hU
  have h2 : (FfR T * (FfR T)ᴴ : Matrix (Conf (ZMod (swapTorus T).Nφ)) (Conf (ZMod (swapTorus T).Nφ)) ℂ) = 1 :=
    mul_eq_one_comm.mp h1
  refine ⟨h1, h2, ?_, fun f => ?_⟩
  · rw [Matrix.mulVec_single_one]
    funext m'
    show secondQuant (rot2 T) m' vac = _
    rw [secondQuant_apply_vac]
    simp [Pi.single_apply]
  · have hc := secondQuant_mul_cVec hU (fun μ => f μ)
    calc FfR T * cf T f * (FfR T)ᴴ
        = (cVec (rot2 T *ᵥ fun μ => f μ) * secondQuant (rot2 T)) * (secondQuant (rot2 T))ᴴ :=
          congrArg (· * (FfR T)ᴴ) hc
      _ = cVec (rot2 T *ᵥ fun μ => f μ) * (secondQuant (rot2 T) * (secondQuant (rot2 T))ᴴ) :=
          Matrix.mul_assoc _ _ _
      _ = cVec (rot2 T *ᵥ fun μ => f μ) * 1 := congrArg (cVec (rot2 T *ᵥ fun μ => f μ) * ·) h2
      _ = cf (swapTorus T) (Matrix.toEuclideanLin (rot2 T) f) := Matrix.mul_one _

/-! ### Proof devices for `FfR_conj` (phase (b), round three; not statements of the paper)

On `𝓗_N` (the Fock spaces of `𝕋_N` and `𝕋'_N` are one type, the orbital labels being `ℤ_{N_φ}` for both):
`𝔉(𝓡 ⊗ 1)` conjugates `c_{jσ}` into `Σ_k \overline{M_{kj}} c'_{kσ}` (`M = rotMat T`, `conj_cjs_dev`), so `N_σ ↦ N'_σ` by
`MM^* = 1` (`conj_Nsig_dev`); for `H_N` the local form `H_N = ∫ h_R dR` of Theorem 4.2(a): with `ϱ r = (−r_y, r_x)`,
`𝓡 e_{ϱ r} = e^{ir_xr_y} e'_r` and `𝓡 e^D_{ϱ r} = i e^{ir_xr_y} e'^D_r` (`rotLin_ev_dev`, `rotLin_evD_dev`, from
`D(𝓡f) = i e^{ixy} (Df)∘ϱ`), so `𝔉 B_ν(ϱ r) 𝔉^* = (phase) B'_ν(r)` with a phase of modulus one, `𝔉 h_{ϱ r} 𝔉^* = h'_r`
(`conj_hR_dev`), and the change of variables `integral_rot_dev` (`conj_HN_dev`) — the paper's route is through the
coefficients `V_{abcd}` and a change of basis; this one uses block C's local form instead (the hand-back says so). -/

section FfRConjDevices

theorem rot2_unitary_dev (T : Torus) : ((rot2 T)ᴴ * rot2 T : Matrix (Modes T) (Modes T) ℂ) = 1 := by
  show ((Matrix.kroneckerMap (· * ·) (rotMat T) (1 : Matrix Spin Spin ℂ))ᴴ *
    Matrix.kroneckerMap (· * ·) (rotMat T) (1 : Matrix Spin Spin ℂ) : Matrix (Modes T) (Modes T) ℂ) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, (rotMat_unitary T).1, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.one_kronecker_one]

theorem conj_cjs_dev (T : Torus) (U : FockOp T) (M : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) (hU2 : U * Uᴴ = 1)
    (hsq : ∀ ν : Modes T, U * HRTorus.Fermion.Pilot.JW.c ν =
      cVec (fun ρ => Matrix.kronecker M (1 : Matrix Spin Spin ℂ) ρ ν) * U)
    (j : ZMod T.Nφ) (σ : Spin) :
    U * cjs T j σ * Uᴴ = ∑ k, star (M k j) • cjs T k σ := by
  rw [cjs_eq, hsq, mul_assoc, hU2, mul_one, cVec, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cjs_eq]
  have hs : ∀ (F : Spin → FockOp T), ∑ τ : Spin, F τ = F .up + F .dn := fun F => by
    rw [show (Finset.univ : Finset Spin) = {Spin.up, Spin.dn} from rfl, Finset.sum_pair (by decide)]
  rw [hs]
  cases σ <;> simp

/-- `Σ_j (Σ_k M_{kj} A_k)(Σ_l \overline{M_{lj}} B_l) = Σ_k A_k B_k` for `MM^* = 1`. -/
theorem sum_contract_dev {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R] [Algebra ℂ R]
    (M : Matrix ι ι ℂ) (hM2 : M * Mᴴ = 1) (A B : ι → R) :
    ∑ j, (∑ k, M k j • A k) * (∑ l, star (M l j) • B l) = ∑ k, A k * B k := by
  have hMkl : ∀ k l, ∑ j, M k j * star (M l j) = if k = l then 1 else 0 := by
    intro k l
    have h := congrFun (congrFun hM2 k) l
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [Matrix.conjTranspose_apply] using h
  calc ∑ j, (∑ k, M k j • A k) * (∑ l, star (M l j) • B l)
      = ∑ j, ∑ k, ∑ l, (M k j * star (M l j)) • (A k * B l) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = ∑ k, ∑ l, (∑ j, M k j * star (M l j)) • (A k * B l) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, A k * B k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hMkl, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem conj_Nsig_dev (T : Torus) (U : FockOp T) (M : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) (hU1 : Uᴴ * U = 1)
    (hM2 : M * Mᴴ = 1)
    (hc : ∀ (j : ZMod T.Nφ) (σ : Spin), U * cjs T j σ * Uᴴ = ∑ k, star (M k j) • cjs T k σ) (σ : Spin) :
    U * Nsig T σ * Uᴴ = Nsig T σ := by
  have hc' : ∀ j, U * (cjs T j σ)ᴴ * Uᴴ = ∑ k, M k j • (cjs T k σ)ᴴ := by
    intro j
    have h := congrArg Matrix.conjTranspose (hc j σ)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul, star_star] at h
    rw [← h, mul_assoc]
  have hn : ∀ j, U * ((cjs T j σ)ᴴ * cjs T j σ) * Uᴴ = (U * (cjs T j σ)ᴴ * Uᴴ) * (U * cjs T j σ * Uᴴ) := by
    intro j
    calc U * ((cjs T j σ)ᴴ * cjs T j σ) * Uᴴ = U * (cjs T j σ)ᴴ * (Uᴴ * U) * cjs T j σ * Uᴴ := by
          rw [hU1, mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  calc U * Nsig T σ * Uᴴ = ∑ j, (U * (cjs T j σ)ᴴ * Uᴴ) * (U * cjs T j σ * Uᴴ) := by
        rw [Nsig, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => hn j
    _ = ∑ j, (∑ k, M k j • (cjs T k σ)ᴴ) * (∑ l, star (M l j) • cjs T l σ) := by
        simp only [hc', hc]
    _ = ∑ k, (cjs T k σ)ᴴ * cjs T k σ := sum_contract_dev M hM2 _ _
    _ = Nsig T σ := rfl

theorem Dx_rotFun_dev (T : Torus) {f : ℝ × ℝ → ℂ} (hf : IsLLL T f) (x y : ℝ) :
    Dx (rotFun f) (x, y) = I * Complex.exp (I * (x : ℂ) * (y : ℂ)) * Dx f (-y, x) := by
  have hEx : HasDerivAt (fun x' : ℝ => Complex.exp (I * (x' : ℂ) * (y : ℂ)))
      (Complex.exp (I * (x : ℂ) * (y : ℂ)) * (I * (y : ℂ))) x := by
    have h0 : HasDerivAt (fun w : ℂ => I * w * (y : ℂ)) (I * (y : ℂ)) (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul I).mul_const (y : ℂ)
    exact h0.cexp.comp_ofReal
  have hfx : HasDerivAt (fun x' : ℝ => f (-y, x')) (fderiv ℝ f (-y, x) (0, 1)) x :=
    lll_hasDerivAt_y_dev hf (-y) x
  have hDx : Dx (rotFun f) (x, y) = Complex.exp (I * (x : ℂ) * (y : ℂ)) * (I * (y : ℂ)) * f (-y, x) +
      Complex.exp (I * (x : ℂ) * (y : ℂ)) * fderiv ℝ f (-y, x) (0, 1) := by
    show deriv (fun x' : ℝ => Complex.exp (I * (x' : ℂ) * (y : ℂ)) * f (-y, x')) x = _
    exact (hEx.mul hfx).deriv
  have hDf : Dx f (-y, x) = fderiv ℝ f (-y, x) (1, 0) := (lll_hasDerivAt_x_dev hf (-y) x).deriv
  rw [hDx, hDf, lll_dx_eq_dev hf (-y) x]
  push_cast
  linear_combination (Complex.exp (I * (x : ℂ) * (y : ℂ)) * fderiv ℝ f (-y, x) (0, 1)) * Complex.I_sq

theorem Dcov_rotFun_dev (T : Torus) {f : ℝ × ℝ → ℂ} (hf : IsLLL T f) (r : ℝ × ℝ) :
    Dcov (rotFun f) r = I * Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)) * Dcov f (-r.2, r.1) := by
  rw [Dcov_eq_Dx_of_isLLL (swapTorus T) (isLLL_rotFun T hf), Dcov_eq_Dx_of_isLLL T hf]
  exact Dx_rotFun_dev T hf r.1 r.2

/-- `ψ'_k = 𝓡(Σ_j \overline{M_{kj}} ψ_j)` (`MM^* = 1`). -/
theorem psi_swap_dev (T : Torus) (k : ZMod (swapTorus T).Nφ) (R : ℝ × ℝ) :
    psi (swapTorus T) k R = rotFun (toFun T (WithLp.toLp 2 fun j => star (rotMat T k j))) R := by
  rw [← toFun_rotLin]
  have hMkl : ∀ l : ZMod (swapTorus T).Nφ,
      (rotLin T (WithLp.toLp 2 fun j => star (rotMat T k j))) l = if l = k then 1 else 0 := by
    intro l
    have h := congrFun (congrFun (rotMat_unitary T).2 l) k
    have e : (rotMat T * (rotMat T)ᴴ : Matrix (ZMod (swapTorus T).Nφ) (ZMod (swapTorus T).Nφ) ℂ) l k =
        ∑ j, rotMat T l j * star (rotMat T k j) := Matrix.mul_apply
    rw [e, Matrix.one_apply] at h
    exact h
  simp only [toFun, hMkl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem rotLin_ev_dev (T : Torus) (r : ℝ × ℝ) :
    rotLin T (ev T (-r.2, r.1)) = Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)) • ev (swapTorus T) r := by
  refine PiLp.ext fun k => ?_
  have hk : (rotLin T (ev T (-r.2, r.1))) k = ∑ j, rotMat T k j * star (psi T j (-r.2, r.1)) := by
    show ∑ j, rotMat T k j * (ev T (-r.2, r.1)) j = _
    simp only [ev_apply]
  have hE : Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)) * star (Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) = 1 := by
    rw [mul_comm]
    exact star_exp_mul_self r.1 r.2
  rw [hk, PiLp.smul_apply, ev_apply, psi_swap_dev T k r, smul_eq_mul]
  simp only [rotFun, toFun, star_mul', star_sum, star_star]
  linear_combination (-(∑ j, rotMat T k j * star (psi T j (-r.2, r.1)))) * hE

theorem rotLin_evD_dev (T : Torus) (r : ℝ × ℝ) :
    rotLin T (evD T (-r.2, r.1)) = (I * Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) • evD (swapTorus T) r := by
  refine PiLp.ext fun k => ?_
  have hk : (rotLin T (evD T (-r.2, r.1))) k = ∑ j, rotMat T k j * star (Dcov (psi T j) (-r.2, r.1)) := by
    show ∑ j, rotMat T k j * (evD T (-r.2, r.1)) j = _
    simp only [evD_apply]
  have hpsi : psi (swapTorus T) k = rotFun (toFun T (WithLp.toLp 2 fun j => star (rotMat T k j))) :=
    funext fun R => psi_swap_dev T k R
  have hD : Dcov (psi (swapTorus T) k) r = I * Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)) *
      ∑ j, star (rotMat T k j) * Dcov (psi T j) (-r.2, r.1) := by
    rw [hpsi, Dcov_rotFun_dev T ((isLLL_iff T _).2 ⟨_, rfl⟩) r, Dcov_toFun]
  have hE : (I * Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) *
      (star I * star (Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)))) = 1 := by
    have h := star_exp_mul_self r.1 r.2
    rw [show star I = -I from Complex.conj_I]
    linear_combination (-I ^ 2) * h - Complex.I_sq
  rw [hk, PiLp.smul_apply, evD_apply, hD, smul_eq_mul]
  simp only [star_mul', star_sum, star_star]
  linear_combination (-(∑ j, rotMat T k j * star (Dcov (psi T j) (-r.2, r.1)))) * hE

theorem spinTensor_rot2_dev (T : Torus) (h : Space T) (σ : Spin) :
    Matrix.toEuclideanLin (rot2 T) (spinTensor h σ) = spinTensor (rotLin T h) σ := by
  refine PiLp.ext fun μ => ?_
  rcases μ with ⟨k, τ⟩
  show (rot2 T *ᵥ (spinTensor h σ).ofLp) (k, τ) = (spinTensor (rotLin T h) σ).ofLp (k, τ)
  simp only [spinTensor, rotLin, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, rot2, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, WithLp.ofLp_toLp, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  by_cases hτ : τ = σ
  · subst hτ
    simp
  · simp [hτ]

theorem cpair_smul_smul_dev (T : Torus) (ν : Triplet) (a b : ℂ) (f g : Space T) :
    cpair T ν (a • f) (b • g) = (star a * star b) • cpair T ν f g := by
  have h0l : ∀ g' : Space T, cpair T ν 0 g' = 0 := fun g' => by
    have h := cpair_smul_add_left T ν 1 0 0 g'
    simp only [smul_zero, add_zero, star_one, one_smul] at h
    simpa using h
  have h0r : ∀ f' : Space T, cpair T ν f' 0 = 0 := fun f' => by
    have h := cpair_smul_add_right T ν 1 f' 0 0
    simp only [smul_zero, add_zero, star_one, one_smul] at h
    simpa using h
  have e1 := cpair_smul_add_left T ν a f 0 (b • g)
  have e2 := cpair_smul_add_right T ν b f g 0
  rw [add_zero, h0l, add_zero] at e1
  rw [add_zero, h0r, add_zero] at e2
  rw [e1, e2, smul_smul]

theorem conj_cpair_dev (T : Torus) (U : FockOp T) (hU1 : Uᴴ * U = 1)
    (hcf : ∀ v : Space2 T, U * cf T v * Uᴴ = cf (swapTorus T) (Matrix.toEuclideanLin (rot2 T) v))
    (ν : Triplet) (f g : Space T) :
    U * cpair T ν f g * Uᴴ = cpair (swapTorus T) ν (rotLin T f) (rotLin T g) := by
  have hm : ∀ X Y : FockOp T, U * (X * Y) * Uᴴ = (U * X * Uᴴ) * (U * Y * Uᴴ) := by
    intro X Y
    calc U * (X * Y) * Uᴴ = U * X * (Uᴴ * U) * Y * Uᴴ := by rw [hU1, mul_one]; simp only [mul_assoc]
      _ = (U * X * Uᴴ) * (U * Y * Uᴴ) := by simp only [mul_assoc]
  simp only [cpair, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, hm, hcf, spinTensor_rot2_dev]
  rfl

theorem smul_conj_dev {n : Type*} [Fintype n] [DecidableEq n] (s : ℂ) (hs : star s * s = 1) (B : Matrix n n ℂ) :
    (s • B)ᴴ * (s • B) = Bᴴ * B := by
  rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hs, one_smul]

theorem conj_hR_dev (T : Torus) (U : FockOp T) (hU1 : Uᴴ * U = 1)
    (hcf : ∀ v : Space2 T, U * cf T v * Uᴴ = cf (swapTorus T) (Matrix.toEuclideanLin (rot2 T) v)) (r : ℝ × ℝ) :
    U * hR T (-r.2, r.1) * Uᴴ = hR (swapTorus T) r := by
  have hB : ∀ ν, U * Bν T ν (-r.2, r.1) * Uᴴ = (star (Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) *
      star (I * Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)))) • Bν (swapTorus T) ν r := by
    intro ν
    rw [Bν, Bν, conj_cpair_dev T U hU1 hcf, rotLin_ev_dev, rotLin_evD_dev, cpair_smul_smul_dev]
  have hs : star (star (Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) * star (I * Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)))) *
      (star (Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) * star (I * Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)))) = 1 := by
    have h := star_exp_mul_self r.1 r.2
    simp only [star_mul', star_star]
    rw [show star I = -I from Complex.conj_I]
    linear_combination (-(I ^ 2) * (star (Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) *
      Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)) + 1)) * h - Complex.I_sq
  have hm : ∀ X : FockOp T, U * (Xᴴ * X) * Uᴴ = (U * X * Uᴴ)ᴴ * (U * X * Uᴴ) := by
    intro X
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc U * (Xᴴ * X) * Uᴴ = U * Xᴴ * (Uᴴ * U) * X * Uᴴ := by rw [hU1, mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  have hsum : U * hR T (-r.2, r.1) * Uᴴ = ((8 * π : ℝ) : ℂ) •
      ∑ ν : Triplet, (U * Bν T ν (-r.2, r.1) * Uᴴ)ᴴ * (U * Bν T ν (-r.2, r.1) * Uᴴ) := by
    rw [hR, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
    simp only [hm]
  rw [hsum]
  simp only [hB]
  have key : ∀ ν, ((star (Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) * star (I * Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))))
      • Bν (swapTorus T) ν r)ᴴ * ((star (Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ))) *
        star (I * Complex.exp (I * (r.1 : ℂ) * (r.2 : ℂ)))) • Bν (swapTorus T) ν r) =
      (Bν (swapTorus T) ν r)ᴴ * Bν (swapTorus T) ν r := fun ν => smul_conj_dev _ hs _
  calc _ = ((8 * π : ℝ) : ℂ) • ∑ ν : Triplet, (Bν (swapTorus T) ν r)ᴴ * Bν (swapTorus T) ν r :=
        congrArg (fun Z => ((8 * π : ℝ) : ℂ) • Z) (Finset.sum_congr rfl fun ν _ => key ν)
    _ = hR (swapTorus T) r := rfl

theorem conj_HN_dev (T : Torus) (U : FockOp T)
    (hpt : ∀ r : ℝ × ℝ, U * hR T (-r.2, r.1) * Uᴴ = hR (swapTorus T) r) :
    U * HN T * Uᴴ = HN (swapTorus T) := by
  let Φ : FockOp T →ₗ[ℂ] FockOp T :=
    { toFun := fun X => U * X * Uᴴ
      map_add' := fun X Y => by simp only [mul_add, add_mul]
      map_smul' := fun a X => by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply] }
  have hint : ∀ m m' : Conf (ZMod T.Nφ), IntegrableOn (fun R => hR T R m m') (fundDom T) := by
    intro m m'
    exact ((hR_contDiff T m m').continuous.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ico_subset_Icc_self Set.Ico_subset_Icc_self)
  have h1 : U * HN T * Uᴴ = opIntegral (fundDom T) (fun R => U * hR T R * Uᴴ) := by
    rw [(localForm_a T).2]
    exact opIntegral_map Φ (fundDom T) (hR T) hint
  rw [h1, (localForm_a (swapTorus T)).2]
  ext m m'
  simp only [opIntegral, Matrix.of_apply]
  have hF : ∀ u v : ℝ, (U * hR T (u + T.Lx, v) * Uᴴ) m m' = (U * hR T (u, v) * Uᴴ) m m' := by
    intro u v
    have h := hR_add_Lx T (u, v)
    rw [show ((u, v) + (T.Lx, 0) : ℝ × ℝ) = (u + T.Lx, v) by ext <;> simp] at h
    rw [h]
  have hcv := integral_rot_dev T (fun p => (U * hR T p * Uᴴ) m m') hF
  refine Eq.trans hcv.symm ?_
  congr 1
  funext r
  show (U * hR T (-r.2, r.1) * Uᴴ) m m' = hR (swapTorus T) r m m'
  rw [hpt r]

end FfRConjDevices

/-- **Lemma 8.3**: "`maps $N_\sigma$ to $N'_\sigma$, $\sigma\in\{\up,\dn\}$, and $H_N$ to $H'_N$.`" -/
theorem FfR_conj (T : Torus) :
    (∀ σ : Spin, FfR T * Nsig T σ * (FfR T)ᴴ = Nsig (swapTorus T) σ) ∧
      FfR T * HN T * (FfR T)ᴴ = HN (swapTorus T) := by
  obtain ⟨h1, h2, -, hcf⟩ := FfR_props T
  exact ⟨fun σ => conj_Nsig_dev T (FfR T) (rotMat T) h1 (rotMat_unitary T).2
      (fun j σ => conj_cjs_dev T (FfR T) (rotMat T) h2 (fun ν => secondQuant_mul_c (rot2_unitary_dev T) ν) j σ) σ,
    conj_HN_dev T (FfR T) fun r => conj_hR_dev T (FfR T) h1 hcf r⟩

/-- **Lemma 8.3**: "`In particular, for every sector label $\nn$, the restrictions of $H_N$ to $\sect\nn$ and of $H'_N$ to the sector of $\mathcal H'_N$ with the same label have the same eigenvalues, with multiplicities.`" -/
theorem secEig_swap (T : Torus) (nn : SectorLabel T) (k : ℕ) :
    secEig (swapTorus T) (HN (swapTorus T)) nn k = secEig T (HN T) nn k := by
  obtain ⟨h1, h2, -, -⟩ := FfR_props T
  obtain ⟨hN, hH⟩ := FfR_conj T
  have hUs : IsSectorPreserving T (FfR T) :=
    ⟨commute_of_conj_dev (U := FfR T) h1 (hN .up), commute_of_conj_dev (U := FfR T) h1 (hN .dn)⟩
  rw [← hH]
  exact secEig_conj_dev (U := FfR T) (HN_isSelfAdjoint T) (HN_isSectorPreserving T) h1 h2 hUs nn k

/-! ### Corollary 8.4 (uniformity over aspect ratios) -/

/-- The family `𝒯_N` is nonempty for `N ≥ L₀²/(4π)` (Corollary 8.4: "`For even $N\ge L_0^2/(4\pi)$`"). -/
theorem tauSet_nonempty {N : ℕ} (hN0 : 0 < N) (hN : L0std ^ 2 / (4 * π) ≤ N) : (tauSet N).Nonempty := by
  have hπ := Real.pi_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have ha : 0 < 4 * π * N := by positivity
  have hL0 : 0 < L0std := lt_of_lt_of_le (by norm_num) (le_max_left 4 _)
  let T : Torus :=
    { N := N
      Lx := Real.sqrt (4 * π * N)
      Ly := Real.sqrt (4 * π * N)
      Lx_pos := Real.sqrt_pos.2 ha
      Ly_pos := Real.sqrt_pos.2 ha
      area := by
        rw [Real.mul_self_sqrt ha.le]
        push_cast
        ring }
  refine ⟨T, rfl, ?_⟩
  show L0std ≤ min (Real.sqrt (4 * π * N)) (Real.sqrt (4 * π * N))
  rw [min_self]
  calc L0std = Real.sqrt (L0std ^ 2) := (Real.sqrt_sq hL0.le).symm
    _ ≤ Real.sqrt (4 * π * N) := by
      apply Real.sqrt_le_sqrt
      rw [div_le_iff₀ (by positivity)] at hN
      linarith

/-! ### Proof devices for `E11_bddAbove` (phase (b), round one; not statements of the paper)

Block C's `norm_hR_le` (`‖h_R‖ ≤ C_h = 7/π`) is stated for admissible tori, and a torus of `𝒯_N` need not be admissible
for any `δ₀` (both sides near `L₀`); its proof uses admissibility only through `4 ≤ min{L_x, L_y}` (block A's
`norm_ev_sq_bound`, `norm_evD_sq_bound`), which `𝒯_N` has (`L₀ = 3√π ≥ 4`). That proof under `4 ≤ min{L_x, L_y}`
is the device `norm_hR_le_of_four_le` of `Hamiltonian.SlotLocal`; with it, `‖H_N‖ ≤ C_h L_xL_y = 28N` and every
`E_k ≤ ‖H_N‖`. -/

section E11Devices

theorem norm_HN_le_dev (T : Torus) (hL : 4 ≤ min T.Lx T.Ly) : ‖toCLM T (HN T)‖ ≤ ChHC * (4 * π * T.N) := by
  have hhR : ∀ R : ℝ × ℝ, ‖toCLM T (hR T R)‖ ≤ ChHC := fun R =>
    (norm_hR_le_of_four_le T hL R).1.trans (norm_hR_le_of_four_le T hL R).2
  have hfd : volume.real (fundDom T) = 4 * π * T.N := by
    rw [measureReal_def, fundDom, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico,
      sub_zero, sub_zero, ENNReal.toReal_mul, ENNReal.toReal_ofReal T.Lx_pos.le, ENNReal.toReal_ofReal T.Ly_pos.le]
    have := T.area
    push_cast at this
    linarith
  rw [(HRTorus.Hamiltonian.localForm_a T).2, ← hfd, toCLM_eq_opCLM]
  exact norm_opIntegral_le_const _ (volume_fundDom_ne_top T).lt_top _
    (fun m m' => MeasureTheory.Measure.integrableOn_of_bounded (volume_fundDom_ne_top T)
      (hR_measurable T m m').aestronglyMeasurable (M := ChHC)
      (Filter.Eventually.of_forall fun R => (norm_entry_le _ m m').trans (hhR R)))
    fun R _ => hhR R

theorem secEig_le_norm_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (nn : SectorLabel T) (k : ℕ) : secEig T H nn k ≤ ‖toCLM T H‖ := by
  by_cases hd : Module.finrank ℂ (sector T nn) = 0
  · rw [secEig_of_finrank_eq_zero_dev hd]
    exact norm_nonneg _
  rw [secEig_congr_dev (b := min (max k 1) (Module.finrank ℂ (sector T nn))) (by omega)]
  obtain ⟨v, -, hv0, hHv⟩ := secEig_hasEigenvector hH hHs nn
    (k := min (max k 1) (Module.finrank ℂ (sector T nn))) (by omega) (min_le_right _ _)
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have h1 := (toCLM T H).le_opNorm v
  rw [hHv, norm_smul, Complex.norm_real, Real.norm_eq_abs] at h1
  have h2 := le_abs_self (secEig T H nn (min (max k 1) (Module.finrank ℂ (sector T nn))))
  have h3 : |secEig T H nn (min (max k 1) (Module.finrank ℂ (sector T nn)))| ≤ ‖toCLM T H‖ :=
    le_of_mul_le_mul_right h1 hv
  linarith

end E11Devices

/-- `E_{11}(N; 𝕋)` is bounded over `𝒯_N` (by `‖H_N‖ ≤ C_h|𝕋_N|`), so the supremum is the real supremum. -/
theorem E11_bddAbove (N : ℕ) : BddAbove (E11 '' tauSet N) := by
  refine ⟨ChHC * (4 * π * N), ?_⟩
  rintro _ ⟨T, ⟨hTN, hTL⟩, rfl⟩
  have hL : 4 ≤ min T.Lx T.Ly := le_trans (le_max_left 4 _) hTL
  have h1 := secEig_le_norm_dev (HN_isSelfAdjoint T) (HN_isSectorPreserving T) (halfSector T) 11
  have h2 := norm_HN_le_dev T hL
  rw [hTN] at h2
  exact h1.trans h2

/-! ### Proof device for Corollary 8.4 (phase (b), round three; not a statement of the paper)

The proof of `uniform_E11_eventually`, placed before `uniform_E11_tendsto`, which uses it (the paper: tori with
`L_x ≥ L_y` by Lemma 8.3, admissible with `L_x ≥ c_*√N`, `c_* = (4π)^{1/2}`, then Corollary 7.3 at `p = 10`). -/

/-- Corollary 8.4 without the supremum, from the equalities `E_1 = ⋯ = E_{10} = 0` only (no `0 < E_{11}`): it serves
`uniform_E11_tendsto`, `uniform_E11_eventually` and `ZeroModes.Lower`'s `uniform_E11_tendsto'`, `uniform_E11_eventually'`. -/
theorem uniform_eventually_dev
    (hzero : ∀ T : Torus, Even T.N → L0std ≤ min T.Lx T.Ly → ∀ k : ℕ, 1 ≤ k → k ≤ 10 → hcEig T (halfSector T) k = 0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop ⊓ 𝓟 {N : ℕ | Even N}, ∀ T ∈ tauSet N, E11 T < ε := by
  intro ε hε
  by_contra h
  rw [Filter.not_eventually, Filter.frequently_inf_principal, Nat.frequently_atTop_iff_infinite] at h
  obtain ⟨Nth, hNth⟩ : ∃ Nth : ℕ, ∀ N : ℕ, Nth ≤ N → 4 * δstd + 4 ≤ Real.sqrt (4 * π * N) := by
    refine ⟨⌈(4 * δstd + 4) ^ 2 / (4 * π)⌉₊, fun N hN => ?_⟩
    have hπ := Real.pi_pos
    have hδ : 0 ≤ δstd := (Real.sqrt_pos.2 Real.pi_pos).le
    have h1 : (4 * δstd + 4) ^ 2 / (4 * π) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [div_le_iff₀ (by positivity)] at h1
    calc 4 * δstd + 4 = Real.sqrt ((4 * δstd + 4) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (4 * π * N) := Real.sqrt_le_sqrt (by linarith)
  have hMi := inf_inter_ge_dev h Nth
  let M : Set ℕ := {N | N ∈ {N : ℕ | Even N} ∧ ¬ ∀ T ∈ tauSet N, E11 T < ε} ∩ {N | Nth ≤ N}
  have hLxT : ∀ T : Torus, T.Ly ≤ T.Lx → Real.sqrt (4 * π * T.N) ≤ T.Lx := by
    intro T hle
    have h4 : 4 * π * (T.N : ℝ) = T.Lx * T.Ly := by
      rw [T.area]
      push_cast
      ring
    rw [h4]
    calc Real.sqrt (T.Lx * T.Ly) ≤ Real.sqrt (T.Lx * T.Lx) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle T.Lx_pos.le)
      _ = T.Lx := Real.sqrt_mul_self T.Lx_pos.le
  have hch : ∀ N : ℕ, ∃ T : Torus, N ∈ M → T ∈ tauSet N ∧ T.Ly ≤ T.Lx ∧ ε ≤ E11 T := by
    intro N
    by_cases hN : N ∈ M
    · obtain ⟨⟨-, hnot⟩, -⟩ := hN
      push Not at hnot
      obtain ⟨T, hT, hTe⟩ := hnot
      by_cases hLL : T.Ly ≤ T.Lx
      · exact ⟨T, fun _ => ⟨hT, hLL, hTe⟩⟩
      · refine ⟨swapTorus T, fun _ => ⟨⟨hT.1, ?_⟩, ?_, ?_⟩⟩
        · show L0std ≤ min T.Ly T.Lx
          rw [min_comm]
          exact hT.2
        · show T.Lx ≤ T.Ly
          linarith [not_le.mp hLL]
        · have hsw : E11 (swapTorus T) = E11 T := secEig_swap T (halfSector T) 11
          rw [hsw]
          exact hTe
    · exact ⟨rectTorus 1 one_pos N, fun h' => absurd h' hN⟩
  choose Tf hTf using hch
  have hN' : ∀ N ∈ M, (Tf N).N = N := fun N hN => (hTf N hN).1.1
  have hLx' : ∀ N ∈ M, Real.sqrt (4 * π) * Real.sqrt N ≤ (Tf N).Lx := by
    intro N hN
    have h1 := hLxT (Tf N) (hTf N hN).2.1
    rw [hN' N hN] at h1
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 * π)]
    exact h1
  have hadm : ∀ N ∈ M, (Tf N).Admissible δstd := by
    intro N hN
    refine ⟨le_trans (hTf N hN).1.2 (min_le_right _ _), ?_⟩
    have h1 := hNth N hN.2
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 * π)] at h1
    exact h1.trans (hLx' N hN)
  let Ts : TorusSeq δstd :=
    { idx := M, idx_infinite := hMi, T := Tf, T_N := hN', admissible := hadm }
  have hc : 0 < Real.sqrt (4 * π) := Real.sqrt_pos.2 (by positivity)
  have hz : ∀ N ∈ M, ∀ k : ℕ, 1 ≤ k → k ≤ 10 → hcEig (Tf N) (halfSector (Tf N)) k = 0 := by
    intro N hN
    have heven : Even (Tf N).N := by
      rw [hN' N hN]
      exact hN.1.1
    exact hzero (Tf N) heven (hTf N hN).1.2
  have h4 : 4 ∣ 10 := four_dvd_hollowCore (p := 10) (Δ := 0) (γ := ε) Ts (Real.sqrt (4 * π)) hc hLx' (fun N hN => hN.1.1)
    ⟨le_rfl, by linarith, fun N hN => ?_, fun N hN => ?_⟩
  · omega
  · show hcEig (Tf N) (halfSector (Tf N)) 10 - hcEig (Tf N) (halfSector (Tf N)) 1 ≤ 0
    rw [hz N hN 10 (by norm_num) le_rfl, hz N hN 1 le_rfl (by norm_num), sub_self]
  · show ε ≤ hcEig (Tf N) (halfSector (Tf N)) (10 + 1) - hcEig (Tf N) (halfSector (Tf N)) 10
    rw [hz N hN 10 (by norm_num) le_rfl, sub_zero]
    exact (hTf N hN).2.2

/-- **Corollary 8.4**: "`Then $\sup_{\Tor\in\mathcal T_N}E_{11}(N;\Tor)\to0$ as $N\to\infty$ through the even integers.`" — under
the zero modes on every torus of the family. -/
theorem uniform_E11_tendsto
    (hzero : ∀ T : Torus, Even T.N → L0std ≤ min T.Lx T.Ly → HasTenZeroModes T) :
    Tendsto (fun N => sSup (E11 '' tauSet N)) (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Filter.Eventually.of_forall fun N => lt_of_lt_of_le ha ?_, fun a ha => ?_⟩
  · refine Real.sSup_nonneg fun x hx => ?_
    obtain ⟨T, -, rfl⟩ := hx
    exact secEig_HN_nonneg T (halfSector T) 11
  · filter_upwards [uniform_eventually_dev (fun T h1 h2 => (hzero T h1 h2).1) (a / 2) (by linarith)] with N hN
    have h : sSup (E11 '' tauSet N) ≤ a / 2 := by
      refine Real.sSup_le (fun x hx => ?_) (by linarith)
      obtain ⟨T, hT, rfl⟩ := hx
      exact (hN T hT).le
    linarith

/-- **Corollary 8.4** without the supremum (an equivalent form, `E_{11} ≥ 0`): for every `ε > 0`, for all large even
`N`, every torus of `𝒯_N` has `E_{11}(N; 𝕋) < ε`. -/
theorem uniform_E11_eventually
    (hzero : ∀ T : Torus, Even T.N → L0std ≤ min T.Lx T.Ly → HasTenZeroModes T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop ⊓ 𝓟 {N : ℕ | Even N}, ∀ T ∈ tauSet N, E11 T < ε := by
  exact uniform_eventually_dev fun T h1 h2 => (hzero T h1 h2).1

end HRTorus.Assembly

end -- noncomputable section
