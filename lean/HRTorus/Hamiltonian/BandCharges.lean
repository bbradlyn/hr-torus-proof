import HRTorus.Locality.Basic

/-!
# Band charges (T-0056 block C, `Hamiltonian.BandCharges`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **The definitions and statements were written first and
reviewed against the paper before any proof (review L9a, accepted with no change); the proof phase proved every
theorem of this module — there is no `sorry` here, and nothing here depends on an open statement — with the proof
devices in a section marked as such. The constants of Lemma 4.11(iii) are `C'_k = (1 + 6δ₀)^k · max(C_k, C)`, independent
of `m` and `η`, as the accepted quantifier order asks.**
The paper: the HR paper, `papers/hr/sections/04-hamiltonian.tex` — Definition 4.9 `def:charges`, Lemma 4.10
`lem:charges-elementary` (with the fact of its proof that Lemma 4.11 cites), Lemma 4.11 `lem:bandcharges`.

## The model

* A band `𝓑 ⊂ ℤ_{N_φ}` is a `Finset (ZMod N_φ)`; `Q_𝓑 := Σ_{j∈𝓑} n_{j↑}` is a finite sum of block A's `njs` (`Qband`);
  `𝓑 + 1` is the image of `𝓑` under `j ↦ j + 1`.
* The spectrum is Mathlib's `spectrum ℂ` of the matrix; `e^{X}` is `NormedSpace.exp` (as in block B's
  `iota_conj_exp`); norms are block A's `‖toCLM T ·‖` and block B's `‖opCLM ·‖`.
* `Col(j)` for a class `j ∈ ℤ_{N_φ}` is block B's `col` at the representative `j.val` (block B's `colBand` convention;
  `col_intCast_val`); `𝓑_X` is `bandX`.
* An interval `I ⊂ ℝ/L_xℤ` is block B's `circImage L_x J` and `I_ρ` is `Metric.cthickening ρ I`. Lemma 4.11(ii)'s last
  sentence is stated for the image of **any** set `J ⊆ ℝ` (the paper: an interval; the proof uses only that `x_s ∈ I`).
* Lemma 4.11(iii): `Z_N = Str(I_N)` with `I_N` the image of the open interval `(a_N, b_N)`, `b_N − a_N ≥ 2δ_x`;
  "`and let $A\in\AS_Z$ with prefactor exponent $m$`" is block B's `ASBound … m Ck` with the constants `Ck` of `A`;
  **"`constants depending only on $C$, on the constants of $A$ and on $\delta_0$`" is the quantifier order**: the new
  constants `C'` are chosen after `δ₀`, `C` and `Ck` and before the profile, the tori, the intervals, the sequence, the
  bands and `u` — which also makes them uniform in `u` and in the bands.
-/

open scoped InnerProductSpace Matrix Real
open Complex (I)

noncomputable section

namespace HRTorus.Hamiltonian

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Locality
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op IsEven CAR Alg)

/-! ## Definitions -/

/-- **Definition 4.9**: "`For a band $\mathcal B\subset\Z_{\Nphi}$ let $Q_{\mathcal B}:=\sum_{j\in\mathcal B}n_{j\up}$.`" -/
def Qband (T : Torus) (B : Finset (ZMod T.Nφ)) : FockOp T :=
  ∑ j ∈ B, njs T j .up

/-- **Lemma 4.11(i)**: "`with $v_j:=\Sa\psi_j\otimes\up$`" (block A's `analysis`, `orb`, `spinTensor`). -/
def vj (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (j : ZMod T.Nφ) : EuclideanSpace ℂ (Mode (Slot δ₀ T)) :=
  spinTensor (analysis η δ₀ T (orb T j)) .up

/-- **Lemma 4.11(ii)**: "`For $X\subset\Slots$ and a band $\mathcal B$ let $\mathcal B_X:=\{j\in\mathcal B:\Col(j)\cap X\ne\emptyset\}$.`" -/
def bandX (δ₀ : ℝ) (T : Torus) (B : Finset (ZMod T.Nφ)) (X : Finset (Slot δ₀ T)) : Finset (ZMod T.Nφ) :=
  B.filter fun j => (col δ₀ T (j.val : ℤ) ∩ X).Nonempty

/-! ## Proof devices for Lemmas 4.10–4.11 (phase (b); not statements of the paper) -/

section DevicesBC

theorem njs_commute_Nsig (T : Torus) (j : ZMod T.Nφ) (σ τ : Spin) : Commute (njs T j σ) (Nsig T τ) := by
  rw [njs_eq_diag, Nsig_eq_diag]; exact commute_diagonal_diagonal _ _

theorem norm_toCLM_le_one_of_isStarProjection (T : Torus) {A : FockOp T} (hA : IsStarProjection A) :
    ‖toCLM T A‖ ≤ 1 := by
  have h1 : ‖toCLM T (Aᴴ * A)‖ = ‖toCLM T A‖ * ‖toCLM T A‖ := by
    rw [show toCLM T (Aᴴ * A) = toCLM T Aᴴ * toCLM T A from
      map_mul (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) Aᴴ A,
      show toCLM T Aᴴ = star (toCLM T A) from map_star (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) A,
      ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.norm_adjoint_comp_self _
  have h2 : Aᴴ * A = A := by
    rw [← Matrix.star_eq_conjTranspose, hA.isSelfAdjoint.star_eq]; exact hA.isIdempotentElem.eq
  rw [h2] at h1
  nlinarith [norm_nonneg (toCLM T A)]

theorem Alg_mono {S : Type*} [Fintype S] [DecidableEq S] {X Y : Finset S} (h : X ⊆ Y) : Alg X ⊆ Alg Y := by
  rintro A ⟨hA1, hA2⟩
  refine ⟨?_, hA2⟩
  refine StarAlgebra.adjoin_mono ?_ hA1
  rintro B ⟨s, hs, σ, rfl⟩
  exact ⟨s, h hs, σ, rfl⟩

theorem Alg_mul_mem {S : Type*} [Fintype S] [DecidableEq S] {X : Finset S} {A B : Op S} (hA : A ∈ Alg X)
    (hB : B ∈ Alg X) : A * B ∈ Alg X :=
  ⟨mul_mem hA.1 hB.1, hA.2.mul_left hB.2⟩

theorem Alg_sum_mem {S : Type*} [Fintype S] [DecidableEq S] {X : Finset S} {ι : Type*} (s : Finset ι)
    (A : ι → Op S) (h : ∀ i ∈ s, A i ∈ Alg X) : ∑ i ∈ s, A i ∈ Alg X :=
  ⟨sum_mem fun i hi => (h i hi).1, Commute.sum_left _ _ _ fun i hi => (h i hi).2⟩

theorem Alg_smul_mem {S : Type*} [Fintype S] [DecidableEq S] {X : Finset S} (c : ℂ) {A : Op S}
    (hA : A ∈ Alg X) : c • A ∈ Alg X :=
  ⟨SMulMemClass.smul_mem c hA.1, hA.2.smul_left c⟩

theorem Alg_zero_mem {S : Type*} [Fintype S] [DecidableEq S] (X : Finset S) : (0 : Op S) ∈ Alg X :=
  ⟨zero_mem _, Commute.zero_left _⟩

theorem Alg_exp_mem {S : Type*} [Fintype S] [DecidableEq S] {X : Finset S} {A : Op S} (hA : A ∈ Alg X) :
    NormedSpace.exp A ∈ Alg X :=
  ⟨NormedSpace.exp_mem (R := ℂ) (Fermion.Pilot.JW.isClosed_CAR X) hA.1, hA.2.exp_left⟩

theorem exp_smul_conjTranspose {S : Type*} [Fintype S] [DecidableEq S] {H : Op S} (hH : IsSelfAdjoint H) (u : ℝ) :
    (NormedSpace.exp ((I * (u : ℂ)) • H))ᴴ = NormedSpace.exp ((-(I * (u : ℂ))) • H) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul]
  have hH' : Hᴴ = H := hH
  rw [hH']
  congr 2
  simp [Complex.conj_ofReal, Complex.conj_I]

theorem exp_smul_mem_unitary {S : Type*} [Fintype S] [DecidableEq S] {H : Op S} (hH : IsSelfAdjoint H) (u : ℝ) :
    NormedSpace.exp ((I * (u : ℂ)) • H) ∈ unitary (Op S) := by
  have h1 : NormedSpace.exp ((I * (u : ℂ)) • H) * NormedSpace.exp ((-(I * (u : ℂ))) • H) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl H).smul_left _ |>.smul_right _), ← add_smul,
      add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  have h2 : NormedSpace.exp ((-(I * (u : ℂ))) • H) * NormedSpace.exp ((I * (u : ℂ)) • H) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl H).smul_left _ |>.smul_right _), ← add_smul,
      neg_add_cancel, zero_smul, NormedSpace.exp_zero]
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, exp_smul_conjTranspose hH]
  exact ⟨h2, h1⟩

theorem rpow_neg_le_mul_rpow_neg {r r' c : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (h : 1 + r' ≤ (1 + r) * (1 + c))
    (k : ℕ) : (1 + r) ^ (-(k : ℝ)) ≤ (1 + c) ^ k * (1 + r') ^ (-(k : ℝ)) := by
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 + r' := by linarith
  rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le, Real.rpow_natCast, Real.rpow_natCast, inv_eq_one_div,
    inv_eq_one_div, mul_one_div, div_le_div_iff₀ (pow_pos h1 k) (pow_pos h2 k), one_mul]
  calc (1 + r') ^ k ≤ ((1 + r) * (1 + c)) ^ k := pow_le_pow_left₀ h2.le h k
    _ = (1 + c) ^ k * (1 + r) ^ k := by rw [mul_pow, mul_comm]

open scoped Matrix.Norms.L2Operator in
theorem norm_opCLM_unitary_conj {S : Type*} [Fintype S] [DecidableEq S] {U : Op S} (hU : U ∈ unitary (Op S))
    (X : Op S) : ‖opCLM (U * X * Uᴴ)‖ = ‖opCLM X‖ := by
  rw [norm_opCLM_eq_l2, norm_opCLM_eq_l2, ← Matrix.star_eq_conjTranspose,
    CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU), CStarRing.norm_mem_unitary_mul _ hU]

end DevicesBC

/-! ## Lemma 4.10 -/

/-- The proof of **Lemma 4.10**: "`So the $n_{j\sigma}$ are mutually commuting orthogonal projections`" — orthogonal
projections (cited by the proof of Lemma 4.11(i)). -/
theorem isStarProjection_njs (T : Torus) (j : ZMod T.Nφ) (σ : Spin) : IsStarProjection (njs T j σ) := by
  rw [njs_eq_diag]
  refine ⟨?_, ?_⟩
  · show Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext m
    by_cases h : m (j, σ) = true <;> simp [h]
  · rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext m
    by_cases h : m (j, σ) = true <;> simp [h]

/-- The same — mutually commuting. -/
theorem commute_njs (T : Torus) (j j' : ZMod T.Nφ) (σ σ' : Spin) : Commute (njs T j σ) (njs T j' σ') := by
  rw [njs_eq_diag, njs_eq_diag]; exact commute_diagonal_diagonal _ _

/-- **Lemma 4.10**: "`The operators $Q_{\mathcal B}$ commute with one another and with $\Nup$ and $\Ndn$`" — with one another. -/
theorem commute_Qband (T : Torus) (B B' : Finset (ZMod T.Nφ)) : Commute (Qband T B) (Qband T B') := by
  exact Commute.sum_left _ _ _ fun j _ => Commute.sum_right _ _ _ fun j' _ => commute_njs T j j' _ _

/-- **Lemma 4.10**: `Q_𝓑` commutes with `N_↑` and `N_↓` (block A's `IsSectorPreserving` is exactly that). -/
theorem Qband_isSectorPreserving (T : Torus) (B : Finset (ZMod T.Nφ)) : IsSectorPreserving T (Qband T B) := by
  exact ⟨Commute.sum_left _ _ _ fun j _ => njs_commute_Nsig T j _ _,
    Commute.sum_left _ _ _ fun j _ => njs_commute_Nsig T j _ _⟩

/-- The proof of **Lemma 4.10** (a sum of orthogonal projections): `Q_𝓑` is self-adjoint (§6 cites Lemma 4.10 for
"`band charges are self-adjoint and sector-preserving`"). -/
theorem Qband_isSelfAdjoint (T : Torus) (B : Finset (ZMod T.Nφ)) : IsSelfAdjoint (Qband T B) := by
  rw [IsSelfAdjoint, Qband, star_sum]
  exact Finset.sum_congr rfl fun j _ => (isStarProjection_njs T j .up).isSelfAdjoint.star_eq

/-- **Lemma 4.10**: "`each has spectrum in $\{0,1,\dots,\abs{\mathcal B}\}$, so that $\norm{Q_{\mathcal B}}\le\abs{\mathcal B}$ and $e^{2\pi\iu Q_{\mathcal B}}=\one$`"
— the spectrum. -/
theorem spectrum_Qband_subset (T : Torus) (B : Finset (ZMod T.Nφ)) :
    spectrum ℂ (Qband T B) ⊆ {z : ℂ | ∃ n : ℕ, n ≤ B.card ∧ z = (n : ℂ)} := by
  have hd : Qband T B = Matrix.diagonal fun m : Conf (ZMod T.Nφ) =>
      (((B.filter fun j => m (j, .up) = true).card : ℕ) : ℂ) := by
    rw [Qband]
    simp_rw [njs_eq_diag]
    ext m m'
    simp only [Matrix.sum_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      simp [Finset.sum_boole]
    · simp
  rw [hd, spectrum_diagonal]
  rintro z ⟨m, rfl⟩
  exact ⟨_, Finset.card_filter_le _ _, rfl⟩

/-- **Lemma 4.10**: `‖Q_𝓑‖ ≤ |𝓑|`. -/
theorem norm_Qband_le (T : Torus) (B : Finset (ZMod T.Nφ)) : ‖toCLM T (Qband T B)‖ ≤ B.card := by
  have e : toCLM T (Qband T B) = ∑ j ∈ B, toCLM T (njs T j .up) :=
    map_sum (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) _ B
  rw [e]
  calc ‖∑ j ∈ B, toCLM T (njs T j .up)‖ ≤ ∑ j ∈ B, ‖toCLM T (njs T j .up)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ B, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => norm_toCLM_le_one_of_isStarProjection T (isStarProjection_njs T j .up)
    _ = B.card := by simp

/-- **Lemma 4.10**: `e^{2πiQ_𝓑} = 1`. -/
theorem exp_Qband (T : Torus) (B : Finset (ZMod T.Nφ)) : NormedSpace.exp ((2 * π * I) • Qband T B) = 1 := by
  have hd : (2 * π * I) • Qband T B = Matrix.diagonal fun m : Conf (ZMod T.Nφ) =>
      (2 * π * I) * (((B.filter fun j => m (j, .up) = true).card : ℕ) : ℂ) := by
    rw [Qband]
    simp_rw [njs_eq_diag]
    ext m m'
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs with h
    · subst h
      simp [Finset.sum_boole]
    · simp
  rw [hd, Matrix.exp_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext m
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  rw [show (2 * (π : ℂ) * I) * (((B.filter fun j => m (j, .up) = true).card : ℕ) : ℂ) =
    (((B.filter fun j => m (j, .up) = true).card : ℕ) : ℂ) * (2 * π * I) by ring]
  exact Complex.exp_nat_mul_two_pi_mul_I _

/-- **Lemma 4.10**: "`$Q_{\Z_{\Nphi}}=\Nup$`". -/
theorem Qband_univ (T : Torus) : Qband T Finset.univ = Nsig T .up := by
  rfl

/-- **Lemma 4.10**: "`$Q_{\mathcal B}+Q_{\mathcal B'}=Q_{\mathcal B\cup\mathcal B'}$ for disjoint bands`". -/
theorem Qband_add (T : Torus) {B B' : Finset (ZMod T.Nφ)} (hBB' : Disjoint B B') :
    Qband T B + Qband T B' = Qband T (B ∪ B') := by
  rw [Qband, Qband, Qband, Finset.sum_union hBB']

/-- **Lemma 4.10**: "`$\Theta^*Q_{\mathcal B}\Theta=Q_{\mathcal B+1}$`". -/
theorem Θ_conj_Qband (T : Torus) (B : Finset (ZMod T.Nφ)) :
    (Θ T)ᴴ * Qband T B * Θ T = Qband T (B.image fun j => j + 1) := by
  rw [Qband, Finset.mul_sum, Finset.sum_mul]
  simp only [Θ_conj_njs]
  rw [Qband, Finset.sum_image (fun x _ y _ h => add_right_cancel h)]

/-! ## Lemma 4.11 -/

/-- **Lemma 4.11(i)**: "`Let the torus be admissible.`"
"`For every $j$, $\iota(n_{j\up})=\chat(v_j)^*\chat(v_j)$ with $v_j:=\Sa\psi_j\otimes\up$, which is supported in $\Col(j)\times\{\up\}$.`"
— the identity. -/
theorem iota_njs_up {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀)
    (j : ZMod T.Nφ) : iota η δ₀ T (njs T j .up) = (chatVec (vj η δ₀ T j))ᴴ * chatVec (vj η δ₀ T j) := by
  rw [njs, ← iotaHom_apply hη hδ₀ hT, map_mul, ← Matrix.star_eq_conjTranspose, map_star, iotaHom_apply, cjs,
    iota_cf hη hδ₀ hT, analysis2_spinTensor, vj, Matrix.star_eq_conjTranspose]

/-- **Lemma 4.11(i)**: `v_j` is supported in `Col(j) × {↑}`. -/
theorem vj_support (η : ℝ → ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (j : ZMod T.Nφ)
    (μ : Mode (Slot δ₀ T)) (hμ : vj η δ₀ T j μ ≠ 0) : μ.1 ∈ col δ₀ T (j.val : ℤ) ∧ μ.2 = .up := by
  rcases μ with ⟨s, τ⟩
  simp only [vj, spinTensor, WithLp.ofLp_toLp] at hμ
  by_cases hτ : τ = Spin.up
  · rw [if_pos hτ] at hμ
    refine ⟨?_, hτ⟩
    have hj : (((j.val : ℕ) : ℤ) : ZMod T.Nφ) = j := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    exact analysis_orb_mem_col hδ₀ hT (j.val : ℤ) s (by rwa [hj])
  · rw [if_neg hτ] at hμ; exact absurd rfl hμ

/-- **Lemma 4.11(i)**: "`The operators $\iota(n_{j\up})$ are mutually commuting orthogonal projections on $\FockS$, $\iota(n_{j\up})\in\Alg(\Col(j))$, and $\iota(Q_{\mathcal B})\in\Alg(\Col(\mathcal B))$ for every band $\mathcal B$.`"
— orthogonal projections. -/
theorem isStarProjection_iota_njs {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (j : ZMod T.Nφ) : IsStarProjection (iota η δ₀ T (njs T j .up)) := by
  have hp := isStarProjection_njs T j .up
  rw [← iotaHom_apply hη hδ₀ hT]
  exact ⟨by rw [IsIdempotentElem, ← map_mul, hp.isIdempotentElem.eq],
    by rw [IsSelfAdjoint, ← map_star, hp.isSelfAdjoint.star_eq]⟩

/-- **Lemma 4.11(i)**: the `ι(n_{j↑})` commute with one another. -/
theorem commute_iota_njs {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (j j' : ZMod T.Nφ) :
    Commute (iota η δ₀ T (njs T j .up)) (iota η δ₀ T (njs T j' .up)) := by
  rw [← iotaHom_apply hη hδ₀ hT, ← iotaHom_apply hη hδ₀ hT]
  exact (commute_njs T j j' _ _).map _

/-- **Lemma 4.11(i)**: `ι(n_{j↑}) ∈ Alg(Col(j))`. -/
theorem iota_njs_mem_Alg {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (j : ZMod T.Nφ) : iota η δ₀ T (njs T j .up) ∈ Alg (col δ₀ T (j.val : ℤ)) := by
  have hc : chatVec (vj η δ₀ T j) ∈ CAR (col δ₀ T (j.val : ℤ)) := by
    refine chatVec_mem_CAR _ _ fun μ hμ => ?_
    by_contra h
    exact hμ (vj_support η hδ₀ hT j μ h).1
  have h1 : iota η δ₀ T (njs T j .up) ∈ CAR (col δ₀ T (j.val : ℤ)) := by
    rw [iota_njs_up hη hδ₀ hT]
    exact mul_mem (Fermion.Pilot.JW.conjTranspose_mem_CAR hc) hc
  have hsp : IsSectorPreserving T (njs T j .up) := ⟨njs_commute_Nsig T j _ _, njs_commute_Nsig T j _ _⟩
  have h2 : IsEven (iota η δ₀ T (njs T j .up)) := iota_isEven hη hδ₀ hT (IsSectorPreserving.isEven T hsp)
  exact ⟨h1, h2⟩

/-- **Lemma 4.11(i)**: `ι(Q_𝓑) ∈ Alg(Col(𝓑))` for every band. -/
theorem iota_Qband_mem_Alg {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (B : Finset (ZMod T.Nφ)) : iota η δ₀ T (Qband T B) ∈ Alg (colBand δ₀ T B) := by
  have hsub : ∀ j ∈ B, col δ₀ T (j.val : ℤ) ⊆ colBand δ₀ T B := fun j hj => by
    unfold colBand
    exact Finset.subset_biUnion_of_mem (fun j : ZMod T.Nφ => col δ₀ T (j.val : ℤ)) hj
  have hsum : iota η δ₀ T (Qband T B) = ∑ j ∈ B, iota η δ₀ T (njs T j .up) := by
    rw [Qband, ← iotaHom_apply hη hδ₀ hT, map_sum]
    simp only [iotaHom_apply]
  rw [hsum]
  exact Alg_sum_mem _ _ fun j hj => Alg_mono (hsub j hj) (iota_njs_mem_Alg hη hδ₀ hT j)

/-- **Lemma 4.11(ii)**: "`For $A\in\Alg(X)$ and $u\in\R$,`"
"`e^{\iu u\iota(Q_{\mathcal B})}Ae^{-\iu u\iota(Q_{\mathcal B})}=e^{\iu u\iota(Q_{\mathcal B_X})}Ae^{-\iu u\iota(Q_{\mathcal B_X})} \in\Alg\bigl(X\cup\Col(\mathcal B_X)\bigr).`"
— the identity. -/
theorem exp_iota_Qband_conj_eq {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (B : Finset (ZMod T.Nφ)) (X : Finset (Slot δ₀ T)) {A : Op (Slot δ₀ T)} (hA : A ∈ Alg X)
    (u : ℝ) :
    NormedSpace.exp ((I * (u : ℂ)) • iota η δ₀ T (Qband T B)) * A *
        NormedSpace.exp ((-(I * (u : ℂ))) • iota η δ₀ T (Qband T B)) =
      NormedSpace.exp ((I * (u : ℂ)) • iota η δ₀ T (Qband T (bandX δ₀ T B X))) * A *
        NormedSpace.exp ((-(I * (u : ℂ))) • iota η δ₀ T (Qband T (bandX δ₀ T B X))) := by
  set BX := bandX δ₀ T B X with hBX
  have hsub : BX ⊆ B := Finset.filter_subset _ _
  have hsplit : Qband T B = Qband T BX + Qband T (B \ BX) := by
    rw [Qband_add T Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
  have hι : iota η δ₀ T (Qband T B) = iota η δ₀ T (Qband T BX) + iota η δ₀ T (Qband T (B \ BX)) := by
    rw [hsplit, iota_add hη hδ₀ hT]
  have hcomm : Commute (iota η δ₀ T (Qband T BX)) (iota η δ₀ T (Qband T (B \ BX))) := by
    rw [← iotaHom_apply hη hδ₀ hT, ← iotaHom_apply hη hδ₀ hT]
    exact (commute_Qband T _ _).map _
  set a := iota η δ₀ T (Qband T BX)
  set b := iota η δ₀ T (Qband T (B \ BX))
  have hb : NormedSpace.exp ((I * (u : ℂ)) • b) ∈ Alg (colBand δ₀ T (B \ BX)) :=
    Alg_exp_mem (Alg_smul_mem _ (iota_Qband_mem_Alg hη hδ₀ hT _))
  have hb' : NormedSpace.exp ((-(I * (u : ℂ))) • b) ∈ Alg (colBand δ₀ T (B \ BX)) :=
    Alg_exp_mem (Alg_smul_mem _ (iota_Qband_mem_Alg hη hδ₀ hT _))
  have hdisj : Disjoint (colBand δ₀ T (B \ BX)) X := by
    rw [colBand, Finset.disjoint_biUnion_left]
    intro j hj
    have hjn : j ∉ BX := (Finset.mem_sdiff.mp hj).2
    rw [hBX, bandX, Finset.mem_filter, not_and] at hjn
    have := hjn (Finset.mem_sdiff.mp hj).1
    rw [Finset.not_nonempty_iff_eq_empty] at this
    exact Finset.disjoint_iff_inter_eq_empty.mpr this
  have hcA : Commute (NormedSpace.exp ((I * (u : ℂ)) • b)) A :=
    commute_of_mem_Alg_of_mem_Alg hdisj hb hA
  have hab1 : NormedSpace.exp ((I * (u : ℂ)) • (a + b)) =
      NormedSpace.exp ((I * (u : ℂ)) • a) * NormedSpace.exp ((I * (u : ℂ)) • b) := by
    rw [smul_add, Matrix.exp_add_of_commute _ _ ((hcomm.smul_left _).smul_right _)]
  have hab2 : NormedSpace.exp ((-(I * (u : ℂ))) • (a + b)) =
      NormedSpace.exp ((-(I * (u : ℂ))) • b) * NormedSpace.exp ((-(I * (u : ℂ))) • a) := by
    rw [smul_add, add_comm, Matrix.exp_add_of_commute _ _ ((hcomm.symm.smul_left _).smul_right _)]
  have hbb : NormedSpace.exp ((I * (u : ℂ)) • b) * NormedSpace.exp ((-(I * (u : ℂ))) • b) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl b).smul_left _ |>.smul_right _), ← add_smul,
      add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  rw [hι, hab1, hab2]
  calc NormedSpace.exp ((I * (u : ℂ)) • a) * NormedSpace.exp ((I * (u : ℂ)) • b) * A *
        (NormedSpace.exp ((-(I * (u : ℂ))) • b) * NormedSpace.exp ((-(I * (u : ℂ))) • a))
      = NormedSpace.exp ((I * (u : ℂ)) • a) * A * (NormedSpace.exp ((I * (u : ℂ)) • b) *
          NormedSpace.exp ((-(I * (u : ℂ))) • b)) * NormedSpace.exp ((-(I * (u : ℂ))) • a) := by
        rw [Matrix.mul_assoc (NormedSpace.exp ((I * (u : ℂ)) • a)) (NormedSpace.exp ((I * (u : ℂ)) • b)) A,
          hcA.eq]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hbb, Matrix.mul_one]

/-- **Lemma 4.11(ii)**: the membership, `… ∈ Alg(X ∪ Col(𝓑_X))`. -/
theorem exp_iota_Qband_conj_mem_Alg {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (B : Finset (ZMod T.Nφ)) (X : Finset (Slot δ₀ T)) {A : Op (Slot δ₀ T)} (hA : A ∈ Alg X)
    (u : ℝ) :
    NormedSpace.exp ((I * (u : ℂ)) • iota η δ₀ T (Qband T (bandX δ₀ T B X))) * A *
        NormedSpace.exp ((-(I * (u : ℂ))) • iota η δ₀ T (Qband T (bandX δ₀ T B X))) ∈
      Alg (X ∪ colBand δ₀ T (bandX δ₀ T B X)) := by
  have hQ := iota_Qband_mem_Alg hη hδ₀ hT (bandX δ₀ T B X)
  have h1 := Alg_mono (Finset.subset_union_right (s₁ := X)) (Alg_exp_mem (Alg_smul_mem (I * (u : ℂ)) hQ))
  have h2 := Alg_mono (Finset.subset_union_right (s₁ := X)) (Alg_exp_mem (Alg_smul_mem (-(I * (u : ℂ))) hQ))
  have h3 := Alg_mono (Finset.subset_union_left (s₂ := colBand δ₀ T (bandX δ₀ T B X))) hA
  exact Alg_mul_mem (Alg_mul_mem h1 h3) h2

/-- **Lemma 4.11(ii)**: "`If $X=\Str(I)$ for an interval $I$, then $X\cup\Col(\mathcal B_X)\subset\Str(I_{2\delta_x})$.`" —
for the image `I` of any set `J ⊆ ℝ` (the module docstring). -/
theorem strip_union_colBand_subset {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (J : Set ℝ)
    (B : Finset (ZMod T.Nφ)) :
    strip δ₀ T (circImage T.Lx J) ∪ colBand δ₀ T (bandX δ₀ T B (strip δ₀ T (circImage T.Lx J))) ⊆
      strip δ₀ T (Metric.cthickening (2 * δx δ₀ T) (circImage T.Lx J)) := by
  intro s hs
  rw [mem_strip]
  rcases Finset.mem_union.mp hs with hs | hs
  · exact Metric.self_subset_cthickening _ (mem_strip.mp hs)
  · obtain ⟨j, hj, hsj⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨_, s', hs'⟩ := Finset.mem_filter.mp hj
    obtain ⟨hs'c, hs'X⟩ := Finset.mem_inter.mp hs'
    have h1 := mem_col.mp hsj
    have h2 := mem_col.mp hs'c
    have h3 : pdist T.Lx (xs δ₀ T s - xs δ₀ T s') < 2 * δx δ₀ T := by
      have e : xs δ₀ T s - xs δ₀ T s' = (xs δ₀ T s - T.κ * (j.val : ℤ)) + -(xs δ₀ T s' - T.κ * (j.val : ℤ)) := by
        ring
      rw [e]
      calc pdist T.Lx _ ≤ pdist T.Lx (xs δ₀ T s - T.κ * (j.val : ℤ)) +
            pdist T.Lx (-(xs δ₀ T s' - T.κ * (j.val : ℤ))) := pdist_add_le _ _ _
        _ < δx δ₀ T + δx δ₀ T := by rw [pdist_neg]; exact add_lt_add h1 h2
        _ = 2 * δx δ₀ T := by ring
    obtain ⟨m, hm⟩ := (pdist_lt_iff _ _ _).mp h3
    obtain ⟨m', hm'⟩ := mem_circImage.mp (mem_strip.mp hs'X)
    refine Metric.mem_cthickening_of_dist_le (xs δ₀ T s) (xs δ₀ T s' - m * T.Lx) _ _ ?_ ?_
    · refine mem_circImage.mpr ⟨m + m', ?_⟩
      convert hm' using 1
      push_cast; ring
    · rw [Real.dist_eq]
      have : xs δ₀ T s - (xs δ₀ T s' - m * T.Lx) = xs δ₀ T s - xs δ₀ T s' + m * T.Lx := by ring
      rw [this]; exact hm.le

/-- **Lemma 4.11(iii)**: "`Let $(\Tor_N)_{N\in\mathcal N}$ be admissible, let $Z_N=\Str(I_N)$ with $I_N$ open intervals of length at least $2\delta_x$, and let $A\in\AS_Z$ with prefactor exponent $m$ and $\norm{A_N}\le CN^m$. Then for all bands $\mathcal B_N$ and $u\in\R$, $e^{\iu uQ_{\mathcal B_N}}A_Ne^{-\iu uQ_{\mathcal B_N}}$ is almost supported in $Z$ with prefactor exponent $m$ and constants depending only on $C$, on the constants of $A$ and on $\delta_0$, uniformly in $u$ and in the bands.`"
— the constants `C'` chosen after `δ₀`, `C` and the constants `Ck` of `A` only (the module docstring). -/
theorem exists_almostSupported_exp_Qband_conj {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (C : ℝ) (Ck : ℕ → ℝ) :
    ∃ C' : ℕ → ℝ, ∀ (η : ℝ → ℝ), IsProfile η → ∀ (Ts : TorusSeq δ₀) (a b : ℕ → ℝ),
      (∀ N ∈ Ts.idx, 2 * δx δ₀ (Ts.T N) ≤ b N - a N) →
      ∀ (A : (N : ℕ) → FockOp (Ts.T N)) (m : ℝ),
        ASBound η δ₀ Ts (fun N => strip δ₀ (Ts.T N) (circImage (Ts.T N).Lx (Set.Ioo (a N) (b N)))) A m Ck →
        (∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (A N)‖ ≤ C * (N : ℝ) ^ m) →
        ∀ (B : (N : ℕ) → Finset (ZMod (Ts.T N).Nφ)) (u : ℝ),
          ASBound η δ₀ Ts (fun N => strip δ₀ (Ts.T N) (circImage (Ts.T N).Lx (Set.Ioo (a N) (b N))))
            (fun N => NormedSpace.exp ((I * (u : ℂ)) • Qband (Ts.T N) (B N)) * A N *
              NormedSpace.exp ((-(I * (u : ℂ))) • Qband (Ts.T N) (B N))) m C' := by
  refine ⟨fun k => (1 + 6 * δ₀) ^ k * max (Ck k) C, ?_⟩
  intro η hη Ts a b hab A m hAS hAn B u
  refine ⟨hAS.1, ?_⟩
  intro k N hN r' hr'
  have hT : (Ts.T N).Admissible δ₀ := Ts.admissible N hN
  have hδxpos : 0 < δx δ₀ (Ts.T N) := δx_pos hδ₀ hT
  have hδx : δx δ₀ (Ts.T N) ≤ 2 * δ₀ := (consistency_ii hδ₀ hT).2.2.1
  have hNpos : (0 : ℝ) < N := by
    have := (Ts.T N).N_pos
    rw [Ts.T_N N hN] at this
    exact_mod_cast this
  have hNm : 0 < (N : ℝ) ^ m := Real.rpow_pos_of_pos hNpos m
  have hE1 : (1 : ℝ) ≤ (1 + 6 * δ₀) ^ k := one_le_pow₀ (by linarith)
  have hQsa : IsSelfAdjoint (Qband (Ts.T N) (B N)) := Qband_isSelfAdjoint _ _
  have hconj := iota_conj_exp hη hδ₀ hT hQsa (A N) u
  have hιQsa : IsSelfAdjoint (iota η δ₀ (Ts.T N) (Qband (Ts.T N) (B N))) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ← iota_conjTranspose hη hδ₀ hT,
      ← Matrix.star_eq_conjTranspose, hQsa.star_eq]
  have hU := exp_smul_mem_unitary hιQsa u
  have hUH := exp_smul_conjTranspose hιQsa u
  have hC0 : 0 ≤ C := by
    have h0 : 0 ≤ C * (N : ℝ) ^ m := le_trans (norm_nonneg _) (hAn N hN)
    by_contra h
    push_neg at h
    have := mul_neg_of_neg_of_pos h hNm
    linarith
  have hY : 0 < (1 + r') ^ (-(k : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  by_cases hr : 3 * δx δ₀ (Ts.T N) ≤ r'
  · have hr0 : 0 ≤ r' - 3 * δx δ₀ (Ts.T N) := by linarith
    obtain ⟨A', hA'mem, hA'bd⟩ := hAS.2 k N hN (r' - 3 * δx δ₀ (Ts.T N)) hr0
    have hfat : fat (strip δ₀ (Ts.T N) (circImage (Ts.T N).Lx (Set.Ioo (a N) (b N)))) (r' - 3 * δx δ₀ (Ts.T N)) ⊆
        strip δ₀ (Ts.T N) (Metric.cthickening (r' - 3 * δx δ₀ (Ts.T N))
          (circImage (Ts.T N).Lx (Set.Ioo (a N) (b N)))) :=
      fat_strip_subset hδ₀ hT (hab N hN) hr0
    have hA'X := Alg_mono hfat hA'mem
    refine ⟨NormedSpace.exp ((I * (u : ℂ)) • iota η δ₀ (Ts.T N) (Qband (Ts.T N) (B N))) * A' *
      NormedSpace.exp ((-(I * (u : ℂ))) • iota η δ₀ (Ts.T N) (Qband (Ts.T N) (B N))), ?_, ?_⟩
    · rw [exp_iota_Qband_conj_eq hη hδ₀ hT (B N) _ hA'X u]
      refine Alg_mono ?_ (exp_iota_Qband_conj_mem_Alg hη hδ₀ hT (B N) _ hA'X u)
      have hab' : a N < b N := by linarith [hab N hN]
      have h1 := cthickening_circImage_Ioo (Ts.T N).Lx_pos hab' hr0
      have h2 := strip_union_colBand_subset hδ₀ hT
        (Set.Icc (a N - (r' - 3 * δx δ₀ (Ts.T N))) (b N + (r' - 3 * δx δ₀ (Ts.T N)))) (B N)
      rw [← h1] at h2
      refine h2.trans ?_
      refine (strip_mono (Metric.cthickening_cthickening_subset (by linarith) hr0 _)).trans ?_
      have h3 := strip_cthickening_subset hδ₀ hT (hab N hN)
        (ρ := 2 * δx δ₀ (Ts.T N) + (r' - 3 * δx δ₀ (Ts.T N))) (by linarith)
      refine h3.trans ?_
      exact fat_mono_right _ (by linarith)
    · rw [hconj, ← hUH, show ∀ X Y : Op (Slot δ₀ (Ts.T N)),
        NormedSpace.exp ((I * (u : ℂ)) • iota η δ₀ (Ts.T N) (Qband (Ts.T N) (B N))) * X *
          (NormedSpace.exp ((I * (u : ℂ)) • iota η δ₀ (Ts.T N) (Qband (Ts.T N) (B N))))ᴴ -
        NormedSpace.exp ((I * (u : ℂ)) • iota η δ₀ (Ts.T N) (Qband (Ts.T N) (B N))) * Y *
          (NormedSpace.exp ((I * (u : ℂ)) • iota η δ₀ (Ts.T N) (Qband (Ts.T N) (B N))))ᴴ =
        NormedSpace.exp ((I * (u : ℂ)) • iota η δ₀ (Ts.T N) (Qband (Ts.T N) (B N))) * (X - Y) *
          (NormedSpace.exp ((I * (u : ℂ)) • iota η δ₀ (Ts.T N) (Qband (Ts.T N) (B N))))ᴴ from
        fun X Y => by rw [Matrix.mul_sub, Matrix.sub_mul], norm_opCLM_unitary_conj hU]
      have hX : 0 < (1 + (r' - 3 * δx δ₀ (Ts.T N))) ^ (-(k : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
      have hCk : 0 ≤ Ck k := by
        have h0 : 0 ≤ Ck k * (N : ℝ) ^ m * (1 + (r' - 3 * δx δ₀ (Ts.T N))) ^ (-(k : ℝ)) :=
          le_trans (norm_nonneg _) hA'bd
        by_contra h
        push_neg at h
        have := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h hNm) hX
        linarith
      have hgeom := rpow_neg_le_mul_rpow_neg (c := 6 * δ₀) hr0 hr'
        (by nlinarith [hδx, hδ₀.le]) k
      calc _ ≤ Ck k * (N : ℝ) ^ m * (1 + (r' - 3 * δx δ₀ (Ts.T N))) ^ (-(k : ℝ)) := hA'bd
        _ ≤ Ck k * (N : ℝ) ^ m * ((1 + 6 * δ₀) ^ k * (1 + r') ^ (-(k : ℝ))) := by gcongr
        _ ≤ max (Ck k) C * (N : ℝ) ^ m * ((1 + 6 * δ₀) ^ k * (1 + r') ^ (-(k : ℝ))) := by
          gcongr
          exact le_max_left _ _
        _ = (1 + 6 * δ₀) ^ k * max (Ck k) C * (N : ℝ) ^ m * (1 + r') ^ (-(k : ℝ)) := by ring
  · push_neg at hr
    refine ⟨0, Alg_zero_mem _, ?_⟩
    have hQU := exp_smul_mem_unitary hQsa u
    have hQH := exp_smul_conjTranspose hQsa u
    rw [sub_zero, norm_iota hη hδ₀ hT]
    beta_reduce
    rw [← hQH, toCLM_eq_opCLM, norm_opCLM_unitary_conj hQU, ← toCLM_eq_opCLM]
    beta_reduce
    have hEY : 1 ≤ (1 + 6 * δ₀) ^ k * (1 + r') ^ (-(k : ℝ)) := by
      have := rpow_neg_le_mul_rpow_neg (r := 0) (r' := r') (c := 6 * δ₀) le_rfl hr'
        (by nlinarith [hδx, hδ₀.le]) k
      simpa using this
    calc ‖toCLM (Ts.T N) (A N)‖ ≤ C * (N : ℝ) ^ m := hAn N hN
      _ ≤ max (Ck k) C * (N : ℝ) ^ m * 1 := by
          rw [mul_one]; gcongr; exact le_max_right _ _
      _ ≤ max (Ck k) C * (N : ℝ) ^ m * ((1 + 6 * δ₀) ^ k * (1 + r') ^ (-(k : ℝ))) := by
          have : 0 ≤ max (Ck k) C * (N : ℝ) ^ m := mul_nonneg (le_trans hC0 (le_max_right _ _)) hNm.le
          exact mul_le_mul_of_nonneg_left hEY this
      _ = (1 + 6 * δ₀) ^ k * max (Ck k) C * (N : ℝ) ^ m * (1 + r') ^ (-(k : ℝ)) := by ring

/-- **Lemma 4.11(iii)** in block B's vocabulary (a corollary of `exists_almostSupported_exp_Qband_conj`): for `A ∈ 𝒜𝒮_Z`
with a witness `w` and `‖A_N‖ ≤ C N^{w.m}`, the conjugates, as a family indexed by `(u, (𝓑_N)_N)`, are almost
supported in `Z` "`uniformly in $u$ and in the bands`" (`AlmostSupportedUniformly`). -/
theorem almostSupportedUniformly_exp_Qband_conj {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (Ts : TorusSeq δ₀) (a b : ℕ → ℝ) (hab : ∀ N ∈ Ts.idx, 2 * δx δ₀ (Ts.T N) ≤ b N - a N)
    {A : (N : ℕ) → FockOp (Ts.T N)}
    (w : ASWitness η δ₀ Ts (fun N => strip δ₀ (Ts.T N) (circImage (Ts.T N).Lx (Set.Ioo (a N) (b N)))) A)
    (C : ℝ) (hA : ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (A N)‖ ≤ C * (N : ℝ) ^ w.m) :
    AlmostSupportedUniformly η δ₀ Ts (P := ℝ × ((N : ℕ) → Finset (ZMod (Ts.T N).Nφ)))
      (fun _ N => strip δ₀ (Ts.T N) (circImage (Ts.T N).Lx (Set.Ioo (a N) (b N))))
      (fun p N => NormedSpace.exp ((I * (p.1 : ℂ)) • Qband (Ts.T N) (p.2 N)) * A N *
        NormedSpace.exp ((-(I * (p.1 : ℂ))) • Qband (Ts.T N) (p.2 N))) := by
  obtain ⟨C', hC'⟩ := exists_almostSupported_exp_Qband_conj hδ₀ C w.C
  exact ⟨w.m, C', fun p => hC' η hη Ts a b hab A w.m w.bound hA p.2 p.1⟩

end HRTorus.Hamiltonian
