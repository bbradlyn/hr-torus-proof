import HRTorus.IndexCore.KP

/-!
# Proposition 6.10(i)–(ii), in-sector clustering

Written by Claude Opus 5.5 (an AI model), 2026-10-23. The HR paper's Proposition 6.10, its algebraic parts: for a sector-preserving
`A`, `𝒬(A) P = 0` and `P 𝒬(A) = P A (1 - P)` (part (i)); hence `P A (1 - P) B P = P [𝒬(A), B] P`
and `‖P A (1 - P) B P‖ ≤ ‖[𝒬(A), B]‖` (part (ii), operator form). Then the *compression form* of
the clustering hypotheses of `index_core`: the four commutator
hypotheses bound Lemma 6.14's `ε₁ = ‖P V₊ (1 - P) V₋ P‖` and `ε₂ = ‖P V₊* (1 - P) V₋* P‖` for
`V_± = 𝓜_±(φ)` and `V_± = e^{2πi Q̄_±}`, which needs those unitaries to be sector-preserving.

Part (ii)'s two statements about a unit vector `Ω ∈ ran P` are included (`norm_clustering_vec`,
`norm_clustering_inner`); the finite argument itself uses only the operator form (Lemma 6.14 is
stated with `ε₁`, `ε₂`).
-/

open scoped InnerProductSpace ComplexConjugate Real
open Complex (I)

noncomputable section
open Classical

namespace HRTorus.IndexCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

namespace Setting

variable (S : Setting E)

/-- The blocks of the clustering filter: `P_μ 𝒬(A) P_ν = g(μ - ν) P_μ A P_ν`. -/
theorem block_Qf (A : E →L[ℂ] E) (μ ν : ℝ) :
    eigProj S.H S.H_sa μ * S.Qf A * eigProj S.H S.H_sa ν =
      S.g (μ - ν) • (eigProj S.H S.H_sa μ * A * eigProj S.H S.H_sa ν) :=
  eigProj_mul_spectralSum_mul_eigProj S.H S.H_sa _ A μ ν

/-- `𝒬(A)` is sector-preserving when `A` is (Lemma 2.6(ii)). -/
theorem commute_Psec_Qf {A : E →L[ℂ] E} (hA : Commute S.Psec A) : Commute S.Psec (S.Qf A) :=
  commute_spectralSum S.H S.H_sa S.Psec_H hA _

/-- **Proposition 6.10(i)**, first half: `𝒬(A) P = 0` for sector-preserving `A`. -/
theorem Qf_mul_P {A : E →L[ℂ] E} (hA : Commute S.Psec A) : S.Qf A * S.P = 0 := by
  have hγ := S.γ_pos
  apply ext_blocks S.H S.H_sa
  intro μ _ ν _
  rw [mul_zero, zero_mul]
  have e : eigProj S.H S.H_sa μ * (S.Qf A * S.P) * eigProj S.H S.H_sa ν =
      eigProj S.H S.H_sa μ * S.Qf A * (S.P * eigProj S.H S.H_sa ν) := by
    simp only [mul_assoc]
  rw [e]
  by_cases hν : ν ∈ Set.Icc S.a S.b
  · rw [S.P_mul_eigProj_of_mem hν, ← mul_assoc, S.block_Qf, smul_mul_assoc]
    by_cases h0 : eigProj S.H S.H_sa μ * A * eigProj S.H S.H_sa ν * S.Psec = 0
    · rw [h0, smul_zero]
    · have hμ : S.a ≤ μ := by
        rcases S.gap_left_of_block_ne_zero hA h0 with h | h
        · exact h.1
        · linarith [hν.1, hν.2]
      rw [S.g_zero _ (by linarith [hν.2, S.width]), zero_smul]
  · rw [S.P_mul_eigProj_of_not_mem hν, mul_zero]

/-- **Proposition 6.10(i)**, second half: `P 𝒬(A) = P A (1 - P)` for sector-preserving `A`. -/
theorem P_mul_Qf {A : E →L[ℂ] E} (hA : Commute S.Psec A) :
    S.P * S.Qf A = S.P * A * (1 - S.P) := by
  have hγ := S.γ_pos
  apply ext_blocks S.H S.H_sa
  intro μ _ ν _
  have eL : eigProj S.H S.H_sa μ * (S.P * S.Qf A) * eigProj S.H S.H_sa ν =
      eigProj S.H S.H_sa μ * S.P * S.Qf A * eigProj S.H S.H_sa ν := by
    simp only [mul_assoc]
  have eR : eigProj S.H S.H_sa μ * (S.P * A * (1 - S.P)) * eigProj S.H S.H_sa ν =
      eigProj S.H S.H_sa μ * S.P * A *
        (eigProj S.H S.H_sa ν - S.P * eigProj S.H S.H_sa ν) := by
    simp only [mul_sub, sub_mul, mul_one, mul_assoc]
  rw [eL, eR]
  by_cases hμ : μ ∈ Set.Icc S.a S.b
  · rw [S.eigProj_mul_P_of_mem hμ]
    have hL : eigProj S.H S.H_sa μ * S.Psec * S.Qf A * eigProj S.H S.H_sa ν =
        S.g (μ - ν) • (eigProj S.H S.H_sa μ * A * eigProj S.H S.H_sa ν * S.Psec) := by
      rw [← S.block_Psec_swap (S.commute_Psec_Qf hA), S.block_Qf, smul_mul_assoc]
    rw [hL]
    by_cases hν : ν ∈ Set.Icc S.a S.b
    · rw [S.P_mul_eigProj_of_mem hν]
      have h1 : eigProj S.H S.H_sa μ * S.Psec * A * (eigProj S.H S.H_sa ν * S.Psec) =
          eigProj S.H S.H_sa μ * S.Psec * A * eigProj S.H S.H_sa ν := by
        rw [← mul_assoc, ← S.block_Psec_swap hA, mul_assoc _ S.Psec S.Psec, S.Psec_mul_self,
          S.block_Psec_swap hA]
      rw [mul_sub, h1, sub_self, S.g_zero _ (by linarith [hμ.1, hν.2, S.width]), zero_smul]
    · rw [S.P_mul_eigProj_of_not_mem hν, sub_zero, ← S.block_Psec_swap hA]
      by_cases h0 : eigProj S.H S.H_sa μ * A * eigProj S.H S.H_sa ν * S.Psec = 0
      · rw [h0, smul_zero]
      · have hν' : S.b + S.γ ≤ ν := (S.gap_right_of_block_ne_zero h0).resolve_right hν
        rw [S.g_one _ (by linarith [hμ.2]), one_smul]
  · rw [S.eigProj_mul_P_of_not_mem hμ]
    simp

/-- **Proposition 6.10(ii)**, operator form: `P A (1 - P) B P = P [𝒬(A), B] P` for
sector-preserving `A` and any `B`. -/
theorem compression_eq {A : E →L[ℂ] E} (hA : Commute S.Psec A) (B : E →L[ℂ] E) :
    S.P * A * (1 - S.P) * B * S.P = S.P * ⁅S.Qf A, B⁆ * S.P := by
  have h2 : S.P * (B * S.Qf A) * S.P = 0 := by
    rw [mul_assoc, mul_assoc, S.Qf_mul_P hA, mul_zero, mul_zero]
  have h3 : S.P * ⁅S.Qf A, B⁆ * S.P =
      S.P * S.Qf A * B * S.P - S.P * (B * S.Qf A) * S.P := by
    rw [Ring.lie_def, mul_sub, sub_mul, ← mul_assoc S.P (S.Qf A) B]
  rw [h3, h2, sub_zero, S.P_mul_Qf hA]

/-- **Proposition 6.10(ii)**, the bound: `‖P A (1 - P) B P‖ ≤ ‖[𝒬(A), B]‖`. -/
theorem norm_compression_le {A : E →L[ℂ] E} (hA : Commute S.Psec A) (B : E →L[ℂ] E) :
    ‖S.P * A * (1 - S.P) * B * S.P‖ ≤ ‖⁅S.Qf A, B⁆‖ := by
  rw [S.compression_eq hA B]
  have hP : ‖S.P‖ ≤ 1 := IsStarProjection.norm_le _ S.isStarProjection_P
  calc ‖S.P * ⁅S.Qf A, B⁆ * S.P‖ ≤ ‖S.P * ⁅S.Qf A, B⁆‖ * ‖S.P‖ := norm_mul_le _ _
    _ ≤ (‖S.P‖ * ‖⁅S.Qf A, B⁆‖) * ‖S.P‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ (1 * ‖⁅S.Qf A, B⁆‖) * 1 := by gcongr
    _ = ‖⁅S.Qf A, B⁆‖ := by ring

/-- **Proposition 6.10(ii)**, the first vector form: for a unit vector `Ω ∈ ran P`,
`‖P A B Ω - P A P B Ω‖ ≤ ‖[𝒬(A), B]‖`. -/
theorem norm_clustering_vec {A : E →L[ℂ] E} (hA : Commute S.Psec A) (B : E →L[ℂ] E) {Ω : E}
    (hΩ : S.P Ω = Ω) (h1 : ‖Ω‖ = 1) :
    ‖S.P (A (B Ω)) - S.P (A (S.P (B Ω)))‖ ≤ ‖⁅S.Qf A, B⁆‖ := by
  have e : S.P (A (B Ω)) - S.P (A (S.P (B Ω))) = (S.P * A * (1 - S.P) * B * S.P) Ω := by
    show _ = S.P (A ((1 - S.P) (B (S.P Ω))))
    rw [hΩ]
    simp [map_sub]
  rw [e]
  calc ‖(S.P * A * (1 - S.P) * B * S.P) Ω‖ ≤ ‖S.P * A * (1 - S.P) * B * S.P‖ * ‖Ω‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖S.P * A * (1 - S.P) * B * S.P‖ := by rw [h1, mul_one]
    _ ≤ ‖⁅S.Qf A, B⁆‖ := S.norm_compression_le hA B

/-- **Proposition 6.10(ii)**, the second vector form: for a unit vector `Ω ∈ ran P`,
`|⟨Ω, A B Ω⟩ - ⟨Ω, A P B Ω⟩| ≤ ‖[𝒬(A), B]‖`. -/
theorem norm_clustering_inner {A : E →L[ℂ] E} (hA : Commute S.Psec A) (B : E →L[ℂ] E) {Ω : E}
    (hΩ : S.P Ω = Ω) (h1 : ‖Ω‖ = 1) :
    ‖⟪Ω, A (B Ω)⟫_ℂ - ⟪Ω, A (S.P (B Ω))⟫_ℂ‖ ≤ ‖⁅S.Qf A, B⁆‖ := by
  have hsym : ∀ x y : E, ⟪S.P x, y⟫_ℂ = ⟪x, S.P y⟫_ℂ := fun x y =>
    S.isStarProjection_P.isSelfAdjoint.isSymmetric x y
  have e : ⟪Ω, A (B Ω)⟫_ℂ - ⟪Ω, A (S.P (B Ω))⟫_ℂ =
      ⟪Ω, (S.P * A * (1 - S.P) * B * S.P) Ω⟫_ℂ := by
    rw [← inner_sub_right]
    show _ = ⟪Ω, S.P (A ((1 - S.P) (B (S.P Ω))))⟫_ℂ
    rw [← hsym Ω, hΩ]
    simp [map_sub]
  rw [e]
  calc ‖⟪Ω, (S.P * A * (1 - S.P) * B * S.P) Ω⟫_ℂ‖
        ≤ ‖Ω‖ * ‖(S.P * A * (1 - S.P) * B * S.P) Ω‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖ * (‖S.P * A * (1 - S.P) * B * S.P‖ * ‖Ω‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖S.P * A * (1 - S.P) * B * S.P‖ := by rw [h1]; ring
    _ ≤ ‖⁅S.Qf A, B⁆‖ := S.norm_compression_le hA B

/-! ## The localized unitaries are sector-preserving -/

theorem commute_Psec_star {X : E →L[ℂ] E} (hX : Commute S.Psec X) : Commute S.Psec (star X) := by
  have h := hX.star_star
  rwa [S.star_Psec] at h

theorem commute_Psec_KUminus : Commute S.Psec S.KUminus :=
  ((S.commute_Psec_star S.Psec_U).mul_right S.commute_Psec_Kminus).mul_right S.Psec_U

theorem commute_Psec_KUplus : Commute S.Psec S.KUplus :=
  ((S.commute_Psec_star S.Psec_U).mul_right S.commute_Psec_Kplus).mul_right S.Psec_U

theorem commute_Psec_QbarMinus : Commute S.Psec S.QbarMinus :=
  S.Psec_Qminus.sub_right S.commute_Psec_Kminus

theorem commute_Psec_QbarPlus : Commute S.Psec S.QbarPlus :=
  S.Psec_Qplus.sub_right S.commute_Psec_Kplus

theorem commute_Psec_QbarUMinus : Commute S.Psec S.QbarUMinus :=
  (S.Psec_Qminus.add_right S.Psec_Tminus).sub_right S.commute_Psec_KUminus

theorem commute_Psec_QbarUPlus : Commute S.Psec S.QbarUPlus :=
  (S.Psec_Qplus.add_right S.Psec_Tplus).sub_right S.commute_Psec_KUplus

theorem commute_Psec_exp_smul {X : E →L[ℂ] E} (hX : Commute S.Psec X) (c : ℂ) :
    Commute S.Psec (NormedSpace.exp (c • X)) :=
  (hX.smul_right c).exp_right

theorem commute_Psec_Mminus (φ : ℝ) : Commute S.Psec (S.Mminus φ) :=
  (S.commute_Psec_exp_smul S.commute_Psec_QbarUMinus _).mul_right
    (S.commute_Psec_exp_smul S.commute_Psec_QbarMinus _)

theorem commute_Psec_Mplus (φ : ℝ) : Commute S.Psec (S.Mplus φ) :=
  (S.commute_Psec_exp_smul S.commute_Psec_QbarUPlus _).mul_right
    (S.commute_Psec_exp_smul S.commute_Psec_QbarPlus _)

theorem commute_Psec_Ominus : Commute S.Psec S.Ominus :=
  S.commute_Psec_exp_smul S.commute_Psec_QbarMinus _

theorem commute_Psec_Oplus : Commute S.Psec S.Oplus :=
  S.commute_Psec_exp_smul S.commute_Psec_QbarPlus _

/-! ## The compression form of the clustering hypotheses -/

/-- From `clu_M`: Lemma 6.14's `ε₁ ≤ ε` for `V_± = 𝓜_±(φ)`, uniformly in `φ ∈ [0, 2π]`. -/
theorem compress_M_le {ε : ℝ}
    (clu_M : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π), ‖⁅S.Qf (S.Mplus φ), S.Mminus φ⁆‖ ≤ ε)
    {φ : ℝ} (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * π)) :
    ‖S.P * S.Mplus φ * (1 - S.P) * S.Mminus φ * S.P‖ ≤ ε :=
  (S.norm_compression_le (S.commute_Psec_Mplus φ) _).trans (clu_M φ hφ)

/-- From `clu_M_adj`: Lemma 6.14's `ε₂ ≤ ε` for `V_± = 𝓜_±(φ)`, uniformly in `φ ∈ [0, 2π]`. -/
theorem compress_M_adj_le {ε : ℝ}
    (clu_M_adj : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖⁅S.Qf (star (S.Mplus φ)), star (S.Mminus φ)⁆‖ ≤ ε)
    {φ : ℝ} (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * π)) :
    ‖S.P * star (S.Mplus φ) * (1 - S.P) * star (S.Mminus φ) * S.P‖ ≤ ε :=
  (S.norm_compression_le (S.commute_Psec_star (S.commute_Psec_Mplus φ)) _).trans
    (clu_M_adj φ hφ)

/-- From `clu_O`: Lemma 6.14's `ε₁ ≤ ε` for `V_± = e^{2πi Q̄_±}`. -/
theorem compress_O_le {ε : ℝ} (clu_O : ‖⁅S.Qf S.Oplus, S.Ominus⁆‖ ≤ ε) :
    ‖S.P * S.Oplus * (1 - S.P) * S.Ominus * S.P‖ ≤ ε :=
  (S.norm_compression_le S.commute_Psec_Oplus _).trans clu_O

/-- From `clu_O_adj`: Lemma 6.14's `ε₂ ≤ ε` for `V_± = e^{2πi Q̄_±}`. -/
theorem compress_O_adj_le {ε : ℝ} (clu_O_adj : ‖⁅S.Qf (star S.Oplus), star S.Ominus⁆‖ ≤ ε) :
    ‖S.P * star S.Oplus * (1 - S.P) * star S.Ominus * S.P‖ ≤ ε :=
  (S.norm_compression_le (S.commute_Psec_star S.commute_Psec_Oplus) _).trans clu_O_adj

end Setting

end HRTorus.IndexCore
