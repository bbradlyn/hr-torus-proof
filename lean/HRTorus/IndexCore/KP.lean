import HRTorus.IndexCore.Spectral

/-!
# Lemma 6.7, the in-sector identity `[K, P] = [Q, P]`

Written by Claude Opus 5.5 (an AI model), 2026-10-23. The HR paper's Lemma 6.7: under Assumption 6.3, `[K, P] = [Q, P]`, hence
`[Q̄, P] = 0` exactly; with the consequences of Lemma 6.6(i) that the finite argument uses:
`K = K_- + K_+` is the dressing of `i[H, Q]`, and `K_±` are self-adjoint and sector-preserving.

The proof is the paper's, block by block: `P_E K P_{E'} = f(E, E') P_E Q P_{E'}` with
`f(E, E') = Ŵ(E' - E) · i(E - E')`, which is `1` when `|E - E'| ≥ γ`; the blocks of `[X, P]` are
nonzero only when exactly one of `E, E'` lies in `[a, b]`, and then (if the block meets the
sector) the gap gives `|E - E'| ≥ γ`.
-/

open scoped InnerProductSpace ComplexConjugate
open Complex (I)

noncomputable section
open Classical

namespace HRTorus.IndexCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

namespace Setting

variable (S : Setting E)

/-- `K_- + K_+` is the dressing of `i[H, Q]` (Lemma 6.6(i): `K = K_- + K_+`). -/
theorem Kminus_add_Kplus :
    S.Kminus + S.Kplus =
      spectralSum S.H S.H_sa (fun μ ν => S.W (ν - μ)) (I • ⁅S.H, S.Q⁆) := by
  rw [Setting.Kminus, Setting.Kplus, ← spectralSum_add, S.current_split]
  rfl

/-- The blocks of `i[H, A]`: `P_μ (i[H, A]) P_ν = i(μ - ν) P_μ A P_ν`. -/
theorem block_I_lie_H (A : E →L[ℂ] E) (μ ν : ℝ) :
    eigProj S.H S.H_sa μ * (I • ⁅S.H, A⁆) * eigProj S.H S.H_sa ν =
      (I * ((μ : ℂ) - ν)) • (eigProj S.H S.H_sa μ * A * eigProj S.H S.H_sa ν) := by
  have h1 : eigProj S.H S.H_sa μ * (S.H * A) * eigProj S.H S.H_sa ν =
      (μ : ℂ) • (eigProj S.H S.H_sa μ * A * eigProj S.H S.H_sa ν) := by
    rw [← mul_assoc, eigProj_mul, smul_mul_assoc, smul_mul_assoc]
  have h2 : eigProj S.H S.H_sa μ * (A * S.H) * eigProj S.H S.H_sa ν =
      (ν : ℂ) • (eigProj S.H S.H_sa μ * A * eigProj S.H S.H_sa ν) := by
    rw [mul_assoc, mul_assoc, mul_eigProj, mul_smul_comm, mul_smul_comm, ← mul_assoc]
  rw [Ring.lie_def, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, h1, h2, ← sub_smul,
    smul_smul]

/-- `f(E, E') = Ŵ(E' - E) · i(E - E') = 1` when `|E - E'| ≥ γ` (proof of Lemma 6.7). -/
theorem W_coeff_eq_one {μ ν : ℝ} (h : S.γ ≤ |μ - ν|) :
    S.W (ν - μ) * (I * ((μ : ℂ) - ν)) = 1 := by
  have hγ := S.γ_pos
  have h' : S.γ ≤ |ν - μ| := by rwa [abs_sub_comm]
  have hne : ((ν : ℂ) - μ) ≠ 0 := by
    have : ν - μ ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h'
      linarith
    exact_mod_cast this
  rw [S.W_eq _ h', Complex.ofReal_sub, div_mul_eq_mul_div, div_eq_one_iff_eq hne, ← mul_assoc,
    Complex.I_mul_I]
  ring

/-- The blocks of the dressing: `P_μ K P_ν = Ŵ(ν - μ) i(μ - ν) P_μ Q P_ν`. -/
theorem block_K (μ ν : ℝ) :
    eigProj S.H S.H_sa μ * (S.Kminus + S.Kplus) * eigProj S.H S.H_sa ν =
      (S.W (ν - μ) * (I * ((μ : ℂ) - ν))) •
        (eigProj S.H S.H_sa μ * S.Q * eigProj S.H S.H_sa ν) := by
  rw [S.Kminus_add_Kplus, eigProj_mul_spectralSum_mul_eigProj, S.block_I_lie_H, smul_smul]

/-- `K_-` is sector-preserving (Lemma 6.6(i)). -/
theorem commute_Psec_Kminus : Commute S.Psec S.Kminus :=
  commute_spectralSum S.H S.H_sa S.Psec_H S.Psec_Jminus _

/-- `K_+` is sector-preserving (Lemma 6.6(i)). -/
theorem commute_Psec_Kplus : Commute S.Psec S.Kplus :=
  commute_spectralSum S.H S.H_sa S.Psec_H S.Psec_Jplus _

theorem commute_Psec_K : Commute S.Psec (S.Kminus + S.Kplus) :=
  S.commute_Psec_Kminus.add_right S.commute_Psec_Kplus

/-- `K_-` is self-adjoint (Lemma 6.6(i)), from `Ŵ(-ω) = conj Ŵ(ω)`. -/
theorem star_Kminus : star S.Kminus = S.Kminus := by
  rw [Setting.Kminus, star_spectralSum, S.Jminus_sa.star_eq]
  congr 1
  funext μ ν
  simp only [← S.W_conj, neg_sub]

/-- `K_+` is self-adjoint (Lemma 6.6(i)). -/
theorem star_Kplus : star S.Kplus = S.Kplus := by
  rw [Setting.Kplus, star_spectralSum, S.Jplus_sa.star_eq]
  congr 1
  funext μ ν
  simp only [← S.W_conj, neg_sub]

theorem isSelfAdjoint_Kminus : IsSelfAdjoint S.Kminus := S.star_Kminus

theorem isSelfAdjoint_Kplus : IsSelfAdjoint S.Kplus := S.star_Kplus

theorem isSelfAdjoint_Q : IsSelfAdjoint S.Q :=
  (S.Qminus_sa.add S.Qmid_sa).add S.Qplus_sa

theorem isSelfAdjoint_Qbar : IsSelfAdjoint S.Qbar :=
  (S.isSelfAdjoint_Q.sub S.isSelfAdjoint_Kminus).sub S.isSelfAdjoint_Kplus

/-- **Lemma 6.7** (the in-sector identity): `[K, P] = [Q, P]`. -/
theorem lie_K_P : ⁅S.Kminus + S.Kplus, S.P⁆ = ⁅S.Q, S.P⁆ := by
  have hγ := S.γ_pos
  apply ext_blocks S.H S.H_sa
  intro μ _ ν _
  by_cases hμI : μ ∈ Set.Icc S.a S.b <;> by_cases hνI : ν ∈ Set.Icc S.a S.b
  · rw [S.block_lie_P_of_mem_of_mem S.commute_Psec_K hμI hνI,
      S.block_lie_P_of_mem_of_mem S.commute_Psec_Q hμI hνI]
  · -- `μ ∈ [a, b]`, `ν ∉ [a, b]`
    rw [S.block_lie_P_of_mem_of_not_mem S.commute_Psec_K hμI hνI,
      S.block_lie_P_of_mem_of_not_mem S.commute_Psec_Q hμI hνI, S.block_K, smul_mul_assoc]
    congr 1
    by_cases h0 : eigProj S.H S.H_sa μ * S.Q * eigProj S.H S.H_sa ν * S.Psec = 0
    · rw [h0, smul_zero]
    · have hν' : S.b + S.γ ≤ ν := (S.gap_right_of_block_ne_zero h0).resolve_right hνI
      have hc : S.γ ≤ |μ - ν| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hμI.2])]
        linarith [hμI.2]
      rw [S.W_coeff_eq_one hc, one_smul]
  · -- `μ ∉ [a, b]`, `ν ∈ [a, b]`
    rw [S.block_lie_P_of_not_mem_of_mem _ hμI hνI, S.block_lie_P_of_not_mem_of_mem _ hμI hνI,
      S.block_K, smul_mul_assoc]
    by_cases h0 : eigProj S.H S.H_sa μ * S.Q * eigProj S.H S.H_sa ν * S.Psec = 0
    · rw [h0, smul_zero]
    · have hμ' : S.b + S.γ ≤ μ := (S.gap_left_of_block_ne_zero S.commute_Psec_Q h0).resolve_left hμI
      have hc : S.γ ≤ |μ - ν| := by
        rw [abs_of_nonneg (by linarith [hνI.2])]
        linarith [hνI.2]
      rw [S.W_coeff_eq_one hc, one_smul]
  · rw [S.block_lie_P_of_not_mem_of_not_mem _ hμI hνI,
      S.block_lie_P_of_not_mem_of_not_mem _ hμI hνI]

/-- **Lemma 6.7**, second form: `[Q̄, P] = 0` exactly. -/
theorem lie_Qbar_P : ⁅S.Qbar, S.P⁆ = 0 := by
  have h := S.lie_K_P
  rw [Ring.lie_def, Ring.lie_def] at h
  have hQbar : S.Qbar = S.Q - (S.Kminus + S.Kplus) := by
    rw [Setting.Qbar, sub_sub]
  rw [hQbar, Ring.lie_def, sub_mul, mul_sub, sub_sub_sub_comm, ← h, sub_self]

/-- `Q̄` commutes with `P` (Lemma 6.7). -/
theorem commute_Qbar_P : Commute S.Qbar S.P :=
  commute_iff_lie_eq.mpr S.lie_Qbar_P

end Setting

end HRTorus.IndexCore
