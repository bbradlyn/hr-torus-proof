import HRTorus.IndexCore.BBDF42
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Lemma 6.16: the differential equation and its stability

Written by Claude Opus 5.5 (an AI model), 2026-10-23. The paper is the HR paper (`papers/hr/`), Section 6,
`lem:ode` (Lemma 6.16). For `φ ∈ ℝ`:

* `𝒵(φ) = P 𝓜₋(φ) P` (`Zc`), `𝒢(φ) = e^{iφQ̄} P T̃ P e^{-iφQ̄}` (`Gc`),
  `𝒴(φ) = P e^{iφ(P T̃ P + Q̄)} e^{-iφQ̄} P` (`Yc`), and `ℰ(φ) = -i 𝒵'(φ) - 𝒵(φ) 𝒢(φ)` (`Ec`),
  written out as `P e^{iφQ̄^U₋} T̃ e^{-iφQ̄₋} P - 𝒵(φ) 𝒢(φ)`.

Proved: `𝒢 = P 𝒢 P` is self-adjoint; `-i 𝒵' = 𝒵 𝒢 + ℰ` (`hasDerivAt_Zc`); `-i 𝒴' = 𝒴 𝒢`
exactly (`hasDerivAt_Yc`); `𝒵(0) = 𝒴(0) = P`; and the lemma's bound
`‖𝒵(φ) - 𝒴(φ)‖ ≤ ∫₀^φ ‖ℰ(u)‖ du` for `φ ≥ 0` (`norm_Zc_sub_Yc_le`), with the size of `ℰ` from
the lemma's proof: `‖ℰ(φ)‖ ≤ ‖[𝓜₋(φ), P]‖ ‖T̃‖ + φ² ‖[Q̄₋, Q_m + Q̄₊]‖ ‖T̃‖ + |φ| ‖[Q_m + Q̄₊, T̃]‖`
(`norm_Ec_le`).

**The route.** The paper compares `𝒵` and `𝒴` through the propagator of
`∂_φ 𝒰 = i 𝒰 𝒢`. Here the comparison uses the integrating factor `W(φ) = e^{iφ(P T̃ P + Q̄)}
e^{-iφQ̄}`, a unitary with `𝒴 = P W`: the function `G(φ) = 𝒵(φ) W(φ)^* - P` vanishes at `0`, has
derivative `i ℰ(φ) W(φ)^*`, and `𝒵 - 𝒴 = G W`. The fundamental theorem of calculus then gives the
stated bound. The error terms and the bound are the paper's; only the comparison argument differs.
-/

open scoped InnerProductSpace ComplexConjugate Real
open Complex (I)

noncomputable section

namespace HRTorus.IndexCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

section Continuity

variable (A : E →L[ℂ] E)

omit [FiniteDimensional ℂ E] in
theorem norm_conj_expI (hA : IsSelfAdjoint A) (φ : ℝ) (X : E →L[ℂ] E) :
    ‖expI φ A * X * expI (-φ) A‖ = ‖X‖ := by
  rw [norm_mul_expI _ hA, norm_expI_mul _ hA]

omit [FiniteDimensional ℂ E] in
@[fun_prop]
theorem continuous_expI_comp {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous fun t : ℝ => expI (f t) A :=
  (continuous_iff_continuousAt.2 fun t => (hasDerivAt_expI A t).continuousAt).comp hf

end Continuity

namespace Setting

variable (S : Setting E)

/-- `𝒵(φ) = P 𝓜₋(φ) P`. -/
def Zc (φ : ℝ) : E →L[ℂ] E := S.P * S.Mminus φ * S.P

/-- `𝒢(φ) = e^{iφQ̄} P T̃ P e^{-iφQ̄}`. -/
def Gc (φ : ℝ) : E →L[ℂ] E := expI φ S.Qbar * (S.P * S.Ttilde * S.P) * expI (-φ) S.Qbar

/-- The generator `P T̃ P + Q̄` of the comparison flow. -/
def Ac : E →L[ℂ] E := S.P * S.Ttilde * S.P + S.Qbar

/-- `𝒴(φ) = P e^{iφ(P T̃ P + Q̄)} e^{-iφQ̄} P`. -/
def Yc (φ : ℝ) : E →L[ℂ] E := S.P * (expI φ S.Ac * expI (-φ) S.Qbar) * S.P

/-- `ℰ(φ) = -i 𝒵'(φ) - 𝒵(φ) 𝒢(φ)`, with `-i 𝒵'(φ) = P e^{iφQ̄^U₋} T̃ e^{-iφQ̄₋} P`. -/
def Ec (φ : ℝ) : E →L[ℂ] E :=
  S.P * (expI φ S.QbarUMinus * S.Ttilde * expI (-φ) S.QbarMinus) * S.P - S.Zc φ * S.Gc φ

/-- The integrating factor `W(φ) = e^{iφ(P T̃ P + Q̄)} e^{-iφQ̄}`. -/
def Wc (φ : ℝ) : E →L[ℂ] E := expI φ S.Ac * expI (-φ) S.Qbar

/-- `W(φ)^* = e^{iφQ̄} e^{-iφ(P T̃ P + Q̄)}`. -/
def WcStar (φ : ℝ) : E →L[ℂ] E := expI φ S.Qbar * expI (-φ) S.Ac

theorem Ttilde_eq : S.QbarUMinus - S.QbarMinus = S.Ttilde := by
  simp only [Setting.QbarUMinus, Setting.QbarMinus, Setting.Ttilde]; abel

theorem isSelfAdjoint_PTP : IsSelfAdjoint (S.P * S.Ttilde * S.P) := by
  show star (S.P * S.Ttilde * S.P) = S.P * S.Ttilde * S.P
  rw [star_mul, star_mul, S.star_P, S.isSelfAdjoint_Ttilde.star_eq, mul_assoc]

theorem isSelfAdjoint_Ac : IsSelfAdjoint S.Ac := S.isSelfAdjoint_PTP.add S.isSelfAdjoint_Qbar

theorem commute_P_Ac : Commute S.P S.Ac := by
  have hPP := S.P_mul_self
  have hQ := S.commute_Qbar_P.eq
  show S.P * (S.P * S.Ttilde * S.P + S.Qbar) = (S.P * S.Ttilde * S.P + S.Qbar) * S.P
  rw [mul_add, add_mul, hQ, ← mul_assoc, ← mul_assoc, hPP, mul_assoc _ S.P S.P, hPP]

theorem commute_P_expI_Ac (t : ℝ) : Commute S.P (expI t S.Ac) :=
  commute_expI_of_commute S.Ac S.commute_P_Ac t

theorem isSelfAdjoint_Gc (φ : ℝ) : IsSelfAdjoint (S.Gc φ) := by
  show star (S.Gc φ) = S.Gc φ
  rw [Setting.Gc, star_mul, star_mul, star_expI _ S.isSelfAdjoint_Qbar,
    star_expI _ S.isSelfAdjoint_Qbar, S.isSelfAdjoint_PTP.star_eq, neg_neg]
  simp only [mul_assoc]

/-- `𝒢 = P 𝒢 P`. -/
theorem P_mul_Gc_mul_P (φ : ℝ) : S.P * S.Gc φ * S.P = S.Gc φ := by
  have hq : ∀ X, S.P * (expI φ S.Qbar * X) = expI φ S.Qbar * (S.P * X) :=
    (S.commute_P_expI_Qbar φ).left_comm
  have hpp : ∀ X, S.P * (S.P * X) = S.P * X := fun X => by rw [← mul_assoc, S.P_mul_self]
  have hn : expI (-φ) S.Qbar * S.P = S.P * expI (-φ) S.Qbar := (S.commute_P_expI_Qbar (-φ)).eq.symm
  simp only [Setting.Gc, mul_assoc, hq, hpp, hn]

theorem Zc_zero : S.Zc 0 = S.P := by
  rw [Setting.Zc, S.Mminus_eq, neg_zero, expI_zero, expI_zero, mul_one, mul_one, S.P_mul_self]

theorem Yc_zero : S.Yc 0 = S.P := by
  rw [Setting.Yc, neg_zero, expI_zero, expI_zero, mul_one, mul_one, S.P_mul_self]

/-- **`-i 𝒵' = 𝒵 𝒢 + ℰ`**: `𝒵'(φ) = i (𝒵(φ) 𝒢(φ) + ℰ(φ))`. -/
theorem hasDerivAt_Zc (φ : ℝ) : HasDerivAt S.Zc (I • (S.Zc φ * S.Gc φ + S.Ec φ)) φ := by
  have h := (((hasDerivAt_expI S.QbarUMinus φ).mul
    (hasDerivAt_expI_neg S.QbarMinus φ)).const_mul S.P).mul_const S.P
  simp only [Pi.mul_apply] at h
  have h' : HasDerivAt S.Zc _ φ := h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by simp only [Setting.Zc, S.Mminus_eq])
  refine h'.congr_deriv ?_
  have e : S.Zc φ * S.Gc φ + S.Ec φ =
      S.P * (expI φ S.QbarUMinus * S.Ttilde * expI (-φ) S.QbarMinus) * S.P := by
    rw [Setting.Ec]; abel
  rw [e]
  calc S.P * (expI φ S.QbarUMinus * (I • S.QbarUMinus) * expI (-φ) S.QbarMinus +
        expI φ S.QbarUMinus * -((I • S.QbarMinus) * expI (-φ) S.QbarMinus)) * S.P
      = S.P * (expI φ S.QbarUMinus * (I • S.Ttilde) * expI (-φ) S.QbarMinus) * S.P := by
        rw [← S.Ttilde_eq, smul_sub]; noncomm_ring
    _ = I • (S.P * (expI φ S.QbarUMinus * S.Ttilde * expI (-φ) S.QbarMinus) * S.P) := by
        simp only [mul_smul_comm, smul_mul_assoc]

/-- **`-i 𝒴' = 𝒴 𝒢` exactly**: `𝒴'(φ) = i 𝒴(φ) 𝒢(φ)`. -/
theorem hasDerivAt_Yc (φ : ℝ) : HasDerivAt S.Yc (I • (S.Yc φ * S.Gc φ)) φ := by
  have h := (((hasDerivAt_expI S.Ac φ).mul
    (hasDerivAt_expI_neg S.Qbar φ)).const_mul S.P).mul_const S.P
  simp only [Pi.mul_apply] at h
  have h' : HasDerivAt S.Yc _ φ := h
  refine h'.congr_deriv ?_
  have hAc : I • S.Ac = I • (S.P * S.Ttilde * S.P) + I • S.Qbar := by rw [Setting.Ac, smul_add]
  have r2 : ∀ X : E →L[ℂ] E, expI (-φ) S.Qbar * (expI φ S.Qbar * X) = X := fun X => by
    rw [← mul_assoc, expI_neg_mul_expI, one_mul]
  have r3 : ∀ X : E →L[ℂ] E, S.P * (S.P * X) = S.P * X := fun X => by
    rw [← mul_assoc, S.P_mul_self]
  have r4' : expI (-φ) S.Qbar * S.P = S.P * expI (-φ) S.Qbar :=
    (S.commute_P_expI_Qbar (-φ)).eq.symm
  calc S.P * (expI φ S.Ac * (I • S.Ac) * expI (-φ) S.Qbar +
        expI φ S.Ac * -((I • S.Qbar) * expI (-φ) S.Qbar)) * S.P
      = S.P * (expI φ S.Ac * (I • (S.P * S.Ttilde * S.P)) * expI (-φ) S.Qbar) * S.P := by
        rw [hAc]; noncomm_ring
    _ = I • (S.P * (expI φ S.Ac * (S.P * S.Ttilde * S.P) * expI (-φ) S.Qbar) * S.P) := by
        simp only [mul_smul_comm, smul_mul_assoc]
    _ = I • (S.Yc φ * S.Gc φ) := by
        congr 1
        simp only [Setting.Yc, Setting.Gc, mul_assoc, r2, r3, r4']

theorem WcStar_mul_Wc (φ : ℝ) : S.WcStar φ * S.Wc φ = 1 := by
  rw [Setting.WcStar, Setting.Wc, mul_assoc, ← mul_assoc (expI (-φ) S.Ac), expI_neg_mul_expI,
    one_mul, expI_mul_expI_neg]

theorem norm_Wc_le (φ : ℝ) : ‖S.Wc φ‖ ≤ 1 := by
  rw [Setting.Wc, norm_expI_mul _ S.isSelfAdjoint_Ac]; exact norm_expI_le _ S.isSelfAdjoint_Qbar _

theorem norm_WcStar_le (φ : ℝ) : ‖S.WcStar φ‖ ≤ 1 := by
  rw [Setting.WcStar, norm_expI_mul _ S.isSelfAdjoint_Qbar]
  exact norm_expI_le _ S.isSelfAdjoint_Ac _

/-- `𝒴(φ) = P W(φ)`. -/
theorem Yc_eq (φ : ℝ) : S.Yc φ = S.P * S.Wc φ := by
  have hc : Commute S.P (S.Wc φ) :=
    (S.commute_P_expI_Ac φ).mul_right (S.commute_P_expI_Qbar (-φ))
  rw [Setting.Yc, ← Setting.Wc, mul_assoc, ← hc.eq, ← mul_assoc, S.P_mul_self]

/-- `G(φ) = 𝒵(φ) W(φ)^* - P` has derivative `i ℰ(φ) W(φ)^*`. -/
theorem hasDerivAt_G (φ : ℝ) :
    HasDerivAt (fun u => S.Zc u * S.WcStar u - S.P) (I • (S.Ec φ * S.WcStar φ)) φ := by
  have hW : HasDerivAt S.WcStar (expI φ S.Qbar * (I • S.Qbar) * expI (-φ) S.Ac +
      expI φ S.Qbar * -((I • S.Ac) * expI (-φ) S.Ac)) φ :=
    (hasDerivAt_expI S.Qbar φ).mul (hasDerivAt_expI_neg S.Ac φ)
  have h := ((S.hasDerivAt_Zc φ).mul hW).sub_const S.P
  refine h.congr_deriv ?_
  set eQ := expI φ S.Qbar
  set eB := expI (-φ) S.Qbar
  set eN := expI (-φ) S.Ac
  set PT := S.P * S.Ttilde * S.P
  have hGW : S.Gc φ * S.WcStar φ = eQ * PT * eN := by
    rw [Setting.Gc, Setting.WcStar, mul_assoc, mul_assoc, ← mul_assoc eB, expI_neg_mul_expI,
      one_mul, ← mul_assoc]
  have hW' : eQ * (I • S.Qbar) * eN + eQ * -((I • S.Ac) * eN) = -(I • (eQ * PT * eN)) := by
    have hAc : I • S.Ac = I • PT + I • S.Qbar := by rw [Setting.Ac, smul_add]
    rw [hAc]
    have : eQ * (I • S.Qbar) * eN + eQ * -((I • PT + I • S.Qbar) * eN) =
        -(eQ * (I • PT) * eN) := by noncomm_ring
    rw [this]
    simp only [mul_smul_comm, smul_mul_assoc]
  rw [hW', smul_mul_assoc, add_mul, mul_assoc (S.Zc φ), hGW, mul_neg, mul_smul_comm, smul_add]
  abel

theorem continuous_Zc : Continuous S.Zc := by
  have : S.Zc = fun u => S.P * (expI u S.QbarUMinus * expI (-u) S.QbarMinus) * S.P := by
    funext u; rw [Setting.Zc, S.Mminus_eq]
  rw [this]; fun_prop

theorem continuous_Ec : Continuous S.Ec := by
  have hZ := S.continuous_Zc
  unfold Setting.Ec Setting.Gc
  fun_prop

theorem continuous_WcStar : Continuous S.WcStar := by
  unfold Setting.WcStar; fun_prop

/-- **Lemma 6.16, the stability bound**: `‖𝒵(φ) - 𝒴(φ)‖ ≤ ∫₀^φ ‖ℰ(u)‖ du` for `φ ≥ 0`. -/
theorem norm_Zc_sub_Yc_le {φ : ℝ} (hφ : 0 ≤ φ) :
    ‖S.Zc φ - S.Yc φ‖ ≤ ∫ u in (0 : ℝ)..φ, ‖S.Ec u‖ := by
  set G : ℝ → E →L[ℂ] E := fun u => S.Zc u * S.WcStar u - S.P with hG
  have hG0 : G 0 = 0 := by
    simp only [hG, S.Zc_zero, Setting.WcStar, neg_zero, expI_zero, mul_one, sub_self]
  have hcont : Continuous fun u => I • (S.Ec u * S.WcStar u) := by
    have := S.continuous_Ec; have := S.continuous_WcStar; fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => S.hasDerivAt_G u) (hcont.intervalIntegrable 0 φ)
  -- `𝒵 - 𝒴 = G W`
  have hdiff : S.Zc φ - S.Yc φ = G φ * S.Wc φ := by
    simp only [hG, sub_mul, mul_assoc, S.WcStar_mul_Wc, mul_one, S.Yc_eq]
  have h1 : ‖S.Zc φ - S.Yc φ‖ ≤ ‖G φ‖ := by
    rw [hdiff]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (S.norm_Wc_le φ))
  have h2 : G φ = ∫ u in (0 : ℝ)..φ, I • (S.Ec u * S.WcStar u) := by
    rw [hftc, show S.Zc 0 * S.WcStar 0 - S.P = 0 from hG0, sub_zero]
  have h3 : ‖∫ u in (0 : ℝ)..φ, I • (S.Ec u * S.WcStar u)‖ ≤
      ∫ u in (0 : ℝ)..φ, ‖I • (S.Ec u * S.WcStar u)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hφ
  have h4 : (∫ u in (0 : ℝ)..φ, ‖I • (S.Ec u * S.WcStar u)‖) ≤ ∫ u in (0 : ℝ)..φ, ‖S.Ec u‖ := by
    refine intervalIntegral.integral_mono_on hφ (hcont.norm.intervalIntegrable 0 φ)
      (S.continuous_Ec.norm.intervalIntegrable 0 φ) fun u _ => ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (S.norm_WcStar_le u))
  rw [← h2] at h3
  exact h1.trans (h3.trans h4)

/-- Lemma 6.16's bound with a uniform bound on `ℰ`: if `‖ℰ(u)‖ ≤ C` on `[0, φ]`, then
`‖𝒵(φ) - 𝒴(φ)‖ ≤ C φ`. -/
theorem norm_Zc_sub_Yc_le_mul {φ C : ℝ} (hφ : 0 ≤ φ) (hE : ∀ u ∈ Set.Icc 0 φ, ‖S.Ec u‖ ≤ C) :
    ‖S.Zc φ - S.Yc φ‖ ≤ C * φ := by
  refine (S.norm_Zc_sub_Yc_le hφ).trans ?_
  have := intervalIntegral.integral_mono_on hφ (S.continuous_Ec.norm.intervalIntegrable 0 φ)
    (intervalIntegrable_const (μ := MeasureTheory.volume)) hE
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm] at this
  exact this

/-! ## The size of `ℰ` (the proof of Lemma 6.16) -/

/-- `ℰ = P 𝓜₋ (1 - P) X P + P 𝓜₋ P (X - Y) P`, with `X = e^{iφQ̄₋} T̃ e^{-iφQ̄₋}` and
`Y = e^{iφQ̄} T̃ e^{-iφQ̄}`. -/
theorem Ec_eq (φ : ℝ) : S.Ec φ =
    S.P * S.Mminus φ * (1 - S.P) *
        (expI φ S.QbarMinus * S.Ttilde * expI (-φ) S.QbarMinus) * S.P +
      S.P * S.Mminus φ * S.P * (expI φ S.QbarMinus * S.Ttilde * expI (-φ) S.QbarMinus -
        expI φ S.Qbar * S.Ttilde * expI (-φ) S.Qbar) * S.P := by
  have hM : expI φ S.QbarUMinus * S.Ttilde * expI (-φ) S.QbarMinus =
      S.Mminus φ * (expI φ S.QbarMinus * S.Ttilde * expI (-φ) S.QbarMinus) := by
    have r : ∀ X : E →L[ℂ] E, expI (-φ) S.QbarMinus * (expI φ S.QbarMinus * X) = X := fun X => by
      rw [← mul_assoc, expI_neg_mul_expI, one_mul]
    rw [S.Mminus_eq]
    simp only [mul_assoc, r]
  have hG : S.Zc φ * S.Gc φ =
      S.P * S.Mminus φ * S.P * (expI φ S.Qbar * S.Ttilde * expI (-φ) S.Qbar) * S.P := by
    have hq : ∀ X, S.P * (expI φ S.Qbar * X) = expI φ S.Qbar * (S.P * X) :=
      (S.commute_P_expI_Qbar φ).left_comm
    have hn' : S.P * expI (-φ) S.Qbar = expI (-φ) S.Qbar * S.P := (S.commute_P_expI_Qbar (-φ)).eq
    have hpp : ∀ X, S.P * (S.P * X) = S.P * X := fun X => by rw [← mul_assoc, S.P_mul_self]
    simp only [Setting.Zc, Setting.Gc, mul_assoc, hq, hn', hpp]
  rw [Setting.Ec, hM, hG]
  noncomm_ring

/-- `‖X - Y‖ ≤ φ² ‖[Q̄₋, B]‖ ‖T̃‖ + |φ| ‖[B, T̃]‖` with `B = Q_m + Q̄₊` (the bound on `ℰ₂`). -/
theorem norm_X_sub_Y_le (φ : ℝ) :
    ‖expI φ S.QbarMinus * S.Ttilde * expI (-φ) S.QbarMinus -
        expI φ S.Qbar * S.Ttilde * expI (-φ) S.Qbar‖ ≤
      φ ^ 2 * ‖⁅S.QbarMinus, S.Qmid + S.QbarPlus⁆‖ * ‖S.Ttilde‖ +
        |φ| * ‖⁅S.Qmid + S.QbarPlus, S.Ttilde⁆‖ := by
  set B := S.Qmid + S.QbarPlus with hB
  set T := S.Ttilde
  have hBsa : IsSelfAdjoint B := S.Qmid_sa.add S.isSelfAdjoint_QbarPlus
  have hm := S.isSelfAdjoint_QbarMinus
  have hQ : S.Qbar = S.QbarMinus + B := by rw [S.Qbar_eq, hB, add_assoc]
  set O₁ := expI φ S.Qbar
  set O₁s := expI (-φ) S.Qbar
  set O₂ := expI φ S.QbarMinus * expI φ B
  set O₂s := expI (-φ) B * expI (-φ) S.QbarMinus
  have hO₁ : ‖O₁‖ ≤ 1 := norm_expI_le _ S.isSelfAdjoint_Qbar _
  have hO₂s : ‖O₂s‖ ≤ 1 := by
    rw [norm_expI_mul _ hBsa]; exact norm_expI_le _ hm _
  have hd : ‖O₂ - O₁‖ ≤ φ ^ 2 / 2 * ‖⁅S.QbarMinus, B⁆‖ := by
    rw [norm_sub_rev]
    show ‖expI φ S.Qbar - expI φ S.QbarMinus * expI φ B‖ ≤ _
    rw [hQ]; exact norm_expI_add_sub_le _ hm hBsa φ
  have hds : ‖O₂s - O₁s‖ ≤ φ ^ 2 / 2 * ‖⁅S.QbarMinus, B⁆‖ := by
    have : O₂s - O₁s = star (O₂ - O₁) := by
      rw [star_sub, star_mul, star_expI _ hBsa, star_expI _ hm, star_expI _ S.isSelfAdjoint_Qbar]
    rw [this]; exact (norm_star (O₂ - O₁)).le.trans hd
  -- the conjugation by `e^{iφB}`
  have hX : ‖expI φ S.QbarMinus * T * expI (-φ) S.QbarMinus - O₂ * T * O₂s‖ ≤
      |φ| * ‖⁅B, T⁆‖ := by
    have e1 : expI φ S.QbarMinus * T * expI (-φ) S.QbarMinus - O₂ * T * O₂s =
        expI φ S.QbarMinus * (T - expI φ B * T * expI (-φ) B) * expI (-φ) S.QbarMinus := by
      simp only [O₂, O₂s]; noncomm_ring
    have e2 : T - expI φ B * T * expI (-φ) B = -(⁅expI φ B, T⁆ * expI (-φ) B) := by
      rw [Ring.lie_def, sub_mul, mul_assoc T, expI_mul_expI_neg, mul_one, neg_sub]
    have e : expI φ S.QbarMinus * T * expI (-φ) S.QbarMinus - O₂ * T * O₂s =
        expI φ S.QbarMinus * (-(⁅expI φ B, T⁆ * expI (-φ) B)) * expI (-φ) S.QbarMinus := by
      rw [e1, e2]
    rw [e, norm_conj_expI _ hm, norm_neg, norm_mul_expI _ hBsa]
    exact norm_lie_expI_le B hBsa T φ
  have hY : ‖O₂ * T * O₂s - O₁ * T * O₁s‖ ≤ φ ^ 2 * ‖⁅S.QbarMinus, B⁆‖ * ‖T‖ := by
    have e : O₂ * T * O₂s - O₁ * T * O₁s = (O₂ - O₁) * T * O₂s + O₁ * T * (O₂s - O₁s) := by
      noncomm_ring
    rw [e]
    calc ‖(O₂ - O₁) * T * O₂s + O₁ * T * (O₂s - O₁s)‖
        ≤ ‖O₂ - O₁‖ * ‖T‖ * ‖O₂s‖ + ‖O₁‖ * ‖T‖ * ‖O₂s - O₁s‖ :=
          (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
            ((norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))))
      _ ≤ (φ ^ 2 / 2 * ‖⁅S.QbarMinus, B⁆‖) * ‖T‖ * 1 + 1 * ‖T‖ * (φ ^ 2 / 2 * ‖⁅S.QbarMinus, B⁆‖) := by
          gcongr
      _ = φ ^ 2 * ‖⁅S.QbarMinus, B⁆‖ * ‖T‖ := by ring
  calc _ ≤ ‖expI φ S.QbarMinus * T * expI (-φ) S.QbarMinus - O₂ * T * O₂s‖ +
        ‖O₂ * T * O₂s - O₁ * T * O₁s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ |φ| * ‖⁅B, T⁆‖ + φ ^ 2 * ‖⁅S.QbarMinus, B⁆‖ * ‖T‖ := add_le_add hX hY
    _ = _ := by ring

/-- **The size of `ℰ`** (proof of Lemma 6.16):
`‖ℰ(φ)‖ ≤ ‖[𝓜₋(φ), P]‖ ‖T̃‖ + φ² ‖[Q̄₋, Q_m + Q̄₊]‖ ‖T̃‖ + |φ| ‖[Q_m + Q̄₊, T̃]‖`. -/
theorem norm_Ec_le (φ : ℝ) :
    ‖S.Ec φ‖ ≤ ‖⁅S.Mminus φ, S.P⁆‖ * ‖S.Ttilde‖ +
      (φ ^ 2 * ‖⁅S.QbarMinus, S.Qmid + S.QbarPlus⁆‖ * ‖S.Ttilde‖ +
        |φ| * ‖⁅S.Qmid + S.QbarPlus, S.Ttilde⁆‖) := by
  have hP1 : ‖S.P‖ ≤ 1 := IsStarProjection.norm_le S.P S.isStarProjection_P
  have hM1 : ‖S.Mminus φ‖ ≤ 1 := norm_le_one_of_mem_unitary (S.Mminus_mem_unitary φ)
  have hm := S.isSelfAdjoint_QbarMinus
  set X := expI φ S.QbarMinus * S.Ttilde * expI (-φ) S.QbarMinus
  set Y := expI φ S.Qbar * S.Ttilde * expI (-φ) S.Qbar
  have hX : ‖X‖ = ‖S.Ttilde‖ := norm_conj_expI _ hm φ _
  have hPM : S.P * S.Mminus φ * (1 - S.P) = -(S.P * ⁅S.Mminus φ, S.P⁆) := by
    simp only [Ring.lie_def, mul_sub, mul_one, ← mul_assoc, S.P_mul_self]; abel
  have e1 : ‖S.P * S.Mminus φ * (1 - S.P) * X * S.P‖ ≤ ‖⁅S.Mminus φ, S.P⁆‖ * ‖S.Ttilde‖ := by
    rw [hPM, ← hX]
    calc ‖-(S.P * ⁅S.Mminus φ, S.P⁆) * X * S.P‖
        ≤ ‖-(S.P * ⁅S.Mminus φ, S.P⁆)‖ * ‖X‖ * ‖S.P‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * ‖⁅S.Mminus φ, S.P⁆‖) * ‖X‖ * 1 := by
          rw [norm_neg]; gcongr; exact (norm_mul_le _ _).trans (by gcongr)
      _ = ‖⁅S.Mminus φ, S.P⁆‖ * ‖X‖ := by ring
  have e2 : ‖S.P * S.Mminus φ * S.P * (X - Y) * S.P‖ ≤ ‖X - Y‖ := by
    calc ‖S.P * S.Mminus φ * S.P * (X - Y) * S.P‖
        ≤ ‖S.P‖ * ‖S.Mminus φ‖ * ‖S.P‖ * ‖X - Y‖ * ‖S.P‖ := by
          refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          exact norm_mul_le _ _
      _ ≤ 1 * 1 * 1 * ‖X - Y‖ * 1 := by gcongr
      _ = ‖X - Y‖ := by ring
  rw [S.Ec_eq]
  exact (norm_add_le _ _).trans (add_le_add e1 (e2.trans (S.norm_X_sub_Y_le φ)))

variable {S} {ε : ℝ}

/-- `‖[Q̄₋, Q_m + Q̄₊]‖ ≤ 4 ε` (A1 + A5). -/
theorem SepBounds.norm_lie_QbarMinus_B_le (h : S.SepBounds ε) :
    ‖⁅S.QbarMinus, S.Qmid + S.QbarPlus⁆‖ ≤ 4 * ε := by
  have := norm_lie_add_right_le S.QbarMinus S.Qmid S.QbarPlus
  have a1 := norm_lie_le_of_comm h.A1
  have a5 := h.A5
  linarith

/-- `‖[Q_m + Q̄₊, T̃]‖ ≤ 9 ε` (A9 + A10). -/
theorem SepBounds.norm_lie_B_Ttilde_le (h : S.SepBounds ε) :
    ‖⁅S.Qmid + S.QbarPlus, S.Ttilde⁆‖ ≤ 9 * ε := by
  have := norm_lie_add_left_le S.Qmid S.QbarPlus S.Ttilde
  have a9 := h.A9
  have a10 := h.A10
  linarith

/-- `‖T̃‖ ≤ 3M` from `‖T₋‖, ‖K₋‖ ≤ M`. -/
theorem norm_Ttilde_le {M : ℝ} (hT : ‖S.Tminus‖ ≤ M) (hK : ‖S.Kminus‖ ≤ M) :
    ‖S.Ttilde‖ ≤ 3 * M := by
  have hKU : ‖S.KUminus‖ ≤ ‖S.Kminus‖ := by
    have hU1 : ‖S.U‖ ≤ 1 := norm_le_one_of_mem_unitary S.U_unitary
    have hUs1 : ‖star S.U‖ ≤ 1 := (norm_star S.U).le.trans hU1
    have e : S.KUminus = star S.U * S.Kminus * S.U := rfl
    rw [e]
    calc ‖star S.U * S.Kminus * S.U‖
        ≤ ‖star S.U‖ * ‖S.Kminus‖ * ‖S.U‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖S.Kminus‖ * 1 := by gcongr
      _ = ‖S.Kminus‖ := by ring
  have e : S.Ttilde = S.Tminus - S.KUminus + S.Kminus := rfl
  rw [e]
  have h1 := norm_add_le (S.Tminus - S.KUminus) S.Kminus
  have h2 := norm_sub_le S.Tminus S.KUminus
  linarith

end Setting

end HRTorus.IndexCore
