import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# A pilot: the analytic core of Lemma 4.1 (`lem:gram`) of the Laughlin torus paper

Written by Claude Opus 5.5 (an AI model), 2026-10-23. **A pilot:** the analytic core of one lemma of the Laughlin
paper, formalized on its own; the rest of that paper is not formalized in this repository. The
paper: the Laughlin paper,
`papers/laughlin/sections/04-projector.tex`, Lemma 4.1 and its proof; the notation `κ`, `L_x`, `L_y`,
`N_φ` from Definition 2.1 (`def:torus`) and `c₀`, `f` from Proposition `orbital`
(`sections/02-setting.tex`).

## What is stated

The analytic step of the proof of Lemma 4.1: Poisson summation on the coset `c + 2ℤ` for the
quadratic-times-Gaussian `g(u) = (u² − M²/4) e^{−κ²u²/2}`, with the Fourier transform of `g` in
closed form — parts (i) and (ii) — and the closed form of the paper's `S_j` that they give —
part (iii). The first sentence of Lemma 4.1 (the support of `G`) and the regrouping
`G_{n,n+mN_φ} = Σ_{j ≡ m (2)} S_j` are the orbital model's combinatorics and are not stated here.

## Conventions

* The Fourier transform is `ĝ(ξ) = ∫ g(u) e^{−2πiuξ} du`, the paper's convention (and that of
  Mathlib's `𝓕`); it is written out as an integral in the statements.
* A sum over a coset `c + 2ℤ` is written as the sum over `t : ℤ` of the term at `c + 2t`; the
  paper's sum over integers `d ≡ n (mod 2)` is the sum over `t : ℤ` of the term at `d = n + 2t`.
* Every series is stated summable, and the identities are between `tsum`s (Lean's `∑'`).
-/

open Real Complex MeasureTheory Filter Asymptotics
open scoped Real FourierTransform

noncomputable section

namespace HRTorus.Laughlin.GramPoisson

/-- The summand on the coset in the proof of Lemma 4.1: `g(u) = (u² − M²/4) e^{−κ²u²/2}`. -/
def g (κ M u : ℝ) : ℝ :=
  (u ^ 2 - M ^ 2 / 4) * Real.exp (-(κ ^ 2 * u ^ 2) / 2)

/-- The closed form of its Fourier transform:
`ĝ(ξ) = (√(2π)/κ³) (1 − 4π²ξ²/κ² − κ²M²/4) e^{−2π²ξ²/κ²}`. -/
def gHat (κ M ξ : ℝ) : ℝ :=
  Real.sqrt (2 * π) / κ ^ 3 * (1 - 4 * π ^ 2 * ξ ^ 2 / κ ^ 2 - κ ^ 2 * M ^ 2 / 4) *
    Real.exp (-(2 * π ^ 2 * ξ ^ 2) / κ ^ 2)

/-! ## Helpers for part (i) (proof devices, not statements of the paper) -/

/-- Helper: Mathlib's Fourier transform `𝓕` on `ℝ → ℂ`, written as the paper's integral
`∫ h(u) e^{−2πiuξ} du`. -/
theorem fourier_eq_integral (h : ℝ → ℂ) (ξ : ℝ) :
    𝓕 h ξ = ∫ u : ℝ, Complex.exp (-(2 * π * I * u * ξ)) * h u := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e : ((-2 * π * u * ξ : ℝ) : ℂ) * I = -(2 * π * I * u * ξ) := by push_cast; ring
  simp only [smul_eq_mul, e]

/-- Helper: the phase `e^{−2πiuξ}` times an integrable function is integrable. -/
theorem integrable_phase_mul {h : ℝ → ℂ} (hh : Integrable h) (ξ : ℝ) :
    Integrable (fun u : ℝ => Complex.exp (-(2 * π * I * u * ξ)) * h u) := by
  refine hh.bdd_mul (c := 1) ?_ (Eventually.of_forall fun u => le_of_eq ?_)
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · have e : -(2 * (π : ℂ) * I * u * ξ) = ((-2 * π * u * ξ : ℝ) : ℂ) * I := by push_cast; ring
    rw [e, Complex.norm_exp_ofReal_mul_I]

/-- Helper: the Gaussian `e^{−κ²u²/2}` as a complex-valued function. -/
def Gc (κ u : ℝ) : ℂ := (Real.exp (-(κ ^ 2 * u ^ 2) / 2) : ℂ)

/-- Helper: `uᵖ e^{−κ²u²/2}` is integrable for `p = 0, 1, 2`. -/
theorem integrable_gauss {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun u : ℝ => Real.exp (-(κ ^ 2 * u ^ 2) / 2)) ∧
      Integrable (fun u : ℝ => u * Real.exp (-(κ ^ 2 * u ^ 2) / 2)) ∧
      Integrable (fun u : ℝ => u ^ 2 * Real.exp (-(κ ^ 2 * u ^ 2) / 2)) := by
  have hb : 0 < κ ^ 2 / 2 := by positivity
  have e : ∀ u : ℝ, -(κ ^ 2 * u ^ 2) / 2 = -(κ ^ 2 / 2) * u ^ 2 := fun u => by ring
  simp only [e]
  refine ⟨integrable_exp_neg_mul_sq hb, integrable_mul_exp_neg_mul_sq hb, ?_⟩
  simpa [Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)

/-- Helper: the Fourier transform of the Gaussian, `𝓕 G(t) = (√(2π)/κ) e^{−(2π²/κ²) t²}`
(Mathlib's `fourier_gaussian_pi` with `b = κ²/(2π)`). -/
theorem fourier_Gc {κ : ℝ} (hκ : 0 < κ) :
    𝓕 (Gc κ) = fun t : ℝ => ((Real.sqrt (2 * π) / κ : ℝ) : ℂ) *
      Complex.exp (-((2 * π ^ 2 / κ ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hκc : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ.ne'
  set b : ℂ := ((κ ^ 2 / (2 * π) : ℝ) : ℂ) with hb_def
  have hb : 0 < b.re := by rw [hb_def, Complex.ofReal_re]; positivity
  have hG : Gc κ = fun x : ℝ => Complex.exp (-π * b * (x : ℂ) ^ 2) := by
    funext x
    simp only [Gc, Complex.ofReal_exp, hb_def]
    congr 1
    push_cast
    field_simp
  rw [hG, fourier_gaussian_pi hb]
  funext t
  congr 1
  · have hsq : b ^ (1 / 2 : ℂ) = ((κ / Real.sqrt (2 * π) : ℝ) : ℂ) := by
      rw [hb_def, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow (x := κ ^ 2 / (2 * π)) (by positivity) (1 / 2),
        ← Real.sqrt_eq_rpow, Real.sqrt_div (sq_nonneg κ), Real.sqrt_sq hκ.le]
    rw [hsq, Complex.ofReal_div, Complex.ofReal_div, one_div_div]
  · congr 1
    rw [hb_def]
    push_cast
    field_simp

/-- **(i) The Fourier transform of `g`.** For `κ > 0` and real `M`, `g` is integrable and
`∫ g(u) e^{−2πiuξ} du = ĝ(ξ)` for every real `ξ`. At `ξ = k/2` this is the paper's display
`∫(u² − M²/4) e^{−κ²u²/2} e^{−iπku} du = (√(2π)/κ³)(1 − π²k²/κ² − κ²M²/4) e^{−π²k²/(2κ²)}`. -/
theorem fourier_g {κ : ℝ} (hκ : 0 < κ) (M : ℝ) :
    Integrable (fun u : ℝ => g κ M u) ∧
      ∀ ξ : ℝ, ∫ u : ℝ, Complex.exp (-(2 * π * I * u * ξ)) * (g κ M u : ℂ) = (gHat κ M ξ : ℂ) := by
  obtain ⟨hR0, hR1, hR2⟩ := integrable_gauss hκ
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hκc : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ.ne'
  refine ⟨(hR2.sub (hR0.const_mul (M ^ 2 / 4))).congr
    (Eventually.of_forall fun u => by simp only [Pi.sub_apply, g]; ring), fun ξ => ?_⟩
  set C : ℂ := ((Real.sqrt (2 * π) / κ : ℝ) : ℂ) with hC
  set K : ℂ := ((2 * π ^ 2 / κ ^ 2 : ℝ) : ℂ) with hK
  -- integrability of the complex functions that enter
  have hG0 : Integrable (Gc κ) := hR0.ofReal
  have hxG0 : Integrable (fun x : ℝ => x • Gc κ x) :=
    hR1.ofReal.congr (Eventually.of_forall fun x => by simp [Gc, Complex.real_smul])
  have hG1 : Integrable (fun x : ℝ => (-2 * π * I * x) • Gc κ x) :=
    (hxG0.const_mul (-2 * π * I)).congr (Eventually.of_forall fun x => by
      simp only [smul_eq_mul, Complex.real_smul]; ring)
  have hxG1 : Integrable (fun x : ℝ => x • ((-2 * π * I * x) • Gc κ x)) :=
    (hR2.ofReal.const_mul (-2 * π * I)).congr (Eventually.of_forall fun x => by
      simp [Gc, Complex.real_smul]; ring)
  have hx2G : Integrable (fun x : ℝ => (x : ℂ) ^ 2 * Gc κ x) :=
    hR2.ofReal.congr (Eventually.of_forall fun x => by simp [Gc])
  -- the closed form `C e^{−K t²}` of `𝓕 G` and its first two derivatives
  have hp : ∀ z : ℂ, HasDerivAt (fun z : ℂ => z ^ 2) (2 * z) z := fun z => by
    simpa using hasDerivAt_pow 2 z
  have d0 : ∀ z : ℂ, HasDerivAt (fun z : ℂ => C * Complex.exp (-K * z ^ 2))
      (C * Complex.exp (-K * z ^ 2) * (-2 * K * z)) z := fun z => by
    convert ((hp z).const_mul (-K)).cexp.const_mul C using 1; ring
  have d1 : ∀ z : ℂ, HasDerivAt (fun z : ℂ => C * Complex.exp (-K * z ^ 2) * (-2 * K * z))
      (C * Complex.exp (-K * z ^ 2) * (4 * K ^ 2 * z ^ 2 - 2 * K)) z := fun z => by
    have hl : HasDerivAt (fun z : ℂ => -2 * K * z) (-2 * K) z := by
      simpa using (hasDerivAt_id z).const_mul (-2 * K)
    convert (d0 z).mul hl using 1; ring
  -- `𝓕 G`, `𝓕 ((−2πix) G)`, `𝓕 ((−2πix)² G)` by Mathlib's derivative of a Fourier transform
  have hF0 : 𝓕 (Gc κ) = fun t : ℝ => C * Complex.exp (-K * (t : ℂ) ^ 2) := fourier_Gc hκ
  have hF1 : 𝓕 (fun x : ℝ => (-2 * π * I * x) • Gc κ x) =
      fun t : ℝ => C * Complex.exp (-K * (t : ℂ) ^ 2) * (-2 * K * t) := by
    funext w
    have h := Real.hasDerivAt_fourier hG0 hxG0 w
    rw [hF0] at h
    exact h.unique (d0 w).comp_ofReal
  have hF2 : 𝓕 (fun x : ℝ => (-2 * π * I * x) • ((-2 * π * I * x) • Gc κ x)) ξ =
      C * Complex.exp (-K * (ξ : ℂ) ^ 2) * (4 * K ^ 2 * (ξ : ℂ) ^ 2 - 2 * K) := by
    have h := Real.hasDerivAt_fourier hG1 hxG1 ξ
    rw [hF1] at h
    exact h.unique (d1 ξ).comp_ofReal
  -- `(−2πix)² G = −4π² x² G`, hence `𝓕 (x² G)`
  have hG2 : (fun x : ℝ => (-2 * π * I * x) • ((-2 * π * I * x) • Gc κ x)) =
      fun x : ℝ => -(4 * (π : ℂ) ^ 2) * ((x : ℂ) ^ 2 * Gc κ x) := by
    funext x
    simp only [smul_eq_mul]
    linear_combination (4 * (π : ℂ) ^ 2 * (x : ℂ) ^ 2 * Gc κ x) * I_sq
  have hFx2 : -(4 * (π : ℂ) ^ 2) * 𝓕 (fun x : ℝ => (x : ℂ) ^ 2 * Gc κ x) ξ =
      C * Complex.exp (-K * (ξ : ℂ) ^ 2) * (4 * K ^ 2 * (ξ : ℂ) ^ 2 - 2 * K) := by
    rw [← hF2, hG2, fourier_eq_integral, fourier_eq_integral, ← integral_const_mul]
    congr 1
    funext u
    ring
  have hX : 𝓕 (fun x : ℝ => (x : ℂ) ^ 2 * Gc κ x) ξ =
      C * Complex.exp (-K * (ξ : ℂ) ^ 2) * (4 * K ^ 2 * (ξ : ℂ) ^ 2 - 2 * K) /
        (-(4 * (π : ℂ) ^ 2)) := by
    rw [eq_div_iff (neg_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ)))]
    linear_combination hFx2
  -- linearity: the paper's integral is `𝓕 (x² G) − (M²/4) 𝓕 G`
  have hlin : ∫ u : ℝ, Complex.exp (-(2 * π * I * u * ξ)) * (g κ M u : ℂ) =
      𝓕 (fun x : ℝ => (x : ℂ) ^ 2 * Gc κ x) ξ - ((M ^ 2 / 4 : ℝ) : ℂ) * 𝓕 (Gc κ) ξ := by
    rw [fourier_eq_integral, fourier_eq_integral, ← integral_const_mul,
      ← integral_sub (integrable_phase_mul hx2G ξ) ((integrable_phase_mul hG0 ξ).const_mul _)]
    congr 1
    funext u
    simp only [g, Gc]
    push_cast
    ring
  -- the closed form
  have hE : Complex.exp (-K * (ξ : ℂ) ^ 2) =
      ((Real.exp (-(2 * π ^ 2 * ξ ^ 2) / κ ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, hK]
    congr 1
    push_cast
    ring
  rw [hlin, hX, hF0]
  beta_reduce
  rw [hE]
  simp only [gHat, hC, hK]
  push_cast
  field_simp
  ring

/-! ## Helper for part (ii) (a proof device, not a statement of the paper) -/

/-- Helper: a quadratic polynomial times `e^{a y² + b y + d}`, `re a < 0`, is `O(|y|^{−2})` at
infinity (from Mathlib's `cexp_neg_quadratic_isLittleO_abs_rpow_cocompact`). -/
theorem isBigO_quad_mul_cexp (A B C : ℂ) {a : ℂ} (ha : a.re < 0) (b d : ℂ) :
    (fun y : ℝ => (A + B * y + C * (y : ℂ) ^ 2) * Complex.exp (a * (y : ℂ) ^ 2 + b * y + d))
      =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-2 : ℝ)) := by
  have e2 := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact ha b (-2)).isBigO
  have e3 := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact ha b (-3)).isBigO
  have e4 := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact ha b (-4)).isBigO
  have p1 : (fun y : ℝ => (y : ℂ)) =O[cocompact ℝ] (fun y : ℝ => |y| ^ (1 : ℝ)) :=
    isBigO_of_le _ fun y => by simp
  have p2 : (fun y : ℝ => (y : ℂ) ^ 2) =O[cocompact ℝ] (fun y : ℝ => |y| ^ (2 : ℝ)) :=
    isBigO_of_le _ fun y => by simp
  have q : ∀ s t : ℝ, s + t = -2 → s + t ≠ 0 →
      (fun y : ℝ => |y| ^ s * |y| ^ t) = fun y : ℝ => |y| ^ (-2 : ℝ) := by
    intro s t hst hne
    funext y
    rw [← Real.rpow_add' (abs_nonneg y) hne, hst]
  have t1 := p1.mul e3
  have t2 := p2.mul e4
  rw [q 1 (-3) (by norm_num) (by norm_num)] at t1
  rw [q 2 (-4) (by norm_num) (by norm_num)] at t2
  refine ((((e2.const_mul_left A).add (t1.const_mul_left B)).add
    (t2.const_mul_left C)).const_mul_left (Complex.exp d)).congr_left fun y => ?_
  rw [Complex.exp_add (a * (y : ℂ) ^ 2 + b * y) d]
  ring

/-- **(ii) Poisson summation on the coset `c + 2ℤ`.** For `κ > 0` and real `M`, `c`:
`Σ_{u ∈ c+2ℤ} g(u) = ½ Σ_{k ∈ ℤ} ĝ(k/2) e^{iπkc}`, both series summable. -/
theorem coset_poisson {κ : ℝ} (hκ : 0 < κ) (M c : ℝ) :
    Summable (fun t : ℤ => g κ M (c + 2 * t)) ∧
      Summable (fun k : ℤ => (gHat κ M (k / 2) : ℂ) * Complex.exp (π * I * k * c)) ∧
      ((∑' t : ℤ, g κ M (c + 2 * t) : ℝ) : ℂ) =
        1 / 2 * ∑' k : ℤ, (gHat κ M (k / 2) : ℂ) * Complex.exp (π * I * k * c) := by
  have hFT := (fourier_g hκ M).2
  have hre : ∀ r : ℝ, 0 < r → (((-r : ℝ) : ℂ)).re < 0 := fun r hr => by
    rw [Complex.ofReal_re]; linarith
  -- `h(y) = g(2y)`, to which Mathlib's Poisson summation is applied at the shift `c/2`
  set h : ℝ → ℂ := fun y => (g κ M (2 * y) : ℂ) with hh
  have hcont : Continuous h := by simp only [hh, g]; fun_prop
  -- its Fourier transform, by the change of variables `u = 2y` and part (i)
  have hFh : ∀ ξ : ℝ, 𝓕 h ξ = (1 / 2 : ℂ) * (gHat κ M (ξ / 2) : ℂ) := by
    intro ξ
    have hcv := Measure.integral_comp_mul_left
      (fun v : ℝ => Complex.exp (-(2 * π * I * v * ((ξ / 2 : ℝ) : ℂ))) * (g κ M v : ℂ)) 2
    beta_reduce at hcv
    rw [hFT (ξ / 2)] at hcv
    rw [fourier_eq_integral]
    have e : ∀ u : ℝ, Complex.exp (-(2 * π * I * u * ξ)) * h u =
        Complex.exp (-(2 * π * I * ((2 * u : ℝ) : ℂ) * ((ξ / 2 : ℝ) : ℂ))) *
          (g κ M (2 * u) : ℂ) := by
      intro u
      simp only [hh]
      congr 2
      push_cast
      ring
    simp only [e]
    rw [hcv, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), Complex.real_smul]
    push_cast
    ring
  -- decay of `h`, of `𝓕 h` and of `y ↦ g(c + 2y)`, each `O(|y|^{−2})`
  have hdec : h =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-2 : ℝ)) := by
    refine (isBigO_quad_mul_cexp ((-(M ^ 2 / 4) : ℝ) : ℂ) 0 4
      (hre (2 * κ ^ 2) (by positivity)) 0 0).congr_left fun y => ?_
    simp only [hh, g]
    push_cast
    ring_nf
  have hFdec : 𝓕 h =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-2 : ℝ)) := by
    rw [show 𝓕 h = fun ξ : ℝ => (1 / 2 : ℂ) * (gHat κ M (ξ / 2) : ℂ) from funext hFh]
    refine (isBigO_quad_mul_cexp
      ((Real.sqrt (2 * π) / κ ^ 3 * (1 - κ ^ 2 * M ^ 2 / 4) / 2 : ℝ) : ℂ) 0
      ((-(Real.sqrt (2 * π) / κ ^ 3 * (π ^ 2 / κ ^ 2) / 2) : ℝ) : ℂ)
      (hre (π ^ 2 / (2 * κ ^ 2)) (by positivity)) 0 0).congr_left fun ξ => ?_
    simp only [gHat]
    push_cast
    ring_nf
  have hHdec : (fun y : ℝ => (g κ M (c + 2 * y) : ℂ)) =O[cocompact ℝ]
      (fun y : ℝ => |y| ^ (-2 : ℝ)) := by
    refine (isBigO_quad_mul_cexp ((c ^ 2 - M ^ 2 / 4 : ℝ) : ℂ) ((4 * c : ℝ) : ℂ) 4
      (hre (2 * κ ^ 2) (by positivity)) ((-(2 * κ ^ 2 * c) : ℝ) : ℂ)
      ((-(κ ^ 2 * c ^ 2) / 2 : ℝ) : ℂ)).congr_left fun y => ?_
    simp only [g]
    push_cast
    ring_nf
  -- summability of both sides
  have hFsumN : Summable (fun n : ℤ => ‖𝓕 h n‖) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hFdec.norm_left.comp_tendsto Int.tendsto_coe_cofinite)
  have hHsum : Summable (fun t : ℤ => (g κ M (c + 2 * t) : ℂ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hHdec.comp_tendsto Int.tendsto_coe_cofinite)
  have hphase : ∀ k : ℤ, ‖Complex.exp (π * I * k * c)‖ = 1 := fun k => by
    rw [show (π * I * k * c : ℂ) = ((π * k * c : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hRsum : Summable (fun k : ℤ => (gHat κ M (k / 2) : ℂ) * Complex.exp (π * I * k * c)) := by
    refine Summable.of_norm ((hFsumN.mul_left 2).congr fun k => ?_)
    rw [norm_mul, hphase, mul_one, hFh, norm_mul]
    norm_num
    ring
  refine ⟨Complex.summable_ofReal.mp hHsum, hRsum, ?_⟩
  -- the identity: Mathlib's Poisson summation for `h` at the shift `c/2`
  rw [Complex.ofReal_tsum]
  calc ∑' t : ℤ, (g κ M (c + 2 * t) : ℂ) = ∑' t : ℤ, h (c / 2 + t) := by
        congr 1
        funext t
        simp only [hh]
        congr 2
        ring
    _ = ∑' n : ℤ, 𝓕 h n * fourier n ((c / 2 : ℝ) : UnitAddCircle) :=
        Real.tsum_eq_tsum_fourier_of_rpow_decay hcont one_lt_two hdec hFdec (c / 2)
    _ = ∑' n : ℤ, (1 / 2 : ℂ) * ((gHat κ M (n / 2) : ℂ) * Complex.exp (π * I * n * c)) := by
        congr 1
        funext n
        rw [hFh, fourier_coe_apply]
        push_cast
        ring_nf
    _ = 1 / 2 * ∑' k : ℤ, (gHat κ M (k / 2) : ℂ) * Complex.exp (π * I * k * c) :=
        tsum_mul_left

/-! ## Part (iii): the paper's `S_j` -/

/-- `c₀ = κ³/√(2π)` (Proposition `orbital`). -/
def c0 (κ : ℝ) : ℝ := κ ^ 3 / Real.sqrt (2 * π)

/-- `f(d) = d e^{−κ²d²/4}` (Proposition `orbital`). -/
def f (κ d : ℝ) : ℝ := d * Real.exp (-(κ ^ 2 * d ^ 2) / 4)

/-- `𝔣(s) = (1 − s) e^{−s/2}` (Section 4.1). -/
def frakf (s : ℝ) : ℝ := (1 - s) * Real.exp (-s / 2)

/-- `s_{jk} = ¼ (j² L_x² + k² L_y²)` (Section 4.1). -/
def sjk (Lx Ly : ℝ) (j k : ℤ) : ℝ := ((j : ℝ) ^ 2 * Lx ^ 2 + (k : ℝ) ^ 2 * Ly ^ 2) / 4

/-- Helper (a proof device): `f(d) f(d + M) = g(d + M/2) e^{−κ²M²/8}`, the change of variables
`u = d + M/2` of the proof of Lemma 4.1. -/
theorem f_mul_f (κ d M : ℝ) :
    f κ d * f κ (d + M) = g κ M (d + M / 2) * Real.exp (-(κ ^ 2 * M ^ 2) / 8) := by
  have e : Real.exp (-(κ ^ 2 * d ^ 2) / 4) * Real.exp (-(κ ^ 2 * (d + M) ^ 2) / 4) =
      Real.exp (-(κ ^ 2 * (d + M / 2) ^ 2) / 2) * Real.exp (-(κ ^ 2 * M ^ 2) / 8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [f, g]
  calc d * Real.exp (-(κ ^ 2 * d ^ 2) / 4) * ((d + M) * Real.exp (-(κ ^ 2 * (d + M) ^ 2) / 4))
      = d * (d + M) * (Real.exp (-(κ ^ 2 * d ^ 2) / 4) *
          Real.exp (-(κ ^ 2 * (d + M) ^ 2) / 4)) := by ring
    _ = ((d + M / 2) ^ 2 - M ^ 2 / 4) * Real.exp (-(κ ^ 2 * (d + M / 2) ^ 2) / 2) *
          Real.exp (-(κ ^ 2 * M ^ 2) / 8) := by rw [e]; ring

/-- **(iii) The closed form of `S_j`.** On the torus of Definition 2.1 (`N_φ ∈ ℕ`, `L_x, L_y > 0`,
`L_x L_y = 2πN_φ`, `κ = 2π/L_y`), for integers `n`, `j`:
`S_j := 2c₀ Σ_{d ≡ n (2)} f(d) f(d + jN_φ) = Σ_{k ∈ ℤ} e^{iπk(n + jN_φ/2)} 𝔣(s_{jk})`,
both series summable. -/
theorem S_closed_form (Nφ : ℕ) {Lx Ly κ : ℝ} (hLx : 0 < Lx) (hLy : 0 < Ly)
    (harea : Lx * Ly = 2 * π * Nφ) (hκ : κ = 2 * π / Ly) (n j : ℤ) :
    Summable (fun t : ℤ => f κ (n + 2 * t) * f κ (n + 2 * t + j * Nφ)) ∧
      Summable (fun k : ℤ =>
        Complex.exp (π * I * k * (n + j * Nφ / 2)) * (frakf (sjk Lx Ly j k) : ℂ)) ∧
      ((2 * c0 κ * ∑' t : ℤ, f κ (n + 2 * t) * f κ (n + 2 * t + j * Nφ) : ℝ) : ℂ) =
        ∑' k : ℤ, Complex.exp (π * I * k * (n + j * Nφ / 2)) * (frakf (sjk Lx Ly j k) : ℂ) := by
  -- the torus data of Definition 2.1
  have hLy0 : Ly ≠ 0 := hLy.ne'
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hκ0 : κ ≠ 0 := hκpos.ne'
  have hLy' : Ly = 2 * π / κ := by rw [hκ]; field_simp
  have hLx' : Lx = κ * Nφ := by rw [hκ]; field_simp; linear_combination harea
  have hsq : Real.sqrt (2 * π) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  -- `M = jN_φ`, `c = n + M/2`, and part (ii)
  set M : ℝ := (j : ℝ) * Nφ with hM
  set c : ℝ := (n : ℝ) + M / 2 with hc
  obtain ⟨hsumL, hsumR, hEq⟩ := coset_poisson hκpos M c
  set E : ℝ := Real.exp (-(κ ^ 2 * M ^ 2) / 8) with hE
  have key : ∀ t : ℤ, f κ (n + 2 * t) * f κ (n + 2 * t + M) = g κ M (c + 2 * t) * E := by
    intro t
    rw [f_mul_f, hE, hc]
    congr 2
    ring
  have hconst : ∀ k : ℤ, c0 κ * E * gHat κ M (k / 2) = frakf (sjk Lx Ly j k) := by
    intro k
    rw [hLx', hLy']
    simp only [hE, hM, c0, gHat, frakf, sjk]
    rw [show ∀ a b P X Y : ℝ, a * X * (b * P * Y) = a * b * P * (X * Y) from
      fun a b P X Y => by ring, ← Real.exp_add]
    congr 1
    · field_simp
      ring
    · congr 1
      field_simp
      ring
  refine ⟨(hsumL.mul_right E).congr fun t => (key t).symm, ?_, ?_⟩
  · refine (hsumR.mul_left ((c0 κ * E : ℝ) : ℂ)).congr fun k => ?_
    rw [← hconst k, hc, hM]
    push_cast
    ring_nf
  · calc ((2 * c0 κ * ∑' t : ℤ, f κ (n + 2 * t) * f κ (n + 2 * t + M) : ℝ) : ℂ)
        = ((2 * c0 κ * E : ℝ) : ℂ) * ((∑' t : ℤ, g κ M (c + 2 * t) : ℝ) : ℂ) := by
          rw [tsum_congr key, tsum_mul_right]
          push_cast
          ring
      _ = ((2 * c0 κ * E : ℝ) : ℂ) *
            (1 / 2 * ∑' k : ℤ, (gHat κ M (k / 2) : ℂ) * Complex.exp (π * I * k * c)) := by
          rw [hEq]
      _ = ∑' k : ℤ, ((c0 κ * E : ℝ) : ℂ) *
            ((gHat κ M (k / 2) : ℂ) * Complex.exp (π * I * k * c)) := by
          rw [tsum_mul_left]
          push_cast
          ring
      _ = ∑' k : ℤ, Complex.exp (π * I * k * (n + j * Nφ / 2)) * (frakf (sjk Lx Ly j k) : ℂ) := by
          congr 1
          funext k
          rw [← hconst k, hc, hM]
          push_cast
          ring_nf

end HRTorus.Laughlin.GramPoisson

#check @HRTorus.Laughlin.GramPoisson.fourier_g
#check @HRTorus.Laughlin.GramPoisson.coset_poisson
#check @HRTorus.Laughlin.GramPoisson.S_closed_form
#print HRTorus.Laughlin.GramPoisson.g
#print HRTorus.Laughlin.GramPoisson.gHat
#print HRTorus.Laughlin.GramPoisson.c0
#print HRTorus.Laughlin.GramPoisson.f
#print HRTorus.Laughlin.GramPoisson.frakf
#print HRTorus.Laughlin.GramPoisson.sjk
