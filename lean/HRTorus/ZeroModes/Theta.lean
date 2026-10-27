import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Theta functions and the elliptic functions of Appendix C (`ZeroModes.Theta`)

Written by Claude Opus 5.5 (an AI model), 2026-10-26. **The definitions and statements were written first
and reviewed against the paper (the statement phase). The proof phase is complete: every reviewed statement of this
module is proved (proof phase round one), no theorem of this module is `sorry`, and the proof devices are
marked as such, in their own sections.** The definitions
`thetaChar`, `theta1`, `thetaSpace`, `periodPairReal` and the Osgood class are those of the stage-F scouting pilot
(a scratch project outside this repository), whose proofs of the corresponding statements were reused in the proof
phase as devices, with attribution.
The paper: the HR paper, `papers/hr/appendices/C-kernel.tex` — the theta functions of `kz:eq:orbital`, the relations
`kz:eq:theta-basic`, Lemma C.`theta` (a), (c)–(f) (`kz:lem:theta`), and from Lemma C.`B`(b) the spaces `Θ_2[ε]`.

## The model

* **`u`-units, general `τ`.** "`$\Lambda_u:=\Z+\tau\Z$`": everything here is in the appendix's `u`-units, for any `τ` in
  the upper half-plane (Mathlib's `UpperHalfPlane`, `ℍ`); the rectangular torus enters only in `ZeroModes.Canonical`.
  `Λu τ` is the set `{p + qτ : p, q ∈ ℤ}`.
* **`ϑ[a,b]`** is F0's change of variables of Mathlib's `jacobiTheta₂` (completing the square), with the paper's
  series as a theorem (`hasSum_thetaChar`); `ϑ₁ := ϑ[½,½]` (`theta1`).
* **`Θ_ℓ[a,b]`** (`thetaSpace`, F0's) and **`Θ_2[ε]`** (`Θ2`, for `ε ∈ {±1}²`, the only multipliers the explicit
  states use) are submodules of `ℂ → ℂ`.
* **`ε ∈ {±1}²`** is the type `Eps` with four elements (`pp, mp, pm, mm` for `(1,1), (−1,1), (1,−1), (−1,−1)`) and
  the components `Eps.e1`, `Eps.e2 ∈ ℂ`.
* **`℘`** is Mathlib's `PeriodPair.weierstrassP` of the period pair `(1, τ)` (`wp`), **not** the paper's
  `℘ := −(log ϑ₁)''`, which differs from it by an additive constant; Lemma C.`theta`(d) is stated in the form Mathlib
  gives (`℘ − u⁻²` analytic at `0`, order `−2` at the lattice points, analytic off the lattice, even, periodic). Where
  the additive constant could matter, `ZeroModes.Explicit` says why it does not.
* **`℘_ε`** (`wpE τ ε`) is the paper's construction from the index-two sublattice `Λ_ε = ker χ_ε` with Mathlib's `℘`
  of `Λ_ε`: `Λ_ε` is `2ℤ + τℤ`, `ℤ + 2τℤ`, `2ℤ + (1+τ)ℤ` for `ε = (−1,1), (1,−1), (−1,−1)`, with `λ_ε = 1, τ, 1`;
  `wpE τ pp := wp τ` ("`Write $\wp_{(1,1)}:=\wp$.`").
* **The Osgood class** `IsOsgood f` on `ι → ℂ`: `f` continuous and entire in each variable separately (F0's
  `IsOsgood2` on `ℂ × ℂ`, generalized); it is the carrier of "entire on `ℂ^N`" in this block — no meromorphic function
  of several variables is ever defined.
* **`J := ∏_{i<j} ϑ₁(u_i − u_j)`** on `Fin N → ℂ` (`Jfun`); "vanishing of order at least two along the divisors" is
  stated as divisibility of `J²` by `ϑ₁(u_i − u_j)²` in the Osgood class (the "exactly" and "nowhere else" of
  Lemma C.`theta`(f) are block F1-upper's).
-/

open Complex
open scoped Real UpperHalfPlane

noncomputable section

namespace HRTorus.ZeroModes

/-! ### Proof devices for Lemma C.theta(a) (proof phase, round one; not statements of the paper)

The theta-space machinery of the stage-F scouting pilot (its `ThetaSpace.lean`, outside this repository), copied
verbatim but for one name: its copy of `thetaSpace` is `thetaSpaceDev` here (the reviewed `thetaSpace` below is defined
after `ϑ₁`, whose zero set these devices serve). The coefficients `c_n` are integrals over `[0, 1]`, independent of the
height by Cauchy's theorem on a rectangle; all coefficients zero gives `F = 0` by Fourier series on each horizontal line;
the existence half is an explicit basis from Mathlib's `jacobiTheta₂`. -/

namespace ThetaDev

section ThetaSpaceDevices

open MeasureTheory intervalIntegral

/-- The theta space `Θ_ℓ[a,b]` of Lemma C.`theta`(a), as a submodule of `ℂ → ℂ`. -/
def thetaSpaceDev (τ : ℂ) (a b : ℝ) (ℓ : ℕ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {F | Differentiable ℂ F ∧ (∀ U, F (U + 1) = cexp (2 * π * I * a) * F U) ∧
      ∀ U, F (U + τ) = cexp (-2 * π * I * b) * cexp (-π * I * ℓ * (2 * U + τ)) * F U}
  add_mem' := by
    rintro F G ⟨hF, hF1, hF2⟩ ⟨hG, hG1, hG2⟩
    refine ⟨hF.add hG, fun U => ?_, fun U => ?_⟩
    · simp only [Pi.add_apply, hF1, hG1]; ring
    · simp only [Pi.add_apply, hF2, hG2]; ring
  zero_mem' := ⟨differentiable_const 0, fun U => by simp, fun U => by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, hF1, hF2⟩
    refine ⟨hF.const_smul c, fun U => ?_, fun U => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hF1]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, hF2]; ring

/-! ## Cauchy on a rectangle: the integral over a unit segment of an entire `1`-periodic function -/

/-- For an entire `1`-periodic `H`, `∫_0^1 H(t + w) dt` does not depend on `w`. -/
theorem integral_unit_shift {H : ℂ → ℂ} (hH : Differentiable ℂ H) (hper : ∀ U, H (U + 1) = H U)
    (w : ℂ) : ∫ t in (0:ℝ)..1, H (t + w) = ∫ t in (0:ℝ)..1, H t := by
  have hg : Function.Periodic (fun s : ℝ => H (s + w.im * I)) 1 := by
    intro s
    simp only
    rw [show ((s + 1 : ℝ) : ℂ) + w.im * I = (s + w.im * I) + 1 by push_cast; ring, hper]
  have h1 : ∫ t in (0:ℝ)..1, H (t + w) = ∫ s in (0:ℝ)..1, H (s + w.im * I) := by
    have e : ∀ t : ℝ, H (t + w) = (fun s : ℝ => H (s + w.im * I)) (t + w.re) := by
      intro t
      simp only
      congr 1
      conv_lhs => rw [← Complex.re_add_im w]
      push_cast; ring
    simp_rw [e]
    rw [intervalIntegral.integral_comp_add_right (fun s : ℝ => H (s + w.im * I)) w.re, zero_add,
      show (1 : ℝ) + w.re = w.re + 1 by ring, hg.intervalIntegral_add_eq w.re 0, zero_add]
  have h2 := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H 0 ⟨1, w.im⟩
    hH.differentiableOn
  have hv : (∫ y : ℝ in (0 : ℂ).im..(⟨1, w.im⟩ : ℂ).im, H ((⟨1, w.im⟩ : ℂ).re + y * I)) =
      ∫ y : ℝ in (0 : ℂ).im..(⟨1, w.im⟩ : ℂ).im, H ((0 : ℂ).re + y * I) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [Complex.zero_re, Complex.ofReal_zero, zero_add, Complex.ofReal_one]
    rw [add_comm, hper]
  rw [hv, add_sub_cancel_right, sub_eq_zero] at h2
  rw [h1]
  simpa using h2.symm

/-! ## The coefficients and the recursion -/

/-- The coefficient `c_n(F) = ∫_0^1 F(t) e^{−2πi(n+a)t} dt`. -/
def coef (a : ℝ) (F : ℂ → ℂ) (n : ℤ) : ℂ :=
  ∫ t in (0:ℝ)..1, F t * cexp (-2 * π * I * (n + a) * t)

theorem exp_mul_mul_exp (A B C : ℂ) : cexp A * C * cexp B = C * cexp (A + B) := by
  rw [Complex.exp_add]; ring

theorem coef_shift {τ : ℂ} {a b : ℝ} {ℓ : ℕ} {F : ℂ → ℂ} (hF : F ∈ thetaSpaceDev τ a b ℓ) (n : ℤ)
    (w : ℂ) : ∫ t in (0:ℝ)..1, F (t + w) * cexp (-2 * π * I * (n + a) * (t + w)) = coef a F n := by
  have hd : Differentiable ℂ (fun U => F U * cexp (-2 * π * I * (n + a) * U)) :=
    hF.1.mul (by fun_prop)
  have hp : ∀ U, (fun U => F U * cexp (-2 * π * I * (n + a) * U)) (U + 1) =
      (fun U => F U * cexp (-2 * π * I * (n + a) * U)) U := by
    intro U
    simp only [hF.2.1 U, exp_mul_mul_exp]
    rw [show 2 * π * I * a + -2 * π * I * (n + a) * (U + 1) =
        -2 * π * I * (n + a) * U + ((-n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  exact integral_unit_shift hd hp w

/-- The recursion `c_n = e^{−2πib − iπℓτ − 2πi(n+a)τ} c_{n+ℓ}` (the paper's, inverted). -/
theorem coef_rec {τ : ℂ} {a b : ℝ} {ℓ : ℕ} {F : ℂ → ℂ} (hF : F ∈ thetaSpaceDev τ a b ℓ) (n : ℤ) :
    coef a F n = cexp (-2 * π * I * b - π * I * ℓ * τ - 2 * π * I * (n + a) * τ) *
      coef a F (n + ℓ) := by
  rw [← coef_shift hF n τ]
  unfold coef
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hF.2.2]
  rw [show ∀ A B C D : ℂ, cexp A * cexp B * C * cexp D = C * cexp (A + B + D) from
      fun A B C D => by rw [Complex.exp_add, Complex.exp_add]; ring,
    show ∀ A B C : ℂ, cexp A * (C * cexp B) = C * cexp (A + B) from
      fun A B C => by rw [Complex.exp_add]; ring]
  congr 2
  push_cast
  ring

theorem coef_eq_zero_of_low {τ : ℂ} {a b : ℝ} {ℓ : ℕ} (hℓ : 0 < ℓ) {F : ℂ → ℂ}
    (hF : F ∈ thetaSpaceDev τ a b ℓ) (h0 : ∀ r : ℕ, r < ℓ → coef a F r = 0) (n : ℤ) :
    coef a F n = 0 := by
  have key : ∀ (r : ℤ) (k : ℤ), coef a F r = 0 → coef a F (r + k * ℓ) = 0 := by
    intro r k hr
    induction k using Int.induction_on with
    | zero => simpa using hr
    | succ i ih =>
      have := coef_rec hF (r + i * ℓ)
      rw [ih] at this
      rw [show r + ((i : ℤ) + 1) * ℓ = r + i * ℓ + ℓ by ring]
      exact (mul_eq_zero.mp this.symm).resolve_left (Complex.exp_ne_zero _)
    | pred i ih =>
      have := coef_rec hF (r + (-(i : ℤ) - 1) * ℓ)
      rw [show r + (-(i : ℤ) - 1) * ℓ + ℓ = r + -(i : ℤ) * ℓ by ring, ih, mul_zero] at this
      exact this
  have hn : n = (n % ℓ) + (n / ℓ) * ℓ := (Int.emod_add_ediv_mul n ℓ).symm
  rw [hn]
  apply key
  have h1 : 0 ≤ n % ℓ := Int.emod_nonneg n (by exact_mod_cast hℓ.ne')
  have h2 : n % ℓ < ℓ := Int.emod_lt_of_pos n (by exact_mod_cast hℓ)
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le h1
  rw [hr]
  exact h0 r (by omega)

/-! ## All coefficients zero ⇒ `F = 0` (Fourier series on each horizontal line) -/

theorem eq_zero_of_coef_eq_zero {τ : ℂ} {a b : ℝ} {ℓ : ℕ} {F : ℂ → ℂ}
    (hF : F ∈ thetaSpaceDev τ a b ℓ) (h : ∀ n : ℤ, coef a F n = 0) : F = 0 := by
  have : Fact ((0:ℝ) < 1) := ⟨one_pos⟩
  funext U
  set y := U.im with hy
  let g : ℝ → ℂ := fun t => F (t + y * I) * cexp (-2 * π * I * a * (t + y * I))
  have hgper : Function.Periodic g 1 := by
    intro t
    simp only [g]
    rw [show ((t + 1 : ℝ) : ℂ) + y * I = (t + y * I) + 1 by push_cast; ring, hF.2.1,
      exp_mul_mul_exp]
    congr 2
    ring
  have hgc : Continuous g := by
    have := hF.1.continuous
    fun_prop
  let G : C(AddCircle (1:ℝ), ℂ) := ⟨hgper.lift, continuous_coinduced_dom.mpr hgc⟩
  have hG : ∀ t : ℝ, G (t : AddCircle (1:ℝ)) = g t := fun t => rfl
  have hcoef : ∀ n : ℤ, fourierCoeff G n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral G n 0]
    have e : ∫ x in (0:ℝ)..0 + 1, fourier (-n) (x : AddCircle (1:ℝ)) • G x =
        cexp (-2 * π * n * y) * coef a F n := by
      rw [← coef_shift hF n (y * I), ← intervalIntegral.integral_const_mul, zero_add]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hG, g, fourier_coe_apply, smul_eq_mul]
      rw [show ∀ A B C : ℂ, cexp A * (C * cexp B) = C * cexp (A + B) from
          fun A B C => by rw [Complex.exp_add]; ring,
        show ∀ A B C : ℂ, cexp A * (C * cexp B) = C * cexp (A + B) from
          fun A B C => by rw [Complex.exp_add]; ring]
      congr 2
      push_cast
      linear_combination (2 * (π : ℂ) * n * y) * Complex.I_sq
    rw [e, h n, mul_zero, smul_zero]
  have hs : Summable (fourierCoeff G) := by
    have : fourierCoeff G = 0 := funext hcoef
    rw [this]; exact summable_zero
  have hsum := has_pointwise_sum_fourier_series_of_summable hs (U.re : AddCircle (1:ℝ))
  simp only [hcoef, zero_smul] at hsum
  have hG0 : G (U.re : AddCircle (1:ℝ)) = 0 := (hasSum_zero.unique hsum).symm
  rw [hG] at hG0
  simp only [g] at hG0
  rw [hy, Complex.re_add_im] at hG0
  exact (mul_eq_zero.mp hG0).resolve_right (Complex.exp_ne_zero _)

/-- **The injectivity half of Lemma C.`theta`(a)**: `c_0 = ⋯ = c_{ℓ−1} = 0 ⇒ F = 0`. -/
theorem eq_zero_of_low_coef {τ : ℂ} {a b : ℝ} {ℓ : ℕ} (hℓ : 0 < ℓ) {F : ℂ → ℂ}
    (hF : F ∈ thetaSpaceDev τ a b ℓ) (h0 : ∀ r : ℕ, r < ℓ → coef a F r = 0) : F = 0 :=
  eq_zero_of_coef_eq_zero hF (coef_eq_zero_of_low hℓ hF h0)

/-! ## The existence half: an explicit basis from Mathlib's `jacobiTheta₂` -/

theorem jacobiTheta₂_add_nat (z τ : ℂ) (k : ℕ) : jacobiTheta₂ (z + k) τ = jacobiTheta₂ z τ := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, ← add_assoc, jacobiTheta₂_add_left, ih]

/-- The basis element `F_r(U) = e^{2πi(r+a)U} ϑ(ℓU + b + (r+a)τ | ℓτ)` (Mathlib's `jacobiTheta₂`), whose
coefficients are `c_s = δ_{rs}` for `0 ≤ r, s < ℓ`. -/
def thetaBasis (τ : ℂ) (a b : ℝ) (ℓ r : ℕ) (U : ℂ) : ℂ :=
  cexp (2 * π * I * (r + a) * U) * jacobiTheta₂ (ℓ * U + b + (r + a) * τ) (ℓ * τ)

theorem im_natCast_mul_pos {τ : ℂ} (hτ : 0 < τ.im) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    0 < ((ℓ : ℂ) * τ).im := by
  rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  exact mul_pos (by exact_mod_cast hℓ) hτ

theorem thetaBasis_mem {τ : ℂ} (hτ : 0 < τ.im) (a b : ℝ) {ℓ : ℕ} (hℓ : 0 < ℓ) (r : ℕ) :
    thetaBasis τ a b ℓ r ∈ thetaSpaceDev τ a b ℓ := by
  have hτ' := im_natCast_mul_pos hτ hℓ
  refine ⟨fun U => ?_, fun U => ?_, fun U => ?_⟩
  · unfold thetaBasis
    refine DifferentiableAt.mul (by fun_prop) ?_
    have h1 : DifferentiableAt ℂ (fun U : ℂ => (ℓ : ℂ) * U + b + (r + a) * τ) U := by fun_prop
    exact (differentiableAt_jacobiTheta₂_fst _ hτ').comp U h1
  · unfold thetaBasis
    rw [show (ℓ : ℂ) * (U + 1) + b + (r + a) * τ = ((ℓ : ℂ) * U + b + (r + a) * τ) + (ℓ : ℕ) by ring,
      jacobiTheta₂_add_nat,
      show 2 * π * I * (r + a) * (U + 1) =
        2 * π * I * (r + a) * U + 2 * π * I * a + ((r : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
    ring
  · unfold thetaBasis
    rw [show (ℓ : ℂ) * (U + τ) + b + (r + a) * τ = ((ℓ : ℂ) * U + b + (r + a) * τ) + ℓ * τ by ring,
      jacobiTheta₂_add_left',
      show ∀ A B C : ℂ, cexp A * (cexp B * C) = C * cexp (A + B) from
        fun A B C => by rw [Complex.exp_add]; ring,
      show ∀ A B C D : ℂ, cexp A * cexp B * (cexp C * D) = D * cexp (A + B + C) from
        fun A B C D => by rw [Complex.exp_add, Complex.exp_add]; ring]
    congr 2
    ring

theorem intervalIntegral_exp_int (A : ℂ) (m : ℤ) :
    ∫ x in (0:ℝ)..1, A * cexp ((2 * π * I * m) * x) = if m = 0 then A else 0 := by
  rw [intervalIntegral.integral_const_mul]
  split_ifs with hm
  · subst hm; simp
  · have hc : (2 * π * I * m : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero, hm]
    rw [integral_exp_mul_complex hc]
    rw [show (2 * π * I * m : ℂ) * ((1:ℝ) : ℂ) = (m : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
    simp

theorem coef_thetaBasis {τ : ℂ} (hτ : 0 < τ.im) (a b : ℝ) {ℓ : ℕ} (hℓ : 0 < ℓ) {r s : ℕ}
    (hr : r < ℓ) (hs : s < ℓ) :
    coef a (thetaBasis τ a b ℓ r) s = if r = s then 1 else 0 := by
  have hτ' := im_natCast_mul_pos hτ hℓ
  set c : ℂ := b + (r + a) * τ with hc
  let m : ℤ → ℤ := fun k => k * ℓ + r - s
  let f : ℤ → C(ℝ, ℂ) := fun k =>
    ⟨fun t => jacobiTheta₂_term k c (ℓ * τ) * cexp ((2 * π * I * (m k : ℂ)) * t), by fun_prop⟩
  have hpt : ∀ t : ℝ, thetaBasis τ a b ℓ r t * cexp (-2 * π * I * ((s : ℤ) + a) * t) =
      ∑' k : ℤ, f k t := by
    intro t
    unfold thetaBasis jacobiTheta₂
    rw [← tsum_mul_left, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    simp only [f, m, ContinuousMap.coe_mk, jacobiTheta₂_term]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, hc]
    congr 1
    push_cast
    ring
  set S : ℝ := |c.im|
  set T : ℝ := ((ℓ : ℂ) * τ).im
  have hbound : ∀ k : ℤ, ‖(f k).restrict
      (⟨Set.uIcc 0 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ ≤
      Real.exp (-π * (T * k ^ 2 - 2 * S * |k|)) := by
    intro k
    refine (ContinuousMap.norm_le _ (Real.exp_pos _).le).mpr fun x => ?_
    simp only [ContinuousMap.restrict_apply, f, ContinuousMap.coe_mk, norm_mul]
    have h1 : ‖cexp ((2 * π * I * (m k : ℂ)) * (x : ℝ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [h1, mul_one]
    have hcz : |(c + 0).im| ≤ S := by simp [S]
    simpa using norm_jacobiTheta₂_term_le hτ' (le_refl S) (le_refl T) k
  have hsum : Summable fun k : ℤ => ‖(f k).restrict
      (⟨Set.uIcc 0 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
      (by simpa using summable_pow_mul_jacobiTheta₂_term_bound S hτ' 0)
  have hhas := intervalIntegral.hasSum_intervalIntegral_of_summable_norm (a := 0) (b := 1) hsum
  have e : ∫ x in (0:ℝ)..1, ∑' k, f k x = coef a (thetaBasis τ a b ℓ r) s := by
    unfold coef
    exact intervalIntegral.integral_congr fun t _ => (hpt t).symm
  rw [e] at hhas
  have hm : ∀ k : ℤ, m k = 0 ↔ k = 0 ∧ r = s := by
    intro k
    simp only [m]
    constructor
    · intro h
      have hk : k = 0 := by
        by_contra hk
        rcases lt_or_gt_of_ne hk with hk | hk
        · have : k * (ℓ : ℤ) ≤ -(ℓ : ℤ) := by nlinarith
          omega
        · have : (ℓ : ℤ) ≤ k * (ℓ : ℤ) := by nlinarith
          omega
      subst hk
      exact ⟨rfl, by omega⟩
    · rintro ⟨rfl, rfl⟩; simp
  have hint : ∀ k : ℤ, ∫ x in (0:ℝ)..1, f k x = if k = 0 then (if r = s then 1 else 0) else 0 := by
    intro k
    simp only [f, ContinuousMap.coe_mk]
    rw [intervalIntegral_exp_int]
    by_cases hk : k = 0
    · subst hk
      by_cases hrs : r = s
      · subst hrs; simp [m, jacobiTheta₂_term]
      · have : m 0 ≠ 0 := fun h => hrs ((hm 0).mp h).2
        simp [this, hrs]
    · have : m k ≠ 0 := fun h => hk ((hm k).mp h).1
      simp [this, hk]
  have hfun : (fun k : ℤ => ∫ x in (0:ℝ)..1, f k x) =
      fun k => if k = 0 then (if r = s then (1 : ℂ) else 0) else 0 := funext hint
  rw [hfun] at hhas
  exact hhas.unique (hasSum_ite_eq 0 _)

/-! ## The dimension -/

theorem coef_add {τ : ℂ} {a b : ℝ} {ℓ : ℕ} {F G : ℂ → ℂ} (hF : F ∈ thetaSpaceDev τ a b ℓ)
    (hG : G ∈ thetaSpaceDev τ a b ℓ) (n : ℤ) : coef a (F + G) n = coef a F n + coef a G n := by
  unfold coef
  have i1 : IntervalIntegrable (fun t : ℝ => F t * cexp (-2 * π * I * (n + a) * t)) volume 0 1 :=
    ((hF.1.continuous.comp continuous_ofReal).mul (by fun_prop)).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun t : ℝ => G t * cexp (-2 * π * I * (n + a) * t)) volume 0 1 :=
    ((hG.1.continuous.comp continuous_ofReal).mul (by fun_prop)).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_add i1 i2]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Pi.add_apply]
  ring

theorem coef_smul (a : ℝ) (c : ℂ) (F : ℂ → ℂ) (n : ℤ) : coef a (c • F) n = c * coef a F n := by
  unfold coef
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The coefficient map `Θ_ℓ[a,b] → ℂ^ℓ`, `F ↦ (c_0, …, c_{ℓ−1})`. -/
def coefMap (τ : ℂ) (a b : ℝ) (ℓ : ℕ) : thetaSpaceDev τ a b ℓ →ₗ[ℂ] (Fin ℓ → ℂ) where
  toFun F := fun r => coef a F ((r : ℕ) : ℤ)
  map_add' F G := by
    funext r
    simp only [Submodule.coe_add, Pi.add_apply]
    exact coef_add F.2 G.2 _
  map_smul' c F := by
    funext r
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact coef_smul a c F _

/-- **Lemma C.`theta`(a)**: `dim Θ_ℓ[a,b] = ℓ` for every `ℓ ≥ 1` (in particular `ℓ = 1, 2`). -/
theorem finrank_thetaSpaceDev {τ : ℂ} (hτ : 0 < τ.im) (a b : ℝ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    Module.finrank ℂ (thetaSpaceDev τ a b ℓ) = ℓ := by
  have hinj : Function.Injective (coefMap τ a b ℓ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro F hF
    have h0 := eq_zero_of_low_coef hℓ F.2 (fun r hr => congr_fun hF ⟨r, hr⟩)
    exact Subtype.ext h0
  have hsurj : Function.Surjective (coefMap τ a b ℓ) := by
    intro v
    refine ⟨∑ r : Fin ℓ, v r • ⟨thetaBasis τ a b ℓ r, thetaBasis_mem hτ a b hℓ r⟩, ?_⟩
    funext s
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single s]
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      change v s * coef a (thetaBasis τ a b ℓ s) ((s : ℕ) : ℤ) = v s
      rw [coef_thetaBasis hτ a b hℓ s.2 s.2]
      simp
    · intro r _ hrs
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      change v r * coef a (thetaBasis τ a b ℓ r) ((s : ℕ) : ℤ) = 0
      have hne : (r : ℕ) ≠ s := fun h => hrs (Fin.ext h)
      rw [coef_thetaBasis hτ a b hℓ r.2 s.2]
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ s) h
  rw [(LinearEquiv.ofBijective (coefMap τ a b ℓ) ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fin_fun]

theorem finrank_thetaSpaceDev_one {τ : ℂ} (hτ : 0 < τ.im) (a b : ℝ) :
    Module.finrank ℂ (thetaSpaceDev τ a b 1) = 1 := finrank_thetaSpaceDev hτ a b one_pos

theorem finrank_thetaSpaceDev_two {τ : ℂ} (hτ : 0 < τ.im) (a b : ℝ) :
    Module.finrank ℂ (thetaSpaceDev τ a b 2) = 2 := finrank_thetaSpaceDev hτ a b two_pos

end ThetaSpaceDevices

end ThetaDev

/-! ## `ϑ[a,b]` and the relations `kz:eq:theta-basic` -/

/-- `ϑ[a,b](u|τ)` (`kz:eq:orbital`: "`\kzvth[a,b](z|\tau)=\sum_n\exp(i\pi\tau(n+a)^2+2\pi i(n+a)(z+b))`") as a change of
variables of Mathlib's `jacobiTheta₂`: `ϑ[a,b](u|τ) = e^{iπa²τ + 2πia(u+b)} jacobiTheta₂(u + b + aτ, τ)` (F0's
`thetaChar`). -/
def thetaChar (a b : ℝ) (u τ : ℂ) : ℂ :=
  cexp (π * I * a ^ 2 * τ + 2 * π * I * a * (u + b)) * jacobiTheta₂ (u + b + a * τ) τ

/-- `kz:eq:orbital`: the definition is the paper's series
"`\kzvth[a,b](z|\tau)=\sum_n\exp(i\pi\tau(n+a)^2+2\pi i(n+a)(z+b))`" (for `Im τ > 0`). -/
theorem hasSum_thetaChar (a b : ℝ) (u : ℂ) (τ : ℍ) :
    HasSum (fun n : ℤ => cexp (π * I * (τ : ℂ) * (n + a) ^ 2 + 2 * π * I * (n + a) * (u + b)))
      (thetaChar a b u τ) := by
  -- the scouting pilot's proof (`hasSum_thetaChar`), at `τ : ℍ`
  have hτ : 0 < (τ : ℂ).im := τ.coe_im_pos
  have h := (hasSum_jacobiTheta₂_term (u + b + a * τ) hτ).mul_left
    (cexp (π * I * a ^ 2 * τ + 2 * π * I * a * (u + b)))
  unfold thetaChar
  convert h using 1
  funext n
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  ring

/-- **(C.eq:theta-basic)**: "`\kzvth[a,b](u+1)=e^{2\pi ia}\kzvth[a,b](u)`". -/
theorem thetaChar_add_one (a b : ℝ) (u τ : ℂ) :
    thetaChar a b (u + 1) τ = cexp (2 * π * I * a) * thetaChar a b u τ := by
  -- F0's proof
  unfold thetaChar
  rw [show u + 1 + b + a * τ = (u + b + a * τ) + 1 by ring, jacobiTheta₂_add_left,
    show π * I * a ^ 2 * τ + 2 * π * I * a * (u + 1 + b) =
      (π * I * a ^ 2 * τ + 2 * π * I * a * (u + b)) + 2 * π * I * a by ring, Complex.exp_add]
  ring

/-- **(C.eq:theta-basic)**: "`\kzvth[a,b](u+\tau)=e^{-i\pi\tau-2\pi i(u+b)}\kzvth[a,b](u)`". -/
theorem thetaChar_add_tau (a b : ℝ) (u τ : ℂ) :
    thetaChar a b (u + τ) τ = cexp (-π * I * τ - 2 * π * I * (u + b)) * thetaChar a b u τ := by
  -- F0's proof
  unfold thetaChar
  rw [show u + τ + b + a * τ = (u + b + a * τ) + τ by ring, jacobiTheta₂_add_left',
    show ∀ A B C : ℂ, cexp A * (cexp B * C) = C * cexp (A + B) from
      fun A B C => by rw [Complex.exp_add]; ring,
    show ∀ A B C : ℂ, cexp A * (cexp B * C) = C * cexp (A + B) from
      fun A B C => by rw [Complex.exp_add]; ring]
  congr 2
  ring

/-- **(C.eq:theta-basic)**: "`\kzvth[a,b](-u)=\kzvth[-a,-b](u)`". -/
theorem thetaChar_neg (a b : ℝ) (u τ : ℂ) : thetaChar a b (-u) τ = thetaChar (-a) (-b) u τ := by
  -- F0's proof
  unfold thetaChar
  rw [show -u + b + a * τ = -(u + ((-b : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * τ) by push_cast; ring,
    jacobiTheta₂_neg_left]
  congr 2
  push_cast
  ring

/-- **(C.eq:theta-basic)**: "`\kzvth[a+1,b]=\kzvth[a,b]`". -/
theorem thetaChar_add_a (a b : ℝ) (u τ : ℂ) : thetaChar (a + 1) b u τ = thetaChar a b u τ := by
  -- F0's proof
  unfold thetaChar
  rw [show u + b + ((a + 1 : ℝ) : ℂ) * τ = (u + b + a * τ) + τ by push_cast; ring,
    jacobiTheta₂_add_left', ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **(C.eq:theta-basic)**: "`\kzvth[a,b+1]=e^{2\pi ia}\kzvth[a,b]`". -/
theorem thetaChar_add_b (a b : ℝ) (u τ : ℂ) :
    thetaChar a (b + 1) u τ = cexp (2 * π * I * a) * thetaChar a b u τ := by
  -- F0's proof
  unfold thetaChar
  rw [show u + ((b + 1 : ℝ) : ℂ) + a * τ = (u + b + a * τ) + 1 by push_cast; ring,
    jacobiTheta₂_add_left, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `ϑ[a,b](·|τ)` is entire (for `Im τ > 0`). -/
theorem thetaChar_differentiable (a b : ℝ) (τ : ℍ) : Differentiable ℂ fun u => thetaChar a b u τ := by
  have hτ : 0 < (τ : ℂ).im := τ.coe_im_pos
  intro u
  unfold thetaChar
  have h2 : DifferentiableAt ℂ (fun u : ℂ => u + (b : ℂ) + (a : ℂ) * (τ : ℂ)) u := by fun_prop
  have h3 : DifferentiableAt ℂ (fun u : ℂ => jacobiTheta₂ (u + (b : ℂ) + (a : ℂ) * (τ : ℂ)) (τ : ℂ)) u :=
    (differentiableAt_jacobiTheta₂_fst (u + b + a * τ) hτ).comp (g := fun z => jacobiTheta₂ z (τ : ℂ)) u h2
  exact (by fun_prop : DifferentiableAt ℂ
      (fun u : ℂ => cexp (π * I * a ^ 2 * τ + 2 * π * I * a * (u + b))) u).mul h3

/-! ## `ϑ₁` and Lemma C.`theta`(c) -/

/-- **Lemma C.theta(c)**: "`$\kzvth_1:=\kzvth[\frac12,\frac12](\cdot|\tau)$ is odd`" — the definition (F0's `theta1`). -/
def theta1 (u τ : ℂ) : ℂ := thetaChar (1 / 2) (1 / 2) u τ

/-- The lattice of periods in `u`-units, "`$\Lambda_u:=\Z+\tau\Z$`". -/
def Λu (τ : ℍ) : Set ℂ := {u | ∃ p q : ℤ, u = p + q * (τ : ℂ)}

/-! ### Proof device for Lemma C.theta(c) (proof phase, round one; not a statement of the paper): F0's
`exp_two_pi_I_half` -/

theorem exp_two_pi_I_half_dev : cexp (2 * π * I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
  rw [show 2 * π * I * ((1 / 2 : ℝ) : ℂ) = π * I by push_cast; ring, Complex.exp_pi_mul_I]

/-- **Lemma C.theta(c)**: "`$\kzvth_1:=\kzvth[\frac12,\frac12](\cdot|\tau)$ is odd`". -/
theorem theta1_neg (u τ : ℂ) : theta1 (-u) τ = -theta1 u τ := by
  -- F0's proof: `ϑ₁(−u) = ϑ[−½,−½](u) = ϑ[½,−½](u) = −ϑ₁(u)`
  unfold theta1
  rw [thetaChar_neg]
  have h1 : thetaChar (-(1 / 2)) (-(1 / 2)) u τ = thetaChar (1 / 2) (-(1 / 2)) u τ := by
    rw [← thetaChar_add_a]; norm_num
  have h2 : thetaChar (1 / 2) (1 / 2) u τ = -thetaChar (1 / 2) (-(1 / 2)) u τ := by
    rw [show (1 / 2 : ℝ) = -(1 / 2) + 1 by norm_num, thetaChar_add_b]
    rw [show (-(1 / 2) + 1 : ℝ) = 1 / 2 by norm_num, exp_two_pi_I_half_dev]
    ring
  rw [h1, h2, neg_neg]

/-- **Lemma C.theta(c)**: "`$\kzvth_1(u+1)=-\kzvth_1(u)$`". -/
theorem theta1_add_one (u τ : ℂ) : theta1 (u + 1) τ = -theta1 u τ := by
  -- F0's proof
  unfold theta1
  rw [thetaChar_add_one, exp_two_pi_I_half_dev]
  ring

/-- **Lemma C.theta(c)**: "`$\kzvth_1(u+\tau)=-e^{-i\pi\tau-2\pi iu}\kzvth_1(u)$`". -/
theorem theta1_add_tau (u τ : ℂ) : theta1 (u + τ) τ = -cexp (-π * I * τ - 2 * π * I * u) * theta1 u τ := by
  -- F0's proof
  unfold theta1
  rw [thetaChar_add_tau,
    show -π * I * τ - 2 * π * I * (u + ((1 / 2 : ℝ) : ℂ)) = (-π * I * τ - 2 * π * I * u) + -(π * I) by
      push_cast; ring,
    Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
  ring

/-! ### Proof devices for Lemma C.theta(c) (proof phase, round one; not statements of the paper)

The scouting pilot's route to the zero set of `ϑ₁` and to `ϑ₁'(0) ≠ 0` (its `Theta1.lean` from `theta1_zero` on and its
`ThetaZerosPart.lean`, outside this repository), copied verbatim but for the names `thetaSpaceDev` (above) and
`exp_two_pi_I_half_dev`: `ϑ₁'(0) ≠ 0` by the dominance of one term of `jacobiTheta₂'` for `Im τ ≥ 1` and Mathlib's
functional equation otherwise; Jacobi's product `P` lies in `Θ_1[0,0]`, which is one-dimensional (Lemma C.theta(a)), so
`jacobiTheta₂ · τ = c P` with `c ≠ 0`, and the zeros of `P` are those of its factors — no argument principle. -/

namespace ThetaDev

section ThetaZeroDevices

open MeasureTheory intervalIntegral

theorem theta1_zero (τ : ℂ) : theta1 0 τ = 0 := by
  have h := theta1_neg 0 τ
  rw [neg_zero] at h
  exact CharZero.eq_neg_self_iff.mp h

/-- `ϑ₁` vanishes on the lattice `ℤ + τℤ`. -/
theorem theta1_lattice (τ : ℂ) (p q : ℤ) : theta1 (p + q * τ) τ = 0 := by
  have hstep1 : ∀ u, theta1 u τ = 0 ↔ theta1 (u + 1) τ = 0 := by
    intro u; rw [theta1_add_one, neg_eq_zero]
  have hstep2 : ∀ u, theta1 u τ = 0 ↔ theta1 (u + τ) τ = 0 := by
    intro u
    rw [theta1_add_tau, mul_eq_zero, neg_eq_zero]
    simp [Complex.exp_ne_zero]
  have hq : ∀ q : ℤ, theta1 (q * τ) τ = 0 := by
    intro q
    induction q using Int.induction_on with
    | zero => simpa using theta1_zero τ
    | succ i ih =>
      rw [show ((i + 1 : ℤ) : ℂ) * τ = (i : ℤ) * τ + τ by push_cast; ring]
      exact (hstep2 _).mp ih
    | pred i ih =>
      rw [hstep2]
      rw [show ((-(i : ℤ) - 1 : ℤ) : ℂ) * τ + τ = ((-(i : ℤ) : ℤ) : ℂ) * τ by push_cast; ring]
      exact ih
  induction p using Int.induction_on with
  | zero => simpa using hq q
  | succ i ih =>
    rw [show ((i + 1 : ℤ) : ℂ) + q * τ = ((i : ℤ) + q * τ) + 1 by push_cast; ring]
    exact (hstep1 _).mp ih
  | pred i ih =>
    rw [hstep1, show ((-(i : ℤ) - 1 : ℤ) : ℂ) + q * τ + 1 = ((-(i : ℤ) : ℤ) : ℂ) + q * τ by
      push_cast; ring]
    exact ih

/-! ## `ϑ₁'(0) ≠ 0` for `Im τ ≥ 1`, by the dominance of the `n = −1` term of `jacobiTheta₂'` -/

theorem hasSum_natAbs_mul_pow {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun n : ℤ => (n.natAbs : ℝ) * r ^ n.natAbs) (2 * (r / (1 - r) ^ 2)) := by
  have hr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hA := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hB : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * r ^ (n + 1)) (r / (1 - r) ^ 2) := by
    have := (hasSum_nat_add_iff' 1).mpr hA
    simpa using this
  rw [two_mul]
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · simpa using hA
  · convert hB using 1
    funext n
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [this]

theorem jacobiTheta₂'_half_ne_zero {τ : ℂ} (hτ : 1 ≤ τ.im) :
    jacobiTheta₂' (1 / 2 + τ / 2) τ ≠ 0 := by
  have hτ0 : 0 < τ.im := by linarith
  set z₀ : ℂ := 1 / 2 + τ / 2 with hz₀
  set r : ℝ := Real.exp (-π * τ.im) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 / 5 := by
    have h1 : -π * τ.im ≤ -3 := by nlinarith [Real.pi_gt_three]
    have h2 : Real.exp (-3) < 1 / 5 := by
      rw [Real.exp_neg]
      rw [inv_lt_comm₀ (Real.exp_pos 3) (by norm_num)]
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h4 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      rw [h3]
      have h5 : (2 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h4 3
      norm_num at h5 ⊢
      linarith
    calc r ≤ Real.exp (-3) := Real.exp_le_exp.mpr h1
      _ ≤ 1 / 5 := h2.le
  have hm1 : jacobiTheta₂'_term (-1) z₀ τ = 2 * π * I := by
    simp only [jacobiTheta₂'_term, jacobiTheta₂_term, hz₀]
    rw [show 2 * (π : ℂ) * I * ((-1 : ℤ) : ℂ) * (1 / 2 + τ / 2) + π * I * ((-1 : ℤ) : ℂ) ^ 2 * τ =
      -(π * I) by push_cast; ring, Complex.exp_neg, Complex.exp_pi_mul_I]
    push_cast
    ring
  let g : ℤ → ℂ := fun n => jacobiTheta₂'_term n z₀ τ - if n = -1 then 2 * π * I else 0
  have hg : HasSum g (jacobiTheta₂' z₀ τ - 2 * π * I) :=
    (hasSum_jacobiTheta₂'_term z₀ hτ0).sub (hasSum_ite_eq (-1) _)
  have hgb : ∀ n : ℤ, ‖g n‖ ≤ 2 * π * ((n.natAbs : ℝ) * r ^ n.natAbs) := by
    intro n
    by_cases hn : n = -1
    · subst hn
      simp only [g, hm1, ite_true, sub_self, norm_zero]
      positivity
    · simp only [g, hn, ite_false, sub_zero, jacobiTheta₂'_term]
      have e1 : ‖(2 : ℂ) * π * I * n‖ = 2 * π * (n.natAbs : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        simp [abs_of_pos Real.pi_pos]
      rw [norm_mul, e1, norm_jacobiTheta₂_term, mul_assoc]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
        (by positivity)
      rw [hr, ← Real.exp_nat_mul, Real.exp_le_exp]
      have hzi : z₀.im = τ.im / 2 := by simp [hz₀]
      rw [hzi]
      have hn2 : (n.natAbs : ℝ) ≤ (n : ℝ) ^ 2 + n := by
        rcases le_or_gt 0 n with h | h
        · have : (n.natAbs : ℝ) = n := by
            rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast h)]
          rw [this]; nlinarith
        · have hn' : n ≤ -2 := by omega
          have : (n.natAbs : ℝ) = -n := by
            rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h)]
          rw [this]
          have : (n : ℝ) ≤ -2 := by exact_mod_cast hn'
          nlinarith
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hτ0.le) (sub_nonneg.mpr hn2)]
  have hB := (hasSum_natAbs_mul_pow hr0 (by linarith)).mul_left (2 * π)
  have hle : ‖jacobiTheta₂' z₀ τ - 2 * π * I‖ ≤ 2 * π * (2 * (r / (1 - r) ^ 2)) := by
    rw [← hg.tsum_eq]
    exact tsum_of_norm_bounded hB hgb
  have hlt : 2 * π * (2 * (r / (1 - r) ^ 2)) < 2 * π := by
    have h1r : 0 < 1 - r := by linarith
    have : 2 * (r / (1 - r) ^ 2) < 1 := by
      rw [← mul_div_assoc, div_lt_one (by positivity)]
      nlinarith
    nlinarith [Real.pi_pos]
  intro h0
  rw [h0, zero_sub, norm_neg] at hle
  have : ‖(2 : ℂ) * π * I‖ = 2 * π := by simp [abs_of_pos Real.pi_pos]
  rw [this] at hle
  linarith

/-- **`ϑ₁'(0) ≠ 0` for `Im τ ≥ 1`.** (For all `τ` in the upper half-plane see the report: the dominance
estimate alone does not reach small `Im τ`.) -/
theorem theta1_deriv_zero_ne_zero {τ : ℂ} (hτ : 1 ≤ τ.im) : deriv (fun u => theta1 u τ) 0 ≠ 0 := by
  have hτ0 : 0 < τ.im := by linarith
  set A : ℂ := π * I * ((1 / 2 : ℝ) : ℂ) ^ 2 * τ
  set B : ℂ := 2 * π * I * ((1 / 2 : ℝ) : ℂ)
  set c : ℂ := ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * τ
  have hform : (fun u => theta1 u τ) = fun u => cexp (A + B * (u + ((1 / 2 : ℝ) : ℂ))) *
      jacobiTheta₂ (u + c) τ := by
    funext u
    unfold theta1 thetaChar
    rw [show u + ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * τ = u + c by simp only [c]; ring]
  have hE : HasDerivAt (fun u : ℂ => cexp (A + B * (u + ((1 / 2 : ℝ) : ℂ))))
      (cexp (A + B * (0 + ((1 / 2 : ℝ) : ℂ))) * B) 0 := by
    have : HasDerivAt (fun u : ℂ => A + B * (u + ((1 / 2 : ℝ) : ℂ))) B 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).add_const ((1 / 2 : ℝ) : ℂ)).const_mul B |>.const_add A
    exact this.cexp
  have hJ : HasDerivAt (fun u : ℂ => jacobiTheta₂ (u + c) τ) (jacobiTheta₂' (0 + c) τ) 0 := by
    have h1 := hasDerivAt_jacobiTheta₂_fst (0 + c) hτ0
    have h2 : HasDerivAt (fun u : ℂ => u + c) 1 0 := (hasDerivAt_id 0).add_const c
    have h3 := h1.comp (0 : ℂ) h2
    rw [mul_one] at h3
    exact h3
  have hd : HasDerivAt (fun u => cexp (A + B * (u + ((1 / 2 : ℝ) : ℂ))) * jacobiTheta₂ (u + c) τ)
      (cexp (A + B * (0 + ((1 / 2 : ℝ) : ℂ))) * B * jacobiTheta₂ (0 + c) τ +
        cexp (A + B * (0 + ((1 / 2 : ℝ) : ℂ))) * jacobiTheta₂' (0 + c) τ) 0 := hE.mul hJ
  rw [hform, hd.deriv]
  have hz : jacobiTheta₂ (0 + c) τ = 0 := by
    have h := theta1_zero τ
    rw [show theta1 0 τ = (fun u => theta1 u τ) 0 from rfl, hform] at h
    exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)
  rw [hz, mul_zero, zero_add]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  have hc : 0 + c = 1 / 2 + τ / 2 := by simp only [c]; push_cast; ring
  rw [hc]
  exact jacobiTheta₂'_half_ne_zero hτ

/-! ## Extension to `Im(−1/τ) ≥ 1` by Mathlib's functional equation (`jacobiTheta₂'_functional_equation`),
hence to every rectangular `τ = it`, `t > 0` -/

theorem jacobiTheta₂_half_eq_zero {τ : ℂ} : jacobiTheta₂ (1 / 2 + τ / 2) τ = 0 := by
  have h := theta1_zero τ
  unfold theta1 thetaChar at h
  rw [show (0 : ℂ) + ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * τ = 1 / 2 + τ / 2 by push_cast; ring] at h
  exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)

theorem jacobiTheta₂'_half_ne_zero_of_S {τ : ℂ} (hτ : 0 < τ.im) (hS : 1 ≤ (-1 / τ).im) :
    jacobiTheta₂' (1 / 2 + τ / 2) τ ≠ 0 := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  set τ' : ℂ := -1 / τ with hτ'
  set w : ℂ := 1 / 2 - τ' / 2 with hw
  have hz : (1 / 2 + τ / 2) / τ = w := by
    rw [hw, hτ']; field_simp; ring
  have hw1 : w + τ' = 1 / 2 + τ' / 2 := by rw [hw]; ring
  have hjw : jacobiTheta₂ w τ' = 0 := by
    have h := jacobiTheta₂_add_left' w τ'
    rw [hw1, jacobiTheta₂_half_eq_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Complex.exp_ne_zero _)
  have hj'w : jacobiTheta₂' w τ' ≠ 0 := by
    intro h0
    have h := jacobiTheta₂'_add_left' w τ'
    rw [hw1, h0, hjw, mul_zero, sub_zero, mul_zero] at h
    exact jacobiTheta₂'_half_ne_zero hS h
  rw [jacobiTheta₂'_functional_equation, hz, hjw, mul_zero, sub_zero]
  refine mul_ne_zero (div_ne_zero (mul_ne_zero ?_ (Complex.exp_ne_zero _)) hτ0) hj'w
  refine one_div_ne_zero ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  intro h
  exact hτ0 (by simpa using h.1)

/-- **`ϑ₁'(0) ≠ 0` for every rectangular `τ = it`, `t > 0`** (both orientations of the torus). -/
theorem theta1_deriv_zero_ne_zero_rect {t : ℝ} (ht : 0 < t) :
    deriv (fun u => theta1 u (t * I)) 0 ≠ 0 := by
  rcases le_or_gt 1 t with h1 | h1
  · exact theta1_deriv_zero_ne_zero (by simpa using h1)
  · -- reuse the derivative computation of `theta1_deriv_zero_ne_zero` through its two halves
    set τ : ℂ := t * I with hτdef
    have hτ0 : 0 < τ.im := by simpa [hτdef] using ht
    have hS : 1 ≤ (-1 / τ).im := by
      have : -1 / τ = ((1 / t : ℝ) : ℂ) * I := by
        rw [hτdef]; field_simp; push_cast; field_simp; rw [Complex.I_sq]; ring
      rw [this]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
        Complex.I_re, mul_zero, add_zero]
      rw [le_div_iff₀ ht]; linarith
    set A : ℂ := π * I * ((1 / 2 : ℝ) : ℂ) ^ 2 * τ
    set B : ℂ := 2 * π * I * ((1 / 2 : ℝ) : ℂ)
    set c : ℂ := ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * τ
    have hform : (fun u => theta1 u τ) = fun u => cexp (A + B * (u + ((1 / 2 : ℝ) : ℂ))) *
        jacobiTheta₂ (u + c) τ := by
      funext u
      unfold theta1 thetaChar
      rw [show u + ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * τ = u + c by simp only [c]; ring]
    have hE : HasDerivAt (fun u : ℂ => cexp (A + B * (u + ((1 / 2 : ℝ) : ℂ))))
        (cexp (A + B * (0 + ((1 / 2 : ℝ) : ℂ))) * B) 0 := by
      have : HasDerivAt (fun u : ℂ => A + B * (u + ((1 / 2 : ℝ) : ℂ))) B 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).add_const ((1 / 2 : ℝ) : ℂ)).const_mul B |>.const_add A
      exact this.cexp
    have hJ : HasDerivAt (fun u : ℂ => jacobiTheta₂ (u + c) τ) (jacobiTheta₂' (0 + c) τ) 0 := by
      have h1 := hasDerivAt_jacobiTheta₂_fst (0 + c) hτ0
      have h2 : HasDerivAt (fun u : ℂ => u + c) 1 0 := (hasDerivAt_id 0).add_const c
      have h3 := h1.comp (0 : ℂ) h2
      rw [mul_one] at h3
      exact h3
    have hd : HasDerivAt (fun u => cexp (A + B * (u + ((1 / 2 : ℝ) : ℂ))) * jacobiTheta₂ (u + c) τ)
        (cexp (A + B * (0 + ((1 / 2 : ℝ) : ℂ))) * B * jacobiTheta₂ (0 + c) τ +
          cexp (A + B * (0 + ((1 / 2 : ℝ) : ℂ))) * jacobiTheta₂' (0 + c) τ) 0 := hE.mul hJ
    rw [hform, hd.deriv]
    have hc : 0 + c = 1 / 2 + τ / 2 := by simp only [c]; push_cast; ring
    rw [hc, jacobiTheta₂_half_eq_zero, mul_zero, zero_add]
    exact mul_ne_zero (Complex.exp_ne_zero _) (jacobiTheta₂'_half_ne_zero_of_S hτ0 hS)

section Product

/-- The factors `q^{2n+1} e^{±2πiu}`, written as exponentials. -/
def fA (τ : ℂ) (n : ℕ) (u : ℂ) : ℂ := cexp ((2 * n + 1) * π * I * τ + 2 * π * I * u)
def fB (τ : ℂ) (n : ℕ) (u : ℂ) : ℂ := cexp ((2 * n + 1) * π * I * τ - 2 * π * I * u)

def PA (τ u : ℂ) : ℂ := ∏' n : ℕ, (1 + fA τ n u)
def PB (τ u : ℂ) : ℂ := ∏' n : ℕ, (1 + fB τ n u)
def Pθ (τ u : ℂ) : ℂ := PA τ u * PB τ u

theorem fA_differentiable (τ : ℂ) (n : ℕ) : Differentiable ℂ (fA τ n) := by
  unfold fA; fun_prop

theorem fB_differentiable (τ : ℂ) (n : ℕ) : Differentiable ℂ (fB τ n) := by
  unfold fB; fun_prop

/-- The majorant `e^{2πR} e^{−πt} (e^{−2πt})^n` on the strip `|Im u| ≤ R`. -/
def bnd (τ : ℂ) (R : ℝ) (n : ℕ) : ℝ :=
  Real.exp (2 * π * R) * Real.exp (-π * τ.im) * Real.exp (-2 * π * τ.im) ^ n

theorem summable_bnd {τ : ℂ} (hτ : 0 < τ.im) (R : ℝ) : Summable (bnd τ R) := by
  unfold bnd
  refine Summable.mul_left _ (summable_geometric_of_lt_one (Real.exp_pos _).le ?_)
  rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]

theorem norm_fA_le {τ : ℂ} {R : ℝ} {u : ℂ} (hu : |u.im| ≤ R) (n : ℕ) : ‖fA τ n u‖ ≤ bnd τ R n := by
  unfold fA bnd
  rw [Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have h1 : ((2 * (n : ℂ) + 1) * π * I * τ + 2 * π * I * u).re =
      -((2 * n + 1) * π * τ.im) - 2 * π * u.im := by
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [h1]
  have := neg_abs_le u.im
  nlinarith [Real.pi_pos]

theorem norm_fB_le {τ : ℂ} {R : ℝ} {u : ℂ} (hu : |u.im| ≤ R) (n : ℕ) : ‖fB τ n u‖ ≤ bnd τ R n := by
  unfold fB bnd
  rw [Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have h1 : ((2 * (n : ℂ) + 1) * π * I * τ - 2 * π * I * u).re =
      -((2 * n + 1) * π * τ.im) + 2 * π * u.im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h1]
  have := le_abs_self u.im
  nlinarith [Real.pi_pos]

theorem summable_fA {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) : Summable (fun n => fA τ n u) :=
  Summable.of_norm_bounded (summable_bnd hτ |u.im|) (norm_fA_le le_rfl)

theorem summable_fB {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) : Summable (fun n => fB τ n u) :=
  Summable.of_norm_bounded (summable_bnd hτ |u.im|) (norm_fB_le le_rfl)

/-- `PA` is entire (a locally uniformly convergent product, as Mathlib's `η` is). -/
theorem PA_differentiable {τ : ℂ} (hτ : 0 < τ.im) : Differentiable ℂ (PA τ) := by
  intro u₀
  set R : ℝ := |u₀.im| + 1
  set K : Set ℂ := {u | |u.im| < R}
  have hK : IsOpen K := (continuous_abs.comp Complex.continuous_im).isOpen_preimage _ isOpen_Iio
  have hu₀ : u₀ ∈ K := by show |u₀.im| < R; simp [R]
  have hprod := Summable.hasProdLocallyUniformlyOn_nat_one_add (f := fun n u => fA τ n u) hK
    (summable_bnd hτ R) (Filter.Eventually.of_forall fun n u hu => norm_fA_le (le_of_lt hu) n)
    (fun n => (fA_differentiable τ n).continuous.continuousOn)
  have hd : DifferentiableOn ℂ (fun u => ∏' i, (1 + fA τ i u)) K :=
    hprod.differentiableOn (.of_forall fun s => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ =>
        ((differentiable_const (1 : ℂ)).add (fA_differentiable τ i)).differentiableOn)) hK
  exact (hd u₀ hu₀).differentiableAt (hK.mem_nhds hu₀)

theorem PB_differentiable {τ : ℂ} (hτ : 0 < τ.im) : Differentiable ℂ (PB τ) := by
  intro u₀
  set R : ℝ := |u₀.im| + 1
  set K : Set ℂ := {u | |u.im| < R}
  have hK : IsOpen K := (continuous_abs.comp Complex.continuous_im).isOpen_preimage _ isOpen_Iio
  have hu₀ : u₀ ∈ K := by show |u₀.im| < R; simp [R]
  have hprod := Summable.hasProdLocallyUniformlyOn_nat_one_add (f := fun n u => fB τ n u) hK
    (summable_bnd hτ R) (Filter.Eventually.of_forall fun n u hu => norm_fB_le (le_of_lt hu) n)
    (fun n => (fB_differentiable τ n).continuous.continuousOn)
  have hd : DifferentiableOn ℂ (fun u => ∏' i, (1 + fB τ i u)) K :=
    hprod.differentiableOn (.of_forall fun s => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ =>
        ((differentiable_const (1 : ℂ)).add (fB_differentiable τ i)).differentiableOn)) hK
  exact (hd u₀ hu₀).differentiableAt (hK.mem_nhds hu₀)

/-! ### The index shifts -/

theorem fA_add_one (τ : ℂ) (n : ℕ) (u : ℂ) : fA τ n (u + 1) = fA τ n u := by
  unfold fA
  rw [show (2 * (n : ℂ) + 1) * π * I * τ + 2 * π * I * (u + 1) =
    ((2 * n + 1) * π * I * τ + 2 * π * I * u) + 2 * π * I by ring, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

theorem fB_add_one (τ : ℂ) (n : ℕ) (u : ℂ) : fB τ n (u + 1) = fB τ n u := by
  unfold fB
  rw [show (2 * (n : ℂ) + 1) * π * I * τ - 2 * π * I * (u + 1) =
    ((2 * n + 1) * π * I * τ - 2 * π * I * u) + ((-1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem fA_add_tau (τ : ℂ) (n : ℕ) (u : ℂ) : fA τ n (u + τ) = fA τ (n + 1) u := by
  unfold fA; congr 1; push_cast; ring

theorem fB_succ_add_tau (τ : ℂ) (n : ℕ) (u : ℂ) : fB τ (n + 1) (u + τ) = fB τ n u := by
  unfold fB; congr 1; push_cast; ring

theorem PA_eq {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) : PA τ u = (1 + fA τ 0 u) * PA τ (u + τ) := by
  unfold PA
  have hs : Summable (fun n => fA τ (n + 1) u) :=
    (summable_nat_add_iff (f := fun n => fA τ n u) 1).mpr (summable_fA hτ u)
  have hm : Multipliable (fun n => 1 + fA τ (n + 1) u) := Complex.multipliable_one_add_of_summable hs
  rw [tprod_eq_zero_mul' (f := fun n => 1 + fA τ n u) hm]
  congr 1
  exact tprod_congr fun n => by rw [fA_add_tau]

theorem PB_add_tau {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) :
    PB τ (u + τ) = (1 + fB τ 0 (u + τ)) * PB τ u := by
  unfold PB
  have hs : Summable (fun n => fB τ (n + 1) (u + τ)) := by
    have e : (fun n => fB τ (n + 1) (u + τ)) = fun n => fB τ n u := funext fun n => fB_succ_add_tau τ n u
    rw [e]; exact summable_fB hτ u
  have hm : Multipliable (fun n => 1 + fB τ (n + 1) (u + τ)) := Complex.multipliable_one_add_of_summable hs
  rw [tprod_eq_zero_mul' (f := fun n => 1 + fB τ n (u + τ)) hm]
  congr 1
  exact tprod_congr fun n => by rw [fB_succ_add_tau]

theorem Pθ_add_one (τ u : ℂ) : Pθ τ (u + 1) = Pθ τ u := by
  unfold Pθ PA PB
  simp only [fA_add_one, fB_add_one]

theorem Pθ_add_tau {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) :
    Pθ τ (u + τ) = cexp (-π * I * (2 * u + τ)) * Pθ τ u := by
  unfold Pθ
  have h1 : 1 + fB τ 0 (u + τ) = cexp (-π * I * (2 * u + τ)) * (1 + fA τ 0 u) := by
    have e1 : fB τ 0 (u + τ) = cexp (-π * I * (2 * u + τ)) := by
      unfold fB; congr 1; push_cast; ring
    have e2 : cexp (-π * I * (2 * u + τ)) * fA τ 0 u = 1 := by
      unfold fA
      rw [← Complex.exp_add, show -π * I * (2 * u + τ) + ((2 * ((0 : ℕ) : ℂ) + 1) * π * I * τ +
        2 * π * I * u) = 0 by push_cast; ring, Complex.exp_zero]
    rw [e1, mul_add (cexp (-π * I * (2 * u + τ))) 1 (fA τ 0 u), mul_one, e2]
    ring
  rw [PB_add_tau hτ, h1, PA_eq hτ u]
  ring

/-- **Jacobi's product lies in `Θ_1[0,0]`.** -/
theorem Pθ_mem {τ : ℂ} (hτ : 0 < τ.im) : Pθ τ ∈ thetaSpaceDev τ 0 0 1 := by
  refine ⟨(PA_differentiable hτ).mul (PB_differentiable hτ), fun U => ?_, fun U => ?_⟩
  · rw [Pθ_add_one]; simp
  · rw [Pθ_add_tau hτ]; simp

/-! ### Nonvanishing of the product off the zeros of its factors -/

theorem one_add_ne_zero_of_norm_lt {z : ℂ} (h : ‖z‖ < 1) : 1 + z ≠ 0 := by
  intro h0
  have : z = -1 := by linear_combination h0
  rw [this, norm_neg, norm_one] at h
  exact lt_irrefl _ h

theorem PA_ne_zero {τ : ℂ} (hτ : 0 < τ.im) {u : ℂ} (h : ∀ n, 1 + fA τ n u ≠ 0) : PA τ u ≠ 0 :=
  tprod_one_add_ne_zero_of_summable h (summable_fA hτ u).norm

theorem PB_ne_zero {τ : ℂ} (hτ : 0 < τ.im) {u : ℂ} (h : ∀ n, 1 + fB τ n u ≠ 0) : PB τ u ≠ 0 :=
  tprod_one_add_ne_zero_of_summable h (summable_fB hτ u).norm

theorem Pθ_zero_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : Pθ τ 0 ≠ 0 := by
  have hA : ∀ n, 1 + fA τ n 0 ≠ 0 := fun n => one_add_ne_zero_of_norm_lt (by
    unfold fA
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    simp [Complex.mul_re, Complex.mul_im]
    have : (0 : ℝ) < 2 * n + 1 := by positivity
    nlinarith [Real.pi_pos, mul_pos (mul_pos this Real.pi_pos) hτ])
  have hB : ∀ n, 1 + fB τ n 0 ≠ 0 := fun n => one_add_ne_zero_of_norm_lt (by
    unfold fB
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    simp [Complex.mul_re, Complex.mul_im]
    have : (0 : ℝ) < 2 * n + 1 := by positivity
    nlinarith [Real.pi_pos, mul_pos (mul_pos this Real.pi_pos) hτ])
  exact mul_ne_zero (PA_ne_zero hτ hA) (PB_ne_zero hτ hB)

/-! ### `jacobiTheta₂ · τ = c P`, `c ≠ 0` (task 1's one-dimensionality) -/

theorem jacobiTheta₂_eq_thetaBasis (τ U : ℂ) : jacobiTheta₂ U τ = thetaBasis τ 0 0 1 0 U := by
  unfold thetaBasis; simp

theorem jacobiTheta₂_mem {τ : ℂ} (hτ : 0 < τ.im) : (fun U => jacobiTheta₂ U τ) ∈ thetaSpaceDev τ 0 0 1 := by
  have : (fun U => jacobiTheta₂ U τ) = thetaBasis τ 0 0 1 0 := funext (jacobiTheta₂_eq_thetaBasis τ)
  rw [this]; exact thetaBasis_mem hτ 0 0 one_pos 0

theorem jacobiTheta₂_ne_zero_fun {τ : ℂ} (hτ : 0 < τ.im) : (fun U => jacobiTheta₂ U τ) ≠ 0 := by
  intro h
  have e : (fun U => jacobiTheta₂ U τ) = thetaBasis τ 0 0 1 0 := funext (jacobiTheta₂_eq_thetaBasis τ)
  have hc := coef_thetaBasis hτ 0 0 one_pos (r := 0) (s := 0) one_pos one_pos
  rw [← e, h] at hc
  simp [coef] at hc

theorem jacobiTheta₂_eq_smul_Pθ {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ U, jacobiTheta₂ U τ = c * Pθ τ U := by
  have hP : (⟨Pθ τ, Pθ_mem hτ⟩ : thetaSpaceDev τ 0 0 1) ≠ 0 := by
    intro h
    have := congrArg (fun F : thetaSpaceDev τ 0 0 1 => (F : ℂ → ℂ) 0) h
    exact Pθ_zero_ne_zero hτ (by simpa using this)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hP).mp (finrank_thetaSpaceDev hτ 0 0 one_pos)
    ⟨_, jacobiTheta₂_mem hτ⟩
  have hfun : (fun U => jacobiTheta₂ U τ) = c • Pθ τ := by
    have := congrArg Subtype.val hc
    simpa using this.symm
  refine ⟨c, ?_, fun U => by simpa using congrFun hfun U⟩
  rintro rfl
  exact jacobiTheta₂_ne_zero_fun hτ (by simpa using hfun)

/-! ### The zero set of `ϑ₁` is exactly the lattice (Lemma C.`theta`(c), first half) -/

theorem exp_eq_neg_one_imp {X : ℂ} (h : 1 + cexp X = 0) : ∃ k : ℤ, X + π * I = k * (2 * π * I) := by
  have h1 : cexp X = -1 := by linear_combination h
  have h2 : cexp (X + π * I) = 1 := by rw [Complex.exp_add, h1, Complex.exp_pi_mul_I]; ring
  exact Complex.exp_eq_one_iff.mp h2

theorem theta1_eq_zero_iff {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) :
    theta1 u τ = 0 ↔ ∃ p q : ℤ, u = p + q * τ := by
  constructor
  · intro h0
    obtain ⟨c, hc0, hc⟩ := jacobiTheta₂_eq_smul_Pθ hτ
    have hj : jacobiTheta₂ (u + 1 / 2 + τ / 2) τ = 0 := by
      unfold theta1 thetaChar at h0
      rw [show u + ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * τ = u + 1 / 2 + τ / 2 by push_cast; ring] at h0
      exact (mul_eq_zero.mp h0).resolve_left (Complex.exp_ne_zero _)
    rw [hc, mul_eq_zero] at hj
    have hP := hj.resolve_left hc0
    unfold Pθ at hP
    have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    rcases mul_eq_zero.mp hP with hA | hB
    · -- a factor of `PA` vanishes
      by_contra hne
      push Not at hne
      refine PA_ne_zero hτ (fun n hn => ?_) hA
      unfold fA at hn
      obtain ⟨k, hk⟩ := exp_eq_neg_one_imp hn
      apply hne (k - 1) (-(n + 1 : ℤ))
      have : (2 * π * I : ℂ) * (u - ((k - 1 : ℤ) : ℂ) - ((-(n + 1 : ℤ) : ℤ) : ℂ) * τ) = 0 := by
        push_cast; linear_combination hk
      have := (mul_eq_zero.mp this).resolve_left hπ
      linear_combination this
    · by_contra hne
      push Not at hne
      refine PB_ne_zero hτ (fun n hn => ?_) hB
      unfold fB at hn
      obtain ⟨k, hk⟩ := exp_eq_neg_one_imp hn
      apply hne (-k) n
      have : (2 * π * I : ℂ) * (u - ((-k : ℤ) : ℂ) - ((n : ℤ) : ℂ) * τ) = 0 := by
        push_cast; linear_combination -hk
      have := (mul_eq_zero.mp this).resolve_left hπ
      linear_combination this
  · rintro ⟨p, q, rfl⟩
    exact theta1_lattice τ p q

/-! ### Simplicity (Lemma C.`theta`(c), second half): `ϑ₁'(λ) ≠ 0` at every lattice point, every `τ` -/

theorem norm_fA_eq (τ : ℂ) (n : ℕ) (u : ℂ) :
    ‖fA τ n u‖ = Real.exp (-((2 * n + 1) * π * τ.im) - 2 * π * u.im) := by
  unfold fA; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]; ring

theorem norm_fB_eq (τ : ℂ) (n : ℕ) (u : ℂ) :
    ‖fB τ n u‖ = Real.exp (-((2 * n + 1) * π * τ.im) + 2 * π * u.im) := by
  unfold fB; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]

theorem PB_eq_shift {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) :
    PB τ u = (1 + fB τ 0 u) * PB τ (u - τ) := by
  have := PB_add_tau hτ (u - τ)
  rwa [sub_add_cancel] at this

theorem fB_hasDerivAt (τ : ℂ) (n : ℕ) (u : ℂ) :
    HasDerivAt (fB τ n) (fB τ n u * (-(2 * π * I))) u := by
  unfold fB
  have h1 : HasDerivAt (fun u : ℂ => (2 * (n : ℂ) + 1) * π * I * τ - 2 * π * I * u) (-(2 * π * I)) u := by
    have := ((hasDerivAt_id u).const_mul (2 * π * I)).const_sub ((2 * (n : ℂ) + 1) * π * I * τ)
    simpa using this
  exact h1.cexp

/-- **`ϑ(·|τ)' ≠ 0` at its zero `½ + τ/2`, for every `τ` in the upper half-plane** (by the product). -/
theorem jacobiTheta₂'_half_ne_zero_all {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂' (1 / 2 + τ / 2) τ ≠ 0 := by
  set z₀ : ℂ := 1 / 2 + τ / 2 with hz₀
  obtain ⟨c, hc0, hc⟩ := jacobiTheta₂_eq_smul_Pθ hτ
  have hPform : Pθ τ = fun u => PA τ u * ((1 + fB τ 0 u) * PB τ (u - τ)) := by
    funext u; unfold Pθ; rw [PB_eq_shift hτ u]
  have hA := (PA_differentiable hτ z₀).hasDerivAt
  have hg : HasDerivAt (fun u => 1 + fB τ 0 u) (fB τ 0 z₀ * (-(2 * π * I))) z₀ :=
    (fB_hasDerivAt τ 0 z₀).const_add 1
  have hB : HasDerivAt (fun u => PB τ (u - τ)) (deriv (PB τ) (z₀ - τ)) z₀ :=
    HasDerivAt.comp_sub_const z₀ τ (PB_differentiable hτ (z₀ - τ)).hasDerivAt
  have hP := hA.mul (hg.mul hB)
  have hfB0 : fB τ 0 z₀ = -1 := by
    unfold fB
    rw [hz₀, show (2 * ((0 : ℕ) : ℂ) + 1) * π * I * τ - 2 * π * I * (1 / 2 + τ / 2) = -(π * I) by
      push_cast; ring, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have hJ : HasDerivAt (fun u => jacobiTheta₂ u τ)
      (c * (deriv (PA τ) z₀ * ((1 + fB τ 0 z₀) * PB τ (z₀ - τ)) +
        PA τ z₀ * (fB τ 0 z₀ * (-(2 * π * I)) * PB τ (z₀ - τ) +
          (1 + fB τ 0 z₀) * deriv (PB τ) (z₀ - τ)))) z₀ := by
    have e : (fun u => jacobiTheta₂ u τ) = fun u => c * (PA τ u * ((1 + fB τ 0 u) * PB τ (u - τ))) := by
      funext u; rw [hc u, hPform]
    rw [e]; exact hP.const_mul c
  rw [(hasDerivAt_jacobiTheta₂_fst z₀ hτ).unique hJ, hfB0]
  have hPA : PA τ z₀ ≠ 0 := PA_ne_zero hτ fun n => one_add_ne_zero_of_norm_lt (by
    rw [norm_fA_eq, Real.exp_lt_one_iff, hz₀]
    simp
    have : (0 : ℝ) < 2 * n + 1 := by positivity
    nlinarith [Real.pi_pos, mul_pos (mul_pos this Real.pi_pos) hτ, mul_pos Real.pi_pos hτ])
  have hPB : PB τ (z₀ - τ) ≠ 0 := PB_ne_zero hτ fun n => one_add_ne_zero_of_norm_lt (by
    rw [norm_fB_eq, Real.exp_lt_one_iff, hz₀]
    simp
    have : (0 : ℝ) < 2 * n + 1 := by positivity
    nlinarith [Real.pi_pos, mul_pos (mul_pos this Real.pi_pos) hτ, mul_pos Real.pi_pos hτ])
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : c * (deriv (PA τ) z₀ * ((1 + -1) * PB τ (z₀ - τ)) +
      PA τ z₀ * (-1 * (-(2 * π * I)) * PB τ (z₀ - τ) + (1 + -1) * deriv (PB τ) (z₀ - τ))) =
      c * PA τ z₀ * (2 * π * I) * PB τ (z₀ - τ) := by ring
  rw [this]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc0 hPA) hπ) hPB

theorem theta1_differentiable {τ : ℂ} (hτ : 0 < τ.im) : Differentiable ℂ (fun u => theta1 u τ) := by
  intro u
  unfold theta1 thetaChar
  refine DifferentiableAt.mul (by fun_prop) ?_
  have h1 : DifferentiableAt ℂ (fun u : ℂ => u + ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * τ) u := by
    fun_prop
  exact (differentiableAt_jacobiTheta₂_fst _ hτ).comp u h1

/-- **`ϑ₁'(0) ≠ 0` for every `τ` in the upper half-plane.** -/
theorem theta1_deriv_zero_ne_zero_all {τ : ℂ} (hτ0 : 0 < τ.im) :
    deriv (fun u => theta1 u τ) 0 ≠ 0 := by
  set A : ℂ := π * I * ((1 / 2 : ℝ) : ℂ) ^ 2 * τ
  set B : ℂ := 2 * π * I * ((1 / 2 : ℝ) : ℂ)
  set c : ℂ := ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * τ
  have hform : (fun u => theta1 u τ) = fun u => cexp (A + B * (u + ((1 / 2 : ℝ) : ℂ))) *
      jacobiTheta₂ (u + c) τ := by
    funext u
    unfold theta1 thetaChar
    rw [show u + ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * τ = u + c by simp only [c]; ring]
  have hE : HasDerivAt (fun u : ℂ => cexp (A + B * (u + ((1 / 2 : ℝ) : ℂ))))
      (cexp (A + B * (0 + ((1 / 2 : ℝ) : ℂ))) * B) 0 := by
    have : HasDerivAt (fun u : ℂ => A + B * (u + ((1 / 2 : ℝ) : ℂ))) B 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).add_const ((1 / 2 : ℝ) : ℂ)).const_mul B |>.const_add A
    exact this.cexp
  have hJ : HasDerivAt (fun u : ℂ => jacobiTheta₂ (u + c) τ) (jacobiTheta₂' (0 + c) τ) 0 := by
    have h1 := hasDerivAt_jacobiTheta₂_fst (0 + c) hτ0
    have h2 : HasDerivAt (fun u : ℂ => u + c) 1 0 := (hasDerivAt_id 0).add_const c
    have h3 := h1.comp (0 : ℂ) h2
    rw [mul_one] at h3
    exact h3
  have hd : HasDerivAt (fun u => cexp (A + B * (u + ((1 / 2 : ℝ) : ℂ))) * jacobiTheta₂ (u + c) τ)
      (cexp (A + B * (0 + ((1 / 2 : ℝ) : ℂ))) * B * jacobiTheta₂ (0 + c) τ +
        cexp (A + B * (0 + ((1 / 2 : ℝ) : ℂ))) * jacobiTheta₂' (0 + c) τ) 0 := hE.mul hJ
  rw [hform, hd.deriv]
  have hc : 0 + c = 1 / 2 + τ / 2 := by simp only [c]; push_cast; ring
  rw [hc, jacobiTheta₂_half_eq_zero, mul_zero, zero_add]
  exact mul_ne_zero (Complex.exp_ne_zero _) (jacobiTheta₂'_half_ne_zero_all hτ0)

theorem theta1_deriv_add_one {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) :
    deriv (fun v => theta1 v τ) (u + 1) = -deriv (fun v => theta1 v τ) u := by
  have h1 : HasDerivAt (fun v => theta1 (v + 1) τ) (deriv (fun v => theta1 v τ) (u + 1)) u :=
    HasDerivAt.comp_add_const u 1 (theta1_differentiable hτ (u + 1)).hasDerivAt
  have e : (fun v => theta1 (v + 1) τ) = fun v => -theta1 v τ := funext fun v => theta1_add_one v τ
  rw [e] at h1
  exact h1.unique (theta1_differentiable hτ u).hasDerivAt.neg

theorem theta1_deriv_add_tau {τ : ℂ} (hτ : 0 < τ.im) {u : ℂ} (hu : theta1 u τ = 0) :
    deriv (fun v => theta1 v τ) (u + τ) =
      -cexp (-π * I * τ - 2 * π * I * u) * deriv (fun v => theta1 v τ) u := by
  have h1 : HasDerivAt (fun v => theta1 (v + τ) τ) (deriv (fun v => theta1 v τ) (u + τ)) u :=
    HasDerivAt.comp_add_const u τ (theta1_differentiable hτ (u + τ)).hasDerivAt
  have e : (fun v => theta1 (v + τ) τ) = fun v => -cexp (-π * I * τ - 2 * π * I * v) * theta1 v τ :=
    funext fun v => theta1_add_tau v τ
  rw [e] at h1
  have hM : HasDerivAt (fun v : ℂ => -cexp (-π * I * τ - 2 * π * I * v))
      (deriv (fun v : ℂ => -cexp (-π * I * τ - 2 * π * I * v)) u) u :=
    (by fun_prop : Differentiable ℂ (fun v : ℂ => -cexp (-π * I * τ - 2 * π * I * v))) u |>.hasDerivAt
  have h2 := hM.mul (theta1_differentiable hτ u).hasDerivAt
  rw [h1.unique h2, hu, mul_zero, zero_add]

/-- **All zeros of `ϑ₁` are simple**: `ϑ₁'(p + qτ) ≠ 0` for all `p, q ∈ ℤ`, every `τ` in the upper
half-plane. With `theta1_eq_zero_iff` this is Lemma C.`theta`(c) in full. -/
theorem theta1_deriv_lattice_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (p q : ℤ) :
    deriv (fun u => theta1 u τ) (p + q * τ) ≠ 0 := by
  have hz : ∀ u, theta1 u τ = 0 → theta1 (u - τ) τ = 0 := by
    intro u hu
    have := theta1_add_tau (u - τ) τ
    rw [sub_add_cancel, hu] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (neg_ne_zero.mpr (Complex.exp_ne_zero _))
  have step1 : ∀ u, deriv (fun v => theta1 v τ) u ≠ 0 ↔ deriv (fun v => theta1 v τ) (u + 1) ≠ 0 := by
    intro u; rw [theta1_deriv_add_one hτ, neg_ne_zero]
  have step2 : ∀ u, theta1 u τ = 0 →
      (deriv (fun v => theta1 v τ) u ≠ 0 ↔ deriv (fun v => theta1 v τ) (u + τ) ≠ 0) := by
    intro u hu
    rw [theta1_deriv_add_tau hτ hu, mul_ne_zero_iff]
    simp [Complex.exp_ne_zero]
  have hq : ∀ q : ℤ, deriv (fun v => theta1 v τ) (q * τ) ≠ 0 := by
    intro q
    induction q using Int.induction_on with
    | zero => simpa using theta1_deriv_zero_ne_zero_all hτ
    | succ i ih =>
      rw [show ((i + 1 : ℤ) : ℂ) * τ = (i : ℤ) * τ + τ by push_cast; ring]
      exact (step2 _ (by simpa using theta1_lattice τ 0 i)).mp ih
    | pred i ih =>
      have hzero : theta1 (((-(i : ℤ) - 1 : ℤ) : ℂ) * τ) τ = 0 := by
        simpa using theta1_lattice τ 0 (-(i : ℤ) - 1)
      rw [step2 _ hzero]
      rw [show ((-(i : ℤ) - 1 : ℤ) : ℂ) * τ + τ = ((-(i : ℤ) : ℤ) : ℂ) * τ by push_cast; ring]
      exact ih
  induction p using Int.induction_on with
  | zero => simpa using hq q
  | succ i ih =>
    rw [show ((i + 1 : ℤ) : ℂ) + q * τ = ((i : ℤ) + q * τ) + 1 by push_cast; ring]
    exact (step1 _).mp ih
  | pred i ih =>
    rw [step1, show ((-(i : ℤ) - 1 : ℤ) : ℂ) + q * τ + 1 = ((-(i : ℤ) : ℤ) : ℂ) + q * τ by
      push_cast; ring]
    exact ih

end Product

end ThetaZeroDevices

end ThetaDev

/-- `ϑ₁` is entire. -/
theorem theta1_differentiable (τ : ℍ) : Differentiable ℂ fun u => theta1 u τ := by
  exact ThetaDev.theta1_differentiable τ.coe_im_pos

/-- **Lemma C.theta(c)**: "`Its zero set is exactly $\Lambda_u$, all zeros are simple,`" — the zero set (F0 proved it by
Jacobi's product, `theta1_eq_zero_iff`, without an argument principle). -/
theorem theta1_eq_zero_iff (τ : ℍ) (u : ℂ) : theta1 u τ = 0 ↔ u ∈ Λu τ := by
  exact ThetaDev.theta1_eq_zero_iff τ.coe_im_pos u

/-- **Lemma C.theta(c)**: "`Its zero set is exactly $\Lambda_u$, all zeros are simple,`" — the simplicity. -/
theorem theta1_deriv_ne_zero_of_mem (τ : ℍ) {u : ℂ} (hu : u ∈ Λu τ) : deriv (fun u => theta1 u τ) u ≠ 0 := by
  obtain ⟨p, q, rfl⟩ := hu
  exact ThetaDev.theta1_deriv_lattice_ne_zero τ.coe_im_pos p q

/-- **Lemma C.theta(c)**: "`and $\kzvth_1'(0)\neq0$.`" -/
theorem theta1_deriv_zero_ne_zero (τ : ℍ) : deriv (fun u => theta1 u τ) 0 ≠ 0 := by
  exact ThetaDev.theta1_deriv_zero_ne_zero_all τ.coe_im_pos

/-! ## The theta spaces: Lemma C.`theta`(a) and `Θ_2[ε]` -/

/-- **Lemma C.theta(a)**: the space `Θ_ℓ[a,b]` of "`entire $F$ with $F(U+1)=e^{2\pi ia}F(U)$ and $F(U+\tau)=e^{-2\pi ib}e^{-i\pi\ell(2U+\tau)}F(U)$`"
(F0's `thetaSpace`). -/
def thetaSpace (τ : ℂ) (a b : ℝ) (ℓ : ℕ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {F | Differentiable ℂ F ∧ (∀ U, F (U + 1) = cexp (2 * π * I * a) * F U) ∧
      ∀ U, F (U + τ) = cexp (-2 * π * I * b) * cexp (-π * I * ℓ * (2 * U + τ)) * F U}
  add_mem' := by
    rintro F G ⟨hF, hF1, hF2⟩ ⟨hG, hG1, hG2⟩
    refine ⟨hF.add hG, fun U => ?_, fun U => ?_⟩
    · simp only [Pi.add_apply, hF1, hG1]; ring
    · simp only [Pi.add_apply, hF2, hG2]; ring
  zero_mem' := ⟨differentiable_const 0, fun U => by simp, fun U => by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, hF1, hF2⟩
    refine ⟨hF.const_smul c, fun U => ?_, fun U => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hF1]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, hF2]; ring

/-- **Lemma C.theta(a)**: "`For $\ell\ge1$ and $a,b\in\R$, the space $\kzTh_\ell[a,b]$ of entire $F$ with $F(U+1)=e^{2\pi ia}F(U)$ and $F(U+\tau)=e^{-2\pi ib}e^{-i\pi\ell(2U+\tau)}F(U)$ has dimension $\ell$.`"
(F0: `finrank_thetaSpace`, for every `ℓ ≥ 1`.) -/
theorem finrank_thetaSpace (τ : ℍ) (a b : ℝ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    Module.finrank ℂ (thetaSpace τ a b ℓ) = ℓ := by
  exact ThetaDev.finrank_thetaSpaceDev τ.coe_im_pos a b hℓ

/-- The sign pairs `ε = (ε₁, ε₂) ∈ {±1}²`: `pp, mp, pm, mm` are `(1,1), (−1,1), (1,−1), (−1,−1)`. -/
inductive Eps
  | pp
  | mp
  | pm
  | mm
  deriving DecidableEq, Inhabited

/-- `Eps` is finite (written out, as block A's `Spin`). -/
instance : Fintype Eps where
  elems := {Eps.pp, Eps.mp, Eps.pm, Eps.mm}
  complete := by intro x; cases x <;> simp

/-- `ε₁ ∈ {±1}`. -/
def Eps.e1 : Eps → ℂ
  | .pp => 1
  | .mp => -1
  | .pm => 1
  | .mm => -1

/-- `ε₂ ∈ {±1}`. -/
def Eps.e2 : Eps → ℂ
  | .pp => 1
  | .mp => 1
  | .pm => -1
  | .mm => -1

/-- **Lemma C.B(b)**: "`let $\kzTh_2[\varepsilon]$ be the space of entire $F$ with $F(U+1)=\varepsilon_1^{-1}F(U)$ and $F(U+\tau)=\varepsilon_2^{-1}e^{-4\pi iU-2\pi i\tau}F(U)$. It is two-dimensional`"
— for `ε ∈ {±1}²`. -/
def Θ2 (τ : ℂ) (ε : Eps) : Submodule ℂ (ℂ → ℂ) where
  carrier := {F | Differentiable ℂ F ∧ (∀ U, F (U + 1) = (ε.e1)⁻¹ * F U) ∧
      ∀ U, F (U + τ) = (ε.e2)⁻¹ * cexp (-4 * π * I * U - 2 * π * I * τ) * F U}
  add_mem' := by
    rintro F G ⟨hF, hF1, hF2⟩ ⟨hG, hG1, hG2⟩
    refine ⟨hF.add hG, fun U => ?_, fun U => ?_⟩
    · simp only [Pi.add_apply, hF1, hG1]; ring
    · simp only [Pi.add_apply, hF2, hG2]; ring
  zero_mem' := ⟨differentiable_const 0, fun U => by simp, fun U => by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, hF1, hF2⟩
    refine ⟨hF.const_smul c, fun U => ?_, fun U => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hF1]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, hF2]; ring

/-! ### Proof devices for Lemma C.B(b)'s dimension (proof phase, round one; not statements of the paper):
`Θ_2[ε] = Θ_2[a, b]` with `e^{2πia} = ε₁⁻¹`, `e^{−2πib} = ε₂⁻¹` (the paper's own reduction) -/

theorem Θ2_eq_thetaSpace_dev (τ : ℂ) (ε : Eps) {a b : ℝ} (ha : cexp (2 * π * I * a) = (ε.e1)⁻¹)
    (hb : cexp (-2 * π * I * b) = (ε.e2)⁻¹) : Θ2 τ ε = thetaSpace τ a b 2 := by
  have hexp : ∀ U : ℂ, cexp (-π * I * ((2 : ℕ) : ℂ) * (2 * U + τ)) = cexp (-4 * π * I * U - 2 * π * I * τ) := by
    intro U; congr 1; push_cast; ring
  ext F
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, fun U => ?_, fun U => ?_⟩
    · rw [h1 U, ha]
    · rw [h2 U, hb, hexp]
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, fun U => ?_, fun U => ?_⟩
    · rw [h1 U, ha]
    · rw [h2 U, hb, hexp]

theorem Θ2_ab_dev (ε : Eps) :
    ∃ a b : ℝ, cexp (2 * π * I * a) = (ε.e1)⁻¹ ∧ cexp (-2 * π * I * b) = (ε.e2)⁻¹ := by
  have h0 : cexp (2 * π * I * ((0 : ℝ) : ℂ)) = 1 := by simp
  have h0' : cexp (-2 * π * I * ((0 : ℝ) : ℂ)) = 1 := by simp
  have h1 : cexp (2 * π * I * ((1 / 2 : ℝ) : ℂ)) = -1 := exp_two_pi_I_half_dev
  have h1' : cexp (-2 * π * I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    rw [show -2 * π * I * ((1 / 2 : ℝ) : ℂ) = -(π * I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    norm_num
  cases ε
  · exact ⟨0, 0, by rw [h0]; simp [Eps.e1], by rw [h0']; simp [Eps.e2]⟩
  · exact ⟨1 / 2, 0, by rw [h1]; simp [Eps.e1], by rw [h0']; simp [Eps.e2]⟩
  · exact ⟨0, 1 / 2, by rw [h0]; simp [Eps.e1], by rw [h1']; simp [Eps.e2]⟩
  · exact ⟨1 / 2, 1 / 2, by rw [h1]; simp [Eps.e1], by rw [h1']; simp [Eps.e2]⟩

/-- **Lemma C.B(b)**: "`It is two-dimensional`" (from Lemma C.theta(a) at `ℓ = 2`: "`$\kzTh_2[\varepsilon]=\kzTh_2[a,b]$ with $e^{2\pi ia}=\varepsilon_1^{-1}$ and $e^{-2\pi ib}=\varepsilon_2^{-1}$`"). -/
theorem finrank_Θ2 (τ : ℍ) (ε : Eps) : Module.finrank ℂ (Θ2 τ ε) = 2 := by
  obtain ⟨a, b, ha, hb⟩ := Θ2_ab_dev ε
  rw [Θ2_eq_thetaSpace_dev (τ : ℂ) ε ha hb]
  exact finrank_thetaSpace τ a b two_pos

/-! ## `℘` and `℘_ε`: Lemma C.`theta`(d)–(e) -/

/-- The period pair `(a, ω)` for real `a ≠ 0` and `Im ω > 0` (F0's `periodPairReal`). -/
def periodPairReal (a : ℝ) (ha : a ≠ 0) (ω : ℂ) (hω : 0 < ω.im) : PeriodPair where
  ω₁ := a
  ω₂ := ω
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have him := congrArg Complex.im hst
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero, Complex.zero_im] at him
    have ht : t = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact h
      · exact absurd h hω.ne'
    subst ht
    simp only [zero_smul, add_zero] at hst
    have hre := congrArg Complex.re hst
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      sub_zero, mul_zero, Complex.zero_re] at hre
    exact ⟨(mul_eq_zero.mp hre).resolve_right ha, rfl⟩

/-- The period pair `(1, τ)` of `Λ_u` (F0's `Lu`). -/
def Lu (τ : ℍ) : PeriodPair := periodPairReal 1 one_ne_zero τ τ.coe_im_pos

theorem im_add_self_pos (τ : ℍ) : 0 < ((τ : ℂ) + τ).im := by
  rw [Complex.add_im]
  linarith [τ.coe_im_pos]

theorem im_one_add_pos (τ : ℍ) : 0 < (1 + (τ : ℂ)).im := by
  rw [Complex.add_im, Complex.one_im, zero_add]
  exact τ.coe_im_pos

/-- The proof of Lemma C.theta(e): "`$\Lambda_\varepsilon:=\ker\chi_\varepsilon$ has index $2$ in $\Lambda_u$`" — a basis of
`Λ_ε`: `(2, τ)`, `(1, 2τ)`, `(2, 1 + τ)` for `ε = (−1,1), (1,−1), (−1,−1)` (and `(1, τ)` for `ε = (1,1)`, unused). -/
def Leps (τ : ℍ) : Eps → PeriodPair
  | .pp => Lu τ
  | .mp => periodPairReal 2 two_ne_zero τ τ.coe_im_pos
  | .pm => periodPairReal 1 one_ne_zero ((τ : ℂ) + τ) (im_add_self_pos τ)
  | .mm => periodPairReal 2 two_ne_zero (1 + (τ : ℂ)) (im_one_add_pos τ)

/-- `λ_ε ∈ Λ_u ∖ Λ_ε`: `1, τ, 1` for `ε = (−1,1), (1,−1), (−1,−1)` (and `0` for `(1,1)`, unused). -/
def lamEps (τ : ℍ) : Eps → ℂ
  | .pp => 0
  | .mp => 1
  | .pm => τ
  | .mm => 1

/-- `℘ := ` Mathlib's Weierstrass function of the period pair `(1, τ)` — not the paper's `−(log ϑ₁)''` (the module
docstring). -/
def wp (τ : ℍ) : ℂ → ℂ := (Lu τ).weierstrassP

/-- The proof of Lemma C.theta(e): "`$\wp_\varepsilon(u):=\wp^{(\varepsilon)}(u)-\wp^{(\varepsilon)}(u-\lambda_\varepsilon)$`", with
`℘^{(ε)}` Mathlib's `℘` of `Λ_ε`; and Proposition C.explicit's "`Write $\wp_{(1,1)}:=\wp$.`" -/
def wpE (τ : ℍ) : Eps → ℂ → ℂ
  | .pp => wp τ
  | ε => fun u => (Leps τ ε).weierstrassP u - (Leps τ ε).weierstrassP (u - lamEps τ ε)

/-! ### Proof devices for Lemma C.theta(d) (proof phase, round one; not statements of the paper): `Λ_u` is the lattice
of the period pair `(1, τ)`; F0's Laurent form of Mathlib's `℘` at `0` -/

theorem mem_lattice_Lu_dev (τ : ℍ) (l : ℂ) : l ∈ (Lu τ).lattice ↔ l ∈ Λu τ := by
  rw [PeriodPair.mem_lattice]
  show (∃ m n : ℤ, (m : ℂ) * ((1 : ℝ) : ℂ) + (n : ℂ) * (τ : ℂ) = l) ↔ ∃ p q : ℤ, l = p + q * (τ : ℂ)
  simp only [Complex.ofReal_one, mul_one]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, h.symm⟩
  · rintro ⟨p, q, h⟩
    exact ⟨p, q, h.symm⟩

theorem weierstrassP_sub_inv_sq_analyticAt_dev (L : PeriodPair) :
    AnalyticAt ℂ (fun u => L.weierstrassP u - 1 / u ^ 2) 0 := by
  -- F0's proof (`weierstrassP_sub_inv_sq_analyticAt`)
  have h0 : (0 : ℂ) ∈ L.lattice := zero_mem _
  have e : (fun u => L.weierstrassP u - 1 / u ^ 2) = L.weierstrassPExcept 0 := by
    funext u
    have := L.weierstrassPExcept_add ⟨0, h0⟩ u
    simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at this
    rw [← this]
    ring
  rw [e]
  exact L.analyticAt_weierstrassPExcept 0

/-- **Lemma C.theta(d)** in Mathlib's form: `℘` "`is meromorphic, even and doubly periodic, with poles exactly at $\Lambda_u$ and $\wp(u)=u^{-2}+O(1)$ at $0$ (no $u^{-1}$ term).`"
— meromorphic. -/
theorem wp_meromorphic (τ : ℍ) : Meromorphic (wp τ) := by
  exact (Lu τ).meromorphic_weierstrassP

/-- **Lemma C.theta(d)**: `℘` is even. -/
theorem wp_neg (τ : ℍ) (u : ℂ) : wp τ (-u) = wp τ u := by
  exact (Lu τ).weierstrassP_neg u

/-- **Lemma C.theta(d)**: `℘` is doubly periodic, `℘(u + 1) = ℘(u)`. -/
theorem wp_add_one (τ : ℍ) (u : ℂ) : wp τ (u + 1) = wp τ u := by
  have h : (Lu τ).weierstrassP (u + ((1 : ℝ) : ℂ)) = (Lu τ).weierstrassP u :=
    (Lu τ).weierstrassP_add_coe u ⟨_, (Lu τ).ω₁_mem_lattice⟩
  rw [Complex.ofReal_one] at h
  exact h

/-- **Lemma C.theta(d)**: `℘(u + τ) = ℘(u)`. -/
theorem wp_add_tau (τ : ℍ) (u : ℂ) : wp τ (u + τ) = wp τ u := by
  exact (Lu τ).weierstrassP_add_coe u ⟨_, (Lu τ).ω₂_mem_lattice⟩

/-- **Lemma C.theta(d)**: the poles are exactly the lattice points, each of order two (Mathlib's
`order_weierstrassP`, `analyticOnNhd_weierstrassP`). -/
theorem wp_order (τ : ℍ) {l : ℂ} (hl : l ∈ Λu τ) : meromorphicOrderAt (wp τ) l = -2 := by
  exact (Lu τ).order_weierstrassP l ((mem_lattice_Lu_dev τ l).2 hl)

/-- **Lemma C.theta(d)**: `℘` is analytic off `Λ_u`. -/
theorem wp_analyticAt (τ : ℍ) {u : ℂ} (hu : u ∉ Λu τ) : AnalyticAt ℂ (wp τ) u := by
  refine (Lu τ).analyticOnNhd_weierstrassP u ?_
  intro h
  exact hu ((mem_lattice_Lu_dev τ u).1 h)

/-- **Lemma C.theta(d)**: "`$\wp(u)=u^{-2}+O(1)$ at $0$ (no $u^{-1}$ term).`" — `℘ − u⁻²` is analytic at `0`. -/
theorem wp_sub_inv_sq_analyticAt (τ : ℍ) : AnalyticAt ℂ (fun u => wp τ u - 1 / u ^ 2) 0 := by
  exact weierstrassP_sub_inv_sq_analyticAt_dev (Lu τ)

/-! ### Proof devices for Lemma C.theta(e) (proof phase, round one; not statements of the paper)

The paper's construction: for a period pair `L` (here `Λ_ε`) and `λ` with `2λ ∈ L`, `λ ∉ L`, the function
`f(u) = ℘_L(u) − ℘_L(u − λ)` is even, `L`-periodic and changes sign under `u ↦ u + λ` (`wpDiff_*_dev`); the facts about
the three sublattices (`Leps_facts_dev`: `2λ_ε ∈ Λ_ε`, `λ_ε ∉ Λ_ε`, `Λ_ε ⊆ Λ_u ∋ λ_ε`, and `Λ_u = Λ_ε ∪ (λ_ε + Λ_ε)`) are
computed in coordinates with `int_combo_eq_dev` (the independence of `1, τ` over `ℤ`); the multipliers on `ℤ + τℤ` follow
from those of the generators by induction (`shift_int_dev`). -/

theorem int_combo_eq_dev (τ : ℍ) {a b c d : ℤ} (h : (a : ℂ) + b * (τ : ℂ) = c + d * (τ : ℂ)) : a = c ∧ b = d := by
  have hτ : 0 < (τ : ℂ).im := τ.coe_im_pos
  have him : (b : ℝ) * (τ : ℂ).im = d * (τ : ℂ).im := by
    have := congrArg Complex.im h
    simpa [Complex.add_im, Complex.mul_im] using this
  have hbd : b = d := by exact_mod_cast mul_right_cancel₀ hτ.ne' him
  subst hbd
  have hac : (a : ℂ) = c := by linear_combination h
  exact ⟨by exact_mod_cast hac, rfl⟩

theorem wpDiff_add_lam_dev (L : PeriodPair) {lam : ℂ} (h2 : 2 * lam ∈ L.lattice) (u : ℂ) :
    L.weierstrassP (u + lam) - L.weierstrassP (u + lam - lam) =
      -(L.weierstrassP u - L.weierstrassP (u - lam)) := by
  have h : L.weierstrassP ((u - lam) + 2 * lam) = L.weierstrassP (u - lam) :=
    L.weierstrassP_add_coe (u - lam) ⟨_, h2⟩
  rw [show u + lam = (u - lam) + 2 * lam by ring, h, show u - lam + 2 * lam - lam = u by ring]
  ring

theorem wpDiff_add_mem_dev (L : PeriodPair) (lam : ℂ) {l : ℂ} (hl : l ∈ L.lattice) (u : ℂ) :
    L.weierstrassP (u + l) - L.weierstrassP (u + l - lam) = L.weierstrassP u - L.weierstrassP (u - lam) := by
  have h1 : L.weierstrassP (u + l) = L.weierstrassP u := L.weierstrassP_add_coe u ⟨l, hl⟩
  have h2 : L.weierstrassP ((u - lam) + l) = L.weierstrassP (u - lam) := L.weierstrassP_add_coe (u - lam) ⟨l, hl⟩
  rw [h1, show u + l - lam = (u - lam) + l by ring, h2]

theorem wpDiff_neg_dev (L : PeriodPair) {lam : ℂ} (h2 : 2 * lam ∈ L.lattice) (u : ℂ) :
    L.weierstrassP (-u) - L.weierstrassP (-u - lam) = L.weierstrassP u - L.weierstrassP (u - lam) := by
  have h : L.weierstrassP ((u - lam) + 2 * lam) = L.weierstrassP (u - lam) :=
    L.weierstrassP_add_coe (u - lam) ⟨_, h2⟩
  rw [L.weierstrassP_neg, show -u - lam = -(u + lam) by ring, L.weierstrassP_neg,
    show u + lam = (u - lam) + 2 * lam by ring, h]

theorem wpE_eq_dev (τ : ℍ) {ε : Eps} (hε : ε ≠ .pp) :
    wpE τ ε = fun u => (Leps τ ε).weierstrassP u - (Leps τ ε).weierstrassP (u - lamEps τ ε) := by
  cases ε
  · exact absurd rfl hε
  all_goals rfl

theorem Leps_facts_dev (τ : ℍ) {ε : Eps} (hε : ε ≠ .pp) :
    2 * lamEps τ ε ∈ (Leps τ ε).lattice ∧ lamEps τ ε ∉ (Leps τ ε).lattice ∧
      (∀ l, l ∈ (Leps τ ε).lattice → l ∈ Λu τ) ∧ lamEps τ ε ∈ Λu τ ∧
      (∀ l ∈ Λu τ, l ∈ (Leps τ ε).lattice ∨ l - lamEps τ ε ∈ (Leps τ ε).lattice) := by
  cases ε
  · exact absurd rfl hε
  · -- `Λ_ε = 2ℤ + τℤ`, `λ_ε = 1`
    refine ⟨PeriodPair.mem_lattice.2 ⟨1, 0, ?_⟩, ?_, ?_, ⟨1, 0, by simp [lamEps]⟩, ?_⟩
    · show ((1 : ℤ) : ℂ) * ((2 : ℝ) : ℂ) + ((0 : ℤ) : ℂ) * (τ : ℂ) = 2 * 1
      push_cast; ring
    · intro h
      obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 h
      have e' : ((2 * m : ℤ) : ℂ) + (n : ℂ) * (τ : ℂ) = ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * (τ : ℂ) := by
        have e0 : (m : ℂ) * ((2 : ℝ) : ℂ) + (n : ℂ) * (τ : ℂ) = 1 := e
        push_cast at e0 ⊢; linear_combination e0
      have := (int_combo_eq_dev τ e').1
      omega
    · intro l h
      obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 h
      refine ⟨2 * m, n, ?_⟩
      have e0 : (m : ℂ) * ((2 : ℝ) : ℂ) + (n : ℂ) * (τ : ℂ) = l := e
      push_cast at e0 ⊢; linear_combination -e0
    · rintro l ⟨p, q, rfl⟩
      obtain ⟨k, hk | hk⟩ := Int.even_or_odd' p
      · left
        refine PeriodPair.mem_lattice.2 ⟨k, q, ?_⟩
        show (k : ℂ) * ((2 : ℝ) : ℂ) + (q : ℂ) * (τ : ℂ) = (p : ℂ) + (q : ℂ) * (τ : ℂ)
        rw [hk]; push_cast; ring
      · right
        refine PeriodPair.mem_lattice.2 ⟨k, q, ?_⟩
        show (k : ℂ) * ((2 : ℝ) : ℂ) + (q : ℂ) * (τ : ℂ) = (p : ℂ) + (q : ℂ) * (τ : ℂ) - 1
        rw [hk]; push_cast; ring
  · -- `Λ_ε = ℤ + 2τℤ`, `λ_ε = τ`
    refine ⟨PeriodPair.mem_lattice.2 ⟨0, 1, ?_⟩, ?_, ?_, ⟨0, 1, by simp [lamEps]⟩, ?_⟩
    · show ((0 : ℤ) : ℂ) * ((1 : ℝ) : ℂ) + ((1 : ℤ) : ℂ) * ((τ : ℂ) + τ) = 2 * (τ : ℂ)
      push_cast; ring
    · intro h
      obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 h
      have e' : ((m : ℤ) : ℂ) + ((2 * n : ℤ) : ℂ) * (τ : ℂ) = ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * (τ : ℂ) := by
        have e0 : (m : ℂ) * ((1 : ℝ) : ℂ) + (n : ℂ) * ((τ : ℂ) + τ) = τ := e
        push_cast at e0 ⊢; linear_combination e0
      have := (int_combo_eq_dev τ e').2
      omega
    · intro l h
      obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 h
      refine ⟨m, 2 * n, ?_⟩
      have e0 : (m : ℂ) * ((1 : ℝ) : ℂ) + (n : ℂ) * ((τ : ℂ) + τ) = l := e
      push_cast at e0 ⊢; linear_combination -e0
    · rintro l ⟨p, q, rfl⟩
      obtain ⟨k, hk | hk⟩ := Int.even_or_odd' q
      · left
        refine PeriodPair.mem_lattice.2 ⟨p, k, ?_⟩
        show (p : ℂ) * ((1 : ℝ) : ℂ) + (k : ℂ) * ((τ : ℂ) + τ) = (p : ℂ) + (q : ℂ) * (τ : ℂ)
        rw [hk]; push_cast; ring
      · right
        refine PeriodPair.mem_lattice.2 ⟨p, k, ?_⟩
        show (p : ℂ) * ((1 : ℝ) : ℂ) + (k : ℂ) * ((τ : ℂ) + τ) = (p : ℂ) + (q : ℂ) * (τ : ℂ) - τ
        rw [hk]; push_cast; ring
  · -- `Λ_ε = 2ℤ + (1 + τ)ℤ`, `λ_ε = 1`
    refine ⟨PeriodPair.mem_lattice.2 ⟨1, 0, ?_⟩, ?_, ?_, ⟨1, 0, by simp [lamEps]⟩, ?_⟩
    · show ((1 : ℤ) : ℂ) * ((2 : ℝ) : ℂ) + ((0 : ℤ) : ℂ) * (1 + (τ : ℂ)) = 2 * 1
      push_cast; ring
    · intro h
      obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 h
      have e' : ((2 * m + n : ℤ) : ℂ) + (n : ℂ) * (τ : ℂ) = ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * (τ : ℂ) := by
        have e0 : (m : ℂ) * ((2 : ℝ) : ℂ) + (n : ℂ) * (1 + (τ : ℂ)) = 1 := e
        push_cast at e0 ⊢; linear_combination e0
      have h1 := int_combo_eq_dev τ e'
      omega
    · intro l h
      obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 h
      refine ⟨2 * m + n, n, ?_⟩
      have e0 : (m : ℂ) * ((2 : ℝ) : ℂ) + (n : ℂ) * (1 + (τ : ℂ)) = l := e
      push_cast at e0 ⊢; linear_combination -e0
    · rintro l ⟨p, q, rfl⟩
      obtain ⟨k, hk | hk⟩ := Int.even_or_odd' (p - q)
      · left
        refine PeriodPair.mem_lattice.2 ⟨k, q, ?_⟩
        show (k : ℂ) * ((2 : ℝ) : ℂ) + (q : ℂ) * (1 + (τ : ℂ)) = (p : ℂ) + (q : ℂ) * (τ : ℂ)
        have hp : p = 2 * k + q := by omega
        rw [hp]; push_cast; ring
      · right
        refine PeriodPair.mem_lattice.2 ⟨k, q, ?_⟩
        show (k : ℂ) * ((2 : ℝ) : ℂ) + (q : ℂ) * (1 + (τ : ℂ)) = (p : ℂ) + (q : ℂ) * (τ : ℂ) - 1
        have hp : p = 2 * k + 1 + q := by omega
        rw [hp]; push_cast; ring

theorem shift_int_dev {f : ℂ → ℂ} {w c : ℂ} (hc : c ≠ 0) (h : ∀ u, f (u + w) = c * f u) (u : ℂ) (p : ℤ) :
    f (u + p * w) = c ^ p * f u := by
  induction p using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show u + ((k : ℤ) + 1 : ℤ) * w = (u + ((k : ℤ) : ℂ) * w) + w by push_cast; ring, h, ih,
      zpow_add_one₀ hc]
    ring
  | pred k ih =>
    have h' := h (u + ((-(k : ℤ) - 1 : ℤ) : ℂ) * w)
    rw [show u + ((-(k : ℤ) - 1 : ℤ) : ℂ) * w + w = u + ((-(k : ℤ) : ℤ) : ℂ) * w by push_cast; ring, ih] at h'
    rw [zpow_sub_one₀ hc, show c ^ (-(k : ℤ)) * c⁻¹ * f u = c⁻¹ * (c ^ (-(k : ℤ)) * f u) by ring, h',
      ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem Eps_e1_ne_zero_dev (ε : Eps) : ε.e1 ≠ 0 := by cases ε <;> norm_num [Eps.e1]

theorem Eps_e2_ne_zero_dev (ε : Eps) : ε.e2 ≠ 0 := by cases ε <;> norm_num [Eps.e2]

theorem neg_two_lt_zero_dev : (-2 : WithTop ℤ) < 0 := by
  have h : ((-2 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) := WithTop.coe_lt_coe.2 (by norm_num)
  have e1 : ((-2 : ℤ) : WithTop ℤ) = -2 := by norm_num
  rw [e1, WithTop.coe_zero] at h
  exact h

theorem wpE_add_one_dev (τ : ℍ) (ε : Eps) (u : ℂ) : wpE τ ε (u + 1) = ε.e1 * wpE τ ε u := by
  cases ε
  · show wp τ (u + 1) = 1 * wp τ u
    rw [one_mul, wp_add_one]
  · show (Leps τ .mp).weierstrassP (u + 1) - (Leps τ .mp).weierstrassP (u + 1 - 1) =
      -1 * ((Leps τ .mp).weierstrassP u - (Leps τ .mp).weierstrassP (u - 1))
    rw [neg_one_mul]
    exact wpDiff_add_lam_dev (Leps τ .mp) (Leps_facts_dev τ (ε := .mp) (by decide)).1 u
  · show (Leps τ .pm).weierstrassP (u + 1) - (Leps τ .pm).weierstrassP (u + 1 - τ) =
      1 * ((Leps τ .pm).weierstrassP u - (Leps τ .pm).weierstrassP (u - τ))
    rw [one_mul]
    refine wpDiff_add_mem_dev (Leps τ .pm) _ ?_ u
    have h : ((1 : ℝ) : ℂ) ∈ (Leps τ .pm).lattice := (Leps τ .pm).ω₁_mem_lattice
    rwa [Complex.ofReal_one] at h
  · show (Leps τ .mm).weierstrassP (u + 1) - (Leps τ .mm).weierstrassP (u + 1 - 1) =
      -1 * ((Leps τ .mm).weierstrassP u - (Leps τ .mm).weierstrassP (u - 1))
    rw [neg_one_mul]
    exact wpDiff_add_lam_dev (Leps τ .mm) (Leps_facts_dev τ (ε := .mm) (by decide)).1 u

theorem wpE_add_tau_dev (τ : ℍ) (ε : Eps) (u : ℂ) : wpE τ ε (u + τ) = ε.e2 * wpE τ ε u := by
  cases ε
  · show wp τ (u + τ) = 1 * wp τ u
    rw [one_mul, wp_add_tau]
  · show (Leps τ .mp).weierstrassP (u + τ) - (Leps τ .mp).weierstrassP (u + τ - 1) =
      1 * ((Leps τ .mp).weierstrassP u - (Leps τ .mp).weierstrassP (u - 1))
    rw [one_mul]
    exact wpDiff_add_mem_dev (Leps τ .mp) _ (Leps τ .mp).ω₂_mem_lattice u
  · show (Leps τ .pm).weierstrassP (u + τ) - (Leps τ .pm).weierstrassP (u + τ - τ) =
      -1 * ((Leps τ .pm).weierstrassP u - (Leps τ .pm).weierstrassP (u - τ))
    rw [neg_one_mul]
    exact wpDiff_add_lam_dev (Leps τ .pm) (Leps_facts_dev τ (ε := .pm) (by decide)).1 u
  · -- `u + τ = (u + 1) + ((1 + τ) − 2)` with `(1 + τ) − 2 ∈ Λ_ε`
    have hl : (1 + (τ : ℂ)) - 2 ∈ (Leps τ .mm).lattice :=
      PeriodPair.mem_lattice.2 ⟨-1, 1, by
        show ((-1 : ℤ) : ℂ) * ((2 : ℝ) : ℂ) + ((1 : ℤ) : ℂ) * (1 + (τ : ℂ)) = (1 + (τ : ℂ)) - 2
        push_cast; ring⟩
    show (Leps τ .mm).weierstrassP (u + τ) - (Leps τ .mm).weierstrassP (u + τ - 1) =
      -1 * ((Leps τ .mm).weierstrassP u - (Leps τ .mm).weierstrassP (u - 1))
    have h1 := wpDiff_add_mem_dev (Leps τ .mm) 1 hl (u + 1)
    have h2 := wpDiff_add_lam_dev (Leps τ .mm) (Leps_facts_dev τ (ε := .mm) (by decide)).1 u
    rw [show u + 1 + (1 + (τ : ℂ) - 2) = u + τ by ring] at h1
    rw [h1, neg_one_mul]
    exact h2

/-- **Lemma C.theta(e)**: "`For $\varepsilon\in\{\pm1\}^2\setminus\{(1,1)\}$ let $\chi_\varepsilon(p+q\tau):=\varepsilon_1^p\varepsilon_2^q$ on $\Lambda_u$.`"
"`There is an even meromorphic $\wp_\varepsilon$ with $\wp_\varepsilon(u+\lambda)=\chi_\varepsilon(\lambda)\wp_\varepsilon(u)$ ($\lambda\in\Lambda_u$), poles exactly at $\Lambda_u$, and $\wp_\varepsilon(u)=u^{-2}+O(1)$ at $0$.`"
— meromorphic. -/
theorem wpE_meromorphic (τ : ℍ) (ε : Eps) : Meromorphic (wpE τ ε) := by
  by_cases hε : ε = .pp
  · subst hε
    exact wp_meromorphic τ
  · rw [wpE_eq_dev τ hε]
    intro x
    exact ((Leps τ ε).meromorphic_weierstrassP x).sub
      (((Leps τ ε).meromorphic_weierstrassP (x - lamEps τ ε)).comp_analyticAt
        (g := fun u => u - lamEps τ ε) (by fun_prop))

/-- **Lemma C.theta(e)**: `℘_ε` is even (also for `ε = (1,1)`, by (d)). -/
theorem wpE_neg (τ : ℍ) (ε : Eps) (u : ℂ) : wpE τ ε (-u) = wpE τ ε u := by
  by_cases hε : ε = .pp
  · subst hε
    exact wp_neg τ u
  · rw [wpE_eq_dev τ hε]
    exact wpDiff_neg_dev (Leps τ ε) (Leps_facts_dev τ hε).1 u

/-- **Lemma C.theta(e)**: "`$\wp_\varepsilon(u+\lambda)=\chi_\varepsilon(\lambda)\wp_\varepsilon(u)$`" for `λ = p + qτ`,
`χ_ε(λ) = ε₁^p ε₂^q` (also for `ε = (1,1)`, by (d)). -/
theorem wpE_add_lattice (τ : ℍ) (ε : Eps) (u : ℂ) (p q : ℤ) :
    wpE τ ε (u + (p + q * (τ : ℂ))) = ε.e1 ^ p * ε.e2 ^ q * wpE τ ε u := by
  have hp := shift_int_dev (Eps_e1_ne_zero_dev ε) (w := 1) (fun v => wpE_add_one_dev τ ε v)
  have hq := shift_int_dev (Eps_e2_ne_zero_dev ε) (w := (τ : ℂ)) (fun v => wpE_add_tau_dev τ ε v)
  rw [show u + ((p : ℂ) + (q : ℂ) * (τ : ℂ)) = (u + (q : ℂ) * (τ : ℂ)) + (p : ℂ) * 1 by ring, hp, hq]
  ring

/-- **Lemma C.theta(e)**: the multiplier under `u ↦ u + 1`. -/
theorem wpE_add_one (τ : ℍ) (ε : Eps) (u : ℂ) : wpE τ ε (u + 1) = ε.e1 * wpE τ ε u := by
  exact wpE_add_one_dev τ ε u

/-- **Lemma C.theta(e)**: the multiplier under `u ↦ u + τ`. -/
theorem wpE_add_tau (τ : ℍ) (ε : Eps) (u : ℂ) : wpE τ ε (u + τ) = ε.e2 * wpE τ ε u := by
  exact wpE_add_tau_dev τ ε u

/-- **Lemma C.theta(e)**: "`poles exactly at $\Lambda_u$`" — order `−2` at every point of `Λ_u` (for `ε ≠ (1,1)`; for
`ε = (1,1)` this is `wp_order`). -/
theorem wpE_order (τ : ℍ) {ε : Eps} (hε : ε ≠ .pp) {l : ℂ} (hl : l ∈ Λu τ) :
    meromorphicOrderAt (wpE τ ε) l = -2 := by
  obtain ⟨-, hlam, -, -, hsplit⟩ := Leps_facts_dev τ hε
  have hfun : wpE τ ε = (Leps τ ε).weierstrassP +
      fun u => -((Leps τ ε).weierstrassP ∘ fun v => v - lamEps τ ε) u := by
    rw [wpE_eq_dev τ hε]
    funext u
    simp [sub_eq_add_neg]
  have hmer2 : MeromorphicAt (fun u => -((Leps τ ε).weierstrassP ∘ fun v => v - lamEps τ ε) u) l :=
    (((Leps τ ε).meromorphic_weierstrassP (l - lamEps τ ε)).comp_analyticAt
      (g := fun v => v - lamEps τ ε) (by fun_prop)).neg
  have hord2 : meromorphicOrderAt (fun u => -((Leps τ ε).weierstrassP ∘ fun v => v - lamEps τ ε) u) l =
      meromorphicOrderAt (Leps τ ε).weierstrassP (l - lamEps τ ε) := by
    rw [show (fun u => -((Leps τ ε).weierstrassP ∘ fun v => v - lamEps τ ε) u) =
        -((Leps τ ε).weierstrassP ∘ fun v => v - lamEps τ ε) from rfl, ← meromorphicOrderAt_neg,
      meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt]
  rw [hfun]
  rcases hsplit l hl with hL | hL
  · -- `l ∈ Λ_ε`: the pole of the first term
    have hnot : l - lamEps τ ε ∉ (Leps τ ε).lattice := fun h => hlam (by
      have := (Leps τ ε).lattice.sub_mem hL h
      simpa using this)
    have hA : AnalyticAt ℂ (Leps τ ε).weierstrassP (l - lamEps τ ε) :=
      (Leps τ ε).analyticOnNhd_weierstrassP _ hnot
    rw [meromorphicOrderAt_add_eq_left_of_lt hmer2 (by
      rw [hord2, (Leps τ ε).order_weierstrassP l hL]
      exact lt_of_lt_of_le neg_two_lt_zero_dev hA.meromorphicOrderAt_nonneg)]
    exact (Leps τ ε).order_weierstrassP l hL
  · -- `l − λ_ε ∈ Λ_ε`: the pole of the second term
    have hnot : l ∉ (Leps τ ε).lattice := fun h => hlam (by
      have := (Leps τ ε).lattice.sub_mem h hL
      simpa using this)
    have hA : AnalyticAt ℂ (Leps τ ε).weierstrassP l := (Leps τ ε).analyticOnNhd_weierstrassP _ hnot
    rw [meromorphicOrderAt_add_eq_right_of_lt ((Leps τ ε).meromorphic_weierstrassP l) (by
      rw [hord2, (Leps τ ε).order_weierstrassP _ hL]
      exact lt_of_lt_of_le neg_two_lt_zero_dev hA.meromorphicOrderAt_nonneg), hord2]
    exact (Leps τ ε).order_weierstrassP _ hL

/-- **Lemma C.theta(e)**: `℘_ε` is analytic off `Λ_u`. -/
theorem wpE_analyticAt (τ : ℍ) (ε : Eps) {u : ℂ} (hu : u ∉ Λu τ) : AnalyticAt ℂ (wpE τ ε) u := by
  by_cases hε : ε = .pp
  · subst hε
    exact wp_analyticAt τ hu
  · obtain ⟨-, -, hsub, hlamU, -⟩ := Leps_facts_dev τ hε
    rw [wpE_eq_dev τ hε]
    have h1 : u ∉ (Leps τ ε).lattice := fun h => hu (hsub u h)
    have h2 : u - lamEps τ ε ∉ (Leps τ ε).lattice := fun h => hu (by
      obtain ⟨p, q, hpq⟩ := hsub _ h
      obtain ⟨p', q', hpq'⟩ := hlamU
      refine ⟨p + p', q + q', ?_⟩
      rw [show u = (u - lamEps τ ε) + lamEps τ ε by ring, hpq, hpq']
      push_cast
      ring)
    exact ((Leps τ ε).analyticOnNhd_weierstrassP u h1).sub
      (AnalyticAt.comp (f := fun v => v - lamEps τ ε) (x := u)
        ((Leps τ ε).analyticOnNhd_weierstrassP (u - lamEps τ ε) h2) (by fun_prop))

/-- **Lemma C.theta(e)**: "`$\wp_\varepsilon(u)=u^{-2}+O(1)$ at $0$.`" — `℘_ε − u⁻²` is analytic at `0` (F0 proved it for
`ε = (−1,1)`, `wpEps_sub_inv_sq_analyticAt`). -/
theorem wpE_sub_inv_sq_analyticAt (τ : ℍ) (ε : Eps) : AnalyticAt ℂ (fun u => wpE τ ε u - 1 / u ^ 2) 0 := by
  by_cases hε : ε = .pp
  · subst hε
    exact wp_sub_inv_sq_analyticAt τ
  · obtain ⟨-, hlam, -, -, -⟩ := Leps_facts_dev τ hε
    have h1 := weierstrassP_sub_inv_sq_analyticAt_dev (Leps τ ε)
    have hm : (0 : ℂ) - lamEps τ ε ∉ (Leps τ ε).lattice := by
      rw [zero_sub, neg_mem_iff]
      exact hlam
    have h2 : AnalyticAt ℂ (fun u => (Leps τ ε).weierstrassP (u - lamEps τ ε)) 0 :=
      AnalyticAt.comp (f := fun v => v - lamEps τ ε) (x := 0)
        ((Leps τ ε).analyticOnNhd_weierstrassP _ hm) (by fun_prop)
    have e : (fun u => wpE τ ε u - 1 / u ^ 2) =
        fun u => ((Leps τ ε).weierstrassP u - 1 / u ^ 2) - (Leps τ ε).weierstrassP (u - lamEps τ ε) := by
      funext u
      simp only [wpE_eq_dev τ hε]
      ring
    rw [e]
    exact h1.sub h2

/-! ## The Osgood class and `J`: Lemma C.`theta`(f) -/

/-- **The Osgood class** (F0's `IsOsgood2`, generalized from `ℂ × ℂ` to `ι → ℂ`): `f` is continuous and entire in each
variable separately — the carrier of "entire on `ℂ^N`" in this block. -/
def IsOsgood {ι : Type*} [DecidableEq ι] (f : (ι → ℂ) → ℂ) : Prop :=
  Continuous f ∧ ∀ (u : ι → ℂ) (i : ι), Differentiable ℂ fun z => f (Function.update u i z)

/-- **Lemma C.theta(f)**: "`$J:=\prod_{i<j}\kzvth_1(u_i-u_j)$ on $\C^N$`". -/
def Jfun (τ : ℂ) {N : ℕ} (u : Fin N → ℂ) : ℂ :=
  ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j : Fin N => i < j), theta1 (u i - u j) τ

/-! ### Proof devices for Lemma C.theta(f) (proof phase, round one; not statements of the paper): `J` as a product
over the pairs `i < j` (`pairsLT_dev`), the sorting of a pair (`sortPair_dev`) for the action of a permutation, and the
coordinate functions `z ↦ (u with u_i := z)_a` -/

/-- The pairs `(i, j)` with `i < j`. -/
def pairsLT_dev (N : ℕ) : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2

/-- A pair put in increasing order. -/
def sortPair_dev {N : ℕ} (q : Fin N × Fin N) : Fin N × Fin N := if q.1 < q.2 then q else (q.2, q.1)

theorem mem_pairsLT_dev {N : ℕ} (p : Fin N × Fin N) : p ∈ pairsLT_dev N ↔ p.1 < p.2 := by
  simp [pairsLT_dev]

theorem prod_pairsLT_dev {N : ℕ} (g : Fin N → Fin N → ℂ) :
    ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j : Fin N => i < j), g i j = ∏ p ∈ pairsLT_dev N, g p.1 p.2 := by
  symm
  apply Finset.prod_finset_product (pairsLT_dev N) Finset.univ (fun i => Finset.univ.filter (fun j : Fin N => i < j))
  intro p
  simp [pairsLT_dev]

theorem Jfun_eq_pairs_dev (τ : ℂ) {N : ℕ} (u : Fin N → ℂ) :
    Jfun τ u = ∏ p ∈ pairsLT_dev N, theta1 (u p.1 - u p.2) τ :=
  prod_pairsLT_dev (fun i j => theta1 (u i - u j) τ)

theorem theta1_sq_neg_dev (w τ : ℂ) : theta1 (-w) τ ^ 2 = theta1 w τ ^ 2 := by
  rw [theta1_neg]; ring

theorem sortPair_mem_dev {N : ℕ} {q : Fin N × Fin N} (hq : q.1 ≠ q.2) : sortPair_dev q ∈ pairsLT_dev N := by
  rw [mem_pairsLT_dev]
  unfold sortPair_dev
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hq)

theorem sortPair_perm_dev {N : ℕ} (σ : Equiv.Perm (Fin N)) {p : Fin N × Fin N} (hp : p.1 < p.2) :
    sortPair_dev (σ.symm (sortPair_dev (σ p.1, σ p.2)).1, σ.symm (sortPair_dev (σ p.1, σ p.2)).2) = p := by
  have hp' : ¬ p.2 < p.1 := not_lt.mpr hp.le
  by_cases h : σ p.1 < σ p.2
  · simp only [sortPair_dev, h, ite_true, Equiv.symm_apply_apply, hp, Prod.mk.eta]
  · simp only [sortPair_dev, h, ite_false, Equiv.symm_apply_apply, hp']

theorem differentiable_update_apply_dev {ι : Type*} [DecidableEq ι] (u : ι → ℂ) (i a : ι) :
    Differentiable ℂ fun z : ℂ => Function.update u i z a := by
  by_cases h : a = i
  · subst h
    simp
  · simp [Function.update_of_ne h]

/-- **Lemma C.theta(f)**: "`$J^2$ is symmetric under all permutations and invariant under $u\mapsto u+c\one$`" — the symmetry. -/
theorem Jfun_sq_perm (τ : ℂ) {N : ℕ} (σ : Equiv.Perm (Fin N)) (u : Fin N → ℂ) :
    Jfun τ (u ∘ σ) ^ 2 = Jfun τ u ^ 2 := by
  rw [Jfun_eq_pairs_dev, Jfun_eq_pairs_dev, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_nbij' (fun p => sortPair_dev (σ p.1, σ p.2))
    (fun q => sortPair_dev (σ.symm q.1, σ.symm q.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_pairsLT_dev] at hp
    exact sortPair_mem_dev fun h => (ne_of_lt hp) (σ.injective h)
  · intro q hq
    rw [mem_pairsLT_dev] at hq
    exact sortPair_mem_dev fun h => (ne_of_lt hq) (σ.symm.injective h)
  · intro p hp
    exact sortPair_perm_dev σ ((mem_pairsLT_dev p).1 hp)
  · intro q hq
    have := sortPair_perm_dev σ.symm ((mem_pairsLT_dev q).1 hq)
    simpa only [Equiv.symm_symm] using this
  · intro p _
    by_cases h : σ p.1 < σ p.2
    · simp only [sortPair_dev, h, ite_true, Function.comp]
    · simp only [sortPair_dev, h, ite_false, Function.comp]
      rw [← theta1_sq_neg_dev, neg_sub]

/-- **Lemma C.theta(f)**: the invariance under `u ↦ u + c𝟙`. -/
theorem Jfun_sq_add_const (τ : ℂ) {N : ℕ} (u : Fin N → ℂ) (c : ℂ) :
    Jfun τ (fun i => u i + c) ^ 2 = Jfun τ u ^ 2 := by
  have h : Jfun τ (fun i => u i + c) = Jfun τ u := by
    unfold Jfun
    simp only [add_sub_add_right_eq_sub]
  rw [h]

/-- **Lemma C.theta(f)**: "`$J^2(u+e_k)=J^2(u)$`". -/
theorem Jfun_sq_add_one (τ : ℂ) {N : ℕ} (u : Fin N → ℂ) (k : Fin N) :
    Jfun τ (Function.update u k (u k + 1)) ^ 2 = Jfun τ u ^ 2 := by
  rw [Jfun_eq_pairs_dev, Jfun_eq_pairs_dev, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [mem_pairsLT_dev] at hp
  have hne : p.1 ≠ p.2 := ne_of_lt hp
  by_cases h1 : p.1 = k
  · have h2 : p.2 ≠ k := fun h => hne (h1.trans h.symm)
    rw [h1, Function.update_self, Function.update_of_ne h2,
      show u k + 1 - u p.2 = (u k - u p.2) + 1 by ring, theta1_add_one]
    ring
  · by_cases h2 : p.2 = k
    · rw [h2, Function.update_self, Function.update_of_ne h1, show u p.1 - (u k + 1) = (u p.1 - u k) - 1 by ring]
      have h := theta1_add_one (u p.1 - u k - 1) τ
      rw [sub_add_cancel] at h
      rw [show theta1 (u p.1 - u k - 1) τ = -theta1 (u p.1 - u k) τ by rw [h]; ring]
      ring
    · rw [Function.update_of_ne h1, Function.update_of_ne h2]

/-- **Lemma C.theta(f)**: "`$J^2(u+\tau e_k)=e^{-2\pi i(N-1)\tau-4\pi i(Nu_k-U)}J^2(u)$`", with `U = Σ_i u_i`. -/
theorem Jfun_sq_add_tau (τ : ℂ) {N : ℕ} (u : Fin N → ℂ) (k : Fin N) :
    Jfun τ (Function.update u k (u k + τ)) ^ 2 =
      cexp (-2 * π * I * ((N : ℂ) - 1) * τ - 4 * π * I * ((N : ℂ) * u k - ∑ i, u i)) * Jfun τ u ^ 2 := by
  set E : Fin N → ℂ := fun v => -2 * π * I * τ - 4 * π * I * (u k - u v) with hE
  -- each factor
  have hfac : ∀ p ∈ pairsLT_dev N,
      theta1 (Function.update u k (u k + τ) p.1 - Function.update u k (u k + τ) p.2) τ ^ 2 =
        cexp ((if p.1 = k then E p.2 else 0) + (if p.2 = k then E p.1 else 0)) * theta1 (u p.1 - u p.2) τ ^ 2 := by
    intro p hp
    rw [mem_pairsLT_dev] at hp
    have hne : p.1 ≠ p.2 := ne_of_lt hp
    by_cases h1 : p.1 = k
    · have h2 : p.2 ≠ k := fun h => hne (h1.trans h.symm)
      rw [ite_eq_left h1, ite_eq_right h2, add_zero, h1, Function.update_self, Function.update_of_ne h2,
        show u k + τ - u p.2 = (u k - u p.2) + τ by ring, theta1_add_tau, mul_pow, neg_sq,
        ← Complex.exp_nat_mul]
      congr 2
      simp only [hE]
      push_cast
      ring
    · rw [ite_eq_right h1, zero_add]
      by_cases h2 : p.2 = k
      · rw [ite_eq_left h2, h2, Function.update_self, Function.update_of_ne h1,
          show u p.1 - (u k + τ) = (u p.1 - u k) - τ by ring]
        have h := theta1_add_tau (u p.1 - u k - τ) τ
        rw [sub_add_cancel] at h
        have h' : theta1 (u p.1 - u k - τ) τ =
            -cexp (-(-π * I * τ - 2 * π * I * (u p.1 - u k - τ))) * theta1 (u p.1 - u k) τ := by
          rw [h, show -cexp (-(-π * I * τ - 2 * π * I * (u p.1 - u k - τ))) *
              (-cexp (-π * I * τ - 2 * π * I * (u p.1 - u k - τ)) * theta1 (u p.1 - u k - τ) τ) =
              (cexp (-(-π * I * τ - 2 * π * I * (u p.1 - u k - τ))) *
                cexp (-π * I * τ - 2 * π * I * (u p.1 - u k - τ))) * theta1 (u p.1 - u k - τ) τ by ring,
            ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
        rw [h', mul_pow, neg_sq, ← Complex.exp_nat_mul]
        congr 2
        simp only [hE]
        push_cast
        ring
      · rw [ite_eq_right h2, Complex.exp_zero, one_mul, Function.update_of_ne h1, Function.update_of_ne h2]
  rw [Jfun_eq_pairs_dev, Jfun_eq_pairs_dev, ← Finset.prod_pow, ← Finset.prod_pow, Finset.prod_congr rfl hfac,
    Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  -- the exponent: `Σ_{i<j} (…) = Σ_{v ≠ k} E_v`
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  have hA : ∑ p ∈ (pairsLT_dev N).filter (fun p => p.1 = k), E p.2 =
      ∑ v ∈ Finset.univ.filter (fun v : Fin N => k < v), E v := by
    refine Finset.sum_nbij' (fun p => p.2) (fun v => (k, v)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, mem_pairsLT_dev] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp.2 ▸ hp.1
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [Finset.mem_filter, mem_pairsLT_dev]
      simpa using hv
    · intro p hp
      simp only [Finset.mem_filter] at hp
      rw [← hp.2]
    · intro v _
      rfl
    · intro p _
      rfl
  have hB : ∑ p ∈ (pairsLT_dev N).filter (fun p => p.2 = k), E p.1 =
      ∑ v ∈ Finset.univ.filter (fun v : Fin N => v < k), E v := by
    refine Finset.sum_nbij' (fun p => p.1) (fun v => (v, k)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, mem_pairsLT_dev] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp.2 ▸ hp.1
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [Finset.mem_filter, mem_pairsLT_dev]
      simpa using hv
    · intro p hp
      simp only [Finset.mem_filter] at hp
      rw [← hp.2]
    · intro v _
      rfl
    · intro p _
      rfl
  rw [hA, hB]
  have htri : ∀ v : Fin N, E v = (if k < v then E v else 0) + (if v < k then E v else 0) +
      (if v = k then E v else 0) := by
    intro v
    rcases lt_trichotomy v k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have hall : ∑ v, E v = ∑ v ∈ Finset.univ.filter (fun v : Fin N => k < v), E v +
      ∑ v ∈ Finset.univ.filter (fun v : Fin N => v < k), E v + E k := by
    rw [Finset.sum_congr rfl fun v _ => htri v, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_filter, Finset.sum_filter, Finset.sum_ite_eq' Finset.univ k E, ite_eq_left (Finset.mem_univ k)]
  have hsumE : ∑ v, E v = (N : ℂ) * (-2 * π * I * τ) - 4 * π * I * ((N : ℂ) * u k - ∑ i, u i) := by
    simp only [hE, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
  have hEk : E k = -2 * π * I * τ := by simp only [hE, sub_self, mul_zero, sub_zero]
  linear_combination -hall + hsumE - hEk

/-- `J` is in the Osgood class (a finite product of entire functions of linear forms). -/
theorem Jfun_isOsgood (τ : ℍ) (N : ℕ) : IsOsgood (Jfun (N := N) τ) := by
  refine ⟨?_, fun u i => ?_⟩
  · unfold Jfun
    refine continuous_finsetProd _ fun a _ => continuous_finsetProd _ fun b _ => ?_
    exact (theta1_differentiable τ).continuous.comp ((continuous_apply a).sub (continuous_apply b))
  · unfold Jfun
    refine Differentiable.fun_finsetProd fun a _ => Differentiable.fun_finsetProd fun b _ => ?_
    exact (theta1_differentiable τ).comp
      ((differentiable_update_apply_dev u i a).sub (differentiable_update_apply_dev u i b))

/-- **Lemma C.theta(f)**: "`It vanishes to order exactly $2$ along each divisor $\{u_i-u_j\in\Lambda_u\}$`" — the "at least
two" half, as divisibility in the Osgood class: `J² = ϑ₁(u_i − u_j)² K` with `K` in the class (by (c), `ϑ₁(u_i − u_j)`
vanishes exactly on the divisor, to order one). -/
theorem Jfun_sq_factor (τ : ℍ) {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    ∃ K : (Fin N → ℂ) → ℂ, IsOsgood K ∧ ∀ u, Jfun τ u ^ 2 = theta1 (u i - u j) τ ^ 2 * K u := by
  -- `K` is the product over the other pairs; the pair of `{i, j}` in increasing order is `sortPair_dev (i, j)`
  have hp₀mem : sortPair_dev (i, j) ∈ pairsLT_dev N := sortPair_mem_dev hij
  refine ⟨fun u => ∏ p ∈ (pairsLT_dev N).erase (sortPair_dev (i, j)), theta1 (u p.1 - u p.2) τ ^ 2,
    ⟨?_, fun u a => ?_⟩, fun u => ?_⟩
  · refine continuous_finsetProd _ fun p _ => ?_
    exact ((theta1_differentiable τ).continuous.comp ((continuous_apply p.1).sub (continuous_apply p.2))).pow 2
  · refine Differentiable.fun_finsetProd fun p _ => ?_
    exact ((theta1_differentiable τ).comp
      ((differentiable_update_apply_dev u a p.1).sub (differentiable_update_apply_dev u a p.2))).pow 2
  · rw [Jfun_eq_pairs_dev, ← Finset.prod_pow, ← Finset.mul_prod_erase _ _ hp₀mem]
    congr 1
    unfold sortPair_dev
    split_ifs
    · rfl
    · rw [← theta1_sq_neg_dev, neg_sub]

end HRTorus.ZeroModes

end -- noncomputable section
