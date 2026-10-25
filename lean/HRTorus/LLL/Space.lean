import HRTorus.SlotFrame.SlotFrame
import HRTorus.Fermion.Pilot.JW
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import HRTorus.LLL.Theta

/-!
# The lowest Landau level of the HR paper as a Hilbert space (T-0056 block A, `LLL.Space`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **The definitions and statements were written
first and reviewed against the paper (phase (a)) and are unchanged; phase (b) added the proofs and the proof
devices, each section of which is marked as such. No theorem is `sorry`: Lemma 2.3(iii)–(iv)
(`norm_ev_sq`, `norm_evD_sq`, `norm_ev_sq_bound`, `norm_evD_sq_bound`) were proved in block C (2026-10-24) through the
devices of `HRTorus.LLL.Theta`, whose import block C added, and `isLLL_iff` (the completeness of Lemma 2.2(ii)) in block E
(2026-10-25) through the devices of the section `LLLDevices` below. Phase (b) added the import
of `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` (the Gaussian integral, for the orthonormality
of Lemma 2.2(ii)).**
The paper: the HR paper, `papers/hr/sections/02-setting.tex` — Definition 2.1 `def:torus`, Lemma 2.2
`lem:orbitals`, Lemma 2.3 `lem:evaluation`, (2.5) `eq:magtrans`, Lemma 2.4 `lem:magtrans`, and from
Definition 2.5 `def:fock` the one-body space `𝔨_N = 𝔥_N ⊗ ℂ²`.

## The model

* **`𝔥_N` is abstract**: `Space T = EuclideanSpace ℂ (ZMod T.Nφ)`, the Hilbert space `ℓ²(ℤ_{N_φ})`, whose
  standard basis vector `orb T j` *is* the orbital `ψ_j`. Lemma 2.2(ii) ("`(ψ_j)` is an orthonormal basis")
  is thereby the definition. A vector `f` stands for the function `toFun T f = Σ_j f_j ψ_j` on `ℝ²`, with
  `ψ_j = SlotFrame.psi T j`; the paper's definition of `𝔥_N` as a space of functions is `IsLLL`, and the
  bridge between the two — orthonormality of the `ψ_j` in `L²` of the fundamental domain, and
  completeness — is proved (`l2inner_psi`, `l2inner_toFun`, `isLLL_iff`).
* The evaluation vectors `e_R`, `e^D_R` are the finite sums of Lemma 2.3, with `D = SlotFrame.Dcov`.
* The magnetic translations act on functions (`thxFun`, `thyFun`, (2.5)) and on `𝔥_N` as the matrices
  `thxMat`, `thyMat` in the orbital basis (the cyclic shift and the diagonal phase), carried to operators by
  `Matrix.toEuclideanCLM`; the bridge is `toFun_thx`, `toFun_thy`.
* `𝔨_N = 𝔥_N ⊗ ℂ²` is `ℓ²(ℤ_{N_φ} × {↑,↓})` (`Space2`), the modes `(j, σ)` of the Jordan–Wigner model
  `HRTorus.Fermion.Pilot.JW`; `spinTensor g σ` is `g ⊗ σ`.
* Everything is a function of the torus `T : SlotFrame.Torus` (`N = T.N`, `N_φ = T.Nφ = 2N`).
-/

open MeasureTheory
open scoped InnerProductSpace ContDiff Real Matrix
open Complex (I)

noncomputable section

namespace HRTorus.LLL

open HRTorus.SlotFrame
open HRTorus.Fermion.Pilot.JW (Spin Mode)

/-- `N_φ = 2N ≠ 0` (`SlotFrame.Torus.Nφ_pos`, from `L_x L_y = 2π N_φ > 0`), so that the orbital labels
`ℤ_{N_φ} = ZMod N_φ` form a finite type. -/
instance Torus.neZero_Nφ (T : Torus) : NeZero T.Nφ := ⟨T.Nφ_pos.ne'⟩

/-! ## §2.1: the lowest Landau level `𝔥_N` -/

/-- **Definition 2.1 / Lemma 2.2(ii)**, the model: "The \emph{lowest Landau level} $\hN$ is the space of
smooth functions" with (2.2)–(2.3), and "`$(\psi_j)_{j\in\Z_{\Nphi}}$ is an orthonormal basis of $\hN$. In
particular $\dim\hN=\Nphi$.`" Here `𝔥_N := ℓ²(ℤ_{N_φ})`; the vector `f` represents `Σ_j f_j ψ_j` (`toFun`). -/
abbrev Space (T : Torus) : Type := EuclideanSpace ℂ (ZMod T.Nφ)

/-- The orbital `ψ_j ∈ 𝔥_N`: the `j`-th standard basis vector. -/
def orb (T : Torus) (j : ZMod T.Nφ) : Space T :=
  EuclideanSpace.single j 1

/-- **Lemma 2.2(ii)**: "`$(\psi_j)_{j\in\Z_{\Nphi}}$ is an orthonormal basis of $\hN$`" (Mathlib's standard basis). -/
def orbBasis (T : Torus) : OrthonormalBasis (ZMod T.Nφ) ℂ (Space T) :=
  EuclideanSpace.basisFun (ZMod T.Nφ) ℂ

/-- The function on `ℝ²` represented by `f ∈ 𝔥_N`: `R ↦ Σ_j f_j ψ_j(R)`. -/
def toFun (T : Torus) (f : Space T) (R : ℝ × ℝ) : ℂ :=
  ∑ j, f j * psi T j R

/-- `D_x := ∂_x` of (2.1) on functions `ℝ² → ℂ` (Mathlib's `deriv` of the restriction to the line):
"`D_x:=\partial_x,\qquad D_y:=\partial_y-\iu x,\qquad D:=\tfrac12(D_x-\iu D_y)`". -/
def Dx (f : ℝ × ℝ → ℂ) (r : ℝ × ℝ) : ℂ :=
  deriv (fun x : ℝ => f (x, r.2)) r.1

/-- `D_y := ∂_y − i x` of (2.1). -/
def Dy (f : ℝ × ℝ → ℂ) (r : ℝ × ℝ) : ℂ :=
  deriv (fun y : ℝ => f (r.1, y)) r.2 - I * (r.1 : ℂ) * f r

/-- **Definition 2.1**, the paper's `𝔥_N` as a set of functions: `f` is smooth and satisfies
"`f(x,y+L_y)=f(x,y),\qquad f(x+L_x,y)=e^{\iu L_xy}f(x,y)`" (2.2) and "`(D_x+\iu D_y)f=0`" (2.3). -/
def IsLLL (T : Torus) (f : ℝ × ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧
    (∀ x y : ℝ, f (x, y + T.Ly) = f (x, y)) ∧
    (∀ x y : ℝ, f (x + T.Lx, y) = Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * f (x, y)) ∧
    (∀ r : ℝ × ℝ, Dx f r + I * Dy f r = 0)

/-- The fundamental domain `[0, L_x) × [0, L_y)` of `𝕋_N = ℝ²/(L_xℤ × L_yℤ)`. -/
def fundDom (T : Torus) : Set (ℝ × ℝ) :=
  Set.Ico 0 T.Lx ×ˢ Set.Ico 0 T.Ly

/-- **Definition 2.1**, the inner product on functions:
"`\ip{f}{g}:=\int_{[0,L_x)\times[0,L_y)}\overline{f}\,g\,\dd r`" (Lebesgue measure on `ℝ × ℝ`, Bochner integral). -/
def l2inner (T : Torus) (f g : ℝ × ℝ → ℂ) : ℂ :=
  ∫ r in fundDom T, star (f r) * g r

/-- The orbital `ψ_j` is the `j`-th vector of the basis. -/
theorem orbBasis_apply (T : Torus) (j : ZMod T.Nφ) : orbBasis T j = orb T j := by
  exact EuclideanSpace.basisFun_apply _ _ _

/-- **Lemma 2.2(ii)**: "`In particular $\dim\hN=\Nphi$.`" -/
theorem finrank_space (T : Torus) : Module.finrank ℂ (Space T) = T.Nφ := by
  rw [finrank_euclideanSpace, ZMod.card]

/-- The vector `ψ_j` represents the function `ψ_j`. -/
theorem toFun_orb (T : Torus) (j : ZMod T.Nφ) : toFun T (orb T j) = psi T j := by
  funext R
  simp [toFun, orb, PiLp.single_apply]

/-- `D = ½(D_x − i D_y)`: `SlotFrame.Dcov` is the paper's `D` of (2.1) in terms of `Dx`, `Dy`. -/
theorem Dcov_eq (f : ℝ × ℝ → ℂ) (r : ℝ × ℝ) : Dcov f r = (1 / 2 : ℂ) * (Dx f r - I * Dy f r) := by
  rfl

/-! ### Proof devices for Lemma 2.2(i) (phase (b); not statements of the paper): the periodicities (2.2) of `φ_n` and `ψ_j` (moved here from the devices of Lemma 2.3(i), unchanged) -/

theorem phi_add_Ly (T : Torus) (n : ℤ) (x y : ℝ) : phi T n (x, y + T.Ly) = phi T n (x, y) := by
  unfold phi
  have hk : (T.κ : ℂ) * (T.Ly : ℂ) = 2 * π := by exact_mod_cast Torus.κ_mul_Ly T
  have h : Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * ((y + T.Ly : ℝ) : ℂ)) =
      Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (y : ℂ)) := by
    rw [show I * (T.κ : ℂ) * (n : ℂ) * ((y + T.Ly : ℝ) : ℂ) =
        I * (T.κ : ℂ) * (n : ℂ) * (y : ℂ) + (n : ℂ) * (2 * π * I) by
      push_cast; linear_combination (I * (n : ℂ)) * hk]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only []
  rw [h]

theorem phi_add_Lx (T : Torus) (n : ℤ) (x y : ℝ) :
    phi T n (x + T.Lx, y) = Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * phi T (n - (T.Nφ : ℤ)) (x, y) := by
  unfold phi
  have hL : T.Lx = T.κ * (T.Nφ : ℝ) := Torus.Lx_eq T
  have hg : Real.exp (-((x + T.Lx - T.κ * n) ^ 2) / 2) =
      Real.exp (-((x - T.κ * ((n - (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2) / 2) := by
    congr 2; rw [hL]; push_cast; ring
  have hp : Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (y : ℂ)) = Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) *
      Complex.exp (I * (T.κ : ℂ) * (((n - (T.Nφ : ℤ) : ℤ)) : ℂ) * (y : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; rw [hL]; push_cast; ring
  simp only []
  rw [hg, hp]
  ring

theorem psi_add_Ly (T : Torus) (j : ZMod T.Nφ) (x y : ℝ) : psi T j (x, y + T.Ly) = psi T j (x, y) := by
  unfold psi
  exact tsum_congr fun m => phi_add_Ly T _ x y

theorem psi_add_Lx (T : Torus) (j : ZMod T.Nφ) (x y : ℝ) :
    psi T j (x + T.Lx, y) = Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * psi T j (x, y) := by
  unfold psi
  simp_rw [phi_add_Lx]
  rw [tsum_mul_left]
  congr 1
  have e : ∀ m : ℤ, ((j.val : ℤ) + m * (T.Nφ : ℤ) - (T.Nφ : ℤ)) = (j.val : ℤ) + (m - 1) * (T.Nφ : ℤ) :=
    fun m => by ring
  simp_rw [e]
  exact (Equiv.subRight (1 : ℤ)).tsum_eq (fun m => phi T ((j.val : ℤ) + m * (T.Nφ : ℤ)) (x, y))

/-! ### Proof devices for Lemma 2.2(i) (phase (b); not statements of the paper): `ψ_j(x, y) = c e^{−x²/2} Θ_j(x + iy)`
with `Θ_j(z) = Σ_m e^{a_m z − a_m²/2}` entire (`a_m = κ(j̃ + m N_φ)`), whence `ψ_j` is smooth -/

/-- The entire factor of `ψ_j` (a proof device). -/
def psiTheta (T : Torus) (j : ZMod T.Nφ) (z : ℂ) : ℂ :=
  ∑' m : ℤ, Complex.exp (((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) * z -
    (((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 2 : ℝ) : ℂ))

theorem phi_eq_theta (T : Torus) (n : ℤ) (x y : ℝ) :
    phi T n (x, y) = (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2) / 2) : ℝ) : ℂ) *
      Complex.exp (((T.κ * n : ℝ) : ℂ) * ((x : ℂ) + I * (y : ℂ)) - (((T.κ * n) ^ 2 / 2 : ℝ) : ℂ)) := by
  simp only [phi]
  rw [Complex.ofReal_mul ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) (Real.exp (-(x ^ 2) / 2)),
    Complex.ofReal_exp, Complex.ofReal_exp]
  calc _ = (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (y : ℂ)) *
        Complex.exp (((-((x - T.κ * n) ^ 2) / 2 : ℝ) : ℂ))) := by ring
    _ = (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Complex.exp (((-(x ^ 2) / 2 : ℝ) : ℂ)) *
        Complex.exp (((T.κ * n : ℝ) : ℂ) * ((x : ℂ) + I * (y : ℂ)) - (((T.κ * n) ^ 2 / 2 : ℝ) : ℂ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    _ = _ := by ring

theorem psi_eq_theta (T : Torus) (j : ZMod T.Nφ) (x y : ℝ) :
    psi T j (x, y) = (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2) / 2) : ℝ) : ℂ) *
      psiTheta T j ((x : ℂ) + I * (y : ℂ)) := by
  rw [psi, psiTheta, ← tsum_mul_left]
  exact tsum_congr fun m => phi_eq_theta T _ x y

theorem theta_bound_aux (a x R : ℝ) (hx : |x| ≤ R) : a * x ≤ a ^ 2 / 4 + R ^ 2 := by
  have h : a * x ≤ |a| * R :=
    calc a * x ≤ |a * x| := le_abs_self _
      _ = |a| * |x| := abs_mul a x
      _ ≤ |a| * R := mul_le_mul_of_nonneg_left hx (abs_nonneg a)
  nlinarith [sq_nonneg (|a| / 2 - R), sq_abs a]

theorem theta_bound_d (a x R : ℝ) (hx : |x| ≤ R) :
    |a| * Real.exp (a * x - a ^ 2 / 2) ≤ Real.exp (2 + R ^ 2) * Real.exp (-(a ^ 2 / 4) / 2) := by
  have h1 : |a| ≤ Real.exp (2 + a ^ 2 / 8) := by
    have := Real.add_one_le_exp (2 + a ^ 2 / 8)
    nlinarith [sq_nonneg (|a| - 4), sq_abs a, abs_nonneg a]
  have h2 := theta_bound_aux a x R hx
  calc |a| * Real.exp (a * x - a ^ 2 / 2) ≤ Real.exp (2 + a ^ 2 / 8) * Real.exp (a * x - a ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (2 + a ^ 2 / 8 + (a * x - a ^ 2 / 2)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (2 + R ^ 2 + (-(a ^ 2 / 4) / 2)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (2 + R ^ 2) * Real.exp (-(a ^ 2 / 4) / 2) := Real.exp_add _ _

theorem theta_bound_0 (a x R : ℝ) (hx : |x| ≤ R) :
    Real.exp (a * x - a ^ 2 / 2) ≤ Real.exp (2 + R ^ 2) * Real.exp (-(a ^ 2 / 4) / 2) := by
  have h2 := theta_bound_aux a x R hx
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg a])

theorem theta_summable (T : Torus) (j : ZMod T.Nφ) (R : ℝ) :
    Summable (fun m : ℤ => Real.exp (2 + R ^ 2) *
      Real.exp (-((-(T.κ * ((j.val : ℤ) : ℝ)) / 2 - (m : ℝ) * (T.Lx / 2)) ^ 2) / 2)) :=
  (Analysis.summable_gauss_int (by linarith [T.Lx_pos] : 0 < T.Lx / 2) _).mul_left _

theorem theta_sq_eq (T : Torus) (j : ZMod T.Nφ) (m : ℤ) :
    (-(T.κ * ((j.val : ℤ) : ℝ)) / 2 - (m : ℝ) * (T.Lx / 2)) ^ 2 =
      (T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 4 := by
  rw [Torus.Lx_eq]; push_cast; ring

theorem psiTheta_hasDerivAt (T : Torus) (j : ZMod T.Nφ) (z : ℂ) :
    HasDerivAt (psiTheta T j) (∑' m : ℤ, ((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) *
      Complex.exp (((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) * z -
        (((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 2 : ℝ) : ℂ))) z := by
  have hball : ∀ w ∈ Metric.ball z 1, |w.re| ≤ |z.re| + 1 := by
    intro w hw
    have h1 : |w.re - z.re| ≤ ‖w - z‖ := by
      have := Complex.abs_re_le_norm (w - z)
      rwa [Complex.sub_re] at this
    have h2 : ‖w - z‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have h3 := abs_sub_abs_le_abs_sub w.re z.re
    linarith
  have hnorm : ∀ (a : ℝ) (w : ℂ), ‖Complex.exp ((a : ℂ) * w - ((a ^ 2 / 2 : ℝ) : ℂ))‖ =
      Real.exp (a * w.re - a ^ 2 / 2) := by
    intro a w
    rw [Complex.norm_exp, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  unfold psiTheta
  refine hasDerivAt_tsum_of_isPreconnected (F := ℂ)
    (g := fun (m : ℤ) (w : ℂ) => Complex.exp (((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) * w -
      (((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 2 : ℝ) : ℂ)))
    (g' := fun (m : ℤ) (w : ℂ) => ((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) *
      Complex.exp (((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) * w -
        (((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 2 : ℝ) : ℂ)))
    (theta_summable T j (|z.re| + 1)) Metric.isOpen_ball
    (convex_ball z 1).isPreconnected (fun m w _ => ?_) (fun m w hw => ?_) (Metric.mem_ball_self one_pos) ?_
    (Metric.mem_ball_self one_pos)
  · have h := (((hasDerivAt_id w).const_mul ((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)).sub_const
      (((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 2 : ℝ) : ℂ)).cexp
    refine h.congr_deriv ?_
    simp only [id, mul_one]
    ring
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnorm, theta_sq_eq]
    exact theta_bound_d _ _ _ (hball w hw)
  · refine Summable.of_norm_bounded (theta_summable T j (|z.re| + 1)) fun m => ?_
    rw [hnorm, theta_sq_eq]
    exact theta_bound_0 _ _ _ (hball z (Metric.mem_ball_self one_pos))

theorem psiTheta_differentiable (T : Torus) (j : ZMod T.Nφ) : Differentiable ℂ (psiTheta T j) :=
  fun z => (psiTheta_hasDerivAt T j z).differentiableAt

theorem gaussFactor_hasDerivAt (T : Torus) (x : ℝ) :
    HasDerivAt (fun x' : ℝ => ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x' ^ 2) / 2) : ℝ)) : ℂ))
      (-(x : ℂ) * ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2) / 2) : ℝ)) : ℂ)) x := by
  have h1 : HasDerivAt (fun x' : ℝ => -(x' ^ 2) / 2) (-x) x := by
    have h := ((hasDerivAt_id x).pow 2).neg.div_const 2
    convert h using 1
    · funext y; simp only [Pi.neg_apply, Pi.pow_apply, id]
    · norm_num [id]; ring
  have hc := (h1.exp.const_mul ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)))).ofReal_comp
  convert hc using 1
  push_cast
  ring

theorem psi_contDiff (T : Torus) (j : ZMod T.Nφ) : ContDiff ℝ ∞ (psi T j) := by
  have hrep : psi T j = fun r : ℝ × ℝ =>
      ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r.1 ^ 2) / 2) : ℝ)) : ℂ) *
        psiTheta T j ((r.1 : ℂ) + I * (r.2 : ℂ)) :=
    funext fun r => psi_eq_theta T j r.1 r.2
  rw [hrep]
  have hΘ : ContDiff ℝ ∞ (psiTheta T j) :=
    ((psiTheta_differentiable T j).contDiff).restrict_scalars ℝ
  have hL : ContDiff ℝ ∞ (fun r : ℝ × ℝ => (r.1 : ℂ) + I * (r.2 : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd))
  have hG : ContDiff ℝ ∞ (fun r : ℝ × ℝ =>
      ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r.1 ^ 2) / 2) : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (Real.contDiff_exp.comp
      (((contDiff_fst.pow 2).neg).div_const 2)))
  exact hG.mul (hΘ.comp hL)

theorem psi_lll_eq (T : Torus) (j : ZMod T.Nφ) (r : ℝ × ℝ) : Dx (psi T j) r + I * Dy (psi T j) r = 0 := by
  rcases r with ⟨x, y⟩
  obtain ⟨d, hd⟩ : ∃ d, HasDerivAt (psiTheta T j) d ((x : ℂ) + I * (y : ℂ)) := ⟨_, psiTheta_hasDerivAt T j _⟩
  have hfx : (fun x' : ℝ => psi T j (x', y)) = fun x' : ℝ =>
      ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x' ^ 2) / 2) : ℝ)) : ℂ) *
        psiTheta T j ((x' : ℂ) + I * (y : ℂ)) :=
    funext fun x' => psi_eq_theta T j x' y
  have hfy : (fun y' : ℝ => psi T j (x, y')) = fun y' : ℝ =>
      ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2) / 2) : ℝ)) : ℂ) *
        psiTheta T j ((x : ℂ) + I * (y' : ℂ)) :=
    funext fun y' => psi_eq_theta T j x y'
  have hΘx : HasDerivAt (fun x' : ℝ => psiTheta T j ((x' : ℂ) + I * (y : ℂ))) d x :=
    (HasDerivAt.comp_add_const (x : ℂ) (I * (y : ℂ)) hd).comp_ofReal
  have hΘy : HasDerivAt (fun y' : ℝ => psiTheta T j ((x : ℂ) + I * (y' : ℂ))) (d * I) y := by
    have hlin : HasDerivAt (fun w : ℂ => (x : ℂ) + I * w) I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).const_mul I).const_add (x : ℂ)
    exact (hd.comp (y : ℂ) hlin).comp_ofReal
  have hdx : deriv (fun x' : ℝ => psi T j (x', y)) x =
      (-(x : ℂ) * ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2) / 2) : ℝ)) : ℂ)) *
        psiTheta T j ((x : ℂ) + I * (y : ℂ)) +
      ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2) / 2) : ℝ)) : ℂ) * d := by
    rw [hfx]
    exact ((gaussFactor_hasDerivAt T x).mul hΘx).deriv
  have hdy : deriv (fun y' : ℝ => psi T j (x, y')) y =
      ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2) / 2) : ℝ)) : ℂ) * (d * I) := by
    rw [hfy]
    exact (hΘy.const_mul _).deriv
  have hψ := psi_eq_theta T j x y
  simp only [Dx, Dy]
  rw [hdx, hdy, hψ]
  linear_combination (((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2) / 2) : ℝ)) : ℂ) * d -
    (x : ℂ) * ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2) / 2) : ℝ)) : ℂ) *
      psiTheta T j ((x : ℂ) + I * (y : ℂ))) * Complex.I_sq

/-- **Lemma 2.2(i)**: "`$\psi_j$ does not depend on the choice of $\tilde\jmath$, and $\psi_j\in\hN$`" — the
membership (smoothness, (2.2), (2.3)). The convergence of (2.4) at every point and the independence of the
representative are `SlotFrame.psi_summable` and `SlotFrame.psi_intCast`. -/
theorem psi_isLLL (T : Torus) (j : ZMod T.Nφ) : IsLLL T (psi T j) := by
  exact ⟨psi_contDiff T j, fun x y => psi_add_Ly T j x y, fun x y => psi_add_Lx T j x y, psi_lll_eq T j⟩

/-! ### Proof devices for Lemma 2.2(ii), the orthonormality (phase (b); not statements of the paper) -/

theorem phi_continuous (T : Torus) (n : ℤ) : Continuous (phi T n) := by
  unfold phi
  fun_prop

theorem phi_norm_summable (T : Torus) (n : ℤ) (r : ℝ × ℝ) :
    Summable (fun m : ℤ => ‖phi T (n + m * (T.Nφ : ℤ)) r‖) := by
  refine ((Analysis.summable_gauss_int T.Lx_pos (r.1 - T.κ * n)).mul_left
    ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)))).congr fun m => ?_
  have e : r.1 - T.κ * (((n + m * (T.Nφ : ℤ) : ℤ)) : ℝ) = r.1 - T.κ * n - m * T.Lx := by
    rw [Torus.Lx_eq]; push_cast; ring
  rw [norm_phi, e]

/-- `\overline{φ_n} φ_{n'}` is a function of `x` times `e^{iκ(n'−n)y}`. -/
theorem star_phi_mul_phi (T : Torus) (n n' : ℤ) (x y : ℝ) :
    star (phi T n (x, y)) * phi T n' (x, y) =
      ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-((x - T.κ * n) ^ 2) / 2) *
        Real.exp (-((x - T.κ * n') ^ 2) / 2) : ℝ) : ℂ) *
      Complex.exp ((I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ)) := by
  have hs : ∀ r : ℝ, star (r : ℂ) = r := fun r => Complex.conj_ofReal r
  have hse : ∀ z : ℂ, star (Complex.exp z) = Complex.exp (star z) := fun z => (Complex.exp_conj z).symm
  have hsI : star I = -I := Complex.conj_I
  simp only [phi]
  simp only [star_mul', hs, hse, hsI, star_intCast]
  rw [show (I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ) =
      -I * (T.κ : ℂ) * (n : ℂ) * (y : ℂ) + I * (T.κ : ℂ) * (n' : ℂ) * (y : ℂ) by push_cast; ring,
    Complex.exp_add]
  push_cast
  ring

theorem integral_exp_y (T : Torus) (k : ℤ) :
    ∫ y in Set.Ico 0 T.Ly, Complex.exp ((I * ((T.κ * (k : ℝ) : ℝ) : ℂ)) * (y : ℂ)) =
      if k = 0 then (T.Ly : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp only [Int.cast_zero, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    rw [setIntegral_const, Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith [T.Ly_pos]), sub_zero,
      Complex.real_smul, mul_one]
  · have hc : I * ((T.κ * (k : ℝ) : ℝ) : ℂ) ≠ 0 := by
      refine mul_ne_zero Complex.I_ne_zero ?_
      exact_mod_cast mul_ne_zero T.κ_pos.ne' (by exact_mod_cast hk)
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le T.Ly_pos.le, integral_exp_mul_complex hc]
    have h1 : I * ((T.κ * (k : ℝ) : ℝ) : ℂ) * (T.Ly : ℂ) = (k : ℂ) * (2 * π * I) := by
      have := Torus.κ_mul_Ly T
      have h' : ((T.κ : ℂ) * (T.Ly : ℂ)) = 2 * π := by exact_mod_cast this
      push_cast
      linear_combination (I * (k : ℂ)) * h'
    rw [h1, Complex.exp_int_mul_two_pi_mul_I, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, zero_div]

theorem integral_star_phi_mul_phi (T : Torus) (n n' : ℤ) :
    ∫ r in fundDom T, star (phi T n r) * phi T n' r =
      (∫ x in Set.Ico 0 T.Lx, ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-((x - T.κ * n) ^ 2) / 2) *
        Real.exp (-((x - T.κ * n') ^ 2) / 2) : ℝ) : ℂ)) * (if n' - n = 0 then (T.Ly : ℂ) else 0) := by
  have e : (fun r : ℝ × ℝ => star (phi T n r) * phi T n' r) = fun r =>
      (fun x : ℝ => ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-((x - T.κ * n) ^ 2) / 2) *
        Real.exp (-((x - T.κ * n') ^ 2) / 2) : ℝ) : ℂ)) r.1 *
      (fun y : ℝ => Complex.exp ((I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ))) r.2 :=
    funext fun r => star_phi_mul_phi T n n' r.1 r.2
  calc ∫ r in fundDom T, star (phi T n r) * phi T n' r
      = ∫ r in Set.Ico 0 T.Lx ×ˢ Set.Ico 0 T.Ly,
          (fun x : ℝ => ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-((x - T.κ * n) ^ 2) / 2) *
            Real.exp (-((x - T.κ * n') ^ 2) / 2) : ℝ) : ℂ)) r.1 *
          (fun y : ℝ => Complex.exp ((I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ))) r.2
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
        rw [← Measure.volume_eq_prod, e]
        rfl
    _ = (∫ x in Set.Ico 0 T.Lx, ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-((x - T.κ * n) ^ 2) / 2) *
            Real.exp (-((x - T.κ * n') ^ 2) / 2) : ℝ) : ℂ)) *
          ∫ y in Set.Ico 0 T.Ly, Complex.exp ((I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ)) :=
        setIntegral_prod_mul (fun x : ℝ => ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 *
            Real.exp (-((x - T.κ * n) ^ 2) / 2) * Real.exp (-((x - T.κ * n') ^ 2) / 2) : ℝ) : ℂ))
          (fun y : ℝ => Complex.exp ((I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ)))
          (Set.Ico 0 T.Lx) (Set.Ico 0 T.Ly)
    _ = _ := by rw [integral_exp_y]

/-- For `0 ≤ x ≤ L_x`: `e^{−(x−a)²/2} ≤ e^{L_x²/2} e^{−(a²/4)/2}`. -/
theorem gauss_strip_bound (a x Lx : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ Lx) :
    Real.exp (-((x - a) ^ 2) / 2) ≤ Real.exp (Lx ^ 2 / 2) * Real.exp (-(a ^ 2 / 4) / 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [sq_nonneg (x - a / 2), sq_nonneg a, mul_le_mul hx1 hx1 hx0 (hx0.trans hx1)]

theorem idx_sub_eq_zero_iff (T : Torus) (i j : ZMod T.Nφ) (m m' : ℤ) :
    ((j.val : ℤ) + m' * (T.Nφ : ℤ)) - ((i.val : ℤ) + m * (T.Nφ : ℤ)) = 0 ↔ i = j ∧ m = m' := by
  constructor
  · intro h
    have hi : (i.val : ℤ) < T.Nφ := by exact_mod_cast ZMod.val_lt i
    have hj : (j.val : ℤ) < T.Nφ := by exact_mod_cast ZMod.val_lt j
    have hi0 : (0 : ℤ) ≤ i.val := by positivity
    have hj0 : (0 : ℤ) ≤ j.val := by positivity
    have hN : (0 : ℤ) < T.Nφ := by exact_mod_cast T.Nφ_pos
    have hmm : m = m' := by
      rcases lt_trichotomy m m' with hlt | heq | hgt
      · have h1 := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ m' - m by omega) hN.le
        nlinarith
      · exact heq
      · have h1 := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ m - m' by omega) hN.le
        nlinarith
    subst hmm
    have hv : (i.val : ℤ) = j.val := by linarith
    exact ⟨ZMod.val_injective _ (by exact_mod_cast hv), rfl⟩
  · rintro ⟨rfl, rfl⟩
    ring

theorem gauss_unfold (T : Torus) (a : ℝ) :
    ∑' m : ℤ, ∫ x in Set.Ico 0 T.Lx, Real.exp (-((x - (a + m * T.Lx)) ^ 2)) = Real.sqrt π := by
  have hfd := isAddFundamentalDomain_Ioc T.Lx_pos 0 (μ := (volume : Measure ℝ))
  have hint : Integrable (fun x : ℝ => Real.exp (-((x - a) ^ 2))) := by
    have := (integrable_exp_neg_mul_sq (b := 1) one_pos).comp_sub_right a
    simpa using this
  have hgauss : ∫ x : ℝ, Real.exp (-((x - a) ^ 2)) = Real.sqrt π := by
    rw [integral_sub_right_eq_self (fun x : ℝ => Real.exp (-(x ^ 2))) a]
    have := integral_gaussian 1
    simpa using this
  rw [← hgauss, hfd.integral_eq_tsum' _ hint]
  have hinj : Function.Injective (fun m : ℤ => (⟨m • T.Lx, AddSubgroup.zsmul_mem_zmultiples T.Lx m⟩ :
      AddSubgroup.zmultiples T.Lx)) := by
    intro m m' h
    have h1 : m • T.Lx = m' • T.Lx := congrArg Subtype.val h
    rw [zsmul_eq_mul, zsmul_eq_mul] at h1
    exact_mod_cast mul_right_cancel₀ T.Lx_pos.ne' h1
  have hsupp : Function.support (fun g : AddSubgroup.zmultiples T.Lx =>
      ∫ x in Set.Ioc 0 (0 + T.Lx), Real.exp (-(((-g +ᵥ x) - a) ^ 2))) ⊆ Set.range (fun m : ℤ =>
        (⟨m • T.Lx, AddSubgroup.zsmul_mem_zmultiples T.Lx m⟩ : AddSubgroup.zmultiples T.Lx)) := by
    rintro ⟨g, hg⟩ _
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
    exact ⟨m, rfl⟩
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun m => ?_
  rw [integral_Ico_eq_integral_Ioc, zero_add]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (-((x - (a + m * T.Lx)) ^ 2)) = Real.exp (-((-(m • T.Lx) + x - a) ^ 2))
  rw [zsmul_eq_mul]
  ring_nf

theorem c0_sq_mul (T : Torus) : ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * T.Ly * Real.sqrt π = 1 := by
  have hpos : 0 < T.Ly * Real.sqrt π := mul_pos T.Ly_pos (Real.sqrt_pos.mpr Real.pi_pos)
  have h1 : T.Ly ≠ 0 := T.Ly_pos.ne'
  have h2 : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num,
    Real.rpow_neg_one]
  field_simp

theorem integral_star_phi_mul_phi' (T : Torus) (n n' : ℤ) :
    ∫ r in fundDom T, star (phi T n r) * phi T n' r =
      if n = n' then ((T.Ly * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 *
        ∫ x in Set.Ico 0 T.Lx, Real.exp (-((x - T.κ * n) ^ 2)) : ℝ) : ℂ) else 0 := by
  rw [integral_star_phi_mul_phi]
  by_cases h : n = n'
  · subst h
    rw [ite_eq_left (sub_self n), ite_eq_left rfl, integral_complex_ofReal]
    have e : (fun x : ℝ => ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-((x - T.κ * n) ^ 2) / 2) *
        Real.exp (-((x - T.κ * n) ^ 2) / 2)) = fun x => ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 *
        Real.exp (-((x - T.κ * n) ^ 2)) := by
      funext x
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [e, integral_const_mul]
    push_cast
    ring
  · rw [ite_eq_right (sub_ne_zero.mpr (Ne.symm h)), ite_eq_right h, mul_zero]

theorem idx_eq_iff (T : Torus) (i j : ZMod T.Nφ) (m m' : ℤ) :
    (i.val : ℤ) + m * (T.Nφ : ℤ) = (j.val : ℤ) + m' * (T.Nφ : ℤ) ↔ i = j ∧ m = m' := by
  rw [← idx_sub_eq_zero_iff T i j m m', sub_eq_zero, eq_comm]

theorem tsum_diag {α : Type*} [AddCommMonoid α] [TopologicalSpace α] (g : ℤ → α) :
    ∑' p : ℤ × ℤ, (if p.1 = p.2 then g p.1 else 0) = ∑' m : ℤ, g m := by
  have hdiag : Function.Injective (fun m : ℤ => (m, m)) := fun m m' h => (Prod.ext_iff.mp h).1
  have hs : Function.support (fun p : ℤ × ℤ => if p.1 = p.2 then g p.1 else 0) ⊆
      Set.range (fun m : ℤ => (m, m)) := by
    intro p hp
    by_cases h : p.1 = p.2
    · exact ⟨p.1, Prod.ext rfl h⟩
    · exact absurd (by simp [h]) hp
  rw [← hdiag.tsum_eq hs]
  simp

theorem phi_bound_fd (T : Torus) (k : ZMod T.Nφ) (m : ℤ) (r : ℝ × ℝ) (hr : r ∈ fundDom T) :
    ‖phi T ((k.val : ℤ) + m * (T.Nφ : ℤ)) r‖ ≤ (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
      (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((-(T.κ * ((k.val : ℤ) : ℝ)) / 2 - (m : ℝ) * (T.Lx / 2)) ^ 2) / 2)) := by
  rw [norm_phi, theta_sq_eq]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (mul_nonneg T.Ly_pos.le (Real.sqrt_nonneg _)) _)
  exact gauss_strip_bound _ _ _ hr.1.1 hr.1.2.le


/-- **Lemma 2.2(ii)**, orthonormality of the functions `ψ_j` for the inner product of Definition 2.1
("`Hence $\ip{\psi_i}{\psi_j}=0$ for $i\ne j$`", and `⟨ψ_j, ψ_j⟩ = 1`). -/
theorem l2inner_psi (T : Torus) (i j : ZMod T.Nφ) :
    l2inner T (psi T i) (psi T j) = if i = j then 1 else 0 := by
  rw [l2inner]
  have hpt : ∀ r : ℝ × ℝ, star (psi T i r) * psi T j r = ∑' p : ℤ × ℤ,
      star (phi T ((i.val : ℤ) + p.1 * (T.Nφ : ℤ)) r) * phi T ((j.val : ℤ) + p.2 * (T.Nφ : ℤ)) r := by
    intro r
    rw [psi, psi, tsum_star]
    exact tsum_mul_tsum_of_summable_norm (by simpa only [norm_star] using phi_norm_summable T _ r)
      (phi_norm_summable T _ r)
  simp_rw [hpt]
  have hmeas : MeasurableSet (fundDom T) := measurableSet_Ico.prod measurableSet_Ico
  have hint : ∀ p : ℤ × ℤ, Integrable (fun r => star (phi T ((i.val : ℤ) + p.1 * (T.Nφ : ℤ)) r) *
      phi T ((j.val : ℤ) + p.2 * (T.Nφ : ℤ)) r) (volume.restrict (fundDom T)) := by
    intro p
    have hc : Continuous (fun r => star (phi T ((i.val : ℤ) + p.1 * (T.Nφ : ℤ)) r) *
        phi T ((j.val : ℤ) + p.2 * (T.Nφ : ℤ)) r) :=
      ((phi_continuous T _).star).mul (phi_continuous T _)
    exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ico_subset_Icc_self Set.Ico_subset_Icc_self)
  have hBs : ∀ k : ZMod T.Nφ, Summable (fun m : ℤ => ‖(T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
      (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((-(T.κ * ((k.val : ℤ) : ℝ)) / 2 - (m : ℝ) * (T.Lx / 2)) ^ 2) / 2))‖) := by
    intro k
    have hLy := T.Ly_pos
    refine (((Analysis.summable_gauss_int (by linarith [T.Lx_pos] : 0 < T.Lx / 2)
      (-(T.κ * ((k.val : ℤ) : ℝ)) / 2)).mul_left
      (Real.exp (T.Lx ^ 2 / 2))).mul_left ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)))).congr fun m => ?_
    rw [Real.norm_of_nonneg (by positivity)]
  have hsum : Summable (fun p : ℤ × ℤ => ∫ r in fundDom T, ‖star (phi T ((i.val : ℤ) + p.1 * (T.Nφ : ℤ)) r) *
      phi T ((j.val : ℤ) + p.2 * (T.Nφ : ℤ)) r‖) := by
    have hLy := T.Ly_pos
    have hprod := (summable_mul_of_summable_norm (hBs i) (hBs j)).mul_left (volume.real (fundDom T))
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun r => norm_nonneg _) (fun p => ?_) hprod
    have hcst : IntegrableOn (fun _ : ℝ × ℝ => (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
        (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((-(T.κ * ((i.val : ℤ) : ℝ)) / 2 - (p.1 : ℝ) * (T.Lx / 2)) ^ 2) / 2)) *
        ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
        (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((-(T.κ * ((j.val : ℤ) : ℝ)) / 2 - (p.2 : ℝ) * (T.Lx / 2)) ^ 2) / 2))))
        (fundDom T) :=
      (continuous_const.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Set.Ico_subset_Icc_self Set.Ico_subset_Icc_self)
    refine (setIntegral_mono_on (hint p).norm hcst hmeas fun r hr => ?_).trans_eq ?_
    · rw [norm_mul, norm_star]
      exact mul_le_mul (phi_bound_fd T i p.1 r hr) (phi_bound_fd T j p.2 r hr) (norm_nonneg _) (by positivity)
    · rw [setIntegral_const, smul_eq_mul]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [integral_star_phi_mul_phi']
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    have hc : ∀ p : ℤ × ℤ, ((i.val : ℤ) + p.1 * (T.Nφ : ℤ) = (i.val : ℤ) + p.2 * (T.Nφ : ℤ)) ↔ p.1 = p.2 := by
      intro p
      rw [idx_eq_iff]
      simp
    simp_rw [hc]
    rw [tsum_diag (fun m : ℤ => ((T.Ly * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 *
        ∫ x in Set.Ico 0 T.Lx, Real.exp (-((x - T.κ * (((i.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2)) : ℝ) : ℂ)),
      ← Complex.ofReal_tsum, tsum_mul_left]
    have e2 : ∀ m : ℤ, (∫ x in Set.Ico 0 T.Lx, Real.exp (-((x - T.κ * (((i.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2))) =
        ∫ x in Set.Ico 0 T.Lx, Real.exp (-((x - (T.κ * ((i.val : ℤ) : ℝ) + m * T.Lx)) ^ 2)) := by
      intro m
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show Real.exp (-((x - T.κ * (((i.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2)) =
        Real.exp (-((x - (T.κ * ((i.val : ℤ) : ℝ) + m * T.Lx)) ^ 2))
      rw [Torus.Lx_eq]
      push_cast
      ring_nf
    simp_rw [e2]
    rw [gauss_unfold T (T.κ * ((i.val : ℤ) : ℝ))]
    have h1 : T.Ly * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.sqrt π = 1 := by
      linarith [c0_sq_mul T]
    rw [h1, Complex.ofReal_one]
  · rw [ite_eq_right hij]
    have h0 : ∀ p : ℤ × ℤ, ¬ ((i.val : ℤ) + p.1 * (T.Nφ : ℤ) = (j.val : ℤ) + p.2 * (T.Nφ : ℤ)) :=
      fun p h => hij ((idx_eq_iff T i j p.1 p.2).mp h).1
    simp only [h0, ite_false, tsum_zero]

/-! ### Proof devices for Lemma 2.2(ii) in the model (phase (b); not statements of the paper) -/

theorem psi_continuous (T : Torus) (j : ZMod T.Nφ) : Continuous (psi T j) :=
  (psi_contDiff T j).continuous

theorem psi_star_mul_integrableOn (T : Torus) (i j : ZMod T.Nφ) :
    IntegrableOn (fun r => star (psi T i r) * psi T j r) (fundDom T) := by
  have hc : Continuous (fun r => star (psi T i r) * psi T j r) :=
    ((psi_continuous T i).star).mul (psi_continuous T j)
  exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ico_subset_Icc_self Set.Ico_subset_Icc_self)


/-- **Lemma 2.2(ii)** in the model: the inner product of `𝔥_N` is the paper's `L²` inner product of the
represented functions ("`with the inner product $\ip{f}{g}:=\int_{[0,L_x)\times[0,L_y)}\overline{f}\,g\,\dd r$`"). -/
theorem l2inner_toFun (T : Torus) (f g : Space T) :
    l2inner T (toFun T f) (toFun T g) = ⟪f, g⟫_ℂ := by
  have e : ∀ r, star (toFun T f r) * toFun T g r =
      ∑ i, ∑ j, (star (f i) * g j) * (star (psi T i r) * psi T j r) := by
    intro r
    simp only [toFun, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [l2inner]
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (psi_star_mul_integrableOn T i j).const_mul _]
  have e2 : ∀ i j : ZMod T.Nφ, ∫ r in fundDom T, (star (f i) * g j) * (star (psi T i r) * psi T j r) =
      (star (f i) * g j) * (if i = j then 1 else 0) := by
    intro i j
    rw [integral_const_mul, ← l2inner_psi T i j]
    rfl
  have e3 : ∀ i : ZMod T.Nφ, ∫ r in fundDom T, ∑ j, (star (f i) * g j) * (star (psi T i r) * psi T j r) =
      star (f i) * g i := by
    intro i
    rw [integral_finsetSum _ fun j _ => (psi_star_mul_integrableOn T i j).const_mul _]
    simp_rw [e2]
    simp
  simp_rw [e3]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply']
  rfl

/-! ### Proof devices for Lemma 2.2(ii), the completeness (T-0056 block E, recruit L11, round one; not statements of
the paper)

The paper's route: for `g ∈ 𝔥_N` the `y`-Fourier coefficients `c_n(x) = ∫_0^{L_y} e^{−iκny} g(x, y) dy` (`fcoef_dev`)
satisfy `c_n' = (κn − x) c_n` (differentiation under the integral sign, (2.3) and an integration by parts with (2.2)),
hence `c_n(x) = A_n e^{−(x−κn)²/2}`; the quasi-periodicity in `x` gives `A_{n+N_φ} = A_n`; the coefficients are then
summable (a Gaussian), so the Fourier series converges to `g` pointwise (Mathlib's
`has_pointwise_sum_fourier_series_of_summable`), and regrouping `n = j̃ + mN_φ` gives
`g = Σ_j (L_y√π)^{1/2} L_y^{−1} A_j ψ_j`. -/

section LLLDevices

open Filter

/-- The (unnormalized) `y`-Fourier coefficient `∫_0^{L_y} e^{−iκny} g(x, y) dy`. -/
noncomputable def fcoef_dev (T : Torus) (g : ℝ × ℝ → ℂ) (n : ℤ) (x : ℝ) : ℂ :=
  ∫ y in (0 : ℝ)..T.Ly, Complex.exp (-(I * ((T.κ * n : ℝ) : ℂ)) * y) * g (x, y)

theorem lll_hasDerivAt_x_dev {T : Torus} {g : ℝ × ℝ → ℂ} (hg : IsLLL T g) (x y : ℝ) :
    HasDerivAt (fun x' : ℝ => g (x', y)) (fderiv ℝ g (x, y) (1, 0)) x :=
  ((hg.1.differentiable (by simp)) (x, y)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

theorem lll_hasDerivAt_y_dev {T : Torus} {g : ℝ × ℝ → ℂ} (hg : IsLLL T g) (x y : ℝ) :
    HasDerivAt (fun y' : ℝ => g (x, y')) (fderiv ℝ g (x, y) (0, 1)) y :=
  ((hg.1.differentiable (by simp)) (x, y)).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

theorem lll_dx_eq_dev {T : Torus} {g : ℝ × ℝ → ℂ} (hg : IsLLL T g) (x y : ℝ) :
    fderiv ℝ g (x, y) (1, 0) = -I * fderiv ℝ g (x, y) (0, 1) - (x : ℂ) * g (x, y) := by
  have h := hg.2.2.2 (x, y)
  simp only [Dx, Dy] at h
  rw [(lll_hasDerivAt_x_dev hg x y).deriv, (lll_hasDerivAt_y_dev hg x y).deriv] at h
  linear_combination h + ((x : ℂ) * g (x, y)) * Complex.I_sq

theorem hasDerivAt_cexp_mul_dev (c : ℂ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * y)) (c * Complex.exp (c * y)) y := by
  have := (((hasDerivAt_id (y : ℂ)).const_mul c).cexp).comp_ofReal
  simpa [mul_comm] using this

theorem norm_cexp_I_mul_dev (r y : ℝ) : ‖Complex.exp (-(I * (r : ℂ)) * y)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem fcoef_hasDerivAt_dev {T : Torus} {g : ℝ × ℝ → ℂ} (hg : IsLLL T g) (n : ℤ) (x : ℝ) :
    HasDerivAt (fcoef_dev T g n) (((T.κ * n - x : ℝ) : ℂ) * fcoef_dev T g n x) x := by
  set c : ℂ := -(I * ((T.κ * n : ℝ) : ℂ)) with hc
  have hG1 : Continuous fun p : ℝ × ℝ => fderiv ℝ g p (1, 0) :=
    (hg.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hG2 : Continuous fun p : ℝ × ℝ => fderiv ℝ g p (0, 1) :=
    (hg.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgc : Continuous g := hg.1.continuous
  have he : Continuous fun y : ℝ => Complex.exp (c * y) := by fun_prop
  obtain ⟨M, hM⟩ := (isCompact_closedBall x 1 |>.prod
    (isCompact_Icc (a := (0 : ℝ)) (b := T.Ly))).exists_bound_of_continuousOn hG1.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0)
    (b := T.Ly) (F := fun x' y => Complex.exp (c * y) * g (x', y))
    (F' := fun x' y => Complex.exp (c * y) * fderiv ℝ g (x', y) (1, 0)) (x₀ := x) (bound := fun _ => M)
    (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun x' => (he.mul (hgc.comp (by fun_prop))).aestronglyMeasurable)
    ((he.mul (hgc.comp (by fun_prop))).intervalIntegrable _ _)
    ((he.mul (hG1.comp (by fun_prop))).aestronglyMeasurable)
    (Eventually.of_forall fun y hy x' hx' => by
      rw [norm_mul, norm_cexp_I_mul_dev, one_mul]
      refine hM (x', y) ⟨Metric.ball_subset_closedBall hx', ?_⟩
      have hL := T.Ly_pos
      rw [Set.uIoc_of_le hL.le] at hy
      exact ⟨hy.1.le, hy.2⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun y _ x' _ => (lll_hasDerivAt_x_dev hg x' y).const_mul _)
  have hF : fcoef_dev T g n = fun x' => ∫ y in (0 : ℝ)..T.Ly, Complex.exp (c * y) * g (x', y) := rfl
  rw [hF]
  convert key.2 using 1
  -- the derivative: `∫ e G1 = −i ∫ e G2 − x ∫ e g` and `∫ e G2 = −c ∫ e g` (integration by parts, periodicity)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T.Ly)
    (u := fun y : ℝ => Complex.exp (c * y)) (u' := fun y => c * Complex.exp (c * y))
    (v := fun y : ℝ => g (x, y)) (v' := fun y => fderiv ℝ g (x, y) (0, 1))
    (fun y _ => hasDerivAt_cexp_mul_dev c y) (fun y _ => lll_hasDerivAt_y_dev hg x y)
    ((continuous_const.mul he).intervalIntegrable _ _) ((hG2.comp (by fun_prop)).intervalIntegrable _ _)
  have hL1 : Complex.exp (c * T.Ly) = 1 := by
    have hκL : T.κ * T.Ly = 2 * π := by
      unfold Torus.κ
      field_simp [T.Ly_pos.ne']
    have e : c * (T.Ly : ℂ) = ((-n : ℤ) : ℂ) * (2 * π * I) := by
      rw [hc]
      have h2 : T.κ * n * T.Ly = 2 * π * n := by
        rw [mul_right_comm, hκL]
      have : ((T.κ * n : ℝ) : ℂ) * (T.Ly : ℂ) = ((2 * π * n : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, h2]
      push_cast at this ⊢
      linear_combination (-I) * this
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  have hper : g (x, T.Ly) = g (x, 0) := by simpa using hg.2.1 x 0
  simp only [Complex.exp_zero, mul_zero, Complex.ofReal_zero, one_mul, hL1, hper, sub_self, zero_sub] at hibp
  have hsplit : (∫ y in (0 : ℝ)..T.Ly, Complex.exp (c * y) * fderiv ℝ g (x, y) (1, 0)) =
      -I * (∫ y in (0 : ℝ)..T.Ly, Complex.exp (c * y) * fderiv ℝ g (x, y) (0, 1)) -
        (x : ℂ) * ∫ y in (0 : ℝ)..T.Ly, Complex.exp (c * y) * g (x, y) := by
    simp_rw [lll_dx_eq_dev hg x]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub]
    · congr 1
      funext y
      ring
    · exact (continuous_const.mul (he.mul (hG2.comp (by fun_prop)))).intervalIntegrable _ _
    · exact (continuous_const.mul (he.mul (hgc.comp (by fun_prop)))).intervalIntegrable _ _
  rw [hsplit, hibp]
  have hmul : (∫ y in (0 : ℝ)..T.Ly, c * Complex.exp (c * y) * g (x, y)) =
      c * ∫ y in (0 : ℝ)..T.Ly, Complex.exp (c * y) * g (x, y) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext y
    ring
  rw [hmul, hc]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem fcoef_eq_dev {T : Torus} {g : ℝ × ℝ → ℂ} (hg : IsLLL T g) (n : ℤ) (x : ℝ) :
    fcoef_dev T g n x = fcoef_dev T g n 0 * ((Real.exp ((T.κ * n) ^ 2 / 2) : ℝ) : ℂ) *
      ((Real.exp (-((x - T.κ * n) ^ 2) / 2) : ℝ) : ℂ) := by
  have hE : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ((Real.exp ((x - T.κ * n) ^ 2 / 2) : ℝ) : ℂ))
      ((((x - T.κ * n) * Real.exp ((x - T.κ * n) ^ 2 / 2) : ℝ)) : ℂ) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => Real.exp ((x - T.κ * n) ^ 2 / 2))
        (Real.exp ((x - T.κ * n) ^ 2 / 2) * ((2 : ℕ) * (x - T.κ * n) ^ (2 - 1) * 1 / 2)) x :=
      ((((hasDerivAt_id x).sub_const (T.κ * n)).pow 2).div_const 2).exp
    have h2 := h1.ofReal_comp
    convert h2 using 1
    push_cast
    ring
  have hu' : ∀ x : ℝ, HasDerivAt
      (fun x : ℝ => fcoef_dev T g n x * ((Real.exp ((x - T.κ * n) ^ 2 / 2) : ℝ) : ℂ)) 0 x := by
    intro x
    have := (fcoef_hasDerivAt_dev hg n x).mul (hE x)
    convert this using 1
    push_cast
    ring
  have hconst := is_const_of_deriv_eq_zero (fun x => (hu' x).differentiableAt) (fun x => (hu' x).deriv) x 0
  have hab : ((Real.exp ((x - T.κ * n) ^ 2 / 2) : ℝ) : ℂ) *
      ((Real.exp (-((x - T.κ * n) ^ 2) / 2) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp [neg_div]
  have h0 : (0 - T.κ * n) ^ 2 / 2 = (T.κ * n) ^ 2 / 2 := by ring
  rw [h0] at hconst
  calc fcoef_dev T g n x = fcoef_dev T g n x * (((Real.exp ((x - T.κ * n) ^ 2 / 2) : ℝ) : ℂ) *
        ((Real.exp (-((x - T.κ * n) ^ 2) / 2) : ℝ) : ℂ)) := by rw [hab, mul_one]
    _ = (fcoef_dev T g n x * ((Real.exp ((x - T.κ * n) ^ 2 / 2) : ℝ) : ℂ)) *
        ((Real.exp (-((x - T.κ * n) ^ 2) / 2) : ℝ) : ℂ) := by ring
    _ = _ := by rw [hconst]

theorem fcoef_add_Lx_dev {T : Torus} {g : ℝ × ℝ → ℂ} (hg : IsLLL T g) (n : ℤ) (x : ℝ) :
    fcoef_dev T g n (x + T.Lx) = fcoef_dev T g (n - T.Nφ) x := by
  unfold fcoef_dev
  congr 1
  funext y
  rw [hg.2.2.1 x y, ← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [T.Lx_eq]
  push_cast
  ring

/-- The constants `A_n := c_n(0) e^{(κn)²/2}` of the Gaussian profiles are `N_φ`-periodic in `n`. -/
theorem fcoefA_periodic_dev {T : Torus} {g : ℝ × ℝ → ℂ} (hg : IsLLL T g) (n : ℤ) :
    fcoef_dev T g n 0 * ((Real.exp ((T.κ * n) ^ 2 / 2) : ℝ) : ℂ) =
      fcoef_dev T g (n - T.Nφ) 0 * ((Real.exp ((T.κ * ((n - T.Nφ : ℤ) : ℝ)) ^ 2 / 2) : ℝ) : ℂ) := by
  have h1 := fcoef_eq_dev hg n T.Lx
  have h2 := fcoef_add_Lx_dev hg n 0
  rw [zero_add] at h2
  rw [h2] at h1
  -- `L_x − κn = −κ(n − N_φ)`
  have e : (T.Lx - T.κ * n) ^ 2 = (T.κ * ((n - T.Nφ : ℤ) : ℝ)) ^ 2 := by
    rw [T.Lx_eq]
    push_cast
    ring
  rw [e] at h1
  have hab : ((Real.exp ((T.κ * ((n - T.Nφ : ℤ) : ℝ)) ^ 2 / 2) : ℝ) : ℂ) *
      ((Real.exp (-((T.κ * ((n - T.Nφ : ℤ) : ℝ)) ^ 2) / 2) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp [neg_div]
  rw [h1]
  calc fcoef_dev T g n 0 * ((Real.exp ((T.κ * n) ^ 2 / 2) : ℝ) : ℂ)
      = fcoef_dev T g n 0 * ((Real.exp ((T.κ * n) ^ 2 / 2) : ℝ) : ℂ) *
        (((Real.exp (-((T.κ * ((n - T.Nφ : ℤ) : ℝ)) ^ 2) / 2) : ℝ) : ℂ) *
          ((Real.exp ((T.κ * ((n - T.Nφ : ℤ) : ℝ)) ^ 2 / 2) : ℝ) : ℂ)) := by
        rw [mul_comm (((Real.exp (-((T.κ * ((n - T.Nφ : ℤ) : ℝ)) ^ 2) / 2) : ℝ) : ℂ)), hab, mul_one]
    _ = _ := by ring

/-- The Fourier series in `y` converges pointwise to `g` once the coefficients are summable. -/
theorem lll_fourier_hasSum_dev {T : Torus} {g : ℝ × ℝ → ℂ} (hg : IsLLL T g) (x y : ℝ)
    (hs : Summable fun n : ℤ => fcoef_dev T g n x) :
    HasSum (fun n : ℤ => ((1 / T.Ly : ℝ) : ℂ) * fcoef_dev T g n x *
      Complex.exp (I * ((T.κ * n : ℝ) : ℂ) * y)) (g (x, y)) := by
  have : Fact (0 < T.Ly) := ⟨T.Ly_pos⟩
  have hper : Function.Periodic (fun y => g (x, y)) T.Ly := fun y => hg.2.1 x y
  have hcont : Continuous fun y => g (x, y) := hg.1.continuous.comp (by fun_prop)
  let F : C(AddCircle T.Ly, ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hcont⟩
  have hF : ∀ y : ℝ, F (y : AddCircle T.Ly) = g (x, y) := fun y => rfl
  have hcoef : ∀ n : ℤ, fourierCoeff F n = ((1 / T.Ly : ℝ) : ℂ) * fcoef_dev T g n x := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral F n 0, zero_add, Complex.real_smul]
    unfold fcoef_dev
    congr 1
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [hF, fourier_coe_apply, smul_eq_mul]
    congr 2
    unfold Torus.κ
    push_cast
    field_simp
  have hsum : Summable (fourierCoeff F) := by
    have e : fourierCoeff F = fun n => ((1 / T.Ly : ℝ) : ℂ) * fcoef_dev T g n x := funext hcoef
    rw [e]
    exact hs.mul_left _
  have h := has_pointwise_sum_fourier_series_of_summable hsum (y : AddCircle T.Ly)
  rw [hF] at h
  convert h using 1
  funext n
  rw [hcoef, fourier_coe_apply, smul_eq_mul]
  congr 2
  unfold Torus.κ
  push_cast
  field_simp

/-- The reindexing `ℤ_{N_φ} × ℤ ≃ ℤ`, `(j, m) ↦ j̃ + m N_φ`. -/
def idxEquiv_dev (T : Torus) : ZMod T.Nφ × ℤ ≃ ℤ where
  toFun p := (p.1.val : ℤ) + p.2 * T.Nφ
  invFun n := ((n : ZMod T.Nφ), n / T.Nφ)
  left_inv p := by
    rcases p with ⟨j, m⟩
    have hj : (j.val : ℤ) < T.Nφ := by exact_mod_cast j.val_lt
    have hN : (T.Nφ : ℤ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
    ext
    · simp
    · show ((j.val : ℤ) + m * T.Nφ) / T.Nφ = m
      rw [Int.add_mul_ediv_right _ _ hN, Int.ediv_eq_zero_of_lt (by positivity) hj, zero_add]
  right_inv n := by
    show (((n : ZMod T.Nφ).val : ℕ) : ℤ) + n / T.Nφ * T.Nφ = n
    rw [ZMod.val_intCast]
    exact Int.emod_add_ediv_mul n _

theorem hasSum_regroup_dev {T : Torus} {F : ℤ → ℂ} {s : ℂ} (hF : HasSum F s) :
    s = ∑ j : ZMod T.Nφ, ∑' m : ℤ, F ((j.val : ℤ) + m * T.Nφ) := by
  have h1 : HasSum (F ∘ idxEquiv_dev T) s := (Equiv.hasSum_iff (idxEquiv_dev T)).mpr hF
  have h2 : ∀ j : ZMod T.Nφ, HasSum (fun m : ℤ => (F ∘ idxEquiv_dev T) (j, m))
      (∑' m : ℤ, F ((j.val : ℤ) + m * T.Nφ)) := fun j =>
    (h1.summable.comp_injective (Prod.mk_right_injective j)).hasSum
  exact (h1.prod_fiberwise h2).unique (hasSum_fintype _)

theorem isLLL_exists_dev {T : Torus} {g : ℝ × ℝ → ℂ} (hg : IsLLL T g) :
    ∃ f : Space T, toFun T f = g := by
  set A : ℤ → ℂ := fun n => fcoef_dev T g n 0 * ((Real.exp ((T.κ * n) ^ 2 / 2) : ℝ) : ℂ) with hA
  have hAper : ∀ n : ℤ, A n = A (n - T.Nφ) := fcoefA_periodic_dev hg
  have hAper' : ∀ (n k : ℤ), A (n + k * T.Nφ) = A n := by
    intro n k
    induction k using Int.induction_on with
    | zero => simp
    | succ i ih =>
      rw [hAper, show n + ((i : ℤ) + 1) * T.Nφ - T.Nφ = n + (i : ℤ) * T.Nφ by ring, ih]
    | pred i ih =>
      rw [show n + (-(i : ℤ) - 1) * T.Nφ = n + -(i : ℤ) * T.Nφ - T.Nφ by ring, ← hAper, ih]
  have hAres : ∀ n : ℤ, A n = A (((n : ZMod T.Nφ).val : ℕ) : ℤ) := by
    intro n
    have e := (idxEquiv_dev T).right_inv n
    change (((n : ZMod T.Nφ).val : ℕ) : ℤ) + n / T.Nφ * T.Nφ = n at e
    conv_lhs => rw [← e]
    exact hAper' _ _
  set M : ℝ := ∑ j : ZMod T.Nφ, ‖A ((j.val : ℕ) : ℤ)‖ with hM
  have hAbd : ∀ n : ℤ, ‖A n‖ ≤ M := by
    intro n
    rw [hAres n]
    exact Finset.single_le_sum (f := fun j : ZMod T.Nφ => ‖A ((j.val : ℕ) : ℤ)‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ (n : ZMod T.Nφ))
  have hLy := T.Ly_pos
  have hc : 0 < T.Ly * Real.sqrt π := by positivity
  set c0 : ℂ := ((1 / T.Ly : ℝ) : ℂ) * (((T.Ly * Real.sqrt π) ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hc0
  refine ⟨WithLp.toLp 2 (fun j : ZMod T.Nφ => c0 * A ((j.val : ℕ) : ℤ)), ?_⟩
  funext r
  rcases r with ⟨x, y⟩
  have hfc : ∀ n : ℤ, fcoef_dev T g n x = A n * ((Real.exp (-((x - T.κ * n) ^ 2) / 2) : ℝ) : ℂ) :=
    fun n => fcoef_eq_dev hg n x
  have hs : Summable fun n : ℤ => fcoef_dev T g n x := by
    refine Summable.of_norm_bounded ((Analysis.summable_gauss_int T.κ_pos x).mul_left M) fun n => ?_
    rw [hfc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm T.κ]
    exact mul_le_mul_of_nonneg_right (hAbd n) (Real.exp_pos _).le
  have h := lll_fourier_hasSum_dev hg x y hs
  have hterm : ∀ n : ℤ, ((1 / T.Ly : ℝ) : ℂ) * fcoef_dev T g n x *
      Complex.exp (I * ((T.κ * n : ℝ) : ℂ) * y) = c0 * A n * phi T n (x, y) := by
    intro n
    rw [hfc, hc0]
    unfold phi
    have hp : ((T.Ly * Real.sqrt π) ^ (1 / 2 : ℝ)) * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) = 1 := by
      rw [← Real.rpow_add hc]
      norm_num
    have hp' : (((T.Ly * Real.sqrt π) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hp, Complex.ofReal_one]
    have he : Complex.exp (I * ((T.κ * n : ℝ) : ℂ) * y) =
        Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (y : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [he]
    linear_combination (((1 / T.Ly : ℝ) : ℂ) * A n * ((Real.exp (-((x - T.κ * n) ^ 2) / 2) : ℝ) : ℂ) *
      Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (y : ℂ))) * hp'.symm
  simp_rw [hterm] at h
  rw [hasSum_regroup_dev (T := T) h]
  show ∑ j : ZMod T.Nφ, (c0 * A ((j.val : ℕ) : ℤ)) * psi T j (x, y) = _
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold psi
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [hAper']

end LLLDevices

/-- **Lemma 2.2(ii)**, completeness, in the model: a function is in the paper's `𝔥_N` if and only if it is
represented by a vector of `Space T` ("`Hence $f=(L_y\sqrt\pi)^{1/2}\sum_{j=0}^{\Nphi-1}a_j\psi_j$`"). -/
theorem isLLL_iff (T : Torus) (g : ℝ × ℝ → ℂ) : IsLLL T g ↔ ∃ f : Space T, toFun T f = g := by
  constructor
  · -- (phase (b), recruit L11, round one) the completeness: the devices above (the `y`-Fourier coefficients)
    exact isLLL_exists_dev
  · rintro ⟨f, rfl⟩
    -- (phase (b), recruit L11, round one) the vectors of `Space T` represent functions of the paper's `𝔥_N`:
    -- smoothness, (2.2) and (2.3) are linear in `f`, from `psi_contDiff`, `psi_add_Ly`, `psi_add_Lx`, `psi_lll_eq`.
    have hdx : ∀ (j : ZMod T.Nφ) (y : ℝ), Differentiable ℝ (fun x : ℝ => psi T j (x, y)) := fun j y =>
      ((psi_contDiff T j).differentiable (by simp)).comp (differentiable_id.prodMk (differentiable_const y))
    have hdy : ∀ (j : ZMod T.Nφ) (x : ℝ), Differentiable ℝ (fun y : ℝ => psi T j (x, y)) := fun j x =>
      ((psi_contDiff T j).differentiable (by simp)).comp ((differentiable_const x).prodMk differentiable_id)
    refine ⟨?_, fun x y => ?_, fun x y => ?_, fun r => ?_⟩
    · exact ContDiff.sum fun j _ => contDiff_const.mul (psi_contDiff T j)
    · simp only [toFun, psi_add_Ly]
    · simp only [toFun, psi_add_Lx, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · have ex : Dx (toFun T f) r = ∑ j, f j * Dx (psi T j) r := by
        simp only [Dx, toFun]
        rw [deriv_fun_sum fun j _ => ((hdx j r.2).differentiableAt).const_mul (f j)]
        exact Finset.sum_congr rfl fun j _ => deriv_const_mul _ (hdx j r.2).differentiableAt
      have ey : Dy (toFun T f) r = ∑ j, f j * Dy (psi T j) r := by
        simp only [Dy, toFun]
        rw [deriv_fun_sum fun j _ => ((hdy j r.1).differentiableAt).const_mul (f j), Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [deriv_const_mul _ (hdy j r.1).differentiableAt]
        ring
      rw [ex, ey, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := psi_lll_eq T j r
      linear_combination f j * this

/-- The representation `f ↦ toFun T f` is injective (with `l2inner_toFun` and `isLLL_iff`: a unitary
identification of `Space T` with the paper's `𝔥_N`). -/
theorem toFun_injective (T : Torus) : Function.Injective (toFun T) := by
  intro f g h
  have hsub : toFun T (f - g) = 0 := by
    funext R
    have := congrFun h R
    simp only [toFun] at this ⊢
    simp only [PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib, this, sub_self, Pi.zero_apply]
  have h0 : ⟪f - g, f - g⟫_ℂ = 0 := by
    rw [← l2inner_toFun, hsub]
    simp [l2inner]
  rw [inner_self_eq_zero, sub_eq_zero] at h0
  exact h0

/-- **Lemma 2.2(iii)**: "`For $f\in\hN$, $Df=D_xf=\partial_xf$, and $Df$ satisfies \eqref{eq:bc}. In
particular`" — the first two equalities. -/
theorem Dcov_eq_Dx_of_isLLL (T : Torus) {f : ℝ × ℝ → ℂ} (hf : IsLLL T f) : Dcov f = Dx f := by
  funext r
  rw [Dcov_eq]
  linear_combination (-(1 / 2 : ℂ)) * (hf.2.2.2 r)

/-- **Lemma 2.2(iii)**: "`and $Df$ satisfies \eqref{eq:bc}`". -/
theorem Dcov_bc_of_isLLL (T : Torus) {f : ℝ × ℝ → ℂ} (hf : IsLLL T f) :
    (∀ x y : ℝ, Dcov f (x, y + T.Ly) = Dcov f (x, y)) ∧
      (∀ x y : ℝ, Dcov f (x + T.Lx, y) = Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * Dcov f (x, y)) := by
  rw [Dcov_eq_Dx_of_isLLL T hf]
  refine ⟨fun x y => ?_, fun x y => ?_⟩
  · simp only [Dx]
    congr 1
    funext x'
    exact hf.2.1 x' y
  · simp only [Dx]
    have h1 : deriv (fun x' : ℝ => f (x', y)) (x + T.Lx) = deriv (fun x' : ℝ => f (x' + T.Lx, y)) x :=
      (deriv_comp_add_const (f := fun x' : ℝ => f (x', y)) (a := T.Lx) (x := x)).symm
    rw [h1]
    have h2 : (fun x' : ℝ => f (x' + T.Lx, y)) = fun x' => Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * f (x', y) := by
      funext x'; exact hf.2.2.1 x' y
    rw [h2, deriv_const_mul_field']

/-- **Lemma 2.2(iii)**: "`$(D\phi_n)(x,y)=-(x-\kappa n)\,\phi_n(x,y)$`". -/
theorem Dcov_phi (T : Torus) (n : ℤ) (x y : ℝ) :
    Dcov (phi T n) (x, y) = -((x - T.κ * n : ℝ) : ℂ) * phi T n (x, y) := by
  rw [Dcov]
  simp only []
  rw [(hasDerivAt_phi_x T n x y).deriv, (hasDerivAt_phi_y T n x y).deriv]
  push_cast
  linear_combination (-(1 / 2 : ℂ) * (T.κ : ℂ) * (n : ℂ) * phi T n (x, y) + (1 / 2 : ℂ) * (x : ℂ) * phi T n (x, y)) * Complex.I_sq

/-! ## Lemma 2.3: the evaluation vectors -/

/-- **Lemma 2.3**: "`\ev R:=\sum_{j\in\Z_{\Nphi}}\overline{\psi_j(R)}\,\psi_j`". -/
def ev (T : Torus) (R : ℝ × ℝ) : Space T :=
  ∑ j, star (psi T j R) • orb T j

/-- **Lemma 2.3**: "`\evD R:=\sum_{j\in\Z_{\Nphi}}\overline{(D\psi_j)(R)}\,\psi_j`". -/
def evD (T : Torus) (R : ℝ × ℝ) : Space T :=
  ∑ j, star (Dcov (psi T j) R) • orb T j

/-- The coordinates of `e_R`: `\overline{ψ_j(R)}`. -/
theorem ev_apply (T : Torus) (R : ℝ × ℝ) (j : ZMod T.Nφ) : ev T R j = star (psi T j R) := by
  simp [ev, orb, Pi.single_apply]

/-- The coordinates of `e^D_R`: `\overline{(Dψ_j)(R)}`. -/
theorem evD_apply (T : Torus) (R : ℝ × ℝ) (j : ZMod T.Nφ) :
    evD T R j = star (Dcov (psi T j) R) := by
  simp [evD, orb, Pi.single_apply]

/-! ### Proof devices for Lemma 2.3(i) (phase (b); not statements of the paper) -/

theorem psi_eq_val (T : Torus) (j : ZMod T.Nφ) : psi T j = psi T ((j.val : ℤ) : ZMod T.Nφ) := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem psi_hasDerivAt_x' (T : Torus) (j : ZMod T.Nφ) (x y : ℝ) :
    DifferentiableAt ℝ (fun x' : ℝ => psi T j (x', y)) x := by
  rw [psi_eq_val]; exact (psi_hasDerivAt_x T _ x y).differentiableAt

theorem psi_hasDerivAt_y' (T : Torus) (j : ZMod T.Nφ) (x y : ℝ) :
    DifferentiableAt ℝ (fun y' : ℝ => psi T j (x, y')) y := by
  rw [psi_eq_val]; exact (psi_hasDerivAt_y T _ x y).differentiableAt

theorem Dcov_const_mul (c : ℂ) (g : ℝ × ℝ → ℂ) (R : ℝ × ℝ) :
    Dcov (fun r => c * g r) R = c * Dcov g R := by
  simp only [Dcov, deriv_const_mul_field']
  ring

theorem Dcov_add (g h : ℝ × ℝ → ℂ) (R : ℝ × ℝ)
    (hgx : DifferentiableAt ℝ (fun x : ℝ => g (x, R.2)) R.1) (hhx : DifferentiableAt ℝ (fun x : ℝ => h (x, R.2)) R.1)
    (hgy : DifferentiableAt ℝ (fun y : ℝ => g (R.1, y)) R.2) (hhy : DifferentiableAt ℝ (fun y : ℝ => h (R.1, y)) R.2) :
    Dcov (fun r => g r + h r) R = Dcov g R + Dcov h R := by
  simp only [Dcov]
  rw [deriv_fun_add hgx hhx, deriv_fun_add hgy hhy]
  ring

theorem Dcov_toFun (T : Torus) (f : Space T) (R : ℝ × ℝ) :
    Dcov (toFun T f) R = ∑ j, f j * Dcov (psi T j) R := by
  have key : ∀ s : Finset (ZMod T.Nφ),
      Dcov (fun r => ∑ j ∈ s, f j * psi T j r) R = ∑ j ∈ s, f j * Dcov (psi T j) R := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Dcov]
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [Dcov_add, Dcov_const_mul, ih]
      · exact (psi_hasDerivAt_x' T a R.1 R.2).const_mul _
      · exact DifferentiableAt.fun_sum fun j _ => (psi_hasDerivAt_x' T j R.1 R.2).const_mul _
      · exact (psi_hasDerivAt_y' T a R.1 R.2).const_mul _
      · exact DifferentiableAt.fun_sum fun j _ => (psi_hasDerivAt_y' T j R.1 R.2).const_mul _
  exact key Finset.univ

theorem Dcov_psi_add_Ly (T : Torus) (j : ZMod T.Nφ) (x y : ℝ) :
    Dcov (psi T j) (x, y + T.Ly) = Dcov (psi T j) (x, y) := by
  simp only [Dcov]
  have h1 : (fun x' : ℝ => psi T j (x', y + T.Ly)) = fun x' => psi T j (x', y) :=
    funext fun x' => psi_add_Ly T j x' y
  have h2 : deriv (fun y' : ℝ => psi T j (x, y')) (y + T.Ly) = deriv (fun y' : ℝ => psi T j (x, y')) y := by
    rw [← deriv_comp_add_const]
    congr 1
    funext y'
    exact psi_add_Ly T j x y'
  rw [h1, h2, psi_add_Ly]

theorem Dcov_psi_add_Lx (T : Torus) (j : ZMod T.Nφ) (x y : ℝ) :
    Dcov (psi T j) (x + T.Lx, y) = Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * Dcov (psi T j) (x, y) := by
  simp only [Dcov]
  have hx : deriv (fun x' : ℝ => psi T j (x', y)) (x + T.Lx) =
      Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * deriv (fun x' : ℝ => psi T j (x', y)) x := by
    rw [← deriv_comp_add_const]
    have : (fun x' : ℝ => psi T j (x' + T.Lx, y)) =
        fun x' => Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * psi T j (x', y) :=
      funext fun x' => psi_add_Lx T j x' y
    rw [this, deriv_const_mul_field']
  have hE : HasDerivAt (fun y' : ℝ => Complex.exp (I * (T.Lx : ℂ) * (y' : ℂ)))
      (Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * (I * (T.Lx : ℂ) * 1)) y :=
    ((hasDerivAt_id y).ofReal_comp.const_mul (I * (T.Lx : ℂ))).cexp
  have hy : deriv (fun y' : ℝ => psi T j (x + T.Lx, y')) y =
      Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * (I * (T.Lx : ℂ) * 1) * psi T j (x, y) +
        Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * deriv (fun y' : ℝ => psi T j (x, y')) y := by
    have : (fun y' : ℝ => psi T j (x + T.Lx, y')) =
        fun y' : ℝ => Complex.exp (I * (T.Lx : ℂ) * (y' : ℂ)) * psi T j (x, y') :=
      funext fun y' => psi_add_Lx T j x y'
    rw [this, (hE.fun_mul (psi_hasDerivAt_y' T j x y).hasDerivAt).deriv]
  rw [hx, hy, psi_add_Lx]
  push_cast
  ring


/-- **Lemma 2.3(i)**: "`$\ip{\ev R}{f}=f(R)$ and $\ip{\evD R}{f}=(Df)(R)$ for every $f\in\hN$`" — the first. -/
theorem inner_ev (T : Torus) (R : ℝ × ℝ) (f : Space T) : ⟪ev T R, f⟫_ℂ = toFun T f R := by
  rw [PiLp.inner_apply, toFun]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_apply, RCLike.inner_apply]
  simp [mul_comm]

/-- **Lemma 2.3(i)**, the second: "`$\ip{\evD R}{f}=(Df)(R)$ for every $f\in\hN$`". -/
theorem inner_evD (T : Torus) (R : ℝ × ℝ) (f : Space T) :
    ⟪evD T R, f⟫_ℂ = Dcov (toFun T f) R := by
  rw [PiLp.inner_apply, Dcov_toFun]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [evD_apply, RCLike.inner_apply]
  simp [mul_comm]

/-- **Lemma 2.3(i)**: "`$\ev{R+(0,L_y)}=\ev R$ and $\ev{R+(L_x,0)}=e^{-\iu L_xR_y}\ev R$, and likewise for
$\evD R$`" — the first. -/
theorem ev_add_Ly (T : Torus) (R : ℝ × ℝ) : ev T (R + (0, T.Ly)) = ev T R := by
  refine PiLp.ext fun j => ?_
  rw [ev_apply, ev_apply]
  rcases R with ⟨x, y⟩
  rw [show ((x, y) + (0, T.Ly) : ℝ × ℝ) = (x, y + T.Ly) by simp, psi_add_Ly]

/-- **Lemma 2.3(i)**: "`$\ev{R+(L_x,0)}=e^{-\iu L_xR_y}\ev R$`". -/
theorem ev_add_Lx (T : Torus) (R : ℝ × ℝ) :
    ev T (R + (T.Lx, 0)) = Complex.exp (-(I * (T.Lx : ℂ) * (R.2 : ℂ))) • ev T R := by
  refine PiLp.ext fun j => ?_
  rw [PiLp.smul_apply, ev_apply, ev_apply]
  rcases R with ⟨x, y⟩
  rw [show ((x, y) + (T.Lx, 0) : ℝ × ℝ) = (x + T.Lx, y) by simp, psi_add_Lx, star_mul', smul_eq_mul]
  congr 1
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

/-- **Lemma 2.3(i)**: `e^D_{R+(0,L_y)} = e^D_R` ("`and likewise for $\evD R$`"). -/
theorem evD_add_Ly (T : Torus) (R : ℝ × ℝ) : evD T (R + (0, T.Ly)) = evD T R := by
  refine PiLp.ext fun j => ?_
  rw [evD_apply, evD_apply]
  rcases R with ⟨x, y⟩
  rw [show ((x, y) + (0, T.Ly) : ℝ × ℝ) = (x, y + T.Ly) by simp, Dcov_psi_add_Ly]

/-- **Lemma 2.3(i)**: `e^D_{R+(L_x,0)} = e^{−iL_xR_y} e^D_R` ("`and likewise for $\evD R$`"). -/
theorem evD_add_Lx (T : Torus) (R : ℝ × ℝ) :
    evD T (R + (T.Lx, 0)) = Complex.exp (-(I * (T.Lx : ℂ) * (R.2 : ℂ))) • evD T R := by
  refine PiLp.ext fun j => ?_
  rw [PiLp.smul_apply, evD_apply, evD_apply]
  rcases R with ⟨x, y⟩
  rw [show ((x, y) + (T.Lx, 0) : ℝ × ℝ) = (x + T.Lx, y) by simp, Dcov_psi_add_Lx, star_mul', smul_eq_mul]
  congr 1
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

/-! ### Proof device for Lemma 2.3(ii) (phase (b); not a statement of the paper) -/

theorem rankOne_ev_expand (T : Torus) (R : ℝ × ℝ) :
    InnerProductSpace.rankOne ℂ (ev T R) (ev T R) =
      ∑ i, ∑ j, (star (psi T i R) * psi T j R) • InnerProductSpace.rankOne ℂ (orb T i) (orb T j) := by
  simp only [ev, map_sum, sum_apply, map_smul, map_smulₛₗ, smul_apply,
    smul_smul, Finset.smul_sum, starRingEnd_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring


/-- **Lemma 2.3(ii)**: "`$\int_{\Tor_N}\lvert\ev R\rangle\langle\ev R\rvert\,\dd R=\one_{\hN}$`", the integral
over the fundamental domain (a Bochner integral in `𝔥_N →L 𝔥_N`; `|e_R⟩⟨e_R|` is `rankOne ℂ (e_R) (e_R)`). -/
theorem integral_rankOne_ev (T : Torus) :
    ∫ R in fundDom T, InnerProductSpace.rankOne ℂ (ev T R) (ev T R) = (1 : Space T →L[ℂ] Space T) := by
  simp_rw [rankOne_ev_expand T]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (psi_star_mul_integrableOn T i j).smul_const _]
  have e2 : ∀ i j : ZMod T.Nφ, ∫ R in fundDom T, (star (psi T i R) * psi T j R) •
      InnerProductSpace.rankOne ℂ (orb T i) (orb T j) =
      (if i = j then (1 : ℂ) else 0) • InnerProductSpace.rankOne ℂ (orb T i) (orb T j) := by
    intro i j
    rw [integral_smul_const, ← l2inner_psi T i j]
    rfl
  have e3 : ∀ i : ZMod T.Nφ, ∫ R in fundDom T, ∑ j, (star (psi T i R) * psi T j R) •
      InnerProductSpace.rankOne ℂ (orb T i) (orb T j) = InnerProductSpace.rankOne ℂ (orb T i) (orb T i) := by
    intro i
    rw [integral_finsetSum _ fun j _ => (psi_star_mul_integrableOn T i j).smul_const _]
    simp_rw [e2]
    simp
  simp_rw [e3]
  ext v : 1
  rw [sum_apply]
  simp only [InnerProductSpace.rankOne_apply, one_apply_eq_self]
  have := (orbBasis T).sum_repr' v
  simp only [orbBasis_apply] at this
  exact this

/-- `q_{pk}^2` of Lemma 2.3(iii): "`$q_{pk}^2:=p^2L_x^2+k^2L_y^2$`" for `(p, k) ∈ ℤ²`. -/
def qsq (T : Torus) (pk : ℤ × ℤ) : ℝ :=
  (pk.1 : ℝ) ^ 2 * T.Lx ^ 2 + (pk.2 : ℝ) ^ 2 * T.Ly ^ 2

/-- **Lemma 2.3(iii)**, the first formula (as a `HasSum` over `ℤ²`, which includes the convergence):
"`\norm{\ev R}^2&=\frac1{2\pi}\sum_{(p,k)\in\Z^2}e^{-q_{pk}^2/4}\cos(kL_yR_x+pL_xR_y)`". -/
theorem norm_ev_sq (T : Torus) (R : ℝ × ℝ) :
    HasSum (fun pk : ℤ × ℤ => 1 / (2 * π) * Real.exp (-qsq T pk / 4) *
        Real.cos (pk.2 * T.Ly * R.1 + pk.1 * T.Lx * R.2)) (‖ev T R‖ ^ 2) := by
  -- block C's proof (L9), through the devices of `HRTorus.LLL.Theta`
  have hz : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have e1 : (∑ j : ZMod T.Nφ, star (psi T j R) * psi T j R).re = ‖ev T R‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz, ev_apply, norm_star]
  have h := Complex.hasSum_re (hasSum_Gev T R)
  rw [e1] at h
  convert h using 1
  funext pk
  simp only [Gev, qsq]
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Lemma 2.3(iii)**, the second formula:
"`\norm{\evD R}^2&=\frac1{4\pi}\sum_{(p,k)\in\Z^2}\Bigl(1-\frac{q_{pk}^2}2\Bigr)e^{-q_{pk}^2/4}\cos(kL_yR_x+pL_xR_y)`". -/
theorem norm_evD_sq (T : Torus) (R : ℝ × ℝ) :
    HasSum (fun pk : ℤ × ℤ => 1 / (4 * π) * (1 - qsq T pk / 2) * Real.exp (-qsq T pk / 4) *
        Real.cos (pk.2 * T.Ly * R.1 + pk.1 * T.Lx * R.2)) (‖evD T R‖ ^ 2) := by
  -- block C's proof (L9), through the devices of `HRTorus.LLL.Theta`
  have hz : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have e1 : (∑ j : ZMod T.Nφ, star (Dcov (psi T j) R) * Dcov (psi T j) R).re = ‖evD T R‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz, evD_apply, norm_star]
  have h := Complex.hasSum_re (hasSum_GevD T R)
  rw [e1] at h
  convert h using 1
  funext pk
  simp only [GevD, qsq]
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Lemma 2.3(iv)**, the first bound: "`Let $L_{\min}:=\min\{L_x,L_y\}\ge4$`", then for every `R`,
"`\bigl\lvert2\pi\norm{\ev R}^2-1\bigr\rvert\le4.2\,e^{-L_{\min}^2/4}\le0.08`". -/
theorem norm_ev_sq_bound (T : Torus) (hL : 4 ≤ min T.Lx T.Ly) (R : ℝ × ℝ) :
    |2 * π * ‖ev T R‖ ^ 2 - 1| ≤ 4.2 * Real.exp (-(min T.Lx T.Ly) ^ 2 / 4) ∧
      4.2 * Real.exp (-(min T.Lx T.Ly) ^ 2 / 4) ≤ 0.08 := by
  -- block C's proof (L9), through the devices of `HRTorus.LLL.Theta`
  have hx : 4 ≤ T.Lx := le_trans hL (min_le_left _ _)
  have hy : 4 ≤ T.Ly := le_trans hL (min_le_right _ _)
  have h := lattice_bound_ev hx hy (fun pk : ℤ × ℤ => pk.2 * T.Ly * R.1 + pk.1 * T.Lx * R.2) (by simp)
    (norm_ev_sq T R)
  have h2 := (eps_facts hL le_rfl).2.2.1
  rw [neg_div]
  exact ⟨h, by linarith⟩

/-- **Lemma 2.3(iv)**, the second bound:
"`\bigl\lvert4\pi\norm{\evD R}^2-1\bigr\rvert\le2.1\,L_{\min}^2e^{-L_{\min}^2/4}\le0.62`". -/
theorem norm_evD_sq_bound (T : Torus) (hL : 4 ≤ min T.Lx T.Ly) (R : ℝ × ℝ) :
    |4 * π * ‖evD T R‖ ^ 2 - 1| ≤ 2.1 * (min T.Lx T.Ly) ^ 2 * Real.exp (-(min T.Lx T.Ly) ^ 2 / 4) ∧
      2.1 * (min T.Lx T.Ly) ^ 2 * Real.exp (-(min T.Lx T.Ly) ^ 2 / 4) ≤ 0.62 := by
  -- block C's proof (L9), through the devices of `HRTorus.LLL.Theta`
  have hx : 4 ≤ T.Lx := le_trans hL (min_le_left _ _)
  have hy : 4 ≤ T.Ly := le_trans hL (min_le_right _ _)
  have h := lattice_bound_evD hx hy (fun pk : ℤ × ℤ => pk.2 * T.Ly * R.1 + pk.1 * T.Lx * R.2) (by simp)
    (norm_evD_sq T R)
  have h1 := mul_exp_anti (s := 16) (t := (min T.Lx T.Ly) ^ 2) (by norm_num) (by nlinarith)
  have h2 : Real.exp (-((16 : ℝ) / 4)) < 0.01832 := by
    rw [show -((16 : ℝ) / 4) = -4 by norm_num]
    exact exp_neg_four_lt
  rw [neg_div]
  exact ⟨h, by nlinarith⟩

/-! ## §2.2: the magnetic translations -/

/-- (2.5) on functions: "`(\thx f)(x,y):=e^{\iu\kappa y}f(x-\kappa,y),\qquad(\thy f)(x,y):=f(x,y+L_y/\Nphi)`" —
the first. -/
def thxFun (T : Torus) (f : ℝ × ℝ → ℂ) (r : ℝ × ℝ) : ℂ :=
  Complex.exp (I * (T.κ : ℂ) * (r.2 : ℂ)) * f (r.1 - T.κ, r.2)

/-- (2.5) on functions, the second: "`(\thy f)(x,y):=f(x,y+L_y/\Nphi)`". -/
def thyFun (T : Torus) (f : ℝ × ℝ → ℂ) (r : ℝ × ℝ) : ℂ :=
  f (r.1, r.2 + T.Ly / (T.Nφ : ℝ))

/-- The matrix of `θ_x` on `𝔥_N` in the orbital basis: the cyclic shift `ψ_j ↦ ψ_{j+1}`
(entry `(i, j)` is `1` if `i = j + 1`). -/
def thxMat (T : Torus) : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ :=
  Matrix.of fun i j => if i = j + 1 then 1 else 0

/-- The matrix of `θ_y` on `𝔥_N`: diagonal, `ψ_j ↦ e^{2πij/N_φ} ψ_j` (`j.val` the representative in
`{0, …, N_φ − 1}`; the phase depends only on the class). -/
def thyMat (T : Torus) : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ :=
  Matrix.diagonal fun j => Complex.exp (2 * π * I * (j.val : ℂ) / (T.Nφ : ℂ))

/-- `θ_x` as an operator on `𝔥_N`. -/
def thx (T : Torus) : Space T →L[ℂ] Space T :=
  Matrix.toEuclideanCLM (n := ZMod T.Nφ) (𝕜 := ℂ) (thxMat T)

/-- `θ_y` as an operator on `𝔥_N`. -/
def thy (T : Torus) : Space T →L[ℂ] Space T :=
  Matrix.toEuclideanCLM (n := ZMod T.Nφ) (𝕜 := ℂ) (thyMat T)

/-! ### Proof devices for Lemma 2.4 (phase (b); not statements of the paper) -/

theorem phi_shift (T : Torus) (n : ℤ) (x y : ℝ) :
    Complex.exp (I * (T.κ : ℂ) * (y : ℂ)) * phi T n (x - T.κ, y) = phi T (n + 1) (x, y) := by
  unfold phi
  simp only []
  have hg : Real.exp (-((x - T.κ - T.κ * n) ^ 2) / 2) =
      Real.exp (-((x - T.κ * ((n + 1 : ℤ) : ℝ)) ^ 2) / 2) := by
    congr 2; push_cast; ring
  have hp : Complex.exp (I * (T.κ : ℂ) * (y : ℂ)) * Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (y : ℂ)) =
      Complex.exp (I * (T.κ : ℂ) * (((n + 1 : ℤ)) : ℂ) * (y : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hg, ← hp]
  ring

theorem phi_yshift (T : Torus) (n : ℤ) (x y : ℝ) :
    phi T n (x, y + T.Ly / (T.Nφ : ℝ)) =
      Complex.exp (2 * π * I * (n : ℂ) / (T.Nφ : ℂ)) * phi T n (x, y) := by
  unfold phi
  have hk : (T.κ : ℂ) * (T.Ly : ℂ) = 2 * π := by exact_mod_cast Torus.κ_mul_Ly T
  have hN : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
  have hp : Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * ((y + T.Ly / (T.Nφ : ℝ) : ℝ) : ℂ)) =
      Complex.exp (2 * π * I * (n : ℂ) / (T.Nφ : ℂ)) * Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (y : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (I * (n : ℂ) * (T.Nφ : ℂ)⁻¹) * hk
  simp only []
  rw [hp]
  ring

/-- The phase `e^{2πi x/N_φ}` depends on `x` only modulo `N_φ`. -/
theorem phase_val (T : Torus) (x : ℤ) :
    Complex.exp (2 * π * I * (((x : ZMod T.Nφ).val : ℕ) : ℂ) / (T.Nφ : ℂ)) =
      Complex.exp (2 * π * I * (x : ℂ) / (T.Nφ : ℂ)) := by
  have hN : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
  have hv : (((x : ZMod T.Nφ).val : ℕ) : ℂ) = ((x % (T.Nφ : ℤ) : ℤ) : ℂ) := by
    rw [← ZMod.val_intCast]; push_cast; rfl
  rw [hv, Int.emod_def]
  rw [show 2 * π * I * (((x - (T.Nφ : ℤ) * (x / (T.Nφ : ℤ)) : ℤ)) : ℂ) / (T.Nφ : ℂ) =
      2 * π * I * (x : ℂ) / (T.Nφ : ℂ) + ((-(x / (T.Nφ : ℤ)) : ℤ) : ℂ) * (2 * π * I) by
    push_cast; field_simp; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem phase_succ (T : Torus) (k : ZMod T.Nφ) :
    Complex.exp (2 * π * I * (((k + 1).val : ℕ) : ℂ) / (T.Nφ : ℂ)) =
      Complex.exp (2 * π * I / (T.Nφ : ℂ)) * Complex.exp (2 * π * I * ((k.val : ℕ) : ℂ) / (T.Nφ : ℂ)) := by
  have hk : k + 1 = (((k.val : ℤ) + 1 : ℤ) : ZMod T.Nφ) := by push_cast; rw [ZMod.natCast_zmod_val]
  rw [hk, phase_val, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem thx_apply (T : Torus) (f : Space T) (i : ZMod T.Nφ) : thx T f i = f (i - 1) := by
  show (Matrix.toEuclideanCLM (n := ZMod T.Nφ) (𝕜 := ℂ) (thxMat T) f).ofLp i = f (i - 1)
  rw [Matrix.ofLp_toEuclideanCLM]
  simp only [Matrix.mulVec, dotProduct, thxMat, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (i - 1)]
  · simp
  · intro b _ hb; rw [ite_eq_right]; intro h; exact hb (by rw [h]; ring)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem thy_apply (T : Torus) (f : Space T) (i : ZMod T.Nφ) :
    thy T f i = Complex.exp (2 * π * I * (i.val : ℂ) / (T.Nφ : ℂ)) * f i := by
  show (Matrix.toEuclideanCLM (n := ZMod T.Nφ) (𝕜 := ℂ) (thyMat T) f).ofLp i = _
  rw [Matrix.ofLp_toEuclideanCLM, thyMat, Matrix.mulVec_diagonal]

theorem toEuclideanCLM_mem_unitary {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (h : Aᴴ * A = 1) :
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A ∈ unitary (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) := by
  rw [Unitary.mem_iff, ← map_star, ← map_mul, ← map_mul, Matrix.star_eq_conjTranspose, h,
    mul_eq_one_comm.mp h, map_one]
  exact ⟨rfl, rfl⟩

theorem thxMat_unitary_dev (T : Torus) : (thxMat T)ᴴ * thxMat T = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, thxMat, Matrix.of_apply, apply_ite star, star_one, star_zero,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

theorem star_phase_mul_self (T : Torus) (v : ℂ) (hv : star v = v) :
    star (Complex.exp (2 * π * I * v / (T.Nφ : ℂ))) * Complex.exp (2 * π * I * v / (T.Nφ : ℂ)) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have hNr : (starRingEnd ℂ) (T.Nφ : ℂ) = (T.Nφ : ℂ) := Complex.conj_natCast _
  have hvr : (starRingEnd ℂ) v = v := by rw [← Complex.star_def]; exact hv
  rw [map_div₀, map_mul, map_mul, map_mul, hNr, hvr, Complex.conj_I, Complex.conj_ofReal]
  simp only [map_ofNat]
  rw [show 2 * (π : ℂ) * -I * v / (T.Nφ : ℂ) + 2 * π * I * v / (T.Nφ : ℂ) = 0 by ring, Complex.exp_zero]

theorem thyMat_unitary_dev (T : Torus) : (thyMat T)ᴴ * thyMat T = 1 := by
  rw [thyMat, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  rw [Pi.star_apply]
  exact star_phase_mul_self T _ (star_natCast _)

theorem thxMat_pow_apply (T : Torus) (n : ℕ) (i k : ZMod T.Nφ) :
    (thxMat T ^ n) i k = if i = k + n then 1 else 0 := by
  induction n generalizing i with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [ih]
    simp only [thxMat, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (i - 1)]
    · simp only [sub_add_cancel, ite_true]
      push_cast
      by_cases h : i - 1 = k + n
      · rw [ite_eq_left h, ite_eq_left (by rw [← add_assoc, ← h]; ring)]
      · rw [ite_eq_right h, ite_eq_right (by intro h'; exact h (by rw [h']; ring))]
    · intro b _ hb; rw [ite_eq_right]; intro h; exact hb (by rw [h]; ring)
    · intro h; exact absurd (Finset.mem_univ _) h

/-- `D` commutes with `θ_x` at a point, for a function differentiable along the vertical line. -/
theorem Dcov_thxFun_at (T : Torus) (g : ℝ × ℝ → ℂ) (x y : ℝ)
    (hgy : DifferentiableAt ℝ (fun y' : ℝ => g (x - T.κ, y')) y) :
    Dx (thxFun T g) (x, y) = thxFun T (Dx g) (x, y) ∧ Dy (thxFun T g) (x, y) = thxFun T (Dy g) (x, y) := by
  have hE : HasDerivAt (fun y' : ℝ => Complex.exp (I * (T.κ : ℂ) * (y' : ℂ)))
      (Complex.exp (I * (T.κ : ℂ) * (y : ℂ)) * (I * (T.κ : ℂ) * 1)) y :=
    ((hasDerivAt_id y).ofReal_comp.const_mul (I * (T.κ : ℂ))).cexp
  constructor
  · show deriv (fun x' : ℝ => Complex.exp (I * (T.κ : ℂ) * (y : ℂ)) * g (x' - T.κ, y)) x =
      Complex.exp (I * (T.κ : ℂ) * (y : ℂ)) * deriv (fun x' : ℝ => g (x', y)) (x - T.κ)
    rw [deriv_const_mul_field']
    beta_reduce
    rw [deriv_comp_sub_const (f := fun x' : ℝ => g (x', y))]
  · simp only [Dy, thxFun]
    rw [(hE.fun_mul hgy.hasDerivAt).deriv]
    push_cast
    ring


/-- **Lemma 2.4(i)** on functions: "`$\thx$ and $\thy$ restrict to unitary operators on $\hN$, with
$\thx\psi_j=\psi_{j+1}$ and $\thy\psi_j=e^{2\pi\iu j/\Nphi}\psi_j$`" — `θ_x ψ_j = ψ_{j+1}` as functions. -/
theorem thxFun_psi (T : Torus) (j : ZMod T.Nφ) : thxFun T (psi T j) = psi T (j + 1) := by
  funext r
  rcases r with ⟨x, y⟩
  simp only [thxFun]
  have hj : j + 1 = (((j.val : ℤ) + 1 : ℤ) : ZMod T.Nφ) := by push_cast; rw [ZMod.natCast_zmod_val]
  rw [hj, psi_intCast, psi_eq_val T j, psi_intCast, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [phi_shift]
  congr 1
  ring

/-- **Lemma 2.4(i)** on functions: "`$\thy\psi_j=e^{2\pi\iu j/\Nphi}\psi_j$`". -/
theorem thyFun_psi (T : Torus) (j : ZMod T.Nφ) :
    thyFun T (psi T j) = fun r => Complex.exp (2 * π * I * (j.val : ℂ) / (T.Nφ : ℂ)) * psi T j r := by
  funext r
  rcases r with ⟨x, y⟩
  simp only [thyFun]
  unfold psi
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [phi_yshift]
  congr 1
  have hN : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
  rw [show 2 * π * I * ((((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ)) : ℂ) / (T.Nφ : ℂ) =
      2 * π * I * ((j.val : ℕ) : ℂ) / (T.Nφ : ℂ) + (m : ℂ) * (2 * π * I) by
    push_cast; field_simp]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Lemma 2.4(i)**, the bridge: on the represented functions, `thx` acts as the paper's `θ_x` ("`$\thx$ and $\thy$
restrict to unitary operators on $\hN$`"). -/
theorem toFun_thx (T : Torus) (f : Space T) : toFun T (thx T f) = thxFun T (toFun T f) := by
  funext r
  rcases r with ⟨x, y⟩
  simp only [toFun, thxFun, thx_apply]
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (1 : ZMod T.Nφ))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [← thxFun_psi]
  simp only [thxFun]
  ring

/-- **Lemma 2.4(i)**, the bridge for `θ_y` ("`$\thx$ and $\thy$ restrict to unitary operators on $\hN$`"). -/
theorem toFun_thy (T : Torus) (f : Space T) : toFun T (thy T f) = thyFun T (toFun T f) := by
  funext r
  simp only [toFun, thyFun, thy_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := congrFun (thyFun_psi T k) r
  simp only [thyFun] at this
  rw [this]
  ring

/-- **Lemma 2.4(i)** on `𝔥_N`: "`$\thx\psi_j=\psi_{j+1}$`". -/
theorem thx_orb (T : Torus) (j : ZMod T.Nφ) : thx T (orb T j) = orb T (j + 1) := by
  refine PiLp.ext fun i => ?_
  rw [thx_apply]
  simp only [orb, PiLp.single_apply]
  by_cases h : i = j + 1
  · rw [ite_eq_left h, ite_eq_left (by rw [h]; ring)]
  · rw [ite_eq_right h, ite_eq_right (by intro h'; exact h (by rw [← h']; ring))]

/-- **Lemma 2.4(i)** on `𝔥_N`: "`$\thy\psi_j=e^{2\pi\iu j/\Nphi}\psi_j$`". -/
theorem thy_orb (T : Torus) (j : ZMod T.Nφ) :
    thy T (orb T j) = Complex.exp (2 * π * I * (j.val : ℂ) / (T.Nφ : ℂ)) • orb T j := by
  refine PiLp.ext fun i => ?_
  rw [thy_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [orb, PiLp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- **Lemma 2.4(i)**: `θ_x` is unitary on `𝔥_N` ("`$\thx$ and $\thy$ restrict to unitary operators on $\hN$`"). -/
theorem thx_mem_unitary (T : Torus) : thx T ∈ unitary (Space T →L[ℂ] Space T) := by
  exact toEuclideanCLM_mem_unitary (thxMat_unitary_dev T)

/-- **Lemma 2.4(i)**: `θ_y` is unitary on `𝔥_N` ("`$\thx$ and $\thy$ restrict to unitary operators on $\hN$`"). -/
theorem thy_mem_unitary (T : Torus) : thy T ∈ unitary (Space T →L[ℂ] Space T) := by
  exact toEuclideanCLM_mem_unitary (thyMat_unitary_dev T)

/-- **Lemma 2.4(ii)**: "`On $\hN$, $\thy\thx=e^{2\pi\iu/\Nphi}\thx\thy$ and $\thx^{\Nphi}=\thy^{\Nphi}=\one$`" —
the commutation relation. -/
theorem thy_mul_thx (T : Torus) :
    thy T * thx T = Complex.exp (2 * π * I / (T.Nφ : ℂ)) • (thx T * thy T) := by
  have hm : thyMat T * thxMat T = Complex.exp (2 * π * I / (T.Nφ : ℂ)) • (thxMat T * thyMat T) := by
    ext i k
    rw [Matrix.smul_apply, smul_eq_mul, thyMat, Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [thxMat, Matrix.of_apply]
    by_cases h : i = k + 1
    · rw [ite_eq_left h, h, phase_succ]; ring
    · rw [ite_eq_right h]; ring
  show Matrix.toEuclideanCLM (n := ZMod T.Nφ) (𝕜 := ℂ) (thyMat T) *
    Matrix.toEuclideanCLM (n := ZMod T.Nφ) (𝕜 := ℂ) (thxMat T) = _
  rw [← map_mul, hm, map_smul, map_mul]
  rfl

/-- **Lemma 2.4(ii)**: "`$\thx^{\Nphi}=\thy^{\Nphi}=\one$`" — for `θ_x`. -/
theorem thx_pow (T : Torus) : thx T ^ T.Nφ = 1 := by
  have hm : thxMat T ^ T.Nφ = 1 := by
    ext i k
    rw [thxMat_pow_apply, ZMod.natCast_self, add_zero, Matrix.one_apply]
  show (Matrix.toEuclideanCLM (n := ZMod T.Nφ) (𝕜 := ℂ) (thxMat T)) ^ T.Nφ = 1
  rw [← map_pow, hm, map_one]

/-- **Lemma 2.4(ii)**: "`$\thx^{\Nphi}=\thy^{\Nphi}=\one$`" — for `θ_y`. -/
theorem thy_pow (T : Torus) : thy T ^ T.Nφ = 1 := by
  have hm : thyMat T ^ T.Nφ = 1 := by
    rw [thyMat, Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext j
    rw [Pi.pow_apply, ← Complex.exp_nat_mul]
    have hN : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
    rw [show (T.Nφ : ℂ) * (2 * π * I * ((j.val : ℕ) : ℂ) / (T.Nφ : ℂ)) = ((j.val : ℕ) : ℂ) * (2 * π * I) by
      field_simp]
    exact Complex.exp_nat_mul_two_pi_mul_I _
  show (Matrix.toEuclideanCLM (n := ZMod T.Nφ) (𝕜 := ℂ) (thyMat T)) ^ T.Nφ = 1
  rw [← map_pow, hm, map_one]

/-- **Lemma 2.4(iii)**: "`$\thx$ and $\thy$ commute with $D_x$ and $D_y$ on smooth functions, hence with
$D$`" — for `θ_x`. -/
theorem thxFun_comm_D (T : Torus) {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    Dx (thxFun T f) = thxFun T (Dx f) ∧ Dy (thxFun T f) = thxFun T (Dy f) ∧
      Dcov (thxFun T f) = thxFun T (Dcov f) := by
  have hd : ∀ x y : ℝ, DifferentiableAt ℝ (fun y' : ℝ => f (x - T.κ, y')) y := by
    intro x y
    have h1 : Differentiable ℝ f := hf.differentiable (by simp)
    exact (h1.comp (differentiable_const _ |>.prodMk differentiable_id)).differentiableAt
  have h1 : Dx (thxFun T f) = thxFun T (Dx f) := funext fun r => (Dcov_thxFun_at T f r.1 r.2 (hd r.1 r.2)).1
  have h2 : Dy (thxFun T f) = thxFun T (Dy f) := funext fun r => (Dcov_thxFun_at T f r.1 r.2 (hd r.1 r.2)).2
  refine ⟨h1, h2, ?_⟩
  funext r
  rw [Dcov_eq, h1, h2]
  simp only [thxFun, Dcov_eq]
  ring

/-- **Lemma 2.4(iii)** for `θ_y`: "`$\thx$ and $\thy$ commute with $D_x$ and $D_y$ on smooth functions, hence with $D$`". -/
theorem thyFun_comm_D (T : Torus) {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    Dx (thyFun T f) = thyFun T (Dx f) ∧ Dy (thyFun T f) = thyFun T (Dy f) ∧
      Dcov (thyFun T f) = thyFun T (Dcov f) := by
  have h1 : Dx (thyFun T f) = thyFun T (Dx f) := by
    funext r; rfl
  have h2 : Dy (thyFun T f) = thyFun T (Dy f) := by
    funext r
    simp only [Dy, thyFun]
    congr 1
    exact deriv_comp_add_const (f := fun y' : ℝ => f (r.1, y')) (a := T.Ly / (T.Nφ : ℝ)) (x := r.2)
  refine ⟨h1, h2, ?_⟩
  funext r
  rw [Dcov_eq, h1, h2]
  simp only [thyFun, Dcov_eq]

/-- **Lemma 2.4(iv)**: "`$\thx\ev R=e^{\iu\kappa R_y}\ev{R+\kappa\ex}$ and
$\thx\evD R=e^{\iu\kappa R_y}\evD{R+\kappa\ex}$`" — the first (`e_x = (1, 0)`). -/
theorem thx_ev (T : Torus) (R : ℝ × ℝ) :
    thx T (ev T R) = Complex.exp (I * (T.κ : ℂ) * (R.2 : ℂ)) • ev T (R + (T.κ, 0)) := by
  refine PiLp.ext fun i => ?_
  rw [thx_apply, PiLp.smul_apply, smul_eq_mul, ev_apply, ev_apply]
  rcases R with ⟨x, y⟩
  have h := congrFun (thxFun_psi T (i - 1)) (x + T.κ, y)
  rw [sub_add_cancel] at h
  simp only [thxFun, add_sub_cancel_right] at h
  rw [show ((x, y) + (T.κ, 0) : ℝ × ℝ) = (x + T.κ, y) by simp, ← h, star_mul', ← mul_assoc]
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  rw [show I * (T.κ : ℂ) * (((x, y) : ℝ × ℝ).2 : ℂ) + (starRingEnd ℂ) (I * (T.κ : ℂ) * (y : ℂ)) = 0 by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]]
  rw [Complex.exp_zero, one_mul]

/-- **Lemma 2.4(iv)**, the second: "`$\thx\evD R=e^{\iu\kappa R_y}\evD{R+\kappa\ex}$`". -/
theorem thx_evD (T : Torus) (R : ℝ × ℝ) :
    thx T (evD T R) = Complex.exp (I * (T.κ : ℂ) * (R.2 : ℂ)) • evD T (R + (T.κ, 0)) := by
  refine PiLp.ext fun i => ?_
  rw [thx_apply, PiLp.smul_apply, smul_eq_mul, evD_apply, evD_apply]
  rcases R with ⟨x, y⟩
  have hfun : psi T i = thxFun T (psi T (i - 1)) := by rw [thxFun_psi, sub_add_cancel]
  have hd := Dcov_thxFun_at T (psi T (i - 1)) (x + T.κ) y (psi_hasDerivAt_y' T (i - 1) _ y)
  have h : Dcov (psi T i) (x + T.κ, y) = Complex.exp (I * (T.κ : ℂ) * (y : ℂ)) * Dcov (psi T (i - 1)) (x, y) := by
    rw [hfun, Dcov_eq, hd.1, hd.2]
    simp only [thxFun, add_sub_cancel_right, Dcov_eq]
    ring
  rw [show ((x, y) + (T.κ, 0) : ℝ × ℝ) = (x + T.κ, y) by simp, h, star_mul', ← mul_assoc]
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  rw [show I * (T.κ : ℂ) * (((x, y) : ℝ × ℝ).2 : ℂ) + (starRingEnd ℂ) (I * (T.κ : ℂ) * (y : ℂ)) = 0 by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]]
  rw [Complex.exp_zero, one_mul]

/-! ## The one-body space `𝔨_N = 𝔥_N ⊗ ℂ²` (Definition 2.5) -/

/-- `g ⊗ σ ∈ ℓ²(ι) ⊗ ℂ² = ℓ²(ι × {↑,↓})` for `g ∈ ℓ²(ι)` and `σ` a standard basis vector of `ℂ²`
(used with `ι = ℤ_{N_φ}` here and `ι = 𝒮` on the slot side). -/
def spinTensor {ι : Type*} [Fintype ι] (g : EuclideanSpace ℂ ι) (σ : Spin) : EuclideanSpace ℂ (ι × Spin) :=
  WithLp.toLp 2 fun μ => if μ.2 = σ then g μ.1 else 0

/-- **Definition 2.5**: "`Let $\kN:=\hN\otimes\C^2$, with the orthonormal basis $\psi_j\otimes\sigma$`"; modelled as
`ℓ²(ℤ_{N_φ} × {↑,↓})`, indexed by the modes `(j, σ)` of the Jordan–Wigner model. -/
abbrev Space2 (T : Torus) : Type := EuclideanSpace ℂ (Mode (ZMod T.Nφ))

/-- `ψ_j ⊗ σ` is the standard basis vector of the mode `(j, σ)`. -/
theorem spinTensor_orb (T : Torus) (j : ZMod T.Nφ) (σ : Spin) :
    spinTensor (orb T j) σ = EuclideanSpace.single ((j, σ) : Mode (ZMod T.Nφ)) 1 := by
  refine PiLp.ext fun μ => ?_
  rcases μ with ⟨i, τ⟩
  simp only [spinTensor, orb, WithLp.ofLp_toLp, PiLp.single_apply, Prod.mk.injEq]
  by_cases h1 : i = j <;> by_cases h2 : τ = σ <;> simp [h1, h2]

/-- `⟨f ⊗ σ, g ⊗ τ⟩ = ⟨f, g⟩ δ_{στ}`: with `spinTensor_orb`, the `ψ_j ⊗ σ` are an orthonormal basis of `𝔨_N`. -/
theorem inner_spinTensor {ι : Type*} [Fintype ι] (f g : EuclideanSpace ℂ ι) (σ τ : Spin) :
    ⟪spinTensor f σ, spinTensor g τ⟫_ℂ = if σ = τ then ⟪f, g⟫_ℂ else 0 := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [spinTensor, WithLp.ofLp_toLp]
  rw [Finset.sum_comm]
  have hs : ∀ (F : Spin → ℂ), ∑ ρ : Spin, F ρ = F .up + F .dn := fun F => by
    rw [show (Finset.univ : Finset Spin) = {Spin.up, Spin.dn} from rfl, Finset.sum_pair (by decide)]
  rw [hs]
  cases σ <;> cases τ <;> simp [RCLike.inner_apply]

end HRTorus.LLL
