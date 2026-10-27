import HRTorus.Laughlin.GramPoisson
import HRTorus.SlotFrame.Analysis
import HRTorus.SlotFrame.SlotFrame
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Gaussian theta sums with a period, and Parseval on the rectangle (`LLL.Theta`: proof devices for `LLL.Space` and `Fock.Hamiltonian`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24, in block C's proof phase (review L9a, rulings 2 and 10: a new
upstream module imported by `HRTorus.LLL.Space`, reusing `HRTorus.Laughlin.GramPoisson`). **Every declaration here is a
proof device, not a statement of the paper; there is no `sorry`, and nothing here depends on an open statement.**
The devices, for block A's Lemma 2.3(iii)–(iv) (`HRTorus.LLL.Space`) and Definition 2.7's lattice-sum form
(`HRTorus.Fock.Vcoef_latticeSum`), in four groups:

* Poisson summation over the lattice `κℤ` for the Gaussian `e^{−u²}` (`gauss_poisson`, from Mathlib's
  `Complex.tsum_exp_neg_quadratic`) and for the quadratic weight `(u² − M²/4) e^{−u²}` (`quad_poisson`, GramPoisson's `g`
  at `κ = √2` by `scaled_poisson_g`, its `coset_poisson` with the period `2` replaced by `λ`) — the two sums the proof of
  Lemma 2.3(iii) of the HR paper ("`By the Poisson summation formula`") evaluates;
* the lattice sums of `‖e_R‖² = Σ_j |ψ_j(R)|²` and `‖e^D_R‖² = Σ_j |(Dψ_j)(R)|²`: the relabelling of `(j, m, m')` as
  `(n, p)` (`zmodIntEquiv`, `sum_zmod_tsum`, `sum_star_tsum_mul_tsum`), the closed forms of `conj(φ_n) φ_{n+pN_φ}` and of
  its `D`-analogue, the summable majorants, and the complex series `hasSum_Gev`, `hasSum_GevD` (device definitions
  `Dphi`, `Gev`, `GevD`, `zmodIntEquiv`);
* for (iv), geometric majorants of the one-dimensional theta sums (device definitions `thetaMaj`, `chiMaj`), the
  monotonicity of `t e^{−t/4}`, the bound `e^{−4} < 0.01832` (from Mathlib's `e > 2.7182818283`, whence the import of
  `Mathlib.Analysis.Complex.ExponentialBounds`), and the cores `lattice_bound_ev`, `lattice_bound_evD`, which the
  proofs in `Space` specialize;
* for `Vcoef_latticeSum`, Parseval's identity on the rectangle `[0, L_x) × [0, L_y)` for doubly periodic continuous
  functions (`parseval_rect`, through Mathlib's `UnitAddTorus.hasSum_prod_mFourierCoeff`, whence the import of
  `Mathlib.Analysis.Fourier.AddCircleMulti`; device definitions `torusMk`, `torusLift`, `rectFT`) and the Fourier
  coefficients of the Laplacian (`rectFT_lap`, two integrations by parts in each variable).
-/

open Real Complex MeasureTheory Filter Asymptotics
open scoped Real FourierTransform

noncomputable section

namespace HRTorus.LLL

open HRTorus.Laughlin.GramPoisson

/-- Device: Poisson summation with period `λ > 0` for GramPoisson's `g κ M`:
`Σ_t g(c + λt) = λ⁻¹ Σ_k ĝ(k/λ) e^{2πikc/λ}`, both series summable (the proof of GramPoisson's `coset_poisson`, the
period `2` replaced by `λ`). -/
theorem scaled_poisson_g {κ lam : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (M c : ℝ) :
    Summable (fun t : ℤ => g κ M (c + lam * t)) ∧
      Summable (fun k : ℤ => (gHat κ M (k / lam) : ℂ) * Complex.exp (2 * π * I * k * c / lam)) ∧
      ((∑' t : ℤ, g κ M (c + lam * t) : ℝ) : ℂ) =
        1 / lam * ∑' k : ℤ, (gHat κ M (k / lam) : ℂ) * Complex.exp (2 * π * I * k * c / lam) := by
  have hFT := (fourier_g hκ M).2
  have hlam0 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have hre : ∀ r : ℝ, 0 < r → (((-r : ℝ) : ℂ)).re < 0 := fun r hr => by
    rw [Complex.ofReal_re]; linarith
  set h : ℝ → ℂ := fun y => (g κ M (lam * y) : ℂ) with hh
  have hcont : Continuous h := by simp only [hh, g]; fun_prop
  have hFh : ∀ ξ : ℝ, 𝓕 h ξ = (1 / lam : ℂ) * (gHat κ M (ξ / lam) : ℂ) := by
    intro ξ
    have hcv := Measure.integral_comp_mul_left
      (fun v : ℝ => Complex.exp (-(2 * π * I * v * ((ξ / lam : ℝ) : ℂ))) * (g κ M v : ℂ)) lam
    beta_reduce at hcv
    rw [hFT (ξ / lam)] at hcv
    rw [fourier_eq_integral]
    have e : ∀ u : ℝ, Complex.exp (-(2 * π * I * u * ξ)) * h u =
        Complex.exp (-(2 * π * I * ((lam * u : ℝ) : ℂ) * ((ξ / lam : ℝ) : ℂ))) *
          (g κ M (lam * u) : ℂ) := by
      intro u
      simp only [hh]
      congr 2
      push_cast
      field_simp
    simp only [e]
    rw [hcv, abs_of_pos (inv_pos.mpr hlam), Complex.real_smul]
    push_cast
    ring
  have hdec : h =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-2 : ℝ)) := by
    refine (isBigO_quad_mul_cexp ((-(M ^ 2 / 4) : ℝ) : ℂ) 0 ((lam ^ 2 : ℝ) : ℂ)
      (hre (κ ^ 2 * lam ^ 2 / 2) (by positivity)) 0 0).congr_left fun y => ?_
    simp only [hh, g]
    push_cast
    ring_nf
  have hFdec : 𝓕 h =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-2 : ℝ)) := by
    rw [show 𝓕 h = fun ξ : ℝ => (1 / lam : ℂ) * (gHat κ M (ξ / lam) : ℂ) from funext hFh]
    refine (isBigO_quad_mul_cexp
      ((Real.sqrt (2 * π) / κ ^ 3 * (1 - κ ^ 2 * M ^ 2 / 4) / lam : ℝ) : ℂ) 0
      ((-(Real.sqrt (2 * π) / κ ^ 3 * (4 * π ^ 2 / (κ ^ 2 * lam ^ 2)) / lam) : ℝ) : ℂ)
      (hre (2 * π ^ 2 / (κ ^ 2 * lam ^ 2)) (by positivity)) 0 0).congr_left fun ξ => ?_
    simp only [gHat]
    push_cast
    field_simp
    ring_nf
  have hHdec : (fun y : ℝ => (g κ M (c + lam * y) : ℂ)) =O[cocompact ℝ]
      (fun y : ℝ => |y| ^ (-2 : ℝ)) := by
    refine (isBigO_quad_mul_cexp ((c ^ 2 - M ^ 2 / 4 : ℝ) : ℂ) ((2 * c * lam : ℝ) : ℂ) ((lam ^ 2 : ℝ) : ℂ)
      (hre (κ ^ 2 * lam ^ 2 / 2) (by positivity)) ((-(κ ^ 2 * c * lam) : ℝ) : ℂ)
      ((-(κ ^ 2 * c ^ 2) / 2 : ℝ) : ℂ)).congr_left fun y => ?_
    simp only [g]
    push_cast
    ring_nf
  have hFsumN : Summable (fun n : ℤ => ‖𝓕 h n‖) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hFdec.norm_left.comp_tendsto Int.tendsto_coe_cofinite)
  have hHsum : Summable (fun t : ℤ => (g κ M (c + lam * t) : ℂ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hHdec.comp_tendsto Int.tendsto_coe_cofinite)
  have hphase : ∀ k : ℤ, ‖Complex.exp (2 * π * I * k * c / lam)‖ = 1 := fun k => by
    rw [show (2 * π * I * k * c / lam : ℂ) = ((2 * π * k * c / lam : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hRsum : Summable (fun k : ℤ => (gHat κ M (k / lam) : ℂ) * Complex.exp (2 * π * I * k * c / lam)) := by
    refine Summable.of_norm ((hFsumN.mul_left lam).congr fun k => ?_)
    rw [norm_mul, hphase, mul_one, hFh, norm_mul]
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
    field_simp
  refine ⟨Complex.summable_ofReal.mp hHsum, hRsum, ?_⟩
  rw [Complex.ofReal_tsum]
  calc ∑' t : ℤ, (g κ M (c + lam * t) : ℂ) = ∑' t : ℤ, h (c / lam + t) := by
        congr 1
        funext t
        simp only [hh]
        congr 2
        field_simp
    _ = ∑' n : ℤ, 𝓕 h n * fourier n ((c / lam : ℝ) : UnitAddCircle) :=
        Real.tsum_eq_tsum_fourier_of_rpow_decay hcont one_lt_two hdec hFdec (c / lam)
    _ = ∑' n : ℤ, (1 / lam : ℂ) * ((gHat κ M (n / lam) : ℂ) * Complex.exp (2 * π * I * n * c / lam)) := by
        congr 1
        funext n
        rw [hFh, fourier_coe_apply]
        push_cast
        ring_nf
    _ = 1 / lam * ∑' k : ℤ, (gHat κ M (k / lam) : ℂ) * Complex.exp (2 * π * I * k * c / lam) :=
        tsum_mul_left

/-- Device: the Gaussian theta sum with period `κ > 0` and shift `v`:
`Σ_n e^{−(v−κn)²} = (√π/κ) Σ_k e^{−π²k²/κ²} e^{2πikv/κ}` (from Mathlib's `Complex.tsum_exp_neg_quadratic`), both series
summable. -/
theorem gauss_poisson {κ : ℝ} (hκ : 0 < κ) (v : ℝ) :
    Summable (fun n : ℤ => Real.exp (-(v - κ * n) ^ 2)) ∧
      Summable (fun k : ℤ => ((Real.exp (-(π ^ 2 * k ^ 2) / κ ^ 2) : ℝ) : ℂ) *
        Complex.exp (2 * π * I * k * v / κ)) ∧
      ((∑' n : ℤ, Real.exp (-(v - κ * n) ^ 2) : ℝ) : ℂ) =
        ((Real.sqrt π / κ : ℝ) : ℂ) * ∑' k : ℤ, ((Real.exp (-(π ^ 2 * k ^ 2) / κ ^ 2) : ℝ) : ℂ) *
          Complex.exp (2 * π * I * k * v / κ) := by
  have hπ : 0 < π := Real.pi_pos
  have hκ0 : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ.ne'
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  -- summability of the left side
  have hL : Summable (fun n : ℤ => Real.exp (-(v - κ * n) ^ 2)) := by
    have := HRTorus.SlotFrame.Analysis.summable_gauss_int (L := κ) hκ v
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) this
    apply Real.exp_le_exp.mpr
    have : (v - κ * n) ^ 2 = (v - n * κ) ^ 2 := by ring
    nlinarith [sq_nonneg (v - n * κ)]
  -- summability of the right side
  have hR : Summable (fun k : ℤ => ((Real.exp (-(π ^ 2 * k ^ 2) / κ ^ 2) : ℝ) : ℂ) *
      Complex.exp (2 * π * I * k * v / κ)) := by
    have hg : Summable (fun k : ℤ => Real.exp (-(π ^ 2 * k ^ 2) / κ ^ 2)) := by
      have := HRTorus.SlotFrame.Analysis.summable_gauss_int (L := π / κ) (by positivity) 0
      refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun k => ?_) this
      apply Real.exp_le_exp.mpr
      have e : (0 - (k : ℝ) * (π / κ)) ^ 2 = π ^ 2 * k ^ 2 / κ ^ 2 := by
        rw [zero_sub, neg_sq, mul_pow, div_pow]; ring
      rw [e]
      have : 0 ≤ π ^ 2 * (k : ℝ) ^ 2 / κ ^ 2 := by positivity
      rw [neg_div]; linarith
    refine Summable.of_norm (hg.congr fun k => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [show (2 * π * I * k * v / κ : ℂ) = ((2 * π * k * v / κ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  refine ⟨hL, hR, ?_⟩
  -- Mathlib's identity with `a = κ²/π` and `b = -κv/π` (the sign makes the phases `e^{+2πikv/κ}` after `k ↦ -k`)
  have ha : 0 < (((κ ^ 2 / π : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; positivity
  have key := Complex.tsum_exp_neg_quadratic ha (((κ * v / π : ℝ) : ℂ))
  have hsq : (((κ ^ 2 / π : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ((κ / Real.sqrt π : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ hπ.le, Real.sqrt_sq hκ.le]
  rw [hsq] at key
  have hl : ∀ n : ℤ, Complex.exp (-π * ((κ ^ 2 / π : ℝ) : ℂ) * n ^ 2 + 2 * π * ((κ * v / π : ℝ) : ℂ) * n) =
      Complex.exp ((v ^ 2 : ℝ) : ℂ) * ((Real.exp (-(v - κ * n) ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have hsq2 : ∀ x y : ℂ, (x + I * y) ^ 2 = x ^ 2 + 2 * x * I * y - y ^ 2 := fun x y => by
    linear_combination y ^ 2 * Complex.I_sq
  have hr : ∀ n : ℤ, Complex.exp (-π / ((κ ^ 2 / π : ℝ) : ℂ) * (n + I * ((κ * v / π : ℝ) : ℂ)) ^ 2) =
      Complex.exp ((v ^ 2 : ℝ) : ℂ) * (((Real.exp (-(π ^ 2 * (-n : ℤ) ^ 2) / κ ^ 2) : ℝ) : ℂ) *
        Complex.exp (2 * π * I * ((-n : ℤ) : ℂ) * v / κ)) := by
    intro n
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, hsq2]
    congr 1
    push_cast
    field_simp
    ring
  simp only [hl, hr] at key
  rw [tsum_mul_left, tsum_mul_left] at key
  have hne : Complex.exp ((v ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have key2 : ∑' n : ℤ, ((Real.exp (-(v - κ * n) ^ 2) : ℝ) : ℂ) =
      1 / ((κ / Real.sqrt π : ℝ) : ℂ) * ∑' n : ℤ, ((Real.exp (-(π ^ 2 * ((-n : ℤ) : ℝ) ^ 2) / κ ^ 2) : ℝ) : ℂ) *
        Complex.exp (2 * π * I * ((-n : ℤ) : ℂ) * v / κ) := by
    apply mul_left_cancel₀ hne
    rw [key]
    ring
  have hneg := (Equiv.neg ℤ).tsum_eq (fun k : ℤ => ((Real.exp (-(π ^ 2 * (k : ℝ) ^ 2) / κ ^ 2) : ℝ) : ℂ) *
    Complex.exp (2 * π * I * k * v / κ))
  simp only [Equiv.neg_apply] at hneg
  rw [Complex.ofReal_tsum, key2, hneg, one_div, ← Complex.ofReal_inv, inv_div]

/-- Device: Poisson summation for `(u² − M²/4) e^{−u²}` with period `κ` (`scaled_poisson_g` at GramPoisson's
`κ = √2`, reindexed by `n ↦ −n`):
`Σ_n ((v−κn)² − M²/4) e^{−(v−κn)²} = κ⁻¹ Σ_k (√π/2)(1 − 2π²k²/κ² − M²/2) e^{−π²k²/κ²} e^{2πikv/κ}`. -/
theorem quad_poisson {κ : ℝ} (hκ : 0 < κ) (M v : ℝ) :
    ((∑' n : ℤ, ((v - κ * n) ^ 2 - M ^ 2 / 4) * Real.exp (-(v - κ * n) ^ 2) : ℝ) : ℂ) =
      1 / (κ : ℂ) * ∑' k : ℤ, ((Real.sqrt π / 2 * (1 - 2 * π ^ 2 * k ^ 2 / κ ^ 2 - M ^ 2 / 2) *
        Real.exp (-(π ^ 2 * k ^ 2) / κ ^ 2) : ℝ) : ℂ) * Complex.exp (2 * π * I * k * v / κ) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, h2]
  obtain ⟨-, -, heq⟩ := scaled_poisson_g hs2 hκ M v
  have hg : ∀ u : ℝ, g (Real.sqrt 2) M u = (u ^ 2 - M ^ 2 / 4) * Real.exp (-u ^ 2) := by
    intro u
    simp only [g]
    rw [h2]
    congr 2
    ring
  have hgh : ∀ k : ℤ, gHat (Real.sqrt 2) M (k / κ) = Real.sqrt π / 2 *
      (1 - 2 * π ^ 2 * k ^ 2 / κ ^ 2 - M ^ 2 / 2) * Real.exp (-(π ^ 2 * k ^ 2) / κ ^ 2) := by
    intro k
    simp only [gHat]
    have hc : Real.sqrt (2 * π) / Real.sqrt 2 ^ 3 = Real.sqrt π / 2 := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), h3, div_eq_div_iff (by positivity) (by norm_num)]
      ring
    have hm : 1 - 4 * π ^ 2 * ((k : ℝ) / κ) ^ 2 / Real.sqrt 2 ^ 2 - Real.sqrt 2 ^ 2 * M ^ 2 / 4 =
        1 - 2 * π ^ 2 * k ^ 2 / κ ^ 2 - M ^ 2 / 2 := by
      rw [h2]; ring
    have he : -(2 * π ^ 2 * ((k : ℝ) / κ) ^ 2) / Real.sqrt 2 ^ 2 = -(π ^ 2 * k ^ 2) / κ ^ 2 := by
      rw [h2]; ring
    rw [hc, hm, he]
  have hre : ∑' n : ℤ, ((v - κ * n) ^ 2 - M ^ 2 / 4) * Real.exp (-(v - κ * n) ^ 2) =
      ∑' t : ℤ, g (Real.sqrt 2) M (v + κ * t) := by
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun t => ?_
    simp only [Equiv.neg_apply]
    have e : v - κ * ((-t : ℤ) : ℝ) = v + κ * t := by push_cast; ring
    rw [e, hg]
  rw [hre, heq]
  congr 1
  refine tsum_congr fun k => ?_
  rw [hgh]

/-! ### Proof devices for Lemma 2.3(iii): the lattice sums of the HR paper (not statements of the paper) -/

open HRTorus.SlotFrame

/-- Device: `(j, m) ↦ j̃ + mN` is a bijection `ℤ_N × ℤ ≃ ℤ` (`j̃ = j.val`). -/
def zmodIntEquiv (N : ℕ) [NeZero N] : ZMod N × ℤ ≃ ℤ where
  toFun q := (q.1.val : ℤ) + q.2 * N
  invFun n := ((n : ZMod N), n / N)
  left_inv q := by
    obtain ⟨j, m⟩ := q
    have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hj0 : (0 : ℤ) ≤ j.val := by positivity
    have hjN : (j.val : ℤ) < N := by exact_mod_cast ZMod.val_lt j
    refine Prod.ext ?_ ?_
    · show ((((j.val : ℤ) + m * N : ℤ)) : ZMod N) = j
      simp
    · show ((j.val : ℤ) + m * N) / N = m
      rw [Int.add_mul_ediv_right _ _ hN, Int.ediv_eq_zero_of_lt hj0 hjN, zero_add]
  right_inv n := by
    show (((n : ZMod N)).val : ℤ) + n / N * N = n
    rw [ZMod.val_intCast]
    exact Int.emod_add_ediv_mul n N

/-- Device: `Σ_{j ∈ ℤ_N} Σ_m F(j̃ + mN) = Σ_n F(n)` for a summable `F : ℤ → ℂ`. -/
theorem sum_zmod_tsum {N : ℕ} [NeZero N] (F : ℤ → ℂ) (hF : Summable F) :
    ∑ j : ZMod N, ∑' m : ℤ, F ((j.val : ℤ) + m * N) = ∑' n : ℤ, F n := by
  have hFe : Summable (fun q => F (zmodIntEquiv N q)) := (zmodIntEquiv N).summable_iff.mpr hF
  rw [← (zmodIntEquiv N).tsum_eq F, hFe.tsum_prod, tsum_fintype]
  rfl

/-- Device: `Σ_j conj(Σ_m Φ(j̃+mN)) (Σ_m Φ(j̃+mN)) = Σ_{(n,p) ∈ ℤ²} conj(Φ n) Φ(n + pN)` when the right side is
summable (the relabelling `n = j̃ + mN`, `p = m' − m` of the proof of Lemma 2.3(iii)). -/
theorem sum_star_tsum_mul_tsum {N : ℕ} [NeZero N] (Φ : ℤ → ℂ)
    (hS : Summable (fun np : ℤ × ℤ => star (Φ np.1) * Φ (np.1 + np.2 * N))) :
    ∑ j : ZMod N, star (∑' m : ℤ, Φ ((j.val : ℤ) + m * N)) * ∑' m : ℤ, Φ ((j.val : ℤ) + m * N) =
      ∑' np : ℤ × ℤ, star (Φ np.1) * Φ (np.1 + np.2 * N) := by
  have hrow : ∀ a m : ℤ, ∑' m' : ℤ, Φ (a + m' * N) = ∑' p : ℤ, Φ (a + m * N + p * N) := by
    intro a m
    rw [← (Equiv.addLeft m).tsum_eq (fun m' => Φ (a + m' * N))]
    refine tsum_congr fun p => ?_
    simp only [Equiv.coe_addLeft]
    congr 1
    ring
  have hj : ∀ j : ZMod N, star (∑' m : ℤ, Φ ((j.val : ℤ) + m * N)) * ∑' m : ℤ, Φ ((j.val : ℤ) + m * N) =
      ∑' m : ℤ, ∑' p : ℤ, star (Φ ((j.val : ℤ) + m * N)) * Φ ((j.val : ℤ) + m * N + p * N) := by
    intro j
    rw [tsum_star, ← tsum_mul_right]
    refine tsum_congr fun m => ?_
    rw [hrow _ m, tsum_mul_left]
  simp only [hj]
  exact (sum_zmod_tsum (fun n => ∑' p : ℤ, star (Φ n) * Φ (n + p * N)) hS.prod).trans hS.tsum_prod.symm

/-- Device: `c₀² = (L_y√π)⁻¹` for the normalisation `c₀ = (L_y√π)^{−1/2}` of the orbitals. -/
theorem c0_sq_eq (T : Torus) : ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (T.Ly * Real.sqrt π) := by
  have hpos : 0 < T.Ly * Real.sqrt π := mul_pos T.Ly_pos (Real.sqrt_pos.mpr Real.pi_pos)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num,
    Real.rpow_neg_one, one_div]

/-- Device: the orbital as a real amplitude times a phase. -/
theorem phi_eq (T : Torus) (n : ℤ) (R : ℝ × ℝ) :
    phi T n R = (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-((R.1 - T.κ * n) ^ 2) / 2) : ℝ) : ℂ) *
      Complex.exp (((T.κ * n * R.2 : ℝ) : ℂ) * I) := by
  unfold phi
  rw [show I * (T.κ : ℂ) * (n : ℂ) * (R.2 : ℂ) = ((T.κ * n * R.2 : ℝ) : ℂ) * I by push_cast; ring]
  push_cast
  ring

/-- Device: the conjugate orbital. -/
theorem star_phi_eq (T : Torus) (n : ℤ) (R : ℝ × ℝ) :
    star (phi T n R) = (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-((R.1 - T.κ * n) ^ 2) / 2) : ℝ) : ℂ) *
      Complex.exp (((-(T.κ * n * R.2) : ℝ) : ℂ) * I) := by
  rw [phi_eq, star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 2
  push_cast
  ring

/-- Device: `conj(φ_n) φ_{n+pN_φ} = c₀² e^{−p²L_x²/4} e^{−(R_x − pL_x/2 − κn)²} e^{ipL_xR_y}` ("`Using
$\kappa\Nphi=L_x$ and $\tfrac12(u^2+(u-pL_x)^2)=(u-pL_x/2)^2+p^2L_x^2/4$`"). -/
theorem star_phi_mul_phi_shift (T : Torus) (n p : ℤ) (R : ℝ × ℝ) :
    star (phi T n R) * phi T (n + p * (T.Nφ : ℤ)) R =
      ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 / 4)) *
        Real.exp (-((R.1 - p * T.Lx / 2) - T.κ * n) ^ 2) : ℝ) : ℂ) *
      Complex.exp (((p * T.Lx * R.2 : ℝ) : ℂ) * I) := by
  rw [star_phi_eq, phi_eq]
  have hLx := T.Lx_eq
  have hexp : Complex.exp (((-(T.κ * n * R.2) : ℝ) : ℂ) * I) *
      Complex.exp (((T.κ * ((n + p * (T.Nφ : ℤ) : ℤ) : ℝ) * R.2 : ℝ) : ℂ) * I) =
      Complex.exp (((p * T.Lx * R.2 : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hLx]
    push_cast
    ring
  have hreal : Real.exp (-((R.1 - T.κ * n) ^ 2) / 2) *
      Real.exp (-((R.1 - T.κ * ((n + p * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2) / 2) =
      Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 / 4)) * Real.exp (-((R.1 - p * T.Lx / 2) - T.κ * n) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hLx]
    push_cast
    ring
  calc _ = ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * (Real.exp (-((R.1 - T.κ * n) ^ 2) / 2) *
          Real.exp (-((R.1 - T.κ * ((n + p * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2) / 2)) : ℝ) : ℂ) *
        (Complex.exp (((-(T.κ * n * R.2) : ℝ) : ℂ) * I) *
          Complex.exp (((T.κ * ((n + p * (T.Nφ : ℤ) : ℤ) : ℝ) * R.2 : ℝ) : ℂ) * I)) := by
        push_cast
        ring
    _ = _ := by
        rw [hreal, hexp]
        push_cast
        ring

/-- Device: the weighted orbital `(Dφ_n)(R) = −(R_x − κn) φ_n(R)` (Lemma 2.2(iii)), the summand of `Dψ_j`. -/
def Dphi (T : Torus) (n : ℤ) (R : ℝ × ℝ) : ℂ :=
  ((-(R.1 - T.κ * n) : ℝ) : ℂ) * phi T n R

/-- Device: `(Dψ_j)(R) = Σ_m (Dφ_{j̃+mN_φ})(R)` (SlotFrame's `Dcov_psi` at the representative `j̃ = j.val`). -/
theorem Dcov_psi_val (T : Torus) [NeZero T.Nφ] (j : ZMod T.Nφ) (R : ℝ × ℝ) :
    Dcov (psi T j) R = ∑' m : ℤ, Dphi T ((j.val : ℤ) + m * (T.Nφ : ℤ)) R := by
  have h := Dcov_psi T (j.val : ℤ) R
  rw [Int.cast_natCast, ZMod.natCast_zmod_val] at h
  exact h

/-- Device: `conj(Dφ_n) Dφ_{n+pN_φ}`, with `(x−κn)(x−κn−pL_x) = v² − p²L_x²/4`, `v = x − pL_x/2 − κn`. -/
theorem star_Dphi_mul_Dphi_shift (T : Torus) (n p : ℤ) (R : ℝ × ℝ) :
    star (Dphi T n R) * Dphi T (n + p * (T.Nφ : ℤ)) R =
      ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 / 4)) *
        ((((R.1 - p * T.Lx / 2) - T.κ * n) ^ 2 - (p * T.Lx) ^ 2 / 4) *
          Real.exp (-((R.1 - p * T.Lx / 2) - T.κ * n) ^ 2)) : ℝ) : ℂ) *
      Complex.exp (((p * T.Lx * R.2 : ℝ) : ℂ) * I) := by
  have hs : ∀ r : ℝ, star (r : ℂ) = r := fun r => Complex.conj_ofReal r
  have h := star_phi_mul_phi_shift T n p R
  have hLx := T.Lx_eq
  calc star (Dphi T n R) * Dphi T (n + p * (T.Nφ : ℤ)) R
      = ((-(R.1 - T.κ * n) : ℝ) : ℂ) * ((-(R.1 - T.κ * ((n + p * (T.Nφ : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) *
          (star (phi T n R) * phi T (n + p * (T.Nφ : ℤ)) R) := by
        simp only [Dphi, star_mul', hs]
        ring
    _ = _ := by
        rw [h, hLx]
        push_cast
        ring

/-- Device: the summand of Lemma 2.3(iii)'s first series, `(2π)⁻¹ e^{−q²/4} e^{i(kL_yR_x + pL_xR_y)}`. -/
def Gev (T : Torus) (R : ℝ × ℝ) (pk : ℤ × ℤ) : ℂ :=
  ((1 / (2 * π) * Real.exp (-((pk.1 : ℝ) ^ 2 * T.Lx ^ 2 + (pk.2 : ℝ) ^ 2 * T.Ly ^ 2) / 4) : ℝ) : ℂ) *
    Complex.exp (((pk.2 * T.Ly * R.1 + pk.1 * T.Lx * R.2 : ℝ) : ℂ) * I)

/-- Device: the summand of the second series, `(4π)⁻¹ (1 − q²/2) e^{−q²/4} e^{i(kL_yR_x + pL_xR_y)}`. -/
def GevD (T : Torus) (R : ℝ × ℝ) (pk : ℤ × ℤ) : ℂ :=
  ((1 / (4 * π) * (1 - ((pk.1 : ℝ) ^ 2 * T.Lx ^ 2 + (pk.2 : ℝ) ^ 2 * T.Ly ^ 2) / 2) *
      Real.exp (-((pk.1 : ℝ) ^ 2 * T.Lx ^ 2 + (pk.2 : ℝ) ^ 2 * T.Ly ^ 2) / 4) : ℝ) : ℂ) *
    Complex.exp (((pk.2 * T.Ly * R.1 + pk.1 * T.Lx * R.2 : ℝ) : ℂ) * I)

/-- Device: the real factor, `c₀² e^{−p²L_x²/4} (√π/κ) e^{−π²k²/κ²} = (2π)⁻¹ e^{−q²/4}`. -/
theorem real_factor (T : Torus) (p k : ℤ) :
    ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 / 4)) *
      (Real.sqrt π / T.κ) * Real.exp (-(π ^ 2 * (k : ℝ) ^ 2) / T.κ ^ 2) =
      1 / (2 * π) * Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 + (k : ℝ) ^ 2 * T.Ly ^ 2) / 4) := by
  rw [c0_sq_eq T]
  have hLy0 : T.Ly ≠ 0 := T.Ly_pos.ne'
  have hs0 : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hπ0 : π ≠ 0 := Real.pi_ne_zero
  have he : Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 / 4)) * Real.exp (-(π ^ 2 * (k : ℝ) ^ 2) / T.κ ^ 2) =
      Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 + (k : ℝ) ^ 2 * T.Ly ^ 2) / 4) := by
    rw [← Real.exp_add]
    congr 1
    unfold Torus.κ
    field_simp
    ring
  calc 1 / (T.Ly * Real.sqrt π) * Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 / 4)) * (Real.sqrt π / T.κ) *
        Real.exp (-(π ^ 2 * (k : ℝ) ^ 2) / T.κ ^ 2)
      = (1 / (T.Ly * Real.sqrt π) * (Real.sqrt π / T.κ)) * (Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 / 4)) *
        Real.exp (-(π ^ 2 * (k : ℝ) ^ 2) / T.κ ^ 2)) := by ring
    _ = 1 / (2 * π) * Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 + (k : ℝ) ^ 2 * T.Ly ^ 2) / 4) := by
      rw [he]
      congr 1
      unfold Torus.κ
      field_simp

/-- Device: the phase factor; `e^{−iπkpN_φ} = 1` because `N_φ` is even ("`$e^{-\iu kL_y\cdot pL_x/2}=e^{-\iu\pi
kp\Nphi}=1$ because $\Nphi$ is even`"). -/
theorem phase_factor (T : Torus) (p k : ℤ) (R : ℝ × ℝ) :
    Complex.exp (((p * T.Lx * R.2 : ℝ) : ℂ) * I) *
      Complex.exp (2 * π * I * k * ((R.1 - p * T.Lx / 2 : ℝ) : ℂ) / T.κ) =
      Complex.exp (((k * T.Ly * R.1 + p * T.Lx * R.2 : ℝ) : ℂ) * I) := by
  have hκ0 : (T.κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr T.κ_pos.ne'
  have hκLy : (T.κ : ℂ) * T.Ly = 2 * π := by exact_mod_cast T.κ_mul_Ly
  have hA : (T.Lx : ℂ) * T.Ly = 2 * π * (2 * (T.N : ℂ)) := by
    have h := T.area
    push_cast at h
    exact_mod_cast h
  rw [← Complex.exp_add]
  have h1 : 2 * π * I * k * ((R.1 - p * T.Lx / 2 : ℝ) : ℂ) / T.κ =
      I * k * T.Ly * ((R.1 - p * T.Lx / 2 : ℝ) : ℂ) := by
    rw [div_eq_iff hκ0, ← hκLy]
    ring
  rw [h1]
  have h2 : ((p * T.Lx * R.2 : ℝ) : ℂ) * I + I * k * T.Ly * ((R.1 - p * T.Lx / 2 : ℝ) : ℂ) =
      (((-(k * p * (T.N : ℤ))) : ℤ) : ℂ) * (2 * π * I) + ((k * T.Ly * R.1 + p * T.Lx * R.2 : ℝ) : ℂ) * I := by
    push_cast
    linear_combination (-(I * k * p / 2)) * hA
  rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- Device: for fixed `p`, the sum over `n` by Poisson summation (the proof of Lemma 2.3(iii)). -/
theorem tsum_n_ev (T : Torus) (p : ℤ) (R : ℝ × ℝ) :
    ∑' n : ℤ, star (phi T n R) * phi T (n + p * (T.Nφ : ℤ)) R = ∑' k : ℤ, Gev T R (p, k) := by
  have h1 : ∀ n : ℤ, star (phi T n R) * phi T (n + p * (T.Nφ : ℤ)) R =
      ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 / 4)) : ℝ) : ℂ) *
        Complex.exp (((p * T.Lx * R.2 : ℝ) : ℂ) * I) *
        ((Real.exp (-((R.1 - p * T.Lx / 2) - T.κ * n) ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [star_phi_mul_phi_shift]
    push_cast
    ring
  simp_rw [h1]
  rw [tsum_mul_left, ← Complex.ofReal_tsum, (gauss_poisson T.κ_pos (R.1 - p * T.Lx / 2)).2.2,
    ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [Gev]
  rw [← real_factor T p k, ← phase_factor T p k R]
  push_cast
  ring

/-- Device: the same for `Dφ`, with `quad_poisson` at `M = pL_x`. -/
theorem tsum_n_evD (T : Torus) (p : ℤ) (R : ℝ × ℝ) :
    ∑' n : ℤ, star (Dphi T n R) * Dphi T (n + p * (T.Nφ : ℤ)) R = ∑' k : ℤ, GevD T R (p, k) := by
  have h1 : ∀ n : ℤ, star (Dphi T n R) * Dphi T (n + p * (T.Nφ : ℤ)) R =
      ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 / 4)) : ℝ) : ℂ) *
        Complex.exp (((p * T.Lx * R.2 : ℝ) : ℂ) * I) *
        (((((R.1 - p * T.Lx / 2) - T.κ * n) ^ 2 - (p * T.Lx) ^ 2 / 4) *
          Real.exp (-((R.1 - p * T.Lx / 2) - T.κ * n) ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [star_Dphi_mul_Dphi_shift]
    push_cast
    ring
  simp_rw [h1]
  rw [tsum_mul_left, ← Complex.ofReal_tsum, quad_poisson T.κ_pos (p * T.Lx) (R.1 - p * T.Lx / 2),
    ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [GevD]
  have hB : 1 - 2 * π ^ 2 * (k : ℝ) ^ 2 / T.κ ^ 2 - (p * T.Lx) ^ 2 / 2 =
      1 - ((p : ℝ) ^ 2 * T.Lx ^ 2 + (k : ℝ) ^ 2 * T.Ly ^ 2) / 2 := by
    have hLy0 : T.Ly ≠ 0 := T.Ly_pos.ne'
    have hπ0 : π ≠ 0 := Real.pi_ne_zero
    unfold Torus.κ
    field_simp
    ring
  have hr := real_factor T p k
  rw [← hB, ← phase_factor T p k R]
  rw [show 1 / (4 * π) * (1 - 2 * π ^ 2 * (k : ℝ) ^ 2 / T.κ ^ 2 - (p * T.Lx) ^ 2 / 2) *
      Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 + (k : ℝ) ^ 2 * T.Ly ^ 2) / 4) =
      1 / 2 * (1 / (2 * π) * Real.exp (-((p : ℝ) ^ 2 * T.Lx ^ 2 + (k : ℝ) ^ 2 * T.Ly ^ 2) / 4)) *
        (1 - 2 * π ^ 2 * (k : ℝ) ^ 2 / T.κ ^ 2 - (p * T.Lx) ^ 2 / 2) by ring, ← hr]
  push_cast
  ring

/-- Device: a weighted Gaussian product bound, `αβ e^{−a²/2} e^{−b²/2} ≤ e^{−a²/8} e^{−(a−b)²/32}` when
`0 ≤ α ≤ e^{a²/4}` and `0 ≤ β ≤ e^{b²/4}`. -/
theorem weight_gauss_le {a b α β : ℝ} (_hα0 : 0 ≤ α) (hα : α ≤ Real.exp (a ^ 2 / 4)) (hβ0 : 0 ≤ β)
    (hβ : β ≤ Real.exp (b ^ 2 / 4)) :
    α * Real.exp (-(a ^ 2) / 2) * (β * Real.exp (-(b ^ 2) / 2)) ≤
      Real.exp (-(a ^ 2) / 8) * Real.exp (-((a - b) ^ 2) / 32) := by
  calc α * Real.exp (-(a ^ 2) / 2) * (β * Real.exp (-(b ^ 2) / 2))
      ≤ Real.exp (a ^ 2 / 4) * Real.exp (-(a ^ 2) / 2) * (Real.exp (b ^ 2 / 4) * Real.exp (-(b ^ 2) / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hα (Real.exp_pos _).le)
          (mul_le_mul_of_nonneg_right hβ (Real.exp_pos _).le) (mul_nonneg hβ0 (Real.exp_pos _).le)
          (by positivity)
    _ = Real.exp (-(a ^ 2 / 4) - b ^ 2 / 4) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-(a ^ 2) / 8) * Real.exp (-((a - b) ^ 2) / 32) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg (3 * a + b), sq_nonneg b]

/-- Device: `|a| ≤ e^{a²/4}`. -/
theorem abs_le_exp_sq_div_four (a : ℝ) : |a| ≤ Real.exp (a ^ 2 / 4) := by
  have h1 := Real.add_one_le_exp (a ^ 2 / 4)
  have h2 : |a| ≤ a ^ 2 / 4 + 1 := by
    nlinarith [sq_abs a, sq_nonneg (|a| / 2 - 1), abs_nonneg a]
  linarith

/-- Device: the summable majorant of the `(n, p)` series. -/
theorem summable_majorant (T : Torus) (R : ℝ × ℝ) :
    Summable (fun np : ℤ × ℤ => ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 *
      (Real.exp (-((R.1 / 2 - np.1 * (T.κ / 2)) ^ 2) / 2) * Real.exp (-((0 - np.2 * (T.Lx / 4)) ^ 2) / 2))) := by
  have hA := Analysis.summable_gauss_int (L := T.κ / 2) (by linarith [T.κ_pos]) (R.1 / 2)
  have hB := Analysis.summable_gauss_int (L := T.Lx / 4) (by linarith [T.Lx_pos]) 0
  have hA' : Summable (fun n : ℤ => ‖Real.exp (-((R.1 / 2 - n * (T.κ / 2)) ^ 2) / 2)‖) :=
    hA.congr fun n => (Real.norm_of_nonneg (Real.exp_pos _).le).symm
  have hB' : Summable (fun p : ℤ => ‖Real.exp (-((0 - p * (T.Lx / 4)) ^ 2) / 2)‖) :=
    hB.congr fun p => (Real.norm_of_nonneg (Real.exp_pos _).le).symm
  exact (summable_mul_of_summable_norm hA' hB').mul_left _

/-- Device: the termwise bound by the majorant, with weights `α, β`. -/
theorem norm_term_le (T : Torus) (n p : ℤ) (R : ℝ × ℝ) {α β : ℝ} (hα0 : 0 ≤ α)
    (hα : α ≤ Real.exp ((R.1 - T.κ * n) ^ 2 / 4)) (hβ0 : 0 ≤ β)
    (hβ : β ≤ Real.exp ((R.1 - T.κ * ((n + p * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 4)) :
    α * ‖phi T n R‖ * (β * ‖phi T (n + p * (T.Nφ : ℤ)) R‖) ≤
      ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 *
        (Real.exp (-((R.1 / 2 - n * (T.κ / 2)) ^ 2) / 2) * Real.exp (-((0 - p * (T.Lx / 4)) ^ 2) / 2)) := by
  rw [norm_phi, norm_phi]
  have hLx := T.Lx_eq
  have key := weight_gauss_le hα0 hα hβ0 hβ
  have hA : Real.exp (-((R.1 / 2 - n * (T.κ / 2)) ^ 2) / 2) = Real.exp (-((R.1 - T.κ * n) ^ 2) / 8) := by
    congr 1
    ring
  have hB : Real.exp (-((0 - p * (T.Lx / 4)) ^ 2) / 2) =
      Real.exp (-((R.1 - T.κ * n - (R.1 - T.κ * ((n + p * (T.Nφ : ℤ) : ℤ) : ℝ))) ^ 2) / 32) := by
    congr 1
    rw [hLx]
    push_cast
    ring
  rw [hA, hB]
  calc α * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-((R.1 - T.κ * n) ^ 2) / 2)) *
        (β * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-((R.1 - T.κ * ((n + p * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2) / 2)))
      = ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * (α * Real.exp (-((R.1 - T.κ * n) ^ 2) / 2) *
        (β * Real.exp (-((R.1 - T.κ * ((n + p * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2) / 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)

/-- Device: the `(n, p)` series of `‖e_R‖²` converges absolutely. -/
theorem summable_ev_terms (T : Torus) (R : ℝ × ℝ) :
    Summable (fun np : ℤ × ℤ => star (phi T np.1 R) * phi T (np.1 + np.2 * (T.Nφ : ℤ)) R) := by
  refine Summable.of_norm_bounded (summable_majorant T R) fun np => ?_
  have h := norm_term_le T np.1 np.2 R zero_le_one (Real.one_le_exp (by positivity)) zero_le_one
    (Real.one_le_exp (by positivity))
  rw [norm_mul, norm_star]
  calc ‖phi T np.1 R‖ * ‖phi T (np.1 + np.2 * (T.Nφ : ℤ)) R‖
      = 1 * ‖phi T np.1 R‖ * (1 * ‖phi T (np.1 + np.2 * (T.Nφ : ℤ)) R‖) := by ring
    _ ≤ _ := h

/-- Device: the `(n, p)` series of `‖e^D_R‖²` converges absolutely. -/
theorem summable_evD_terms (T : Torus) (R : ℝ × ℝ) :
    Summable (fun np : ℤ × ℤ => star (Dphi T np.1 R) * Dphi T (np.1 + np.2 * (T.Nφ : ℤ)) R) := by
  refine Summable.of_norm_bounded (summable_majorant T R) fun np => ?_
  have h := norm_term_le T np.1 np.2 R (abs_nonneg _) (abs_le_exp_sq_div_four _) (abs_nonneg _)
    (abs_le_exp_sq_div_four _)
  simp only [Dphi, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  exact h

/-- Device: the summable majorant of the `(p, k)` series. -/
theorem summable_Gmajorant (T : Torus) :
    Summable (fun pk : ℤ × ℤ => 4 * (Real.exp (-((0 - pk.1 * (T.Lx / 2)) ^ 2) / 2) *
      Real.exp (-((0 - pk.2 * (T.Ly / 2)) ^ 2) / 2))) := by
  have hA := Analysis.summable_gauss_int (L := T.Lx / 2) (by linarith [T.Lx_pos]) 0
  have hB := Analysis.summable_gauss_int (L := T.Ly / 2) (by linarith [T.Ly_pos]) 0
  have hA' : Summable (fun p : ℤ => ‖Real.exp (-((0 - p * (T.Lx / 2)) ^ 2) / 2)‖) :=
    hA.congr fun p => (Real.norm_of_nonneg (Real.exp_pos _).le).symm
  have hB' : Summable (fun k : ℤ => ‖Real.exp (-((0 - k * (T.Ly / 2)) ^ 2) / 2)‖) :=
    hB.congr fun k => (Real.norm_of_nonneg (Real.exp_pos _).le).symm
  exact (summable_mul_of_summable_norm hA' hB').mul_left _

/-- Device: `e^{−q²/4} ≤ e^{−p²L_x²/8} e^{−k²L_y²/8}` in the majorant's form. -/
theorem exp_q_le (T : Torus) (pk : ℤ × ℤ) :
    Real.exp (-((pk.1 : ℝ) ^ 2 * T.Lx ^ 2 + (pk.2 : ℝ) ^ 2 * T.Ly ^ 2) / 8) =
      Real.exp (-((0 - pk.1 * (T.Lx / 2)) ^ 2) / 2) * Real.exp (-((0 - pk.2 * (T.Ly / 2)) ^ 2) / 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem summable_Gev (T : Torus) (R : ℝ × ℝ) : Summable (Gev T R) := by
  refine Summable.of_norm_bounded (summable_Gmajorant T) fun pk => ?_
  simp only [Gev, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hq : 0 ≤ (pk.1 : ℝ) ^ 2 * T.Lx ^ 2 + (pk.2 : ℝ) ^ 2 * T.Ly ^ 2 := by positivity
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * π)), abs_of_pos (Real.exp_pos _), ← exp_q_le]
  have h1 : 1 / (2 * π) ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.two_le_pi]
  have h2 : Real.exp (-((pk.1 : ℝ) ^ 2 * T.Lx ^ 2 + (pk.2 : ℝ) ^ 2 * T.Ly ^ 2) / 4) ≤
      Real.exp (-((pk.1 : ℝ) ^ 2 * T.Lx ^ 2 + (pk.2 : ℝ) ^ 2 * T.Ly ^ 2) / 8) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)

theorem summable_GevD (T : Torus) (R : ℝ × ℝ) : Summable (GevD T R) := by
  refine Summable.of_norm_bounded (summable_Gmajorant T) fun pk => ?_
  simp only [GevD, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [← exp_q_le]
  have hq : 0 ≤ (pk.1 : ℝ) ^ 2 * T.Lx ^ 2 + (pk.2 : ℝ) ^ 2 * T.Ly ^ 2 := by positivity
  generalize (pk.1 : ℝ) ^ 2 * T.Lx ^ 2 + (pk.2 : ℝ) ^ 2 * T.Ly ^ 2 = q at hq ⊢
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (4 * π)), abs_of_pos (Real.exp_pos _)]
  have h1 : |1 - q / 2| ≤ 4 * Real.exp (q / 8) := by
    have := Real.add_one_le_exp (q / 8)
    rw [abs_le]
    constructor <;> nlinarith
  have h2 : Real.exp (q / 8) * Real.exp (-q / 4) = Real.exp (-q / 8) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : 1 / (4 * π) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.two_le_pi]
  calc 1 / (4 * π) * |1 - q / 2| * Real.exp (-q / 4) ≤ 1 * (4 * Real.exp (q / 8)) * Real.exp (-q / 4) := by
        gcongr
    _ = 4 * Real.exp (-q / 8) := by rw [← h2]; ring

/-- Device: the series of Lemma 2.3(iii) for `‖e_R‖² = Σ_j |ψ_j(R)|²`, complex form. -/
theorem hasSum_Gev (T : Torus) [NeZero T.Nφ] (R : ℝ × ℝ) :
    HasSum (Gev T R) (∑ j : ZMod T.Nφ, star (psi T j R) * psi T j R) := by
  have hS := summable_ev_terms T R
  have hS' : Summable (Function.uncurry fun n p : ℤ => star (phi T n R) * phi T (n + p * (T.Nφ : ℤ)) R) := hS
  have e1 : ∑ j : ZMod T.Nφ, star (psi T j R) * psi T j R =
      ∑' np : ℤ × ℤ, star (phi T np.1 R) * phi T (np.1 + np.2 * (T.Nφ : ℤ)) R :=
    sum_star_tsum_mul_tsum (fun n => phi T n R) hS
  have e2 : ∑' np : ℤ × ℤ, star (phi T np.1 R) * phi T (np.1 + np.2 * (T.Nφ : ℤ)) R =
      ∑' p : ℤ, ∑' n : ℤ, star (phi T n R) * phi T (n + p * (T.Nφ : ℤ)) R := by
    rw [hS'.tsum_comm]
    exact hS.tsum_prod
  have e3 : ∑' p : ℤ, ∑' n : ℤ, star (phi T n R) * phi T (n + p * (T.Nφ : ℤ)) R =
      ∑' p : ℤ, ∑' k : ℤ, Gev T R (p, k) := tsum_congr fun p => tsum_n_ev T p R
  rw [e1, e2, e3, ← (summable_Gev T R).tsum_prod]
  exact (summable_Gev T R).hasSum

/-- Device: the series of Lemma 2.3(iii) for `‖e^D_R‖² = Σ_j |(Dψ_j)(R)|²`, complex form. -/
theorem hasSum_GevD (T : Torus) [NeZero T.Nφ] (R : ℝ × ℝ) :
    HasSum (GevD T R) (∑ j : ZMod T.Nφ, star (Dcov (psi T j) R) * Dcov (psi T j) R) := by
  have hS := summable_evD_terms T R
  have hS' : Summable (Function.uncurry fun n p : ℤ => star (Dphi T n R) * Dphi T (n + p * (T.Nφ : ℤ)) R) := hS
  have e1 : ∑ j : ZMod T.Nφ, star (Dcov (psi T j) R) * Dcov (psi T j) R =
      ∑' np : ℤ × ℤ, star (Dphi T np.1 R) * Dphi T (np.1 + np.2 * (T.Nφ : ℤ)) R := by
    simp only [Dcov_psi_val]
    exact sum_star_tsum_mul_tsum (fun n => Dphi T n R) hS
  have e2 : ∑' np : ℤ × ℤ, star (Dphi T np.1 R) * Dphi T (np.1 + np.2 * (T.Nφ : ℤ)) R =
      ∑' p : ℤ, ∑' n : ℤ, star (Dphi T n R) * Dphi T (n + p * (T.Nφ : ℤ)) R := by
    rw [hS'.tsum_comm]
    exact hS.tsum_prod
  have e3 : ∑' p : ℤ, ∑' n : ℤ, star (Dphi T n R) * Dphi T (n + p * (T.Nφ : ℤ)) R =
      ∑' p : ℤ, ∑' k : ℤ, GevD T R (p, k) := tsum_congr fun p => tsum_n_evD T p R
  rw [e1, e2, e3, ← (summable_GevD T R).tsum_prod]
  exact (summable_GevD T R).hasSum

/-! ### Proof devices for Lemma 2.3(iv): geometric majorants of the lattice sums (not statements of the paper) -/

/-- Device: `e^{−4} < 0.01832` (from Mathlib's `e > 2.7182818283`). -/
theorem exp_neg_four_lt : Real.exp (-4) < 0.01832 := by
  have h1 := Real.exp_one_gt_d9
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  have h5 : (2.7182818283 : ℝ) ^ 4 < Real.exp 1 ^ 4 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h6 : (54.59 : ℝ) < Real.exp 4 := by
    rw [h4]
    have : (54.59 : ℝ) < 2.7182818283 ^ 4 := by norm_num
    linarith
  have h7 : Real.exp (-4) * Real.exp 4 = 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (-4)]

/-- Device: the geometric majorant of `e^{−p²a}` over `ℤ`: `1` at `0`, `ε (ε³)^{|p|−1}` elsewhere. -/
def thetaMaj (ε : ℝ) (p : ℤ) : ℝ := if p = 0 then 1 else ε * (ε ^ 3) ^ (p.natAbs - 1)

/-- Device: the geometric majorant of `p² e^{−p²a}` over `ℤ`: `0` at `0`, `ε (4ε³)^{|p|−1}` elsewhere. -/
def chiMaj (ε : ℝ) (p : ℤ) : ℝ := if p = 0 then 0 else ε * (4 * ε ^ 3) ^ (p.natAbs - 1)

theorem natAbs_succ_aux (n : ℕ) : ((n : ℤ) + 1).natAbs = n + 1 ∧ (-((n : ℤ) + 1)).natAbs = n + 1 := by
  constructor <;> omega

/-- Device: a two-sided geometric series over `ℤ`. -/
theorem hasSum_geomMaj {ε r c : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (f : ℤ → ℝ) (hf0 : f 0 = c)
    (hf : ∀ p : ℤ, p ≠ 0 → f p = ε * r ^ (p.natAbs - 1)) :
    HasSum f (c + 2 * ε / (1 - r)) := by
  have hg : HasSum (fun n : ℕ => ε * r ^ n) (ε * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left ε
  have e1 : (fun n : ℕ => f ((n : ℤ) + 1)) = fun n : ℕ => ε * r ^ n := by
    funext n
    rw [hf _ (by omega), (natAbs_succ_aux n).1, Nat.add_sub_cancel]
  have e2 : (fun n : ℕ => f (-((n : ℤ) + 1))) = fun n : ℕ => ε * r ^ n := by
    funext n
    rw [hf _ (by omega), (natAbs_succ_aux n).2, Nat.add_sub_cancel]
  have h1 : HasSum (fun n : ℕ => f ((n : ℤ) + 1)) (ε * (1 - r)⁻¹) := by rw [e1]; exact hg
  have h2 : HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) (ε * (1 - r)⁻¹) := by rw [e2]; exact hg
  have h := HasSum.of_add_one_of_neg_add_one h1 h2
  convert h using 1
  rw [hf0]
  have : (1 - r) ≠ 0 := (sub_pos.mpr hr1).ne'
  field_simp
  ring

theorem hasSum_thetaMaj {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) :
    HasSum (thetaMaj ε) (1 + 2 * ε / (1 - ε ^ 3)) :=
  hasSum_geomMaj (by positivity) (pow_lt_one₀ h0 h1 (by norm_num)) (thetaMaj ε) (by simp [thetaMaj])
    (fun p hp => by simp [thetaMaj, hp])

theorem hasSum_chiMaj {ε : ℝ} (h0 : 0 ≤ ε) (h1 : 4 * ε ^ 3 < 1) :
    HasSum (chiMaj ε) (0 + 2 * ε / (1 - 4 * ε ^ 3)) :=
  hasSum_geomMaj (by positivity) h1 (chiMaj ε) (by simp [chiMaj]) (fun p hp => by simp [chiMaj, hp])

theorem thetaMaj_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (p : ℤ) : 0 ≤ thetaMaj ε p := by
  unfold thetaMaj; split_ifs <;> positivity

theorem chiMaj_nonneg {ε : ℝ} (h0 : 0 ≤ ε) (p : ℤ) : 0 ≤ chiMaj ε p := by
  unfold chiMaj; split_ifs <;> positivity

theorem exp_sq_le_aux {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    Real.exp (-(((j : ℝ) + 1) ^ 2 * a)) ≤ Real.exp (-a) * (Real.exp (-a) ^ 3) ^ j := by
  rw [← pow_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hj2 : (j : ℝ) ≤ (j : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) j
  push_cast
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hj2)]

theorem natAbs_sq_aux {p : ℤ} {j : ℕ} (hj : p.natAbs = j.succ) : (p : ℝ) ^ 2 = ((j : ℝ) + 1) ^ 2 := by
  have h := Int.natAbs_sq p
  rw [hj] at h
  exact_mod_cast h.symm

/-- Device: `e^{−p²a} ≤ m(p)` for `a ≥ 0`, `ε = e^{−a}` (`p² ≥ 3|p| − 2`). -/
theorem exp_sq_le_thetaMaj {a : ℝ} (ha : 0 ≤ a) (p : ℤ) :
    Real.exp (-((p : ℝ) ^ 2 * a)) ≤ thetaMaj (Real.exp (-a)) p := by
  unfold thetaMaj
  split_ifs with hp
  · subst hp; simp
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Int.natAbs_ne_zero.mpr hp)
    rw [hj, Nat.succ_sub_one, natAbs_sq_aux hj]
    exact exp_sq_le_aux ha j

/-- Device: `p² e^{−p²a} ≤ c(p)` (`p² ≤ 4^{|p|−1}`). -/
theorem sq_mul_exp_sq_le_chiMaj {a : ℝ} (ha : 0 ≤ a) (p : ℤ) :
    (p : ℝ) ^ 2 * Real.exp (-((p : ℝ) ^ 2 * a)) ≤ chiMaj (Real.exp (-a)) p := by
  unfold chiMaj
  split_ifs with hp
  · subst hp; simp
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Int.natAbs_ne_zero.mpr hp)
    rw [hj, Nat.succ_sub_one, natAbs_sq_aux hj]
    have h4 : ((j : ℝ) + 1) ^ 2 ≤ 4 ^ j := by
      have h' : (j : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast Nat.succ_le_of_lt (@Nat.lt_two_pow_self j)
      calc ((j : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ j) ^ 2 := pow_le_pow_left₀ (by positivity) h' 2
        _ = 4 ^ j := by rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
    calc ((j : ℝ) + 1) ^ 2 * Real.exp (-(((j : ℝ) + 1) ^ 2 * a))
        ≤ 4 ^ j * (Real.exp (-a) * (Real.exp (-a) ^ 3) ^ j) :=
          mul_le_mul h4 (exp_sq_le_aux ha j) (Real.exp_pos _).le (by positivity)
      _ = Real.exp (-a) * (4 * Real.exp (-a) ^ 3) ^ j := by rw [mul_pow]; ring

/-- Device: `t e^{−t/4}` decreases for `t ≥ 4`. -/
theorem mul_exp_anti {s t : ℝ} (hs : 4 ≤ s) (hst : s ≤ t) :
    t * Real.exp (-(t / 4)) ≤ s * Real.exp (-(s / 4)) := by
  have h1 := Real.add_one_le_exp ((t - s) / 4)
  have h2 : t ≤ s * Real.exp ((t - s) / 4) := by
    have : t ≤ s * ((t - s) / 4 + 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hst) (by linarith : (0 : ℝ) ≤ s / 4 - 1)]
    calc t ≤ s * ((t - s) / 4 + 1) := this
      _ ≤ s * Real.exp ((t - s) / 4) := mul_le_mul_of_nonneg_left h1 (by linarith)
  calc t * Real.exp (-(t / 4)) ≤ s * Real.exp ((t - s) / 4) * Real.exp (-(t / 4)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = s * Real.exp (-(s / 4)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- Device: the facts about `ε_L = e^{−L²/4}` used below, for `L ≥ m ≥ 4`. -/
theorem eps_facts {L m : ℝ} (hm : 4 ≤ m) (hmL : m ≤ L) :
    0 ≤ Real.exp (-(L ^ 2 / 4)) ∧ Real.exp (-(L ^ 2 / 4)) ≤ Real.exp (-(m ^ 2 / 4)) ∧
      Real.exp (-(m ^ 2 / 4)) < 0.01832 ∧
        L ^ 2 * Real.exp (-(L ^ 2 / 4)) ≤ m ^ 2 * Real.exp (-(m ^ 2 / 4)) := by
  have hm2 : m ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) hmL 2
  refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (by linarith), ?_, mul_exp_anti (by nlinarith) hm2⟩
  calc Real.exp (-(m ^ 2 / 4)) ≤ Real.exp (-4) := Real.exp_le_exp.mpr (by nlinarith)
    _ < 0.01832 := exp_neg_four_lt

/-- Device: `1 ≤ 1 + 2ε/(1−ε³) ≤ 1 + 2.03ε'` for `0 ≤ ε ≤ ε' < 0.01832`. -/
theorem thetaSum_le {ε ε' : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ ε') (h2 : ε' < 0.01832) :
    1 ≤ 1 + 2 * ε / (1 - ε ^ 3) ∧ 1 + 2 * ε / (1 - ε ^ 3) ≤ 1 + 2.03 * ε' := by
  have h3 : ε ^ 3 ≤ 0.01832 ^ 3 := pow_le_pow_left₀ h0 (by linarith) 3
  have h4 : (0 : ℝ) < 1 - ε ^ 3 := by nlinarith
  have h5 : 0 ≤ 2 * ε / (1 - ε ^ 3) := div_nonneg (by linarith) h4.le
  have : 2 * ε / (1 - ε ^ 3) ≤ 2.03 * ε' := by
    rw [div_le_iff₀ h4]
    nlinarith
  constructor <;> linarith

/-- Device: `0 ≤ 2ε/(1−4ε³) ≤ 2.001ε` for `0 ≤ ε < 0.01832`. -/
theorem chiSum_le {ε : ℝ} (h0 : 0 ≤ ε) (h2 : ε < 0.01832) :
    0 ≤ 0 + 2 * ε / (1 - 4 * ε ^ 3) ∧ 0 + 2 * ε / (1 - 4 * ε ^ 3) ≤ 2.001 * ε ∧ 4 * ε ^ 3 < 1 := by
  have h3 : ε ^ 3 ≤ 0.01832 ^ 3 := pow_le_pow_left₀ h0 h2.le 3
  have h4 : (0 : ℝ) < 1 - 4 * ε ^ 3 := by nlinarith
  refine ⟨by rw [zero_add]; exact div_nonneg (by linarith) h4.le, ?_, by linarith⟩
  rw [zero_add, div_le_iff₀ h4]
  nlinarith

theorem exp_lattice_split (Lx Ly : ℝ) (p k : ℤ) :
    Real.exp (-((p : ℝ) ^ 2 * Lx ^ 2 + (k : ℝ) ^ 2 * Ly ^ 2) / 4) =
      Real.exp (-((p : ℝ) ^ 2 * (Lx ^ 2 / 4))) * Real.exp (-((k : ℝ) ^ 2 * (Ly ^ 2 / 4))) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem ev_term_le (Lx Ly : ℝ) (p k : ℤ) :
    Real.exp (-((p : ℝ) ^ 2 * Lx ^ 2 + (k : ℝ) ^ 2 * Ly ^ 2) / 4) ≤
      thetaMaj (Real.exp (-(Lx ^ 2 / 4))) p * thetaMaj (Real.exp (-(Ly ^ 2 / 4))) k := by
  rw [exp_lattice_split]
  exact mul_le_mul (exp_sq_le_thetaMaj (by positivity) p) (exp_sq_le_thetaMaj (by positivity) k)
    (Real.exp_pos _).le (thetaMaj_nonneg (Real.exp_pos _).le _)

theorem one_le_sq_of_ne {p : ℤ} (hp : p ≠ 0) : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
  have h1 : (1 : ℤ) ≤ p ^ 2 := by
    have := Int.one_le_abs hp
    nlinarith [sq_abs p, abs_nonneg p]
  exact_mod_cast h1

theorem evD_term_le {Lx Ly : ℝ} (hx : 4 ≤ Lx) (hy : 4 ≤ Ly) (p k : ℤ) (hpk : (p, k) ≠ 0) (c : ℝ)
    (hc : |c| ≤ 1) :
    |(1 - ((p : ℝ) ^ 2 * Lx ^ 2 + (k : ℝ) ^ 2 * Ly ^ 2) / 2) *
        Real.exp (-((p : ℝ) ^ 2 * Lx ^ 2 + (k : ℝ) ^ 2 * Ly ^ 2) / 4) * c| ≤
      1 / 2 * (Lx ^ 2 * (chiMaj (Real.exp (-(Lx ^ 2 / 4))) p * thetaMaj (Real.exp (-(Ly ^ 2 / 4))) k) +
        Ly ^ 2 * (thetaMaj (Real.exp (-(Lx ^ 2 / 4))) p * chiMaj (Real.exp (-(Ly ^ 2 / 4))) k)) := by
  have hax : 0 ≤ Lx ^ 2 / 4 := by positivity
  have hay : 0 ≤ Ly ^ 2 / 4 := by positivity
  have hεx0 : 0 ≤ Real.exp (-(Lx ^ 2 / 4)) := (Real.exp_pos _).le
  have hq : 2 ≤ (p : ℝ) ^ 2 * Lx ^ 2 + (k : ℝ) ^ 2 * Ly ^ 2 := by
    have hLx2 : 16 ≤ Lx ^ 2 := by nlinarith
    have hLy2 : 16 ≤ Ly ^ 2 := by nlinarith
    have hp0 : 0 ≤ (p : ℝ) ^ 2 := sq_nonneg _
    have hk0 : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
    by_cases hp : p = 0
    · have hk : k ≠ 0 := by
        rintro rfl
        exact hpk (by rw [hp]; rfl)
      have := one_le_sq_of_ne hk
      nlinarith
    · have := one_le_sq_of_ne hp
      nlinarith
  have hcx := sq_mul_exp_sq_le_chiMaj hax p
  have hcy := sq_mul_exp_sq_le_chiMaj hay k
  have htx := exp_sq_le_thetaMaj hax p
  have hty := exp_sq_le_thetaMaj hay k
  have hex := Real.exp_pos (-((p : ℝ) ^ 2 * (Lx ^ 2 / 4)))
  have hey := Real.exp_pos (-((k : ℝ) ^ 2 * (Ly ^ 2 / 4)))
  have hb1 : (p : ℝ) ^ 2 * Real.exp (-((p : ℝ) ^ 2 * (Lx ^ 2 / 4))) * Real.exp (-((k : ℝ) ^ 2 * (Ly ^ 2 / 4))) ≤
      chiMaj (Real.exp (-(Lx ^ 2 / 4))) p * thetaMaj (Real.exp (-(Ly ^ 2 / 4))) k :=
    mul_le_mul hcx hty hey.le (chiMaj_nonneg hεx0 _)
  have hb2 : Real.exp (-((p : ℝ) ^ 2 * (Lx ^ 2 / 4))) * ((k : ℝ) ^ 2 * Real.exp (-((k : ℝ) ^ 2 * (Ly ^ 2 / 4)))) ≤
      thetaMaj (Real.exp (-(Lx ^ 2 / 4))) p * chiMaj (Real.exp (-(Ly ^ 2 / 4))) k :=
    mul_le_mul htx hcy (by positivity) (thetaMaj_nonneg hεx0 _)
  have habs : |1 - ((p : ℝ) ^ 2 * Lx ^ 2 + (k : ℝ) ^ 2 * Ly ^ 2) / 2| ≤
      ((p : ℝ) ^ 2 * Lx ^ 2 + (k : ℝ) ^ 2 * Ly ^ 2) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [exp_lattice_split, abs_mul, abs_mul, abs_of_pos (mul_pos hex hey)]
  calc |1 - ((p : ℝ) ^ 2 * Lx ^ 2 + (k : ℝ) ^ 2 * Ly ^ 2) / 2| *
        (Real.exp (-((p : ℝ) ^ 2 * (Lx ^ 2 / 4))) * Real.exp (-((k : ℝ) ^ 2 * (Ly ^ 2 / 4)))) * |c|
      ≤ ((p : ℝ) ^ 2 * Lx ^ 2 + (k : ℝ) ^ 2 * Ly ^ 2) / 2 *
        (Real.exp (-((p : ℝ) ^ 2 * (Lx ^ 2 / 4))) * Real.exp (-((k : ℝ) ^ 2 * (Ly ^ 2 / 4)))) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right habs (by positivity)) hc (abs_nonneg _) (by positivity)
    _ = 1 / 2 * (Lx ^ 2 * ((p : ℝ) ^ 2 * Real.exp (-((p : ℝ) ^ 2 * (Lx ^ 2 / 4))) *
          Real.exp (-((k : ℝ) ^ 2 * (Ly ^ 2 / 4)))) +
        Ly ^ 2 * (Real.exp (-((p : ℝ) ^ 2 * (Lx ^ 2 / 4))) *
          ((k : ℝ) ^ 2 * Real.exp (-((k : ℝ) ^ 2 * (Ly ^ 2 / 4)))))) := by ring
    _ ≤ _ := by gcongr

/-- Device: the core of Lemma 2.3(iv), first bound, for any phases `θ` with `θ 0 = 0`. -/
theorem lattice_bound_ev {Lx Ly : ℝ} (hx : 4 ≤ Lx) (hy : 4 ≤ Ly) (θ : ℤ × ℤ → ℝ) (hθ : θ 0 = 0) {S : ℝ}
    (hS : HasSum (fun pk : ℤ × ℤ => 1 / (2 * π) *
      Real.exp (-((pk.1 : ℝ) ^ 2 * Lx ^ 2 + (pk.2 : ℝ) ^ 2 * Ly ^ 2) / 4) * Real.cos (θ pk)) S) :
    |2 * π * S - 1| ≤ 4.2 * Real.exp (-((min Lx Ly) ^ 2 / 4)) := by
  have hm4 : 4 ≤ min Lx Ly := le_min hx hy
  obtain ⟨hεx0, hεxε, hεs, -⟩ := eps_facts hm4 (min_le_left Lx Ly)
  obtain ⟨hεy0, hεyε, -, -⟩ := eps_facts hm4 (min_le_right Lx Ly)
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  have hS2 : HasSum (fun pk : ℤ × ℤ => Real.exp (-((pk.1 : ℝ) ^ 2 * Lx ^ 2 + (pk.2 : ℝ) ^ 2 * Ly ^ 2) / 4) *
      Real.cos (θ pk)) (2 * π * S) := by
    convert hS.mul_left (2 * π) using 1
    funext pk
    rw [← mul_assoc, ← mul_assoc, mul_one_div_cancel hπ, one_mul]
  have hMx := hasSum_thetaMaj hεx0 (by linarith)
  have hMy := hasSum_thetaMaj hεy0 (by linarith)
  have hM := hMx.mul hMy (hMx.summable.mul_of_nonneg hMy.summable (thetaMaj_nonneg hεx0)
    (thetaMaj_nonneg hεy0))
  have hδ : HasSum (fun pk : ℤ × ℤ => if pk = 0 then (1 : ℝ) else 0) 1 := hasSum_ite_eq 0 1
  have hA := hasSum_le (fun pk => by
      have h1 := ev_term_le Lx Ly pk.1 pk.2
      have h2 := Real.cos_le_one (θ pk)
      have h3 := Real.exp_pos (-((pk.1 : ℝ) ^ 2 * Lx ^ 2 + (pk.2 : ℝ) ^ 2 * Ly ^ 2) / 4)
      nlinarith) (hS2.sub hδ) (hM.sub hδ)
  have hB := hasSum_le (fun pk => by
      by_cases h0 : pk = 0
      · subst h0
        simp [thetaMaj, hθ]
      · have h1 := ev_term_le Lx Ly pk.1 pk.2
        have h2 := Real.neg_one_le_cos (θ pk)
        have h3 := Real.exp_pos (-((pk.1 : ℝ) ^ 2 * Lx ^ 2 + (pk.2 : ℝ) ^ 2 * Ly ^ 2) / 4)
        simp only [ite_eq_right h0]
        nlinarith) (hS2.sub hδ).neg (hM.sub hδ)
  obtain ⟨hMx1, hMxle⟩ := thetaSum_le hεx0 hεxε hεs
  obtain ⟨hMy1, hMyle⟩ := thetaSum_le hεy0 hεyε hεs
  have hprod := mul_le_mul hMxle hMyle (by linarith) (by linarith)
  have hε0 : 0 ≤ Real.exp (-((min Lx Ly) ^ 2 / 4)) := (Real.exp_pos _).le
  have hfin : (1 + 2.03 * Real.exp (-((min Lx Ly) ^ 2 / 4))) * (1 + 2.03 * Real.exp (-((min Lx Ly) ^ 2 / 4))) - 1 ≤
      4.2 * Real.exp (-((min Lx Ly) ^ 2 / 4)) := by
    nlinarith [mul_le_mul_of_nonneg_left hεs.le hε0]
  rw [abs_le]
  constructor <;> linarith

/-- Device: the core of Lemma 2.3(iv), second bound. -/
theorem lattice_bound_evD {Lx Ly : ℝ} (hx : 4 ≤ Lx) (hy : 4 ≤ Ly) (θ : ℤ × ℤ → ℝ) (hθ : θ 0 = 0) {S : ℝ}
    (hS : HasSum (fun pk : ℤ × ℤ => 1 / (4 * π) * (1 - ((pk.1 : ℝ) ^ 2 * Lx ^ 2 + (pk.2 : ℝ) ^ 2 * Ly ^ 2) / 2) *
      Real.exp (-((pk.1 : ℝ) ^ 2 * Lx ^ 2 + (pk.2 : ℝ) ^ 2 * Ly ^ 2) / 4) * Real.cos (θ pk)) S) :
    |4 * π * S - 1| ≤ 2.1 * (min Lx Ly) ^ 2 * Real.exp (-((min Lx Ly) ^ 2 / 4)) := by
  have hm4 : 4 ≤ min Lx Ly := le_min hx hy
  obtain ⟨hεx0, hεxε, hεs, hLxε⟩ := eps_facts hm4 (min_le_left Lx Ly)
  obtain ⟨hεy0, hεyε, -, hLyε⟩ := eps_facts hm4 (min_le_right Lx Ly)
  have hπ : (4 * π : ℝ) ≠ 0 := by positivity
  have hS2 : HasSum (fun pk : ℤ × ℤ => (1 - ((pk.1 : ℝ) ^ 2 * Lx ^ 2 + (pk.2 : ℝ) ^ 2 * Ly ^ 2) / 2) *
      Real.exp (-((pk.1 : ℝ) ^ 2 * Lx ^ 2 + (pk.2 : ℝ) ^ 2 * Ly ^ 2) / 4) * Real.cos (θ pk)) (4 * π * S) := by
    convert hS.mul_left (4 * π) using 1
    funext pk
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_one_div_cancel hπ, one_mul]
  obtain ⟨hCx0, hCxle, hCx4⟩ := chiSum_le hεx0 (lt_of_le_of_lt hεxε hεs)
  obtain ⟨hCy0, hCyle, hCy4⟩ := chiSum_le hεy0 (lt_of_le_of_lt hεyε hεs)
  obtain ⟨hMx1, hMxle⟩ := thetaSum_le hεx0 hεxε hεs
  obtain ⟨hMy1, hMyle⟩ := thetaSum_le hεy0 hεyε hεs
  have hMx := hasSum_thetaMaj hεx0 (by linarith)
  have hMy := hasSum_thetaMaj hεy0 (by linarith)
  have hCx := hasSum_chiMaj hεx0 hCx4
  have hCy := hasSum_chiMaj hεy0 hCy4
  have hW1 := hCx.mul hMy (hCx.summable.mul_of_nonneg hMy.summable (chiMaj_nonneg hεx0) (thetaMaj_nonneg hεy0))
  have hW2 := hMx.mul hCy (hMx.summable.mul_of_nonneg hCy.summable (thetaMaj_nonneg hεx0) (chiMaj_nonneg hεy0))
  have hW := ((hW1.mul_left (Lx ^ 2)).add (hW2.mul_left (Ly ^ 2))).mul_left (1 / 2)
  have hδ : HasSum (fun pk : ℤ × ℤ => if pk = 0 then (1 : ℝ) else 0) 1 := hasSum_ite_eq 0 1
  have hterm : ∀ pk : ℤ × ℤ,
      |(1 - ((pk.1 : ℝ) ^ 2 * Lx ^ 2 + (pk.2 : ℝ) ^ 2 * Ly ^ 2) / 2) *
        Real.exp (-((pk.1 : ℝ) ^ 2 * Lx ^ 2 + (pk.2 : ℝ) ^ 2 * Ly ^ 2) / 4) * Real.cos (θ pk) -
          (if pk = 0 then (1 : ℝ) else 0)| ≤
        1 / 2 * (Lx ^ 2 * (chiMaj (Real.exp (-(Lx ^ 2 / 4))) pk.1 * thetaMaj (Real.exp (-(Ly ^ 2 / 4))) pk.2) +
          Ly ^ 2 * (thetaMaj (Real.exp (-(Lx ^ 2 / 4))) pk.1 * chiMaj (Real.exp (-(Ly ^ 2 / 4))) pk.2)) := by
    intro pk
    by_cases h0 : pk = 0
    · subst h0
      simp [thetaMaj, chiMaj, hθ]
    · rw [ite_eq_right h0, sub_zero]
      exact evD_term_le hx hy pk.1 pk.2 (by rwa [Prod.mk.eta]) _ (Real.abs_cos_le_one _)
  have hA := hasSum_le (fun pk => (abs_le.mp (hterm pk)).2) (hS2.sub hδ) hW
  have hB := hasSum_le (fun pk => by
      have := (abs_le.mp (hterm pk)).1
      linarith) (hS2.sub hδ).neg hW
  have hε0 : 0 ≤ Real.exp (-((min Lx Ly) ^ 2 / 4)) := (Real.exp_pos _).le
  have hA0 : 0 ≤ (min Lx Ly) ^ 2 * Real.exp (-((min Lx Ly) ^ 2 / 4)) := by positivity
  have hX : Lx ^ 2 * (0 + 2 * Real.exp (-(Lx ^ 2 / 4)) / (1 - 4 * Real.exp (-(Lx ^ 2 / 4)) ^ 3)) ≤
      2.001 * ((min Lx Ly) ^ 2 * Real.exp (-((min Lx Ly) ^ 2 / 4))) := by
    calc Lx ^ 2 * (0 + 2 * Real.exp (-(Lx ^ 2 / 4)) / (1 - 4 * Real.exp (-(Lx ^ 2 / 4)) ^ 3))
        ≤ Lx ^ 2 * (2.001 * Real.exp (-(Lx ^ 2 / 4))) := mul_le_mul_of_nonneg_left hCxle (sq_nonneg _)
      _ ≤ 2.001 * ((min Lx Ly) ^ 2 * Real.exp (-((min Lx Ly) ^ 2 / 4))) := by linarith
  have hY : Ly ^ 2 * (0 + 2 * Real.exp (-(Ly ^ 2 / 4)) / (1 - 4 * Real.exp (-(Ly ^ 2 / 4)) ^ 3)) ≤
      2.001 * ((min Lx Ly) ^ 2 * Real.exp (-((min Lx Ly) ^ 2 / 4))) := by
    calc Ly ^ 2 * (0 + 2 * Real.exp (-(Ly ^ 2 / 4)) / (1 - 4 * Real.exp (-(Ly ^ 2 / 4)) ^ 3))
        ≤ Ly ^ 2 * (2.001 * Real.exp (-(Ly ^ 2 / 4))) := mul_le_mul_of_nonneg_left hCyle (sq_nonneg _)
      _ ≤ 2.001 * ((min Lx Ly) ^ 2 * Real.exp (-((min Lx Ly) ^ 2 / 4))) := by linarith
  have hP1 := mul_le_mul hX hMyle (by linarith) (by positivity)
  have hP2 := mul_le_mul hY hMxle (by linarith) (by positivity)
  have hfin : 1 / 2 * (Lx ^ 2 * ((0 + 2 * Real.exp (-(Lx ^ 2 / 4)) / (1 - 4 * Real.exp (-(Lx ^ 2 / 4)) ^ 3)) *
      (1 + 2 * Real.exp (-(Ly ^ 2 / 4)) / (1 - Real.exp (-(Ly ^ 2 / 4)) ^ 3))) +
      Ly ^ 2 * ((1 + 2 * Real.exp (-(Lx ^ 2 / 4)) / (1 - Real.exp (-(Lx ^ 2 / 4)) ^ 3)) *
        (0 + 2 * Real.exp (-(Ly ^ 2 / 4)) / (1 - 4 * Real.exp (-(Ly ^ 2 / 4)) ^ 3)))) ≤
      2.1 * (min Lx Ly) ^ 2 * Real.exp (-((min Lx Ly) ^ 2 / 4)) := by
    have e1 : Lx ^ 2 * ((0 + 2 * Real.exp (-(Lx ^ 2 / 4)) / (1 - 4 * Real.exp (-(Lx ^ 2 / 4)) ^ 3)) *
        (1 + 2 * Real.exp (-(Ly ^ 2 / 4)) / (1 - Real.exp (-(Ly ^ 2 / 4)) ^ 3))) =
        Lx ^ 2 * (0 + 2 * Real.exp (-(Lx ^ 2 / 4)) / (1 - 4 * Real.exp (-(Lx ^ 2 / 4)) ^ 3)) *
        (1 + 2 * Real.exp (-(Ly ^ 2 / 4)) / (1 - Real.exp (-(Ly ^ 2 / 4)) ^ 3)) := by ring
    have e2 : Ly ^ 2 * ((1 + 2 * Real.exp (-(Lx ^ 2 / 4)) / (1 - Real.exp (-(Lx ^ 2 / 4)) ^ 3)) *
        (0 + 2 * Real.exp (-(Ly ^ 2 / 4)) / (1 - 4 * Real.exp (-(Ly ^ 2 / 4)) ^ 3))) =
        Ly ^ 2 * (0 + 2 * Real.exp (-(Ly ^ 2 / 4)) / (1 - 4 * Real.exp (-(Ly ^ 2 / 4)) ^ 3)) *
        (1 + 2 * Real.exp (-(Lx ^ 2 / 4)) / (1 - Real.exp (-(Lx ^ 2 / 4)) ^ 3)) := by ring
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left hεs.le hA0]
  rw [abs_le]
  constructor <;> linarith


/-! ### Proof devices for Definition 2.7's lattice-sum form (`Vcoef_latticeSum`; phase (b), not statements of the paper)

Parseval's identity on the rectangle `[0, L_x) × [0, L_y)` for doubly periodic continuous functions, through Mathlib's
`UnitAddTorus` (`UnitAddTorus.hasSum_prod_mFourierCoeff`, with the Haar measure of `ℝ/ℤ` as Mathlib's
`Mathlib.Analysis.Fourier.AddCircleMulti` takes it, by the same local instances), and the Fourier coefficients of the
Laplacian by two integrations by parts in each variable (`rectFT_lap`). The section's devices are generic (any doubly
periodic function); block A's `Vcoef_latticeSum` (`HRTorus.Fock`) specializes them to the pair densities. -/

section VcoefDevices

open scoped ComplexConjugate ContDiff

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open UnitAddTorus

/-- the quotient map `(Fin 2 → ℝ) → 𝕋²` -/
def torusMk (x : Fin 2 → ℝ) : UnitAddTorus (Fin 2) := fun i => (x i : UnitAddCircle)

theorem isOpenQuotientMap_torusMk : IsOpenQuotientMap torusMk :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

/-- the rescaled lift of a doubly periodic function -/
def torusLift (Lx Ly : ℝ) (f : ℝ × ℝ → ℂ) (t : UnitAddTorus (Fin 2)) : ℂ :=
  f (Lx * (AddCircle.equivIco 1 0 (t 0) : ℝ), Ly * (AddCircle.equivIco 1 0 (t 1) : ℝ))

theorem torusLift_mk {Lx Ly : ℝ} {f : ℝ × ℝ → ℂ} (hx : ∀ x y, f (x + Lx, y) = f (x, y))
    (hy : ∀ x y, f (x, y + Ly) = f (x, y)) (x : Fin 2 → ℝ) :
    torusLift Lx Ly f (torusMk x) = f (Lx * x 0, Ly * x 1) := by
  have hpx : ∀ y, Function.Periodic (fun u => f (u, y)) Lx := fun y u => hx u y
  have hpy : ∀ u, Function.Periodic (fun y => f (u, y)) Ly := fun u y => hy u y
  unfold torusLift torusMk
  have e0 : (AddCircle.equivIco 1 0 ((x 0 : ℝ) : UnitAddCircle) : ℝ) = Int.fract (x 0) := by
    rw [AddCircle.coe_equivIco_mk_apply]; simp
  have e1 : (AddCircle.equivIco 1 0 ((x 1 : ℝ) : UnitAddCircle) : ℝ) = Int.fract (x 1) := by
    rw [AddCircle.coe_equivIco_mk_apply]; simp
  rw [e0, e1, Int.fract, Int.fract]
  have h1 : f (Lx * (x 0 - ⌊x 0⌋), Ly * (x 1 - ⌊x 1⌋)) = f (Lx * x 0, Ly * (x 1 - ⌊x 1⌋)) := by
    have := (hpx (Ly * (x 1 - ⌊x 1⌋))).sub_int_mul_eq (x := Lx * x 0) ⌊x 0⌋
    rw [← this]; congr 2; ring
  have h2 : f (Lx * x 0, Ly * (x 1 - ⌊x 1⌋)) = f (Lx * x 0, Ly * x 1) := by
    have := (hpy (Lx * x 0)).sub_int_mul_eq (x := Ly * x 1) ⌊x 1⌋
    rw [← this]; congr 2; ring
  rw [h1, h2]

theorem continuous_torusLift {Lx Ly : ℝ} {f : ℝ × ℝ → ℂ} (hx : ∀ x y, f (x + Lx, y) = f (x, y))
    (hy : ∀ x y, f (x, y + Ly) = f (x, y)) (hf : Continuous f) : Continuous (torusLift Lx Ly f) := by
  rw [← isOpenQuotientMap_torusMk.continuous_comp_iff]
  have e : torusLift Lx Ly f ∘ torusMk = fun x => f (Lx * x 0, Ly * x 1) := funext (torusLift_mk hx hy)
  rw [e]
  fun_prop

/-- the Fourier coefficient on the rectangle (block A's `torusFourier`, for general sides) -/
def rectFT (Lx Ly : ℝ) (f : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  ∫ r in Set.Ico 0 Lx ×ˢ Set.Ico 0 Ly, f r * Complex.exp (-(I * ((q.1 * r.1 + q.2 * r.2 : ℝ) : ℂ)))

theorem setIntegral_Ioc_comp_mul {L : ℝ} (hL : 0 < L) (h : ℝ → ℂ) :
    ∫ t in Set.Ioc (0 : ℝ) 1, h (L * t) = (1 / L : ℂ) * ∫ u in Set.Ioc (0 : ℝ) L, h u := by
  rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le hL.le,
    intervalIntegral.integral_comp_mul_left h hL.ne', mul_zero, mul_one, Complex.real_smul]
  push_cast
  ring

theorem integral_cube {G : ℝ × ℝ → ℂ} (hG : Continuous G) :
    ∫ x in {x : Fin 2 → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i + 1)}, G (x 0, x 1) =
      ∫ s in Set.Ioc (0 : ℝ) 1, ∫ t in Set.Ioc (0 : ℝ) 1, G (s, t) := by
  have hmp := measurePreserving_finTwoArrow (volume : Measure ℝ)
  have himg : (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ''
      {x : Fin 2 → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i + 1)} =
      Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1 := by
    ext p
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_prod, Pi.zero_apply, zero_add]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx 0, hx 1⟩
    · rintro ⟨h0, h1⟩
      refine ⟨![p.1, p.2], fun i => ?_, ?_⟩
      · fin_cases i
        · simpa using h0
        · simpa using h1
      · rfl
  have hint : IntegrableOn G (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) ((volume : Measure ℝ).prod volume) :=
    (hG.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  rw [← setIntegral_prod G hint, ← himg, hmp.setIntegral_image_emb MeasurableEquiv.finTwoArrow.measurableEmbedding]
  rfl

theorem mFourierCoeff_torusLift {Lx Ly : ℝ} (hLx : 0 < Lx) (hLy : 0 < Ly) {f : ℝ × ℝ → ℂ}
    (hx : ∀ x y, f (x + Lx, y) = f (x, y)) (hy : ∀ x y, f (x, y + Ly) = f (x, y)) (hf : Continuous f)
    (n : Fin 2 → ℤ) :
    mFourierCoeff (torusLift Lx Ly f) n =
      (1 / (Lx * Ly) : ℂ) * rectFT Lx Ly f (2 * π * n 0 / Lx, 2 * π * n 1 / Ly) := by
  rw [mFourierCoeff_eq_integral _ n 0]
  set G : ℝ × ℝ → ℂ := fun p => Complex.exp (-(2 * π * I * (n 0 : ℂ) * p.1)) *
    Complex.exp (-(2 * π * I * (n 1 : ℂ) * p.2)) * f (Lx * p.1, Ly * p.2) with hG
  have hpt : ∀ x : Fin 2 → ℝ, mFourier (-n) (fun i => (x i : UnitAddCircle)) •
      torusLift Lx Ly f (fun i => (x i : UnitAddCircle)) = G (x 0, x 1) := by
    intro x
    have h1 : torusLift Lx Ly f (fun i => (x i : UnitAddCircle)) = f (Lx * x 0, Ly * x 1) := torusLift_mk hx hy x
    rw [h1, smul_eq_mul, hG]
    simp only [mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two, Pi.neg_apply, fourier_coe_apply,
      Complex.ofReal_one, div_one]
    push_cast
    ring_nf
  have hGc : Continuous G := by rw [hG]; fun_prop
  rw [show (∫ x in {x : Fin 2 → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i + 1)},
      mFourier (-n) (fun i => (x i : UnitAddCircle)) • torusLift Lx Ly f (fun i => (x i : UnitAddCircle))) =
      ∫ x in {x : Fin 2 → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i + 1)}, G (x 0, x 1) by
    congr 1; funext x; exact hpt x, integral_cube hGc]
  simp only [hG]
  -- the scalings
  have hin : ∀ s : ℝ, ∫ t in Set.Ioc (0 : ℝ) 1, Complex.exp (-(2 * π * I * (n 0 : ℂ) * s)) *
      Complex.exp (-(2 * π * I * (n 1 : ℂ) * t)) * f (Lx * s, Ly * t) =
      (1 / Ly : ℂ) * ∫ u in Set.Ioc (0 : ℝ) Ly, Complex.exp (-(2 * π * I * (n 0 : ℂ) * s)) *
        Complex.exp (-(2 * π * I * (n 1 : ℂ) * u / Ly)) * f (Lx * s, u) := by
    intro s
    rw [← setIntegral_Ioc_comp_mul hLy]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    have hLy0 : (Ly : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLy.ne'
    congr 2
    push_cast
    field_simp
  simp_rw [hin]
  rw [integral_const_mul]
  have hout : ∫ s in Set.Ioc (0 : ℝ) 1, ∫ u in Set.Ioc (0 : ℝ) Ly, Complex.exp (-(2 * π * I * (n 0 : ℂ) * s)) *
        Complex.exp (-(2 * π * I * (n 1 : ℂ) * u / Ly)) * f (Lx * s, u) =
      (1 / Lx : ℂ) * ∫ w in Set.Ioc (0 : ℝ) Lx, ∫ u in Set.Ioc (0 : ℝ) Ly,
        Complex.exp (-(2 * π * I * (n 0 : ℂ) * w / Lx)) *
        Complex.exp (-(2 * π * I * (n 1 : ℂ) * u / Ly)) * f (w, u) := by
    rw [← setIntegral_Ioc_comp_mul hLx (fun w => ∫ u in Set.Ioc (0 : ℝ) Ly,
        Complex.exp (-(2 * π * I * (n 0 : ℂ) * w / Lx)) *
        Complex.exp (-(2 * π * I * (n 1 : ℂ) * u / Ly)) * f (w, u))]
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    have hLx0 : (Lx : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLx.ne'
    congr 3
    push_cast
    field_simp
  rw [hout]
  -- the rectangle
  have hrect : rectFT Lx Ly f (2 * π * n 0 / Lx, 2 * π * n 1 / Ly) =
      ∫ w in Set.Ioc (0 : ℝ) Lx, ∫ u in Set.Ioc (0 : ℝ) Ly, Complex.exp (-(2 * π * I * (n 0 : ℂ) * w / Lx)) *
        Complex.exp (-(2 * π * I * (n 1 : ℂ) * u / Ly)) * f (w, u) := by
    unfold rectFT
    dsimp only
    rw [Measure.volume_eq_prod, setIntegral_prod _ ((by fun_prop : Continuous fun r : ℝ × ℝ => f r *
      Complex.exp (-(I * (((2 * π * n 0 / Lx) * r.1 + (2 * π * n 1 / Ly) * r.2 : ℝ) : ℂ)))).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc) |>.mono_set (Set.prod_mono Set.Ico_subset_Icc_self Set.Ico_subset_Icc_self)),
      integral_Ico_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioc fun w _ => ?_
    rw [integral_Ico_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only []
    rw [← Complex.exp_add, mul_comm (f (w, u))]
    congr 2
    push_cast
    ring
  rw [hrect]
  ring

theorem rectFT_zero (Lx Ly : ℝ) (f : ℝ × ℝ → ℂ) :
    rectFT Lx Ly f (0, 0) = ∫ r in Set.Ico 0 Lx ×ˢ Set.Ico 0 Ly, f r := by
  unfold rectFT
  simp

theorem rectFT_star (Lx Ly : ℝ) (f : ℝ × ℝ → ℂ) (q : ℝ × ℝ) :
    star (rectFT Lx Ly (fun r => star (f r)) q) = rectFT Lx Ly f (-q) := by
  unfold rectFT
  rw [Complex.star_def, ← integral_conj]
  congr 1
  funext r
  rw [map_mul, Complex.conj_conj, ← Complex.exp_conj]
  congr 2
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Prod.fst_neg, Prod.snd_neg]
  push_cast
  ring

/-- Parseval's identity on the rectangle, for doubly periodic continuous functions. -/
theorem parseval_rect {Lx Ly : ℝ} (hLx : 0 < Lx) (hLy : 0 < Ly) {f g : ℝ × ℝ → ℂ}
    (hfx : ∀ x y, f (x + Lx, y) = f (x, y)) (hfy : ∀ x y, f (x, y + Ly) = f (x, y)) (hf : Continuous f)
    (hgx : ∀ x y, g (x + Lx, y) = g (x, y)) (hgy : ∀ x y, g (x, y + Ly) = g (x, y)) (hg : Continuous g) :
    HasSum (fun pk : ℤ × ℤ => (1 / (Lx * Ly) : ℂ) * rectFT Lx Ly f (-(2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly)) *
        rectFT Lx Ly g (2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly))
      (∫ r in Set.Ico 0 Lx ×ˢ Set.Ico 0 Ly, f r * g r) := by
  have hsx : ∀ x y, (fun r => star (f r)) (x + Lx, y) = (fun r => star (f r)) (x, y) := fun x y => by
    simp only [hfx]
  have hsy : ∀ x y, (fun r => star (f r)) (x, y + Ly) = (fun r => star (f r)) (x, y) := fun x y => by
    simp only [hfy]
  have hsc : Continuous (fun r => star (f r)) := hf.star
  let F1 : C(UnitAddTorus (Fin 2), ℂ) := ⟨torusLift Lx Ly (fun r => star (f r)), continuous_torusLift hsx hsy hsc⟩
  let F2 : C(UnitAddTorus (Fin 2), ℂ) := ⟨torusLift Lx Ly g, continuous_torusLift hgx hgy hg⟩
  have h := hasSum_prod_mFourierCoeff (F1.toLp 2 volume ℂ) (F2.toLp 2 volume ℂ)
  simp only [mFourierCoeff_toLp] at h
  -- the integral
  have hint : ∫ t, conj ((F1.toLp 2 volume ℂ) t) * (F2.toLp 2 volume ℂ) t =
      ∫ t, mFourier (-0) t • torusLift Lx Ly (fun r => f r * g r) t := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) F1,
      ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) F2] with t h1 h2
    rw [h1, h2, neg_zero, mFourier_zero, ContinuousMap.one_apply, one_smul]
    show conj (star (f _)) * g _ = f _ * g _
    rw [Complex.star_def, Complex.conj_conj]
  rw [hint] at h
  have hfgx : ∀ x y, (fun r => f r * g r) (x + Lx, y) = (fun r => f r * g r) (x, y) := fun x y => by
    simp only [hfx, hgx]
  have hfgy : ∀ x y, (fun r => f r * g r) (x, y + Ly) = (fun r => f r * g r) (x, y) := fun x y => by
    simp only [hfy, hgy]
  have h0 := mFourierCoeff_torusLift (f := fun r => f r * g r) hLx hLy hfgx hfgy (hf.mul hg) 0
  unfold mFourierCoeff at h0
  rw [h0] at h
  have h1 : ∀ n : Fin 2 → ℤ, conj (mFourierCoeff (⇑F1) n) * mFourierCoeff (⇑F2) n =
      (1 / (Lx * Ly) : ℂ) * (1 / (Lx * Ly) : ℂ) * (rectFT Lx Ly f (-(2 * π * n 0 / Lx, 2 * π * n 1 / Ly)) *
        rectFT Lx Ly g (2 * π * n 0 / Lx, 2 * π * n 1 / Ly)) := by
    intro n
    rw [show (⇑F1 : UnitAddTorus (Fin 2) → ℂ) = torusLift Lx Ly (fun r => star (f r)) from rfl,
      show (⇑F2 : UnitAddTorus (Fin 2) → ℂ) = torusLift Lx Ly g from rfl,
      mFourierCoeff_torusLift hLx hLy hsx hsy hsc n, mFourierCoeff_torusLift hLx hLy hgx hgy hg n, map_mul,
      ← Complex.star_def, rectFT_star]
    have hc : star (1 / ((Lx : ℂ) * Ly)) = 1 / ((Lx : ℂ) * Ly) := by
      rw [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [hc]
    ring
  simp only [h1] at h
  have h2 := ((finTwoArrowEquiv ℤ).symm.hasSum_iff.mpr h).mul_left ((Lx * Ly : ℝ) : ℂ)
  have hLx0 : (Lx : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLx.ne'
  have hLy0 : (Ly : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLy.ne'
  convert h2 using 1
  · funext pk
    simp only [Function.comp, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    field_simp
  · simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_div]
    rw [rectFT_zero]
    push_cast
    field_simp

theorem periodic_deriv {L : ℝ} {h : ℝ → ℂ} (hper : Function.Periodic h L) : Function.Periodic (deriv h) L := by
  intro x
  have e : (fun y => h (y + L)) = h := funext hper
  rw [← deriv_comp_add_const, e]

/-- 1D: `∫_0^L h'' e^{−iαx} dx = −α² ∫_0^L h e^{−iαx} dx` for `h` smooth and `L`-periodic, `α = 2πp/L`. -/
theorem integral_deriv2_mul_exp {L : ℝ} (hL : 0 < L) {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hper : Function.Periodic h L) (p : ℤ) :
    ∫ x in Set.Ico 0 L, deriv (deriv h) x * Complex.exp (-(I * ((2 * π * p / L * x : ℝ) : ℂ))) =
      -((2 * π * p / L : ℝ) : ℂ) ^ 2 * ∫ x in Set.Ico 0 L, h x * Complex.exp (-(I * ((2 * π * p / L * x : ℝ) : ℂ))) := by
  set α : ℝ := 2 * π * p / L with hα
  set c : ℂ := -(I * (α : ℂ)) with hc
  have hE : ∀ x : ℝ, Complex.exp (-(I * ((α * x : ℝ) : ℂ))) = Complex.exp ((x : ℂ) * c) := fun x => by
    rw [hc]; congr 1; push_cast; ring
  have hEd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * c)) (Complex.exp ((x : ℂ) * c) * c) x :=
    fun x => ((hasDerivAt_id x).ofReal_comp.mul_const c).cexp.congr_deriv (by simp)
  have hEL : Complex.exp ((L : ℂ) * c) = 1 := by
    have : (L : ℂ) * c = ((-p : ℤ) : ℂ) * (2 * π * I) := by
      rw [hc, hα]
      have hL0 : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
      push_cast
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hd := contDiff_infty_iff_deriv.mp hh
  have hdd := contDiff_infty_iff_deriv.mp hd.2
  have hper' := periodic_deriv hper
  simp_rw [hE]
  rw [integral_Ico_eq_integral_Ioc, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL.le,
    ← intervalIntegral.integral_of_le hL.le]
  have hcont1 : Continuous (deriv h) := hd.2.continuous
  have hcont2 : Continuous (deriv (deriv h)) := hdd.2.continuous
  -- first integration by parts: `∫ E h'' = [E h'] − ∫ E' h'`
  have ibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := L)
    (u := fun x : ℝ => Complex.exp ((x : ℂ) * c)) (u' := fun x => Complex.exp ((x : ℂ) * c) * c)
    (v := deriv h) (v' := deriv (deriv h)) (fun x _ => hEd x)
    (fun x _ => (hdd.1 x).hasDerivAt) (by apply Continuous.intervalIntegrable; fun_prop)
    (hcont2.intervalIntegrable _ _)
  have ibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := L)
    (u := fun x : ℝ => Complex.exp ((x : ℂ) * c)) (u' := fun x => Complex.exp ((x : ℂ) * c) * c)
    (v := h) (v' := deriv h) (fun x _ => hEd x)
    (fun x _ => (hd.1 x).hasDerivAt) (by apply Continuous.intervalIntegrable; fun_prop)
    (hcont1.intervalIntegrable _ _)
  have hp1 : deriv h L = deriv h 0 := by simpa using hper' 0
  have hp0 : h L = h 0 := by simpa using hper 0
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, hEL, hp1, hp0, sub_self, zero_sub] at ibp1 ibp2
  have e1 : (∫ x in (0 : ℝ)..L, deriv (deriv h) x * Complex.exp ((x : ℂ) * c)) =
      ∫ x in (0 : ℝ)..L, Complex.exp ((x : ℂ) * c) * deriv (deriv h) x := by
    congr 1; funext x; ring
  have e2 : (∫ x in (0 : ℝ)..L, Complex.exp ((x : ℂ) * c) * c * deriv h x) =
      c * ∫ x in (0 : ℝ)..L, Complex.exp ((x : ℂ) * c) * deriv h x := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  have e3 : (∫ x in (0 : ℝ)..L, Complex.exp ((x : ℂ) * c) * c * h x) =
      c * ∫ x in (0 : ℝ)..L, h x * Complex.exp ((x : ℂ) * c) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  rw [e1, ibp1, e2, ibp2, e3, hc]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem integrableOn_rect {Lx Ly : ℝ} {g : ℝ × ℝ → ℂ} (hg : Continuous g) :
    IntegrableOn g (Set.Ico 0 Lx ×ˢ Set.Ico 0 Ly) ((volume : Measure ℝ).prod volume) :=
  (hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ico_subset_Icc_self Set.Ico_subset_Icc_self)

theorem rectFT_iter {Lx Ly : ℝ} {g : ℝ × ℝ → ℂ} (hg : Continuous g) (q : ℝ × ℝ) :
    rectFT Lx Ly g q = ∫ x in Set.Ico 0 Lx, ∫ y in Set.Ico 0 Ly,
      g (x, y) * Complex.exp (-(I * ((q.1 * x : ℝ) : ℂ))) * Complex.exp (-(I * ((q.2 * y : ℝ) : ℂ))) := by
  unfold rectFT
  rw [Measure.volume_eq_prod, setIntegral_prod _ (integrableOn_rect (by fun_prop))]
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => setIntegral_congr_fun measurableSet_Ico fun y _ => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem rectFT_iter_swap {Lx Ly : ℝ} {g : ℝ × ℝ → ℂ} (hg : Continuous g) (q : ℝ × ℝ) :
    rectFT Lx Ly g q = ∫ y in Set.Ico 0 Ly, ∫ x in Set.Ico 0 Lx,
      g (x, y) * Complex.exp (-(I * ((q.1 * x : ℝ) : ℂ))) * Complex.exp (-(I * ((q.2 * y : ℝ) : ℂ))) := by
  rw [rectFT_iter hg q]
  refine integral_integral_swap ?_
  have h := integrableOn_rect (Lx := Lx) (Ly := Ly) (g := fun r : ℝ × ℝ => g r *
    Complex.exp (-(I * ((q.1 * r.1 : ℝ) : ℂ))) * Complex.exp (-(I * ((q.2 * r.2 : ℝ) : ℂ)))) (by fun_prop)
  rw [IntegrableOn, ← Measure.prod_restrict] at h
  exact h

theorem contDiff_px {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun r : ℝ × ℝ => deriv (fun x : ℝ => f (x, r.2)) r.1 := by
  have e : (fun r : ℝ × ℝ => deriv (fun x : ℝ => f (x, r.2)) r.1) = fun r => fderiv ℝ f r ((1 : ℝ), (0 : ℝ)) := by
    funext r
    have hd : HasFDerivAt f (fderiv ℝ f r) r := ((hf.differentiable (by simp)) r).hasFDerivAt
    have hc : HasDerivAt (fun x : ℝ => (x, r.2)) ((1 : ℝ), (0 : ℝ)) r.1 :=
      (hasDerivAt_id r.1).prodMk (hasDerivAt_const r.1 r.2)
    exact (hd.comp_hasDerivAt r.1 hc).deriv
  rw [e]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_py {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun r : ℝ × ℝ => deriv (fun y : ℝ => f (r.1, y)) r.2 := by
  have e : (fun r : ℝ × ℝ => deriv (fun y : ℝ => f (r.1, y)) r.2) = fun r => fderiv ℝ f r ((0 : ℝ), (1 : ℝ)) := by
    funext r
    have hd : HasFDerivAt f (fderiv ℝ f r) r := ((hf.differentiable (by simp)) r).hasFDerivAt
    have hc : HasDerivAt (fun y : ℝ => (r.1, y)) ((0 : ℝ), (1 : ℝ)) r.2 :=
      (hasDerivAt_const r.2 r.1).prodMk (hasDerivAt_id r.2)
    exact (hd.comp_hasDerivAt r.2 hc).deriv
  rw [e]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The Fourier coefficients of the Laplacian: `(∇²f)^(q) = −|q|² f̂(q)` on the dual lattice. -/
theorem rectFT_lap {Lx Ly : ℝ} (hLx : 0 < Lx) (hLy : 0 < Ly) {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hx : ∀ x y, f (x + Lx, y) = f (x, y)) (hy : ∀ x y, f (x, y + Ly) = f (x, y)) (pk : ℤ × ℤ) :
    rectFT Lx Ly (fun r => deriv (fun x => deriv (fun x' => f (x', r.2)) x) r.1 +
        deriv (fun y => deriv (fun y' => f (r.1, y')) y) r.2) (2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) =
      -(((2 * π * pk.1 / Lx : ℝ) : ℂ) ^ 2 + ((2 * π * pk.2 / Ly : ℝ) : ℂ) ^ 2) *
        rectFT Lx Ly f (2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) := by
  have hxx : ContDiff ℝ ∞ fun r : ℝ × ℝ => deriv (fun x => deriv (fun x' => f (x', r.2)) x) r.1 :=
    contDiff_px (f := fun r : ℝ × ℝ => deriv (fun x : ℝ => f (x, r.2)) r.1) (contDiff_px hf)
  have hyy : ContDiff ℝ ∞ fun r : ℝ × ℝ => deriv (fun y => deriv (fun y' => f (r.1, y')) y) r.2 :=
    contDiff_py (f := fun r : ℝ × ℝ => deriv (fun y : ℝ => f (r.1, y)) r.2) (contDiff_py hf)
  have hsplit : rectFT Lx Ly (fun r => deriv (fun x => deriv (fun x' => f (x', r.2)) x) r.1 +
        deriv (fun y => deriv (fun y' => f (r.1, y')) y) r.2) (2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) =
      rectFT Lx Ly (fun r => deriv (fun x => deriv (fun x' => f (x', r.2)) x) r.1) (2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) +
      rectFT Lx Ly (fun r => deriv (fun y => deriv (fun y' => f (r.1, y')) y) r.2) (2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) := by
    unfold rectFT
    rw [← integral_add]
    · congr 1; funext r; ring
    · exact integrableOn_rect (hxx.continuous.mul (by fun_prop))
    · exact integrableOn_rect (hyy.continuous.mul (by fun_prop))
  -- the `x`-part, with `x` inner
  have hX : rectFT Lx Ly (fun r => deriv (fun x => deriv (fun x' => f (x', r.2)) x) r.1)
      (2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) =
      -((2 * π * pk.1 / Lx : ℝ) : ℂ) ^ 2 * rectFT Lx Ly f (2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) := by
    rw [rectFT_iter_swap hxx.continuous, rectFT_iter_swap hf.continuous, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ico fun y _ => ?_
    have hh : ContDiff ℝ ∞ (fun x : ℝ => f (x, y)) := hf.comp (contDiff_id.prodMk contDiff_const)
    have hper : Function.Periodic (fun x : ℝ => f (x, y)) Lx := fun x => hx x y
    have h1 := integral_deriv2_mul_exp hLx hh hper pk.1
    simp only []
    rw [show (fun x : ℝ => deriv (fun x => deriv (fun x' => f (x', (x, y).2)) x) (x, y).1 *
        Complex.exp (-(I * (((2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) : ℝ × ℝ).1 * x : ℝ) : ℂ)) *
        Complex.exp (-(I * (((2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) : ℝ × ℝ).2 * y : ℝ) : ℂ))) =
        fun x => (deriv (deriv (fun x : ℝ => f (x, y))) x *
          Complex.exp (-(I * ((2 * π * pk.1 / Lx * x : ℝ) : ℂ)))) *
          Complex.exp (-(I * ((2 * π * pk.2 / Ly * y : ℝ) : ℂ))) from rfl]
    rw [integral_mul_const, h1, mul_assoc, ← integral_mul_const]
  -- the `y`-part, with `y` inner
  have hY : rectFT Lx Ly (fun r => deriv (fun y => deriv (fun y' => f (r.1, y')) y) r.2)
      (2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) =
      -((2 * π * pk.2 / Ly : ℝ) : ℂ) ^ 2 * rectFT Lx Ly f (2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) := by
    rw [rectFT_iter hyy.continuous, rectFT_iter hf.continuous, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
    have hh : ContDiff ℝ ∞ (fun y : ℝ => f (x, y)) := hf.comp (contDiff_const.prodMk contDiff_id)
    have hper : Function.Periodic (fun y : ℝ => f (x, y)) Ly := fun y => hy x y
    have h1 := integral_deriv2_mul_exp hLy hh hper pk.2
    rw [show (fun y : ℝ => deriv (fun y => deriv (fun y' => f ((x, y).1, y')) y) (x, y).2 *
        Complex.exp (-(I * (((2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) : ℝ × ℝ).1 * x : ℝ) : ℂ)) *
        Complex.exp (-(I * (((2 * π * pk.1 / Lx, 2 * π * pk.2 / Ly) : ℝ × ℝ).2 * y : ℝ) : ℂ))) =
        fun y => (deriv (deriv (fun y : ℝ => f (x, y))) y *
          Complex.exp (-(I * ((2 * π * pk.2 / Ly * y : ℝ) : ℂ)))) *
          Complex.exp (-(I * ((2 * π * pk.1 / Lx * x : ℝ) : ℂ))) by
      funext y; ring]
    rw [integral_mul_const, h1, mul_assoc, ← integral_mul_const]
    congr 2
    funext y
    ring
  rw [hsplit, hX, hY]
  ring

theorem contDiff_star2 {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ fun r => star (f r) := by
  have h : (fun r => star (f r)) = fun r => Complex.conjCLE (f r) := by
    funext r; simp
  rw [h]
  exact Complex.conjCLE.contDiff.comp hf

theorem phase_star_mul_self2 {z : ℂ} (hz : z.re = 0) : star (Complex.exp z) * Complex.exp z = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have : (starRingEnd ℂ) z + z = 0 := by
    apply Complex.ext <;> simp [hz]
  rw [this, Complex.exp_zero]

/-- the second partials of a doubly periodic `C^∞` function are doubly periodic, and so is its Laplacian -/
theorem lap_periodic {Lx Ly : ℝ} {f : ℝ × ℝ → ℂ} (hx : ∀ x y, f (x + Lx, y) = f (x, y))
    (hy : ∀ x y, f (x, y + Ly) = f (x, y)) :
    (∀ x y, (fun r : ℝ × ℝ => deriv (fun x => deriv (fun x' => f (x', r.2)) x) r.1 +
        deriv (fun y => deriv (fun y' => f (r.1, y')) y) r.2) (x + Lx, y) =
      (fun r : ℝ × ℝ => deriv (fun x => deriv (fun x' => f (x', r.2)) x) r.1 +
        deriv (fun y => deriv (fun y' => f (r.1, y')) y) r.2) (x, y)) ∧
    (∀ x y, (fun r : ℝ × ℝ => deriv (fun x => deriv (fun x' => f (x', r.2)) x) r.1 +
        deriv (fun y => deriv (fun y' => f (r.1, y')) y) r.2) (x, y + Ly) =
      (fun r : ℝ × ℝ => deriv (fun x => deriv (fun x' => f (x', r.2)) x) r.1 +
        deriv (fun y => deriv (fun y' => f (r.1, y')) y) r.2) (x, y)) := by
  constructor
  · intro x y
    have h1 : Function.Periodic (deriv (fun x' => f (x', y))) Lx := periodic_deriv fun u => hx u y
    have h2 : Function.Periodic (deriv (deriv (fun x' => f (x', y)))) Lx := periodic_deriv h1
    have h3 : (fun y' => f (x + Lx, y')) = fun y' => f (x, y') := funext fun y' => hx x y'
    simp only []
    rw [h3]
    congr 1
    exact h2 x
  · intro x y
    have h1 : Function.Periodic (deriv (fun y' => f (x, y'))) Ly := periodic_deriv fun u => hy x u
    have h2 : Function.Periodic (deriv (deriv (fun y' => f (x, y')))) Ly := periodic_deriv h1
    have h3 : (fun x' => f (x', y + Ly)) = fun x' => f (x', y) := funext fun x' => hy x' y
    simp only []
    rw [h3]
    congr 1
    exact h2 y

end VcoefDevices

end HRTorus.LLL
