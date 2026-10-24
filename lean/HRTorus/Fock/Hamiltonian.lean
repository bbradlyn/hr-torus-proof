import HRTorus.Fock.Physical
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The hollow-core Hamiltonian as an operator on the physical Fock space (T-0056 block A, `Fock.Hamiltonian`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **The definitions and statements were written
first and reviewed against the paper (phase (a)) and are unchanged; phase (b) added the proofs and the proof
devices, each section of which is marked as such. Two theorems are still `sorry`: `Vcoef_latticeSum` (the
lattice-sum form) and `HN_posSemidef` (carried to block C).** The paper: the HR paper, `papers/hr/sections/02-setting.tex`, §2.4 —
Definition 2.7 `def:hamiltonian` with (2.6) `eq:Vabcd` and (2.7) `eq:HN`, its equivalent lattice-sum form, and the
paragraph after it (self-adjoint, sector-preserving, even, invariant under global spin rotations, commuting with
`Θ`, `H_N ≥ 0`). Nothing of §4 is stated.

## The model

* `V_{abcd}` is **defined by the integrals (2.6)** over the fundamental domain `[0, L_x) × [0, L_y)` (Lebesgue
  measure on `ℝ × ℝ`, Mathlib's Bochner integral), with `ψ_j = SlotFrame.psi T j`; `∇²` is written out as
  `∂_x² + ∂_y²` of the product `\overline{ψ_a} ψ_c`, each `∂` Mathlib's one-variable `deriv` (`lap`). The lattice
  sum is a stated theorem (`Vcoef_latticeSum`, a `HasSum`, which includes the convergence).
* `H_N` is the operator (2.7) on `𝓗_N`, a finite sum of products of the `c_{jσ}` of `Fock.Physical`.
-/

open MeasureTheory
open scoped InnerProductSpace Real Matrix ComplexOrder
open Complex (I)

noncomputable section

namespace HRTorus.Fock

open HRTorus.SlotFrame HRTorus.LLL
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op IsEven)

variable (T : Torus)

/-- "`$\nabla^2=\partial_x^2+\partial_y^2$`" on functions `ℝ² → ℂ`, by iterated one-variable derivatives. -/
def lap (g : ℝ × ℝ → ℂ) (r : ℝ × ℝ) : ℂ :=
  deriv (fun x : ℝ => deriv (fun x' : ℝ => g (x', r.2)) x) r.1 +
    deriv (fun y : ℝ => deriv (fun y' : ℝ => g (r.1, y')) y) r.2

/-- The integral `∫_{𝕋_N} g dr` of a periodic function, over the fundamental domain `[0, L_x) × [0, L_y)`. -/
def torusIntegral (g : ℝ × ℝ → ℂ) : ℂ :=
  ∫ r in fundDom T, g r

/-- The pair density `\overline{ψ_a} ψ_c`, "`smooth on $\Tor_N$ by \eqref{eq:bc}`". -/
def pairDensity (a c : ZMod T.Nφ) (r : ℝ × ℝ) : ℂ :=
  star (psi T a r) * psi T c r

/-- **Definition 2.7**, (2.6):
"`V_{abcd}:=4\pi\int_{\Tor_N}\overline{\psi_a}\psi_c\,\overline{\psi_b}\psi_d\,\dd r+4\pi\int_{\Tor_N}\overline{\psi_b}\psi_d\,\nabla^2\bigl(\overline{\psi_a}\psi_c\bigr)\,\dd r`". -/
def Vcoef (a b c d : ZMod T.Nφ) : ℂ :=
  4 * π * torusIntegral T (fun r => pairDensity T a c r * pairDensity T b d r) +
    4 * π * torusIntegral T (fun r => pairDensity T b d r * lap (pairDensity T a c) r)

/-- **Definition 2.7**, (2.7): "`H_N:=\frac12\sum_{\sigma,\sigma'\in\{\up,\dn\}}\ \sum_{a,b,c,d\in\Z_{\Nphi}}V_{abcd}\;
c_{a\sigma}^*c_{b\sigma'}^*c_{d\sigma'}c_{c\sigma}`" on `𝓗_N`. -/
def HN : FockOp T :=
  (1 / 2 : ℂ) • ∑ σ : Spin, ∑ σ' : Spin, ∑ a : ZMod T.Nφ, ∑ b : ZMod T.Nφ, ∑ c : ZMod T.Nφ, ∑ d : ZMod T.Nφ,
    Vcoef T a b c d • ((cjs T a σ)ᴴ * (cjs T b σ')ᴴ * cjs T d σ' * cjs T c σ)

/-- The Fourier coefficient on the torus: "`\hat f(q):=\int_{\Tor_N}f(r)e^{-\iu q\cdot r}\,\dd r`". -/
def torusFourier (g : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  torusIntegral T fun r => g r * Complex.exp (-(I * ((q.1 * r.1 + q.2 * r.2 : ℝ) : ℂ)))

/-- The point `q = (2πp/L_x, 2πk/L_y)` of the dual lattice `(2π/L_x)ℤ × (2π/L_y)ℤ`. -/
def dualPt (pk : ℤ × ℤ) : ℝ × ℝ :=
  (2 * π * (pk.1 : ℝ) / T.Lx, 2 * π * (pk.2 : ℝ) / T.Ly)

/-! ### Proof devices for the statements of §2.4 (phase (b); not statements of the paper) -/

section HamDevices

open HRTorus.Fermion.Pilot.JW (c c_anticomm c_anticomm_star)

theorem c_mul_self (μ : Modes T) : c μ * c μ = (0 : FockOp T) := by
  have h := c_anticomm μ μ
  rw [← two_smul ℂ] at h
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

/-- `[n_ν, c_μ] = −δ_{νμ} c_μ`. -/
theorem n_mul_c (ν μ : Modes T) :
    (c ν)ᴴ * c ν * c μ = c μ * ((c ν)ᴴ * c ν) - (if ν = μ then (1 : ℂ) else 0) • c μ := by
  by_cases h : ν = μ
  · subst h
    have h2 : c ν * (c ν)ᴴ = 1 - (c ν)ᴴ * c ν := eq_sub_of_add_eq (by simpa using c_anticomm_star ν ν)
    rw [ite_eq_left rfl, one_smul, mul_assoc, c_mul_self, mul_zero, ← mul_assoc, h2, sub_mul, one_mul, mul_assoc,
      c_mul_self, mul_zero, sub_zero]
    simp
  · have h1 : c ν * c μ = -(c μ * c ν) := eq_neg_of_add_eq_zero_left (c_anticomm ν μ)
    have h2 : (c ν)ᴴ * c μ = -(c μ * (c ν)ᴴ) := by
      have := c_anticomm_star μ ν
      rw [if_neg (Ne.symm h)] at this
      exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact this)
    rw [if_neg h, zero_smul, sub_zero, mul_assoc, h1, mul_neg, ← mul_assoc, h2, neg_mul, neg_neg, mul_assoc]

/-- `N_τ c_μ = c_μ (N_τ − [μ.2 = τ])`. -/
theorem Nsig_mul_c (τ : Spin) (μ : Modes T) :
    Nsig T τ * c μ = c μ * (Nsig T τ - (if μ.2 = τ then (1 : ℂ) else 0) • 1) := by
  have hN : Nsig T τ = ∑ k : ZMod T.Nφ, (c (k, τ))ᴴ * c (k, τ) := by
    rw [Nsig]; exact Finset.sum_congr rfl fun k _ => by rw [njs, cjs_eq]
  rw [hN, Finset.sum_mul, mul_sub, Finset.mul_sum]
  simp_rw [n_mul_c]
  rw [Finset.sum_sub_distrib, mul_smul_comm, mul_one, ← Finset.sum_smul]
  congr 2
  rcases μ with ⟨j, σ⟩
  by_cases hs : σ = τ
  · subst hs
    simp only [ite_true]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Prod.ext_iff, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [hs, ite_false]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [Prod.ext_iff, Ne.symm hs]

/-- `N_τ c_μ^* = c_μ^* (N_τ + [μ.2 = τ])`. -/
theorem Nsig_mul_cdag (τ : Spin) (μ : Modes T) :
    Nsig T τ * (c μ)ᴴ = (c μ)ᴴ * (Nsig T τ + (if μ.2 = τ then (1 : ℂ) else 0) • 1) := by
  have h := congrArg Matrix.conjTranspose (Nsig_mul_c T τ μ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Nsig_conjTranspose,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one] at h
  have e : star (if μ.2 = τ then (1 : ℂ) else 0) = if μ.2 = τ then 1 else 0 := by split_ifs <;> simp
  rw [e] at h
  -- h : (c μ)ᴴ * N = (N - e • 1) * (c μ)ᴴ
  rw [mul_add, mul_smul_comm, mul_one, h, sub_mul, smul_mul_assoc, one_mul, sub_add_cancel]

theorem prod_shift (A Y1 Y2 : FockOp T) (e1 e2 : ℂ) (h1 : A * Y1 = Y1 * (A + e1 • 1))
    (h2 : A * Y2 = Y2 * (A + e2 • 1)) : A * (Y1 * Y2) = (Y1 * Y2) * (A + (e1 + e2) • 1) := by
  calc A * (Y1 * Y2) = (A * Y1) * Y2 := (mul_assoc _ _ _).symm
    _ = Y1 * (A + e1 • 1) * Y2 := by rw [h1]
    _ = Y1 * (A * Y2 + e1 • Y2) := by rw [mul_assoc, add_mul, smul_mul_assoc, one_mul]
    _ = Y1 * (Y2 * (A + e2 • 1) + e1 • Y2) := by rw [h2]
    _ = Y1 * Y2 * (A + (e1 + e2) • 1) := by
      simp only [mul_add, add_smul, mul_smul_comm, mul_one, mul_assoc]
      abel

theorem Nsig_commute_monomial (τ : Spin) (a b c' d : ZMod T.Nφ) (σ σ' : Spin) :
    Commute (Nsig T τ) ((cjs T a σ)ᴴ * (cjs T b σ')ᴴ * cjs T d σ' * cjs T c' σ) := by
  rw [cjs_eq, cjs_eq, cjs_eq, cjs_eq]
  have hc : ∀ μ : Modes T, Nsig T τ * c μ = c μ * (Nsig T τ + (-(if μ.2 = τ then (1 : ℂ) else 0)) • 1) := by
    intro μ; rw [Nsig_mul_c, neg_smul, sub_eq_add_neg]
  have h := prod_shift T _ _ _ _ _ (prod_shift T _ _ _ _ _ (prod_shift T _ _ _ _ _ (Nsig_mul_cdag T τ (a, σ))
    (Nsig_mul_cdag T τ (b, σ'))) (hc (d, σ'))) (hc (c', σ))
  show Nsig T τ * ((c (a, σ))ᴴ * (c (b, σ'))ᴴ * c (d, σ') * c (c', σ)) =
    (c (a, σ))ᴴ * (c (b, σ'))ᴴ * c (d, σ') * c (c', σ) * Nsig T τ
  rw [h]
  congr 1
  simp only []
  have : ((if σ = τ then (1 : ℂ) else 0) + (if σ' = τ then 1 else 0) + -(if σ' = τ then 1 else 0) +
      -(if σ = τ then 1 else 0)) = 0 := by ring
  rw [this, zero_smul, add_zero]

end HamDevices


section HamDevices2

theorem lap_star (g : ℝ × ℝ → ℂ) (r : ℝ × ℝ) : lap (fun r => star (g r)) r = star (lap g r) := by
  simp only [lap, deriv.star, star_add]

theorem pairDensity_star (a c : ZMod T.Nφ) : (fun r => star (pairDensity T c a r)) = pairDensity T a c := by
  funext r
  simp only [pairDensity, star_mul', star_star]
  ring

theorem pairDensity_star_apply (a c : ZMod T.Nφ) (r : ℝ × ℝ) :
    pairDensity T a c r = star (pairDensity T c a r) := by
  rw [← congrFun (pairDensity_star T a c) r]

theorem sum4_swap {Z M : Type*} [Fintype Z] [AddCommMonoid M] (f : Z → Z → Z → Z → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f c d a b = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f c d a b = ∑ a, ∑ c, ∑ b, ∑ d, f c d a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f c d a b := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f c d a b :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f c d a b := Finset.sum_congr rfl fun c _ => Finset.sum_comm

end HamDevices2


/-- **Definition 2.7**, the equivalent form "by Parseval's identity on `𝕋_N`":
"`V_{abcd}=\frac1{\abs{\Tor_N}}\sum_{q\in\frac{2\pi}{L_x}\Z\times\frac{2\pi}{L_y}\Z}4\pi\bigl(1-\abs q^2\bigr)\,
\widehat{\overline{\psi_a}\psi_c}(-q)\,\widehat{\overline{\psi_b}\psi_d}(q),\qquad\hat f(q):=\int_{\Tor_N}f(r)e^{-\iu q\cdot r}\,\dd r`"
(`|𝕋_N| = L_x L_y`; a `HasSum` over `(p, k) ∈ ℤ²`). -/
theorem Vcoef_latticeSum (a b c d : ZMod T.Nφ) :
    HasSum (fun pk : ℤ × ℤ =>
        ((1 / (T.Lx * T.Ly) : ℝ) : ℂ) *
          ((4 * π * (1 - ((dualPt T pk).1 ^ 2 + (dualPt T pk).2 ^ 2)) : ℝ) : ℂ) *
          torusFourier T (pairDensity T a c) (-dualPt T pk) * torusFourier T (pairDensity T b d) (dualPt T pk))
      (Vcoef T a b c d) := by
  sorry

/-! ## The statements of §2.4 about `H_N` -/

/-- **§2.4**: "`The operator $H_N$ is self-adjoint, since $V_{abcd}=\overline{V_{cdab}}$`" — the symmetry of the
coefficients. -/
theorem Vcoef_eq_star (a b c d : ZMod T.Nφ) : Vcoef T a b c d = star (Vcoef T c d a b) := by
  simp only [Vcoef, torusIntegral, star_add, star_mul']
  have h4 : star (4 : ℂ) * star (π : ℂ) = 4 * π := by simp [Complex.conj_ofReal]
  rw [h4]
  congr 2
  · rw [Complex.star_def, ← integral_conj]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [← Complex.star_def, star_mul']
    rw [pairDensity_star_apply T a c, pairDensity_star_apply T b d]
  · rw [Complex.star_def, ← integral_conj]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [← Complex.star_def, star_mul']
    rw [pairDensity_star_apply T b d, ← pairDensity_star T a c, lap_star]

/-- **§2.4**: "`The operator $H_N$ is self-adjoint`". -/
theorem HN_isSelfAdjoint : IsSelfAdjoint (HN T) := by
  show star (HN T) = HN T
  rw [HN, star_smul, star_sum]
  have h12 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h12]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  simp only [star_sum, star_smul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  rw [← sum4_swap]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Vcoef_eq_star T a b c d]
  simp only [mul_assoc]

/-- **§2.4**: "`and it is sector-preserving, even, and invariant under global spin rotations`" — sector-preserving. -/
theorem HN_isSectorPreserving : IsSectorPreserving T (HN T) := by
  have key : ∀ τ : Spin, Commute (HN T) (Nsig T τ) := by
    intro τ
    refine Commute.smul_left ?_ _
    refine Commute.sum_left _ _ _ fun σ _ => Commute.sum_left _ _ _ fun σ' _ =>
      Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ =>
      Commute.sum_left _ _ _ fun c _ => Commute.sum_left _ _ _ fun d _ => ?_
    exact ((Nsig_commute_monomial T τ a b c d σ σ').symm).smul_left _
  exact ⟨key .up, key .dn⟩

/-- **§2.4**: "`and it is sector-preserving, even`" — even. -/
theorem HN_isEven : IsEven (HN T) := by
  exact IsSectorPreserving.isEven T (HN_isSectorPreserving T)

/-! ### Proof devices for the global spin rotation (phase (b); not statements of the paper) -/

section HamDevices3

theorem spinU_unitary {u : Matrix Spin Spin ℂ} (hu : u ∈ Matrix.specialUnitaryGroup Spin ℂ) :
    Matrix.kronecker (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) u ∈ unitary (Matrix (Modes T) (Modes T) ℂ) := by
  have hu' : u ∈ unitary (Matrix Spin Spin ℂ) := (Matrix.mem_specialUnitaryGroup_iff.mp hu).1
  have h1 : uᴴ * u = 1 := conjTranspose_mul_self_of_mem_unitary hu'
  have hk : (Matrix.kronecker (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) u)ᴴ *
      Matrix.kronecker (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) u = 1 := by
    show (Matrix.kroneckerMap (· * ·) (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) u)ᴴ *
      Matrix.kroneckerMap (· * ·) (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) u = 1
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one, Matrix.one_mul, h1]
    exact Matrix.one_kronecker_one
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
  exact ⟨hk, mul_eq_one_comm.mp hk⟩

theorem spinU_spinTensor (u : Matrix Spin Spin ℂ) (j : ZMod T.Nφ) (σ : Spin) :
    Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) (Matrix.kronecker (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) u)
      (spinTensor (orb T j) σ) = ∑ τ, u τ σ • spinTensor (orb T j) τ := by
  refine PiLp.ext fun μ => ?_
  rcases μ with ⟨k, ρ⟩
  rw [Matrix.ofLp_toEuclideanCLM]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    spinTensor, orb, WithLp.ofLp_toLp, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, PiLp.single_apply]
  by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

theorem Ff_spin_cjs {u : Matrix Spin Spin ℂ} (hu : u ∈ Matrix.specialUnitaryGroup Spin ℂ) (j : ZMod T.Nφ)
    (σ : Spin) :
    Ff T (Matrix.kronecker (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) u) * cjs T j σ *
        (Ff T (Matrix.kronecker (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) u))ᴴ =
      ∑ τ, star (u τ σ) • cjs T j τ := by
  rw [cjs, Ff_conj_cf T (spinU_unitary T hu), spinU_spinTensor]
  have hadd : ∀ g : Spin → Space2 T, cf T (∑ τ, g τ) = ∑ τ, cf T (g τ) :=
    fun g => map_sum (AddMonoidHom.mk' (cf T) (cf_add T)) g Finset.univ
  rw [hadd]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [cf_smul]
  rfl

theorem conj_mul4 (W A B C D : FockOp T) (hW : Wᴴ * W = 1) :
    W * (A * B * C * D) * Wᴴ = (W * A * Wᴴ) * (W * B * Wᴴ) * (W * C * Wᴴ) * (W * D * Wᴴ) := by
  have e : ∀ X Y : FockOp T, W * (X * Y) * Wᴴ = (W * X * Wᴴ) * (W * Y * Wᴴ) := by
    intro X Y
    calc W * (X * Y) * Wᴴ = W * X * (Wᴴ * W) * Y * Wᴴ := by rw [hW, mul_one]; simp only [mul_assoc]
      _ = (W * X * Wᴴ) * (W * Y * Wᴴ) := by simp only [mul_assoc]
  rw [e, e, e]

theorem spin_pair_contract (u : Matrix Spin Spin ℂ) (h : u * uᴴ = 1) (X Y : Spin → FockOp T) (M : FockOp T) :
    ∑ σ : Spin, (∑ τ, u τ σ • X τ) * M * (∑ τ, star (u τ σ) • Y τ) = ∑ τ, X τ * M * Y τ := by
  have e1 : ∀ σ : Spin, (∑ τ, u τ σ • X τ) * M * (∑ τ, star (u τ σ) • Y τ) =
      ∑ τ, ∑ τ', (u τ σ * star (u τ' σ)) • (X τ * M * Y τ') := by
    intro σ
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ' _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp_rw [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm]
  have e2 : ∀ τ' : Spin, ∑ σ : Spin, (u τ σ * star (u τ' σ)) • (X τ * M * Y τ') =
      (if τ = τ' then (1 : ℂ) else 0) • (X τ * M * Y τ') := by
    intro τ'
    rw [← Finset.sum_smul]
    congr 1
    have := congrFun (congrFun h τ) τ'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [Matrix.conjTranspose_apply] using this
  simp_rw [e2]
  simp

theorem sum_mid (P S : FockOp T) (Q R : Spin → FockOp T) :
    ∑ σ' : Spin, P * Q σ' * R σ' * S = P * (∑ σ', Q σ' * 1 * R σ') * S := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  simp only [mul_one, mul_assoc]

theorem spin_sum_identity (u : Matrix Spin Spin ℂ) (h : u * uᴴ = 1) (A B C D : Spin → FockOp T) :
    ∑ σ : Spin, ∑ σ' : Spin, (∑ τ, u τ σ • A τ) * (∑ τ, u τ σ' • B τ) * (∑ τ, star (u τ σ') • C τ) *
        (∑ τ, star (u τ σ) • D τ) = ∑ σ : Spin, ∑ σ' : Spin, A σ * B σ' * C σ' * D σ := by
  have e : ∀ σ : Spin, ∑ σ' : Spin, (∑ τ, u τ σ • A τ) * (∑ τ, u τ σ' • B τ) * (∑ τ, star (u τ σ') • C τ) *
        (∑ τ, star (u τ σ) • D τ) =
      (∑ τ, u τ σ • A τ) * (∑ τ, B τ * 1 * C τ) * (∑ τ, star (u τ σ) • D τ) := by
    intro σ
    rw [← spin_pair_contract T u h B C 1]
    exact sum_mid T _ _ (fun σ' => ∑ τ, u τ σ' • B τ) (fun σ' => ∑ τ, star (u τ σ') • C τ)
  calc _ = ∑ σ : Spin, (∑ τ, u τ σ • A τ) * (∑ τ, B τ * 1 * C τ) * (∑ τ, star (u τ σ) • D τ) :=
        Finset.sum_congr rfl fun σ _ => e σ
    _ = ∑ τ, A τ * (∑ τ, B τ * 1 * C τ) * D τ := spin_pair_contract T u h A D _
    _ = _ := Finset.sum_congr rfl fun σ _ => (sum_mid T (A σ) (D σ) B C).symm

theorem sum_comm4_dev {X Z M : Type*} [Fintype X] [Fintype Z] [AddCommMonoid M] (g : X → Z → Z → Z → Z → M) :
    ∑ x, ∑ a, ∑ b, ∑ c, ∑ d, g x a b c d = ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, g x a b c d := by
  calc ∑ x, ∑ a, ∑ b, ∑ c, ∑ d, g x a b c d = ∑ a, ∑ x, ∑ b, ∑ c, ∑ d, g x a b c d := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ x, ∑ c, ∑ d, g x a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ x, ∑ d, g x a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, g x a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
          Finset.sum_comm

/-- `H_N` with the spin sums innermost. -/
theorem HN_eq_alt : HN T = (1 / 2 : ℂ) • ∑ a : ZMod T.Nφ, ∑ b : ZMod T.Nφ, ∑ c : ZMod T.Nφ, ∑ d : ZMod T.Nφ,
    Vcoef T a b c d • ∑ σ : Spin, ∑ σ' : Spin, ((cjs T a σ)ᴴ * (cjs T b σ')ᴴ * cjs T d σ' * cjs T c σ) := by
  rw [HN]
  congr 1
  simp only [Finset.smul_sum]
  calc _ = ∑ σ : Spin, ∑ a : ZMod T.Nφ, ∑ b : ZMod T.Nφ, ∑ c : ZMod T.Nφ, ∑ d : ZMod T.Nφ, ∑ σ' : Spin,
        Vcoef T a b c d • ((cjs T a σ)ᴴ * (cjs T b σ')ᴴ * cjs T d σ' * cjs T c σ) :=
        Finset.sum_congr rfl fun σ _ => sum_comm4_dev (fun σ' a b c d =>
          Vcoef T a b c d • ((cjs T a σ)ᴴ * (cjs T b σ')ᴴ * cjs T d σ' * cjs T c σ))
    _ = _ := sum_comm4_dev (fun σ a b c d => ∑ σ' : Spin,
          Vcoef T a b c d • ((cjs T a σ)ᴴ * (cjs T b σ')ᴴ * cjs T d σ' * cjs T c σ))

end HamDevices3


/-- **§2.4**: "`invariant under global spin rotations`": `𝔉(1 ⊗ u) H_N 𝔉(1 ⊗ u)^* = H_N` for `u ∈ SU(2)`. -/
theorem HN_spinRotation {u : Matrix Spin Spin ℂ} (hu : u ∈ Matrix.specialUnitaryGroup Spin ℂ) :
    Ff T (Matrix.kronecker (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) u) * HN T *
        (Ff T (Matrix.kronecker (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) u))ᴴ = HN T := by
  set W := Ff T (Matrix.kronecker (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) u) with hWdef
  have hWu : W ∈ unitary (FockOp T) := Ff_mem_unitary T (spinU_unitary T hu)
  have hW : Wᴴ * W = 1 := conjTranspose_mul_self_of_mem_unitary hWu
  have huu : u * uᴴ = 1 := mul_conjTranspose_self_of_mem_unitary (Matrix.mem_specialUnitaryGroup_iff.mp hu).1
  have hc : ∀ j σ, W * cjs T j σ * Wᴴ = ∑ τ, star (u τ σ) • cjs T j τ := fun j σ => Ff_spin_cjs T hu j σ
  have hcd : ∀ j σ, W * (cjs T j σ)ᴴ * Wᴴ = ∑ τ, u τ σ • (cjs T j τ)ᴴ := by
    intro j σ
    have := congrArg Matrix.conjTranspose (hc j σ)
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, mul_assoc] using this
  rw [HN_eq_alt, Matrix.mul_smul, Matrix.smul_mul]
  refine congrArg (fun X => (1 / 2 : ℂ) • X) ?_
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  refine congrArg (fun X => Vcoef T a b c d • X) ?_
  simp only [conj_mul4 T W _ _ _ _ hW, hc, hcd]
  exact spin_sum_identity T u huu (fun τ => (cjs T a τ)ᴴ) (fun τ => (cjs T b τ)ᴴ) (fun τ => cjs T d τ)
    (fun τ => cjs T c τ)

/-! ### Proof devices for `[Θ, H_N] = 0` (phase (b); not statements of the paper): the coefficient identity
`V_{a+1,b+1,c+1,d+1} = V_{abcd}` from the orbitals' covariance `θ_x ψ_j = ψ_{j+1}` -/

section HamDevices4

theorem star_exp_mul_self (a b : ℝ) :
    star (Complex.exp (I * (a : ℂ) * (b : ℂ))) * Complex.exp (I * (a : ℂ) * (b : ℂ)) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) (I * (a : ℂ) * (b : ℂ)) + I * (a : ℂ) * (b : ℂ) = 0 := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [h, Complex.exp_zero]

/-- The pair density of the translated orbitals: `\overline{ψ_{a+1}} ψ_{c+1}(x, y) = \overline{ψ_a} ψ_c(x − κ, y)`
(from `θ_x ψ_j = ψ_{j+1}`, `thxFun_psi`, and `|e^{iκy}| = 1`). -/
theorem pairDensity_succ (a c : ZMod T.Nφ) (r : ℝ × ℝ) :
    pairDensity T (a + 1) (c + 1) r = pairDensity T a c (r.1 - T.κ, r.2) := by
  have ha := congrFun (thxFun_psi T a) r
  have hc := congrFun (thxFun_psi T c) r
  simp only [thxFun] at ha hc
  rw [pairDensity, pairDensity, ← ha, ← hc, star_mul']
  calc star (Complex.exp (I * (T.κ : ℂ) * (r.2 : ℂ))) * star (psi T a (r.1 - T.κ, r.2)) *
        (Complex.exp (I * (T.κ : ℂ) * (r.2 : ℂ)) * psi T c (r.1 - T.κ, r.2))
      = (star (Complex.exp (I * (T.κ : ℂ) * (r.2 : ℂ))) * Complex.exp (I * (T.κ : ℂ) * (r.2 : ℂ))) *
        (star (psi T a (r.1 - T.κ, r.2)) * psi T c (r.1 - T.κ, r.2)) := by ring
    _ = star (psi T a (r.1 - T.κ, r.2)) * psi T c (r.1 - T.κ, r.2) := by rw [star_exp_mul_self, one_mul]

/-- The pair density is `L_x`-periodic in `x` (from `ψ_j(x + L_x, y) = e^{iL_x y} ψ_j(x, y)`). -/
theorem pairDensity_add_Lx (a c : ZMod T.Nφ) (x y : ℝ) :
    pairDensity T a c (x + T.Lx, y) = pairDensity T a c (x, y) := by
  rw [pairDensity, pairDensity, psi_add_Lx, psi_add_Lx, star_mul']
  calc star (Complex.exp (I * (T.Lx : ℂ) * (y : ℂ))) * star (psi T a (x, y)) *
        (Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * psi T c (x, y))
      = (star (Complex.exp (I * (T.Lx : ℂ) * (y : ℂ))) * Complex.exp (I * (T.Lx : ℂ) * (y : ℂ))) *
        (star (psi T a (x, y)) * psi T c (x, y)) := by ring
    _ = star (psi T a (x, y)) * psi T c (x, y) := by rw [star_exp_mul_self, one_mul]

/-- `∇²` commutes with the translation `x ↦ x − s` (no differentiability needed: `deriv_comp_sub_const`). -/
theorem lap_shift (g : ℝ × ℝ → ℂ) (s : ℝ) (r : ℝ × ℝ) :
    lap (fun r => g (r.1 - s, r.2)) r = lap g (r.1 - s, r.2) := by
  simp only [lap]
  congr 1
  have e1 : (fun x : ℝ => deriv (fun x' : ℝ => g (x' - s, r.2)) x) =
      fun x : ℝ => deriv (fun x' : ℝ => g (x', r.2)) (x - s) :=
    funext fun x => deriv_comp_sub_const (fun x' : ℝ => g (x', r.2)) s x
  rw [e1]
  exact deriv_comp_sub_const (fun x : ℝ => deriv (fun x' : ℝ => g (x', r.2)) x) s r.1

/-- `∇²` of a `p`-periodic function (in `x`) is `p`-periodic. -/
theorem lap_periodic (g : ℝ × ℝ → ℂ) (p : ℝ) (hg : ∀ x y, g (x + p, y) = g (x, y)) (x y : ℝ) :
    lap g (x + p, y) = lap g (x, y) := by
  simp only [lap]
  have h2 : (fun y' : ℝ => g (x + p, y')) = fun y' => g (x, y') := funext fun y' => hg x y'
  have hG : ∀ x : ℝ, deriv (fun x' : ℝ => g (x', y)) (x + p) = deriv (fun x' : ℝ => g (x', y)) x := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun F => deriv F x) (funext fun x' => hg x' y)
  have hF : ∀ x : ℝ, deriv (fun x₁ : ℝ => deriv (fun x' : ℝ => g (x', y)) x₁) (x + p) =
      deriv (fun x₁ : ℝ => deriv (fun x' : ℝ => g (x', y)) x₁) x := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun F => deriv F x) (funext fun x₁ => hG x₁)
  rw [hF, h2]

/-- The strip `[a, a + L_x) × ℝ` is a fundamental domain for the translations by `L_x ℤ × {0}`. -/
theorem strip_fd (a : ℝ) : IsAddFundamentalDomain (AddSubgroup.zmultiples ((T.Lx, 0) : ℝ × ℝ))
    (Set.Ico a (a + T.Lx) ×ˢ (Set.univ : Set ℝ)) volume := by
  refine IsAddFundamentalDomain.mk' (measurableSet_Ico.prod MeasurableSet.univ).nullMeasurableSet fun r => ?_
  have hinj : Function.Injective (fun n : ℤ => n • ((T.Lx, 0) : ℝ × ℝ)) := by
    intro m n h
    have h1 : m • T.Lx = n • T.Lx := congrArg Prod.fst h
    rw [zsmul_eq_mul, zsmul_eq_mul] at h1
    exact_mod_cast mul_right_cancel₀ T.Lx_pos.ne' h1
  have hb : Function.Bijective (Set.codRestrict (fun n : ℤ => n • ((T.Lx, 0) : ℝ × ℝ))
      (AddSubgroup.zmultiples ((T.Lx, 0) : ℝ × ℝ)) _) :=
    (Equiv.ofInjective (fun n : ℤ => n • ((T.Lx, 0) : ℝ × ℝ)) hinj).bijective
  refine hb.existsUnique_iff.2 ?_
  have key : ∀ n : ℤ, (n • ((T.Lx, 0) : ℝ × ℝ) + r ∈ Set.Ico a (a + T.Lx) ×ˢ (Set.univ : Set ℝ)) ↔
      r.1 + n • T.Lx ∈ Set.Ico a (a + T.Lx) := by
    intro n
    simp only [Set.mem_prod, Set.mem_univ, and_true, Prod.fst_add, Prod.smul_fst]
    rw [add_comm (n • T.Lx) r.1]
  exact (existsUnique_congr key).2 (existsUnique_add_zsmul_mem_Ico T.Lx_pos r.1 a)

/-- The integral over `𝕋_N` of an `L_x`-periodic (in `x`) function is invariant under `x ↦ x − s`. -/
theorem torusIntegral_shift (F : ℝ × ℝ → ℂ) (hF : ∀ x y, F (x + T.Lx, y) = F (x, y)) (s : ℝ) :
    torusIntegral T (fun r => F (r.1 - s, r.2)) = torusIntegral T F := by
  have : Countable (AddSubgroup.zmultiples ((T.Lx, 0) : ℝ × ℝ)) := by
    have hs : Function.Surjective (fun n : ℤ => (⟨n • ((T.Lx, 0) : ℝ × ℝ), AddSubgroup.zsmul_mem_zmultiples _ n⟩ :
        AddSubgroup.zmultiples ((T.Lx, 0) : ℝ × ℝ))) := by
      rintro ⟨g, hg⟩
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
      exact ⟨n, rfl⟩
    exact hs.countable
  have : (volume : Measure (ℝ × ℝ)).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : (volume : Measure (ℝ × ℝ)).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : VAddInvariantMeasure (AddSubgroup.zmultiples ((T.Lx, 0) : ℝ × ℝ)) (ℝ × ℝ) volume :=
    ⟨fun g A _ => measure_preimage_add volume (g : ℝ × ℝ) A⟩
  have hmeasB : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Set.Ico 0 T.Ly) := MeasurableSet.univ.prod measurableSet_Ico
  have hdom : fundDom T = (Set.Ico 0 (0 + T.Lx) ×ˢ (Set.univ : Set ℝ)) ∩ ((Set.univ : Set ℝ) ×ˢ Set.Ico 0 T.Ly) := by
    ext r
    simp only [fundDom, Set.mem_prod, Set.mem_inter_iff, Set.mem_univ, zero_add, true_and, and_true]
  have e0 : ∀ r : ℝ × ℝ, r + (-s, 0) = (r.1 - s, r.2) := fun r => by
    ext
    · simp [sub_eq_add_neg]
    · simp
  have hR : torusIntegral T F = ∫ r in Set.Ico 0 (0 + T.Lx) ×ˢ (Set.univ : Set ℝ),
      ((Set.univ : Set ℝ) ×ˢ Set.Ico 0 T.Ly).indicator F r := by
    rw [torusIntegral, setIntegral_indicator hmeasB, ← hdom]
  have hL : torusIntegral T (fun r => F (r.1 - s, r.2)) = ∫ r in Set.Ico 0 (0 + T.Lx) ×ˢ (Set.univ : Set ℝ),
      ((Set.univ : Set ℝ) ×ˢ Set.Ico 0 T.Ly).indicator F (r + (-s, 0)) := by
    have e : (fun r : ℝ × ℝ => ((Set.univ : Set ℝ) ×ˢ Set.Ico 0 T.Ly).indicator F (r + (-s, 0))) =
        ((Set.univ : Set ℝ) ×ˢ Set.Ico 0 T.Ly).indicator (fun r => F (r.1 - s, r.2)) := by
      funext r
      rw [e0]
      simp only [Set.indicator, Set.mem_prod, Set.mem_univ, true_and]
    rw [e, torusIntegral, setIntegral_indicator hmeasB, ← hdom]
  have hpre : (fun r : ℝ × ℝ => r + (-s, 0)) ⁻¹' (Set.Ico (-s) (-s + T.Lx) ×ˢ (Set.univ : Set ℝ)) =
      Set.Ico 0 (0 + T.Lx) ×ˢ (Set.univ : Set ℝ) := by
    ext r
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true, Prod.fst_add]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have h2 : ∫ r in Set.Ico 0 (0 + T.Lx) ×ˢ (Set.univ : Set ℝ),
        ((Set.univ : Set ℝ) ×ˢ Set.Ico 0 T.Ly).indicator F (r + (-s, 0)) =
      ∫ r in Set.Ico (-s) (-s + T.Lx) ×ˢ (Set.univ : Set ℝ), ((Set.univ : Set ℝ) ×ˢ Set.Ico 0 T.Ly).indicator F r := by
    rw [← hpre]
    exact (measurePreserving_add_right volume ((-s, 0) : ℝ × ℝ)).setIntegral_preimage_emb
      (measurableEmbedding_addRight _) _ _
  have hinv : ∀ (g : AddSubgroup.zmultiples ((T.Lx, 0) : ℝ × ℝ)) (r : ℝ × ℝ),
      ((Set.univ : Set ℝ) ×ˢ Set.Ico 0 T.Ly).indicator F (g +ᵥ r) =
        ((Set.univ : Set ℝ) ×ˢ Set.Ico 0 T.Ly).indicator F r := by
    rintro ⟨g, hg⟩ r
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
    show ((Set.univ : Set ℝ) ×ˢ Set.Ico 0 T.Ly).indicator F (n • ((T.Lx, 0) : ℝ × ℝ) + r) = _
    have e1 : n • ((T.Lx, 0) : ℝ × ℝ) + r = (r.1 + n • T.Lx, r.2) := by
      ext
      · simp [add_comm]
      · simp
    have hpn : ∀ x y, F (x + n • T.Lx, y) = F (x, y) := fun x y =>
      (show Function.Periodic (fun x => F (x, y)) T.Lx from fun x => hF x y).zsmul n x
    rw [e1]
    simp only [Set.indicator, Set.mem_prod, Set.mem_univ, true_and]
    rw [hpn]
  have h3 := (strip_fd T (-s)).setIntegral_eq (strip_fd T 0) hinv
  rw [hL, h2, h3, hR]

theorem Vcoef_shift (a b c d : ZMod T.Nφ) : Vcoef T (a + 1) (b + 1) (c + 1) (d + 1) = Vcoef T a b c d := by
  have e1 : (fun r => pairDensity T (a + 1) (c + 1) r * pairDensity T (b + 1) (d + 1) r) =
      fun r => pairDensity T a c (r.1 - T.κ, r.2) * pairDensity T b d (r.1 - T.κ, r.2) := by
    funext r
    rw [pairDensity_succ, pairDensity_succ]
  have e2 : (fun r => pairDensity T (b + 1) (d + 1) r * lap (pairDensity T (a + 1) (c + 1)) r) =
      fun r => pairDensity T b d (r.1 - T.κ, r.2) * lap (pairDensity T a c) (r.1 - T.κ, r.2) := by
    funext r
    have hP : pairDensity T (a + 1) (c + 1) = fun r => pairDensity T a c (r.1 - T.κ, r.2) :=
      funext fun r => pairDensity_succ T a c r
    rw [hP, lap_shift (pairDensity T a c) T.κ r, pairDensity_succ]
  have hp1 : ∀ x y, pairDensity T a c (x + T.Lx, y) * pairDensity T b d (x + T.Lx, y) =
      pairDensity T a c (x, y) * pairDensity T b d (x, y) := fun x y => by
    rw [pairDensity_add_Lx, pairDensity_add_Lx]
  have hp2 : ∀ x y, pairDensity T b d (x + T.Lx, y) * lap (pairDensity T a c) (x + T.Lx, y) =
      pairDensity T b d (x, y) * lap (pairDensity T a c) (x, y) := fun x y => by
    rw [pairDensity_add_Lx, lap_periodic _ _ (pairDensity_add_Lx T a c)]
  rw [Vcoef, Vcoef, e1, e2,
    torusIntegral_shift T (fun r => pairDensity T a c r * pairDensity T b d r) hp1 T.κ,
    torusIntegral_shift T (fun r => pairDensity T b d r * lap (pairDensity T a c) r) hp2 T.κ]

theorem sum4_shift {M : Type*} [AddCommMonoid M] (f : ZMod T.Nφ → ZMod T.Nφ → ZMod T.Nφ → ZMod T.Nφ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f (a + 1) (b + 1) (c + 1) (d + 1) = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := by
  have e : ∀ g : ZMod T.Nφ → M, ∑ a, g (a + 1) = ∑ a, g a := fun g =>
    Equiv.sum_comp (Equiv.addRight (1 : ZMod T.Nφ)) g
  rw [e (fun a => ∑ b, ∑ c, ∑ d, f a (b + 1) (c + 1) (d + 1))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [e (fun b => ∑ c, ∑ d, f a b (c + 1) (d + 1))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [e (fun c => ∑ d, f a b c (d + 1))]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact e (fun d => f a b c d)

theorem conj_mul4' (W A B C D : FockOp T) (hW : W * Wᴴ = 1) :
    Wᴴ * (A * B * C * D) * W = (Wᴴ * A * W) * (Wᴴ * B * W) * (Wᴴ * C * W) * (Wᴴ * D * W) := by
  have e : ∀ X Y : FockOp T, Wᴴ * (X * Y) * W = (Wᴴ * X * W) * (Wᴴ * Y * W) := by
    intro X Y
    calc Wᴴ * (X * Y) * W = Wᴴ * X * (W * Wᴴ) * Y * W := by rw [hW, mul_one]; simp only [mul_assoc]
      _ = (Wᴴ * X * W) * (Wᴴ * Y * W) := by simp only [mul_assoc]
  rw [e, e, e]

end HamDevices4


/-- **§2.4**: "`It commutes with $\Theta$ (Lemma~\ref{lem:covariance})`" — `[Θ, H_N] = 0`. -/
theorem HN_commute_Θ : Commute (Θ T) (HN T) := by
  have hU : Θ T ∈ unitary (FockOp T) := Θ_mem_unitary T
  have h2 : Θ T * (Θ T)ᴴ = 1 := mul_conjTranspose_self_of_mem_unitary hU
  have hc : ∀ j σ, (Θ T)ᴴ * cjs T j σ * Θ T = cjs T (j + 1) σ := Θ_conj_cjs T
  have hcd : ∀ j σ, (Θ T)ᴴ * (cjs T j σ)ᴴ * Θ T = (cjs T (j + 1) σ)ᴴ := by
    intro j σ
    have := congrArg Matrix.conjTranspose (hc j σ)
    simpa [Matrix.conjTranspose_mul, mul_assoc] using this
  have key : (Θ T)ᴴ * HN T * Θ T = HN T := by
    rw [HN, Matrix.mul_smul, Matrix.smul_mul]
    refine congrArg (fun X => (1 / 2 : ℂ) • X) ?_
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    simp only [conj_mul4' T (Θ T) _ _ _ _ h2, hc, hcd]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
    rw [← sum4_shift T (fun a b c d => Vcoef T a b c d • ((cjs T a σ)ᴴ * (cjs T b σ')ᴴ * cjs T d σ' * cjs T c σ))]
    simp only [Vcoef_shift]
  show Θ T * HN T = HN T * Θ T
  calc Θ T * HN T = Θ T * ((Θ T)ᴴ * HN T * Θ T) := by rw [key]
    _ = HN T * Θ T := by rw [← mul_assoc, ← mul_assoc, h2, one_mul]

/-- **§2.4**: "`in particular $H_N\ge0$`" (the paper derives it from Theorem 4.2(a), §4). -/
theorem HN_posSemidef : (HN T).PosSemidef := by
  sorry

/-- The fields of `HRTorus.IndexCore.Orbital` that concern `H` (`H_sa`, `Psec_H`, `Θ_H`), for `H = H_N`, the sector
projection `Π^𝐧` and `Θ`, on `𝓗_N`; with `orbitalFit_spin`, `orbitalFit_total` (`Fock.Physical`) these are the
orbital and Hamiltonian fields of `Orbital` for the hollow-core model. -/
theorem HN_orbitalFit (nn : SectorLabel T) :
    IsSelfAdjoint (toCLM T (HN T)) ∧ Commute (toCLM T (Psec T nn)) (toCLM T (HN T)) ∧
      Commute (toCLM T (Θ T)) (toCLM T (HN T)) := by
  refine ⟨toCLM_isSelfAdjoint T ?_, ?_, ?_⟩
  · have := HN_isSelfAdjoint T
    rwa [IsSelfAdjoint, Matrix.star_eq_conjTranspose] at this
  · exact (((isSectorPreserving_iff_commute T _).mp (HN_isSectorPreserving T) nn).symm).map _
  · exact (HN_commute_Θ T).map _

end HRTorus.Fock
