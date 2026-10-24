import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.PID
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Algebra.Polynomial

/-!
# The determinant lemmas — Lemma A.9 and `det_P`

Written by Claude Opus 5.5 (an AI model), 2026-10-23. The HR paper's Lemma A.9
(`papers/hr/appendices/A-bbdf.tex`, "determinants and integers", the reproduction of
BBDF's determinant lemma), in the form its use in Lemma 6.17's proof
(`sections/06-index-theorem.tex`) needs. **Every theorem in this file is proved; there are no
proof gaps.** Everything is parametrized by the projection and the operators; nothing
depends on `Setting`, and `Statement.lean` is not imported (the conventions are the same: `E` a
finite-dimensional complex inner product space with `[CompleteSpace E]`, operators `E →L[ℂ] E`,
`star` the adjoint, `⁅A, B⁆ = A * B - B * A`, `IsStarProjection P`, `p = finrank (range P)`).

## Contents and correspondence with Lemma A.9

* §1 Hadamard's inequality: `norm_det_le_one_of_col` (matrices whose columns have norm `≤ 1`),
  `norm_basis_det_le_prod_norm` (`|det_b(v_1, …, v_n)| ≤ ∏ ‖v_j‖` in an orthonormal basis `b`),
  `norm_det_le_pow_of_le`, `norm_det_le_norm_pow` (`|det A| ≤ ‖A‖^p`). Not in Mathlib for complex
  matrices (Mathlib has the real volume-form version `Orientation.abs_volumeForm_apply_le`).
* §2 **Lemma A.9(i)**: `norm_det_sub_det_le_of_norm_le_one` (the paper's statement), with the
  radius-`r` form `norm_det_sub_det_le_of_norm_le` and the pointwise core `norm_det_sub_det_le`.
* §3 `det (exp A) = exp (tr A)` for every operator on a finite-dimensional complex inner product
  space: `det_exp` (a TODO in Mathlib's `MatrixExponential.lean`).
* §4 `det_P`: `detP P X := det (P X P|_{ran P})`, total in `X`; `detP_eq_det_restrict` (for `X`
  mapping `ran P` into itself it is `LinearMap.det` of `LinearMap.restrict`); **(i) on `ran P`**:
  `norm_detP_sub_detP_le_of_norm_le_one`, `norm_detP_sub_detP_le`; **(ii)**: `detP_exp`
  (`det_P (e^X) = e^{Tr (P X)}` for `[X, P] = 0`, any `X`), `detP_mul` (multiplicativity);
  **(iii)**:
  `compress_star_mul_compress_sub` (the identity) and `norm_detP_star_mul_detP_sub_one_le` (the
  bound); the Hadamard-type bounds `norm_detP_le_pow`, `norm_detP_le_one`.
* §5 **Lemma A.9(iv)**: `four_mul_infDist_int_le` (the paper's `|e^{2πix} - 1| ≥ 4 dist(x, ℤ)`),
  `four_mul_abs_sub_round_le`, `exists_int_abs_sub_le`.

## Names

The lemmas of Lemma A.9 and `det_P` are in the namespace `HRTorus.IndexCore`; generic helpers that another
file of the formalization might also state (the identity of a projection on its range, `‖P Z P‖ ≤ ‖Z‖`,
`‖V‖ ≤ 1` for unitary `V`, the two analytic steps of §3, …) are in `HRTorus.IndexCore.Det`, so that
importing this file beside the other files of `HRTorus/IndexCore/` cannot clash.

## Two design notes

* `detP P X` is defined for every `X` as the determinant of the compression `P X P` restricted to
  `ran P` (the paper's formula, read literally), so that no proof argument sits inside the
  definition; `detP_eq_det_restrict` gives the restriction of `X` itself when `X` preserves `ran P`.
* The analysis is never done on the subspace `K = ran P`: for a submodule `K`, Mathlib's
  operator-norm topology on `K →L[ℂ] K` is not definitionally its `ContinuousLinearMap` topology, so
  `NormedSpace.exp` on `K →L[ℂ] K` does not elaborate (`IsTopologicalRing` fails to synthesize).
  Lemma A.9(ii) is therefore proved by running the one-parameter-group argument of §3 for
  `z ↦ det_P (exp (z X))` on `E →L[ℂ] E` itself (`hasDerivAt_detP_exp_smul_zero`, `detP_exp`).
-/

open scoped InnerProductSpace ComplexConjugate Real ComplexOrder Topology
open Complex (I)
open Module Filter Asymptotics

noncomputable section

namespace HRTorus.IndexCore

/-! ## 1. Hadamard's inequality -/

section Hadamard

/-- **The light Hadamard inequality.** A complex square matrix whose columns have Euclidean norm
at most one has determinant of modulus at most one. Proof: `|det M|² = det (Mᴴ M)`, the product of
the eigenvalues `λ_i ≥ 0` of the positive matrix `Mᴴ M`, whose sum `tr (Mᴴ M) = ∑ ‖columns‖²` is at
most `n`; and `∏ λ_i ≤ ∏ e^{λ_i - 1} = e^{∑ λ_i - n} ≤ 1` (AM–GM in the form `λ ≤ e^{λ - 1}`). -/
theorem norm_det_le_one_of_col {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (hM : ∀ j, ∑ i, ‖M i j‖ ^ 2 ≤ 1) : ‖M.det‖ ≤ 1 := by
  have hpsd : (M.conjTranspose * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hH : (M.conjTranspose * M).IsHermitian := hpsd.1
  have hev0 : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hpsd.eigenvalues_nonneg i
  -- `det (Mᴴ M) = ‖det M‖²`
  have hprod : ‖M.det‖ ^ 2 = ∏ i, hH.eigenvalues i := by
    have h1 := hH.det_eq_prod_eigenvalues
    rw [Matrix.det_mul, Matrix.det_conjTranspose, RCLike.star_def, RCLike.conj_mul] at h1
    exact_mod_cast h1
  -- `tr (Mᴴ M) = ∑ ‖columns‖²`
  have hsum : ∑ i, hH.eigenvalues i = ∑ j, ∑ i, ‖M i j‖ ^ 2 := by
    have h1 := hH.trace_eq_sum_eigenvalues
    have h2 : (M.conjTranspose * M).trace = ∑ j, ∑ i, conj (M i j) * M i j := by
      rw [Matrix.trace]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.diag_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.conjTranspose_apply, RCLike.star_def]
    rw [h2] at h1
    simp only [RCLike.conj_mul] at h1
    exact_mod_cast h1.symm
  have hsum_le : ∑ i, hH.eigenvalues i ≤ Fintype.card n := by
    rw [hsum]
    calc ∑ j, ∑ i, ‖M i j‖ ^ 2 ≤ ∑ _j : n, (1 : ℝ) := Finset.sum_le_sum fun j _ => hM j
      _ = Fintype.card n := by simp
  have hprod_le : ∏ i, hH.eigenvalues i ≤ 1 := by
    calc ∏ i, hH.eigenvalues i ≤ ∏ i, Real.exp (hH.eigenvalues i - 1) :=
          Finset.prod_le_prod₀ (fun i _ => hev0 i) fun i _ => by
            linarith [Real.add_one_le_exp (hH.eigenvalues i - 1)]
      _ = Real.exp (∑ i, (hH.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
      _ ≤ 1 := by
          rw [Real.exp_le_one_iff, Finset.sum_sub_distrib]
          simpa using hsum_le
  have h0 : 0 ≤ ‖M.det‖ := norm_nonneg _
  nlinarith [hprod, hprod_le]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The light Hadamard inequality for the determinant in an orthonormal basis: vectors of norm
at most one have `|det_b(v)| ≤ 1`. -/
theorem norm_basis_det_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ F) (v : ι → F) (hv : ∀ j, ‖v j‖ ≤ 1) :
    ‖b.toBasis.det v‖ ≤ 1 := by
  rw [Module.Basis.det_apply]
  refine norm_det_le_one_of_col _ fun j => ?_
  simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  rw [b.sum_sq_norm_inner_right]
  exact pow_le_one₀ (norm_nonneg _) (hv j)

/-- **Hadamard's inequality** for the determinant in an orthonormal basis of a complex inner
product space: `|det_b(v_1, …, v_n)| ≤ ∏_j ‖v_j‖`. (For a matrix this is `|det M| ≤ ∏` of the
Euclidean norms of its columns.) Proof: the light form after scaling each column to norm one. -/
theorem norm_basis_det_le_prod_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ F) (v : ι → F) :
    ‖b.toBasis.det v‖ ≤ ∏ j, ‖v j‖ := by
  by_cases h : ∃ j, v j = 0
  · obtain ⟨j, hj⟩ := h
    rw [b.toBasis.det.map_coord_zero j hj, norm_zero]
    exact Finset.prod_nonneg fun j _ => norm_nonneg _
  · simp only [not_exists] at h
    have hpos : ∀ j, 0 < ‖v j‖ := fun j => norm_pos_iff.2 (h j)
    have hne : ∀ j, (‖v j‖ : ℂ) ≠ 0 := fun j => by exact_mod_cast (hpos j).ne'
    have key : b.toBasis.det v =
        (∏ j, (‖v j‖ : ℂ)) • b.toBasis.det (fun j => (‖v j‖ : ℂ)⁻¹ • v j) := by
      rw [← AlternatingMap.map_smul_univ]
      congr 1
      funext j
      rw [smul_smul, mul_inv_cancel₀ (hne j), one_smul]
    have hw : ∀ j, ‖(‖v j‖ : ℂ)⁻¹ • v j‖ ≤ 1 := fun j => by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (hpos j).ne']
    rw [key, norm_smul, norm_prod]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    calc (∏ j, ‖v j‖) * ‖b.toBasis.det (fun j => (‖v j‖ : ℂ)⁻¹ • v j)‖
        ≤ (∏ j, ‖v j‖) * 1 := by
          gcongr
          exact norm_basis_det_le_one b _ hw
      _ = ∏ j, ‖v j‖ := mul_one _

/-- The determinant of a linear map is the determinant, in any orthonormal basis `b`, of the images
of the basis vectors. -/
theorem Det.det_eq_basis_det {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ F)
    (f : F →ₗ[ℂ] F) : LinearMap.det f = b.toBasis.det (f ∘ b) := by
  have h := b.toBasis.det_comp f b.toBasis
  rw [Module.Basis.det_self, mul_one, OrthonormalBasis.coe_toBasis] at h
  exact h.symm

variable [FiniteDimensional ℂ F]

/-- The Hadamard-type bound for a linear map: if `‖A v‖ ≤ r ‖v‖` for all `v`, then
`|det A| ≤ r^p` with `p = dim F`. -/
theorem norm_det_le_pow_of_le (A : F →ₗ[ℂ] F) {r : ℝ}
    (hA : ∀ v, ‖A v‖ ≤ r * ‖v‖) : ‖LinearMap.det A‖ ≤ r ^ finrank ℂ F := by
  let b := stdOrthonormalBasis ℂ F
  rw [Det.det_eq_basis_det b A]
  calc ‖b.toBasis.det (A ∘ b)‖ ≤ ∏ j, ‖A (b j)‖ := norm_basis_det_le_prod_norm b _
    _ ≤ ∏ _j : Fin (finrank ℂ F), r := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          fun j _ => by simpa [b.orthonormal.1 j] using hA (b j)
    _ = r ^ finrank ℂ F := by simp

/-- The Hadamard-type bound, operator form: `|det A| ≤ ‖A‖^p`. -/
theorem norm_det_le_norm_pow (A : F →L[ℂ] F) :
    ‖LinearMap.det (A : F →ₗ[ℂ] F)‖ ≤ ‖A‖ ^ finrank ℂ F :=
  norm_det_le_pow_of_le _ fun v => A.le_opNorm v

end Hadamard

/-! ## 2. Lemma A.9(i): the determinant is Lipschitz on contractions -/

section Lipschitz

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Lemma A.9(i), quantitative core** (pointwise form, any radius `r`): if `A`, `B` are bounded
by `r` and `A - B` by `δ` on a `p`-dimensional complex inner product space, then
`|det A - det B| ≤ p r^{p-1} δ`. Proof: the determinant in an orthonormal basis is multilinear in
the images of the basis vectors and bounded by `∏ ‖v_j‖` (Hadamard); the telescoping over the
columns is Mathlib's `MultilinearMap.norm_image_sub_le_of_bound`. -/
theorem norm_det_sub_det_le (A B : F →ₗ[ℂ] F) {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hA : ∀ v, ‖A v‖ ≤ r * ‖v‖) (hB : ∀ v, ‖B v‖ ≤ r * ‖v‖)
    (hAB : ∀ v, ‖A v - B v‖ ≤ δ * ‖v‖) :
    ‖LinearMap.det A - LinearMap.det B‖ ≤ finrank ℂ F * r ^ (finrank ℂ F - 1) * δ := by
  let b := stdOrthonormalBasis ℂ F
  have hb : ∀ j, ‖b j‖ = 1 := b.orthonormal.1
  have hbound := MultilinearMap.norm_image_sub_le_of_bound b.toBasis.det.toMultilinearMap
    zero_le_one (fun m => by simpa using norm_basis_det_le_prod_norm b m) (A ∘ b) (B ∘ b)
  have h1 : ‖(A ∘ b : Fin (finrank ℂ F) → F)‖ ≤ r :=
    (pi_norm_le_iff_of_nonneg hr).2 fun j => by simpa [hb j] using hA (b j)
  have h2 : ‖(B ∘ b : Fin (finrank ℂ F) → F)‖ ≤ r :=
    (pi_norm_le_iff_of_nonneg hr).2 fun j => by simpa [hb j] using hB (b j)
  have h3 : ‖(A ∘ b : Fin (finrank ℂ F) → F) - B ∘ b‖ ≤ δ :=
    (pi_norm_le_iff_of_nonneg hδ).2 fun j => by simpa [hb j] using hAB (b j)
  rw [Det.det_eq_basis_det b A, Det.det_eq_basis_det b B]
  calc ‖b.toBasis.det (A ∘ b) - b.toBasis.det (B ∘ b)‖
      ≤ 1 * Fintype.card (Fin (finrank ℂ F)) *
          max ‖(A ∘ b : Fin (finrank ℂ F) → F)‖ ‖(B ∘ b : Fin (finrank ℂ F) → F)‖ ^
            (Fintype.card (Fin (finrank ℂ F)) - 1) * ‖(A ∘ b : Fin (finrank ℂ F) → F) - B ∘ b‖ :=
        hbound
    _ ≤ 1 * Fintype.card (Fin (finrank ℂ F)) * r ^ (Fintype.card (Fin (finrank ℂ F)) - 1) * δ := by
        gcongr
        exact max_le h1 h2
    _ = finrank ℂ F * r ^ (finrank ℂ F - 1) * δ := by simp

/-- **Lemma A.9(i)** with a radius: for operators of norm at most `r` on a `p`-dimensional complex
inner product space, `|det A - det B| ≤ p r^{p-1} ‖A - B‖`. -/
theorem norm_det_sub_det_le_of_norm_le (A B : F →L[ℂ] F) {r : ℝ} (hA : ‖A‖ ≤ r)
    (hB : ‖B‖ ≤ r) :
    ‖LinearMap.det (A : F →ₗ[ℂ] F) - LinearMap.det (B : F →ₗ[ℂ] F)‖ ≤
      finrank ℂ F * r ^ (finrank ℂ F - 1) * ‖A - B‖ :=
  norm_det_sub_det_le _ _ ((norm_nonneg _).trans hA) (norm_nonneg _)
    (fun v => (A.le_opNorm v).trans (by gcongr)) (fun v => (B.le_opNorm v).trans (by gcongr))
    (fun v => (A - B).le_opNorm v)

/-- **Lemma A.9(i)**, the paper's statement: if `A` and `B` act on a `p`-dimensional space and
`‖A‖, ‖B‖ ≤ 1`, then `|det A - det B| ≤ p ‖A - B‖`. -/
theorem norm_det_sub_det_le_of_norm_le_one (A B : F →L[ℂ] F) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖LinearMap.det (A : F →ₗ[ℂ] F) - LinearMap.det (B : F →ₗ[ℂ] F)‖ ≤ finrank ℂ F * ‖A - B‖ := by
  simpa using norm_det_sub_det_le_of_norm_le A B hA hB

end Lipschitz

/-! ## 3. `det (exp A) = exp (tr A)` on a finite-dimensional complex inner product space

Mathlib lists this as a TODO (`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`). The proof
here: `f(z) := det (exp (z A))` satisfies `f(z + w) = f(z) f(w)` and `f'(0) = tr A` (from
`det (1 + z A) = 1 + z tr A + O(z²)` and the Lipschitz bound of §2), hence `f' = f · tr A`, so
`f(z) e^{-z tr A}` has derivative zero and is constant. The two analytic steps are stated
abstractly (`Det.eq_cexp_of_add_mul`, `Det.hasDerivAt_zero_of_expansion`) so that §4 reuses them for
`det_P` without doing analysis on the subspace `ran P`. -/

section DetExp

/-- **The one-parameter-group step.** If `f : ℂ → ℂ` satisfies `f 0 = 1`,
`f (z + w) = f z · f w` and `f'(0) = t`, then `f 1 = e^t`. -/
theorem Det.eq_cexp_of_add_mul {f : ℂ → ℂ} {t : ℂ} (hf0 : f 0 = 1)
    (hmul : ∀ z w, f (z + w) = f z * f w) (hd0 : HasDerivAt f t 0) : f 1 = Complex.exp t := by
  have hd : ∀ z, HasDerivAt f (f z * t) z := by
    intro z
    have h1 : HasDerivAt (fun w => f (w - z)) t z := by
      apply HasDerivAt.comp_sub_const
      rwa [sub_self]
    have h2 := h1.const_mul (f z)
    have h3 : (fun w => f z * f (w - z)) = f := by
      funext w
      rw [← hmul, add_sub_cancel]
    rwa [h3] at h2
  have hg : ∀ z, HasDerivAt (fun z => f z * Complex.exp (-(z * t))) 0 z := by
    intro z
    have h1 : HasDerivAt (fun z : ℂ => -(z * t)) (-(1 * t)) z :=
      ((hasDerivAt_id' z).mul_const t).neg
    have h2 := (hd z).mul h1.cexp
    convert h2 using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (fun z => (hg z).differentiableAt)
    (fun z => (hg z).deriv) 1 0
  simp only [hf0, zero_mul, neg_zero, Complex.exp_zero, mul_one, one_mul] at hconst
  have h := congrArg (· * Complex.exp t) hconst
  simp only [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one,
    one_mul] at h
  exact h

/-- **The derivative step.** If `f 0 = 1` and, near `0`, `f z` differs from
`1 + t z + q(z) z²` (`q` a polynomial) by at most `C ‖e z‖` with `e z = o(z)`, then `f'(0) = t`. -/
theorem Det.hasDerivAt_zero_of_expansion {G : Type*} [NormedAddCommGroup G] {f : ℂ → ℂ} {t : ℂ}
    (q : Polynomial ℂ) {e : ℂ → G} {C : ℝ} (hf0 : f 0 = 1) (he : e =o[𝓝 0] fun z => z)
    (hbound : ∀ᶠ z in 𝓝 (0 : ℂ), ‖f z - (1 + t * z + q.eval z * z ^ 2)‖ ≤ C * ‖e z‖) :
    HasDerivAt f t 0 := by
  have hterm1 : (fun z : ℂ => f z - (1 + t * z + q.eval z * z ^ 2)) =o[𝓝 0] fun z => z :=
    (IsBigO.of_bound C hbound).trans_isLittleO he
  have hterm2 : (fun z : ℂ => q.eval z * z ^ 2) =o[𝓝 0] fun z => z := by
    have h1 : (fun z : ℂ => q.eval z) =O[𝓝 0] fun _ => (1 : ℂ) :=
      (q.continuous.tendsto 0).isBigO_one ℂ
    have h2 : (fun z : ℂ => z ^ 2) =o[𝓝 0] fun z => z := isLittleO_pow_id one_lt_two
    simpa using h1.mul_isLittleO h2
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine (hterm1.add hterm2).congr_left fun z => ?_
  rw [zero_add, hf0, smul_eq_mul]
  ring

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- `exp (z A) - 1 - z A = o(z)`. -/
theorem Det.isLittleO_exp_smul_sub_one_sub (A : 𝔸) :
    (fun z : ℂ => NormedSpace.exp (z • A) - 1 - z • A) =o[𝓝 0] fun z => z := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) A 0
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at h
  simpa using h

/-- Near `0`, `‖exp (z A)‖ < ‖1‖ + 1`. -/
theorem Det.eventually_norm_exp_smul_lt (A : 𝔸) :
    ∀ᶠ z in 𝓝 (0 : ℂ), ‖NormedSpace.exp (z • A)‖ < ‖(1 : 𝔸)‖ + 1 := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) A 0).continuousAt.norm).tendsto
  simp only [zero_smul, NormedSpace.exp_zero] at h
  exact h.eventually_lt_const (lt_add_one _)

omit [CompleteSpace 𝔸] in
/-- Near `0`, `‖1 + z A‖ < ‖1‖ + 1`. -/
theorem Det.eventually_norm_one_add_smul_lt (A : 𝔸) :
    ∀ᶠ z in 𝓝 (0 : ℂ), ‖1 + z • A‖ < ‖(1 : 𝔸)‖ + 1 := by
  have hcont : Continuous fun z : ℂ => (1 : 𝔸) + z • A := by fun_prop
  have h := (hcont.tendsto 0).norm
  simp only [zero_smul, add_zero] at h
  exact h.eventually_lt_const (lt_add_one _)

end Algebra

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- `det (1 + z A) = 1 + z tr A + q(z) z²` for a polynomial `q` (Mathlib's `Matrix.det_one_add_smul`
transported to linear maps). -/
theorem exists_det_one_add_smul (A : F →ₗ[ℂ] F) :
    ∃ q : Polynomial ℂ, ∀ z : ℂ,
      LinearMap.det (1 + z • A) = 1 + LinearMap.trace ℂ F A * z + q.eval z * z ^ 2 := by
  let b := Module.finBasis ℂ F
  refine ⟨(Matrix.det (1 + (Polynomial.X : Polynomial ℂ) •
    (LinearMap.toMatrix b b A).map Polynomial.C)).divX.divX, fun z => ?_⟩
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_one, map_smul,
    Matrix.det_one_add_smul, LinearMap.trace_eq_matrix_trace ℂ b]

/-- The derivative of `z ↦ det (exp (z A))` at `0` is `tr A`. -/
theorem hasDerivAt_det_exp_smul_zero (A : F →L[ℂ] F) :
    HasDerivAt (fun z : ℂ => LinearMap.det ((NormedSpace.exp (z • A) : F →L[ℂ] F) : F →ₗ[ℂ] F))
      (LinearMap.trace ℂ F (A : F →ₗ[ℂ] F)) 0 := by
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  obtain ⟨q, hq⟩ := exists_det_one_add_smul (A : F →ₗ[ℂ] F)
  refine Det.hasDerivAt_zero_of_expansion q
    (C := finrank ℂ F * (‖(1 : F →L[ℂ] F)‖ + 1) ^ (finrank ℂ F - 1)) ?_
    (Det.isLittleO_exp_smul_sub_one_sub A) ?_
  · simp only [zero_smul, NormedSpace.exp_zero]
    exact map_one _
  · filter_upwards [Det.eventually_norm_exp_smul_lt A, Det.eventually_norm_one_add_smul_lt A]
      with z h1 h2
    have hcoe : (((1 : F →L[ℂ] F) + z • A : F →L[ℂ] F) : F →ₗ[ℂ] F) =
        1 + z • (A : F →ₗ[ℂ] F) := rfl
    rw [← hq z, ← hcoe, ← sub_add_eq_sub_sub]
    exact norm_det_sub_det_le_of_norm_le _ _ h1.le h2.le

/-- **`det (exp A) = exp (tr A)`** for every operator `A` on a finite-dimensional complex inner
product space (the general form of Lemma A.9(ii) before restriction to `ran P`). -/
theorem det_exp (A : F →L[ℂ] F) :
    LinearMap.det ((NormedSpace.exp A : F →L[ℂ] F) : F →ₗ[ℂ] F) =
      Complex.exp (LinearMap.trace ℂ F (A : F →ₗ[ℂ] F)) := by
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  let _ : NormedAlgebra ℚ (F →L[ℂ] F) := NormedAlgebra.restrictScalars ℚ ℂ (F →L[ℂ] F)
  have h := Det.eq_cexp_of_add_mul
    (f := fun z : ℂ => LinearMap.det ((NormedSpace.exp (z • A) : F →L[ℂ] F) : F →ₗ[ℂ] F))
    ?_ ?_ (hasDerivAt_det_exp_smul_zero A)
  · simpa using h
  · simp only [zero_smul, NormedSpace.exp_zero]
    exact map_one _
  · intro z w
    rw [add_smul, NormedSpace.exp_add_of_commute (((Commute.refl A).smul_left z).smul_right w),
      ContinuousLinearMap.toLinearMap_mul, map_mul]

end DetExp

/-! ## 4. The determinant on the range of a projection, `det_P`, and Lemma A.9(i)–(iii) on `ran P`

For a projection `P` the paper writes `det_P X := det (P X P|_{ran P})` (§6.4, used for `X` with
`[X, P] = 0`, or for compressions `X = P Y P`). Here `detP P X` is that determinant for every `X`:
`P X P` maps `E` into `ran P = LinearMap.range P`, so its restriction to `ran P` is always defined;
for `X` mapping `ran P` into itself it equals the determinant of the restriction of `X` itself
(`detP_eq_det_restrict`). -/

section DetP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `P X P` maps every vector into `ran P`. -/
theorem Det.compress_mem_range (P X : E →L[ℂ] E) (v : E) :
    (P * X * P : E →L[ℂ] E) v ∈ LinearMap.range (P : E →ₗ[ℂ] E) :=
  LinearMap.mem_range.2 ⟨X (P v), rfl⟩

/-- **`det_P X := det (P X P|_{ran P})`** (§6.4 of the paper; Lemma A.9). -/
def detP (P X : E →L[ℂ] E) : ℂ :=
  LinearMap.det (((P * X * P : E →L[ℂ] E) : E →ₗ[ℂ] E).restrict
    (p := LinearMap.range (P : E →ₗ[ℂ] E)) (q := LinearMap.range (P : E →ₗ[ℂ] E))
    fun v _ => Det.compress_mem_range P X v)

/-- An operator commuting with `P` maps `ran P` into itself. -/
theorem Det.mapsTo_range_of_commute {P X : E →L[ℂ] E} (hX : Commute X P) :
    ∀ v ∈ LinearMap.range (P : E →ₗ[ℂ] E), X v ∈ LinearMap.range (P : E →ₗ[ℂ] E) := by
  intro v hv
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
  exact LinearMap.mem_range.2 ⟨X u, congrArg (fun T : E →L[ℂ] E => T u) hX.eq.symm⟩

/-- `det_P` is multiplicative whenever the right factor maps `ran P` into itself (no condition on
the left factor, and no condition on `P`): the algebra of Lemma A.9(ii), second half. -/
theorem detP_mul_of_mapsTo' (P X Y : E →L[ℂ] E)
    (hP : ∀ v ∈ LinearMap.range (P : E →ₗ[ℂ] E), P v = v)
    (hY : ∀ v ∈ LinearMap.range (P : E →ₗ[ℂ] E), Y v ∈ LinearMap.range (P : E →ₗ[ℂ] E)) :
    detP P (X * Y) = detP P X * detP P Y := by
  unfold detP
  rw [← LinearMap.det_comp]
  congr 1
  refine LinearMap.ext fun w => Subtype.ext ?_
  show P (X (Y (P w))) = P (X (P (P (Y (P w)))))
  have hw : P w = w := hP _ w.2
  have hYw : P (Y w) = Y w := hP _ (hY _ w.2)
  rw [hw, hYw, hYw]

variable [CompleteSpace E] {P : E →L[ℂ] E}

/-- A projection acts as the identity on its range. -/
theorem Det.starProj_apply_of_mem (hP : IsStarProjection P) {v : E}
    (hv : v ∈ LinearMap.range (P : E →ₗ[ℂ] E)) : P v = v := by
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
  exact congrArg (fun T : E →L[ℂ] E => T u) hP.isIdempotentElem.eq

/-- For `X` mapping `ran P` into itself, `det_P X` is the determinant of the restriction of `X`
to `ran P` (`LinearMap.det` of `LinearMap.restrict`). -/
theorem detP_eq_det_restrict (hP : IsStarProjection P) (X : E →L[ℂ] E)
    (hX : ∀ v ∈ LinearMap.range (P : E →ₗ[ℂ] E), X v ∈ LinearMap.range (P : E →ₗ[ℂ] E)) :
    detP P X = LinearMap.det ((X : E →ₗ[ℂ] E).restrict hX) := by
  unfold detP
  congr 1
  refine LinearMap.ext fun w => Subtype.ext ?_
  show P (X (P w)) = X w
  rw [Det.starProj_apply_of_mem hP w.2, Det.starProj_apply_of_mem hP (hX _ w.2)]

/-- `det_P` sees only the compression: `det_P (P X P) = det_P X`. -/
theorem detP_compress (hP : IsStarProjection P) (X : E →L[ℂ] E) :
    detP P (P * X * P) = detP P X := by
  have hPP : ∀ v, P (P v) = P v := fun v =>
    Det.starProj_apply_of_mem hP (LinearMap.mem_range_self _ v)
  unfold detP
  congr 1
  refine LinearMap.ext fun w => Subtype.ext ?_
  show P (P (X (P (P w)))) = P (X (P w))
  simp only [hPP]

/-- `det_P 1 = 1`. -/
theorem detP_one (hP : IsStarProjection P) : detP P 1 = 1 := by
  rw [detP_eq_det_restrict hP 1 fun v hv => hv]
  have h : ((1 : E →L[ℂ] E) : E →ₗ[ℂ] E).restrict
      (p := LinearMap.range (P : E →ₗ[ℂ] E)) (q := LinearMap.range (P : E →ₗ[ℂ] E))
      (fun v hv => hv) = 1 :=
    LinearMap.ext fun w => rfl
  rw [h, map_one]

/-- **Multiplicativity of `det_P`** (Lemma A.9(ii), second half), in the generality the proof
gives: `det_P (X Y) = det_P X · det_P Y` whenever `Y` maps `ran P` into itself (no condition on
`X`). -/
theorem detP_mul_of_mapsTo (hP : IsStarProjection P) (X Y : E →L[ℂ] E)
    (hY : ∀ v ∈ LinearMap.range (P : E →ₗ[ℂ] E), Y v ∈ LinearMap.range (P : E →ₗ[ℂ] E)) :
    detP P (X * Y) = detP P X * detP P Y :=
  detP_mul_of_mapsTo' P X Y (fun _ hv => Det.starProj_apply_of_mem hP hv) hY

/-- **Lemma A.9(ii), second half**, the paper's form: `det_P (X Y) = det_P X · det_P Y` when
`[Y, P] = 0` (the paper assumes also `[X, P] = 0`, which the proof does not use). -/
theorem detP_mul (hP : IsStarProjection P) (X : E →L[ℂ] E) {Y : E →L[ℂ] E} (hY : Commute Y P) :
    detP P (X * Y) = detP P X * detP P Y :=
  detP_mul_of_mapsTo hP X Y (Det.mapsTo_range_of_commute hY)

/-- Multiplicativity for a product of compressions (the form of Lemma 6.17(i), Step 3):
`det_P ((P X P)(P Y P)) = det_P X · det_P Y`, for any `X`, `Y`. -/
theorem detP_compress_mul_compress (hP : IsStarProjection P) (X Y : E →L[ℂ] E) :
    detP P (P * X * P * (P * Y * P)) = detP P X * detP P Y := by
  rw [detP_mul_of_mapsTo hP _ _ fun v _ => Det.compress_mem_range P Y v, detP_compress hP,
    detP_compress hP]

/-- The compression by a star projection is a contraction: `‖P Z P‖ ≤ ‖Z‖`. -/
theorem Det.norm_compress_le (hP : IsStarProjection P) (Z : E →L[ℂ] E) : ‖P * Z * P‖ ≤ ‖Z‖ := by
  have hP1 : ‖P‖ ≤ 1 := IsStarProjection.norm_le P hP
  calc ‖P * Z * P‖ ≤ ‖P * Z‖ * ‖P‖ := norm_mul_le _ _
    _ ≤ (‖P‖ * ‖Z‖) * ‖P‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ (1 * ‖Z‖) * 1 := by gcongr
    _ = ‖Z‖ := by ring

/-- A unitary operator is a contraction. -/
theorem Det.norm_le_one_of_mem_unitary {V : E →L[ℂ] E} (hV : V ∈ unitary (E →L[ℂ] E)) :
    ‖V‖ ≤ 1 := by
  have h : ‖V‖ * ‖V‖ = ‖(1 : E →L[ℂ] E)‖ := by
    rw [← CStarRing.norm_star_mul_self, Unitary.star_mul_self_of_mem hV]
  have h1 : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg V]

/-- **Lemma A.9(iii)**, the identity: for unitary `V`, `P V* P V P - P = P V* [P, V] P`. -/
theorem compress_star_mul_compress_sub (hP : IsStarProjection P) {V : E →L[ℂ] E}
    (hV : V ∈ unitary (E →L[ℂ] E)) :
    P * star V * P * V * P - P = P * star V * ⁅P, V⁆ * P := by
  have h1 : star V * V = 1 := Unitary.star_mul_self_of_mem hV
  have h2 : P * P = P := hP.isIdempotentElem.eq
  have h3 : P * star V * (P * V - V * P) * P =
      P * star V * P * V * P - P * (star V * V) * (P * P) := by noncomm_ring
  rw [Ring.lie_def, h3, h1, h2, mul_one, h2]

variable [FiniteDimensional ℂ E]

omit [CompleteSpace E] in
/-- **Lemma A.9(i) on `ran P`**, refined: if `‖P X P‖, ‖P Y P‖ ≤ r`, then
`|det_P X - det_P Y| ≤ p r^{p-1} ‖P X P - P Y P‖`, with `p = rank P`. -/
theorem norm_detP_sub_detP_le {X Y : E →L[ℂ] E} {r : ℝ}
    (hX : ‖P * X * P‖ ≤ r) (hY : ‖P * Y * P‖ ≤ r) :
    ‖detP P X - detP P Y‖ ≤
      finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) *
        r ^ (finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) - 1) * ‖P * X * P - P * Y * P‖ := by
  unfold detP
  refine norm_det_sub_det_le _ _ ((norm_nonneg _).trans hX) (norm_nonneg _) ?_ ?_ ?_
  · intro w
    exact ((P * X * P).le_opNorm (w : E)).trans (mul_le_mul_of_nonneg_right hX (norm_nonneg _))
  · intro w
    exact ((P * Y * P).le_opNorm (w : E)).trans (mul_le_mul_of_nonneg_right hY (norm_nonneg _))
  · intro w
    exact (P * X * P - P * Y * P).le_opNorm (w : E)

/-- **Lemma A.9(i) on `ran P`**, the form Lemma 6.17 uses: for `‖X‖, ‖Y‖ ≤ 1`,
`|det_P X - det_P Y| ≤ p ‖X - Y‖` with `p = rank P`. -/
theorem norm_detP_sub_detP_le_of_norm_le_one (hP : IsStarProjection P) {X Y : E →L[ℂ] E}
    (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    ‖detP P X - detP P Y‖ ≤ finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) * ‖X - Y‖ := by
  have hXY : ‖P * X * P - P * Y * P‖ ≤ ‖X - Y‖ := by
    rw [← sub_mul, ← mul_sub]
    exact Det.norm_compress_le hP _
  calc ‖detP P X - detP P Y‖
      ≤ finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) *
          1 ^ (finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) - 1) * ‖P * X * P - P * Y * P‖ :=
        norm_detP_sub_detP_le ((Det.norm_compress_le hP X).trans hX)
          ((Det.norm_compress_le hP Y).trans hY)
    _ ≤ finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) * ‖X - Y‖ := by
        rw [one_pow, mul_one]
        gcongr

omit [CompleteSpace E] in
/-- The Hadamard-type bound on `ran P`: `|det_P X| ≤ ‖P X P‖^p`. -/
theorem norm_detP_le_pow (X : E →L[ℂ] E) :
    ‖detP P X‖ ≤ ‖P * X * P‖ ^ finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) := by
  unfold detP
  exact norm_det_le_pow_of_le _ fun w => (P * X * P).le_opNorm (w : E)

/-- `|det_P X| ≤ 1` for `‖X‖ ≤ 1` (used for `|d_i| ≤ 1` in Lemma 6.17(i), Step 3). -/
theorem norm_detP_le_one (hP : IsStarProjection P) {X : E →L[ℂ] E} (hX : ‖X‖ ≤ 1) :
    ‖detP P X‖ ≤ 1 :=
  (norm_detP_le_pow X).trans
    (pow_le_one₀ (norm_nonneg _) ((Det.norm_compress_le hP X).trans hX))

/-- `|det_P V| ≤ 1` for unitary `V` (`|d_i| ≤ 1` in Lemma 6.17(i), Step 3). -/
theorem norm_detP_le_one_of_mem_unitary (hP : IsStarProjection P) {V : E →L[ℂ] E}
    (hV : V ∈ unitary (E →L[ℂ] E)) : ‖detP P V‖ ≤ 1 :=
  norm_detP_le_one hP (Det.norm_le_one_of_mem_unitary hV)

/-- `det_P (1 + z X) = 1 + z Tr (P X) + q(z) z²` for `X` commuting with `P`, `q` a polynomial. -/
theorem detP_one_add_smul (hP : IsStarProjection P) {X : E →L[ℂ] E} (hX : Commute X P) :
    ∃ q : Polynomial ℂ, ∀ z : ℂ, detP P (1 + z • X) =
      1 + LinearMap.trace ℂ E ((P * X : E →L[ℂ] E) : E →ₗ[ℂ] E) * z + q.eval z * z ^ 2 := by
  set B := ((P * X * P : E →L[ℂ] E) : E →ₗ[ℂ] E).restrict
    (p := LinearMap.range (P : E →ₗ[ℂ] E)) (q := LinearMap.range (P : E →ₗ[ℂ] E))
    (fun v _ => Det.compress_mem_range P X v) with hB
  obtain ⟨q, hq⟩ := exists_det_one_add_smul B
  have htr : LinearMap.trace ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) B =
      LinearMap.trace ℂ E ((P * X : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    rw [hB, LinearMap.trace_restrict_eq_of_forall_mem _ _ (Det.compress_mem_range P X)]
    congr 2
    rw [mul_assoc, hX.eq, ← mul_assoc, hP.isIdempotentElem.eq]
  refine ⟨q, fun z => ?_⟩
  rw [← htr, ← hq z]
  unfold detP
  congr 1
  refine LinearMap.ext fun w => Subtype.ext ?_
  have hw : P w = w := Det.starProj_apply_of_mem hP w.2
  show P ((1 + z • X) (P w)) = (w : E) + z • P (X (P w))
  simp [hw]

/-- The derivative of `z ↦ det_P (exp (z X))` at `0` is `Tr (P X)`, for `X` commuting with `P`. -/
theorem hasDerivAt_detP_exp_smul_zero (hP : IsStarProjection P) {X : E →L[ℂ] E}
    (hX : Commute X P) :
    HasDerivAt (fun z : ℂ => detP P (NormedSpace.exp (z • X)))
      (LinearMap.trace ℂ E ((P * X : E →L[ℂ] E) : E →ₗ[ℂ] E)) 0 := by
  obtain ⟨q, hq⟩ := detP_one_add_smul hP hX
  refine Det.hasDerivAt_zero_of_expansion q
    (C := finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) * (‖(1 : E →L[ℂ] E)‖ + 1) ^
      (finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) - 1)) ?_
    (Det.isLittleO_exp_smul_sub_one_sub X) ?_
  · simp only [zero_smul, NormedSpace.exp_zero]
    exact detP_one hP
  · filter_upwards [Det.eventually_norm_exp_smul_lt X, Det.eventually_norm_one_add_smul_lt X]
      with z h1 h2
    rw [← hq z]
    refine (norm_detP_sub_detP_le ((Det.norm_compress_le hP _).trans h1.le)
      ((Det.norm_compress_le hP _).trans h2.le)).trans ?_
    gcongr
    rw [← sub_mul, ← mul_sub, ← sub_sub]
    exact Det.norm_compress_le hP _

/-- **Lemma A.9(ii), first half**: if `[X, P] = 0`, then `det_P (e^X) = e^{Tr (P X)}`. -/
theorem detP_exp (hP : IsStarProjection P) {X : E →L[ℂ] E} (hX : Commute X P) :
    detP P (NormedSpace.exp X) =
      Complex.exp (LinearMap.trace ℂ E ((P * X : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  let _ : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
  have h := Det.eq_cexp_of_add_mul (f := fun z : ℂ => detP P (NormedSpace.exp (z • X))) ?_ ?_
    (hasDerivAt_detP_exp_smul_zero hP hX)
  · simpa using h
  · simp only [zero_smul, NormedSpace.exp_zero]
    exact detP_one hP
  · intro z w
    rw [add_smul, NormedSpace.exp_add_of_commute (((Commute.refl X).smul_left z).smul_right w)]
    exact detP_mul hP _ (hX.smul_left w).exp_left

/-- **Lemma A.9(iii)**, the bound: for unitary `V`,
`|det (P V* P|_{ran P}) · det (P V P|_{ran P}) - 1| ≤ p ‖[P, V]‖`. -/
theorem norm_detP_star_mul_detP_sub_one_le (hP : IsStarProjection P) {V : E →L[ℂ] E}
    (hV : V ∈ unitary (E →L[ℂ] E)) :
    ‖detP P (star V) * detP P V - 1‖ ≤
      finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) * ‖⁅P, V⁆‖ := by
  have hP1 : ‖P‖ ≤ 1 := IsStarProjection.norm_le P hP
  have hV1 : ‖V‖ ≤ 1 := Det.norm_le_one_of_mem_unitary hV
  have hVs1 : ‖star V‖ ≤ 1 := Det.norm_le_one_of_mem_unitary (Unitary.star_mem hV)
  have h2 : P * P = P := hP.isIdempotentElem.eq
  have hmul : detP P (star V) * detP P V = detP P (star V * (P * V * P)) := by
    rw [detP_mul_of_mapsTo hP _ _ fun v _ => Det.compress_mem_range P V v, detP_compress hP]
  have hA : ‖P * (star V * (P * V * P)) * P‖ ≤ 1 := by
    refine (Det.norm_compress_le hP _).trans ?_
    calc ‖star V * (P * V * P)‖ ≤ ‖star V‖ * ‖P * V * P‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := by gcongr; exact (Det.norm_compress_le hP V).trans hV1
      _ = 1 := one_mul 1
  have hB : ‖P * 1 * P‖ ≤ 1 := by rw [mul_one, h2]; exact hP1
  have hdiff : P * (star V * (P * V * P)) * P - P * 1 * P = P * star V * ⁅P, V⁆ * P := by
    rw [← compress_star_mul_compress_sub hP hV]
    have h4 : P * (star V * (P * V * P)) * P - P * 1 * P =
        P * star V * P * V * (P * P) - P * P := by noncomm_ring
    rw [h4, h2]
  have hnorm : ‖P * star V * ⁅P, V⁆ * P‖ ≤ ‖⁅P, V⁆‖ := by
    have h5 : P * star V * ⁅P, V⁆ * P = P * (star V * ⁅P, V⁆) * P := by noncomm_ring
    rw [h5]
    refine (Det.norm_compress_le hP _).trans ?_
    calc ‖star V * ⁅P, V⁆‖ ≤ ‖star V‖ * ‖⁅P, V⁆‖ := norm_mul_le _ _
      _ ≤ 1 * ‖⁅P, V⁆‖ := by gcongr
      _ = ‖⁅P, V⁆‖ := one_mul _
  rw [hmul, ← detP_one hP]
  calc ‖detP P (star V * (P * V * P)) - detP P 1‖
      ≤ finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) *
          1 ^ (finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) - 1) *
            ‖P * (star V * (P * V * P)) * P - P * 1 * P‖ := norm_detP_sub_detP_le hA hB
    _ ≤ finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) * ‖⁅P, V⁆‖ := by
        rw [one_pow, mul_one, hdiff]
        gcongr

end DetP

/-! ## 5. Lemma A.9(iv): `|e^{2πix} - 1| ≥ 4 dist(x, ℤ)` -/

section Integers

/-- `|e^{2πix} - 1| = 2|sin(πx)|`. -/
theorem norm_cexp_two_pi_I_mul_sub_one (x : ℝ) :
    ‖Complex.exp (2 * π * I * x) - 1‖ = 2 * |Real.sin (π * x)| := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * π * x)
  rw [show (2 * π * I * x : ℂ) = I * ((2 * π * x : ℝ) : ℂ) by push_cast; ring, h,
    norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two,
    show 2 * π * x / 2 = π * x by ring]

/-- **Lemma A.9(iv)**, with `dist(x, ℤ) = |x - round x|`: `4 |x - round x| ≤ |e^{2πix} - 1|`.
Proof: `|e^{2πix} - 1| = 2|sin(πx)| = 2|sin(πd)|` with `d = x - round x ∈ [-1/2, 1/2]`, and
`|sin(πd)| = sin(π|d|) ≥ 2|d|` (Jordan's inequality, `Real.mul_le_sin`). -/
theorem four_mul_abs_sub_round_le (x : ℝ) :
    4 * |x - round x| ≤ ‖Complex.exp (2 * π * I * x) - 1‖ := by
  rw [norm_cexp_two_pi_I_mul_sub_one]
  set d := x - round x with hd_def
  have hd : |d| ≤ 1 / 2 := abs_sub_round x
  have h2 : |Real.sin (π * x)| = |Real.sin (π * d)| := by
    have : π * x = π * d + (round x : ℝ) * π := by rw [hd_def]; ring
    rw [this, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  have h4 : Real.sin (π * |d|) = |Real.sin (π * d)| := by
    rcases abs_cases d with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [h, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [Real.pi_pos])
    · rw [h, mul_neg, Real.sin_neg, abs_of_nonpos]
      have : 0 ≤ Real.sin (π * -d) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      rw [mul_neg, Real.sin_neg] at this
      linarith
  have h5 := Real.mul_le_sin (x := π * |d|) (by positivity) (by nlinarith [Real.pi_pos])
  have h6 : 2 / π * (π * |d|) = 2 * |d| := by field_simp
  rw [h2, ← h4]
  linarith

/-- **Lemma A.9(iv)**, the paper's form: `4 dist(x, ℤ) ≤ |e^{2πix} - 1|`, with `dist(x, ℤ)` the
infimum distance to the integers. -/
theorem four_mul_infDist_int_le (x : ℝ) :
    4 * Metric.infDist x (Set.range ((↑) : ℤ → ℝ)) ≤ ‖Complex.exp (2 * π * I * x) - 1‖ := by
  have h : Metric.infDist x (Set.range ((↑) : ℤ → ℝ)) ≤ |x - round x| :=
    calc Metric.infDist x (Set.range ((↑) : ℤ → ℝ)) ≤ dist x (round x : ℝ) :=
          Metric.infDist_le_dist_of_mem ⟨round x, rfl⟩
      _ = |x - round x| := Real.dist_eq _ _
  linarith [four_mul_abs_sub_round_le x]

/-- The form in which Lemma 6.17(iii) uses Lemma A.9(iv): some integer is within
`|e^{2πix} - 1| / 4` of `x`. -/
theorem exists_int_abs_sub_le (x : ℝ) :
    ∃ n : ℤ, |x - n| ≤ ‖Complex.exp (2 * π * I * x) - 1‖ / 4 :=
  ⟨round x, by linarith [four_mul_abs_sub_round_le x]⟩

end Integers

end HRTorus.IndexCore
