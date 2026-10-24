import HRTorus.IndexCore.Clustering
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Lemma A.8 and the Duhamel bound (6.7)

Written by Claude Opus 5.5 (an AI model), 2026-10-23. The exponential estimates of the HR paper's Section 6 and Appendix A, for the
unitary groups `e^{itA}` of self-adjoint operators on a finite-dimensional Hilbert space:

* `expI t A = exp(t • (i • A))`, its group law, adjoint `e^{-itA}`, unitarity and norm `≤ 1`,
  commutation, derivative, and the bridges from the forms used in `Statement.lean`;
* **(6.7)** `‖[e^{iφA}, C]‖ ≤ |φ| ‖[A, C]‖` (Lemma A.8, first bound) and its two-exponential form
  `‖[e^{iφA}, e^{iψB}]‖ ≤ |φ ψ| ‖[A, B]‖`;
* **Lemma A.8, second bound:** `‖e^{iθ(A+B)} - e^{iθA} e^{iθB}‖ ≤ θ²/2 · ‖[A, B]‖`;
* **Lemma A.8, third bound:** `‖e^{iA} - e^{iA'}‖ ≤ ‖A - A'‖`;
* two elementary facts about products of contractions used throughout Lemma 6.13.

The paper proves the first bound through the integral identity (6.7); here the bound is proved by
the mean value inequality for `s ↦ e^{isA} C e^{-isA}`, whose derivative is
`e^{isA} (i[A, C]) e^{-isA}` — the integrand of (6.7). The integral identity itself is not stated.
The second bound uses the comparison form of the mean value inequality with the boundary function
`s²/2 · ‖[A, B]‖`, which gives the paper's constant `1/2`.

Exponential lemmas that need a `NormedAlgebra ℚ` structure get Mathlib's own local workaround,
`NormedAlgebra.restrictScalars ℚ ℂ`.
-/

open scoped InnerProductSpace ComplexConjugate Real
open Complex (I)

noncomputable section

namespace HRTorus.IndexCore

/-! ## Generic facts in a normed ring -/

section NormedRing

variable {𝔸 : Type*} [NormedRing 𝔸]

theorem norm_lie_comm (x y : 𝔸) : ‖⁅x, y⁆‖ = ‖⁅y, x⁆‖ := by
  rw [Ring.lie_def, Ring.lie_def, ← norm_neg, neg_sub]

/-- A product of contractions changes by at most the sum of the changes of its factors. -/
theorem norm_mul_sub_mul_le {a b a' b' : 𝔸} (hb : ‖b‖ ≤ 1) (ha' : ‖a'‖ ≤ 1) :
    ‖a * b - a' * b'‖ ≤ ‖a - a'‖ + ‖b - b'‖ := by
  have e : a * b - a' * b' = (a - a') * b + a' * (b - b') := by noncomm_ring
  rw [e]
  calc ‖(a - a') * b + a' * (b - b')‖ ≤ ‖(a - a') * b‖ + ‖a' * (b - b')‖ := norm_add_le _ _
    _ ≤ ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖a - a'‖ * 1 + 1 * ‖b - b'‖ := by gcongr
    _ = ‖a - a'‖ + ‖b - b'‖ := by ring

/-- `‖[ab, c]‖ ≤ ‖[a, c]‖ + ‖[b, c]‖` for contractions `a`, `b`. -/
theorem norm_lie_mul_le {a b : 𝔸} (c : 𝔸) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖⁅a * b, c⁆‖ ≤ ‖⁅a, c⁆‖ + ‖⁅b, c⁆‖ := by
  have e : ⁅a * b, c⁆ = a * ⁅b, c⁆ + ⁅a, c⁆ * b := by
    simp only [Ring.lie_def]; noncomm_ring
  rw [e]
  calc ‖a * ⁅b, c⁆ + ⁅a, c⁆ * b‖ ≤ ‖a * ⁅b, c⁆‖ + ‖⁅a, c⁆ * b‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖⁅b, c⁆‖ + ‖⁅a, c⁆‖ * ‖b‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 1 * ‖⁅b, c⁆‖ + ‖⁅a, c⁆‖ * 1 := by gcongr
    _ = ‖⁅a, c⁆‖ + ‖⁅b, c⁆‖ := by ring

theorem norm_lie_add_left_le (a b c : 𝔸) : ‖⁅a + b, c⁆‖ ≤ ‖⁅a, c⁆‖ + ‖⁅b, c⁆‖ := by
  have e : ⁅a + b, c⁆ = ⁅a, c⁆ + ⁅b, c⁆ := by simp only [Ring.lie_def]; noncomm_ring
  rw [e]; exact norm_add_le _ _

theorem norm_lie_sub_left_le (a b c : 𝔸) : ‖⁅a - b, c⁆‖ ≤ ‖⁅a, c⁆‖ + ‖⁅b, c⁆‖ := by
  have e : ⁅a - b, c⁆ = ⁅a, c⁆ - ⁅b, c⁆ := by simp only [Ring.lie_def]; noncomm_ring
  rw [e]; exact norm_sub_le _ _

theorem norm_lie_add_right_le (a b c : 𝔸) : ‖⁅a, b + c⁆‖ ≤ ‖⁅a, b⁆‖ + ‖⁅a, c⁆‖ := by
  have e : ⁅a, b + c⁆ = ⁅a, b⁆ + ⁅a, c⁆ := by simp only [Ring.lie_def]; noncomm_ring
  rw [e]; exact norm_add_le _ _

theorem norm_lie_sub_right_le (a b c : 𝔸) : ‖⁅a, b - c⁆‖ ≤ ‖⁅a, b⁆‖ + ‖⁅a, c⁆‖ := by
  have e : ⁅a, b - c⁆ = ⁅a, b⁆ - ⁅a, c⁆ := by simp only [Ring.lie_def]; noncomm_ring
  rw [e]; exact norm_sub_le _ _

end NormedRing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A unitary operator has norm at most one (no nontriviality needed). -/
theorem norm_le_one_of_mem_unitary {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) :
    ‖U‖ ≤ 1 := by
  have h1 : ‖star U * U‖ = ‖U‖ * ‖U‖ := CStarRing.norm_star_mul_self
  rw [(Unitary.mem_iff.mp hU).1] at h1
  have h2 : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := by
    rw [ContinuousLinearMap.one_def]; exact ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg U]

/-! ## The unitary groups `e^{itA}` -/

/-- `e^{itA}`: the exponential of `t • (i • A)`, the real parameter acting by real scalars. -/
def expI (t : ℝ) (A : E →L[ℂ] E) : E →L[ℂ] E := NormedSpace.exp (t • (I • A))

omit [CompleteSpace E] in
theorem expI_def (t : ℝ) (A : E →L[ℂ] E) : expI t A = NormedSpace.exp (t • (I • A)) := rfl

omit [CompleteSpace E] in
theorem smul_I_mul (t : ℝ) (A : E →L[ℂ] E) : (I * (t : ℂ)) • A = t • (I • A) := by
  rw [mul_comm, mul_smul, Complex.coe_smul]

omit [CompleteSpace E] in
/-- The form `e^{(iφ)•X}` of `Statement.lean`. -/
theorem exp_I_mul_smul (t : ℝ) (A : E →L[ℂ] E) :
    NormedSpace.exp ((I * (t : ℂ)) • A) = expI t A := by
  rw [smul_I_mul]; rfl

omit [CompleteSpace E] in
/-- The form `e^{-(iφ)•X}` of `Statement.lean`. -/
theorem exp_neg_I_mul_smul (t : ℝ) (A : E →L[ℂ] E) :
    NormedSpace.exp ((-(I * (t : ℂ))) • A) = expI (-t) A := by
  rw [← exp_I_mul_smul]; congr 2; push_cast; ring

omit [CompleteSpace E] in
/-- The form `e^{(2πi)•X}` of `Statement.lean`. -/
theorem exp_two_pi_I_smul (A : E →L[ℂ] E) :
    NormedSpace.exp ((2 * π * I) • A) = expI (2 * π) A := by
  rw [← exp_I_mul_smul]; congr 2; push_cast; ring

section Exp

variable (A : E →L[ℂ] E)

omit [CompleteSpace E] in
theorem expI_zero : expI 0 A = 1 := by
  rw [expI_def, zero_smul, NormedSpace.exp_zero]

theorem expI_add (s t : ℝ) : expI (s + t) A = expI s A * expI t A := by
  let _ : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
  rw [expI_def, expI_def, expI_def, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl (I • A)).smul_left s).smul_right t)

theorem expI_mul_expI_neg (t : ℝ) : expI t A * expI (-t) A = 1 := by
  rw [← expI_add, add_neg_cancel, expI_zero]

theorem expI_neg_mul_expI (t : ℝ) : expI (-t) A * expI t A = 1 := by
  rw [← expI_add, neg_add_cancel, expI_zero]

omit [CompleteSpace E] in
theorem commute_expI_of_commute {X : E →L[ℂ] E} (h : Commute X A) (t : ℝ) :
    Commute X (expI t A) :=
  ((h.smul_right I).smul_right t).exp_right

omit [CompleteSpace E] in
theorem commute_expI_self (t : ℝ) : Commute A (expI t A) :=
  commute_expI_of_commute A (Commute.refl A) t

omit [CompleteSpace E] in
theorem commute_expI_expI_of_commute {B : E →L[ℂ] E} (h : Commute A B) (s t : ℝ) :
    Commute (expI s A) (expI t B) :=
  commute_expI_of_commute B (commute_expI_of_commute A h.symm s).symm t

/-- `e^{itA}* = e^{-itA}` for self-adjoint `A`. -/
theorem star_expI (hA : IsSelfAdjoint A) (t : ℝ) : star (expI t A) = expI (-t) A := by
  rw [expI_def, expI_def, NormedSpace.star_exp, star_smul, star_trivial, star_smul, hA.star_eq,
    Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_smul]

/-- `e^{itA}` is unitary for self-adjoint `A`. -/
theorem expI_mem_unitary (hA : IsSelfAdjoint A) (t : ℝ) : expI t A ∈ unitary (E →L[ℂ] E) := by
  rw [Unitary.mem_iff, star_expI A hA, expI_neg_mul_expI, expI_mul_expI_neg]
  exact ⟨rfl, rfl⟩

theorem norm_expI_le (hA : IsSelfAdjoint A) (t : ℝ) : ‖expI t A‖ ≤ 1 :=
  norm_le_one_of_mem_unitary (expI_mem_unitary A hA t)

theorem norm_expI_mul (hA : IsSelfAdjoint A) (t : ℝ) (X : E →L[ℂ] E) :
    ‖expI t A * X‖ = ‖X‖ :=
  CStarRing.norm_coe_unitary_mul ⟨_, expI_mem_unitary A hA t⟩ X

theorem norm_mul_expI (hA : IsSelfAdjoint A) (t : ℝ) (X : E →L[ℂ] E) :
    ‖X * expI t A‖ = ‖X‖ :=
  CStarRing.norm_mul_coe_unitary X ⟨_, expI_mem_unitary A hA t⟩

/-- Conjugation by a unitary: `U* e^{itX} U = e^{it U*XU}`. -/
theorem conj_expI {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) (t : ℝ) :
    star U * expI t A * U = expI t (star U * A * U) := by
  let _ : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
  have hUU : U * star U = 1 := (Unitary.mem_iff.mp hU).2
  have hUU' : star U * U = 1 := (Unitary.mem_iff.mp hU).1
  have hsc : SemiconjBy (star U) (t • (I • A)) (t • (I • (star U * A * U))) := by
    rw [SemiconjBy, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm]
    simp only [mul_assoc, hUU, mul_one]
  have h := hsc.exp_right
  rw [SemiconjBy] at h
  rw [expI_def, expI_def, h, mul_assoc, hUU', mul_one]

/-! ## Derivatives -/

theorem hasDerivAt_expI (t : ℝ) :
    HasDerivAt (fun s : ℝ => expI s A) (expI t A * (I • A)) t :=
  hasDerivAt_exp_smul_const (I • A) t

theorem hasDerivAt_expI' (t : ℝ) :
    HasDerivAt (fun s : ℝ => expI s A) ((I • A) * expI t A) t :=
  hasDerivAt_exp_smul_const' (I • A) t

theorem hasDerivAt_expI_neg (t : ℝ) :
    HasDerivAt (fun s : ℝ => expI (-s) A) (-((I • A) * expI (-t) A)) t := by
  have h := (hasDerivAt_expI' A (-t)).scomp t (hasDerivAt_neg t)
  rw [neg_one_smul] at h
  exact h

/-! ## Lemma A.8 -/

/-- **(6.7) / Lemma A.8, first bound:** `‖[e^{iφA}, B]‖ ≤ |φ| ‖[A, B]‖` for self-adjoint `A`
and any `B`. -/
theorem norm_lie_expI_le (hA : IsSelfAdjoint A) (B : E →L[ℂ] E) (φ : ℝ) :
    ‖⁅expI φ A, B⁆‖ ≤ |φ| * ‖⁅A, B⁆‖ := by
  set g : ℝ → E →L[ℂ] E := fun s => expI s A * B * expI (-s) A with hg_def
  have hderiv : ∀ s, HasDerivAt g (expI s A * (I • ⁅A, B⁆) * expI (-s) A) s := by
    intro s
    have h := ((hasDerivAt_expI A s).mul_const B).mul (hasDerivAt_expI_neg A s)
    convert h using 1
    rw [Ring.lie_def, smul_sub, ← smul_mul_assoc, ← mul_smul_comm]
    noncomm_ring
  have hbound : ∀ s ∈ (Set.univ : Set ℝ),
      ‖expI s A * (I • ⁅A, B⁆) * expI (-s) A‖ ≤ ‖⁅A, B⁆‖ := by
    intro s _
    rw [norm_mul_expI A hA, norm_expI_mul A hA, norm_smul, Complex.norm_I, one_mul]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hderiv s).hasDerivWithinAt) hbound convex_univ (Set.mem_univ 0)
    (Set.mem_univ φ)
  have hg0 : g 0 = B := by
    simp only [hg_def, neg_zero, expI_zero, one_mul, mul_one]
  have hcomm : ⁅expI φ A, B⁆ = (g φ - g 0) * expI φ A := by
    rw [hg0, sub_mul, Ring.lie_def]
    congr 1
    show expI φ A * B = expI φ A * B * expI (-φ) A * expI φ A
    rw [mul_assoc (expI φ A * B), expI_neg_mul_expI, mul_one]
  rw [hcomm, norm_mul_expI A hA]
  calc ‖g φ - g 0‖ ≤ ‖⁅A, B⁆‖ * ‖φ - 0‖ := hmvt
    _ = |φ| * ‖⁅A, B⁆‖ := by rw [sub_zero, Real.norm_eq_abs, mul_comm]

/-- **(6.7), applied twice:** `‖[e^{iφA}, e^{iψB}]‖ ≤ |φ| |ψ| ‖[A, B]‖` for self-adjoint `A`, `B`. -/
theorem norm_lie_expI_expI_le (hA : IsSelfAdjoint A) {B : E →L[ℂ] E} (hB : IsSelfAdjoint B)
    (φ ψ : ℝ) : ‖⁅expI φ A, expI ψ B⁆‖ ≤ |φ| * |ψ| * ‖⁅A, B⁆‖ := by
  calc ‖⁅expI φ A, expI ψ B⁆‖ ≤ |φ| * ‖⁅A, expI ψ B⁆‖ := norm_lie_expI_le A hA _ φ
    _ = |φ| * ‖⁅expI ψ B, A⁆‖ := by rw [norm_lie_comm]
    _ ≤ |φ| * (|ψ| * ‖⁅B, A⁆‖) := by gcongr; exact norm_lie_expI_le B hB A ψ
    _ = |φ| * |ψ| * ‖⁅A, B⁆‖ := by rw [norm_lie_comm B A]; ring

/-- **Lemma A.8, second bound** at `θ = 1`: `‖e^{i(A+B)} - e^{iA} e^{iB}‖ ≤ ‖[A, B]‖ / 2`. -/
theorem norm_expI_one_add_sub_le (hA : IsSelfAdjoint A) {B : E →L[ℂ] E} (hB : IsSelfAdjoint B) :
    ‖expI 1 (A + B) - expI 1 A * expI 1 B‖ ≤ 1 / 2 * ‖⁅A, B⁆‖ := by
  have hAB : IsSelfAdjoint (A + B) := hA.add hB
  set O : ℝ → E →L[ℂ] E := fun s => expI s A * expI s B * expI (-s) (A + B) with hO_def
  set D : ℝ → E →L[ℂ] E := fun s => expI s A * (I • ⁅A, expI s B⁆) * expI (-s) (A + B)
    with hD_def
  have hd : ∀ s, HasDerivAt O (D s) s := by
    intro s
    have h := ((hasDerivAt_expI A s).mul (hasDerivAt_expI' B s)).mul
      (hasDerivAt_expI_neg (A + B) s)
    simp only [Pi.mul_apply] at h
    convert h using 1
    have hc : (I • B) * expI s B = expI s B * (I • B) :=
      ((commute_expI_self B s).smul_left I).eq
    have e1 : I • ⁅A, expI s B⁆ = (I • A) * expI s B - expI s B * (I • A) := by
      rw [Ring.lie_def, smul_sub, smul_mul_assoc, mul_smul_comm]
    simp only [hD_def]
    rw [e1, smul_add, hc]
    noncomm_ring
  have hbd : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖D s‖ ≤ s * ‖⁅A, B⁆‖ := by
    intro s hs
    simp only [hD_def]
    rw [norm_mul_expI _ hAB, norm_expI_mul _ hA, norm_smul, Complex.norm_I, one_mul,
      norm_lie_comm]
    calc ‖⁅expI s B, A⁆‖ ≤ |s| * ‖⁅B, A⁆‖ := norm_lie_expI_le B hB A s
      _ = s * ‖⁅A, B⁆‖ := by rw [abs_of_nonneg hs.1, norm_lie_comm]
  have hBd : ∀ x : ℝ, HasDerivAt (fun s : ℝ => s ^ 2 / 2 * ‖⁅A, B⁆‖) (x * ‖⁅A, B⁆‖) x := by
    intro x
    have h := ((hasDerivAt_pow 2 x).div_const 2).mul_const ‖⁅A, B⁆‖
    convert h using 1
    push_cast; ring
  have hcont : ContinuousOn (fun s => O s - 1) (Set.Icc 0 1) := fun s _ =>
    ((hd s).sub_const 1).continuousAt.continuousWithinAt
  have hO0 : O 0 = 1 := by
    simp only [hO_def, neg_zero, expI_zero, mul_one]
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont
    (fun s _ => ((hd s).sub_const 1).hasDerivWithinAt) (by simp [hO0]) hBd hbd
    (Set.right_mem_Icc.2 zero_le_one)
  have e : expI 1 (A + B) - expI 1 A * expI 1 B = -((O 1 - 1) * expI 1 (A + B)) := by
    simp only [hO_def]
    rw [sub_mul, one_mul, mul_assoc (expI 1 A * expI 1 B), expI_neg_mul_expI, mul_one, neg_sub]
  rw [e, norm_neg, norm_mul_expI _ hAB]
  calc ‖O 1 - 1‖ ≤ (1 : ℝ) ^ 2 / 2 * ‖⁅A, B⁆‖ := key
    _ = 1 / 2 * ‖⁅A, B⁆‖ := by norm_num

/-- **Lemma A.8, second bound:** `‖e^{iθ(A+B)} - e^{iθA} e^{iθB}‖ ≤ θ²/2 · ‖[A, B]‖`. -/
theorem norm_expI_add_sub_le (hA : IsSelfAdjoint A) {B : E →L[ℂ] E} (hB : IsSelfAdjoint B)
    (θ : ℝ) : ‖expI θ (A + B) - expI θ A * expI θ B‖ ≤ θ ^ 2 / 2 * ‖⁅A, B⁆‖ := by
  have e : ∀ X : E →L[ℂ] E, expI θ X = expI 1 (θ • X) := by
    intro X
    rw [expI_def, expI_def, one_smul, smul_comm θ I X]
  have hθA : IsSelfAdjoint (θ • A) := (IsSelfAdjoint.all θ).smul hA
  have hθB : IsSelfAdjoint (θ • B) := (IsSelfAdjoint.all θ).smul hB
  rw [e, e, e, smul_add]
  calc ‖expI 1 (θ • A + θ • B) - expI 1 (θ • A) * expI 1 (θ • B)‖
        ≤ 1 / 2 * ‖⁅θ • A, θ • B⁆‖ := norm_expI_one_add_sub_le _ hθA hθB
    _ = θ ^ 2 / 2 * ‖⁅A, B⁆‖ := by
        rw [Ring.lie_def, smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, norm_smul,
          ← Ring.lie_def, Real.norm_eq_abs, abs_mul_self]
        ring

/-- **Lemma A.8, third bound:** `‖e^{iA} - e^{iA'}‖ ≤ ‖A - A'‖` for self-adjoint `A`, `A'`. -/
theorem norm_expI_sub_expI_le (hA : IsSelfAdjoint A) {A' : E →L[ℂ] E} (hA' : IsSelfAdjoint A') :
    ‖expI 1 A - expI 1 A'‖ ≤ ‖A - A'‖ := by
  set g : ℝ → E →L[ℂ] E := fun s => expI s A * expI (-s) A' with hg_def
  have hderiv : ∀ s, HasDerivAt g (expI s A * (I • (A - A')) * expI (-s) A') s := by
    intro s
    have h := (hasDerivAt_expI A s).mul (hasDerivAt_expI_neg A' s)
    convert h using 1
    rw [smul_sub]
    noncomm_ring
  have hbound : ∀ s ∈ (Set.univ : Set ℝ),
      ‖expI s A * (I • (A - A')) * expI (-s) A'‖ ≤ ‖A - A'‖ := by
    intro s _
    rw [norm_mul_expI A' hA', norm_expI_mul A hA, norm_smul, Complex.norm_I, one_mul]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hderiv s).hasDerivWithinAt) hbound convex_univ (Set.mem_univ 0)
    (Set.mem_univ 1)
  have hg0 : g 0 = 1 := by simp only [hg_def, neg_zero, expI_zero, mul_one]
  have e : expI 1 A - expI 1 A' = (g 1 - g 0) * expI 1 A' := by
    rw [hg0, sub_mul, one_mul]
    simp only [hg_def]
    rw [mul_assoc, expI_neg_mul_expI, mul_one]
  rw [e, norm_mul_expI A' hA']
  calc ‖g 1 - g 0‖ ≤ ‖A - A'‖ * ‖(1 : ℝ) - 0‖ := hmvt
    _ = ‖A - A'‖ := by norm_num

end Exp

end HRTorus.IndexCore
