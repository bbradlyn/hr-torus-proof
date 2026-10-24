import HRTorus.IndexCore.ODE
import HRTorus.IndexCore.Det
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Lemma 6.17 (the determinant at `2π`) and the trace bound

Written by Claude Opus 5.5 (an AI model), 2026-10-23. The paper is the HR paper (`papers/hr/`), Section 6,
`lem:determinant` (Lemma 6.17). The determinant on `ran P` is the `detP` of `Det.lean`,
used through its API only; `Det.lean` is not edited.

* **The trace bound** `|Tr(P X)| ≤ p ‖X‖` with `p = rank P` (`norm_trc_P_mul_le`), from
  `Tr(P X) = ∑ᵢ ⟪bᵢ, X bᵢ⟫` over an orthonormal basis of `ran P` (`trc_P_mul_eq_sum`); and the
  reality of `Tr(P X)` for self-adjoint `X` (`im_trc_P_mul_eq_zero`).
* **(i)** Steps 1–2: `‖𝓜₋(2π) - U^* e^{2πiQ̄₋} U e^{-2πiQ̄₋}‖ ≤ (24π² + 1) ε`
  (`SepBounds.norm_Mminus_two_pi_sub_le`); Step 3:
  `|det_P 𝒵(2π) - 1| ≤ p (‖𝓜₋(2π) - U^* e^{2πiQ̄₋} U e^{-2πiQ̄₋}‖ + 3 ‖[P, U]‖ + 2 ‖[P, e^{2πiQ̄₋}]‖)`
  (`norm_detP_Zc_two_pi_sub_one_le`).
* **(ii)** `det_P 𝒴(2π) = e^{2πi Tr(P T̃)}` exactly (`detP_Yc_two_pi`).
* **(iii)** `|e^{2πi Tr(P T̃)} - 1| ≤ p ‖𝒴(2π) - 𝒵(2π)‖ + |det_P 𝒵(2π) - 1|`, and `Tr(P T̃)` is
  real, within a quarter of that of an integer (`exists_int_norm_trc_Ttilde_sub_le`).
* **(iv)** `Tr(P T̃) - Tr(P T₋) = Tr(P K₋) - Tr(P K^U₋)` and
  `|Tr(P T̃) - Tr(P T₋)| ≤ 2p ‖[U, P]‖ ‖K₋‖` (`norm_trc_Ttilde_sub_trc_Tminus_le`). The paper's
  proof bounds the trace norm of the rank-`2p` operator `UPU^* - P`; here the same bound comes from
  the trace bound for `P`, applied twice after splitting with the projection `UPU^*`.
-/

open scoped InnerProductSpace ComplexConjugate Real
open Complex (I)
open Module

noncomputable section

namespace HRTorus.IndexCore

/-! ## Norms of products of contractions -/

section NormedRing

variable {𝔸 : Type*} [NormedRing 𝔸]

theorem norm_mul_le_of_le_one_left {a b : 𝔸} (ha : ‖a‖ ≤ 1) : ‖a * b‖ ≤ ‖b‖ :=
  (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) ha)

theorem norm_mul_le_of_le_one_right {a b : 𝔸} (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ ‖a‖ :=
  (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hb)

theorem norm_mul_le_one {a b : 𝔸} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 :=
  (norm_mul_le_of_le_one_left ha).trans hb

end NormedRing

/-! ## The trace -/

section Trace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E] {P : E →L[ℂ] E}

/-- `Tr X` for a continuous linear endomorphism of `E`. -/
def trc (X : E →L[ℂ] E) : ℂ := LinearMap.trace ℂ E (X : E →ₗ[ℂ] E)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem trc_add (X Y : E →L[ℂ] E) : trc (X + Y) = trc X + trc Y :=
  map_add (LinearMap.trace ℂ E) (X : E →ₗ[ℂ] E) Y

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem trc_sub (X Y : E →L[ℂ] E) : trc (X - Y) = trc X - trc Y :=
  map_sub (LinearMap.trace ℂ E) (X : E →ₗ[ℂ] E) Y

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem trc_neg (X : E →L[ℂ] E) : trc (-X) = -trc X :=
  map_neg (LinearMap.trace ℂ E) (X : E →ₗ[ℂ] E)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem trc_smul (c : ℂ) (X : E →L[ℂ] E) : trc (c • X) = c * trc X :=
  (map_smul (LinearMap.trace ℂ E) c (X : E →ₗ[ℂ] E)).trans (smul_eq_mul _ _)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
/-- Cyclicity: `Tr(X Y) = Tr(Y X)`. -/
theorem trc_mul_comm (X Y : E →L[ℂ] E) : trc (X * Y) = trc (Y * X) :=
  LinearMap.trace_mul_comm ℂ (X : E →ₗ[ℂ] E) Y

omit [FiniteDimensional ℂ E] in
/-- `Tr(P Y) = Tr(P (Y P))` for a projection `P`. -/
theorem trc_P_mul_eq (hP : IsStarProjection P) (Y : E →L[ℂ] E) :
    trc (P * Y) = trc (P * (Y * P)) := by
  calc trc (P * Y) = trc (P * (P * Y)) := by rw [← mul_assoc, hP.isIdempotentElem.eq]
    _ = trc (P * Y * P) := trc_mul_comm _ _
    _ = trc (P * (Y * P)) := by rw [mul_assoc]

/-- `Tr(P X) = ∑ᵢ ⟪bᵢ, X bᵢ⟫` for an orthonormal basis `b` of `ran P`. -/
theorem trc_P_mul_eq_sum (hP : IsStarProjection P) (X : E →L[ℂ] E) :
    trc (P * X) = ∑ i, ⟪((stdOrthonormalBasis ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) i : _) : E),
      X (stdOrthonormalBasis ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) i)⟫_ℂ := by
  set R := LinearMap.range (P : E →ₗ[ℂ] E)
  set b := stdOrthonormalBasis ℂ R
  have hf : ∀ x, ((P * X : E →L[ℂ] E) : E →ₗ[ℂ] E) x ∈ R := fun x =>
    LinearMap.mem_range_self (P : E →ₗ[ℂ] E) (X x)
  rw [trc, ← LinearMap.trace_restrict_eq_of_forall_mem R _ hf, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_inner, LinearMap.coe_restrict_apply, ContinuousLinearMap.coe_coe,
    mul_apply_eq_comp, ← starProj_inner hP, Det.starProj_apply_of_mem hP (b i).2]

/-- **The trace bound**: `|Tr(P X)| ≤ p ‖X‖`. -/
theorem norm_trc_P_mul_le (hP : IsStarProjection P) (X : E →L[ℂ] E) :
    ‖trc (P * X)‖ ≤ finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) * ‖X‖ := by
  rw [trc_P_mul_eq_sum hP]
  set b := stdOrthonormalBasis ℂ (LinearMap.range (P : E →ₗ[ℂ] E))
  calc ‖∑ i, ⟪((b i : _) : E), X (b i)⟫_ℂ‖ ≤ ∑ i, ‖⟪((b i : _) : E), X (b i)⟫_ℂ‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i, ‖X‖ := by
        refine Finset.sum_le_sum fun i _ => (norm_inner_le_norm _ _).trans ?_
        have h1 : ‖((b i : _) : E)‖ = 1 := by rw [Submodule.norm_coe]; exact b.norm_eq_one i
        rw [h1, one_mul]
        exact (X.le_opNorm _).trans (by rw [h1, mul_one])
    _ = finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) * ‖X‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `Tr(P X)` is real for self-adjoint `X`. -/
theorem im_trc_P_mul_eq_zero (hP : IsStarProjection P) {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) :
    (trc (P * X)).im = 0 := by
  rw [trc_P_mul_eq_sum hP, Complex.im_sum]
  exact Finset.sum_eq_zero fun i _ => hX.isSymmetric.im_inner_self_apply _

theorem trc_P_mul_eq_re (hP : IsStarProjection P) {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) :
    trc (P * X) = ((trc (P * X)).re : ℂ) :=
  Complex.ext (by simp) (by rw [im_trc_P_mul_eq_zero hP hX, Complex.ofReal_im])

omit [FiniteDimensional ℂ E] in
/-- `Q = U P U^*` is a projection when `U` is unitary. -/
theorem isStarProjection_conj (hP : IsStarProjection P) {U : E →L[ℂ] E}
    (hU : U ∈ unitary (E →L[ℂ] E)) : IsStarProjection (U * P * star U) where
  isIdempotentElem := by
    show U * P * star U * (U * P * star U) = U * P * star U
    have h1 : star U * U = 1 := Unitary.star_mul_self_of_mem hU
    calc U * P * star U * (U * P * star U) = U * P * (star U * U) * P * star U := by noncomm_ring
      _ = U * (P * P) * star U := by rw [h1, mul_one, mul_assoc U P P]
      _ = U * P * star U := by rw [hP.isIdempotentElem.eq]
  isSelfAdjoint := by
    show star (U * P * star U) = U * P * star U
    rw [star_mul, star_mul, star_star, hP.isSelfAdjoint.star_eq, mul_assoc]

/-- The core of **Lemma 6.17(iv)**: `|Tr(P U^* K U) - Tr(P K)| ≤ 2p ‖[U, P]‖ ‖K‖`. -/
theorem norm_trc_conj_sub_le (hP : IsStarProjection P) {U : E →L[ℂ] E}
    (hU : U ∈ unitary (E →L[ℂ] E)) (K : E →L[ℂ] E) :
    ‖trc (P * (star U * K * U)) - trc (P * K)‖ ≤
      2 * finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) * ‖⁅U, P⁆‖ * ‖K‖ := by
  set p := finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E))
  set Q := U * P * star U with hQ
  set D := Q - P with hD
  have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hU
  have hU1 : ‖U‖ ≤ 1 := norm_le_one_of_mem_unitary hU
  have hUs1 : ‖star U‖ ≤ 1 := (norm_star U).le.trans hU1
  have hQp := isStarProjection_conj hP hU
  have hQQ : Q * Q = Q := hQp.isIdempotentElem.eq
  have h1Q : ‖1 - Q‖ ≤ 1 := IsStarProjection.norm_le _ hQp.one_sub
  have hDeq : D = ⁅U, P⁆ * star U := by
    rw [hD, hQ, Ring.lie_def, sub_mul, mul_assoc P U (star U), hUU, mul_one]
  have hnD : ‖D‖ ≤ ‖⁅U, P⁆‖ := by rw [hDeq]; exact norm_mul_le_of_le_one_right hUs1
  -- `Tr(P U^* K U) - Tr(P K) = Tr(D K)`
  have e1 : trc (P * (star U * K * U)) = trc (Q * K) := by
    calc trc (P * (star U * K * U)) = trc ((P * star U * K) * U) := by simp only [mul_assoc]
      _ = trc (U * (P * star U * K)) := trc_mul_comm _ _
      _ = trc (Q * K) := by rw [hQ]; simp only [mul_assoc]
  have e2 : trc (Q * K) - trc (P * K) = trc (D * K) := by rw [← trc_sub, hD, sub_mul]
  -- `D K = Q (D K) + (1 - Q) (D K)`
  have e3 : trc (D * K) = trc (Q * (D * K)) + trc ((1 - Q) * (D * K)) := by
    rw [← trc_add]; congr 1; noncomm_ring
  -- the first half: `Tr(Q D K) = Tr(P U^* D K U)`
  have a1 : ‖trc (Q * (D * K))‖ ≤ p * (‖⁅U, P⁆‖ * ‖K‖) := by
    have : trc (Q * (D * K)) = trc (P * (star U * D * K * U)) := by
      calc trc (Q * (D * K)) = trc (U * (P * star U * D * K)) := by rw [hQ]; simp only [mul_assoc]
        _ = trc ((P * star U * D * K) * U) := trc_mul_comm _ _
        _ = trc (P * (star U * D * K * U)) := by simp only [mul_assoc]
    rw [this]
    refine (norm_trc_P_mul_le hP _).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    calc ‖star U * D * K * U‖ ≤ ‖star U * D * K‖ := norm_mul_le_of_le_one_right hU1
      _ ≤ ‖star U * D‖ * ‖K‖ := norm_mul_le _ _
      _ ≤ ‖D‖ * ‖K‖ := by gcongr; exact norm_mul_le_of_le_one_left hUs1
      _ ≤ ‖⁅U, P⁆‖ * ‖K‖ := by gcongr
  -- the second half: `(1 - Q) D = -(1 - Q) P`
  have hQD : (1 - Q) * D = -((1 - Q) * P) := by
    rw [hD, mul_sub, sub_mul (1 : E →L[ℂ] E) Q Q, one_mul, hQQ, sub_self, zero_sub]
  have a2 : ‖trc ((1 - Q) * (D * K))‖ ≤ p * (‖⁅U, P⁆‖ * ‖K‖) := by
    have : trc ((1 - Q) * (D * K)) = -trc (P * (K * (1 - Q) * P)) := by
      calc trc ((1 - Q) * (D * K)) = trc (-((1 - Q) * P * K)) := by
            rw [← mul_assoc, hQD, neg_mul]
        _ = -trc ((1 - Q) * (P * K)) := by rw [trc_neg, mul_assoc]
        _ = -trc (P * K * (1 - Q)) := by rw [trc_mul_comm]
        _ = -trc (P * (K * (1 - Q) * P)) := by rw [mul_assoc, trc_P_mul_eq hP]
    rw [this, norm_neg]
    refine (norm_trc_P_mul_le hP _).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    have hQP : (1 - Q) * P = -((1 - Q) * D) := by rw [hQD, neg_neg]
    calc ‖K * (1 - Q) * P‖ = ‖K * ((1 - Q) * P)‖ := by rw [mul_assoc]
      _ ≤ ‖K‖ * ‖(1 - Q) * P‖ := norm_mul_le _ _
      _ ≤ ‖K‖ * ‖D‖ := by
          gcongr; rw [hQP, norm_neg]; exact norm_mul_le_of_le_one_left h1Q
      _ ≤ ‖⁅U, P⁆‖ * ‖K‖ := by rw [mul_comm]; gcongr
  rw [e1, e2, e3]
  calc ‖trc (Q * (D * K)) + trc ((1 - Q) * (D * K))‖
      ≤ ‖trc (Q * (D * K))‖ + ‖trc ((1 - Q) * (D * K))‖ := norm_add_le _ _
    _ ≤ p * (‖⁅U, P⁆‖ * ‖K‖) + p * (‖⁅U, P⁆‖ * ‖K‖) := add_le_add a1 a2
    _ = 2 * p * ‖⁅U, P⁆‖ * ‖K‖ := by ring

end Trace

/-! ## Step 3 of Lemma 6.17(i): four unitaries on `ran P` -/

section Four

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E] {P : E →L[ℂ] E}

omit [FiniteDimensional ℂ E] in
theorem norm_P_mul_mul_one_sub_le (hP : IsStarProjection P) (O : E →L[ℂ] E) :
    ‖P * O * (1 - P)‖ ≤ ‖⁅P, O⁆‖ := by
  have e : P * O * (1 - P) = ⁅P, O⁆ * (1 - P) := by
    rw [Ring.lie_def, sub_mul, mul_assoc O P, mul_sub P, mul_one, hP.isIdempotentElem.eq,
      sub_self, mul_zero, sub_zero]
  rw [e]; exact norm_mul_le_of_le_one_right (IsStarProjection.norm_le _ hP.one_sub)

omit [FiniteDimensional ℂ E] in
theorem norm_compress_le_one (hP : IsStarProjection P) {O : E →L[ℂ] E} (hO : ‖O‖ ≤ 1) :
    ‖P * O * P‖ ≤ 1 := (Det.norm_compress_le hP O).trans hO

omit [FiniteDimensional ℂ E] in
/-- Inserting `P` between four contractions: `‖P O₁O₂O₃O₄ P - Π (P Oᵢ P)‖ ≤ ∑_{i ≤ 3} ‖[P, Oᵢ]‖`. -/
theorem norm_compress4_sub_le (hP : IsStarProjection P) {O₁ O₂ O₃ O₄ : E →L[ℂ] E}
    (h₁ : ‖O₁‖ ≤ 1) (h₂ : ‖O₂‖ ≤ 1) (h₃ : ‖O₃‖ ≤ 1) (h₄ : ‖O₄‖ ≤ 1) :
    ‖P * (O₁ * O₂ * O₃ * O₄) * P - P * O₁ * P * (P * O₂ * P) * (P * O₃ * P) * (P * O₄ * P)‖ ≤
      ‖⁅P, O₁⁆‖ + ‖⁅P, O₂⁆‖ + ‖⁅P, O₃⁆‖ := by
  have hP1 : ‖P‖ ≤ 1 := IsStarProjection.norm_le P hP
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hPP' : ∀ X : E →L[ℂ] E, P * (P * X) = P * X := fun X => by rw [← mul_assoc, hPP]
  have e : P * (O₁ * O₂ * O₃ * O₄) * P - P * O₁ * P * (P * O₂ * P) * (P * O₃ * P) * (P * O₄ * P) =
      P * O₁ * (1 - P) * O₂ * O₃ * O₄ * P + P * O₁ * P * (P * O₂ * (1 - P)) * O₃ * O₄ * P +
        P * O₁ * P * (P * O₂ * P) * (P * O₃ * (1 - P)) * O₄ * P := by
    simp only [mul_sub, sub_mul, mul_one, mul_assoc, hPP']
    abel
  rw [e]
  have c1 : ‖P * O₁ * P‖ ≤ 1 := norm_compress_le_one hP h₁
  have c2 : ‖P * O₂ * P‖ ≤ 1 := norm_compress_le_one hP h₂
  have t1 : ‖P * O₁ * (1 - P) * O₂ * O₃ * O₄ * P‖ ≤ ‖⁅P, O₁⁆‖ := by
    refine (norm_mul_le_of_le_one_right hP1).trans ?_
    refine (norm_mul_le_of_le_one_right h₄).trans ?_
    refine (norm_mul_le_of_le_one_right h₃).trans ?_
    refine (norm_mul_le_of_le_one_right h₂).trans ?_
    exact norm_P_mul_mul_one_sub_le hP O₁
  have t2 : ‖P * O₁ * P * (P * O₂ * (1 - P)) * O₃ * O₄ * P‖ ≤ ‖⁅P, O₂⁆‖ := by
    refine (norm_mul_le_of_le_one_right hP1).trans ?_
    refine (norm_mul_le_of_le_one_right h₄).trans ?_
    refine (norm_mul_le_of_le_one_right h₃).trans ?_
    refine (norm_mul_le_of_le_one_left c1).trans ?_
    exact norm_P_mul_mul_one_sub_le hP O₂
  have t3 : ‖P * O₁ * P * (P * O₂ * P) * (P * O₃ * (1 - P)) * O₄ * P‖ ≤ ‖⁅P, O₃⁆‖ := by
    refine (norm_mul_le_of_le_one_right hP1).trans ?_
    refine (norm_mul_le_of_le_one_right h₄).trans ?_
    refine (norm_mul_le_of_le_one_left (norm_mul_le_one c1 c2)).trans ?_
    exact norm_P_mul_mul_one_sub_le hP O₃
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)

omit [FiniteDimensional ℂ E] in
theorem detP_compress4 (hP : IsStarProjection P) (O₁ O₂ O₃ O₄ : E →L[ℂ] E) :
    detP P (P * O₁ * P * (P * O₂ * P) * (P * O₃ * P) * (P * O₄ * P)) =
      detP P O₁ * detP P O₂ * detP P O₃ * detP P O₄ := by
  rw [detP_mul_of_mapsTo hP _ _ fun v _ => Det.compress_mem_range P O₄ v,
    detP_mul_of_mapsTo hP _ _ fun v _ => Det.compress_mem_range P O₃ v,
    detP_compress_mul_compress hP, detP_compress hP, detP_compress hP]

omit [FiniteDimensional ℂ E] in
theorem norm_lie_P_star_eq (hP : IsStarProjection P) (U : E →L[ℂ] E) :
    ‖⁅P, star U⁆‖ = ‖⁅P, U⁆‖ := by
  have : ⁅P, star U⁆ = -star ⁅P, U⁆ := by
    simp only [Ring.lie_def, star_sub, star_mul, hP.isSelfAdjoint.star_eq]; abel
  rw [this, norm_neg]; exact norm_star ⁅P, U⁆

/-- **Lemma 6.17(i), Step 3**: `|det_P (U^* O U O^*) - 1| ≤ p (3 ‖[P, U]‖ + 2 ‖[P, O]‖)`. -/
theorem norm_detP_four_sub_one_le (hP : IsStarProjection P) {U O : E →L[ℂ] E}
    (hU : U ∈ unitary (E →L[ℂ] E)) (hO : O ∈ unitary (E →L[ℂ] E)) :
    ‖detP P (star U * O * U * star O) - 1‖ ≤
      finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E)) * (3 * ‖⁅P, U⁆‖ + 2 * ‖⁅P, O⁆‖) := by
  set p := finrank ℂ (LinearMap.range (P : E →ₗ[ℂ] E))
  have hU1 : ‖U‖ ≤ 1 := norm_le_one_of_mem_unitary hU
  have hO1 : ‖O‖ ≤ 1 := norm_le_one_of_mem_unitary hO
  have hUs1 : ‖star U‖ ≤ 1 := (norm_star U).le.trans hU1
  have hOs1 : ‖star O‖ ≤ 1 := (norm_star O).le.trans hO1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  -- the compression of the product against the product of the compressions
  have h4 : ‖detP P (star U * O * U * star O) -
      detP P (star U) * detP P O * detP P U * detP P (star O)‖ ≤
        p * (‖⁅P, star U⁆‖ + ‖⁅P, O⁆‖ + ‖⁅P, U⁆‖) := by
    rw [← detP_compress hP (star U * O * U * star O), ← detP_compress4 hP]
    refine (norm_detP_sub_detP_le_of_norm_le_one hP
      (norm_compress_le_one hP (norm_mul_le_one (norm_mul_le_one (norm_mul_le_one hUs1 hO1) hU1)
        hOs1))
      (norm_mul_le_one (norm_mul_le_one (norm_mul_le_one (norm_compress_le_one hP hUs1)
        (norm_compress_le_one hP hO1)) (norm_compress_le_one hP hU1))
          (norm_compress_le_one hP hOs1))).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_compress4_sub_le hP hUs1 hO1 hU1 hOs1) hp0
  have h13 := norm_detP_star_mul_detP_sub_one_le hP hU
  have h42 := norm_detP_star_mul_detP_sub_one_le hP hO
  have hd2 : ‖detP P O‖ ≤ 1 := norm_detP_le_one_of_mem_unitary hP hO
  have hd4 : ‖detP P (star O)‖ ≤ 1 := norm_detP_le_one_of_mem_unitary hP (Unitary.star_mem hO)
  have hprod : ‖detP P (star U) * detP P O * detP P U * detP P (star O) - 1‖ ≤
      p * ‖⁅P, U⁆‖ + p * ‖⁅P, O⁆‖ := by
    have e : detP P (star U) * detP P O * detP P U * detP P (star O) - 1 =
        (detP P (star U) * detP P U - 1) * (detP P (star O) * detP P O) +
          (detP P (star O) * detP P O - 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ h42)
    rw [norm_mul]
    have : ‖detP P (star O) * detP P O‖ ≤ 1 := by
      rw [norm_mul]; nlinarith [norm_nonneg (detP P (star O)), norm_nonneg (detP P O)]
    exact (mul_le_of_le_one_right (norm_nonneg _) this).trans h13
  rw [norm_lie_P_star_eq hP] at h4
  calc ‖detP P (star U * O * U * star O) - 1‖
      ≤ ‖detP P (star U * O * U * star O) -
          detP P (star U) * detP P O * detP P U * detP P (star O)‖ +
        ‖detP P (star U) * detP P O * detP P U * detP P (star O) - 1‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ p * (‖⁅P, U⁆‖ + ‖⁅P, O⁆‖ + ‖⁅P, U⁆‖) + (p * ‖⁅P, U⁆‖ + p * ‖⁅P, O⁆‖) := add_le_add h4 hprod
    _ = p * (3 * ‖⁅P, U⁆‖ + 2 * ‖⁅P, O⁆‖) := by ring

end Four

/-! ## Lemma 6.17 in the setting -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

omit [FiniteDimensional ℂ E] in
/-- `e^{it(A + B)} = e^{itA} e^{itB}` for commuting `A`, `B`. -/
theorem expI_add_of_commute {A B : E →L[ℂ] E} (h : Commute A B) (t : ℝ) :
    expI t (A + B) = expI t A * expI t B := by
  let _ : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
  rw [expI_def, expI_def, expI_def, smul_add, smul_add]
  exact NormedSpace.exp_add_of_commute (((h.smul_left I).smul_right I).smul_left t |>.smul_right t)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem expI_eq_exp (t : ℝ) (A : E →L[ℂ] E) :
    expI t A = NormedSpace.exp ((I * (t : ℂ)) • A) := (exp_I_mul_smul t A).symm

namespace Setting

variable (S : Setting E)

theorem expI_two_pi_Qminus : expI (2 * π) S.Qminus = 1 := by
  rw [← exp_two_pi_I_smul]; exact S.exp_Qminus

theorem expI_two_pi_Qplus : expI (2 * π) S.Qplus = 1 := by
  rw [← exp_two_pi_I_smul]; exact S.exp_Qplus

variable {S} {ε : ℝ}

/-- **Lemma 6.17(i), Step 1**: `‖e^{2πi(Q - K₋)} - e^{2πiQ̄₋}‖ ≤ 4π² ε`. -/
theorem SepBounds.norm_step1_le (h : S.SepBounds ε) :
    ‖expI (2 * π) (S.Q - S.Kminus) - S.Ominus‖ ≤ 4 * π ^ 2 * ε := by
  have hQK : S.Q - S.Kminus = S.QbarMinus + (S.Qmid + S.Qplus) := by
    simp only [Setting.Q, Setting.QbarMinus]; abel
  have h1 : expI (2 * π) (S.Qmid + S.Qplus) = 1 := by
    rw [expI_add_of_commute S.comm_Qmid_Qplus, S.expI_two_pi_Qmid, S.expI_two_pi_Qplus, mul_one]
  have hb := norm_expI_add_sub_le _ S.isSelfAdjoint_QbarMinus (S.Qmid_sa.add S.Qplus_sa) (2 * π)
  rw [← hQK, h1, mul_one, ← S.Ominus_eq] at hb
  have a11 := h.A11
  calc _ ≤ (2 * π) ^ 2 / 2 * ‖⁅S.QbarMinus, S.Qmid + S.Qplus⁆‖ := hb
    _ ≤ (2 * π) ^ 2 / 2 * (2 * ε) := by gcongr
    _ = 4 * π ^ 2 * ε := by ring

/-- `‖e^{2πi(Q₊ + T₊)} - 1‖ ≤ (4π² + 1) ε` (Step 2 of Lemma 6.17(i), from (U4)). -/
theorem SepBounds.norm_expI_QplusTplus_sub_one_le (h : S.SepBounds ε)
    (hU4 : ‖NormedSpace.exp ((2 * π * I) • (S.Q + S.Tplus)) - 1‖ ≤ ε) :
    ‖expI (2 * π) (S.Qplus + S.Tplus) - 1‖ ≤ (4 * π ^ 2 + 1) * ε := by
  rw [exp_two_pi_I_smul] at hU4
  have hsplit : S.Q + S.Tplus = (S.Qminus + S.Qmid) + (S.Qplus + S.Tplus) := by
    simp only [Setting.Q]; abel
  have h1 : expI (2 * π) (S.Qminus + S.Qmid) = 1 := by
    rw [expI_add_of_commute S.comm_Qminus_Qmid, S.expI_two_pi_Qminus, S.expI_two_pi_Qmid,
      mul_one]
  have hb := norm_expI_add_sub_le _ (S.Qminus_sa.add S.Qmid_sa) (S.Qplus_sa.add S.Tplus_sa)
    (2 * π)
  rw [← hsplit, h1, one_mul] at hb
  have a14 := h.A14
  have hb' : ‖expI (2 * π) (S.Q + S.Tplus) - expI (2 * π) (S.Qplus + S.Tplus)‖ ≤
      4 * π ^ 2 * ε := by
    refine hb.trans ?_
    calc (2 * π) ^ 2 / 2 * ‖⁅S.Qminus + S.Qmid, S.Qplus + S.Tplus⁆‖
        ≤ (2 * π) ^ 2 / 2 * (2 * ε) := by gcongr
      _ = 4 * π ^ 2 * ε := by ring
  calc ‖expI (2 * π) (S.Qplus + S.Tplus) - 1‖
      ≤ ‖expI (2 * π) (S.Qplus + S.Tplus) - expI (2 * π) (S.Q + S.Tplus)‖ +
        ‖expI (2 * π) (S.Q + S.Tplus) - 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4 * π ^ 2 * ε + ε := by rw [norm_sub_rev]; exact add_le_add hb' hU4
    _ = (4 * π ^ 2 + 1) * ε := by ring

/-- **Lemma 6.17(i), Step 2**: `‖U^* e^{2πi(Q - K₋)} U - e^{2πiQ̄^U₋}‖ ≤ (20π² + 1) ε`. -/
theorem SepBounds.norm_step2_le (h : S.SepBounds ε)
    (hU4 : ‖NormedSpace.exp ((2 * π * I) • (S.Q + S.Tplus)) - 1‖ ≤ ε) :
    ‖star S.U * expI (2 * π) (S.Q - S.Kminus) * S.U - expI (2 * π) S.QbarUMinus‖ ≤
      (20 * π ^ 2 + 1) * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hU4
  rw [conj_expI _ S.U_unitary]
  have hconj : star S.U * (S.Q - S.Kminus) * S.U =
      S.QbarUMinus + (S.Qmid + (S.Qplus + S.Tplus)) := by
    have ht := S.transport
    have e1 : star S.U * (S.Q - S.Kminus) * S.U = star S.U * S.Q * S.U - S.KUminus := by
      rw [mul_sub, sub_mul, Setting.KUminus]
    rw [e1, show star S.U * S.Q * S.U = S.Q + (S.Tminus + S.Tplus) by
      rw [← ht, Setting.Q]; abel]
    simp only [Setting.Q, Setting.QbarUMinus]; abel
  rw [hconj]
  have hX := S.isSelfAdjoint_QbarUMinus
  have hY := S.Qmid_sa
  have hZ : IsSelfAdjoint (S.Qplus + S.Tplus) := S.Qplus_sa.add S.Tplus_sa
  have b1 := norm_expI_add_sub_le _ hX (hY.add hZ) (2 * π)
  have b2 := norm_expI_add_sub_le _ hY hZ (2 * π)
  rw [S.expI_two_pi_Qmid, one_mul] at b2
  have a12 : ‖⁅S.QbarUMinus, S.Qmid + (S.Qplus + S.Tplus)⁆‖ ≤ 7 * ε := by
    have := h.A12; rwa [add_assoc] at this
  have a13 := h.A13
  have hZ1 := h.norm_expI_QplusTplus_sub_one_le hU4
  have hXu : ‖expI (2 * π) S.QbarUMinus‖ ≤ 1 := norm_expI_le _ hX _
  calc ‖expI (2 * π) (S.QbarUMinus + (S.Qmid + (S.Qplus + S.Tplus))) -
        expI (2 * π) S.QbarUMinus‖
      ≤ ‖expI (2 * π) (S.QbarUMinus + (S.Qmid + (S.Qplus + S.Tplus))) -
          expI (2 * π) S.QbarUMinus * expI (2 * π) (S.Qmid + (S.Qplus + S.Tplus))‖ +
        ‖expI (2 * π) S.QbarUMinus * expI (2 * π) (S.Qmid + (S.Qplus + S.Tplus)) -
          expI (2 * π) S.QbarUMinus‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (2 * π) ^ 2 / 2 * (7 * ε) +
        (‖expI (2 * π) (S.Qmid + (S.Qplus + S.Tplus)) - expI (2 * π) (S.Qplus + S.Tplus)‖ +
          ‖expI (2 * π) (S.Qplus + S.Tplus) - 1‖) := by
        refine add_le_add (b1.trans (by gcongr)) ?_
        rw [← mul_sub_one]
        refine (norm_mul_le_of_le_one_left hXu).trans ?_
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (2 * π) ^ 2 / 2 * (7 * ε) + ((2 * π) ^ 2 / 2 * ε + (4 * π ^ 2 + 1) * ε) :=
        add_le_add le_rfl (add_le_add (b2.trans (by gcongr)) hZ1)
    _ = (20 * π ^ 2 + 1) * ε := by ring

/-- **Lemma 6.17(i), Steps 1–2**: `‖𝓜₋(2π) - U^* e^{2πiQ̄₋} U e^{-2πiQ̄₋}‖ ≤ (24π² + 1) ε`. -/
theorem SepBounds.norm_Mminus_two_pi_sub_le (h : S.SepBounds ε)
    (hU4 : ‖NormedSpace.exp ((2 * π * I) • (S.Q + S.Tplus)) - 1‖ ≤ ε) :
    ‖S.Mminus (2 * π) - star S.U * S.Ominus * S.U * star S.Ominus‖ ≤ (24 * π ^ 2 + 1) * ε := by
  have hU1 : ‖S.U‖ ≤ 1 := norm_le_one_of_mem_unitary S.U_unitary
  have hUs1 : ‖star S.U‖ ≤ 1 := (norm_star S.U).le.trans hU1
  have hst : star S.Ominus = expI (-(2 * π)) S.QbarMinus := by
    rw [S.Ominus_eq, star_expI _ S.isSelfAdjoint_QbarMinus]
  have e : S.Mminus (2 * π) - star S.U * S.Ominus * S.U * star S.Ominus =
      (expI (2 * π) S.QbarUMinus - star S.U * S.Ominus * S.U) * expI (-(2 * π)) S.QbarMinus := by
    rw [S.Mminus_eq, hst, sub_mul]
  rw [e, norm_mul_expI _ S.isSelfAdjoint_QbarMinus]
  have s1 := h.norm_step1_le
  have s2 := h.norm_step2_le hU4
  have s3 : ‖star S.U * expI (2 * π) (S.Q - S.Kminus) * S.U - star S.U * S.Ominus * S.U‖ ≤
      4 * π ^ 2 * ε := by
    rw [← sub_mul, ← mul_sub]
    exact (norm_mul_le_of_le_one_right hU1).trans ((norm_mul_le_of_le_one_left hUs1).trans s1)
  calc ‖expI (2 * π) S.QbarUMinus - star S.U * S.Ominus * S.U‖
      ≤ ‖expI (2 * π) S.QbarUMinus - star S.U * expI (2 * π) (S.Q - S.Kminus) * S.U‖ +
        ‖star S.U * expI (2 * π) (S.Q - S.Kminus) * S.U - star S.U * S.Ominus * S.U‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (20 * π ^ 2 + 1) * ε + 4 * π ^ 2 * ε := by rw [norm_sub_rev]; exact add_le_add s2 s3
    _ = (24 * π ^ 2 + 1) * ε := by ring

variable (S)

/-- **Lemma 6.17(i), Step 3**, in the setting:
`|det_P 𝒵(2π) - 1| ≤ p (‖𝓜₋(2π) - U^* O₋ U O₋^*‖ + 3 ‖[P, U]‖ + 2 ‖[P, O₋]‖)`. -/
theorem norm_detP_Zc_two_pi_sub_one_le :
    ‖detP S.P (S.Zc (2 * π)) - 1‖ ≤
      S.p * (‖S.Mminus (2 * π) - star S.U * S.Ominus * S.U * star S.Ominus‖ +
        3 * ‖⁅S.P, S.U⁆‖ + 2 * ‖⁅S.P, S.Ominus⁆‖) := by
  have hP := S.isStarProjection_P
  have hW : star S.U * S.Ominus * S.U * star S.Ominus ∈ unitary (E →L[ℂ] E) :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem S.U_unitary)
      S.Ominus_mem_unitary) S.U_unitary) (Unitary.star_mem S.Ominus_mem_unitary)
  have h1 : ‖detP S.P (S.Zc (2 * π)) - detP S.P (star S.U * S.Ominus * S.U * star S.Ominus)‖ ≤
      S.p * ‖S.Mminus (2 * π) - star S.U * S.Ominus * S.U * star S.Ominus‖ := by
    rw [Setting.Zc, detP_compress hP]
    exact norm_detP_sub_detP_le_of_norm_le_one hP
      (norm_le_one_of_mem_unitary (S.Mminus_mem_unitary _)) (norm_le_one_of_mem_unitary hW)
  have h2 := norm_detP_four_sub_one_le hP S.U_unitary S.Ominus_mem_unitary
  calc ‖detP S.P (S.Zc (2 * π)) - 1‖
      ≤ ‖detP S.P (S.Zc (2 * π)) - detP S.P (star S.U * S.Ominus * S.U * star S.Ominus)‖ +
        ‖detP S.P (star S.U * S.Ominus * S.U * star S.Ominus) - 1‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ S.p * ‖S.Mminus (2 * π) - star S.U * S.Ominus * S.U * star S.Ominus‖ +
        S.p * (3 * ‖⁅S.P, S.U⁆‖ + 2 * ‖⁅S.P, S.Ominus⁆‖) := add_le_add h1 h2
    _ = _ := by ring

theorem detP_expI {A : E →L[ℂ] E} (hA : Commute A S.P) (t : ℝ) :
    detP S.P (expI t A) = Complex.exp (I * t * trc (S.P * A)) := by
  rw [expI_eq_exp, detP_exp S.isStarProjection_P (hA.smul_left _)]
  congr 1
  show trc (S.P * ((I * (t : ℂ)) • A)) = _
  rw [mul_smul_comm, trc_smul]

/-- **Lemma 6.17(ii)**: `det_P 𝒴(2π) = e^{2πi Tr(P T̃)}` exactly. -/
theorem detP_Yc_two_pi :
    detP S.P (S.Yc (2 * π)) = Complex.exp (2 * π * I * trc (S.P * S.Ttilde)) := by
  have hP := S.isStarProjection_P
  rw [Setting.Yc, detP_compress hP,
    detP_mul hP _ (S.commute_P_expI_Qbar (-(2 * π))).symm,
    S.detP_expI S.commute_P_Ac.symm, S.detP_expI S.commute_Qbar_P, ← Complex.exp_add]
  congr 1
  have hPT : trc (S.P * (S.P * S.Ttilde * S.P)) = trc (S.P * S.Ttilde) := by
    rw [← mul_assoc, ← mul_assoc, hP.isIdempotentElem.eq, mul_assoc, ← trc_P_mul_eq hP]
  rw [Setting.Ac, mul_add, trc_add, hPT]
  push_cast
  ring

/-- **Lemma 6.17(iii)**: `|e^{2πi Tr(P T̃)} - 1| ≤ p ‖𝒴(2π) - 𝒵(2π)‖ + |det_P 𝒵(2π) - 1|`. -/
theorem norm_cexp_trc_Ttilde_sub_one_le :
    ‖Complex.exp (2 * π * I * trc (S.P * S.Ttilde)) - 1‖ ≤
      S.p * ‖S.Yc (2 * π) - S.Zc (2 * π)‖ + ‖detP S.P (S.Zc (2 * π)) - 1‖ := by
  have hP := S.isStarProjection_P
  have hY : ‖S.Yc (2 * π)‖ ≤ 1 := by
    rw [S.Yc_eq]
    exact norm_mul_le_one (IsStarProjection.norm_le _ hP) (S.norm_Wc_le _)
  have hZ : ‖S.Zc (2 * π)‖ ≤ 1 :=
    norm_compress_le_one hP (norm_le_one_of_mem_unitary (S.Mminus_mem_unitary _))
  rw [← S.detP_Yc_two_pi]
  calc ‖detP S.P (S.Yc (2 * π)) - 1‖
      ≤ ‖detP S.P (S.Yc (2 * π)) - detP S.P (S.Zc (2 * π))‖ + ‖detP S.P (S.Zc (2 * π)) - 1‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ S.p * ‖S.Yc (2 * π) - S.Zc (2 * π)‖ + ‖detP S.P (S.Zc (2 * π)) - 1‖ := by
        gcongr; exact norm_detP_sub_detP_le_of_norm_le_one hP hY hZ

/-- **Lemma 6.17(iii)**, the integer: `Tr(P T̃)` is real and within a quarter of
`|e^{2πi Tr(P T̃)} - 1|` of an integer. -/
theorem exists_int_norm_trc_Ttilde_sub_le :
    ∃ n : ℤ, ‖trc (S.P * S.Ttilde) - n‖ ≤
      ‖Complex.exp (2 * π * I * trc (S.P * S.Ttilde)) - 1‖ / 4 := by
  have hre := trc_P_mul_eq_re S.isStarProjection_P S.isSelfAdjoint_Ttilde
  obtain ⟨n, hn⟩ := exists_int_abs_sub_le (trc (S.P * S.Ttilde)).re
  refine ⟨n, ?_⟩
  rw [hre, ← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hn

/-- **Lemma 6.17(iv)**: `Tr(P T̃) - Tr(P T₋) = Tr(P K₋) - Tr(P K^U₋)`, and
`|Tr(P T̃) - Tr(P T₋)| ≤ 2p ‖[U, P]‖ ‖K₋‖`. -/
theorem trc_Ttilde_sub_trc_Tminus :
    trc (S.P * S.Ttilde) - trc (S.P * S.Tminus) = trc (S.P * S.Kminus) - trc (S.P * S.KUminus) := by
  rw [Setting.Ttilde, mul_add, mul_sub, trc_add, trc_sub]; ring

theorem norm_trc_Ttilde_sub_trc_Tminus_le :
    ‖trc (S.P * S.Ttilde) - trc (S.P * S.Tminus)‖ ≤ 2 * S.p * ‖⁅S.U, S.P⁆‖ * ‖S.Kminus‖ := by
  rw [S.trc_Ttilde_sub_trc_Tminus, norm_sub_rev]
  exact norm_trc_conj_sub_le S.isStarProjection_P S.U_unitary S.Kminus

end Setting

end HRTorus.IndexCore
