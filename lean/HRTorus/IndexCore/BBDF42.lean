import HRTorus.IndexCore.Commutation

/-!
# Lemma A.6, Lemma 6.14 and Corollary 6.15

Written by Claude Opus 5.5 (an AI model), 2026-10-23. The paper is the HR paper (`papers/hr/`):
Appendix A (`lem:bbdf41`, Lemma A.6) and Section 6 (`lem:bbdf42`, Lemma 6.14;
`cor:Zcommute`, Corollary 6.15).

* **Lemma A.6** (BBDF's Lemma 4.1, sharpened): (i) `‖P V ψ‖² ≥ (1 - ‖[V, P]‖) ‖ψ‖²` for
  `ψ ∈ ran P`; (ii) if `‖P V ψ‖², ‖P V^* ψ‖² ≥ (1 - δ²) ‖ψ‖²` on `ran P`, then `‖(1 - P) V P‖`,
  `‖P V (1 - P)‖` and `‖[V, P]‖` are at most `δ`.
* **Lemma 6.14**, quantitative, in the paper's form: with `a = min(√(1 - ε₀ - 2ε_c) - ε₁,
  √(1 - ε₀) - ε₂) > 0`, `‖[V₋, P]‖ ≤ √(1 - a²)`; and the form the proof of Lemma 6.14 then
  uses: if `ε̄ = ε₀ + 2ε_c + ε₁ + ε₂ ≤ 1/2`, then `‖[V₋, P]‖ ≤ √(2 ε̄)`. The `ε`'s enter as
  upper bounds (`‖…‖ ≤ ε_i`), which is the paper's statement made monotone.
* **Corollary 6.15**, instantiated with explicit constants: for `φ ∈ [0, 2π]`,
  `‖[𝓜₋(φ), P]‖ ≤ √(2 c_𝓜 ε)` with `c_𝓜 = 324π² + 4`, and `‖[e^{2πiQ̄₋}, P]‖ ≤ √(2 c_O ε)` with
  `c_O = 44π² + 2`, whenever `c ε ≤ 1/2`.
-/

open scoped InnerProductSpace ComplexConjugate Real
open Complex (I)

noncomputable section

namespace HRTorus.IndexCore

/-! ## Lemma A.6 -/

section BBDF41

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {P V : E →L[ℂ] E}

theorem starProj_inner (hP : IsStarProjection P) (x y : E) : ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ :=
  hP.isSelfAdjoint.isSymmetric x y

theorem starProj_apply_apply (hP : IsStarProjection P) (x : E) : P (P x) = P x := by
  rw [← mul_apply_eq_comp, hP.isIdempotentElem.eq]

theorem starProj_apply_one_sub (hP : IsStarProjection P) (x : E) : P ((1 - P) x) = 0 := by
  rw [sub_apply, one_apply_eq_self, map_sub, starProj_apply_apply hP, sub_self]

theorem one_sub_apply_one_sub (hP : IsStarProjection P) (x : E) :
    (1 - P) ((1 - P) x) = (1 - P) x := by
  rw [sub_apply (1 : E →L[ℂ] E) P ((1 - P) x), one_apply_eq_self, starProj_apply_one_sub hP,
    sub_zero]

theorem norm_apply_le_of_starProj (hP : IsStarProjection P) (x : E) : ‖P x‖ ≤ ‖x‖ :=
  (P.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) (IsStarProjection.norm_le P hP))

/-- Pythagoras for a star projection: `‖x‖² = ‖P x‖² + ‖(1 - P) x‖²`. -/
theorem norm_sq_eq_add_starProj (hP : IsStarProjection P) (x : E) :
    ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖(1 - P) x‖ ^ 2 := by
  have h0 : ⟪P x, (1 - P) x⟫_ℂ = 0 := by
    rw [starProj_inner hP, starProj_apply_one_sub hP, inner_zero_right]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) ((1 - P) x) h0
  have hx : P x + (1 - P) x = x := by rw [sub_apply, one_apply_eq_self]; abel
  rw [hx] at h
  rw [sq, sq, sq]; exact h

/-- `‖X‖ = ‖X^*‖`-type bound used twice: `‖[X, P]‖ ≤ 2 ‖X‖` for a projection `P`. -/
theorem norm_lie_starProj_le (hP : IsStarProjection P) (X : E →L[ℂ] E) :
    ‖⁅X, P⁆‖ ≤ 2 * ‖X‖ := by
  have hP1 : ‖P‖ ≤ 1 := IsStarProjection.norm_le P hP
  rw [Ring.lie_def]
  calc ‖X * P - P * X‖ ≤ ‖X * P‖ + ‖P * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖P‖ + ‖P‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖X‖ * 1 + 1 * ‖X‖ := by gcongr
    _ = 2 * ‖X‖ := by ring

/-- `‖[X, P]‖ ≤ 2 ‖X - Y‖ + ‖[Y, P]‖`. -/
theorem norm_lie_starProj_le_of_sub (hP : IsStarProjection P) (X Y : E →L[ℂ] E) :
    ‖⁅X, P⁆‖ ≤ 2 * ‖X - Y‖ + ‖⁅Y, P⁆‖ := by
  have e : ⁅X, P⁆ = ⁅X - Y, P⁆ + ⁅Y, P⁆ := by simp only [Ring.lie_def]; noncomm_ring
  rw [e]
  exact (norm_add_le _ _).trans (by linarith [norm_lie_starProj_le hP (X - Y)])

/-- **Lemma A.6(i)**: for `ψ ∈ ran P`, `‖P V ψ‖² ≥ (1 - ‖[V, P]‖) ‖ψ‖²`. -/
theorem bbdf41_i (hP : IsStarProjection P) (hV : V ∈ unitary (E →L[ℂ] E)) {ψ : E}
    (hψ : P ψ = ψ) : (1 - ‖⁅V, P⁆‖) * ‖ψ‖ ^ 2 ≤ ‖P (V ψ)‖ ^ 2 := by
  have h1 : ‖P (V ψ)‖ ^ 2 = RCLike.re ⟪V ψ, P (V ψ)⟫_ℂ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), starProj_inner hP, starProj_apply_apply hP]
  have h2 : P (V ψ) = V ψ + ⁅P, V⁆ ψ := by
    rw [Ring.lie_def, sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, hψ]; abel
  have h3 : ‖V ψ‖ = ‖ψ‖ := ContinuousLinearMap.norm_map_of_mem_unitary hV ψ
  have h4 : |RCLike.re ⟪V ψ, ⁅P, V⁆ ψ⟫_ℂ| ≤ ‖⁅V, P⁆‖ * ‖ψ‖ ^ 2 := by
    refine (RCLike.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [h3]
    calc ‖ψ‖ * ‖⁅P, V⁆ ψ‖ ≤ ‖ψ‖ * (‖⁅P, V⁆‖ * ‖ψ‖) := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖⁅V, P⁆‖ * ‖ψ‖ ^ 2 := by rw [norm_lie_comm]; ring
  rw [h1, h2, inner_add_right, map_add, inner_self_eq_norm_sq, h3]
  have h5 := neg_abs_le (RCLike.re ⟪V ψ, ⁅P, V⁆ ψ⟫_ℂ)
  nlinarith

/-- **Lemma A.6(i)** for `V^*`: `‖P V^* ψ‖² ≥ (1 - ‖[V, P]‖) ‖ψ‖²` on `ran P`. -/
theorem bbdf41_i_star (hP : IsStarProjection P) (hV : V ∈ unitary (E →L[ℂ] E)) {ψ : E}
    (hψ : P ψ = ψ) : (1 - ‖⁅V, P⁆‖) * ‖ψ‖ ^ 2 ≤ ‖P (star V ψ)‖ ^ 2 := by
  have e : ‖⁅star V, P⁆‖ = ‖⁅V, P⁆‖ := by
    have : ⁅star V, P⁆ = -star ⁅V, P⁆ := by
      simp only [Ring.lie_def, star_sub, star_mul, hP.isSelfAdjoint.star_eq]; abel
    rw [this, norm_neg]; exact norm_star ⁅V, P⁆
  rw [← e]
  exact bbdf41_i hP (Unitary.star_mem hV) hψ

/-- The pointwise half of Lemma A.6(ii): `‖(1 - P) V P φ‖ ≤ δ ‖P φ‖`. -/
theorem norm_one_sub_apply_le (hP : IsStarProjection P) (hV : V ∈ unitary (E →L[ℂ] E))
    {δ : ℝ} (hδ : 0 ≤ δ) (h1 : ∀ ψ, P ψ = ψ → (1 - δ ^ 2) * ‖ψ‖ ^ 2 ≤ ‖P (V ψ)‖ ^ 2) (φ : E) :
    ‖(1 - P) (V (P φ))‖ ≤ δ * ‖P φ‖ := by
  have hψ : P (P φ) = P φ := starProj_apply_apply hP φ
  have hpy := norm_sq_eq_add_starProj hP (V (P φ))
  rw [ContinuousLinearMap.norm_map_of_mem_unitary hV] at hpy
  have h := h1 (P φ) hψ
  have hsq : ‖(1 - P) (V (P φ))‖ ^ 2 ≤ (δ * ‖P φ‖) ^ 2 := by nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).1 hsq

/-- **Lemma A.6(ii)**: if `‖P V ψ‖² ≥ (1 - δ²) ‖ψ‖²` and `‖P V^* ψ‖² ≥ (1 - δ²) ‖ψ‖²` for every
`ψ ∈ ran P`, then `‖(1 - P) V P‖ ≤ δ`, `‖P V (1 - P)‖ ≤ δ` and `‖[V, P]‖ ≤ δ`. -/
theorem bbdf41_ii (hP : IsStarProjection P) (hV : V ∈ unitary (E →L[ℂ] E)) {δ : ℝ} (hδ : 0 ≤ δ)
    (h1 : ∀ ψ, P ψ = ψ → (1 - δ ^ 2) * ‖ψ‖ ^ 2 ≤ ‖P (V ψ)‖ ^ 2)
    (h2 : ∀ ψ, P ψ = ψ → (1 - δ ^ 2) * ‖ψ‖ ^ 2 ≤ ‖P (star V ψ)‖ ^ 2) :
    ‖(1 - P) * V * P‖ ≤ δ ∧ ‖P * V * (1 - P)‖ ≤ δ ∧ ‖⁅V, P⁆‖ ≤ δ := by
  have hVs : star V ∈ unitary (E →L[ℂ] E) := Unitary.star_mem hV
  have p1 : ∀ φ, ‖(1 - P) (V (P φ))‖ ≤ δ * ‖P φ‖ := norm_one_sub_apply_le hP hV hδ h1
  have p2 : ∀ φ, ‖(1 - P) (star V (P φ))‖ ≤ δ * ‖P φ‖ := norm_one_sub_apply_le hP hVs hδ h2
  have n1 : ‖(1 - P) * V * P‖ ≤ δ := by
    refine ContinuousLinearMap.opNorm_le_bound _ hδ fun φ => ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    exact (p1 φ).trans (by gcongr; exact norm_apply_le_of_starProj hP φ)
  have n2' : ‖(1 - P) * star V * P‖ ≤ δ := by
    refine ContinuousLinearMap.opNorm_le_bound _ hδ fun φ => ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    exact (p2 φ).trans (by gcongr; exact norm_apply_le_of_starProj hP φ)
  have n2 : ‖P * V * (1 - P)‖ ≤ δ := by
    have : P * V * (1 - P) = star ((1 - P) * star V * P) := by
      simp only [star_mul, star_star, star_sub, star_one, hP.isSelfAdjoint.star_eq, mul_assoc]
    rw [this]; exact (norm_star ((1 - P) * star V * P)).le.trans n2'
  refine ⟨n1, n2, ContinuousLinearMap.opNorm_le_bound _ hδ fun φ => ?_⟩
  -- `[V, P] φ = (1 - P) V P φ - P V (1 - P) φ`, two orthogonal vectors
  set x := (1 - P) (V (P φ)) with hx
  set y := P (V ((1 - P) φ)) with hy
  have hdec : ⁅V, P⁆ φ = x + -y := by
    rw [hx, hy, Ring.lie_def, sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, sub_apply,
      one_apply_eq_self, sub_apply, one_apply_eq_self, map_sub, map_sub]
    abel
  have horth : ⟪x, -y⟫_ℂ = 0 := by
    rw [inner_neg_right, hx, hy,
      ← starProj_inner hP ((1 - P) (V (P φ))) (V ((1 - P) φ)), starProj_apply_one_sub hP,
      inner_zero_left, neg_zero]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x (-y) horth
  rw [norm_neg, ← hdec] at hpy
  have hxb : ‖x‖ ≤ δ * ‖P φ‖ := p1 φ
  have hyb : ‖y‖ ≤ δ * ‖(1 - P) φ‖ := by
    have : y = (P * V * (1 - P)) ((1 - P) φ) := by
      rw [hy, mul_apply_eq_comp, mul_apply_eq_comp, one_sub_apply_one_sub hP]
    rw [this]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
  have hφ := norm_sq_eq_add_starProj hP φ
  have hsq : ‖⁅V, P⁆ φ‖ ^ 2 ≤ (δ * ‖φ‖) ^ 2 := by
    have a1 : ‖x‖ ^ 2 ≤ (δ * ‖P φ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxb 2
    have a2 : ‖y‖ ^ 2 ≤ (δ * ‖(1 - P) φ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyb 2
    rw [sq ‖⁅V, P⁆ φ‖, hpy]
    calc ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by ring
      _ ≤ (δ * ‖P φ‖) ^ 2 + (δ * ‖(1 - P) φ‖) ^ 2 := add_le_add a1 a2
      _ = δ ^ 2 * (‖P φ‖ ^ 2 + ‖(1 - P) φ‖ ^ 2) := by ring
      _ = (δ * ‖φ‖) ^ 2 := by rw [← hφ]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).1 hsq

end BBDF41

/-! ## Lemma 6.14 -/

section BBDF42

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {P Vm Vp : E →L[ℂ] E}

/-- The step shared by both halves of Lemma 6.14: if `‖P V ψ‖² ≥ (1 - x) ‖ψ‖²` for `V = V₂ V₁`
and `‖P V₂ (1 - P) V₁ P‖ ≤ e`, then `‖P V₁ ψ‖ ≥ (√(1 - x) - e) ‖ψ‖` on `ran P`. -/
theorem bbdf42_step (hP : IsStarProjection P) {V₁ V₂ : E →L[ℂ] E} (hV₂ : ‖V₂‖ ≤ 1) {x e : ℝ}
    (hx : x ≤ 1) (he : ‖P * V₂ * (1 - P) * V₁ * P‖ ≤ e) {ψ : E} (hψ : P ψ = ψ)
    (h : (1 - x) * ‖ψ‖ ^ 2 ≤ ‖P (V₂ (V₁ ψ))‖ ^ 2) :
    (√(1 - x) - e) * ‖ψ‖ ≤ ‖P (V₁ ψ)‖ := by
  have hP1 : ‖P‖ ≤ 1 := IsStarProjection.norm_le P hP
  -- `‖P V₂ V₁ ψ‖ ≥ √(1 - x) ‖ψ‖`
  have hy : √(1 - x) * ‖ψ‖ ≤ ‖P (V₂ (V₁ ψ))‖ := by
    have hs : (√(1 - x) * ‖ψ‖) ^ 2 ≤ ‖P (V₂ (V₁ ψ))‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]; exact h
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 hs
  -- the compression term
  have hc : ‖P (V₂ (V₁ ψ)) - P (V₂ (P (V₁ ψ)))‖ ≤ e * ‖ψ‖ := by
    have : P (V₂ (V₁ ψ)) - P (V₂ (P (V₁ ψ))) = (P * V₂ * (1 - P) * V₁ * P) ψ := by
      simp only [mul_apply_eq_comp, hψ, sub_apply, one_apply_eq_self, map_sub]
    rw [this]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
  -- `‖P V₂ P V₁ ψ‖ ≤ ‖P V₁ ψ‖`
  have hpv : ‖P (V₂ (P (V₁ ψ)))‖ ≤ ‖P (V₁ ψ)‖ := by
    have : P (V₂ (P (V₁ ψ))) = (P * V₂) (P (V₁ ψ)) := by rw [mul_apply_eq_comp]
    rw [this]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have : ‖P * V₂‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg P, norm_nonneg V₂])
    exact mul_le_of_le_one_left (norm_nonneg _) this
  have htri := norm_sub_norm_le (P (V₂ (V₁ ψ))) (P (V₂ (P (V₁ ψ))))
  nlinarith

/-- **Lemma 6.14, quantitative** (the paper's form, with the `ε`'s as upper bounds): with
`a = min(√(1 - ε₀ - 2ε_c) - ε₁, √(1 - ε₀) - ε₂) > 0` and `ε₀ + 2ε_c ≤ 1`,
`‖[V₋, P]‖ ≤ √(1 - a²)`. -/
theorem bbdf42 (hP : IsStarProjection P) (hVm : Vm ∈ unitary (E →L[ℂ] E))
    (hVp : Vp ∈ unitary (E →L[ℂ] E)) {ε₀ εc ε₁ ε₂ : ℝ}
    (h₀ : ‖⁅Vm * Vp, P⁆‖ ≤ ε₀) (hc : ‖⁅Vm, Vp⁆‖ ≤ εc)
    (h₁ : ‖P * Vp * (1 - P) * Vm * P‖ ≤ ε₁) (h₂ : ‖P * star Vp * (1 - P) * star Vm * P‖ ≤ ε₂)
    (hx : ε₀ + 2 * εc ≤ 1) (ha : 0 < min (√(1 - ε₀ - 2 * εc) - ε₁) (√(1 - ε₀) - ε₂)) :
    ‖⁅Vm, P⁆‖ ≤ √(1 - (min (√(1 - ε₀ - 2 * εc) - ε₁) (√(1 - ε₀) - ε₂)) ^ 2) := by
  set a := min (√(1 - ε₀ - 2 * εc) - ε₁) (√(1 - ε₀) - ε₂) with ha_def
  have hP1 : ‖P‖ ≤ 1 := IsStarProjection.norm_le P hP
  have hVp1 : ‖Vp‖ ≤ 1 := norm_le_one_of_mem_unitary hVp
  have hVps1 : ‖star Vp‖ ≤ 1 := (norm_star Vp).le.trans hVp1
  have hε₀ : 0 ≤ ε₀ := (norm_nonneg _).trans h₀
  have hεc : 0 ≤ εc := (norm_nonneg _).trans hc
  have hε₂ : 0 ≤ ε₂ := (norm_nonneg _).trans h₂
  -- `‖[V₊ V₋, P]‖ ≤ ε₀ + 2 ε_c`
  have hpm : ‖⁅Vp * Vm, P⁆‖ ≤ ε₀ + 2 * εc := by
    have e : Vp * Vm = Vm * Vp + ⁅Vp, Vm⁆ := by rw [Ring.lie_def]; abel
    have e2 : ⁅Vp * Vm, P⁆ = ⁅Vm * Vp, P⁆ + ⁅⁅Vp, Vm⁆, P⁆ := by
      rw [e]; simp only [Ring.lie_def]; noncomm_ring
    rw [e2]
    have := norm_lie_starProj_le hP ⁅Vp, Vm⁆
    rw [norm_lie_comm Vp Vm] at this
    exact (norm_add_le _ _).trans (by linarith)
  -- `‖[V₊^* V₋^*, P]‖ = ‖[V₋ V₊, P]‖ ≤ ε₀`
  have hpm' : ‖⁅star Vp * star Vm, P⁆‖ ≤ ε₀ := by
    have : ⁅star Vp * star Vm, P⁆ = -star ⁅Vm * Vp, P⁆ := by
      simp only [Ring.lie_def, star_sub, star_mul, hP.isSelfAdjoint.star_eq]; noncomm_ring
    rw [this, norm_neg]; exact (norm_star ⁅Vm * Vp, P⁆).le.trans h₀
  have hU1 : Vp * Vm ∈ unitary (E →L[ℂ] E) := Submonoid.mul_mem _ hVp hVm
  have hU2 : star Vp * star Vm ∈ unitary (E →L[ℂ] E) :=
    Submonoid.mul_mem _ (Unitary.star_mem hVp) (Unitary.star_mem hVm)
  have ha1 : a ≤ 1 := by
    have : √(1 - ε₀) ≤ 1 :=
      (Real.sqrt_le_sqrt (show 1 - ε₀ ≤ 1 by linarith)).trans_eq Real.sqrt_one
    exact (min_le_right _ _).trans (by linarith)
  -- the two hypotheses of Lemma A.6(ii), with `δ = √(1 - a²)`
  have hδ2 : (√(1 - a ^ 2)) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have k1 : ∀ ψ, P ψ = ψ → (1 - (√(1 - a ^ 2)) ^ 2) * ‖ψ‖ ^ 2 ≤ ‖P (Vm ψ)‖ ^ 2 := by
    intro ψ hψ
    have hA := bbdf41_i hP hU1 hψ
    simp only [mul_apply_eq_comp] at hA
    have hA' : (1 - (ε₀ + 2 * εc)) * ‖ψ‖ ^ 2 ≤ ‖P (Vp (Vm ψ))‖ ^ 2 :=
      le_trans (by gcongr) hA
    have hs := bbdf42_step hP hVp1 (by linarith) h₁ hψ hA'
    rw [show 1 - (ε₀ + 2 * εc) = 1 - ε₀ - 2 * εc by ring] at hs
    have hb : a * ‖ψ‖ ≤ ‖P (Vm ψ)‖ :=
      le_trans (by gcongr; exact min_le_left _ _) hs
    rw [hδ2, sub_sub_cancel]
    have := (pow_le_pow_left₀ (mul_nonneg ha.le (norm_nonneg _)) hb 2)
    rw [mul_pow] at this; exact this
  have k2 : ∀ ψ, P ψ = ψ → (1 - (√(1 - a ^ 2)) ^ 2) * ‖ψ‖ ^ 2 ≤ ‖P (star Vm ψ)‖ ^ 2 := by
    intro ψ hψ
    have hA := bbdf41_i hP hU2 hψ
    simp only [mul_apply_eq_comp] at hA
    have hA' : (1 - ε₀) * ‖ψ‖ ^ 2 ≤ ‖P (star Vp (star Vm ψ))‖ ^ 2 := le_trans (by gcongr) hA
    have hs := bbdf42_step hP hVps1 (by linarith) h₂ hψ hA'
    have hb : a * ‖ψ‖ ≤ ‖P (star Vm ψ)‖ :=
      le_trans (by gcongr; exact min_le_right _ _) hs
    rw [hδ2, sub_sub_cancel]
    have := (pow_le_pow_left₀ (mul_nonneg ha.le (norm_nonneg _)) hb 2)
    rw [mul_pow] at this; exact this
  exact (bbdf41_ii hP hVm (Real.sqrt_nonneg _) k1 k2).2.2

/-- **Lemma 6.14 in the form its proof uses**: with `ε̄ = ε₀ + 2ε_c + ε₁ + ε₂ ≤ 1/2`,
`‖[V₋, P]‖ ≤ √(2 ε̄)`. -/
theorem bbdf42_eps (hP : IsStarProjection P) (hVm : Vm ∈ unitary (E →L[ℂ] E))
    (hVp : Vp ∈ unitary (E →L[ℂ] E)) {ε₀ εc ε₁ ε₂ : ℝ}
    (h₀ : ‖⁅Vm * Vp, P⁆‖ ≤ ε₀) (hc : ‖⁅Vm, Vp⁆‖ ≤ εc)
    (h₁ : ‖P * Vp * (1 - P) * Vm * P‖ ≤ ε₁) (h₂ : ‖P * star Vp * (1 - P) * star Vm * P‖ ≤ ε₂)
    (hsmall : ε₀ + 2 * εc + ε₁ + ε₂ ≤ 1 / 2) :
    ‖⁅Vm, P⁆‖ ≤ √(2 * (ε₀ + 2 * εc + ε₁ + ε₂)) := by
  have hε₀ : 0 ≤ ε₀ := (norm_nonneg _).trans h₀
  have hεc : 0 ≤ εc := (norm_nonneg _).trans hc
  have hε₁ : 0 ≤ ε₁ := (norm_nonneg _).trans h₁
  have hε₂ : 0 ≤ ε₂ := (norm_nonneg _).trans h₂
  set eb := ε₀ + 2 * εc + ε₁ + ε₂ with heb
  -- `√t ≥ t` on `[0, 1]`
  have hsq : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t ≤ √t := fun t h0 h1 =>
    calc t = √(t ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ √t := Real.sqrt_le_sqrt (by nlinarith)
  have hA : 1 - eb ≤ √(1 - ε₀ - 2 * εc) - ε₁ := by
    have := hsq (1 - ε₀ - 2 * εc) (by linarith) (by linarith); linarith
  have hB : 1 - eb ≤ √(1 - ε₀) - ε₂ := by
    have := hsq (1 - ε₀) (by linarith) (by linarith); linarith
  have hmin : 1 - eb ≤ min (√(1 - ε₀ - 2 * εc) - ε₁) (√(1 - ε₀) - ε₂) := le_min hA hB
  have hpos : 0 < min (√(1 - ε₀ - 2 * εc) - ε₁) (√(1 - ε₀) - ε₂) := by linarith
  have hmain := bbdf42 hP hVm hVp h₀ hc h₁ h₂ (by linarith) hpos
  refine hmain.trans (Real.sqrt_le_sqrt ?_)
  set a := min (√(1 - ε₀ - 2 * εc) - ε₁) (√(1 - ε₀) - ε₂)
  have ha1 : a ≤ 1 := by
    have : √(1 - ε₀) ≤ 1 :=
      (Real.sqrt_le_sqrt (show 1 - ε₀ ≤ 1 by linarith)).trans_eq Real.sqrt_one
    exact (min_le_right _ _).trans (by linarith)
  nlinarith

/-- Lemma 6.14 for `V₊`: the same statement for the ordered pair `(V₊, V₋)`. -/
theorem bbdf42_eps_plus (hP : IsStarProjection P) (hVm : Vm ∈ unitary (E →L[ℂ] E))
    (hVp : Vp ∈ unitary (E →L[ℂ] E)) {ε₀ εc ε₁ ε₂ : ℝ}
    (h₀ : ‖⁅Vp * Vm, P⁆‖ ≤ ε₀) (hc : ‖⁅Vm, Vp⁆‖ ≤ εc)
    (h₁ : ‖P * Vm * (1 - P) * Vp * P‖ ≤ ε₁) (h₂ : ‖P * star Vm * (1 - P) * star Vp * P‖ ≤ ε₂)
    (hsmall : ε₀ + 2 * εc + ε₁ + ε₂ ≤ 1 / 2) :
    ‖⁅Vp, P⁆‖ ≤ √(2 * (ε₀ + 2 * εc + ε₁ + ε₂)) :=
  bbdf42_eps hP hVp hVm h₀ (by rw [norm_lie_comm]; exact hc) h₁ h₂ hsmall

end BBDF42

/-! ## Corollary 6.15, with explicit constants -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

namespace Setting

variable (S : Setting E)

theorem Mminus_mem_unitary (φ : ℝ) : S.Mminus φ ∈ unitary (E →L[ℂ] E) := by
  rw [S.Mminus_eq]
  exact Submonoid.mul_mem _ (expI_mem_unitary _ S.isSelfAdjoint_QbarUMinus φ)
    (expI_mem_unitary _ S.isSelfAdjoint_QbarMinus (-φ))

theorem Mplus_mem_unitary (φ : ℝ) : S.Mplus φ ∈ unitary (E →L[ℂ] E) := by
  rw [S.Mplus_eq]
  exact Submonoid.mul_mem _ (expI_mem_unitary _ S.isSelfAdjoint_QbarUPlus φ)
    (expI_mem_unitary _ S.isSelfAdjoint_QbarPlus (-φ))

theorem Ominus_mem_unitary : S.Ominus ∈ unitary (E →L[ℂ] E) := by
  rw [S.Ominus_eq]; exact expI_mem_unitary _ S.isSelfAdjoint_QbarMinus _

theorem Oplus_mem_unitary : S.Oplus ∈ unitary (E →L[ℂ] E) := by
  rw [S.Oplus_eq]; exact expI_mem_unitary _ S.isSelfAdjoint_QbarPlus _

/-- `c_𝓜 = 324π² + 4`. -/
def cM : ℝ := 324 * π ^ 2 + 4

/-- `c_O = 44π² + 2`. -/
def cO : ℝ := 44 * π ^ 2 + 2

variable {S} {ε : ℝ}

/-- Lemma 6.14's `ε₀` for the flux insertions: `‖[𝓜₋(φ) 𝓜₊(φ), P]‖ ≤ 39 φ² ε + 2 ε`. -/
theorem SepBounds.norm_lie_MM_P_le (h : S.SepBounds ε) (hU2 : ‖⁅S.U, S.P⁆‖ ≤ ε) (φ : ℝ) :
    ‖⁅S.Mminus φ * S.Mplus φ, S.P⁆‖ ≤ 39 * φ ^ 2 * ε + 2 * ε := by
  have h1 := norm_lie_starProj_le_of_sub S.isStarProjection_P (S.Mminus φ * S.Mplus φ) (S.M φ)
  have h2 := h.norm_M_sub_le φ
  rw [norm_sub_rev] at h2
  have h3 := S.norm_lie_P_M_le φ
  rw [norm_lie_comm] at h3
  linarith

/-- **Corollary 6.15 for `𝓜₋`**: if `c_𝓜 ε ≤ 1/2`, then `‖[𝓜₋(φ), P]‖ ≤ √(2 c_𝓜 ε)` for every
`φ ∈ [0, 2π]`. -/
theorem SepBounds.norm_lie_Mminus_P_le (h : S.SepBounds ε) (hU2 : ‖⁅S.U, S.P⁆‖ ≤ ε)
    (clu_M : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π), ‖⁅S.Qf (S.Mplus φ), S.Mminus φ⁆‖ ≤ ε)
    (clu_M_adj : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖⁅S.Qf (star (S.Mplus φ)), star (S.Mminus φ)⁆‖ ≤ ε)
    (hsmall : cM * ε ≤ 1 / 2) {φ : ℝ} (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * π)) :
    ‖⁅S.Mminus φ, S.P⁆‖ ≤ √(2 * (cM * ε)) := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hU2
  have hφ2 : φ ^ 2 ≤ 4 * π ^ 2 := by nlinarith [hφ.1, hφ.2, Real.pi_pos]
  have hb : 39 * φ ^ 2 * ε + 2 * ε + 2 * (21 * φ ^ 2 * ε) + ε + ε ≤ cM * ε := by
    rw [cM]; nlinarith
  have hmain := bbdf42_eps S.isStarProjection_P (S.Mminus_mem_unitary φ)
    (S.Mplus_mem_unitary φ) (h.norm_lie_MM_P_le hU2 φ) (h.norm_lie_Mminus_Mplus_le φ)
    (S.compress_M_le clu_M hφ) (S.compress_M_adj_le clu_M_adj hφ) (hb.trans hsmall)
  exact hmain.trans (Real.sqrt_le_sqrt (by linarith))

/-- Lemma 6.14's `ε₀` for the charge unitaries: `‖[e^{2πiQ̄₋} e^{2πiQ̄₊}, P]‖ ≤ 20 π² ε`. -/
theorem SepBounds.norm_lie_OO_P_le (h : S.SepBounds ε) :
    ‖⁅S.Ominus * S.Oplus, S.P⁆‖ ≤ 20 * π ^ 2 * ε := by
  have h1 := norm_lie_starProj_le_of_sub S.isStarProjection_P (S.Ominus * S.Oplus)
    (expI (2 * π) S.Qbar)
  have h2 := h.norm_expI_Qbar_sub_le
  rw [norm_sub_rev] at h2
  have h3 : ‖⁅expI (2 * π) S.Qbar, S.P⁆‖ = 0 := by
    rw [norm_lie_comm, S.lie_P_expI_Qbar, norm_zero]
  linarith

/-- **Corollary 6.15 for `e^{2πiQ̄₋}`**: if `c_O ε ≤ 1/2`, then
`‖[e^{2πiQ̄₋}, P]‖ ≤ √(2 c_O ε)`. -/
theorem SepBounds.norm_lie_Ominus_P_le (h : S.SepBounds ε)
    (clu_O : ‖⁅S.Qf S.Oplus, S.Ominus⁆‖ ≤ ε)
    (clu_O_adj : ‖⁅S.Qf (star S.Oplus), star S.Ominus⁆‖ ≤ ε)
    (hsmall : cO * ε ≤ 1 / 2) : ‖⁅S.Ominus, S.P⁆‖ ≤ √(2 * (cO * ε)) := by
  have hb : 20 * π ^ 2 * ε + 2 * (12 * π ^ 2 * ε) + ε + ε = cO * ε := by rw [cO]; ring
  have hmain := bbdf42_eps S.isStarProjection_P S.Ominus_mem_unitary S.Oplus_mem_unitary
    h.norm_lie_OO_P_le h.norm_lie_Ominus_Oplus_le (S.compress_O_le clu_O)
    (S.compress_O_adj_le clu_O_adj) (hb.le.trans hsmall)
  rw [hb] at hmain
  exact hmain

end Setting

end HRTorus.IndexCore
