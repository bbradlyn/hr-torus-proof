import HRTorus.IndexCore.Statement

/-!
# The eigenprojection algebra

Written by Claude Opus 5.5 (an AI model), 2026-10-23. The spectral layer under Lemma 6.7 and Proposition 6.10 of the HR paper:
the eigenprojections `P_E = 1_{E}(H)` of `Statement.lean` (`eigProj`), their algebra
(orthogonality, completeness, `H P_E = E P_E = P_E H`, commutation with everything that commutes
with `H`), the blocks, adjoint and commutation of `spectralSum`, the projection `P` (a star
projection commuting with `H` and `Π`), the gap of Assumption 6.3 in eigenprojection form, and the
bridge `eigProj H μ = (eigenspace H μ).starProjection` (the eigenprojection does not depend on the
eigenbasis Mathlib chose).

Membership in a set `S` is handled by pairs of lemmas (`…_of_mem`, `…_of_not_mem`) rather than by
`if … ∈ S`, so that no decidability instance has to match the classical one inside `specProj`.
-/

open scoped InnerProductSpace ComplexConjugate
open Complex (I)

noncomputable section
open Classical

namespace HRTorus.IndexCore

/-! ## Rank-one operators -/

section RankOne

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem rankOne_mul_rankOne (x y z w : E) :
    InnerProductSpace.rankOne ℂ x y * InnerProductSpace.rankOne ℂ z w =
      ⟪y, z⟫_ℂ • InnerProductSpace.rankOne ℂ x w := by
  rw [ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp_rankOne]

theorem mul_rankOne (A : E →L[ℂ] E) (x y : E) :
    A * InnerProductSpace.rankOne ℂ x y = InnerProductSpace.rankOne ℂ (A x) y := by
  rw [ContinuousLinearMap.mul_def, InnerProductSpace.comp_rankOne]

theorem rankOne_smul_left (c : ℂ) (x y : E) :
    InnerProductSpace.rankOne ℂ (c • x) y = c • InnerProductSpace.rankOne ℂ x y := by
  ext z; simp [InnerProductSpace.rankOne_apply, smul_comm c]

variable [CompleteSpace E]

theorem rankOne_mul (A : E →L[ℂ] E) (x y : E) :
    InnerProductSpace.rankOne ℂ x y * A = InnerProductSpace.rankOne ℂ x (star A y) := by
  rw [ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp,
    ContinuousLinearMap.star_eq_adjoint]

theorem star_rankOne (x y : E) :
    star (InnerProductSpace.rankOne ℂ x y) = InnerProductSpace.rankOne ℂ y x := by
  rw [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]

end RankOne

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

section Spectral

variable (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)

/-! ## The eigenbasis -/

theorem apply_eigBasis (i : Fin (Module.finrank ℂ E)) :
    H (eigBasis H hH i) = (eigVal H hH i : ℂ) • eigBasis H hH i :=
  hH.isSymmetric.apply_eigenvectorBasis rfl i

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem inner_eigBasis_self_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (i j : ι) : ⟪b i, b j⟫_ℂ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp b.orthonormal i j

theorem inner_eigBasis (i j : Fin (Module.finrank ℂ E)) :
    ⟪eigBasis H hH i, eigBasis H hH j⟫_ℂ = if i = j then 1 else 0 :=
  inner_eigBasis_self_aux (eigBasis H hH) i j

theorem mem_spec_iff (μ : ℝ) : μ ∈ spec H hH ↔ ∃ i, eigVal H hH i = μ := by
  simp [spec]

theorem eigVal_mem_spec (i : Fin (Module.finrank ℂ E)) : eigVal H hH i ∈ spec H hH :=
  (mem_spec_iff H hH _).2 ⟨i, rfl⟩

/-- The rank-one projectors `|eᵢ⟩⟨eᵢ|` multiply as `δᵢⱼ`. -/
theorem rk_mul_rk (i j : Fin (Module.finrank ℂ E)) :
    InnerProductSpace.rankOne ℂ (eigBasis H hH i) (eigBasis H hH i) *
        InnerProductSpace.rankOne ℂ (eigBasis H hH j) (eigBasis H hH j) =
      if i = j then InnerProductSpace.rankOne ℂ (eigBasis H hH i) (eigBasis H hH i) else 0 := by
  rw [rankOne_mul_rankOne, inner_eigBasis]
  split_ifs with h
  · subst h; rw [one_smul]
  · rw [zero_smul]

/-! ## The eigenprojections `P_E` -/

theorem eigProj_def (μ : ℝ) :
    eigProj H hH μ = ∑ i ∈ Finset.univ.filter (fun i => eigVal H hH i = μ),
      InnerProductSpace.rankOne ℂ (eigBasis H hH i) (eigBasis H hH i) := rfl

/-- `P_μ P_ν = δ_{μν} P_μ`. -/
theorem eigProj_mul_eigProj (μ ν : ℝ) :
    eigProj H hH μ * eigProj H hH ν = if μ = ν then eigProj H hH μ else 0 := by
  simp only [eigProj_def, Finset.sum_mul_sum, rk_mul_rk]
  split_ifs with hμν
  · subst hμν
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_ite_eq, ite_eq_left hi]
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.sum_ite_eq, ite_eq_right]
    intro hi'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact hμν (hi.symm.trans hi')

theorem eigProj_mul_self (μ : ℝ) : eigProj H hH μ * eigProj H hH μ = eigProj H hH μ := by
  rw [eigProj_mul_eigProj, ite_eq_left rfl]

theorem eigProj_mul_eigProj_of_ne {μ ν : ℝ} (h : μ ≠ ν) :
    eigProj H hH μ * eigProj H hH ν = 0 := by
  rw [eigProj_mul_eigProj, ite_eq_right h]

theorem eigProj_eq_zero_of_not_mem {μ : ℝ} (h : μ ∉ spec H hH) : eigProj H hH μ = 0 := by
  rw [eigProj_def]
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact absurd (hi ▸ eigVal_mem_spec H hH i) h

/-- Completeness: `∑_{E ∈ σ(H)} P_E = 1`. -/
theorem sum_eigProj : ∑ μ ∈ spec H hH, eigProj H hH μ = 1 := by
  simp only [eigProj_def]
  rw [Finset.sum_fiberwise_of_maps_to (g := eigVal H hH)
    (fun i _ => eigVal_mem_spec H hH i)]
  rw [OrthonormalBasis.sum_rankOne_eq_id, ContinuousLinearMap.one_def]

theorem star_eigProj (μ : ℝ) : star (eigProj H hH μ) = eigProj H hH μ := by
  rw [eigProj_def, star_sum]
  exact Finset.sum_congr rfl fun i _ => star_rankOne _ _

theorem isSelfAdjoint_eigProj (μ : ℝ) : IsSelfAdjoint (eigProj H hH μ) :=
  star_eigProj H hH μ

theorem isStarProjection_eigProj (μ : ℝ) : IsStarProjection (eigProj H hH μ) where
  isIdempotentElem := eigProj_mul_self H hH μ
  isSelfAdjoint := isSelfAdjoint_eigProj H hH μ

/-- `H P_μ = μ P_μ`. -/
theorem mul_eigProj (μ : ℝ) : H * eigProj H hH μ = (μ : ℂ) • eigProj H hH μ := by
  rw [eigProj_def, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [mul_rankOne, apply_eigBasis, rankOne_smul_left, hi]

/-- `P_μ H = μ P_μ`. -/
theorem eigProj_mul (μ : ℝ) : eigProj H hH μ * H = (μ : ℂ) • eigProj H hH μ := by
  have h := congrArg star (mul_eigProj H hH μ)
  rw [star_mul, star_eigProj, hH.star_eq, star_smul, star_eigProj] at h
  rw [h, Complex.star_def, Complex.conj_ofReal]

theorem commute_H_eigProj (μ : ℝ) : Commute H (eigProj H hH μ) := by
  rw [Commute, SemiconjBy, mul_eigProj, eigProj_mul]

/-- The off-diagonal blocks of an operator commuting with `H` vanish. -/
theorem eigProj_mul_mul_eigProj_of_commute {X : E →L[ℂ] E} (hX : Commute X H) {μ ν : ℝ}
    (h : μ ≠ ν) : eigProj H hH μ * X * eigProj H hH ν = 0 := by
  have h1 : eigProj H hH μ * H * X * eigProj H hH ν =
      (μ : ℂ) • (eigProj H hH μ * X * eigProj H hH ν) := by
    rw [eigProj_mul, smul_mul_assoc, smul_mul_assoc]
  have h2 : eigProj H hH μ * H * X * eigProj H hH ν =
      (ν : ℂ) • (eigProj H hH μ * X * eigProj H hH ν) := by
    have hHX : H * X = X * H := hX.eq.symm
    rw [mul_assoc (eigProj H hH μ) H X, hHX, ← mul_assoc, mul_assoc _ H, mul_eigProj,
      mul_smul_comm]
  have h3 : ((μ : ℂ) - ν) • (eigProj H hH μ * X * eigProj H hH ν) = 0 := by
    rw [sub_smul, ← h1, ← h2, sub_self]
  have hne : ((μ : ℂ) - ν) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast h
  exact (smul_eq_zero.mp h3).resolve_left hne

/-- Every operator commuting with `H` commutes with each eigenprojection. -/
theorem commute_eigProj_of_commute {X : E →L[ℂ] E} (hX : Commute X H) (μ : ℝ) :
    Commute X (eigProj H hH μ) := by
  by_cases hμ : μ ∈ spec H hH
  · have hL : X * eigProj H hH μ = eigProj H hH μ * X * eigProj H hH μ := by
      calc X * eigProj H hH μ = (∑ ν ∈ spec H hH, eigProj H hH ν) * X * eigProj H hH μ := by
              rw [sum_eigProj, one_mul]
        _ = ∑ ν ∈ spec H hH, eigProj H hH ν * X * eigProj H hH μ := by
              rw [Finset.sum_mul, Finset.sum_mul]
        _ = eigProj H hH μ * X * eigProj H hH μ := by
              rw [Finset.sum_eq_single μ]
              · intro ν _ hν
                exact eigProj_mul_mul_eigProj_of_commute H hH hX hν
              · intro h; exact absurd hμ h
    have hR : eigProj H hH μ * X = eigProj H hH μ * X * eigProj H hH μ := by
      calc eigProj H hH μ * X = eigProj H hH μ * X * ∑ ν ∈ spec H hH, eigProj H hH ν := by
              rw [sum_eigProj, mul_one]
        _ = ∑ ν ∈ spec H hH, eigProj H hH μ * X * eigProj H hH ν := by
              rw [Finset.mul_sum]
        _ = eigProj H hH μ * X * eigProj H hH μ := by
              rw [Finset.sum_eq_single μ]
              · intro ν _ hν
                exact eigProj_mul_mul_eigProj_of_commute H hH hX (Ne.symm hν)
              · intro h; exact absurd hμ h
    exact hL.trans hR.symm
  · rw [eigProj_eq_zero_of_not_mem H hH hμ]
    exact Commute.zero_right X

/-! ## Blocks -/

/-- Every operator is the sum of its blocks: `A = ∑_{μ,ν} P_μ A P_ν`. -/
theorem sum_blocks (A : E →L[ℂ] E) :
    ∑ μ ∈ spec H hH, ∑ ν ∈ spec H hH, eigProj H hH μ * A * eigProj H hH ν = A := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sum_eigProj, one_mul, mul_one]

/-- Two operators with the same blocks are equal. -/
theorem ext_blocks {X Y : E →L[ℂ] E}
    (h : ∀ μ ∈ spec H hH, ∀ ν ∈ spec H hH,
      eigProj H hH μ * X * eigProj H hH ν = eigProj H hH μ * Y * eigProj H hH ν) :
    X = Y := by
  rw [← sum_blocks H hH X, ← sum_blocks H hH Y]
  exact Finset.sum_congr rfl fun μ hμ => Finset.sum_congr rfl fun ν hν => h μ hμ ν hν

/-- The block of a block. -/
theorem eigProj_mul_block_mul_eigProj (A : E →L[ℂ] E) (μ κ κ' ν : ℝ) :
    eigProj H hH μ * (eigProj H hH κ * A * eigProj H hH κ') * eigProj H hH ν =
      if μ = κ ∧ κ' = ν then eigProj H hH μ * A * eigProj H hH ν else 0 := by
  have e : eigProj H hH μ * (eigProj H hH κ * A * eigProj H hH κ') * eigProj H hH ν =
      (eigProj H hH μ * eigProj H hH κ) * A * (eigProj H hH κ' * eigProj H hH ν) := by
    simp only [mul_assoc]
  rw [e, eigProj_mul_eigProj, eigProj_mul_eigProj]
  by_cases h1 : μ = κ <;> by_cases h2 : κ' = ν
  · subst h1; subst h2; simp
  · simp [h2]
  · simp [h1]
  · simp [h1]

/-! ## The double spectral sum: blocks, linearity, adjoint, commutation -/

theorem spectralSum_def (f : ℝ → ℝ → ℂ) (A : E →L[ℂ] E) :
    spectralSum H hH f A = ∑ μ ∈ spec H hH, ∑ ν ∈ spec H hH,
      f μ ν • (eigProj H hH μ * A * eigProj H hH ν) := rfl

/-- The blocks of the double spectral sum: `P_μ (∑ f P A P) P_ν = f μ ν • P_μ A P_ν`. -/
theorem eigProj_mul_spectralSum_mul_eigProj (f : ℝ → ℝ → ℂ) (A : E →L[ℂ] E) (μ ν : ℝ) :
    eigProj H hH μ * spectralSum H hH f A * eigProj H hH ν =
      f μ ν • (eigProj H hH μ * A * eigProj H hH ν) := by
  rw [spectralSum_def]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    eigProj_mul_block_mul_eigProj]
  by_cases hμ : μ ∈ spec H hH
  · by_cases hν : ν ∈ spec H hH
    · rw [Finset.sum_eq_single μ]
      · rw [Finset.sum_eq_single ν]
        · simp
        · intro κ' _ h; simp [h]
        · intro h; exact absurd hν h
      · intro κ _ h
        refine Finset.sum_eq_zero fun κ' _ => ?_
        simp [Ne.symm h]
      · intro h; exact absurd hμ h
    · simp [eigProj_eq_zero_of_not_mem H hH hν]
  · simp [eigProj_eq_zero_of_not_mem H hH hμ]

theorem spectralSum_add (f : ℝ → ℝ → ℂ) (A B : E →L[ℂ] E) :
    spectralSum H hH f (A + B) = spectralSum H hH f A + spectralSum H hH f B := by
  simp only [spectralSum_def, mul_add, add_mul, smul_add, Finset.sum_add_distrib]

theorem spectralSum_smul (f : ℝ → ℝ → ℂ) (c : ℂ) (A : E →L[ℂ] E) :
    spectralSum H hH f (c • A) = c • spectralSum H hH f A := by
  rw [spectralSum_def, spectralSum_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, smul_comm]

/-- The adjoint of a double spectral sum. -/
theorem star_spectralSum (f : ℝ → ℝ → ℂ) (A : E →L[ℂ] E) :
    star (spectralSum H hH f A) =
      spectralSum H hH (fun μ ν => starRingEnd ℂ (f ν μ)) (star A) := by
  rw [spectralSum_def, spectralSum_def, star_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [star_smul, star_mul, star_mul, star_eigProj, star_eigProj, mul_assoc, Complex.star_def]

/-- An operator commuting with `H` and with `A` commutes with every double spectral sum of `A`. -/
theorem commute_spectralSum {X : E →L[ℂ] E} (hXH : Commute X H) {A : E →L[ℂ] E}
    (hXA : Commute X A) (f : ℝ → ℝ → ℂ) : Commute X (spectralSum H hH f A) := by
  rw [spectralSum_def]
  refine Commute.sum_right _ _ _ fun μ _ => Commute.sum_right _ _ _ fun ν _ => ?_
  refine Commute.smul_right ?_ _
  exact ((commute_eigProj_of_commute H hH hXH μ).mul_right hXA).mul_right
    (commute_eigProj_of_commute H hH hXH ν)

/-! ## Spectral projections `1_S(H)` -/

theorem specProj_def (S : Set ℝ) :
    specProj H hH S = ∑ μ ∈ (spec H hH).filter (· ∈ S), eigProj H hH μ := rfl

theorem specProj_mul_eigProj_of_mem {S : Set ℝ} {ν : ℝ} (hS : ν ∈ S) :
    specProj H hH S * eigProj H hH ν = eigProj H hH ν := by
  rw [specProj_def, Finset.sum_mul]
  by_cases hν : ν ∈ spec H hH
  · rw [Finset.sum_eq_single ν]
    · exact eigProj_mul_self H hH ν
    · intro κ _ hκ; exact eigProj_mul_eigProj_of_ne H hH hκ
    · intro h; exact absurd (Finset.mem_filter.2 ⟨hν, hS⟩) h
  · rw [eigProj_eq_zero_of_not_mem H hH hν]
    simp

theorem specProj_mul_eigProj_of_not_mem {S : Set ℝ} {ν : ℝ} (hS : ν ∉ S) :
    specProj H hH S * eigProj H hH ν = 0 := by
  rw [specProj_def, Finset.sum_mul]
  refine Finset.sum_eq_zero fun κ hκ => ?_
  have hκS : κ ∈ S := (Finset.mem_filter.1 hκ).2
  exact eigProj_mul_eigProj_of_ne H hH (fun h => hS (h ▸ hκS))

theorem star_specProj (S : Set ℝ) : star (specProj H hH S) = specProj H hH S := by
  rw [specProj_def, star_sum]
  exact Finset.sum_congr rfl fun μ _ => star_eigProj H hH μ

theorem eigProj_mul_specProj_of_mem {S : Set ℝ} {ν : ℝ} (hS : ν ∈ S) :
    eigProj H hH ν * specProj H hH S = eigProj H hH ν := by
  have h := congrArg star (specProj_mul_eigProj_of_mem H hH hS)
  rwa [star_mul, star_specProj, star_eigProj] at h

theorem eigProj_mul_specProj_of_not_mem {S : Set ℝ} {ν : ℝ} (hS : ν ∉ S) :
    eigProj H hH ν * specProj H hH S = 0 := by
  have h := congrArg star (specProj_mul_eigProj_of_not_mem H hH hS)
  rwa [star_mul, star_specProj, star_eigProj, star_zero] at h

theorem specProj_mul_self (S : Set ℝ) :
    specProj H hH S * specProj H hH S = specProj H hH S := by
  conv_lhs => rw [specProj_def H hH S, Finset.mul_sum]
  rw [specProj_def]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  exact specProj_mul_eigProj_of_mem H hH (Finset.mem_filter.1 hμ).2

theorem isStarProjection_specProj (S : Set ℝ) : IsStarProjection (specProj H hH S) where
  isIdempotentElem := specProj_mul_self H hH S
  isSelfAdjoint := star_specProj H hH S

theorem commute_specProj_of_commute {X : E →L[ℂ] E} (hX : Commute X H) (S : Set ℝ) :
    Commute X (specProj H hH S) := by
  rw [specProj_def]
  exact Commute.sum_right _ _ _ fun μ _ => commute_eigProj_of_commute H hH hX μ

theorem commute_H_specProj (S : Set ℝ) : Commute H (specProj H hH S) :=
  commute_specProj_of_commute H hH (Commute.refl H) S

/-- `∑_{μ ∈ σ, μ ∉ S} P_μ = 1 - 1_S(H)`. -/
theorem sum_eigProj_not_mem (S : Set ℝ) :
    ∑ μ ∈ (spec H hH).filter (· ∉ S), eigProj H hH μ = 1 - specProj H hH S := by
  rw [← sum_eigProj H hH, specProj_def,
    ← Finset.sum_filter_add_sum_filter_not (spec H hH) (· ∈ S)]
  abel

/-! ## The bridge: `P_μ` is the orthogonal projection onto the `μ`-eigenspace -/

theorem eigProj_apply_eigBasis (μ : ℝ) (j : Fin (Module.finrank ℂ E)) :
    eigProj H hH μ (eigBasis H hH j) = if eigVal H hH j = μ then eigBasis H hH j else 0 := by
  rw [eigProj_def, sum_apply]
  simp only [InnerProductSpace.rankOne_apply, inner_eigBasis, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The bridge**: the eigenprojection built from Mathlib's
eigenbasis is the orthogonal projection onto the eigenspace of `μ`; in particular it does not
depend on the choice of eigenbasis. -/
theorem eigProj_eq_starProjection (μ : ℝ) :
    eigProj H hH μ =
      (Module.End.eigenspace (H : E →ₗ[ℂ] E) (μ : ℂ)).starProjection := by
  apply ContinuousLinearMap.coe_injective
  refine (eigBasis H hH).toBasis.ext fun j => ?_
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
  rw [eigProj_apply_eigBasis]
  split_ifs with hj
  · symm
    rw [Submodule.starProjection_eq_self_iff, Module.End.mem_eigenspace_iff,
      ContinuousLinearMap.coe_coe, apply_eigBasis, hj]
  · symm
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
    intro u hu
    rw [Module.End.mem_eigenspace_iff] at hu
    have hsym := hH.isSymmetric u (eigBasis H hH j)
    rw [hu, ContinuousLinearMap.coe_coe, apply_eigBasis, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal] at hsym
    have hne : (μ : ℂ) - eigVal H hH j ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast Ne.symm hj
    have h0 : ((μ : ℂ) - eigVal H hH j) * ⟪u, eigBasis H hH j⟫_ℂ = 0 := by
      rw [sub_mul, hsym, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left hne

end Spectral

/-! ## The setting: the projection `P` and the gap in eigenprojection form -/

namespace Setting

variable (S : Setting E)

theorem Q_def : S.Q = S.Qminus + S.Qmid + S.Qplus := rfl

theorem P_def : S.P = specProj S.H S.H_sa (Set.Icc S.a S.b) * S.Psec := rfl

theorem γ_pos : 0 < S.γ := lt_of_le_of_lt S.Δ_nonneg S.Δ_lt_γ

theorem Psec_mul_self : S.Psec * S.Psec = S.Psec := S.Psec_proj.isIdempotentElem.eq

theorem star_Psec : star S.Psec = S.Psec := S.Psec_proj.isSelfAdjoint.star_eq

theorem commute_Psec_eigProj (μ : ℝ) : Commute S.Psec (eigProj S.H S.H_sa μ) :=
  commute_eigProj_of_commute S.H S.H_sa S.Psec_H μ

theorem commute_Psec_specProj (T : Set ℝ) : Commute S.Psec (specProj S.H S.H_sa T) :=
  commute_specProj_of_commute S.H S.H_sa S.Psec_H T

theorem commute_Psec_Q : Commute S.Psec S.Q :=
  (S.Psec_Qminus.add_right S.Psec_Qmid).add_right S.Psec_Qplus

theorem isStarProjection_P : IsStarProjection S.P :=
  (isStarProjection_specProj S.H S.H_sa _).mul S.Psec_proj (S.commute_Psec_specProj _).symm

theorem P_mul_self : S.P * S.P = S.P := S.isStarProjection_P.isIdempotentElem.eq

theorem star_P : star S.P = S.P := S.isStarProjection_P.isSelfAdjoint.star_eq

theorem P_mul_Psec : S.P * S.Psec = S.P := by
  rw [P_def, mul_assoc, S.Psec_mul_self]

theorem Psec_mul_P : S.Psec * S.P = S.P := by
  rw [P_def, ← mul_assoc, (S.commute_Psec_specProj _).eq, mul_assoc, S.Psec_mul_self]

theorem commute_Psec_P : Commute S.Psec S.P := by
  rw [Commute, SemiconjBy, S.Psec_mul_P, S.P_mul_Psec]

theorem commute_P_H : Commute S.P S.H :=
  (commute_H_specProj S.H S.H_sa _).symm.mul_left S.Psec_H

theorem commute_P_eigProj (μ : ℝ) : Commute S.P (eigProj S.H S.H_sa μ) :=
  commute_eigProj_of_commute S.H S.H_sa S.commute_P_H μ

/-- `P_ν P = P_ν Π` if `ν ∈ [a, b]`. -/
theorem eigProj_mul_P_of_mem {ν : ℝ} (h : ν ∈ Set.Icc S.a S.b) :
    eigProj S.H S.H_sa ν * S.P = eigProj S.H S.H_sa ν * S.Psec := by
  rw [P_def, ← mul_assoc, eigProj_mul_specProj_of_mem S.H S.H_sa h]

/-- `P_ν P = 0` if `ν ∉ [a, b]`. -/
theorem eigProj_mul_P_of_not_mem {ν : ℝ} (h : ν ∉ Set.Icc S.a S.b) :
    eigProj S.H S.H_sa ν * S.P = 0 := by
  rw [P_def, ← mul_assoc, eigProj_mul_specProj_of_not_mem S.H S.H_sa h, zero_mul]

theorem P_mul_eigProj_of_mem {ν : ℝ} (h : ν ∈ Set.Icc S.a S.b) :
    S.P * eigProj S.H S.H_sa ν = eigProj S.H S.H_sa ν * S.Psec := by
  rw [(S.commute_P_eigProj ν).eq, S.eigProj_mul_P_of_mem h]

theorem P_mul_eigProj_of_not_mem {ν : ℝ} (h : ν ∉ Set.Icc S.a S.b) :
    S.P * eigProj S.H S.H_sa ν = 0 := by
  rw [(S.commute_P_eigProj ν).eq, S.eigProj_mul_P_of_not_mem h]

/-- **The gap in eigenprojection form** (Assumption 6.3): an eigenvalue whose eigenprojection
meets the sector lies in `[a, b]` or at least `b + γ`. -/
theorem gap_of_eigProj_mul_Psec_ne_zero {μ : ℝ} (h : eigProj S.H S.H_sa μ * S.Psec ≠ 0) :
    μ ∈ Set.Icc S.a S.b ∨ S.b + S.γ ≤ μ := by
  obtain ⟨w, hw⟩ : ∃ w, (eigProj S.H S.H_sa μ * S.Psec) w ≠ 0 := by
    by_contra hcon
    refine h (ContinuousLinearMap.ext fun w => ?_)
    by_contra hw
    exact hcon ⟨w, hw⟩
  refine S.gap μ _ hw ?_ ?_
  · show (S.Psec * (eigProj S.H S.H_sa μ * S.Psec)) w = (eigProj S.H S.H_sa μ * S.Psec) w
    rw [← mul_assoc, (S.commute_Psec_eigProj μ).eq, mul_assoc, S.Psec_mul_self]
  · show (S.H * (eigProj S.H S.H_sa μ * S.Psec)) w = (μ : ℂ) • (eigProj S.H S.H_sa μ * S.Psec) w
    rw [← mul_assoc, mul_eigProj, smul_mul_assoc]
    rfl

/-- A sector-preserving operator's block `P_μ X P_ν Π` can be written with `Π` on the left. -/
theorem block_Psec_swap {X : E →L[ℂ] E} (hX : Commute S.Psec X) (μ ν : ℝ) :
    eigProj S.H S.H_sa μ * X * eigProj S.H S.H_sa ν * S.Psec =
      eigProj S.H S.H_sa μ * S.Psec * X * eigProj S.H S.H_sa ν := by
  simp only [mul_assoc]
  rw [← (S.commute_Psec_eigProj ν).eq, ← mul_assoc X, ← hX.eq, mul_assoc]

/-- If the block `P_μ X P_ν Π` of a sector-preserving `X` is nonzero, `μ` is a sector eigenvalue. -/
theorem gap_left_of_block_ne_zero {X : E →L[ℂ] E} (hX : Commute S.Psec X) {μ ν : ℝ}
    (h : eigProj S.H S.H_sa μ * X * eigProj S.H S.H_sa ν * S.Psec ≠ 0) :
    μ ∈ Set.Icc S.a S.b ∨ S.b + S.γ ≤ μ := by
  refine S.gap_of_eigProj_mul_Psec_ne_zero fun h0 => h ?_
  rw [S.block_Psec_swap hX, h0, zero_mul, zero_mul]

/-- If the block `P_μ X P_ν Π` is nonzero, `ν` is a sector eigenvalue. -/
theorem gap_right_of_block_ne_zero {X : E →L[ℂ] E} {μ ν : ℝ}
    (h : eigProj S.H S.H_sa μ * X * eigProj S.H S.H_sa ν * S.Psec ≠ 0) :
    S.b + S.γ ≤ ν ∨ ν ∈ Set.Icc S.a S.b := by
  refine Or.symm (S.gap_of_eigProj_mul_Psec_ne_zero fun h0 => h ?_)
  rw [mul_assoc, h0, mul_zero]

/-- The blocks of a commutator with `P`. -/
theorem block_lie_P (X : E →L[ℂ] E) (μ ν : ℝ) :
    eigProj S.H S.H_sa μ * ⁅X, S.P⁆ * eigProj S.H S.H_sa ν =
      eigProj S.H S.H_sa μ * X * (S.P * eigProj S.H S.H_sa ν) -
        eigProj S.H S.H_sa μ * S.P * X * eigProj S.H S.H_sa ν := by
  simp only [Ring.lie_def, mul_sub, sub_mul, mul_assoc]

/-- The blocks of `[X, P]` when `ν ∈ [a, b]` and `μ ∉ [a, b]`. -/
theorem block_lie_P_of_not_mem_of_mem (X : E →L[ℂ] E) {μ ν : ℝ}
    (hμ : μ ∉ Set.Icc S.a S.b) (hν : ν ∈ Set.Icc S.a S.b) :
    eigProj S.H S.H_sa μ * ⁅X, S.P⁆ * eigProj S.H S.H_sa ν =
      eigProj S.H S.H_sa μ * X * eigProj S.H S.H_sa ν * S.Psec := by
  rw [S.block_lie_P, S.P_mul_eigProj_of_mem hν, S.eigProj_mul_P_of_not_mem hμ, zero_mul,
    zero_mul, sub_zero, ← mul_assoc]

/-- The blocks of `[X, P]` for a sector-preserving `X`, when `μ ∈ [a, b]` and `ν ∉ [a, b]`. -/
theorem block_lie_P_of_mem_of_not_mem {X : E →L[ℂ] E} (hX : Commute S.Psec X) {μ ν : ℝ}
    (hμ : μ ∈ Set.Icc S.a S.b) (hν : ν ∉ Set.Icc S.a S.b) :
    eigProj S.H S.H_sa μ * ⁅X, S.P⁆ * eigProj S.H S.H_sa ν =
      -(eigProj S.H S.H_sa μ * X * eigProj S.H S.H_sa ν * S.Psec) := by
  rw [S.block_lie_P, S.P_mul_eigProj_of_not_mem hν, S.eigProj_mul_P_of_mem hμ, mul_zero,
    zero_sub, S.block_Psec_swap hX]

/-- The blocks of `[X, P]` vanish for a sector-preserving `X` when `μ, ν ∈ [a, b]`. -/
theorem block_lie_P_of_mem_of_mem {X : E →L[ℂ] E} (hX : Commute S.Psec X) {μ ν : ℝ}
    (hμ : μ ∈ Set.Icc S.a S.b) (hν : ν ∈ Set.Icc S.a S.b) :
    eigProj S.H S.H_sa μ * ⁅X, S.P⁆ * eigProj S.H S.H_sa ν = 0 := by
  rw [S.block_lie_P, S.P_mul_eigProj_of_mem hν, S.eigProj_mul_P_of_mem hμ,
    ← S.block_Psec_swap hX]
  simp only [mul_assoc, sub_self]

/-- The blocks of `[X, P]` vanish when `μ, ν ∉ [a, b]`. -/
theorem block_lie_P_of_not_mem_of_not_mem (X : E →L[ℂ] E) {μ ν : ℝ}
    (hμ : μ ∉ Set.Icc S.a S.b) (hν : ν ∉ Set.Icc S.a S.b) :
    eigProj S.H S.H_sa μ * ⁅X, S.P⁆ * eigProj S.H S.H_sa ν = 0 := by
  rw [S.block_lie_P, S.P_mul_eigProj_of_not_mem hν, S.eigProj_mul_P_of_not_mem hμ]
  simp

end Setting

end HRTorus.IndexCore
