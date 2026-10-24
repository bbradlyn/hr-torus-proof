import HRTorus.IndexCore.Main

/-!
# The non-vacuity instance

Written by Claude Opus 5.5 (an AI model), 2026-10-23. This file builds an instance satisfying every
hypothesis of `index_core` with `T₋ ≠ 0`, on the
ring `ℓ²(ℤ_{2N})` for `N = 1`, that is on `ℓ²(ℤ₂) = ℂ²` with the standard basis `e₀, e₁`:

* `H = 0`, `Π = 1`, `[a, b] = [0, 0]`, `Δ = 0`, `γ = 1` (so `P = 1` and `p = 2`);
* the band `Γ = {0}`: `Q₋ = n₀ = |e₀⟩⟨e₀|`, `Q_m = Q₊ = 0`;
* `U` the shift `e_j ↦ e_{j-1}` (on `ℤ₂`: `e₀ ↦ e₁ ↦ e₀`), so `U^* Q U - Q = n₁ - n₀`, and
  `T₋ = -n₀`, `T₊ = n₁ = n_N`;
* `J_± = 0`, hence `K_± = 0`; `\widehat W_γ(ω) = i/ω`; `g = 1` on `(-∞, -1]` and `0` elsewhere,
  hence `𝒬 = 0` (all eigenvalues of `H` are `0` and `g 0 = 0`).

Every hypothesis of `index_core` holds with `ε = 0` and `M = 1`, and `Tr(P T₋) = -1`
(`sanity`). The general-`N` ring is the same construction with more bookkeeping; it is not done
here.
-/

open scoped InnerProductSpace ComplexConjugate Real Nat
open Complex (I)

noncomputable section

namespace HRTorus.IndexCore

/-- `exp (z p) = 1 + (e^z - 1) p` for an idempotent `p` of a complete normed `ℂ`-algebra. -/
theorem exp_smul_of_isIdempotentElem {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]
    [CompleteSpace 𝔸] {p : 𝔸} (hp : IsIdempotentElem p) (z : ℂ) :
    NormedSpace.exp (z • p) = 1 + (Complex.exp z - 1) • p := by
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) (z • p)
  have hsz := NormedSpace.expSeries_summable' (𝕂 := ℂ) z
  have h1 : ∀ n : ℕ, ((n + 1)! ⁻¹ : ℂ) • (z • p) ^ (n + 1) =
      (((n + 1)! ⁻¹ : ℂ) * z ^ (n + 1)) • p := by
    intro n; rw [smul_pow, hp.pow_succ_eq n, smul_smul]
  have hc : Summable fun n : ℕ => (((n + 1)! ⁻¹ : ℂ) * z ^ (n + 1)) := by
    have := (summable_nat_add_iff 1).2 hsz
    simpa only [smul_eq_mul] using this
  have hez : Complex.exp z - 1 = ∑' n : ℕ, (((n + 1)! ⁻¹ : ℂ) * z ^ (n + 1)) := by
    have e : NormedSpace.exp z = ∑' n : ℕ, (n ! ⁻¹ : ℂ) • z ^ n :=
      congrFun (NormedSpace.exp_eq_tsum ℂ) z
    rw [← Complex.exp_eq_exp_ℂ] at e
    rw [e, hsz.tsum_eq_zero_add]
    simp [smul_eq_mul]
  have e1 : NormedSpace.exp (z • p) = ∑' n : ℕ, (n ! ⁻¹ : ℂ) • (z • p) ^ n :=
    congrFun (NormedSpace.exp_eq_tsum ℂ) (z • p)
  rw [e1, hs.tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, h1]
  rw [hc.tsum_smul_const, ← hez]

/-- `e^{2πi p} = 1` for an idempotent `p`. -/
theorem exp_two_pi_I_smul_of_isIdempotentElem {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]
    [CompleteSpace 𝔸] {p : 𝔸} (hp : IsIdempotentElem p) :
    NormedSpace.exp ((2 * π * I) • p) = 1 := by
  rw [exp_smul_of_isIdempotentElem hp, Complex.exp_two_pi_mul_I, sub_self, zero_smul, add_zero]

namespace Sanity

/-- `ℓ²(ℤ₂) = ℂ²`. -/
abbrev E2 : Type := EuclideanSpace ℂ (Fin 2)

/-- The standard orthonormal basis `e₀, e₁`. -/
def e : OrthonormalBasis (Fin 2) ℂ E2 := EuclideanSpace.basisFun (Fin 2) ℂ

/-- `|eᵢ⟩⟨eⱼ|`. -/
def r (i j : Fin 2) : E2 →L[ℂ] E2 := InnerProductSpace.rankOne ℂ (e i) (e j)

theorem inner_e (i j : Fin 2) : ⟪e i, e j⟫_ℂ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp e.orthonormal i j

theorem r_mul_r (i j k l : Fin 2) : r i j * r k l = if j = k then r i l else 0 := by
  rw [r, r, rankOne_mul_rankOne, inner_e]
  split_ifs <;> simp [r]

theorem star_r (i j : Fin 2) : star (r i j) = r j i := star_rankOne _ _

theorem r00_add_r11 : r 0 0 + r 1 1 = 1 := by
  have h := e.sum_rankOne_eq_id
  rw [Fin.sum_univ_two] at h
  rw [r, r, h, ContinuousLinearMap.one_def]

/-- The shift `e_j ↦ e_{j-1}` on `ℓ²(ℤ₂)`: `e₀ ↦ e₁ ↦ e₀`. -/
def shift : E2 →L[ℂ] E2 := r 1 0 + r 0 1

theorem star_shift : star shift = shift :=
  (star_add (r 1 0) (r 0 1)).trans (by rw [star_r, star_r, add_comm]; rfl)

theorem shift_mul_shift : shift * shift = 1 := by
  simp only [shift, add_mul, mul_add, r_mul_r]
  simp only [Fin.isValue, zero_ne_one, one_ne_zero, ite_false, ite_true, zero_add, add_zero]
  exact r00_add_r11

theorem shift_mem_unitary : shift ∈ unitary (E2 →L[ℂ] E2) := by
  rw [Unitary.mem_iff, star_shift, shift_mul_shift]; exact ⟨rfl, rfl⟩

theorem isIdempotentElem_r (i : Fin 2) : IsIdempotentElem (r i i) := by
  show r i i * r i i = r i i
  rw [r_mul_r]; simp

theorem isStarProjection_r (i : Fin 2) : IsStarProjection (r i i) :=
  ⟨isIdempotentElem_r i, star_r i i⟩

theorem commute_r00_r11 : Commute (r 0 0) (r 1 1) := by
  show r 0 0 * r 1 1 = r 1 1 * r 0 0
  rw [r_mul_r, r_mul_r]; simp

theorem r00_mul_r11 : r 0 0 * r 1 1 = 0 := by rw [r_mul_r]; simp

theorem r11_mul_r00 : r 1 1 * r 0 0 = 0 := by rw [r_mul_r]; simp

theorem shift_conj_r00 : star shift * r 0 0 * shift = r 1 1 := by
  rw [star_shift]
  simp [shift, add_mul, mul_add, r_mul_r]

/-- The instance. -/
def S : Setting E2 where
  H := 0
  H_sa := IsSelfAdjoint.zero _
  Psec := 1
  Psec_proj := IsStarProjection.one _
  Psec_H := Commute.one_left _
  Qminus := r 0 0
  Qmid := 0
  Qplus := 0
  Qminus_sa := star_r 0 0
  Qmid_sa := IsSelfAdjoint.zero _
  Qplus_sa := IsSelfAdjoint.zero _
  comm_Qminus_Qmid := Commute.zero_right _
  comm_Qmid_Qplus := Commute.zero_left _
  comm_Qminus_Qplus := Commute.zero_right _
  exp_Qminus := exp_two_pi_I_smul_of_isIdempotentElem (isIdempotentElem_r 0)
  exp_Qmid := by rw [smul_zero, NormedSpace.exp_zero]
  exp_Qplus := by rw [smul_zero, NormedSpace.exp_zero]
  Psec_Qminus := Commute.one_left _
  Psec_Qmid := Commute.one_left _
  Psec_Qplus := Commute.one_left _
  γ := 1
  Δ := 0
  a := 0
  b := 0
  Δ_nonneg := le_rfl
  Δ_lt_γ := zero_lt_one
  width := by norm_num
  gap := by
    intro μ v hv _ hHv
    left
    have h0 : (μ : ℂ) • v = 0 := hHv.symm
    rcases smul_eq_zero.mp h0 with h | h
    · have : μ = 0 := by exact_mod_cast h
      simp [this]
    · exact absurd h hv
  U := shift
  U_unitary := shift_mem_unitary
  Psec_U := Commute.one_left _
  Tminus := -r 0 0
  Tplus := r 1 1
  Tminus_sa := IsSelfAdjoint.neg (star_r 0 0)
  Tplus_sa := star_r 1 1
  Psec_Tminus := Commute.one_left _
  Psec_Tplus := Commute.one_left _
  transport := by
    rw [add_zero, add_zero, shift_conj_r00]; abel
  Jminus := 0
  Jplus := 0
  Jminus_sa := IsSelfAdjoint.zero _
  Jplus_sa := IsSelfAdjoint.zero _
  Psec_Jminus := Commute.zero_right _
  Psec_Jplus := Commute.zero_right _
  current_split := by simp [Ring.lie_def]
  W := fun ω => I / ω
  W_eq := fun _ _ => rfl
  W_conj := fun ω => by
    simp only [Complex.ofReal_neg, map_div₀, Complex.conj_I, Complex.conj_ofReal, div_neg,
      neg_div]
  g := fun ω => if ω ≤ -1 then 1 else 0
  g_zero := fun ω hω => by
    have : ¬ ω ≤ -1 := by linarith
    simp [this]
  g_one := fun ω hω => by
    have : ω ≤ -1 := by simpa using hω
    simp [this]

/-! ## The spectral data of `H = 0` -/

theorem eigVal_eq_zero (i : Fin (Module.finrank ℂ E2)) : eigVal S.H S.H_sa i = 0 := by
  have h := apply_eigBasis S.H S.H_sa i
  have hz : ((eigVal S.H S.H_sa i : ℝ) : ℂ) • eigBasis S.H S.H_sa i = 0 := h.symm
  rcases smul_eq_zero.mp hz with h1 | h1
  · exact_mod_cast h1
  · exact absurd h1 ((eigBasis S.H S.H_sa).orthonormal.ne_zero i)

theorem mem_spec_eq_zero {μ : ℝ} (hμ : μ ∈ spec S.H S.H_sa) : μ = 0 := by
  obtain ⟨i, rfl⟩ := (mem_spec_iff S.H S.H_sa μ).1 hμ
  exact eigVal_eq_zero i

theorem S_P : S.P = 1 := by
  have hS : specProj S.H S.H_sa (Set.Icc S.a S.b) = 1 := by
    calc specProj S.H S.H_sa (Set.Icc S.a S.b)
        = specProj S.H S.H_sa (Set.Icc S.a S.b) * ∑ μ ∈ spec S.H S.H_sa, eigProj S.H S.H_sa μ := by
          rw [sum_eigProj, mul_one]
      _ = ∑ μ ∈ spec S.H S.H_sa, eigProj S.H S.H_sa μ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun μ hμ => specProj_mul_eigProj_of_mem S.H S.H_sa ?_
          rw [mem_spec_eq_zero hμ]
          exact ⟨le_rfl, le_rfl⟩
      _ = 1 := sum_eigProj S.H S.H_sa
  rw [Setting.P_def, hS]
  exact mul_one 1

theorem S_Kminus : S.Kminus = 0 := by
  simp only [Setting.Kminus, spectralSum_def]
  exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by
    show _ • (_ * (0 : E2 →L[ℂ] E2) * _) = 0
    rw [mul_zero, zero_mul, smul_zero]

theorem S_Kplus : S.Kplus = 0 := by
  simp only [Setting.Kplus, spectralSum_def]
  exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by
    show _ • (_ * (0 : E2 →L[ℂ] E2) * _) = 0
    rw [mul_zero, zero_mul, smul_zero]

theorem S_KUminus : S.KUminus = 0 := by rw [Setting.KUminus, S_Kminus, mul_zero, zero_mul]

theorem S_KUplus : S.KUplus = 0 := by rw [Setting.KUplus, S_Kplus, mul_zero, zero_mul]

theorem S_Qf (A : E2 →L[ℂ] E2) : S.Qf A = 0 := by
  simp only [Setting.Qf, spectralSum_def]
  refine Finset.sum_eq_zero fun μ hμ => Finset.sum_eq_zero fun ν hν => ?_
  rw [mem_spec_eq_zero hμ, mem_spec_eq_zero hν, sub_zero]
  show (if (0 : ℝ) ≤ -1 then (1 : ℂ) else 0) • _ = 0
  have : ¬ (0 : ℝ) ≤ -1 := by norm_num
  simp [this]

theorem S_p : S.p = 2 := by
  rw [Setting.p, S_P, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id, LinearMap.range_id,
    finrank_top, finrank_euclideanSpace_fin]

/-! ## Every hypothesis of `index_core` with `ε = 0` and `M = 1` -/

theorem norm_lie_zero_left (X : E2 →L[ℂ] E2) : ‖⁅(0 : E2 →L[ℂ] E2), X⁆‖ ≤ 0 := by
  rw [Ring.lie_def, zero_mul, mul_zero, sub_zero, norm_zero]

theorem norm_lie_zero_right (X : E2 →L[ℂ] E2) : ‖⁅X, (0 : E2 →L[ℂ] E2)⁆‖ ≤ 0 := by
  rw [Ring.lie_def, zero_mul, mul_zero, sub_zero, norm_zero]

theorem hU2 : ‖⁅S.U, S.P⁆‖ ≤ 0 := by
  rw [S_P, Ring.lie_def, mul_one, one_mul, sub_self, norm_zero]

theorem hU4 : ‖NormedSpace.exp ((2 * π * I) • (S.Q + S.Tplus)) - 1‖ ≤ 0 := by
  have hQT : S.Q + S.Tplus = 1 := by
    show r 0 0 + 0 + 0 + r 1 1 = 1
    rw [add_zero, add_zero]; exact r00_add_r11
  have h1 : NormedSpace.exp ((2 * π * I) • (1 : E2 →L[ℂ] E2)) = 1 :=
    exp_two_pi_I_smul_of_isIdempotentElem (𝔸 := E2 →L[ℂ] E2) IsIdempotentElem.one
  rw [hQT, h1, sub_self, norm_zero]

theorem sep_Qminus_Tplus : ‖⁅S.Qminus, S.Tplus⁆‖ ≤ 0 := by
  show ‖⁅r 0 0, r 1 1⁆‖ ≤ 0
  rw [commute_r00_r11.lie_eq, norm_zero]

theorem sep_Tminus_Tplus : ‖⁅S.Tminus, S.Tplus⁆‖ ≤ 0 := by
  show ‖⁅-r 0 0, r 1 1⁆‖ ≤ 0
  rw [commute_r00_r11.neg_left.lie_eq, norm_zero]

theorem norm_Tminus_le : ‖S.Tminus‖ ≤ 1 := by
  show ‖-r 0 0‖ ≤ 1
  rw [norm_neg]; exact IsStarProjection.norm_le _ (isStarProjection_r 0)

theorem norm_Kminus_le : ‖S.Kminus‖ ≤ 1 := by rw [S_Kminus, norm_zero]; exact zero_le_one

/-- `Tr(P T₋) = -1`. -/
theorem trace_P_Tminus :
    LinearMap.trace ℂ E2 (S.P * S.Tminus : E2 →L[ℂ] E2).toLinearMap = -1 := by
  have h : (S.P * S.Tminus : E2 →L[ℂ] E2) = -r 0 0 := by
    rw [S_P, one_mul]; rfl
  rw [h, ContinuousLinearMap.toLinearMap_neg, map_neg]
  have ht := InnerProductSpace.trace_rankOne (𝕜 := ℂ) (e 0) (e 0)
  rw [show (r 0 0 : E2 →L[ℂ] E2) = InnerProductSpace.rankOne ℂ (e 0) (e 0) from rfl]
  rw [ht, inner_e]; simp

/-- **The non-vacuity instance.** On `ℓ²(ℤ₂)` with the shift, every hypothesis of
`index_core` holds with `ε = 0` and `M = 1`, `p = 2`, and `Tr(P T₋) = -1`; `index_core` then gives
an integer `n` with `‖Tr(P T₋) - n‖ ≤ 0`. -/
theorem sanity :
    LinearMap.trace ℂ E2 (S.P * S.Tminus : E2 →L[ℂ] E2).toLinearMap = -1 ∧ S.p = 2 ∧
    ∃ n : ℤ, ‖LinearMap.trace ℂ E2 (S.P * S.Tminus : E2 →L[ℂ] E2).toLinearMap - n‖ ≤
      indexConst S.p 1 * √0 := by
  refine ⟨trace_P_Tminus, S_p, ?_⟩
  have z := norm_lie_zero_left
  have z' := norm_lie_zero_right
  exact index_core S 0 1 hU2 hU4
    (by rw [S_Kminus]; exact z _) (by rw [S_KUminus]; exact z _) (by rw [S_Kplus]; exact z _)
    (by rw [S_KUplus]; exact z _) (z' _) (z' _)
    (by rw [S_Kplus]; exact z' _) (by rw [S_KUplus]; exact z' _) (by rw [S_Kminus]; exact z _)
    (by rw [S_KUminus]; exact z _) sep_Qminus_Tplus (z' _) sep_Tminus_Tplus
    (by rw [S_Kplus]; exact z' _) (by rw [S_KUplus]; exact z' _) (by rw [S_Kminus]; exact z _)
    (by rw [S_Kminus]; exact z _) (by rw [S_Kminus]; exact z _) (by rw [S_KUminus]; exact z _)
    (by rw [S_KUminus]; exact z _) (by rw [S_KUminus]; exact z _)
    (fun x _ => by rw [S_Qf]; exact z _) (fun x _ => by rw [S_Qf]; exact z _)
    (by rw [S_Qf]; exact z _) (by rw [S_Qf]; exact z _) norm_Tminus_le norm_Kminus_le

end Sanity

end HRTorus.IndexCore

#print axioms HRTorus.IndexCore.Sanity.sanity
