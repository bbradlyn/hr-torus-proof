import HRTorus.IndexCore.Translation
import HRTorus.IndexCore.Sanity

/-!
# The general-`N` non-vacuity instance of the orbital structure

Written by Claude Opus 5.5 (an AI model), 2026-10-23. One particle on the ring `ℤ_{2N}`, for every `N ≥ 1`
(the hypothesis `[NeZero N]`):

* `E = ℓ²(ℤ_{2N}) = EuclideanSpace ℂ (ZMod (2N))`, with `e_j` its standard basis;
* `n_j = |e_j⟩⟨e_j|` and `Θ = ∑_j |e_{j-1}⟩⟨e_j|`, so that `Θ e_j = e_{j-1}`, `Θ^* e_j = e_{j+1}`
  and `Θ^* n_j Θ = n_{j+1}`;
* `H = 0`, `Π = 1`, `nup = 1` (`∑_j n_j = 1`), `J_± = 0`, `\widehat W(ω) = i/ω`,
  `g = 1_{(-∞, -1]}`, `γ = 1`, `Δ = 0`, `a = b = 0`;
* the bands are the paper's quarters of `Γ = {0, …, N-1}` (`quarters_partition`).

Then `P = 1`, `p = 2N`, `K_± = 0`, `𝒬 = 0`, every field of `Orbital.Inputs` holds with `ε = 0`
and `M = 1`, `Tr(P T_-) = -1 = -p · nup / N_φ`, and `translation_corollary` gives an integer
within `0` of `p · nup / N_φ = 1` (`nonvacuity`). As with `Sanity.lean` (the core's instance at
`N = 1`), this shows the data and hypotheses jointly satisfiable at `ε = 0` with `P = 1`: it
exercises the exact relations of the orbital structure, not the `ε`-parts of the argument.
-/

open scoped InnerProductSpace ComplexConjugate Real
open Complex (I)

noncomputable section

namespace HRTorus.IndexCore

namespace OrbitalRing

section Defs

variable (N : ℕ) [NeZero N]

/-- `2N ≠ 0`. -/
instance neZero_two_mul : NeZero (2 * N) := ⟨by have := NeZero.ne N; omega⟩

/-- `ℓ²(ℤ_{2N})`. -/
abbrev EN : Type := EuclideanSpace ℂ (ZMod (2 * N))

/-- The standard orthonormal basis `e_j`, `j ∈ ℤ_{2N}`. -/
def e : OrthonormalBasis (ZMod (2 * N)) ℂ (EN N) := EuclideanSpace.basisFun (ZMod (2 * N)) ℂ

/-- `|e_i⟩⟨e_j|`. -/
def r (i j : ZMod (2 * N)) : EN N →L[ℂ] EN N := InnerProductSpace.rankOne ℂ (e N i) (e N j)

/-- The translation `Θ = ∑_j |e_{j-1}⟩⟨e_j|`. -/
def Θ : EN N →L[ℂ] EN N := ∑ j, r N (j - 1) j

end Defs

variable {N : ℕ} [NeZero N]

/-! ## The rank-one algebra -/

theorem inner_e (i j : ZMod (2 * N)) : ⟪e N i, e N j⟫_ℂ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp (e N).orthonormal i j

theorem r_mul_r (i j k l : ZMod (2 * N)) :
    r N i j * r N k l = if j = k then r N i l else 0 := by
  rw [r, r, rankOne_mul_rankOne, inner_e]
  split_ifs <;> simp [r]

theorem star_r (i j : ZMod (2 * N)) : star (r N i j) = r N j i := star_rankOne _ _

theorem sum_r : ∑ j, r N j j = 1 := by
  show ∑ j, InnerProductSpace.rankOne ℂ (e N j) (e N j) = 1
  rw [(e N).sum_rankOne_eq_id, ContinuousLinearMap.one_def]

theorem isIdempotentElem_r (j : ZMod (2 * N)) : IsIdempotentElem (r N j j) := by
  show r N j j * r N j j = r N j j
  rw [r_mul_r]
  simp

theorem isStarProjection_r (j : ZMod (2 * N)) : IsStarProjection (r N j j) :=
  ⟨isIdempotentElem_r j, star_r j j⟩

theorem commute_r (i j : ZMod (2 * N)) : Commute (r N i i) (r N j j) := by
  show r N i i * r N j j = r N j j * r N i i
  rw [r_mul_r, r_mul_r]
  by_cases h : i = j
  · subst h; rfl
  · simp [h, Ne.symm h]

/-! ## The translation -/

theorem star_Θ : star (Θ N) = ∑ j, r N j (j - 1) :=
  (star_sum Finset.univ fun j => r N (j - 1) j).trans
    (Finset.sum_congr rfl fun j _ => star_r (j - 1) j)

theorem star_Θ_mul_Θ : star (Θ N) * Θ N = 1 := by
  rw [star_Θ, Θ, Finset.sum_mul]
  simp_rw [Finset.mul_sum, r_mul_r, sub_left_inj]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact sum_r

theorem Θ_mul_star_Θ : Θ N * star (Θ N) = 1 := by
  rw [star_Θ, Θ, Finset.sum_mul]
  simp_rw [Finset.mul_sum, r_mul_r]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← sum_r (N := N)]
  exact Equiv.sum_comp (Equiv.subRight 1) (fun j => r N j j)

theorem Θ_mem_unitary : Θ N ∈ unitary (EN N →L[ℂ] EN N) :=
  Unitary.mem_iff.2 ⟨star_Θ_mul_Θ, Θ_mul_star_Θ⟩

theorem star_Θ_mul_r (j : ZMod (2 * N)) : star (Θ N) * r N j j = r N (j + 1) j := by
  rw [star_Θ, Finset.sum_mul]
  simp_rw [r_mul_r, sub_eq_iff_eq_add]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem r_mul_Θ (i j : ZMod (2 * N)) : r N i j * Θ N = r N i (j + 1) := by
  rw [Θ, Finset.mul_sum]
  simp_rw [r_mul_r, eq_sub_iff_add_eq]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- `Θ^* n_j Θ = n_{j+1}`. -/
theorem Θ_conj_r (j : ZMod (2 * N)) : star (Θ N) * r N j j * Θ N = r N (j + 1) (j + 1) := by
  rw [star_Θ_mul_r, r_mul_Θ]

/-! ## The instance -/

variable (N) in
/-- The orbital structure of one particle on the ring `ℤ_{2N}`. -/
def S : Orbital (EN N) where
  H := 0
  H_sa := IsSelfAdjoint.zero _
  Psec := 1
  Psec_proj := IsStarProjection.one _
  Psec_H := Commute.one_left _
  Nφ := 2 * N
  Nφ_neZero := inferInstance
  N := N
  N_le_Nφ := by omega
  n := fun j => r N j j
  n_sa := fun j => star_r j j
  n_comm := fun i j => commute_r i j
  exp_n := fun j => exp_two_pi_I_smul_of_isIdempotentElem (isIdempotentElem_r j)
  Psec_n := fun _ => Commute.one_left _
  nup := 1
  sum_n_Psec := by
    show (∑ j, r N j j) * 1 = ((1 : ℕ) : ℂ) • (1 : EN N →L[ℂ] EN N)
    rw [mul_one, sum_r, Nat.cast_one, one_smul]
  Γminus := quarterMinus (2 * N) N
  Γmid := quarterMid (2 * N) N
  Γplus := quarterPlus (2 * N) N
  disjoint_minus_mid := (quarters_partition (by omega)).1
  disjoint_minus_plus := (quarters_partition (by omega)).2.1
  disjoint_mid_plus := (quarters_partition (by omega)).2.2.1
  bands_union := (quarters_partition (by omega)).2.2.2
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
  Θ := Θ N
  Θ_unitary := Θ_mem_unitary
  Psec_Θ := Commute.one_left _
  Θ_H := Commute.zero_right _
  Θ_n := fun j => Θ_conj_r j
  Jminus := 0
  Jplus := 0
  Jminus_sa := IsSelfAdjoint.zero _
  Jplus_sa := IsSelfAdjoint.zero _
  Psec_Jminus := Commute.zero_right _
  Psec_Jplus := Commute.zero_right _
  current_split := by rw [add_zero, Ring.lie_def, zero_mul, mul_zero, sub_zero, smul_zero]
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

theorem S_nup : (S N).nup = 1 := rfl

theorem S_Nφ : (S N).Nφ = 2 * N := rfl

/-! ## The spectral data of `H = 0` (as in `Sanity.lean`) -/

theorem eigVal_eq_zero (i : Fin (Module.finrank ℂ (EN N))) :
    eigVal (S N).toSetting.H (S N).toSetting.H_sa i = 0 := by
  have h := apply_eigBasis (S N).toSetting.H (S N).toSetting.H_sa i
  have hz : ((eigVal (S N).toSetting.H (S N).toSetting.H_sa i : ℝ) : ℂ) •
      eigBasis (S N).toSetting.H (S N).toSetting.H_sa i = 0 := h.symm
  rcases smul_eq_zero.mp hz with h1 | h1
  · exact_mod_cast h1
  · exact absurd h1 ((eigBasis (S N).toSetting.H (S N).toSetting.H_sa).orthonormal.ne_zero i)

theorem mem_spec_eq_zero {μ : ℝ} (hμ : μ ∈ spec (S N).toSetting.H (S N).toSetting.H_sa) :
    μ = 0 := by
  obtain ⟨i, rfl⟩ := (mem_spec_iff (S N).toSetting.H (S N).toSetting.H_sa μ).1 hμ
  exact eigVal_eq_zero i

/-- `P = 1`. -/
theorem S_P : (S N).toSetting.P = 1 := by
  have hS : specProj (S N).toSetting.H (S N).toSetting.H_sa
      (Set.Icc (S N).toSetting.a (S N).toSetting.b) = 1 := by
    calc specProj (S N).toSetting.H (S N).toSetting.H_sa
          (Set.Icc (S N).toSetting.a (S N).toSetting.b)
        = specProj (S N).toSetting.H (S N).toSetting.H_sa
            (Set.Icc (S N).toSetting.a (S N).toSetting.b) *
          ∑ μ ∈ spec (S N).toSetting.H (S N).toSetting.H_sa,
            eigProj (S N).toSetting.H (S N).toSetting.H_sa μ := by
          rw [sum_eigProj, mul_one]
      _ = ∑ μ ∈ spec (S N).toSetting.H (S N).toSetting.H_sa,
            eigProj (S N).toSetting.H (S N).toSetting.H_sa μ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun μ hμ =>
            specProj_mul_eigProj_of_mem (S N).toSetting.H (S N).toSetting.H_sa ?_
          rw [mem_spec_eq_zero hμ]
          exact ⟨le_rfl, le_rfl⟩
      _ = 1 := sum_eigProj _ _
  rw [Setting.P_def, hS]
  exact mul_one 1

theorem S_Kminus : (S N).toSetting.Kminus = 0 := by
  simp only [Setting.Kminus, spectralSum_def]
  exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by
    show _ • (_ * (0 : EN N →L[ℂ] EN N) * _) = 0
    rw [mul_zero, zero_mul, smul_zero]

theorem S_Kplus : (S N).toSetting.Kplus = 0 := by
  simp only [Setting.Kplus, spectralSum_def]
  exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by
    show _ • (_ * (0 : EN N →L[ℂ] EN N) * _) = 0
    rw [mul_zero, zero_mul, smul_zero]

theorem S_KUminus : (S N).toSetting.KUminus = 0 := by
  rw [Setting.KUminus, S_Kminus, mul_zero, zero_mul]

theorem S_KUplus : (S N).toSetting.KUplus = 0 := by
  rw [Setting.KUplus, S_Kplus, mul_zero, zero_mul]

theorem S_Qf (A : EN N →L[ℂ] EN N) : (S N).toSetting.Qf A = 0 := by
  simp only [Setting.Qf, spectralSum_def]
  refine Finset.sum_eq_zero fun μ hμ => Finset.sum_eq_zero fun ν hν => ?_
  rw [mem_spec_eq_zero hμ, mem_spec_eq_zero hν, sub_zero]
  show (if (0 : ℝ) ≤ -1 then (1 : ℂ) else 0) • _ = 0
  have : ¬ (0 : ℝ) ≤ -1 := by norm_num
  simp [this]

/-- `p = 2N`. -/
theorem S_p : (S N).toSetting.p = 2 * N := by
  rw [Setting.p, S_P, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id,
    LinearMap.range_id, finrank_top, finrank_euclideanSpace, ZMod.card]

/-! ## Every input with `ε = 0` and `M = 1` -/

theorem norm_lie_zero_left (X : EN N →L[ℂ] EN N) : ‖⁅(0 : EN N →L[ℂ] EN N), X⁆‖ ≤ 0 := by
  rw [Ring.lie_def, zero_mul, mul_zero, sub_zero, norm_zero]

theorem norm_lie_zero_right (X : EN N →L[ℂ] EN N) : ‖⁅X, (0 : EN N →L[ℂ] EN N)⁆‖ ≤ 0 := by
  rw [Ring.lie_def, zero_mul, mul_zero, sub_zero, norm_zero]

/-- Every field of `Orbital.Inputs` holds with `ε = 0` and `M = 1`. -/
theorem inputs : (S N).Inputs 0 1 where
  sep_Kminus_Qmid := by rw [S_Kminus]; exact norm_lie_zero_left _
  sep_KUminus_Qmid := by rw [S_KUminus]; exact norm_lie_zero_left _
  sep_Kplus_Qmid := by rw [S_Kplus]; exact norm_lie_zero_left _
  sep_KUplus_Qmid := by rw [S_KUplus]; exact norm_lie_zero_left _
  sep_Qminus_Kplus := by rw [S_Kplus]; exact norm_lie_zero_right _
  sep_Qminus_KUplus := by rw [S_KUplus]; exact norm_lie_zero_right _
  sep_Kminus_Qplus := by rw [S_Kminus]; exact norm_lie_zero_left _
  sep_KUminus_Qplus := by rw [S_KUminus]; exact norm_lie_zero_left _
  sep_Tminus_Kplus := by rw [S_Kplus]; exact norm_lie_zero_right _
  sep_Tminus_KUplus := by rw [S_KUplus]; exact norm_lie_zero_right _
  sep_Kminus_Tplus := by rw [S_Kminus]; exact norm_lie_zero_left _
  sep_Kminus_Kplus := by rw [S_Kminus]; exact norm_lie_zero_left _
  sep_Kminus_KUplus := by rw [S_Kminus]; exact norm_lie_zero_left _
  sep_KUminus_Tplus := by rw [S_KUminus]; exact norm_lie_zero_left _
  sep_KUminus_Kplus := by rw [S_KUminus]; exact norm_lie_zero_left _
  sep_KUminus_KUplus := by rw [S_KUminus]; exact norm_lie_zero_left _
  clu_M := fun _ _ => by rw [S_Qf]; exact norm_lie_zero_left _
  clu_M_adj := fun _ _ => by rw [S_Qf]; exact norm_lie_zero_left _
  clu_O := by rw [S_Qf]; exact norm_lie_zero_left _
  clu_O_adj := by rw [S_Qf]; exact norm_lie_zero_left _
  norm_n_zero := IsStarProjection.norm_le _ (isStarProjection_r 0)
  norm_Kminus := by rw [S_Kminus, norm_zero]; exact zero_le_one

/-- `Tr(P T_-) = -1`, from Lemma 7.1(d) (`Orbital.trc_P_Tminus`) with `p = 2N`, `nup = 1`,
`N_φ = 2N`. -/
theorem trc_P_Tminus_eq_neg_one : trc ((S N).toSetting.P * (S N).toSetting.Tminus) = -1 := by
  rw [(S N).trc_P_Tminus, S_p, S_nup, S_Nφ, Nat.cast_one, mul_one,
    div_self (Nat.cast_ne_zero.2 (NeZero.ne (2 * N)))]

/-- `p · nup / N_φ = 1`. -/
theorem ratio_eq_one : ((S N).toSetting.p : ℝ) * (S N).nup / (S N).Nφ = 1 := by
  rw [S_p, S_nup, S_Nφ, Nat.cast_one, mul_one, div_self (Nat.cast_ne_zero.2 (NeZero.ne (2 * N)))]

/-- **The general-`N` non-vacuity instance.** For every `N ≥ 1` (`[NeZero N]`), on `ℓ²(ℤ_{2N})`:
every input of `translation_corollary` holds with `ε = 0` and `M = 1`; `P = 1`, `p = 2N`,
`Tr(P T_-) = -1`, `p · nup / N_φ = 1`; and `translation_corollary`, applied to these inputs,
gives an integer within `400 p (1 + 1) √0 = 0` of `p · nup / N_φ`. -/
theorem nonvacuity :
    (S N).Inputs 0 1 ∧ (S N).toSetting.P = 1 ∧ (S N).toSetting.p = 2 * N ∧
      trc ((S N).toSetting.P * (S N).toSetting.Tminus) = -1 ∧
      ((S N).toSetting.p : ℝ) * (S N).nup / (S N).Nφ = 1 ∧
      ∃ k : ℤ, |((S N).toSetting.p : ℝ) * (S N).nup / (S N).Nφ - k| ≤
        400 * (S N).toSetting.p * (1 + 1) * √0 :=
  ⟨inputs, S_P, S_p, trc_P_Tminus_eq_neg_one, ratio_eq_one, Orbital.translation_corollary inputs⟩

end OrbitalRing

end HRTorus.IndexCore

end -- noncomputable section

#check @HRTorus.IndexCore.OrbitalRing.nonvacuity
#print axioms HRTorus.IndexCore.OrbitalRing.nonvacuity
