import HRTorus.LLL.Space
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Field.GeomSum

/-!
# The slot frame in `𝔥_N`, the analysis map and Parseval (T-0056 block A, `LLL.Frame`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **The definitions and statements were written
first and reviewed against the paper (phase (a)) and are unchanged; phase (b) added the proofs and the proof
devices, each section of which is marked as such. Every theorem is proved; there is no `sorry`.** The paper: the HR paper, `papers/hr/sections/03-slot-frame.tex` —
Definition 3.1 `def:frame` (the frame vectors (3.1) `eq:zs` and the analysis map), Proposition 3.3
`prop:parseval`, and Lemma 3.5(iii) `lem:localization` in its original form, with the identity
`(𝒮 e_R)_s = \overline{z_s(R)}` from its proof.

## The model

* The slot lattice, the windows `w_a`, the sets `I_a` and `n_y` are `SlotFrame`'s (`Slot`, `wa`, `Ia`, `ny`);
  the frame vector `z_s ∈ 𝔥_N` is the finite sum (3.1) on the orbital basis (`frameVec`), and the function it
  represents is `SlotFrame.frame` (`toFun_frameVec`), the `z_s(R)` of Lemma 3.5.
* `ℓ²(Λ_N)` is `EuclideanSpace ℂ (Slot δ₀ T)` (`SlotSpace`); the paper's analysis map `𝒮` (`\Sa`, written `𝒜` in
  the brief) is the linear map `analysis`, `(𝒮f)_s := ⟨z_s, f⟩` literally; `𝒮 ⊗ 1_{ℂ²}` is `analysis2`.
* The profile `η` and the target width `δ₀` are parameters, as in `SlotFrame`; the statements that need it
  assume `IsProfile η`, `0 < δ₀` and an admissible torus, as Proposition 3.3 and Lemma 3.5 do.
* §3.1 states no intertwining of `𝒮` with `θ_x` and a translation of the slot lattice (`θ_x` shifts by `κ`,
  the slots by `δ_x`); none is stated here. The covariance the proof uses is Lemma 4.5, on the physical side.
-/

open MeasureTheory
open scoped InnerProductSpace Real
open Complex (I)

noncomputable section

namespace HRTorus.LLL

open HRTorus.SlotFrame
open HRTorus.Fermion.Pilot.JW (Spin Mode)

/-- **Definition 3.1**, (3.1): "`z_s:=\ny^{-1/2}\sum_{j\in I_a}w_a(j)\,e^{-2\pi\iu j\ell/\ny}\,\psi_{[j]}\in\hN,\qquad s=(a,\ell)\in\Slots`",
with `a ∈ {0, …, n_x − 1}` and `ℓ ∈ {0, …, n_y − 1}` the representatives (`Slot δ₀ T = Fin n_x × Fin n_y`) and
`[j]` the class of `j` in `ℤ_{N_φ}`. -/
def frameVec (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (s : Slot δ₀ T) : Space T :=
  (((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
    ∑ j ∈ Ia δ₀ T ((s.1 : ℕ) : ℤ),
      (((wa η δ₀ T ((s.1 : ℕ) : ℤ) j : ℝ) : ℂ) *
          Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (((s.2 : ℕ) : ℤ) : ℂ) / ((ny δ₀ T : ℕ) : ℂ)))) •
        orb T (j : ZMod T.Nφ)

/-- `ℓ²(Λ_N)`, the functions on the slot lattice with the Euclidean inner product. -/
abbrev SlotSpace (δ₀ : ℝ) (T : Torus) : Type := EuclideanSpace ℂ (Slot δ₀ T)

/-- **Definition 3.1**, the analysis map: "`The \emph{analysis map} is $\Sa:\hN\to\ell^2(\Slots)$, $(\Sa f)_s:=\ip{z_s}{f}$`"
(the inner product conjugate-linear in the first argument, as Mathlib's). -/
def analysis (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) : Space T →ₗ[ℂ] SlotSpace δ₀ T :=
  (WithLp.linearEquiv 2 ℂ (Slot δ₀ T → ℂ)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun s => innerₛₗ ℂ (frameVec η δ₀ T s)

/-- **Definition 3.1**: "`we write $\Sa$ also for $\Sa\otimes\one_{\C^2}:\kN\to\ell^2(\Slots)\otimes\C^2$`" —
`((𝒮 ⊗ 1)f)_{(s,σ)} := ⟨z_s ⊗ σ, f⟩`, on `ℓ²(Λ_N) ⊗ ℂ² = ℓ²(Λ_N × {↑,↓})`. -/
def analysis2 (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) : Space2 T →ₗ[ℂ] EuclideanSpace ℂ (Mode (Slot δ₀ T)) :=
  (WithLp.linearEquiv 2 ℂ (Mode (Slot δ₀ T) → ℂ)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun μ => innerₛₗ ℂ (spinTensor (frameVec η δ₀ T μ.1) μ.2)

/-- **Lemma 3.5(iii)**: "`where $\one_X$ denotes the orthogonal projection of $\ell^2(\Slots)$ onto the functions
supported in $X$`" — here as the diagonal matrix of the indicator of `X` (`slotProj_apply`,
`slotProj_isStarProjection`). -/
def slotProj (δ₀ : ℝ) (T : Torus) (X : Finset (Slot δ₀ T)) : SlotSpace δ₀ T →L[ℂ] SlotSpace δ₀ T :=
  Matrix.toEuclideanCLM (n := Slot δ₀ T) (𝕜 := ℂ) (Matrix.diagonal fun s => if s ∈ X then 1 else 0)

/-! ### Proof devices (phase (b); not statements of the paper)

The analysis map of any finite family `v` of vectors, `f ↦ (⟨v_i, f⟩)_i`, its adjoint `g ↦ Σ_i g_i v_i`, and the
consequences of `Σ_i |v_i⟩⟨v_i| = 1`; the frame's Gram identity `Σ_s z_s(c) \overline{z_s(c')} = δ_{cc'}` from the
discrete Fourier sum over `ℓ` and the window's partition of unity. -/

section FrameDevices

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The analysis map `f ↦ (⟨v_i, f⟩)_i` of a finite family. -/
def anaMap (v : ι → EuclideanSpace ℂ κ) : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ι :=
  (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap ∘ₗ LinearMap.pi fun i => innerₛₗ ℂ (v i)

theorem anaMap_apply (v : ι → EuclideanSpace ℂ κ) (f : EuclideanSpace ℂ κ) (i : ι) :
    anaMap v f i = ⟪v i, f⟫_ℂ := rfl

theorem adjoint_anaMap_apply (v : ι → EuclideanSpace ℂ κ) (g : EuclideanSpace ℂ ι) :
    LinearMap.adjoint (anaMap v) g = ∑ i, g i • v i := by
  symm
  apply ext_inner_left ℂ
  intro f
  rw [LinearMap.adjoint_inner_right, inner_sum, PiLp.inner_apply (anaMap v f)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, anaMap_apply, RCLike.inner_apply, inner_conj_symm]

theorem adjoint_anaMap_comp_apply (v : ι → EuclideanSpace ℂ κ) (f : EuclideanSpace ℂ κ) :
    LinearMap.adjoint (anaMap v) (anaMap v f) = ∑ i, InnerProductSpace.rankOne ℂ (v i) (v i) f := by
  rw [adjoint_anaMap_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [InnerProductSpace.rankOne_apply, anaMap_apply]

theorem sum_rankOne_eq_one_of (v : ι → EuclideanSpace ℂ κ)
    (h : ∀ c c' : κ, ∑ i, v i c * star (v i c') = if c = c' then 1 else 0) :
    ∑ i, InnerProductSpace.rankOne ℂ (v i) (v i) = (1 : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ) := by
  refine ContinuousLinearMap.ext fun f => PiLp.ext fun c => ?_
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.one_apply]
  simp only [InnerProductSpace.rankOne_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ x, ∑ i, f x * (starRingEnd ℂ) (v i x) * v i c = f x * (if c = x then 1 else 0) := by
    intro x
    rw [← h c x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def]; ring
  simp_rw [e]
  simp

theorem anaMap_isometry_of (v : ι → EuclideanSpace ℂ κ)
    (h : ∑ i, InnerProductSpace.rankOne ℂ (v i) (v i) = (1 : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ)) :
    LinearMap.adjoint (anaMap v) ∘ₗ anaMap v = LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.comp_apply, adjoint_anaMap_comp_apply, ← ContinuousLinearMap.sum_apply, h]
  rfl

theorem norm_anaMap_of (v : ι → EuclideanSpace ℂ κ)
    (h : LinearMap.adjoint (anaMap v) ∘ₗ anaMap v = LinearMap.id) (f : EuclideanSpace ℂ κ) :
    ‖anaMap v f‖ = ‖f‖ := by
  have e : ⟪anaMap v f, anaMap v f⟫_ℂ = ⟪f, f⟫_ℂ := by
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, h, LinearMap.id_apply]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) f, e]

theorem anaMap_comp_adjoint_of (v : ι → EuclideanSpace ℂ κ)
    (h : LinearMap.adjoint (anaMap v) ∘ₗ anaMap v = LinearMap.id) :
    anaMap v ∘ₗ LinearMap.adjoint (anaMap v) =
      ((LinearMap.range (anaMap v)).starProjection : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) := by
  refine LinearMap.ext fun g => ?_
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact LinearMap.mem_range_self _ _
  · rintro w ⟨f, rfl⟩
    rw [← LinearMap.adjoint_inner_left, map_sub, LinearMap.comp_apply, ← LinearMap.comp_apply
      (LinearMap.adjoint (anaMap v)) (anaMap v), h, LinearMap.id_apply, sub_self, inner_zero_left]

theorem finrank_range_anaMap_of (v : ι → EuclideanSpace ℂ κ)
    (h : LinearMap.adjoint (anaMap v) ∘ₗ anaMap v = LinearMap.id) :
    Module.finrank ℂ (LinearMap.range (anaMap v)) = Fintype.card κ := by
  have hinj : Function.Injective (anaMap v) := by
    intro f g hfg
    have := congrArg (LinearMap.adjoint (anaMap v)) hfg
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, h, LinearMap.id_apply, LinearMap.id_apply] at this
  rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace]

end FrameDevices


section FrameGram

variable (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus)

theorem frameVec_apply (s : Slot δ₀ T) (c : ZMod T.Nφ) :
    frameVec η δ₀ T s c = (((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ∑ j ∈ (Ia δ₀ T ((s.1 : ℕ) : ℤ)).filter (fun j : ℤ => (j : ZMod T.Nφ) = c),
        ((wa η δ₀ T ((s.1 : ℕ) : ℤ) j : ℝ) : ℂ) *
          Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (((s.2 : ℕ) : ℤ) : ℂ) / ((ny δ₀ T : ℕ) : ℂ))) := by
  simp only [frameVec, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, orb, smul_eq_mul,
    PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (j : ZMod T.Nφ) = c
  · simp [h]
  · simp [h, Ne.symm h]

/-- The discrete Fourier sum: `Σ_{ℓ < n} e^{−2πikℓ/n} = n δ_{k0}` for `|k| < n`. -/
theorem sum_exp_neg_two_pi (n : ℕ) (hn : 0 < n) (k : ℤ) (hk : |k| < n) :
    ∑ ℓ : Fin n, Complex.exp (-(2 * (π : ℂ) * I * (k : ℂ) * (((ℓ : ℕ) : ℤ) : ℂ) / ((n : ℕ) : ℂ))) =
      if k = 0 then (n : ℂ) else 0 := by
  have hn' : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  split_ifs with h0
  · subst h0; simp
  · set r := Complex.exp (-(2 * (π : ℂ) * I * (k : ℂ) / ((n : ℕ) : ℂ))) with hr
    have hterm : ∀ ℓ : Fin n, Complex.exp (-(2 * (π : ℂ) * I * (k : ℂ) * (((ℓ : ℕ) : ℤ) : ℂ) / ((n : ℕ) : ℂ))) =
        r ^ (ℓ : ℕ) := by
      intro ℓ; rw [hr, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    simp_rw [hterm]
    rw [Fin.sum_univ_eq_sum_range (fun i => r ^ i) n]
    have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hr1 : r ≠ 1 := by
      intro h1
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h1
      have e1 : (2 * π * I : ℂ) * (-(k : ℂ)) = (2 * π * I) * ((m : ℂ) * ((n : ℕ) : ℂ)) := by
        calc (2 * π * I : ℂ) * (-(k : ℂ)) = (-(2 * (π : ℂ) * I * (k : ℂ) / ((n : ℕ) : ℂ))) * ((n : ℕ) : ℂ) := by
              field_simp
          _ = ((m : ℂ) * (2 * π * I)) * ((n : ℕ) : ℂ) := by rw [hm]
          _ = (2 * π * I) * ((m : ℂ) * ((n : ℕ) : ℂ)) := by ring
      have e2 := mul_left_cancel₀ h2pi e1
      have e3 : -k = m * (n : ℤ) := by exact_mod_cast e2
      have hdvd : (n : ℤ) ∣ k := ⟨-m, by linarith⟩
      exact h0 (Int.eq_zero_of_abs_lt_dvd hdvd hk)
    have hrn : r ^ n = 1 := by
      rw [hr, ← Complex.exp_nat_mul, show ((n : ℕ) : ℂ) * -(2 * (π : ℂ) * I * (k : ℂ) / ((n : ℕ) : ℂ)) =
        ((-k : ℤ) : ℂ) * (2 * π * I) by field_simp; push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [geom_sum_eq hr1, hrn, sub_self, zero_div]

theorem abs_sub_lt_ny {δ₀ : ℝ} {T : Torus} {a j j' : ℤ}
    (hj : j ∈ Ia δ₀ T a) (hj' : j' ∈ Ia δ₀ T a) : |j - j'| < (ny δ₀ T : ℤ) := by
  rw [mem_Ia] at hj hj'
  have hκ := T.κ_pos
  have h1 : |T.κ * ((j - j' : ℤ) : ℝ)| < 2 * δx δ₀ T := by
    have : T.κ * ((j - j' : ℤ) : ℝ) = (T.κ * j - xa δ₀ T a) - (T.κ * j' - xa δ₀ T a) := by push_cast; ring
    rw [this]
    calc |(T.κ * j - xa δ₀ T a) - (T.κ * j' - xa δ₀ T a)|
        ≤ |T.κ * j - xa δ₀ T a| + |T.κ * j' - xa δ₀ T a| := abs_sub _ _
      _ < δx δ₀ T + δx δ₀ T := add_lt_add hj hj'
      _ = 2 * δx δ₀ T := by ring
  rw [abs_mul, abs_of_pos hκ] at h1
  have h2 : |((j - j' : ℤ) : ℝ)| < 2 * δx δ₀ T / T.κ := by rw [lt_div_iff₀ hκ]; linarith
  have h3 : 2 * δx δ₀ T / T.κ ≤ ((ny δ₀ T : ℤ) : ℝ) := by
    rw [ny_spec]; exact Int.le_ceil _
  have h4 : |((j - j' : ℤ) : ℝ)| < ((ny δ₀ T : ℤ) : ℝ) := lt_of_lt_of_le h2 h3
  rw [← Int.cast_abs] at h4
  exact_mod_cast h4

end FrameGram


section FrameGram2

theorem gram_fixed_a (η : ℝ → ℝ) {δ₀ : ℝ} {T : Torus} (hny : 0 < ny δ₀ T) (a : ℤ) (c c' : ZMod T.Nφ) :
    ∑ ℓ : Fin (ny δ₀ T),
      ((((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ j ∈ (Ia δ₀ T a).filter (fun j : ℤ => (j : ZMod T.Nφ) = c),
            ((wa η δ₀ T a j : ℝ) : ℂ) *
              Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (((ℓ : ℕ) : ℤ) : ℂ) / ((ny δ₀ T : ℕ) : ℂ)))) *
        star ((((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ j ∈ (Ia δ₀ T a).filter (fun j : ℤ => (j : ZMod T.Nφ) = c'),
            ((wa η δ₀ T a j : ℝ) : ℂ) *
              Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (((ℓ : ℕ) : ℤ) : ℂ) / ((ny δ₀ T : ℕ) : ℂ)))) =
    ∑ j ∈ (Ia δ₀ T a).filter (fun j : ℤ => (j : ZMod T.Nφ) = c ∧ (j : ZMod T.Nφ) = c'),
      ((wa η δ₀ T a j : ℝ) : ℂ) ^ 2 := by
  set n := ny δ₀ T with hn
  set C : ℂ := (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hC
  set F : ZMod T.Nφ → Finset ℤ := fun c => (Ia δ₀ T a).filter (fun j : ℤ => (j : ZMod T.Nφ) = c) with hF
  set w : ℤ → ℂ := fun j => ((wa η δ₀ T a j : ℝ) : ℂ) with hw
  set e : ℤ → Fin n → ℂ := fun j ℓ =>
    Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (((ℓ : ℕ) : ℤ) : ℂ) / ((n : ℕ) : ℂ))) with he
  have hn0 : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hny.ne'
  have hCC : C * star C = 1 / ((n : ℕ) : ℂ) := by
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hny
    rw [hC, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.rpow_add hpos]
    norm_num [Real.rpow_neg_one]
  have hww : ∀ j, star (w j) = w j := fun j => by rw [hw, Complex.star_def, Complex.conj_ofReal]
  have hee : ∀ (j j' : ℤ) (ℓ : Fin n), e j ℓ * star (e j' ℓ) =
      Complex.exp (-(2 * (π : ℂ) * I * (((j - j' : ℤ)) : ℂ) * (((ℓ : ℕ) : ℤ) : ℂ) / ((n : ℕ) : ℂ))) := by
    intro j j' ℓ
    rw [he, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_neg, map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast,
      map_natCast]
    push_cast
    ring
  -- expand the product of the two sums
  have expand : ∀ ℓ : Fin n, (C * ∑ j ∈ F c, w j * e j ℓ) * star (C * ∑ j ∈ F c', w j * e j ℓ) =
      ∑ j ∈ F c, ∑ j' ∈ F c', (C * star C * (w j * w j')) * (e j ℓ * star (e j' ℓ)) := by
    intro ℓ
    rw [star_mul', star_sum, mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [star_mul', hww]
    ring
  show ∑ ℓ : Fin n, (C * ∑ j ∈ F c, w j * e j ℓ) * star (C * ∑ j ∈ F c', w j * e j ℓ) = _
  simp_rw [expand]
  rw [Finset.sum_comm]
  have inner : ∀ j ∈ F c, ∑ ℓ : Fin n, ∑ j' ∈ F c', (C * star C * (w j * w j')) * (e j ℓ * star (e j' ℓ)) =
      if j ∈ F c' then w j ^ 2 else 0 := by
    intro j hj
    rw [Finset.sum_comm]
    have hk : ∀ j' ∈ F c', ∑ ℓ : Fin n, (C * star C * (w j * w j')) * (e j ℓ * star (e j' ℓ)) =
        if j = j' then w j ^ 2 else 0 := by
      intro j' hj'
      rw [← Finset.mul_sum]
      simp_rw [hee]
      have hjI : j ∈ Ia δ₀ T a := (Finset.mem_filter.mp hj).1
      have hj'I : j' ∈ Ia δ₀ T a := (Finset.mem_filter.mp hj').1
      rw [sum_exp_neg_two_pi n hny (j - j') (abs_sub_lt_ny hjI hj'I)]
      by_cases hjj : j = j'
      · subst hjj
        rw [ite_eq_left (sub_self j), ite_eq_left rfl, hCC]
        field_simp
      · rw [ite_eq_right (sub_ne_zero.mpr hjj), ite_eq_right hjj, mul_zero]
    rw [Finset.sum_congr rfl hk, Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl inner, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [hF, Finset.mem_filter]
  tauto

end FrameGram2


section FrameGram3

theorem window_partition {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (c : ZMod T.Nφ) :
    ∑ a : Fin (nx δ₀ T), ∑ j ∈ (Ia δ₀ T ((a : ℕ) : ℤ)).filter (fun j : ℤ => (j : ZMod T.Nφ) = c),
      (wa η δ₀ T ((a : ℕ) : ℤ) j) ^ 2 = 1 := by
  obtain ⟨hnx4, hδm, -, -⟩ := consistency_ii hδ₀ hT
  have hnx : (0 : ℤ) < (nx δ₀ T : ℤ) := by exact_mod_cast (show 0 < nx δ₀ T by omega)
  have hδx : 0 < δx δ₀ T := by unfold δminus at hδm; linarith
  have hκ := T.κ_pos
  have hNφ : (0 : ℤ) < (T.Nφ : ℤ) := by exact_mod_cast T.Nφ_pos
  set u : ℝ := T.κ * ((c.val : ℕ) : ℝ) / δx δ₀ T with hu
  have hN : (T.κ * (T.Nφ : ℝ)) / δx δ₀ T = (nx δ₀ T : ℝ) := by
    rw [← Torus.Lx_eq, Lx_eq_nx hδ₀ hT]; field_simp
  have hwa : ∀ (a m : ℤ), wa η δ₀ T a ((c.val : ℤ) + m * (T.Nφ : ℤ)) =
      window η (u - ((a - m * (nx δ₀ T : ℤ) : ℤ) : ℝ)) := by
    intro a m
    unfold wa
    congr 1
    rw [hu]
    push_cast
    rw [show T.κ * (((c.val : ℕ) : ℝ) + (m : ℝ) * (T.Nφ : ℝ)) / δx δ₀ T =
      T.κ * ((c.val : ℕ) : ℝ) / δx δ₀ T + (m : ℝ) * ((T.κ * (T.Nφ : ℝ)) / δx δ₀ T) by ring, hN]
    ring
  -- the target: the partition of unity, as a finite sum
  have hsupp : ∀ k : ℤ, window η (u - k) ≠ 0 → |u - k| < 1 := by
    intro k hk
    by_contra h
    exact hk (window_eq_zero hη (not_lt.mp h))
  set K : Finset ℤ := Finset.Icc (⌊u⌋ - 1) (⌈u⌉ + 1) with hK
  have hKmem : ∀ k : ℤ, |u - k| < 1 → k ∈ K := by
    intro k hk
    rw [hK, Finset.mem_Icc]
    rw [abs_lt] at hk
    constructor
    · have : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
      have h2 : ((⌊u⌋ - 1 : ℤ) : ℝ) < k := by push_cast; linarith
      exact_mod_cast h2.le
    · have : u ≤ (⌈u⌉ : ℝ) := Int.le_ceil u
      have h2 : (k : ℝ) < ((⌈u⌉ + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h2.le
  have htsum : ∑' k : ℤ, window η (u - k) ^ 2 = ∑ k ∈ K, window η (u - k) ^ 2 := by
    apply tsum_eq_sum
    intro k hk
    by_contra hne
    exact hk (hKmem k (hsupp k (fun h => hne (by rw [h]; ring))))
  rw [← window_sq_tsum hη u, htsum, Finset.sum_sigma']
  -- the bijection (a, j) ↦ a - m n_x, j = c + m N_φ
  have hdvd : ∀ j : ℤ, (j : ZMod T.Nφ) = c → (T.Nφ : ℤ) ∣ j - (c.val : ℤ) := by
    intro j hj
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hj, ZMod.natCast_zmod_val, sub_self]
  refine Finset.sum_bij_ne_zero (fun x _ _ => ((x.1 : ℕ) : ℤ) - ((x.2 - (c.val : ℤ)) / (T.Nφ : ℤ)) * (nx δ₀ T : ℤ))
    ?_ ?_ ?_ ?_
  · rintro ⟨a, j⟩ hx hne
    rw [Finset.mem_sigma, Finset.mem_filter] at hx
    obtain ⟨m, hm⟩ := hdvd j hx.2.2
    have hj : j = (c.val : ℤ) + ((j - (c.val : ℤ)) / (T.Nφ : ℤ)) * (T.Nφ : ℤ) := by
      have hq : (j - (c.val : ℤ)) / (T.Nφ : ℤ) = m := by rw [hm, Int.mul_ediv_cancel_left _ hNφ.ne']
      rw [hq]; linarith
    apply hKmem
    apply hsupp
    intro h0
    apply hne
    simp only []
    rw [hj, hwa, h0]
    ring
  · rintro ⟨a1, j1⟩ hx1 _ ⟨a2, j2⟩ hx2 _ heq
    rw [Finset.mem_sigma, Finset.mem_filter] at hx1 hx2
    simp only [] at heq
    obtain ⟨m1, hm1⟩ := hdvd j1 hx1.2.2
    obtain ⟨m2, hm2⟩ := hdvd j2 hx2.2.2
    rw [hm1, hm2, Int.mul_ediv_cancel_left _ hNφ.ne', Int.mul_ediv_cancel_left _ hNφ.ne'] at heq
    have ha1 : (0 : ℤ) ≤ ((a1 : ℕ) : ℤ) ∧ ((a1 : ℕ) : ℤ) < (nx δ₀ T : ℤ) := ⟨by positivity, by exact_mod_cast a1.2⟩
    have ha2 : (0 : ℤ) ≤ ((a2 : ℕ) : ℤ) ∧ ((a2 : ℕ) : ℤ) < (nx δ₀ T : ℤ) := ⟨by positivity, by exact_mod_cast a2.2⟩
    have hmod : ((a1 : ℕ) : ℤ) = ((a2 : ℕ) : ℤ) := by
      have e1 : ((a1 : ℕ) : ℤ) % (nx δ₀ T : ℤ) = ((a1 : ℕ) : ℤ) := Int.emod_eq_of_lt ha1.1 ha1.2
      have e2 : ((a2 : ℕ) : ℤ) % (nx δ₀ T : ℤ) = ((a2 : ℕ) : ℤ) := Int.emod_eq_of_lt ha2.1 ha2.2
      rw [← e1, ← e2]
      have : ((a1 : ℕ) : ℤ) = ((a2 : ℕ) : ℤ) + (m1 - m2) * (nx δ₀ T : ℤ) := by linarith
      rw [this, Int.add_mul_emod_self_right]
    have ha : a1 = a2 := Fin.ext (by exact_mod_cast hmod)
    subst ha
    have hm : m1 = m2 := by
      have : (m1 - m2) * (nx δ₀ T : ℤ) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hnx.ne'
    subst hm
    have hj : j1 = j2 := by linarith
    subst hj
    rfl
  · intro k hk hne
    have hk1 : |u - k| < 1 := hsupp k (fun h => hne (by rw [h]; ring))
    set q := k / (nx δ₀ T : ℤ) with hq
    set r := k % (nx δ₀ T : ℤ) with hr
    have hr0 : 0 ≤ r := Int.emod_nonneg _ hnx.ne'
    have hrn : r < (nx δ₀ T : ℤ) := Int.emod_lt_of_pos _ hnx
    have hkr : k = r + (nx δ₀ T : ℤ) * q := by
      have := Int.emod_def k (nx δ₀ T : ℤ); rw [hq, hr]; linarith
    let a : Fin (nx δ₀ T) := ⟨r.toNat, by omega⟩
    have ha : ((a : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
    let j : ℤ := (c.val : ℤ) + (-q) * (T.Nφ : ℤ)
    have hjw : wa η δ₀ T ((a : ℕ) : ℤ) j = window η (u - k) := by
      rw [hwa, ha]; congr 2; rw [hkr]; push_cast; ring
    refine ⟨⟨a, j⟩, ?_, ?_, ?_⟩
    · rw [Finset.mem_sigma, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [mem_Ia]
        have hw0 : window η (T.κ * (j : ℝ) / δx δ₀ T - ((a : ℕ) : ℤ)) ≠ 0 := by
          have := hjw; unfold wa at this; rw [this]; exact fun h => hne (by rw [h]; ring)
        have hlt : |T.κ * (j : ℝ) / δx δ₀ T - (((a : ℕ) : ℤ) : ℝ)| < 1 := by
          by_contra h; exact hw0 (window_eq_zero hη (not_lt.mp h))
        have e : T.κ * (j : ℝ) - xa δ₀ T ((a : ℕ) : ℤ) =
            (T.κ * (j : ℝ) / δx δ₀ T - (((a : ℕ) : ℤ) : ℝ)) * δx δ₀ T := by
          unfold xa; field_simp
        rw [e, abs_mul, abs_of_pos hδx]
        nlinarith [abs_nonneg (T.κ * (j : ℝ) / δx δ₀ T - (((a : ℕ) : ℤ) : ℝ))]
      · show (((c.val : ℤ) + (-q) * (T.Nφ : ℤ) : ℤ) : ZMod T.Nφ) = c
        push_cast
        rw [ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val]
    · simp only []
      rw [hjw]
      exact hne
    · simp only []
      have : (j - (c.val : ℤ)) / (T.Nφ : ℤ) = -q := by
        rw [show j - (c.val : ℤ) = (T.Nφ : ℤ) * (-q) by ring, Int.mul_ediv_cancel_left _ hNφ.ne']
      rw [this, ha, hkr]
      ring
  · rintro ⟨a, j⟩ hx _
    rw [Finset.mem_sigma, Finset.mem_filter] at hx
    obtain ⟨m, hm⟩ := hdvd j hx.2.2
    have hj : j = (c.val : ℤ) + ((j - (c.val : ℤ)) / (T.Nφ : ℤ)) * (T.Nφ : ℤ) := by
      have hq : (j - (c.val : ℤ)) / (T.Nφ : ℤ) = m := by rw [hm, Int.mul_ediv_cancel_left _ hNφ.ne']
      rw [hq]; linarith
    simp only []
    conv_lhs => rw [hj]
    rw [hwa]

theorem frame_gram {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (c c' : ZMod T.Nφ) :
    ∑ s : Slot δ₀ T, frameVec η δ₀ T s c * star (frameVec η δ₀ T s c') = if c = c' then 1 else 0 := by
  have hny : 0 < ny δ₀ T := by have := two_le_ny hδ₀ hT; omega
  rw [Fintype.sum_prod_type]
  simp only [frameVec_apply]
  simp_rw [gram_fixed_a η hny]
  by_cases hcc : c = c'
  · subst hcc
    rw [ite_eq_left rfl]
    have := window_partition hη hδ₀ hT c
    have e : ∀ a : Fin (nx δ₀ T), ∑ j ∈ (Ia δ₀ T ((a : ℕ) : ℤ)).filter (fun j : ℤ => (j : ZMod T.Nφ) = c ∧ (j : ZMod T.Nφ) = c),
        ((wa η δ₀ T ((a : ℕ) : ℤ) j : ℝ) : ℂ) ^ 2 =
        ((∑ j ∈ (Ia δ₀ T ((a : ℕ) : ℤ)).filter (fun j : ℤ => (j : ZMod T.Nφ) = c), (wa η δ₀ T ((a : ℕ) : ℤ) j) ^ 2 : ℝ) : ℂ) := by
      intro a
      push_cast
      congr 1
      ext j
      simp
    simp_rw [e]
    rw [← Complex.ofReal_sum, this, Complex.ofReal_one]
  · rw [ite_eq_right hcc]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_eq_zero]
    intro j hj
    rw [Finset.mem_filter] at hj
    exact absurd (hj.2.1.symm.trans hj.2.2) hcc

end FrameGram3


section FrameGram4

theorem spin_frame_gram {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (c c' : Mode (ZMod T.Nφ)) :
    ∑ μ : Mode (Slot δ₀ T), spinTensor (frameVec η δ₀ T μ.1) μ.2 c *
      star (spinTensor (frameVec η δ₀ T μ.1) μ.2 c') = if c = c' then 1 else 0 := by
  rcases c with ⟨j, τ⟩
  rcases c' with ⟨j', τ'⟩
  rw [Fintype.sum_prod_type]
  simp only [spinTensor, WithLp.ofLp_toLp]
  have hs : ∀ (F : Spin → ℂ), ∑ ρ : Spin, F ρ = F .up + F .dn := fun F => by
    rw [show (Finset.univ : Finset Spin) = {Spin.up, Spin.dn} from rfl, Finset.sum_pair (by decide)]
  simp_rw [hs]
  have hg := frame_gram hη hδ₀ hT j j'
  simp only [Complex.star_def] at hg
  cases τ <;> cases τ' <;> simp [Prod.ext_iff] <;> simpa using hg

end FrameGram4


/-- The analysis map is the paper's: `(𝒮f)_s = ⟨z_s, f⟩`. -/
theorem analysis_apply (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (f : Space T) (s : Slot δ₀ T) :
    analysis η δ₀ T f s = ⟪frameVec η δ₀ T s, f⟫_ℂ := by
  rfl

/-- `analysis2` is `𝒮 ⊗ 1_{ℂ²}`: on `f ⊗ σ` it is `(𝒮f) ⊗ σ`. -/
theorem analysis2_spinTensor (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (f : Space T) (σ : Spin) :
    analysis2 η δ₀ T (spinTensor f σ) = spinTensor (analysis η δ₀ T f) σ := by
  refine PiLp.ext fun μ => ?_
  rcases μ with ⟨s, τ⟩
  show ⟪spinTensor (frameVec η δ₀ T s) τ, spinTensor f σ⟫_ℂ = (spinTensor (analysis η δ₀ T f) σ) (s, τ)
  rw [inner_spinTensor]
  simp only [spinTensor, WithLp.ofLp_toLp, analysis_apply]

/-- The vector `z_s` represents `SlotFrame`'s function `z_s(R)` (`SlotFrame.frame`, the object of
Lemma 3.5(i)–(ii)). -/
theorem toFun_frameVec (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (s : Slot δ₀ T) :
    toFun T (frameVec η δ₀ T s) = frame η δ₀ T s := by
  funext R
  simp only [toFun, frameVec, frame, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, orb,
    PiLp.single_apply, mul_ite, mul_one, mul_zero]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_ite, ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  ring

/-- The bridge of the proof of **Lemma 3.5(iii)**: "`$(\Sa\ev R)_s=\ip{z_s}{\ev R}=\overline{\ip{\ev R}{z_s}}=\overline{z_s(R)}$`". -/
theorem analysis_ev (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (R : ℝ × ℝ) (s : Slot δ₀ T) :
    analysis η δ₀ T (ev T R) s = star (frame η δ₀ T s R) := by
  rw [analysis_apply, ← inner_conj_symm, inner_ev, toFun_frameVec, Complex.star_def]

/-- The bridge of the proof of **Lemma 3.5(iii)**: "`likewise $(\Sa\evD R)_s=\overline{(Dz_s)(R)}$`". -/
theorem analysis_evD (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (R : ℝ × ℝ) (s : Slot δ₀ T) :
    analysis η δ₀ T (evD T R) s = star (Dcov (frame η δ₀ T s) R) := by
  rw [analysis_apply, ← inner_conj_symm, inner_evD, toFun_frameVec, Complex.star_def]

/-- `1_X` acts as multiplication by the indicator of `X`. -/
theorem slotProj_apply (δ₀ : ℝ) (T : Torus) (X : Finset (Slot δ₀ T)) (g : SlotSpace δ₀ T)
    (s : Slot δ₀ T) : slotProj δ₀ T X g s = if s ∈ X then g s else 0 := by
  show (Matrix.toEuclideanCLM (n := Slot δ₀ T) (𝕜 := ℂ) _ g).ofLp s = _
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]
  split_ifs <;> simp

/-- `1_X` is an orthogonal projection (self-adjoint and idempotent); with `slotProj_apply`, the one onto the
functions supported in `X`. -/
theorem slotProj_isStarProjection (δ₀ : ℝ) (T : Torus) (X : Finset (Slot δ₀ T)) :
    IsStarProjection (slotProj δ₀ T X) := by
  refine ⟨?_, ?_⟩
  · show slotProj δ₀ T X * slotProj δ₀ T X = slotProj δ₀ T X
    rw [slotProj, ← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2
    funext s
    split_ifs with h <;> simp [h]
  · show star (slotProj δ₀ T X) = slotProj δ₀ T X
    rw [slotProj, ← map_star, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 2
    funext s
    split_ifs with h <;> simp [h]

/-! ## Proposition 3.3 (Parseval) -/

/-- **Proposition 3.3**: "`For every admissible torus, $\sum_{s\in\Slots}\lvert z_s\rangle\langle z_s\rvert=\one_{\hN}$.`" -/
theorem sum_rankOne_frameVec {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) :
    ∑ s : Slot δ₀ T, InnerProductSpace.rankOne ℂ (frameVec η δ₀ T s) (frameVec η δ₀ T s) =
      (1 : Space T →L[ℂ] Space T) := by
  exact sum_rankOne_eq_one_of _ (frame_gram hη hδ₀ hT)

/-- **Proposition 3.3**: "`Equivalently $\Sa^*\Sa=\one$: the analysis map is an isometry, and $\Sa\Sa^*$ is the
orthogonal projection of $\ell^2(\Slots)$ onto $\ran\Sa$, of rank $\Nphi$.`" — `𝒮*𝒮 = 1`. -/
theorem adjoint_analysis_comp_analysis {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {T : Torus} (hT : T.Admissible δ₀) :
    LinearMap.adjoint (analysis η δ₀ T) ∘ₗ analysis η δ₀ T = LinearMap.id := by
  exact anaMap_isometry_of _ (sum_rankOne_frameVec hη hδ₀ hT)

/-- **Proposition 3.3**: "`the analysis map is an isometry`". -/
theorem norm_analysis {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (f : Space T) : ‖analysis η δ₀ T f‖ = ‖f‖ := by
  exact norm_anaMap_of _ (adjoint_analysis_comp_analysis hη hδ₀ hT) f

/-- **Proposition 3.3**: "`$\Sa\Sa^*$ is the orthogonal projection of $\ell^2(\Slots)$ onto $\ran\Sa$`". -/
theorem analysis_comp_adjoint {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) :
    analysis η δ₀ T ∘ₗ LinearMap.adjoint (analysis η δ₀ T) =
      ((LinearMap.range (analysis η δ₀ T)).starProjection : SlotSpace δ₀ T →ₗ[ℂ] SlotSpace δ₀ T) := by
  exact anaMap_comp_adjoint_of _ (adjoint_analysis_comp_analysis hη hδ₀ hT)

/-- **Proposition 3.3**: `ran 𝒮` has dimension `N_φ` (the projection `𝒮𝒮*` has rank `N_φ`: "`of rank $\Nphi$`"). -/
theorem finrank_range_analysis {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) : Module.finrank ℂ (LinearMap.range (analysis η δ₀ T)) = T.Nφ := by
  rw [show analysis η δ₀ T = anaMap (frameVec η δ₀ T) from rfl,
    finrank_range_anaMap_of _ (adjoint_analysis_comp_analysis hη hδ₀ hT), ZMod.card]

/-- **Proposition 3.3**: "`The same holds for $\Sa\otimes\one_{\C^2}$.`" — `(𝒮 ⊗ 1)*(𝒮 ⊗ 1) = 1`. -/
theorem adjoint_analysis2_comp_analysis2 {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {T : Torus} (hT : T.Admissible δ₀) :
    LinearMap.adjoint (analysis2 η δ₀ T) ∘ₗ analysis2 η δ₀ T = LinearMap.id := by
  exact anaMap_isometry_of _ (sum_rankOne_eq_one_of _ (spin_frame_gram hη hδ₀ hT))

/-- **Proposition 3.3** for `𝒮 ⊗ 1` ("`The same holds for $\Sa\otimes\one_{\C^2}$.`"): an isometry. -/
theorem norm_analysis2 {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (f : Space2 T) : ‖analysis2 η δ₀ T f‖ = ‖f‖ := by
  exact norm_anaMap_of _ (adjoint_analysis2_comp_analysis2 hη hδ₀ hT) f

/-- **Proposition 3.3** for `𝒮 ⊗ 1` ("`The same holds for $\Sa\otimes\one_{\C^2}$.`"): `(𝒮 ⊗ 1)(𝒮 ⊗ 1)*` is the
orthogonal projection onto its range. -/
theorem analysis2_comp_adjoint {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) :
    analysis2 η δ₀ T ∘ₗ LinearMap.adjoint (analysis2 η δ₀ T) =
      ((LinearMap.range (analysis2 η δ₀ T)).starProjection :
        EuclideanSpace ℂ (Mode (Slot δ₀ T)) →ₗ[ℂ] EuclideanSpace ℂ (Mode (Slot δ₀ T))) := by
  exact anaMap_comp_adjoint_of _ (adjoint_analysis2_comp_analysis2 hη hδ₀ hT)

/-- **Proposition 3.3** for `𝒮 ⊗ 1` ("`The same holds for $\Sa\otimes\one_{\C^2}$.`"): its range has dimension
`dim 𝔨_N = 2N_φ`. -/
theorem finrank_range_analysis2 {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) : Module.finrank ℂ (LinearMap.range (analysis2 η δ₀ T)) = 2 * T.Nφ := by
  rw [show analysis2 η δ₀ T = anaMap (fun μ : Mode (Slot δ₀ T) => spinTensor (frameVec η δ₀ T μ.1) μ.2) from rfl,
    finrank_range_anaMap_of _ (adjoint_analysis2_comp_analysis2 hη hδ₀ hT), Fintype.card_prod, ZMod.card]
  have : Fintype.card Spin = 2 := rfl
  rw [this, mul_comm]

/-! ## Lemma 3.5(iii) in the paper's form -/

/-- **Lemma 3.5(iii)** as the paper states it, with the analysis map and the evaluation vectors:
"`$\norm{\one_{\Slots\setminus\Ball rR}\,\Sa\ev R}\le C_k(1+r)^{-k}$ and
$\norm{\one_{\Slots\setminus\Ball rR}\,\Sa\evD R}\le C_k(1+r)^{-k}$ for every $r\ge0$`", with `C_k` depending only on
`k`, `η` and `δ₀` (`SlotFrame.localization_iii` is the reduced form; `𝒮 ∖ B(r,R)` is `SlotFrame.ballCompl`). -/
theorem localization_iii_analysis {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {k : ℝ} (hk : 0 ≤ k) :
    ∃ C : ℝ, ∀ T : Torus, T.Admissible δ₀ → ∀ (R : ℝ × ℝ) (r : ℝ), 0 ≤ r →
      ‖slotProj δ₀ T (ballCompl δ₀ T R r) (analysis η δ₀ T (ev T R))‖ ≤ C * (1 + r) ^ (-k) ∧
      ‖slotProj δ₀ T (ballCompl δ₀ T R r) (analysis η δ₀ T (evD T R))‖ ≤ C * (1 + r) ^ (-k) := by
  obtain ⟨C, hC⟩ := localization_iii hη hδ₀ hk
  refine ⟨C, fun T hT R r hr => ?_⟩
  have key : ∀ (v : SlotSpace δ₀ T) (F : Slot δ₀ T → ℂ), (∀ s, v s = star (F s)) →
      ‖slotProj δ₀ T (ballCompl δ₀ T R r) v‖ = Real.sqrt (∑ s ∈ ballCompl δ₀ T R r, ‖F s‖ ^ 2) := by
    intro v F hv
    rw [EuclideanSpace.norm_eq]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => s ∈ ballCompl δ₀ T R r)]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have h0 : ∑ s ∈ Finset.univ.filter (fun s => s ∉ ballCompl δ₀ T R r),
        ‖slotProj δ₀ T (ballCompl δ₀ T R r) v s‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [Finset.mem_filter] at hs
      rw [slotProj_apply, ite_eq_right hs.2]
      simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [slotProj_apply, ite_eq_left hs, hv, norm_star]
  rw [key _ (fun s => frame η δ₀ T s R) (analysis_ev η δ₀ T R),
    key _ (fun s => Dcov (frame η δ₀ T s) R) (analysis_evD η δ₀ T R)]
  exact hC T hT R r hr

end HRTorus.LLL
