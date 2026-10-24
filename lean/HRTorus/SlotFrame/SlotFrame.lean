import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Round
import HRTorus.SlotFrame.Analysis
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The slot frame of the HR paper and its uniform localization (Lemma 3.5)

Written by Claude Opus 5.5 (an AI model), 2026-10-23. The paper: the HR paper,
`papers/hr/sections/02-setting.tex` (Definition 2.1 `def:torus`, Lemma 2.2 `lem:orbitals`) and
`papers/hr/sections/03-slot-frame.tex` (Definition 3.1 `def:frame`, Lemma 3.2
`lem:frame-consistency`, Lemma 3.5 `lem:localization`), with the conventions `|u|_P` and `(u)_+`
of `sections/01-introduction.tex` (paragraph "Conventions").

**Every theorem in this file is proved; there is no `sorry`.** The definitions and the
statements were written first and reviewed against the paper (phase (a)) and are unchanged;
phase (b) added the proofs, the helper lemmas marked as proof
devices, and the statement `Dcov_psi` (Lemma 2.2(iii) termwise). The
one-dimensional analysis is in `HRTorus.SlotFrame.Analysis`.

## Modelling choices

* Points of `ℝ²` are `ℝ × ℝ`, `R = (R.1, R.2) = (R_x, R_y)`. Mathlib's `dist` on `ℝ × ℝ` is the
  sup metric and is never used; the flat distance is `flatDist`.
* The profile `η` is any function with the three properties of Definition 3.1 (`IsProfile`); the
  theorems quantify over it before `∃ C`, so `C` depends on `η`. The paper's definiteness choice
  `e^{−1/(1−u²)}` is `etaStd`, built from Mathlib's `expNegInvGlue`.
* The slot lattice `ℤ_{n_x} × ℤ_{n_y}` is `Fin n_x × Fin n_y`, i.e. the representatives
  `{0,…,n_x−1} × {0,…,n_y−1}` (the paper's definition of `z_s` uses exactly these representatives
  for `a`); no group operation on slots enters Lemma 3.5. The orbital labels `ℤ_{N_φ}` are
  `ZMod N_φ`, where the class map `[j]` of `ℤ → ℤ_{N_φ}` is used.
* Part (iii) is stated after Lemma 2.3(i)'s identity `(𝒜 e_R)_s = \overline{z_s(R)}`, i.e. as the
  ℓ²-norm of `s ↦ z_s(R)` over the slots outside the ball; the Hilbert space `𝔥_N`, the evaluation
  vectors and the analysis map are not modelled.
-/

open Real Complex
open scoped ContDiff

noncomputable section

namespace HRTorus.SlotFrame

/-! ## §2: the torus and the Landau-gauge orbitals -/

/-- **Definition 2.1** (the data): `N ∈ ℕ`, `L_x, L_y > 0` with `L_x L_y = 2π N_φ = 4πN`, where
`N_φ := 2N` (`Torus.Nφ`). -/
structure Torus where
  /-- the electron-number parameter `N ∈ ℕ` -/
  N : ℕ
  /-- the side `L_x` (the transverse direction `x`) -/
  Lx : ℝ
  /-- the side `L_y` -/
  Ly : ℝ
  Lx_pos : 0 < Lx
  Ly_pos : 0 < Ly
  /-- `L_x L_y = 2π N_φ` with `N_φ = 2N` -/
  area : Lx * Ly = 2 * π * ((2 * N : ℕ) : ℝ)

/-- `N_φ := 2N`, the number of flux quanta and of orbitals. -/
def Torus.Nφ (T : Torus) : ℕ := 2 * T.N

/-- `κ := 2π / L_y`. -/
def Torus.κ (T : Torus) : ℝ := 2 * π / T.Ly

/-- **Lemma 2.2**, the planar orbital
`φ_n(x,y) := (L_y √π)^{−1/2} e^{iκny} e^{−(x−κn)²/2}` for `n ∈ ℤ`. -/
def phi (T : Torus) (n : ℤ) (r : ℝ × ℝ) : ℂ :=
  (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (r.2 : ℂ)) *
    ((Real.exp (-((r.1 - T.κ * n) ^ 2) / 2) : ℝ) : ℂ)

/-- **Lemma 2.2**, the torus orbital `ψ_j := Σ_{m∈ℤ} φ_{j̃ + m N_φ}` for `j ∈ ℤ_{N_φ}`, with the
representative `j̃ := j.val ∈ {0, …, N_φ − 1}` (the paper allows any representative; that the value
does not depend on it is `psi_intCast`). The value at `r` is the sum of the series (`tsum`). -/
def psi (T : Torus) (j : ZMod T.Nφ) (r : ℝ × ℝ) : ℂ :=
  ∑' m : ℤ, phi T ((j.val : ℤ) + m * (T.Nφ : ℤ)) r

/-- The covariant derivative of (2.1): `D := ½(D_x − i D_y)` with `D_x := ∂_x`,
`D_y := ∂_y − i x`, on functions `ℝ² → ℂ`, the partial derivatives being Mathlib's `deriv` of the
coordinate restrictions. -/
def Dcov (f : ℝ × ℝ → ℂ) (r : ℝ × ℝ) : ℂ :=
  (1 / 2 : ℂ) * (deriv (fun x : ℝ => f (x, r.2)) r.1 -
    I * (deriv (fun y : ℝ => f (r.1, y)) r.2 - I * (r.1 : ℂ) * f r))

/-! ## Conventions of §1 -/

/-- `|u|_P`: the distance from `u` to `Pℤ` (Mathlib's `Metric.infDist` to the set of integer
multiples of `P`). -/
def pdist (P u : ℝ) : ℝ := Metric.infDist u (AddSubgroup.zmultiples P : Set ℝ)

/-- The flat distance on `𝕋_N = ℝ²/(L_xℤ × L_yℤ)` between the images of `r` and `r'`, in the form
the proof of Lemma 3.5(iii) uses: `d = (|Δx|²_{L_x} + |Δy|²_{L_y})^{1/2}`. -/
def flatDist (T : Torus) (r r' : ℝ × ℝ) : ℝ :=
  Real.sqrt (pdist T.Lx (r.1 - r'.1) ^ 2 + pdist T.Ly (r.2 - r'.2) ^ 2)

/-! ## §3.1: the profile, the window, admissible tori and the slot frame (Definition 3.1) -/

/-- A **profile**: `η ∈ C^∞(ℝ)` with `η > 0` on `(−1, 1)` and `η = 0` on `ℝ ∖ (−1, 1)`. -/
def IsProfile (η : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ η ∧ (∀ u : ℝ, |u| < 1 → 0 < η u) ∧ (∀ u : ℝ, 1 ≤ |u| → η u = 0)

/-- The paper's definiteness choice `η(u) = e^{−1/(1−u²)}` for `|u| < 1` (and `0` otherwise):
Mathlib's `expNegInvGlue x = e^{−1/x}` for `x > 0`, `0` for `x ≤ 0`, at `x = 1 − u²`. -/
def etaStd (u : ℝ) : ℝ := expNegInvGlue (1 - u ^ 2)

/-- The **window** `w(u) := η(u) (Σ_{k∈ℤ} η(u − k)²)^{−1/2}`. -/
def window (η : ℝ → ℝ) (u : ℝ) : ℝ :=
  η u * (∑' k : ℤ, η (u - k) ^ 2) ^ (-(1 / 2 : ℝ))

/-- `L₀ := max{4, 3π/δ₀}`. -/
def L0 (δ₀ : ℝ) : ℝ := max 4 (3 * π / δ₀)

/-- `δ₋ := (2/3) δ₀`. -/
def δminus (δ₀ : ℝ) : ℝ := 2 / 3 * δ₀

/-- `δ₊ := 2 δ₀`. -/
def δplus (δ₀ : ℝ) : ℝ := 2 * δ₀

/-- A torus is **admissible** (for the target slot width `δ₀`) if `L_y ≥ L₀` and
`L_x ≥ 4δ₀ + 4`. -/
def Torus.Admissible (δ₀ : ℝ) (T : Torus) : Prop :=
  L0 δ₀ ≤ T.Ly ∧ 4 * δ₀ + 4 ≤ T.Lx

/-- `n_x :=` the integer nearest to `L_x/δ₀` (Mathlib's `round`, as a natural number; it is
`round (L_x/δ₀)` itself whenever `δ₀ > 0`, `nx_spec`). -/
def nx (δ₀ : ℝ) (T : Torus) : ℕ := (round (T.Lx / δ₀)).toNat

/-- `δ_x := L_x / n_x`. -/
def δx (δ₀ : ℝ) (T : Torus) : ℝ := T.Lx / (nx δ₀ T : ℝ)

/-- `x_a := a δ_x` for `a ∈ ℤ`. -/
def xa (δ₀ : ℝ) (T : Torus) (a : ℤ) : ℝ := (a : ℝ) * δx δ₀ T

/-- `n_y := ⌈2δ_x/κ⌉` (as a natural number; it is the paper's integer, `ny_spec`). -/
def ny (δ₀ : ℝ) (T : Torus) : ℕ := (⌈2 * δx δ₀ T / T.κ⌉).toNat

/-- `δ_y := L_y / n_y`. -/
def δy (δ₀ : ℝ) (T : Torus) : ℝ := T.Ly / (ny δ₀ T : ℝ)

/-- `y_ℓ := ℓ δ_y` for `ℓ ∈ ℤ`. -/
def yl (δ₀ : ℝ) (T : Torus) (ℓ : ℤ) : ℝ := (ℓ : ℝ) * δy δ₀ T

/-- The **slot lattice** `𝒮 := ℤ_{n_x} × ℤ_{n_y}`, as the representatives
`{0,…,n_x−1} × {0,…,n_y−1}`; a slot is `s = (a, ℓ)`. -/
abbrev Slot (δ₀ : ℝ) (T : Torus) : Type := Fin (nx δ₀ T) × Fin (ny δ₀ T)

/-- The centre `r_s := (x_a, y_ℓ)` of the slot `s = (a, ℓ)` (a point of `ℝ²` representing the
point of `𝕋_N`). -/
def centre (δ₀ : ℝ) (T : Torus) (s : Slot δ₀ T) : ℝ × ℝ :=
  (xa δ₀ T ((s.1 : ℕ) : ℤ), yl δ₀ T ((s.2 : ℕ) : ℤ))

/-- `w_a(j) := w(κj/δ_x − a)` for `a, j ∈ ℤ`. -/
def wa (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (a j : ℤ) : ℝ :=
  window η (T.κ * (j : ℝ) / δx δ₀ T - (a : ℝ))

/-- `I_a := {j ∈ ℤ : |κj − x_a| < δ_x}`, as a finset: the integers of the box
`[⌊(x_a − δ_x)/κ⌋, ⌈(x_a + δ_x)/κ⌉]` satisfying the paper's condition (the box contains every such
integer, `mem_Ia`). -/
def Ia (δ₀ : ℝ) (T : Torus) (a : ℤ) : Finset ℤ :=
  (Finset.Icc ⌊(xa δ₀ T a - δx δ₀ T) / T.κ⌋ ⌈(xa δ₀ T a + δx δ₀ T) / T.κ⌉).filter
    (fun j : ℤ => |T.κ * (j : ℝ) - xa δ₀ T a| < δx δ₀ T)

/-- The **slot frame** (3.1): for `s = (a, ℓ)`,
`z_s := n_y^{−1/2} Σ_{j ∈ I_a} w_a(j) e^{−2πijℓ/n_y} ψ_{[j]}`, as a function `ℝ² → ℂ`, with
`a ∈ {0,…,n_x−1}` and `ℓ ∈ {0,…,n_y−1}` the representatives and `[j]` the class of `j` in
`ℤ_{N_φ}`. -/
def frame (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (s : Slot δ₀ T) (R : ℝ × ℝ) : ℂ :=
  (((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ∑ j ∈ Ia δ₀ T ((s.1 : ℕ) : ℤ),
      ((wa η δ₀ T ((s.1 : ℕ) : ℤ) j : ℝ) : ℂ) *
        Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (((s.2 : ℕ) : ℤ) : ℂ) / ((ny δ₀ T : ℕ) : ℂ))) *
        psi T (j : ZMod T.Nφ) R

/-- The slots outside the ball, `𝒮 ∖ B(r,R) = {s ∈ 𝒮 : d(s,R) > r}`, where
`d(s,R) := d(r_s, R)` is the flat distance. -/
def ballCompl (δ₀ : ℝ) (T : Torus) (R : ℝ × ℝ) (r : ℝ) : Finset (Slot δ₀ T) :=
  Finset.univ.filter (fun s : Slot δ₀ T => r < flatDist T (centre δ₀ T s) R)

/-! ## Helpers (phase (b); proof devices, not statements of the paper) -/

theorem Torus.κ_pos (T : Torus) : 0 < T.κ := by
  unfold Torus.κ; exact div_pos (by positivity) T.Ly_pos

theorem Torus.κ_mul_Ly (T : Torus) : T.κ * T.Ly = 2 * π := by
  unfold Torus.κ; field_simp [T.Ly_pos.ne']

theorem Torus.N_pos (T : Torus) : 0 < T.N := by
  have h1 : 0 < T.Lx * T.Ly := mul_pos T.Lx_pos T.Ly_pos
  rw [T.area] at h1
  rcases Nat.eq_zero_or_pos (2 * T.N) with h0 | h0
  · rw [h0] at h1; simp at h1
  · omega

theorem Torus.Nφ_pos (T : Torus) : 0 < T.Nφ := by
  unfold Torus.Nφ; have := T.N_pos; omega

theorem norm_phi (T : Torus) (n : ℤ) (r : ℝ × ℝ) :
    ‖phi T n r‖ = (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-((r.1 - T.κ * n) ^ 2) / 2) := by
  unfold phi
  have h : ‖Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (r.2 : ℂ))‖ = 1 := by
    rw [show I * (T.κ : ℂ) * (n : ℂ) * (r.2 : ℂ) = ((T.κ * n * r.2 : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, norm_mul, h, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (mul_nonneg T.Ly_pos.le (Real.sqrt_nonneg _)) _),
    abs_of_pos (Real.exp_pos _)]

/-! ## Statements of §2 used by the frame -/

/-- Definition 2.1: "so that `L_x = κ N_φ`". -/
theorem Torus.Lx_eq (T : Torus) : T.Lx = T.κ * (T.Nφ : ℝ) := by
  have h := T.area
  have hLy : T.Ly ≠ 0 := T.Ly_pos.ne'
  unfold Torus.κ Torus.Nφ
  push_cast at h ⊢
  field_simp
  linear_combination h

/-- Lemma 2.2(i), the convergence of (2.3) at every point, for every representative `n`. -/
theorem psi_summable (T : Torus) (n : ℤ) (r : ℝ × ℝ) :
    Summable (fun m : ℤ => phi T (n + m * (T.Nφ : ℤ)) r) := by
  refine Summable.of_norm_bounded ((Analysis.summable_gauss_int T.Lx_pos (r.1 - T.κ * n)).mul_left
    ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)))) (fun m => ?_)
  have e : r.1 - T.κ * (((n + m * (T.Nφ : ℤ) : ℤ)) : ℝ) = r.1 - T.κ * n - m * T.Lx := by
    rw [Torus.Lx_eq]; push_cast; ring
  rw [norm_phi, e]

/-- Lemma 2.2(i), "`ψ_j` does not depend on the choice of `j̃`": `ψ_{[j]}` is the series with the
representative `j`. -/
theorem psi_intCast (T : Torus) (j : ℤ) (r : ℝ × ℝ) :
    psi T (j : ZMod T.Nφ) r = ∑' m : ℤ, phi T (j + m * (T.Nφ : ℤ)) r := by
  have : NeZero T.Nφ := ⟨T.Nφ_pos.ne'⟩
  unfold psi
  rw [ZMod.val_intCast]
  have e : ∀ m : ℤ, j % (T.Nφ : ℤ) + m * (T.Nφ : ℤ) = j + (m - j / (T.Nφ : ℤ)) * (T.Nφ : ℤ) := by
    intro m; rw [Int.emod_def]; ring
  simp_rw [e]
  exact (Equiv.subRight (j / (T.Nφ : ℤ))).tsum_eq (fun m => phi T (j + m * (T.Nφ : ℤ)) r)

/-! ## Statements of §3.1 used by Lemma 3.5 -/

/-- The definiteness choice is a profile. -/
theorem isProfile_etaStd : IsProfile etaStd := by
  refine ⟨?_, fun u hu => ?_, fun u hu => ?_⟩
  · unfold etaStd
    exact (expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_const.sub (contDiff_id.pow 2))
  · unfold etaStd
    apply expNegInvGlue.pos_of_pos
    have := (sq_lt_one_iff_abs_lt_one u).mpr hu
    linarith
  · unfold etaStd
    apply expNegInvGlue.zero_of_nonpos
    have := (one_le_sq_iff_one_le_abs u).mpr hu
    linarith

/-- **Lemma 3.2(i)**, first clause: `w` is smooth. -/
theorem window_contDiff {η : ℝ → ℝ} (hη : IsProfile η) : ContDiff ℝ ∞ (window η) :=
  Analysis.win_contDiff hη.2.2 hη.1 hη.2.1

/-- **Lemma 3.2(i)**, second clause: `w = 0` on `ℝ ∖ (−1, 1)`. -/
theorem window_eq_zero {η : ℝ → ℝ} (hη : IsProfile η) {u : ℝ} (hu : 1 ≤ |u|) :
    window η u = 0 :=
  Analysis.win_eq_zero hη.2.2 hu

/-- **Lemma 3.2(i)**, the partition of unity: `Σ_{k∈ℤ} w(u − k)² = 1` for every `u ∈ ℝ`. -/
theorem window_sq_tsum {η : ℝ → ℝ} (hη : IsProfile η) (u : ℝ) :
    ∑' k : ℤ, window η (u - k) ^ 2 = 1 :=
  Analysis.win_sq_tsum hη.2.2 hη.2.1 u

/-- The natural number `n_x` is the paper's integer `round (L_x/δ₀)`. -/
theorem nx_spec {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (T : Torus) :
    ((nx δ₀ T : ℕ) : ℤ) = round (T.Lx / δ₀) := by
  unfold nx
  apply Int.toNat_of_nonneg
  rw [round_eq]
  apply Int.floor_nonneg.mpr
  have : 0 < T.Lx / δ₀ := div_pos T.Lx_pos hδ₀
  linarith

/-- The natural number `n_y` is the paper's integer `⌈2δ_x/κ⌉`. -/
theorem ny_spec (δ₀ : ℝ) (T : Torus) :
    ((ny δ₀ T : ℕ) : ℤ) = ⌈2 * δx δ₀ T / T.κ⌉ := by
  unfold ny
  apply Int.toNat_of_nonneg
  apply Int.ceil_nonneg
  apply div_nonneg _ T.κ_pos.le
  apply mul_nonneg (by norm_num)
  unfold δx
  exact div_nonneg T.Lx_pos.le (Nat.cast_nonneg _)

/-- The finset `Ia` is the paper's set `I_a = {j ∈ ℤ : |κj − x_a| < δ_x}`. -/
theorem mem_Ia (δ₀ : ℝ) (T : Torus) (a j : ℤ) :
    j ∈ Ia δ₀ T a ↔ |T.κ * (j : ℝ) - xa δ₀ T a| < δx δ₀ T := by
  unfold Ia
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have hκ := T.κ_pos
    have h' := abs_lt.mp h
    refine ⟨⟨?_, ?_⟩, h⟩
    · rw [Int.floor_le_iff, div_lt_iff₀ hκ]
      nlinarith [h'.1]
    · rw [Int.le_ceil_iff, lt_div_iff₀ hκ]
      nlinarith [h'.2]

/-- **Lemma 3.2(ii)**: `n_x ≥ 4`, `δ_x ∈ [δ₋, δ₊]` and `δ_x/κ ≥ 1`. -/
theorem consistency_ii {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) :
    4 ≤ nx δ₀ T ∧ δminus δ₀ ≤ δx δ₀ T ∧ δx δ₀ T ≤ δplus δ₀ ∧ 1 ≤ δx δ₀ T / T.κ := by
  obtain ⟨hLy, hLx⟩ := hT
  have hπ := Real.pi_pos
  have hround : |T.Lx / δ₀ - ((round (T.Lx / δ₀) : ℤ) : ℝ)| ≤ 1 / 2 := abs_sub_round _
  have hnx : ((nx δ₀ T : ℕ) : ℝ) = ((round (T.Lx / δ₀) : ℤ) : ℝ) := by
    have h := nx_spec hδ₀ T
    have h' : (((nx δ₀ T : ℕ) : ℤ) : ℝ) = ((round (T.Lx / δ₀) : ℤ) : ℝ) := by rw [h]
    simpa using h'
  rw [← hnx] at hround
  have hv4 : 4 < T.Lx / δ₀ := by rw [lt_div_iff₀ hδ₀]; linarith
  have hn1 : T.Lx / δ₀ - 1 / 2 ≤ (nx δ₀ T : ℝ) := by linarith [(abs_le.mp hround).2]
  have hn2 : (nx δ₀ T : ℝ) ≤ T.Lx / δ₀ + 1 / 2 := by linarith [(abs_le.mp hround).1]
  have hnpos : 0 < (nx δ₀ T : ℝ) := by linarith
  have h4 : 4 ≤ nx δ₀ T := by
    have h3 : (3 : ℝ) < (nx δ₀ T : ℝ) := by linarith
    have : 3 < nx δ₀ T := by exact_mod_cast h3
    omega
  have hLxv : T.Lx = T.Lx / δ₀ * δ₀ := by field_simp
  have hδx : δx δ₀ T = T.Lx / (nx δ₀ T : ℝ) := rfl
  have hlow : 2 / 3 * δ₀ ≤ δx δ₀ T := by
    rw [hδx, le_div_iff₀ hnpos]
    nlinarith [mul_le_mul_of_nonneg_left hn2 hδ₀.le]
  have hκ_le : T.κ ≤ 2 / 3 * δ₀ := by
    have hLy3 : 3 * π / δ₀ ≤ T.Ly := le_trans (le_max_right _ _) hLy
    rw [div_le_iff₀ hδ₀] at hLy3
    unfold Torus.κ
    rw [div_le_iff₀ T.Ly_pos]
    nlinarith
  refine ⟨h4, ?_, ?_, ?_⟩
  · unfold δminus; exact hlow
  · unfold δplus
    rw [hδx, div_le_iff₀ hnpos]
    nlinarith [mul_le_mul_of_nonneg_left hn1 hδ₀.le]
  · rw [le_div_iff₀ T.κ_pos, one_mul]
    linarith

/-- **Lemma 3.2(ii)**, after the colon: "every window contains at least one orbital centre". -/
theorem Ia_nonempty {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (a : ℤ) :
    (Ia δ₀ T a).Nonempty := by
  obtain ⟨_, hδm, _, h1⟩ := consistency_ii hδ₀ hT
  have hκ := T.κ_pos
  have hκδ : T.κ ≤ δx δ₀ T := by rwa [le_div_iff₀ hκ, one_mul] at h1
  refine ⟨⌊xa δ₀ T a / T.κ⌋, (mem_Ia δ₀ T a _).mpr ?_⟩
  have hf1 : (⌊xa δ₀ T a / T.κ⌋ : ℝ) ≤ xa δ₀ T a / T.κ := Int.floor_le _
  have hf2 : xa δ₀ T a / T.κ < (⌊xa δ₀ T a / T.κ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hκ] at hf1
  rw [div_lt_iff₀ hκ] at hf2
  rw [abs_lt]
  constructor <;> nlinarith

/-- `n_y ≥ 2` on admissible tori (from `n_y ≥ 2δ_x/κ` and `δ_x/κ ≥ 1`): the slot lattice is not
empty, and `n_y^{−1/2} ≠ 0`. Not a statement of the paper; a non-vacuity check of the encoding. -/
theorem two_le_ny {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) :
    2 ≤ ny δ₀ T := by
  obtain ⟨_, _, _, h1⟩ := consistency_ii hδ₀ hT
  have h := ny_spec δ₀ T
  have h2 : (2 : ℝ) ≤ 2 * δx δ₀ T / T.κ := by rw [mul_div_assoc]; linarith
  have h3 : (2 : ℤ) ≤ ⌈2 * δx δ₀ T / T.κ⌉ := Int.le_ceil_iff.mpr (by push_cast; linarith)
  omega

/-- Admissible tori exist for every `δ₀ > 0`. Not a statement of the paper; a non-vacuity check:
the statements below quantify over admissible tori. -/
theorem exists_admissible {δ₀ : ℝ} (hδ₀ : 0 < δ₀) : ∃ T : Torus, T.Admissible δ₀ := by
  have hπ := Real.pi_pos
  have hLx0 : 0 < 4 * δ₀ + 4 := by positivity
  have hL0 : 0 < L0 δ₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  set N : ℕ := ⌈L0 δ₀ * (4 * δ₀ + 4) / (4 * π)⌉₊ + 1 with hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hLy0 : 0 < 2 * π * ((2 * N : ℕ) : ℝ) / (4 * δ₀ + 4) := by positivity
  refine ⟨⟨N, 4 * δ₀ + 4, 2 * π * ((2 * N : ℕ) : ℝ) / (4 * δ₀ + 4), hLx0, hLy0, ?_⟩, ?_, le_refl _⟩
  · field_simp
  · show L0 δ₀ ≤ 2 * π * ((2 * N : ℕ) : ℝ) / (4 * δ₀ + 4)
    have h1 : L0 δ₀ * (4 * δ₀ + 4) / (4 * π) ≤ (⌈L0 δ₀ * (4 * δ₀ + 4) / (4 * π)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : L0 δ₀ * (4 * δ₀ + 4) / (4 * π) ≤ (N : ℝ) := by rw [hN]; push_cast; linarith
    rw [div_le_iff₀ (by positivity)] at h2
    rw [le_div_iff₀ hLx0]
    push_cast
    nlinarith

/-! ## Helpers for Lemma 3.5(i) (phase (b); proof devices, not statements of the paper) -/

/-- Step 1 for one term: `w_a(j) e^{−2πijℓ/n_y} φ_{j+mN_φ}(R) = c₀ e^{imL_xR_y} g_m(j) e^{ijξ}`. -/
theorem term_identity (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (hny : ny δ₀ T ≠ 0) (a ℓ j m : ℤ)
    (R : ℝ × ℝ) :
    ((wa η δ₀ T a j : ℝ) : ℂ) *
        Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (ℓ : ℂ) / ((ny δ₀ T : ℕ) : ℂ))) *
        phi T (j + m * (T.Nφ : ℤ)) R =
      (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((m * T.Lx * R.2 : ℝ) : ℂ) * I) *
        (((window η (T.κ / δx δ₀ T * j - a) * Analysis.q0 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
          cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ℓ) : ℝ) : ℂ) * I)) := by
  have hw : wa η δ₀ T a j = window η (T.κ / δx δ₀ T * j - a) := by
    unfold wa; congr 1; ring
  have hq : Real.exp (-((R.1 - T.κ * (((j + m * (T.Nφ : ℤ) : ℤ)) : ℝ)) ^ 2) / 2) =
      Analysis.q0 (T.κ * j - (R.1 - m * T.Lx)) := by
    unfold Analysis.q0
    rw [Torus.Lx_eq]
    congr 1
    push_cast
    ring
  have hphase : Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (ℓ : ℂ) / ((ny δ₀ T : ℕ) : ℂ))) *
        Complex.exp (I * (T.κ : ℂ) * (((j + m * (T.Nφ : ℤ) : ℤ)) : ℂ) * (R.2 : ℂ)) =
      cexp (((m * T.Lx * R.2 : ℝ) : ℂ) * I) *
        cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ℓ) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have hκLyC : (T.κ : ℂ) * (T.Ly : ℂ) = 2 * (π : ℂ) := by exact_mod_cast Torus.κ_mul_Ly T
    have hLxC : (T.Lx : ℂ) = (T.κ : ℂ) * ((T.Nφ : ℕ) : ℂ) := by exact_mod_cast Torus.Lx_eq T
    have hnyC : ((ny δ₀ T : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hny
    simp only [yl, δy]
    push_cast
    rw [hLxC]
    linear_combination ((j : ℂ) * (ℓ : ℂ) * I / ((ny δ₀ T : ℕ) : ℂ)) * hκLyC
  unfold phi
  rw [hw, hq, show ((window η (T.κ / δx δ₀ T * j - a) * Analysis.q0 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ)
      = ((window η (T.κ / δx δ₀ T * j - a) : ℝ) : ℂ) *
        ((Analysis.q0 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) from Complex.ofReal_mul _ _]
  linear_combination ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ((window η (T.κ / δx δ₀ T * j - a) : ℝ) : ℂ) *
      ((Analysis.q0 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ)) * hphase

/-- Step 1: `z_s(R) = n_y^{−1/2} (L_y√π)^{−1/2} Σ_m e^{imL_xR_y} S_m`,
`S_m = Σ_j w(κj/δ_x − a) q₀(κj − (R_x − mL_x)) e^{ijξ}`, `ξ = κ(R_y − y_ℓ)`. -/
theorem frame_repr {η : ℝ → ℝ} (hη : IsProfile η) (δ₀ : ℝ) (T : Torus) (hny : ny δ₀ T ≠ 0)
    (hδx : 0 < δx δ₀ T) (s : Slot δ₀ T) (R : ℝ × ℝ) :
    frame η δ₀ T s R =
      (((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' m : ℤ, cexp (((m * T.Lx * R.2 : ℝ) : ℂ) * I) *
          ∑' j : ℤ, ((window η (T.κ / δx δ₀ T * j - ((s.1 : ℕ) : ℤ)) *
              Analysis.q0 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
            cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) : ℝ) : ℂ) * I)) := by
  unfold frame
  congr 1
  set a : ℤ := ((s.1 : ℕ) : ℤ) with ha
  set ℓ : ℤ := ((s.2 : ℕ) : ℤ) with hℓ
  have h1 : ∀ j ∈ Ia δ₀ T a, ((wa η δ₀ T a j : ℝ) : ℂ) *
      Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (ℓ : ℂ) / ((ny δ₀ T : ℕ) : ℂ))) *
      psi T (j : ZMod T.Nφ) R =
      ∑' m : ℤ, (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((m * T.Lx * R.2 : ℝ) : ℂ) * I) *
        (((window η (T.κ / δx δ₀ T * j - a) * Analysis.q0 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
          cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ℓ) : ℝ) : ℂ) * I)) := by
    intro j _
    rw [psi_intCast, ← tsum_mul_left]
    congr 1
    funext m
    exact term_identity η δ₀ T hny a ℓ j m R
  rw [Finset.sum_congr rfl h1]
  have hsum : ∀ j ∈ Ia δ₀ T a, Summable (fun m : ℤ =>
      (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((m * T.Lx * R.2 : ℝ) : ℂ) * I) *
        (((window η (T.κ / δx δ₀ T * j - a) * Analysis.q0 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
          cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ℓ) : ℝ) : ℂ) * I))) := by
    intro j _
    have h := (psi_summable T j R).mul_left (((wa η δ₀ T a j : ℝ) : ℂ) *
      Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (ℓ : ℂ) / ((ny δ₀ T : ℕ) : ℂ))))
    refine h.congr (fun m => ?_)
    exact term_identity η δ₀ T hny a ℓ j m R
  rw [← Summable.tsum_finsetSum hsum, ← tsum_mul_left]
  congr 1
  funext m
  rw [← Finset.mul_sum]
  have hz : ∀ j ∉ Ia δ₀ T a,
      ((window η (T.κ / δx δ₀ T * j - a) * Analysis.q0 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
        cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ℓ) : ℝ) : ℂ) * I) = 0 := by
    intro j hj
    rw [mem_Ia, not_lt] at hj
    have h1' : 1 ≤ |T.κ / δx δ₀ T * j - a| := by
      have e : T.κ / δx δ₀ T * j - a = (T.κ * j - xa δ₀ T a) / δx δ₀ T := by
        unfold xa; field_simp
      rw [e, abs_div, abs_of_pos hδx, le_div_iff₀ hδx, one_mul]
      exact hj
    rw [window_eq_zero hη h1']
    simp
  rw [tsum_eq_sum hz, mul_assoc]

/-- Step 5: `(n_y L_y √π)^{−1/2} (2δ_x/κ + n + 1) ≤ (n + 3)(1 + 2δ₀)`. -/
theorem prefactor_bound {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (n : ℕ) :
    (ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) * (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
      (2 / (T.κ / δx δ₀ T) + n + 1) ≤ (n + 3) * (1 + 2 * δ₀) := by
  have hπ := Real.pi_pos
  have hκ := T.κ_pos
  obtain ⟨_, hδm, hδp, hδκ⟩ := consistency_ii hδ₀ hT
  unfold δminus at hδm
  unfold δplus at hδp
  have hδpos : 0 < δx δ₀ T := by linarith
  set δ := δx δ₀ T with hδ
  set t := δ / T.κ with ht
  have ht1 : 1 ≤ t := hδκ
  have hny2 : 2 * t ≤ (ny δ₀ T : ℝ) := by
    have h := ny_spec δ₀ T
    have h2 : 2 * δ / T.κ ≤ ((⌈2 * δ / T.κ⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h3 : ((ny δ₀ T : ℕ) : ℝ) = ((⌈2 * δ / T.κ⌉ : ℤ) : ℝ) := by exact_mod_cast h
    rw [h3, ht, ← mul_div_assoc]
    exact h2
  have hLy : T.Ly = 2 * π / T.κ := by
    have := Torus.κ_mul_Ly T
    field_simp
    linarith
  have hsqrtπ : 1 ≤ Real.sqrt π := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
  have hnyp : 0 < (ny δ₀ T : ℝ) := by linarith
  set Y := (ny δ₀ T : ℝ) * (T.Ly * Real.sqrt π) with hY
  have hLyp : 0 < T.Ly * Real.sqrt π := mul_pos T.Ly_pos (by positivity)
  have hYpos : 0 < Y := mul_pos hnyp hLyp
  have hP : (ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) * (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) =
      1 / Real.sqrt Y := by
    rw [← Real.mul_rpow hnyp.le hLyp.le, Real.rpow_neg hYpos.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hP]
  have hQ : 2 / (T.κ / δ) + n + 1 = 2 * t + n + 1 := by rw [ht]; field_simp
  rw [hQ, one_div_mul_eq_div, div_le_iff₀ (Real.sqrt_pos.mpr hYpos)]
  -- `Y ≥ 4 t² / δ`
  have hY4 : 4 * t ^ 2 / δ ≤ Y := by
    have h1 : 2 * π / T.κ ≤ T.Ly * Real.sqrt π := by
      rw [← hLy]; nlinarith [T.Ly_pos]
    have h2 : 2 * t * (2 * π / T.κ) ≤ Y := by
      rw [hY]
      exact mul_le_mul hny2 h1 (by positivity) hnyp.le
    have h3 : 4 * t ^ 2 / δ ≤ 2 * t * (2 * π / T.κ) := by
      rw [ht]
      rw [div_le_iff₀ hδpos]
      field_simp
      nlinarith [Real.two_le_pi, hκ, hδpos]
    linarith
  have hK : 0 ≤ ((n : ℝ) + 3) * (1 + 2 * δ₀) := by positivity
  have hlhs : 0 ≤ 2 * t + n + 1 := by positivity
  rw [show ((n : ℝ) + 3) * (1 + 2 * δ₀) * Real.sqrt Y =
      Real.sqrt ((((n : ℝ) + 3) * (1 + 2 * δ₀)) ^ 2 * Y) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK]]
  rw [show 2 * t + n + 1 = Real.sqrt ((2 * t + n + 1) ^ 2) from (Real.sqrt_sq hlhs).symm]
  apply Real.sqrt_le_sqrt
  have hA : 2 * t + n + 1 ≤ ((n : ℝ) + 3) * t := by nlinarith
  have hB : (2 * t + n + 1) ^ 2 ≤ (((n : ℝ) + 3) * t) ^ 2 := pow_le_pow_left₀ hlhs hA 2
  have hC : (((n : ℝ) + 3) * t) ^ 2 ≤ (((n : ℝ) + 3) * (1 + 2 * δ₀)) ^ 2 * (4 * t ^ 2 / δ) := by
    rw [show (((n : ℝ) + 3) * (1 + 2 * δ₀)) ^ 2 * (4 * t ^ 2 / δ) =
        (((n : ℝ) + 3) * t) ^ 2 * (4 * (1 + 2 * δ₀) ^ 2 / δ) by field_simp]
    have h4 : 1 ≤ 4 * (1 + 2 * δ₀) ^ 2 / δ := by
      rw [le_div_iff₀ hδpos, one_mul]; nlinarith
    nlinarith [sq_nonneg (((n : ℝ) + 3) * t)]
  have hD : (((n : ℝ) + 3) * (1 + 2 * δ₀)) ^ 2 * (4 * t ^ 2 / δ) ≤
      (((n : ℝ) + 3) * (1 + 2 * δ₀)) ^ 2 * Y :=
    mul_le_mul_of_nonneg_left hY4 (sq_nonneg _)
  linarith

/-- Steps 2–6 for a general Gaussian-type profile `q` (`q₀` for (i), `q₁` for (ii)): the bound of
`n_y^{−1/2}(L_y√π)^{−1/2} Σ_m e^{imL_xR_y} Σ_j w(κj/δ_x − a) q(κj − (R_x − mL_x)) e^{ijξ}`. -/
theorem images_bound {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (n : ℕ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hqb : ∀ i : ℕ, ∃ μ : ℝ, 0 ≤ μ ∧ ∀ u : ℝ, |iteratedDeriv i q u| ≤ μ * Real.exp (-(u ^ 2 / 4))) :
    ∃ C : ℝ, ∀ T : Torus, T.Admissible δ₀ → ∀ (s : Slot δ₀ T) (R : ℝ × ℝ),
      ‖(((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' m : ℤ, cexp (((m * T.Lx * R.2 : ℝ) : ℂ) * I) *
          ∑' j : ℤ, ((window η (T.κ / δx δ₀ T * j - ((s.1 : ℕ) : ℤ)) *
              q (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
            cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) : ℝ) : ℂ) * I))‖ ≤
      C * ((1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ n)⁻¹ *
        Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2 / 4)) := by
  have hπ := Real.pi_pos
  obtain ⟨K0, hK00, hK0⟩ := Analysis.windowed_sum_bound hη.2.2 hη.1 hη.2.1 hq hqb 0
  obtain ⟨Kn, hKn0, hKn⟩ := Analysis.windowed_sum_bound hη.2.2 hη.1 hη.2.1 hq hqb n
  set Y : ℝ := (π / 2) ^ n * Kn * (1 + 3 / (2 * δ₀)) ^ n with hY
  set C'' : ℝ := 2 ^ n * max K0 Y with hC''
  set KG : ℝ := ∑' t : ℤ, Analysis.Gimg t with hKG
  have hKG0 : 0 ≤ KG := tsum_nonneg Analysis.Gimg_nonneg
  have hY0 : 0 ≤ Y := by positivity
  have hmax0 : 0 ≤ max K0 Y := le_trans hK00 (le_max_left _ _)
  have hC''0 : 0 ≤ C'' := by positivity
  refine ⟨((n : ℝ) + 3) * (1 + 2 * δ₀) * C'' * KG, fun T hT s R => ?_⟩
  -- the torus
  obtain ⟨hnx4, hδm, hδp, hδκ⟩ := consistency_ii hδ₀ hT
  unfold δminus at hδm
  unfold δplus at hδp
  have hny2 := two_le_ny hδ₀ hT
  have hκ := T.κ_pos
  have hδpos : 0 < δx δ₀ T := by linarith
  have hLx4 : 4 ≤ T.Lx := by linarith [hT.2]
  have h2δ : 2 * δx δ₀ T ≤ T.Lx := by
    have e : δx δ₀ T * (nx δ₀ T : ℝ) = T.Lx := by
      unfold δx; field_simp
    have h4 : (4 : ℝ) ≤ (nx δ₀ T : ℝ) := by exact_mod_cast hnx4
    nlinarith
  set δ := δx δ₀ T with hδ
  set α := T.κ / δ with hα_def
  have hα : 0 < α := div_pos hκ hδpos
  set a : ℤ := ((s.1 : ℕ) : ℤ) with ha
  set ℓ : ℤ := ((s.2 : ℕ) : ℤ) with hℓ
  set ξ : ℝ := T.κ * (R.2 - yl δ₀ T ℓ) with hξ
  set Δy := pdist T.Ly (R.2 - yl δ₀ T ℓ) with hΔy
  have hΔy0 : 0 ≤ Δy := Metric.infDist_nonneg
  set Q : ℝ := 2 / α + n + 1 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  -- Jordan for ξ
  have hJ : 2 / π * (T.κ * Δy) ≤ ‖1 - cexp (ξ * I)‖ := by
    have h := Analysis.jordan_infDist ξ
    have e : Metric.infDist ξ (AddSubgroup.zmultiples (2 * π) : Set ℝ) = T.κ * Δy := by
      rw [hξ, ← Torus.κ_mul_Ly T]
      exact Analysis.infDist_zmultiples_mul hκ T.Ly _
    rw [e] at h
    exact h
  -- the per-image bound
  have hSm : ∀ m : ℤ,
      ‖∑' j : ℤ, ((Analysis.win η (α * j - a) * q (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
          cexp ((j : ℂ) * (ξ : ℂ) * I)‖ ≤
        Q * C'' * ((1 + Δy) ^ n)⁻¹ *
          Real.exp (-((max (|R.1 - xa δ₀ T a - m * T.Lx| - δ) 0) ^ 2 / 4)) := by
    intro m
    set εm := max (|R.1 - xa δ₀ T a - m * T.Lx| - δ) 0 with hεm
    have hε0 : 0 ≤ εm := le_max_right _ _
    have hεv : ∀ v : ℝ, |α * v - a| ≤ 1 → εm ≤ |T.κ * v - (R.1 - m * T.Lx)| := by
      intro v hv
      have h1 : |T.κ * v - a * δ| ≤ δ := by
        have e : T.κ * v - a * δ = δ * (α * v - a) := by rw [hα_def]; field_simp
        rw [e, abs_mul, abs_of_pos hδpos]
        nlinarith [abs_nonneg (α * v - a)]
      apply max_le _ (abs_nonneg _)
      have hxa : xa δ₀ T a = a * δ := rfl
      rw [hxa]
      have h2 := abs_sub_abs_le_abs_sub (R.1 - a * δ - m * T.Lx) (T.κ * v - a * δ)
      have e2 : (R.1 - a * δ - m * T.Lx) - (T.κ * v - a * δ) = -(T.κ * v - (R.1 - m * T.Lx)) := by
        ring
      rw [e2, abs_neg] at h2
      linarith
    have h0 := hK0 α T.κ a (R.1 - m * T.Lx) εm ξ hα hκ hε0 hεv
    have hn := hKn α T.κ a (R.1 - m * T.Lx) εm ξ hα hκ hε0 hεv
    simp only [pow_zero, one_mul, mul_one, Nat.cast_zero, add_zero] at h0
    have hcomb := Analysis.decay_combine n hκ hΔy0 h0 hn hJ
    refine le_trans hcomb ?_
    have he0 : 0 ≤ Real.exp (-(εm ^ 2 / 4)) := (Real.exp_pos _).le
    have hratio : π / (2 * T.κ) * (α + T.κ) ≤ π / 2 * (1 + 3 / (2 * δ₀)) := by
      have e : π / (2 * T.κ) * (α + T.κ) = π / 2 * (1 / δ + 1) := by
        rw [hα_def]; field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h3 : 1 / δ ≤ 3 / (2 * δ₀) := by
        rw [div_le_div_iff₀ hδpos (by positivity)]; linarith
      linarith
    have hpowr : (π / (2 * T.κ)) ^ n * (α + T.κ) ^ n ≤ (π / 2) ^ n * (1 + 3 / (2 * δ₀)) ^ n := by
      rw [← mul_pow, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hratio n
    have hXn : (π / (2 * T.κ)) ^ n * ((2 / α + n + 1) * (Kn * (α + T.κ) ^ n * Real.exp (-(εm ^ 2 / 4)))) ≤
        Q * (max K0 Y * Real.exp (-(εm ^ 2 / 4))) := by
      calc (π / (2 * T.κ)) ^ n * ((2 / α + n + 1) * (Kn * (α + T.κ) ^ n * Real.exp (-(εm ^ 2 / 4))))
          = Q * (Kn * ((π / (2 * T.κ)) ^ n * (α + T.κ) ^ n) * Real.exp (-(εm ^ 2 / 4))) := by
            rw [hQ]; ring
        _ ≤ Q * (Kn * ((π / 2) ^ n * (1 + 3 / (2 * δ₀)) ^ n) * Real.exp (-(εm ^ 2 / 4))) := by
            apply mul_le_mul_of_nonneg_left _ hQ0
            apply mul_le_mul_of_nonneg_right _ he0
            exact mul_le_mul_of_nonneg_left hpowr hKn0
        _ = Q * (Y * Real.exp (-(εm ^ 2 / 4))) := by rw [hY]; ring
        _ ≤ Q * (max K0 Y * Real.exp (-(εm ^ 2 / 4))) := by
            apply mul_le_mul_of_nonneg_left _ hQ0
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) he0
    have hB0 : (2 / α + 1) * (K0 * Real.exp (-(εm ^ 2 / 4))) ≤ Q * (max K0 Y * Real.exp (-(εm ^ 2 / 4))) := by
      have hq1 : 2 / α + 1 ≤ Q := by rw [hQ]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      apply mul_le_mul hq1 _ (by positivity) hQ0
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) he0
    have hmax : max ((2 / α + 1) * (K0 * Real.exp (-(εm ^ 2 / 4))))
        ((π / (2 * T.κ)) ^ n * ((2 / α + n + 1) * (Kn * (α + T.κ) ^ n * Real.exp (-(εm ^ 2 / 4))))) ≤
        Q * (max K0 Y * Real.exp (-(εm ^ 2 / 4))) := max_le hB0 hXn
    calc 2 ^ n * max ((2 / α + 1) * (K0 * Real.exp (-(εm ^ 2 / 4))))
          ((π / (2 * T.κ)) ^ n * ((2 / α + n + 1) * (Kn * (α + T.κ) ^ n * Real.exp (-(εm ^ 2 / 4))))) *
          ((1 + Δy) ^ n)⁻¹
        ≤ 2 ^ n * (Q * (max K0 Y * Real.exp (-(εm ^ 2 / 4)))) * ((1 + Δy) ^ n)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hmax (by positivity)
      _ = Q * C'' * ((1 + Δy) ^ n)⁻¹ * Real.exp (-(εm ^ 2 / 4)) := by rw [hC'']; ring
  -- Step 1 and the sum over the images
  simp only [show window η = Analysis.win η from rfl]
  set m₀ : ℤ := round (T.Lx⁻¹ * (R.1 - xa δ₀ T a)) with hm₀
  set E := Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T a) - δ) 0) ^ 2 / 4)) with hE
  set cst := Q * C'' * ((1 + Δy) ^ n)⁻¹ * E with hcst
  have hbound : ∀ m : ℤ, ‖cexp (((m * T.Lx * R.2 : ℝ) : ℂ) * I) *
      ∑' j : ℤ, ((Analysis.win η (T.κ / δ * j - a) * q (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
        cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ℓ) : ℝ) : ℂ) * I)‖ ≤ cst * Analysis.Gimg (m - m₀) := by
    intro m
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    calc _ ≤ Q * C'' * ((1 + Δy) ^ n)⁻¹ *
            Real.exp (-((max (|R.1 - xa δ₀ T a - m * T.Lx| - δ) 0) ^ 2 / 4)) := hSm m
      _ ≤ Q * C'' * ((1 + Δy) ^ n)⁻¹ * (E * Analysis.Gimg (m - m₀)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Analysis.image_pointwise hLx4 hδpos.le h2δ m
      _ = cst * Analysis.Gimg (m - m₀) := by rw [hcst]; ring
  have hsum := tsum_of_norm_bounded ((Analysis.hasSum_Gimg_shift m₀).mul_left cst) hbound
  have hcy : 0 ≤ (ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hc0 : 0 ≤ (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (mul_nonneg T.Ly_pos.le (Real.sqrt_nonneg _)) _
  have hpre := prefactor_bound hδ₀ hT n
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hcy, abs_of_nonneg hc0]
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hinv0 : 0 ≤ ((1 + Δy) ^ n)⁻¹ := by positivity
  calc (ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * ‖_‖)
      ≤ (ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * (cst * KG)) := by
        apply mul_le_mul_of_nonneg_left _ hcy
        exact mul_le_mul_of_nonneg_left hsum hc0
    _ = ((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) * (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Q) *
          (C'' * KG * ((1 + Δy) ^ n)⁻¹ * E) := by rw [hcst]; ring
    _ ≤ (((n : ℝ) + 3) * (1 + 2 * δ₀)) * (C'' * KG * ((1 + Δy) ^ n)⁻¹ * E) := by
        apply mul_le_mul_of_nonneg_right hpre (by positivity)
    _ = ((n : ℝ) + 3) * (1 + 2 * δ₀) * C'' * KG * ((1 + Δy) ^ n)⁻¹ * E := by ring

/-- Lemma 3.5(i) for integer `n`, with the stronger Gaussian `e^{−(Δ_x − δ_x)₊²/4}`. -/
theorem localization_core {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (n : ℕ) :
    ∃ C : ℝ, ∀ T : Torus, T.Admissible δ₀ → ∀ (s : Slot δ₀ T) (R : ℝ × ℝ),
      ‖frame η δ₀ T s R‖ ≤ C * ((1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ n)⁻¹ *
        Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2 / 4)) := by
  obtain ⟨C, hC⟩ := images_bound hη hδ₀ n Analysis.contDiff_q0 Analysis.q0_bounds
  refine ⟨C, fun T hT s R => ?_⟩
  obtain ⟨_, hδm, _, _⟩ := consistency_ii hδ₀ hT
  unfold δminus at hδm
  have hny2 := two_le_ny hδ₀ hT
  rw [frame_repr hη δ₀ T (by omega) (by linarith) s R]
  exact hC T hT s R

/-! ## Helpers for Lemma 3.5(ii): the termwise derivatives of `ψ_j` (Lemma 2.2(i), (iii)) -/

theorem hasDerivAt_phi_x (T : Torus) (n : ℤ) (x y : ℝ) :
    HasDerivAt (fun x' : ℝ => phi T n (x', y)) ((((-(x - T.κ * n)) : ℝ) : ℂ) * phi T n (x, y)) x := by
  have h1 : HasDerivAt (fun x' : ℝ => -((x' - T.κ * n) ^ 2) / 2) (-(x - T.κ * n)) x := by
    have h := (((hasDerivAt_id x).sub_const (T.κ * n)).pow 2).neg.div_const 2
    convert h using 1
    · funext y; simp only [Pi.neg_apply, Pi.pow_apply, id]
    · norm_num [id]; ring
  have hc := h1.exp.ofReal_comp.const_mul ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (y : ℂ)))
  unfold phi
  convert hc using 1
  push_cast
  ring

theorem hasDerivAt_phi_y (T : Torus) (n : ℤ) (x y : ℝ) :
    HasDerivAt (fun y' : ℝ => phi T n (x, y')) ((I * (T.κ : ℂ) * (n : ℂ)) * phi T n (x, y)) y := by
  have hin : HasDerivAt (fun y' : ℝ => I * (T.κ : ℂ) * (n : ℂ) * (y' : ℂ)) (I * (T.κ : ℂ) * (n : ℂ)) y := by
    have h := (hasDerivAt_id y).ofReal_comp.const_mul (I * (T.κ : ℂ) * (n : ℂ))
    simpa using h
  have hc := (hin.cexp.const_mul (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).mul_const
    (((Real.exp (-((x - T.κ * n) ^ 2) / 2) : ℝ) : ℂ))
  unfold phi
  convert hc using 1
  ring

theorem summable_gauss8 (T : Torus) (j : ℤ) (x : ℝ) :
    Summable (fun m : ℤ => Real.exp (-((x - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 8))) := by
  have hL : 0 < T.Lx / 2 := by linarith [T.Lx_pos]
  refine (Analysis.summable_gauss_int hL ((x - T.κ * j) / 2)).congr (fun m => ?_)
  congr 1
  rw [Torus.Lx_eq]
  push_cast
  ring

theorem Dx_term_bound (T : Torus) (n : ℤ) (x x' y : ℝ) (hx : |x' - x| < 1) :
    ‖((-(x' - T.κ * n) : ℝ) : ℂ) * phi T n (x', y)‖ ≤
      5 * Real.exp (1 / 4) * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-((x - T.κ * n) ^ 2 / 8))) := by
  rw [norm_mul, norm_phi, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  have hc0 : 0 ≤ (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (mul_nonneg T.Ly_pos.le (Real.sqrt_nonneg _)) _
  set t' := x' - T.κ * n with ht'
  set t := x - T.κ * n with ht
  have h5 : |t'| * Real.exp (-(t' ^ 2 / 4)) ≤ 5 := by
    have h := Analysis.abs_pow_mul_exp_le t' 1
    norm_num at h
    linarith
  have hsplit : Real.exp (-(t' ^ 2) / 2) = Real.exp (-(t' ^ 2 / 4)) * Real.exp (-(t' ^ 2 / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hcomp : Real.exp (-(t' ^ 2 / 4)) ≤ Real.exp (1 / 4) * Real.exp (-(t ^ 2 / 8)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hd : t' - t = x' - x := by rw [ht', ht]; ring
    have h2 : (t' - t) ^ 2 ≤ 1 := by
      rw [hd]; have := abs_lt.mp hx; nlinarith
    nlinarith [sq_nonneg (2 * t' - t), h2]
  have hE : 0 ≤ Real.exp (-(t' ^ 2 / 4)) := (Real.exp_pos _).le
  calc |t'| * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(t' ^ 2) / 2))
      = (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
          ((|t'| * Real.exp (-(t' ^ 2 / 4))) * Real.exp (-(t' ^ 2 / 4))) := by rw [hsplit]; ring
    _ ≤ (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
          (5 * (Real.exp (1 / 4) * Real.exp (-(t ^ 2 / 8)))) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        exact mul_le_mul h5 hcomp hE (by norm_num)
    _ = 5 * Real.exp (1 / 4) * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(t ^ 2 / 8))) := by ring

theorem Dy_term_bound (T : Torus) (n : ℤ) (x y : ℝ) :
    ‖(I * (T.κ : ℂ) * (n : ℂ)) * phi T n (x, y)‖ ≤
      (|x| + 5) * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-((x - T.κ * n) ^ 2 / 8))) := by
  rw [norm_mul, norm_phi]
  have hc0 : 0 ≤ (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (mul_nonneg T.Ly_pos.le (Real.sqrt_nonneg _)) _
  have hIκn : ‖I * (T.κ : ℂ) * (n : ℂ)‖ = |T.κ * n| := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, show ((T.κ : ℂ)) = ((T.κ : ℝ) : ℂ) from rfl,
      Complex.norm_real, show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  rw [hIκn]
  set t := x - T.κ * n with ht
  have htri : |T.κ * n| ≤ |x| + |t| := by
    have e : T.κ * n = x - t := by rw [ht]; ring
    rw [e]; exact abs_sub _ _
  have h5 : |t| * Real.exp (-(t ^ 2 / 4)) ≤ 5 := by
    have h := Analysis.abs_pow_mul_exp_le t 1
    norm_num at h
    linarith
  have e1 : Real.exp (-(t ^ 2) / 2) ≤ Real.exp (-(t ^ 2 / 8)) := by
    apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg t]
  have e2 : |t| * Real.exp (-(t ^ 2) / 2) ≤ 5 * Real.exp (-(t ^ 2 / 8)) := by
    have hsplit : Real.exp (-(t ^ 2) / 2) = Real.exp (-(t ^ 2 / 4)) * Real.exp (-(t ^ 2 / 4)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e3 : Real.exp (-(t ^ 2 / 4)) ≤ Real.exp (-(t ^ 2 / 8)) := by
      apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg t]
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul h5 e3 (Real.exp_pos _).le (by norm_num)
  have hE : 0 ≤ Real.exp (-(t ^ 2) / 2) := (Real.exp_pos _).le
  calc |T.κ * n| * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2) / 2))
      ≤ (|x| + |t|) * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2) / 2)) :=
        mul_le_mul_of_nonneg_right htri (mul_nonneg hc0 hE)
    _ = (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
          (|x| * Real.exp (-(t ^ 2) / 2) + |t| * Real.exp (-(t ^ 2) / 2)) := by ring
    _ ≤ (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
          (|x| * Real.exp (-(t ^ 2 / 8)) + 5 * Real.exp (-(t ^ 2 / 8))) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        exact add_le_add (mul_le_mul_of_nonneg_left e1 (abs_nonneg _)) e2
    _ = (|x| + 5) * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-(t ^ 2 / 8))) := by ring

theorem psi_hasDerivAt_x (T : Torus) (j : ℤ) (x y : ℝ) :
    HasDerivAt (fun x' : ℝ => psi T (j : ZMod T.Nφ) (x', y))
      (∑' m : ℤ, ((-(x - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) *
        phi T (j + m * (T.Nφ : ℤ)) (x, y)) x := by
  have hfun : (fun x' : ℝ => psi T (j : ZMod T.Nφ) (x', y)) =
      fun x' => ∑' m : ℤ, phi T (j + m * (T.Nφ : ℤ)) (x', y) := by
    funext x'; exact psi_intCast T j (x', y)
  rw [hfun]
  have hu : Summable (fun m : ℤ => 5 * Real.exp (1 / 4) * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-((x - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 8)))) :=
    ((summable_gauss8 T j x).mul_left _).mul_left _
  have hg : ∀ (m : ℤ) (x' : ℝ), x' ∈ Metric.ball x 1 →
      HasDerivAt (fun z : ℝ => phi T (j + m * (T.Nφ : ℤ)) (z, y))
        (((-(x' - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) * phi T (j + m * (T.Nφ : ℤ)) (x', y)) x' :=
    fun m x' _ => hasDerivAt_phi_x T _ x' y
  have hg' : ∀ (m : ℤ) (x' : ℝ), x' ∈ Metric.ball x 1 →
      ‖((-(x' - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) * phi T (j + m * (T.Nφ : ℤ)) (x', y)‖ ≤
        5 * Real.exp (1 / 4) * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-((x - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 8))) := by
    intro m x' hx'
    rw [Metric.mem_ball, Real.dist_eq] at hx'
    exact Dx_term_bound T _ x x' y hx'
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball x 1).isPreconnected hg hg'
    (Metric.mem_ball_self one_pos) (psi_summable T j (x, y)) (Metric.mem_ball_self one_pos)

theorem psi_hasDerivAt_y (T : Torus) (j : ℤ) (x y : ℝ) :
    HasDerivAt (fun y' : ℝ => psi T (j : ZMod T.Nφ) (x, y'))
      (∑' m : ℤ, (I * (T.κ : ℂ) * (((j + m * (T.Nφ : ℤ) : ℤ)) : ℂ)) *
        phi T (j + m * (T.Nφ : ℤ)) (x, y)) y := by
  have hfun : (fun y' : ℝ => psi T (j : ZMod T.Nφ) (x, y')) =
      fun y' => ∑' m : ℤ, phi T (j + m * (T.Nφ : ℤ)) (x, y') := by
    funext y'; exact psi_intCast T j (x, y')
  rw [hfun]
  have hu : Summable (fun m : ℤ => (|x| + 5) * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-((x - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 8)))) :=
    ((summable_gauss8 T j x).mul_left _).mul_left _
  exact hasDerivAt_tsum hu (fun m y' => hasDerivAt_phi_y T _ x y')
    (fun m y' => Dy_term_bound T _ x y') (psi_summable T j (x, y)) y

theorem summable_Dphi (T : Torus) (j : ℤ) (R : ℝ × ℝ) :
    Summable (fun m : ℤ => ((-(R.1 - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) *
      phi T (j + m * (T.Nφ : ℤ)) R) := by
  refine Summable.of_norm_bounded (((summable_gauss8 T j R.1).mul_left
    ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)))).mul_left (5 * Real.exp (1 / 4))) (fun m => ?_)
  have h := Dx_term_bound T (j + m * (T.Nφ : ℤ)) R.1 R.1 R.2 (by simp)
  simpa only [Prod.mk.eta] using h

/-- **Lemma 2.2(iii)** with the termwise differentiation of Lemma 2.2(i), at a point (the statement
added with part (ii)):
`(Dψ_{[j]})(R) = Σ_m −(R_x − κ(j + mN_φ)) φ_{j+mN_φ}(R)`; the paper writes
`$(D\phi_n)(x,y)=-(x-\kappa n)\,\phi_n(x,y)$`. -/
theorem Dcov_psi (T : Torus) (j : ℤ) (R : ℝ × ℝ) :
    Dcov (psi T (j : ZMod T.Nφ)) R =
      ∑' m : ℤ, ((-(R.1 - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) *
        phi T (j + m * (T.Nφ : ℤ)) R := by
  unfold Dcov
  rw [(psi_hasDerivAt_x T j R.1 R.2).deriv, (psi_hasDerivAt_y T j R.1 R.2).deriv, psi_intCast]
  simp only [Prod.mk.eta]
  have hA : Summable (fun m : ℤ => ((-(R.1 - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) *
      phi T (j + m * (T.Nφ : ℤ)) R) := by
    refine Summable.of_norm_bounded (((summable_gauss8 T j R.1).mul_left
      ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)))).mul_left (5 * Real.exp (1 / 4))) (fun m => ?_)
    have h := Dx_term_bound T (j + m * (T.Nφ : ℤ)) R.1 R.1 R.2 (by simp)
    simpa only [Prod.mk.eta] using h
  have hφ := psi_summable T j R
  have hBA : ∀ m : ℤ, (I * (T.κ : ℂ) * (((j + m * (T.Nφ : ℤ) : ℤ)) : ℂ)) * phi T (j + m * (T.Nφ : ℤ)) R =
      I * (((-(R.1 - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) * phi T (j + m * (T.Nφ : ℤ)) R +
        (R.1 : ℂ) * phi T (j + m * (T.Nφ : ℤ)) R) := by
    intro m; push_cast; ring
  rw [tsum_congr hBA, tsum_mul_left, hA.tsum_add (hφ.mul_left _), tsum_mul_left]
  linear_combination (-(1 / 2 : ℂ) * ∑' m : ℤ, ((-(R.1 - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) *
    phi T (j + m * (T.Nφ : ℤ)) R) * Complex.I_sq

/-! ## Helpers for Lemma 3.5(ii): `D` through the frame, Step 1 for `Dz_s` -/

/-- `D` commutes with the finite sum and the constants of (3.1). -/
theorem frame_Dcov (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (s : Slot δ₀ T) (R : ℝ × ℝ) :
    Dcov (frame η δ₀ T s) R = (((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ∑ j ∈ Ia δ₀ T ((s.1 : ℕ) : ℤ), ((wa η δ₀ T ((s.1 : ℕ) : ℤ) j : ℝ) : ℂ) *
        Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (((s.2 : ℕ) : ℤ) : ℂ) / ((ny δ₀ T : ℕ) : ℂ))) *
        Dcov (psi T (j : ZMod T.Nφ)) R := by
  set cy : ℂ := (((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcy
  set S := Ia δ₀ T ((s.1 : ℕ) : ℤ) with hS
  set A : ℤ → ℂ := fun j => ((wa η δ₀ T ((s.1 : ℕ) : ℤ) j : ℝ) : ℂ) *
    Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (((s.2 : ℕ) : ℤ) : ℂ) / ((ny δ₀ T : ℕ) : ℂ))) with hA
  have hfx : (fun x : ℝ => frame η δ₀ T s (x, R.2)) =
      fun x => cy * ∑ j ∈ S, A j * psi T (j : ZMod T.Nφ) (x, R.2) := by
    funext x; rfl
  have hfy : (fun y : ℝ => frame η δ₀ T s (R.1, y)) =
      fun y => cy * ∑ j ∈ S, A j * psi T (j : ZMod T.Nφ) (R.1, y) := by
    funext y; rfl
  have hx : HasDerivAt (fun x : ℝ => frame η δ₀ T s (x, R.2))
      (cy * ∑ j ∈ S, A j * deriv (fun x : ℝ => psi T (j : ZMod T.Nφ) (x, R.2)) R.1) R.1 := by
    rw [hfx]
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.const_mul
    exact (psi_hasDerivAt_x T j R.1 R.2).differentiableAt.hasDerivAt
  have hy : HasDerivAt (fun y : ℝ => frame η δ₀ T s (R.1, y))
      (cy * ∑ j ∈ S, A j * deriv (fun y : ℝ => psi T (j : ZMod T.Nφ) (R.1, y)) R.2) R.2 := by
    rw [hfy]
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.const_mul
    exact (psi_hasDerivAt_y T j R.1 R.2).differentiableAt.hasDerivAt
  have hf0 : frame η δ₀ T s R = cy * ∑ j ∈ S, A j * psi T (j : ZMod T.Nφ) R := rfl
  unfold Dcov
  rw [hx.deriv, hy.deriv, hf0]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Step 1 for one term of `Dz_s`: the factor `−(R_x − κn)` turns `q₀` into `q₁`. -/
theorem term_identity_D (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (hny : ny δ₀ T ≠ 0) (a ℓ j m : ℤ)
    (R : ℝ × ℝ) :
    ((wa η δ₀ T a j : ℝ) : ℂ) *
        Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (ℓ : ℂ) / ((ny δ₀ T : ℕ) : ℂ))) *
        ((((-(R.1 - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ))) : ℝ) : ℂ) * phi T (j + m * (T.Nφ : ℤ)) R) =
      (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((m * T.Lx * R.2 : ℝ) : ℂ) * I) *
        (((window η (T.κ / δx δ₀ T * j - a) * Analysis.q1 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
          cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ℓ) : ℝ) : ℂ) * I)) := by
  have h := term_identity η δ₀ T hny a ℓ j m R
  have hf : (-(R.1 - T.κ * ((j + m * (T.Nφ : ℤ) : ℤ) : ℝ))) = T.κ * j - (R.1 - m * T.Lx) := by
    rw [Torus.Lx_eq]; push_cast; ring
  have hq1 : Analysis.q1 (T.κ * j - (R.1 - m * T.Lx)) =
      (T.κ * j - (R.1 - m * T.Lx)) * Analysis.q0 (T.κ * j - (R.1 - m * T.Lx)) := by
    unfold Analysis.q1 Analysis.q0; ring
  rw [hf, hq1]
  have e1 : ((window η (T.κ / δx δ₀ T * j - a) *
      ((T.κ * j - (R.1 - m * T.Lx)) * Analysis.q0 (T.κ * j - (R.1 - m * T.Lx))) : ℝ) : ℂ) =
      ((T.κ * j - (R.1 - m * T.Lx) : ℝ) : ℂ) *
        ((window η (T.κ / δx δ₀ T * j - a) * Analysis.q0 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1]
  linear_combination ((T.κ * j - (R.1 - m * T.Lx) : ℝ) : ℂ) * h

/-- Step 1 for `Dz_s`: the representation of `frame_repr` with `q₁` in place of `q₀`. -/
theorem Dframe_repr {η : ℝ → ℝ} (hη : IsProfile η) (δ₀ : ℝ) (T : Torus) (hny : ny δ₀ T ≠ 0)
    (hδx : 0 < δx δ₀ T) (s : Slot δ₀ T) (R : ℝ × ℝ) :
    Dcov (frame η δ₀ T s) R =
      (((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' m : ℤ, cexp (((m * T.Lx * R.2 : ℝ) : ℂ) * I) *
          ∑' j : ℤ, ((window η (T.κ / δx δ₀ T * j - ((s.1 : ℕ) : ℤ)) *
              Analysis.q1 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
            cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) : ℝ) : ℂ) * I)) := by
  rw [frame_Dcov]
  congr 1
  set a : ℤ := ((s.1 : ℕ) : ℤ) with ha
  set ℓ : ℤ := ((s.2 : ℕ) : ℤ) with hℓ
  have h1 : ∀ j ∈ Ia δ₀ T a, ((wa η δ₀ T a j : ℝ) : ℂ) *
      Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (ℓ : ℂ) / ((ny δ₀ T : ℕ) : ℂ))) *
      Dcov (psi T (j : ZMod T.Nφ)) R =
      ∑' m : ℤ, (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((m * T.Lx * R.2 : ℝ) : ℂ) * I) *
        (((window η (T.κ / δx δ₀ T * j - a) * Analysis.q1 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
          cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ℓ) : ℝ) : ℂ) * I)) := by
    intro j _
    rw [Dcov_psi, ← tsum_mul_left]
    congr 1
    funext m
    exact term_identity_D η δ₀ T hny a ℓ j m R
  rw [Finset.sum_congr rfl h1]
  have hsum : ∀ j ∈ Ia δ₀ T a, Summable (fun m : ℤ =>
      (((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((m * T.Lx * R.2 : ℝ) : ℂ) * I) *
        (((window η (T.κ / δx δ₀ T * j - a) * Analysis.q1 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
          cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ℓ) : ℝ) : ℂ) * I))) := by
    intro j _
    have h := (summable_Dphi T j R).mul_left (((wa η δ₀ T a j : ℝ) : ℂ) *
      Complex.exp (-(2 * (π : ℂ) * I * (j : ℂ) * (ℓ : ℂ) / ((ny δ₀ T : ℕ) : ℂ))))
    refine h.congr (fun m => ?_)
    exact term_identity_D η δ₀ T hny a ℓ j m R
  rw [← Summable.tsum_finsetSum hsum, ← tsum_mul_left]
  congr 1
  funext m
  rw [← Finset.mul_sum]
  have hz : ∀ j ∉ Ia δ₀ T a,
      ((window η (T.κ / δx δ₀ T * j - a) * Analysis.q1 (T.κ * j - (R.1 - m * T.Lx)) : ℝ) : ℂ) *
        cexp ((j : ℂ) * ((T.κ * (R.2 - yl δ₀ T ℓ) : ℝ) : ℂ) * I) = 0 := by
    intro j hj
    rw [mem_Ia, not_lt] at hj
    have h1' : 1 ≤ |T.κ / δx δ₀ T * j - a| := by
      have e : T.κ / δx δ₀ T * j - a = (T.κ * j - xa δ₀ T a) / δx δ₀ T := by
        unfold xa; field_simp
      rw [e, abs_div, abs_of_pos hδx, le_div_iff₀ hδx, one_mul]
      exact hj
    rw [window_eq_zero hη h1']
    simp
  rw [tsum_eq_sum hz, mul_assoc]

/-- The last step of (i) and (ii): from the integer-`n` bound with `e^{−p²/4}` to the statement's
form with the real power `(1 + D)^{−k}` and `e^{−p²/8}`. -/
theorem bound_to_statement {X : ℂ} {C D p k : ℝ} (hD : 0 ≤ D)
    (h : ‖X‖ ≤ C * ((1 + D) ^ ⌈k⌉₊)⁻¹ * Real.exp (-(p ^ 2 / 4))) :
    ‖X‖ ≤ max C 0 * (1 + D) ^ (-k) * Real.exp (-(p ^ 2) / 8) := by
  have h1 : ((1 + D) ^ ⌈k⌉₊)⁻¹ ≤ (1 + D) ^ (-k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [Nat.le_ceil k])
  have h2 : Real.exp (-(p ^ 2 / 4)) ≤ Real.exp (-(p ^ 2) / 8) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg p]
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc ‖X‖ ≤ C * ((1 + D) ^ ⌈k⌉₊)⁻¹ * Real.exp (-(p ^ 2 / 4)) := h
    _ ≤ max C 0 * ((1 + D) ^ ⌈k⌉₊)⁻¹ * Real.exp (-(p ^ 2 / 4)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + D) ^ (-k) * Real.exp (-(p ^ 2) / 8) := by
        apply mul_le_mul _ h2 (Real.exp_pos _).le
          (mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _))
        exact mul_le_mul_of_nonneg_left h1 hC0

/-! ## Helpers for Lemma 3.5(iii): the slot sums -/

theorem pdist_neg (P u : ℝ) : pdist P (-u) = pdist P u := by
  unfold pdist
  rw [← QuotientAddGroup.norm_mk, ← QuotientAddGroup.norm_mk, QuotientAddGroup.mk_neg, norm_neg]

/-- Proposition 3.4(i)'s lower bound, in the form used here: `δ_y ≥ π/(3δ₀)`. -/
theorem δy_lower {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) :
    π / (3 * δ₀) ≤ δy δ₀ T := by
  have hπ := Real.pi_pos
  obtain ⟨_, hδm, hδp, hδκ⟩ := consistency_ii hδ₀ hT
  unfold δminus at hδm
  unfold δplus at hδp
  have hκ := T.κ_pos
  have hny := two_le_ny hδ₀ hT
  have hnyR : (0 : ℝ) < (ny δ₀ T : ℝ) := by
    have : 0 < ny δ₀ T := by omega
    exact_mod_cast this
  have hceil : ((ny δ₀ T : ℕ) : ℝ) < 2 * δx δ₀ T / T.κ + 1 := by
    have h := ny_spec δ₀ T
    have h2 := Int.ceil_lt_add_one (2 * δx δ₀ T / T.κ)
    have h3 : ((ny δ₀ T : ℕ) : ℝ) = ((⌈2 * δx δ₀ T / T.κ⌉ : ℤ) : ℝ) := by exact_mod_cast h
    rw [h3]; exact h2
  have h3 : ((ny δ₀ T : ℕ) : ℝ) ≤ 3 * δx δ₀ T / T.κ := by
    have e : 3 * δx δ₀ T / T.κ = 2 * δx δ₀ T / T.κ + δx δ₀ T / T.κ := by ring
    linarith
  have hLy := Torus.κ_mul_Ly T
  unfold δy
  rw [le_div_iff₀ hnyR]
  calc π / (3 * δ₀) * (ny δ₀ T : ℝ) ≤ π / (3 * δ₀) * (3 * δx δ₀ T / T.κ) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = π * δx δ₀ T / (δ₀ * T.κ) := by field_simp
    _ ≤ T.Ly := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hδp hπ.le]

theorem Lx_eq_nx {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) :
    T.Lx = (nx δ₀ T : ℝ) * δx δ₀ T := by
  obtain ⟨h4, _, _, _⟩ := consistency_ii hδ₀ hT
  have : (0 : ℝ) < (nx δ₀ T : ℝ) := by exact_mod_cast (by omega : 0 < nx δ₀ T)
  unfold δx; field_simp

theorem Ly_eq_ny {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) :
    T.Ly = (ny δ₀ T : ℝ) * δy δ₀ T := by
  have h2 := two_le_ny hδ₀ hT
  have : (0 : ℝ) < (ny δ₀ T : ℝ) := by exact_mod_cast (by omega : 0 < ny δ₀ T)
  unfold δy; field_simp

/-- The majorants and constants of the proof of (iii); they depend only on `δ₀`. -/
def FX (δ₀ u : ℝ) : ℝ := Real.exp (-((max (u - 2 * δ₀) 0) ^ 2 / 8))

def FY (u : ℝ) : ℝ := ((1 + u) ^ 2)⁻¹

def KX (δ₀ : ℝ) : ℝ := ∑' u : ℤ, FX δ₀ (|(u : ℝ)| * (δ₀ / 3))

def KY (δ₀ : ℝ) : ℝ := ∑' u : ℤ, FY (|(u : ℝ)| * (π / (6 * δ₀)))

theorem FX_nonneg (δ₀ u : ℝ) : 0 ≤ FX δ₀ u := (Real.exp_pos _).le

theorem FY_nonneg (u : ℝ) : 0 ≤ FY u := by unfold FY; positivity

theorem FX_anti (δ₀ : ℝ) : AntitoneOn (FX δ₀) (Set.Ici 0) := by
  intro a ha b hb hab
  unfold FX
  apply Real.exp_le_exp.mpr
  have h1 : max (a - 2 * δ₀) 0 ≤ max (b - 2 * δ₀) 0 := max_le_max (by linarith) le_rfl
  have h2 : (max (a - 2 * δ₀) 0) ^ 2 ≤ (max (b - 2 * δ₀) 0) ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) h1 2
  linarith

theorem FY_anti : AntitoneOn FY (Set.Ici 0) := by
  intro a ha b hb hab
  unfold FY
  rw [Set.mem_Ici] at ha hb
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)

theorem KX_nonneg (δ₀ : ℝ) : 0 ≤ KX δ₀ := tsum_nonneg (fun _ => FX_nonneg _ _)

theorem KY_nonneg (δ₀ : ℝ) : 0 ≤ KY δ₀ := tsum_nonneg (fun _ => FY_nonneg _)

/-- The sum over all slots of `(1 + Δ_y)^{−2} e^{−(Δ_x − δ_x)₊²/8}` is at most `KX δ₀ · KY δ₀`. -/
theorem sum_w_le {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (R : ℝ × ℝ) :
    ∑ s : Slot δ₀ T, ((1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ 2)⁻¹ *
        Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2 / 8)) ≤
      KX δ₀ * KY δ₀ := by
  have hπ := Real.pi_pos
  obtain ⟨h4, hδm, hδp, _⟩ := consistency_ii hδ₀ hT
  unfold δminus at hδm
  unfold δplus at hδp
  have hny := two_le_ny hδ₀ hT
  rw [Fintype.sum_prod_type]
  have e : ∀ a : Fin (nx δ₀ T), ∑ ℓ : Fin (ny δ₀ T),
      ((1 + pdist T.Ly (R.2 - yl δ₀ T ((((a, ℓ) : Slot δ₀ T).2 : ℕ) : ℤ))) ^ 2)⁻¹ *
        Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((((a, ℓ) : Slot δ₀ T).1 : ℕ) : ℤ)) -
          δx δ₀ T) 0) ^ 2 / 8)) =
      Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((a : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2 / 8)) *
        ∑ ℓ : Fin (ny δ₀ T), ((1 + pdist T.Ly (R.2 - yl δ₀ T ((ℓ : ℕ) : ℤ))) ^ 2)⁻¹ := by
    intro a
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ _
    ring
  rw [Finset.sum_congr rfl (fun a _ => e a), ← Finset.sum_mul]
  have hX : ∑ a : Fin (nx δ₀ T),
      Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((a : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2 / 8)) ≤ KX δ₀ := by
    have hc : 0 < δ₀ / 3 := by positivity
    have hcδ : δ₀ / 3 ≤ δx δ₀ T / 2 := by linarith
    have hsum : Summable (fun u : ℤ => FX δ₀ (|(u : ℝ)| * (δ₀ / 3))) :=
      Analysis.summable_gauss_tail hc (2 * δ₀) (by positivity)
    have hlift := Analysis.fin_sum_infDist_le (n := nx δ₀ T) (by omega) hc hcδ (FX_nonneg δ₀)
      (FX_anti δ₀) hsum R.1
    refine le_trans (Finset.sum_le_sum (fun a _ => ?_)) hlift
    have hpd : pdist T.Lx (R.1 - xa δ₀ T ((a : ℕ) : ℤ)) =
        Metric.infDist (R.1 - ((a : ℕ) : ℝ) * δx δ₀ T)
          (AddSubgroup.zmultiples ((nx δ₀ T : ℝ) * δx δ₀ T) : Set ℝ) := by
      unfold pdist xa
      rw [← Lx_eq_nx hδ₀ hT]
      push_cast
      rfl
    rw [hpd]
    unfold FX
    apply Real.exp_le_exp.mpr
    set D := Metric.infDist (R.1 - ((a : ℕ) : ℝ) * δx δ₀ T)
      (AddSubgroup.zmultiples ((nx δ₀ T : ℝ) * δx δ₀ T) : Set ℝ)
    have h1 : max (D - 2 * δ₀) 0 ≤ max (D - δx δ₀ T) 0 := max_le_max (by linarith) le_rfl
    have h2 : (max (D - 2 * δ₀) 0) ^ 2 ≤ (max (D - δx δ₀ T) 0) ^ 2 :=
      pow_le_pow_left₀ (le_max_right _ _) h1 2
    linarith
  have hY : ∑ ℓ : Fin (ny δ₀ T), ((1 + pdist T.Ly (R.2 - yl δ₀ T ((ℓ : ℕ) : ℤ))) ^ 2)⁻¹ ≤ KY δ₀ := by
    have hc : 0 < π / (6 * δ₀) := by positivity
    have hcδ : π / (6 * δ₀) ≤ δy δ₀ T / 2 := by
      have := δy_lower hδ₀ hT
      have e : π / (6 * δ₀) = π / (3 * δ₀) / 2 := by field_simp; ring
      linarith
    have hsum : Summable (fun u : ℤ => FY (|(u : ℝ)| * (π / (6 * δ₀)))) :=
      Analysis.summable_inv_sq_int hc
    have hFY0 : ∀ u, 0 ≤ FY (max u 0) := fun u => FY_nonneg _
    have hlift := Analysis.fin_sum_infDist_le (n := ny δ₀ T) (F := fun u => FY (max u 0)) (by omega)
      hc hcδ hFY0
      (fun a ha b hb hab => by
        show FY (max b 0) ≤ FY (max a 0)
        rw [max_eq_left (Set.mem_Ici.mp ha), max_eq_left (Set.mem_Ici.mp hb)]
        exact FY_anti ha hb hab)
      (by
        refine hsum.congr (fun u => ?_)
        show FY (|(u : ℝ)| * (π / (6 * δ₀))) = FY (max (|(u : ℝ)| * (π / (6 * δ₀))) 0)
        rw [max_eq_left (by positivity)]) R.2
    refine le_trans (Finset.sum_le_sum (fun ℓ _ => ?_)) (le_trans hlift (le_of_eq ?_))
    · have hpd : pdist T.Ly (R.2 - yl δ₀ T ((ℓ : ℕ) : ℤ)) =
          Metric.infDist (R.2 - ((ℓ : ℕ) : ℝ) * δy δ₀ T)
            (AddSubgroup.zmultiples ((ny δ₀ T : ℝ) * δy δ₀ T) : Set ℝ) := by
        unfold pdist yl
        rw [← Ly_eq_ny hδ₀ hT]
        push_cast
        rfl
      rw [hpd, max_eq_left Metric.infDist_nonneg]
      rfl
    · apply tsum_congr
      intro u
      show FY (max (|(u : ℝ)| * (π / (6 * δ₀))) 0) = FY (|(u : ℝ)| * (π / (6 * δ₀)))
      rw [max_eq_left (by positivity)]
  have hS0 : 0 ≤ ∑ ℓ : Fin (ny δ₀ T), ((1 + pdist T.Ly (R.2 - yl δ₀ T ((ℓ : ℕ) : ℤ))) ^ 2)⁻¹ :=
    Finset.sum_nonneg (fun ℓ _ => by
      have : 0 ≤ pdist T.Ly (R.2 - yl δ₀ T ((ℓ : ℕ) : ℤ)) := Metric.infDist_nonneg
      positivity)
  exact mul_le_mul hX hY hS0 (KX_nonneg δ₀)

/-- (ii)'s integer-`n` bound for `Dz_s` (the analogue of `localization_core`). -/
theorem core_D {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (n : ℕ) :
    ∃ C : ℝ, ∀ T : Torus, T.Admissible δ₀ → ∀ (s : Slot δ₀ T) (R : ℝ × ℝ),
      ‖Dcov (frame η δ₀ T s) R‖ ≤ C * ((1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ n)⁻¹ *
        Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2 / 4)) := by
  obtain ⟨C, hC⟩ := images_bound hη hδ₀ n Analysis.contDiff_q1 Analysis.q1_bounds
  refine ⟨C, fun T hT s R => ?_⟩
  obtain ⟨_, hδm, _, _⟩ := consistency_ii hδ₀ hT
  unfold δminus at hδm
  have hny2 := two_le_ny hδ₀ hT
  rw [Dframe_repr hη δ₀ T (by omega) (by linarith) s R]
  exact hC T hT s R

/-- The tail estimate of (iii) for any family of slot values with the bound of (i)/(ii) at order
`k' + 2`. -/
theorem tail_bound {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (k' : ℕ) {k : ℝ}
    (hkk : k ≤ k') {C Kp : ℝ} (hC : 0 ≤ C) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ p : ℝ, 0 ≤ p → (1 + p) ^ k' * Real.exp (-(p ^ 2 / 8)) ≤ Kp)
    (R : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) (X : Slot δ₀ T → ℂ)
    (hX : ∀ s, ‖X s‖ ≤ C * ((1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ (k' + 2))⁻¹ *
        Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2 / 4))) :
    Real.sqrt (∑ s ∈ ballCompl δ₀ T R r, ‖X s‖ ^ 2) ≤
      C * Kp * (1 + 2 * δ₀) ^ k' * Real.sqrt (KX δ₀ * KY δ₀) * (1 + r) ^ (-k) := by
  obtain ⟨_, hδm, hδp, _⟩ := consistency_ii hδ₀ hT
  unfold δminus at hδm
  unfold δplus at hδp
  set A := C * Kp * (1 + 2 * δ₀) ^ k' with hA
  have hA0 : 0 ≤ A := by positivity
  have hpt : ∀ s ∈ ballCompl δ₀ T R r, ‖X s‖ ^ 2 ≤ A ^ 2 * (((1 + r) ^ k') ^ 2)⁻¹ *
      (((1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ 2)⁻¹ *
        Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2 / 8))) := by
    intro s hs
    set Δx := pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) with hΔx
    set Δy := pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) with hΔy
    set p := max (Δx - δx δ₀ T) 0 with hp
    have hΔx0 : 0 ≤ Δx := Metric.infDist_nonneg
    have hΔy0 : 0 ≤ Δy := Metric.infDist_nonneg
    have hp0 : 0 ≤ p := le_max_right _ _
    have hd : r < Δx + Δy := by
      have h1 : r < flatDist T (centre δ₀ T s) R := (Finset.mem_filter.mp hs).2
      have h2 : flatDist T (centre δ₀ T s) R = Real.sqrt (Δx ^ 2 + Δy ^ 2) := by
        unfold flatDist centre
        rw [show xa δ₀ T ((s.1 : ℕ) : ℤ) - R.1 = -(R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) by ring, pdist_neg,
          show yl δ₀ T ((s.2 : ℕ) : ℤ) - R.2 = -(R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) by ring, pdist_neg]
      have h3 : Real.sqrt (Δx ^ 2 + Δy ^ 2) ≤ Δx + Δy := by
        rw [Real.sqrt_le_left (by positivity)]; nlinarith
      linarith
    have hprod : 1 + r ≤ (1 + Δx) * (1 + Δy) := by nlinarith
    have hxp : 1 + Δx ≤ (1 + 2 * δ₀) * (1 + p) := by
      have h1 : Δx ≤ p + δx δ₀ T := by
        have := le_max_left (Δx - δx δ₀ T) 0
        linarith
      nlinarith
    have hE : Real.exp (-(p ^ 2 / 4)) ≤ Kp * ((1 + p) ^ k')⁻¹ * Real.exp (-(p ^ 2 / 8)) := by
      have h1 := hKp p hp0
      have hsplit : Real.exp (-(p ^ 2 / 4)) = Real.exp (-(p ^ 2 / 8)) * Real.exp (-(p ^ 2 / 8)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hpos : 0 < (1 + p) ^ k' := by positivity
      have h2 : Real.exp (-(p ^ 2 / 8)) ≤ Kp * ((1 + p) ^ k')⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        linarith [mul_comm ((1 + p) ^ k') (Real.exp (-(p ^ 2 / 8)))]
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    have hI1 : ((1 + p) ^ k')⁻¹ ≤ (1 + 2 * δ₀) ^ k' * ((1 + Δx) ^ k')⁻¹ := by
      have h1 : (1 + Δx) ^ k' ≤ (1 + 2 * δ₀) ^ k' * (1 + p) ^ k' := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hxp k'
      have h2 : ((1 + 2 * δ₀) ^ k' * (1 + p) ^ k')⁻¹ ≤ ((1 + Δx) ^ k')⁻¹ :=
        inv_anti₀ (by positivity) h1
      have h3 : ((1 + p) ^ k')⁻¹ = (1 + 2 * δ₀) ^ k' * ((1 + 2 * δ₀) ^ k' * (1 + p) ^ k')⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      rw [h3]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have hI2 : ((1 + Δx) ^ k')⁻¹ * ((1 + Δy) ^ k')⁻¹ ≤ ((1 + r) ^ k')⁻¹ := by
      rw [← mul_inv, ← mul_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hprod k')
    have hw0 : 0 ≤ ((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8)) := by positivity
    have hw1 : ((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8)) ≤ 1 := by
      have h1 : ((1 + Δy) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
      have h2 : Real.exp (-(p ^ 2 / 8)) ≤ 1 := by
        rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
      calc ((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8)) ≤ 1 * 1 :=
            mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
        _ = 1 := one_mul 1
    have hstep : ‖X s‖ ≤ A * ((1 + r) ^ k')⁻¹ * (((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8))) := by
      have hsplitY : ((1 + Δy) ^ (k' + 2))⁻¹ = ((1 + Δy) ^ k')⁻¹ * ((1 + Δy) ^ 2)⁻¹ := by
        rw [pow_add, mul_inv]
      calc ‖X s‖ ≤ C * ((1 + Δy) ^ (k' + 2))⁻¹ * Real.exp (-(p ^ 2 / 4)) := hX s
        _ ≤ C * ((1 + Δy) ^ (k' + 2))⁻¹ * (Kp * ((1 + p) ^ k')⁻¹ * Real.exp (-(p ^ 2 / 8))) :=
            mul_le_mul_of_nonneg_left hE (by positivity)
        _ = C * Kp * (((1 + p) ^ k')⁻¹ * ((1 + Δy) ^ k')⁻¹) *
              (((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8))) := by rw [hsplitY]; ring
        _ ≤ C * Kp * ((1 + 2 * δ₀) ^ k' * ((1 + Δx) ^ k')⁻¹ * ((1 + Δy) ^ k')⁻¹) *
              (((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8))) := by
            apply mul_le_mul_of_nonneg_right _ hw0
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hI1 (by positivity)
        _ = A * (((1 + Δx) ^ k')⁻¹ * ((1 + Δy) ^ k')⁻¹) *
              (((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8))) := by rw [hA]; ring
        _ ≤ A * ((1 + r) ^ k')⁻¹ * (((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8))) := by
            apply mul_le_mul_of_nonneg_right _ hw0
            exact mul_le_mul_of_nonneg_left hI2 hA0
    calc ‖X s‖ ^ 2 ≤ (A * ((1 + r) ^ k')⁻¹ * (((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8)))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hstep 2
      _ = A ^ 2 * (((1 + r) ^ k') ^ 2)⁻¹ * ((((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8))) *
            (((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8)))) := by ring
      _ ≤ A ^ 2 * (((1 + r) ^ k') ^ 2)⁻¹ * (((1 + Δy) ^ 2)⁻¹ * Real.exp (-(p ^ 2 / 8))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
  have hsum : ∑ s ∈ ballCompl δ₀ T R r, ‖X s‖ ^ 2 ≤
      A ^ 2 * (((1 + r) ^ k') ^ 2)⁻¹ * (KX δ₀ * KY δ₀) := by
    calc ∑ s ∈ ballCompl δ₀ T R r, ‖X s‖ ^ 2
        ≤ ∑ s ∈ ballCompl δ₀ T R r, A ^ 2 * (((1 + r) ^ k') ^ 2)⁻¹ *
            (((1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ 2)⁻¹ *
              Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2 / 8))) :=
          Finset.sum_le_sum hpt
      _ ≤ ∑ s : Slot δ₀ T, A ^ 2 * (((1 + r) ^ k') ^ 2)⁻¹ *
            (((1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ 2)⁻¹ *
              Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2 / 8))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro s _ _
          have : 0 ≤ pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) := Metric.infDist_nonneg
          positivity
      _ = A ^ 2 * (((1 + r) ^ k') ^ 2)⁻¹ * ∑ s : Slot δ₀ T,
            ((1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ 2)⁻¹ *
              Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2 / 8)) := by
          rw [Finset.mul_sum]
      _ ≤ A ^ 2 * (((1 + r) ^ k') ^ 2)⁻¹ * (KX δ₀ * KY δ₀) :=
          mul_le_mul_of_nonneg_left (sum_w_le hδ₀ hT R) (by positivity)
  have hK0 : 0 ≤ KX δ₀ * KY δ₀ := mul_nonneg (KX_nonneg δ₀) (KY_nonneg δ₀)
  have hrk : ((1 + r) ^ k')⁻¹ ≤ (1 + r) ^ (-k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc Real.sqrt (∑ s ∈ ballCompl δ₀ T R r, ‖X s‖ ^ 2)
      ≤ Real.sqrt (A ^ 2 * (((1 + r) ^ k') ^ 2)⁻¹ * (KX δ₀ * KY δ₀)) := Real.sqrt_le_sqrt hsum
    _ = A * ((1 + r) ^ k')⁻¹ * Real.sqrt (KX δ₀ * KY δ₀) := by
        rw [show A ^ 2 * (((1 + r) ^ k') ^ 2)⁻¹ * (KX δ₀ * KY δ₀) =
            (A * ((1 + r) ^ k')⁻¹) ^ 2 * (KX δ₀ * KY δ₀) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    _ ≤ A * (1 + r) ^ (-k) * Real.sqrt (KX δ₀ * KY δ₀) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hrk hA0
    _ = C * Kp * (1 + 2 * δ₀) ^ k' * Real.sqrt (KX δ₀ * KY δ₀) * (1 + r) ^ (-k) := by rw [hA]; ring

/-! ## Lemma 3.5 (uniform localization) -/

/-- **Lemma 3.5(i).** For every `k ≥ 0` there is a constant `C_k`, depending only on `k`, `η` and
`δ₀`, such that for every admissible torus, every slot `s = (a, ℓ)` and every `R = (R_x, R_y) ∈ ℝ²`:
`|z_s(R)| ≤ C_k (1 + |R_y − y_ℓ|_{L_y})^{−k} exp(−(|R_x − x_a|_{L_x} − δ_x)₊²/8)`. -/
theorem localization_i {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {k : ℝ} (hk : 0 ≤ k) :
    ∃ C : ℝ, ∀ T : Torus, T.Admissible δ₀ → ∀ (s : Slot δ₀ T) (R : ℝ × ℝ),
      ‖frame η δ₀ T s R‖ ≤
        C * (1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ (-k) *
          Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2) / 8) := by
  obtain ⟨C, hC⟩ := localization_core hη hδ₀ ⌈k⌉₊
  refine ⟨max C 0, fun T hT s R => ?_⟩
  have h := hC T hT s R
  set D := pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) with hD
  set p := max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0 with hp
  have hD0 : 0 ≤ D := Metric.infDist_nonneg
  have h1 : ((1 + D) ^ ⌈k⌉₊)⁻¹ ≤ (1 + D) ^ (-k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [Nat.le_ceil k])
  have h2 : Real.exp (-(p ^ 2 / 4)) ≤ Real.exp (-(p ^ 2) / 8) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg p]
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc ‖frame η δ₀ T s R‖ ≤ C * ((1 + D) ^ ⌈k⌉₊)⁻¹ * Real.exp (-(p ^ 2 / 4)) := h
    _ ≤ max C 0 * ((1 + D) ^ ⌈k⌉₊)⁻¹ * Real.exp (-(p ^ 2 / 4)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + D) ^ (-k) * Real.exp (-(p ^ 2) / 8) := by
        apply mul_le_mul _ h2 (Real.exp_pos _).le
          (mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _))
        exact mul_le_mul_of_nonneg_left h1 hC0

/-- **Lemma 3.5(ii).** The same bound holds for `|(Dz_s)(R)|`. -/
theorem localization_ii {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {k : ℝ} (hk : 0 ≤ k) :
    ∃ C : ℝ, ∀ T : Torus, T.Admissible δ₀ → ∀ (s : Slot δ₀ T) (R : ℝ × ℝ),
      ‖Dcov (frame η δ₀ T s) R‖ ≤
        C * (1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ (-k) *
          Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2) / 8) := by
  obtain ⟨C, hC⟩ := images_bound hη hδ₀ ⌈k⌉₊ Analysis.contDiff_q1 Analysis.q1_bounds
  refine ⟨max C 0, fun T hT s R => ?_⟩
  obtain ⟨_, hδm, _, _⟩ := consistency_ii hδ₀ hT
  unfold δminus at hδm
  have hny2 := two_le_ny hδ₀ hT
  have h := hC T hT s R
  rw [← Dframe_repr hη δ₀ T (by omega) (by linarith) s R] at h
  exact bound_to_statement Metric.infDist_nonneg h

/-- **Lemma 3.5(iii)**, after Lemma 2.3(i)'s identity `(𝒜 e_R)_s = \overline{z_s(R)}` and
`(𝒜 e^D_R)_s = \overline{(Dz_s)(R)}`: `‖1_{𝒮∖B(r,R)} 𝒜 e_R‖ ≤ C_k (1 + r)^{−k}` and the same for
`e^D_R`, for every `r ≥ 0`, the norm being that of `ℓ²(𝒮)`. -/
theorem localization_iii {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {k : ℝ} (hk : 0 ≤ k) :
    ∃ C : ℝ, ∀ T : Torus, T.Admissible δ₀ → ∀ (R : ℝ × ℝ) (r : ℝ), 0 ≤ r →
      Real.sqrt (∑ s ∈ ballCompl δ₀ T R r, ‖frame η δ₀ T s R‖ ^ 2) ≤ C * (1 + r) ^ (-k) ∧
      Real.sqrt (∑ s ∈ ballCompl δ₀ T R r, ‖Dcov (frame η δ₀ T s) R‖ ^ 2) ≤
        C * (1 + r) ^ (-k) := by
  obtain ⟨C0, hC0⟩ := localization_core hη hδ₀ (⌈k⌉₊ + 2)
  obtain ⟨C1, hC1⟩ := core_D hη hδ₀ (⌈k⌉₊ + 2)
  obtain ⟨Kp, hKp0, hKp⟩ := Analysis.one_add_pow_mul_exp_le ⌈k⌉₊
  set Cm := max (max C0 C1) 0 with hCm
  have hCm0 : 0 ≤ Cm := le_max_right _ _
  have hC0m : C0 ≤ Cm := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC1m : C1 ≤ Cm := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨Cm * Kp * (1 + 2 * δ₀) ^ ⌈k⌉₊ * Real.sqrt (KX δ₀ * KY δ₀), fun T hT R r hr => ⟨?_, ?_⟩⟩
  · refine tail_bound hδ₀ hT ⌈k⌉₊ (Nat.le_ceil k) hCm0 hKp0 hKp R hr (fun s => frame η δ₀ T s R)
      (fun s => le_trans (hC0 T hT s R) ?_)
    have hD : 0 ≤ pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) := Metric.infDist_nonneg
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hC0m (by positivity)
  · refine tail_bound hδ₀ hT ⌈k⌉₊ (Nat.le_ceil k) hCm0 hKp0 hKp R hr
      (fun s => Dcov (frame η δ₀ T s) R) (fun s => le_trans (hC1 T hT s R) ?_)
    have hD : 0 ≤ pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) := Metric.infDist_nonneg
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hC1m (by positivity)

/-- **Lemma 3.5** as the paper states it, one constant `C_k` for (i)–(iii) ("we rename the larger
of the constants in (i)–(iii) `C_k`"). -/
theorem localization {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {k : ℝ} (hk : 0 ≤ k) :
    ∃ C : ℝ, ∀ T : Torus, T.Admissible δ₀ →
      (∀ (s : Slot δ₀ T) (R : ℝ × ℝ),
        ‖frame η δ₀ T s R‖ ≤
          C * (1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ (-k) *
            Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2) / 8) ∧
        ‖Dcov (frame η δ₀ T s) R‖ ≤
          C * (1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ))) ^ (-k) *
            Real.exp (-((max (pdist T.Lx (R.1 - xa δ₀ T ((s.1 : ℕ) : ℤ)) - δx δ₀ T) 0) ^ 2) / 8)) ∧
      (∀ (R : ℝ × ℝ) (r : ℝ), 0 ≤ r →
        Real.sqrt (∑ s ∈ ballCompl δ₀ T R r, ‖frame η δ₀ T s R‖ ^ 2) ≤ C * (1 + r) ^ (-k) ∧
        Real.sqrt (∑ s ∈ ballCompl δ₀ T R r, ‖Dcov (frame η δ₀ T s) R‖ ^ 2) ≤
          C * (1 + r) ^ (-k)) := by
  obtain ⟨C1, h1⟩ := localization_i hη hδ₀ hk
  obtain ⟨C2, h2⟩ := localization_ii hη hδ₀ hk
  obtain ⟨C3, h3⟩ := localization_iii hη hδ₀ hk
  set Cm := max (max C1 C2) (max C3 0) with hCm
  have hC1 : C1 ≤ Cm := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 ≤ Cm := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3 : C3 ≤ Cm := le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨Cm, fun T hT => ⟨fun s R => ⟨?_, ?_⟩, fun R r hr => ⟨?_, ?_⟩⟩⟩
  · have hD : 0 ≤ 1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) := by
      have : 0 ≤ pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) := Metric.infDist_nonneg
      linarith
    refine le_trans (h1 T hT s R) ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg hD _)
  · have hD : 0 ≤ 1 + pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) := by
      have : 0 ≤ pdist T.Ly (R.2 - yl δ₀ T ((s.2 : ℕ) : ℤ)) := Metric.infDist_nonneg
      linarith
    refine le_trans (h2 T hT s R) ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hD _)
  · exact le_trans (h3 T hT R r hr).1
      (mul_le_mul_of_nonneg_right hC3 (Real.rpow_nonneg (by linarith) _))
  · exact le_trans (h3 T hT R r hr).2
      (mul_le_mul_of_nonneg_right hC3 (Real.rpow_nonneg (by linarith) _))

end HRTorus.SlotFrame

#check @HRTorus.SlotFrame.localization_i
#check @HRTorus.SlotFrame.localization_ii
#check @HRTorus.SlotFrame.localization_iii
#check @HRTorus.SlotFrame.localization
#print HRTorus.SlotFrame.Torus
#print HRTorus.SlotFrame.phi
#print HRTorus.SlotFrame.psi
#print HRTorus.SlotFrame.Dcov
#print HRTorus.SlotFrame.pdist
#print HRTorus.SlotFrame.flatDist
#print HRTorus.SlotFrame.IsProfile
#print HRTorus.SlotFrame.etaStd
#print HRTorus.SlotFrame.window
#print HRTorus.SlotFrame.nx
#print HRTorus.SlotFrame.ny
#print HRTorus.SlotFrame.Ia
#print HRTorus.SlotFrame.frame
#print HRTorus.SlotFrame.ballCompl
#print axioms HRTorus.SlotFrame.frame
#print axioms HRTorus.SlotFrame.ballCompl
#print axioms HRTorus.SlotFrame.localization_i
