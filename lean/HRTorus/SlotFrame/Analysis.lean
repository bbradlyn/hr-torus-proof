import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.PSeries

/-!
# The one-dimensional analysis behind Lemma 3.5

Written by Claude Opus 5.5 (an AI model), 2026-10-23. Lemmas independent of the torus model: majorants over `ℤ`, the backward
difference with summation by parts and the iterated mean-value bound (Step 2 of the proof of
Lemma 3.5), the Gaussian derivative bounds and the Leibniz bound (Step 3), the periodic distance
(`Metric.infDist` to `Pℤ`) and the Jordan bound (Step 4). Proof devices, not statements of the paper.
-/

open Real Complex
open scoped ContDiff

noncomputable section

namespace HRTorus.SlotFrame.Analysis

/-! ## 1. Majorants over `ℤ` -/

theorem summable_geom_int {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun m : ℤ => r ^ m.natAbs) := by
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · simpa using summable_geometric_of_lt_one h0 h1
  · simpa using summable_geometric_of_lt_one h0 h1

theorem exp_neg_sq_half_le (t : ℝ) :
    Real.exp (-(t ^ 2) / 2) ≤ Real.exp 2 * Real.exp (-(2 * |t|)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_abs t, sq_nonneg (|t| - 2)]

theorem exp_neg_two_mul_abs_le {L : ℝ} (hL : 0 < L) (c : ℝ) (m : ℤ) :
    Real.exp (-(2 * |c - m * L|)) ≤ Real.exp (2 * |c|) * Real.exp (-(2 * L)) ^ m.natAbs := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : |(m : ℝ) * L| - |c| ≤ |(m : ℝ) * L - c| := abs_sub_abs_le_abs_sub _ _
  have h2 : |(m : ℝ) * L| = |(m : ℝ)| * L := by rw [abs_mul, abs_of_pos hL]
  have h3 : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [abs_sub_comm] at h1
  rw [h3]
  nlinarith [abs_nonneg (m : ℝ)]

theorem summable_gauss_int {L : ℝ} (hL : 0 < L) (c : ℝ) :
    Summable (fun m : ℤ => Real.exp (-((c - m * L) ^ 2) / 2)) := by
  have hr0 : 0 ≤ Real.exp (-(2 * L)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(2 * L)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) (fun m => ?_)
    ((summable_geom_int hr0 hr1).mul_left (Real.exp 2 * Real.exp (2 * |c|)))
  calc Real.exp (-((c - m * L) ^ 2) / 2)
      ≤ Real.exp 2 * Real.exp (-(2 * |c - m * L|)) := exp_neg_sq_half_le _
    _ ≤ Real.exp 2 * (Real.exp (2 * |c|) * Real.exp (-(2 * L)) ^ m.natAbs) := by
        gcongr
        exact exp_neg_two_mul_abs_le hL c m
    _ = Real.exp 2 * Real.exp (2 * |c|) * Real.exp (-(2 * L)) ^ m.natAbs := by ring

/-! ## 2. The backward difference and summation by parts (Step 2) -/

/-- The backward difference `(𝔡g)(v) := g(v) − g(v − 1)`. -/
def bd (g : ℝ → ℝ) : ℝ → ℝ := fun v => g v - g (v - 1)

theorem bd_support {g : ℝ → ℝ} {A B : ℝ} (hg : ∀ v, v < A ∨ B < v → g v = 0) :
    ∀ v, v < A ∨ B + 1 < v → bd g v = 0 := by
  intro v hv
  unfold bd
  rcases hv with hv | hv
  · rw [hg v (Or.inl hv), hg (v - 1) (Or.inl (by linarith))]; ring
  · rw [hg v (Or.inr (by linarith)), hg (v - 1) (Or.inr (by linarith))]; ring

theorem bd_iter_support (k : ℕ) : ∀ (g : ℝ → ℝ) (A B : ℝ), (∀ v, v < A ∨ B < v → g v = 0) →
    ∀ v, v < A ∨ B + k < v → (bd^[k] g) v = 0 := by
  induction k with
  | zero => intro g A B hg v hv; simpa using hg v (by simpa using hv)
  | succ k ih =>
    intro g A B hg v hv
    rw [Function.iterate_succ_apply]
    refine ih (bd g) A (B + 1) (bd_support hg) v ?_
    push_cast at hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr (by linarith)

theorem contDiff_bd {n : WithTop ℕ∞} {g : ℝ → ℝ} (hg : ContDiff ℝ n g) : ContDiff ℝ n (bd g) := by
  unfold bd
  exact hg.sub (hg.comp (contDiff_id.sub contDiff_const))

theorem iteratedDeriv_bd {n : ℕ} {g : ℝ → ℝ} (hg : ContDiff ℝ n g) :
    iteratedDeriv n (bd g) = bd (iteratedDeriv n g) := by
  funext v
  have hsh : ContDiff ℝ n (fun y => g (y - 1)) := hg.comp (contDiff_id.sub contDiff_const)
  have e : bd g = g - (fun y => g (y - 1)) := rfl
  rw [e, iteratedDeriv_sub hg.contDiffAt hsh.contDiffAt, iteratedDeriv_comp_sub_const]
  rfl

/-- The iterated mean-value bound: `|𝔡^k g| ≤ sup |g^{(k)}|`. -/
theorem abs_bd_iter_le {M : ℝ} (k : ℕ) : ∀ (g : ℝ → ℝ), ContDiff ℝ k g →
    (∀ v, |iteratedDeriv k g v| ≤ M) → ∀ x, |(bd^[k] g) x| ≤ M := by
  induction k with
  | zero => intro g _ h x; simpa using h x
  | succ k ih =>
    intro g hg h x
    rw [Function.iterate_succ_apply]
    have hgk : ContDiff ℝ k g := hg.of_le (by exact_mod_cast Nat.le_succ k)
    refine ih (bd g) (contDiff_bd hgk) (fun v => ?_) x
    rw [iteratedDeriv_bd hgk]
    unfold bd
    have hdiff : Differentiable ℝ (iteratedDeriv k g) :=
      hg.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
    have hbound : ∀ y ∈ (Set.univ : Set ℝ), ‖deriv (iteratedDeriv k g) y‖ ≤ M := by
      intro y _
      rw [← iteratedDeriv_succ]
      exact h y
    have := Convex.norm_image_sub_le_of_norm_deriv_le (fun y _ => hdiff y) hbound convex_univ
      (Set.mem_univ (v - 1)) (Set.mem_univ v)
    simpa [Real.norm_eq_abs] using this

theorem summable_of_support {f : ℤ → ℂ} {A B : ℝ} (hf : ∀ j : ℤ, ((j : ℝ) < A ∨ B < j) → f j = 0) :
    Summable f := by
  refine summable_of_ne_finset_zero (s := Finset.Icc ⌈A⌉ ⌊B⌋) (fun j hj => hf j ?_)
  simp only [Finset.mem_Icc, not_and_or, not_le] at hj
  rcases hj with hj | hj
  · exact Or.inl (Int.lt_ceil.mp hj)
  · exact Or.inr (Int.floor_lt.mp hj)

theorem sum_by_parts {g : ℝ → ℝ} {A B : ℝ} (hg : ∀ v, v < A ∨ B < v → g v = 0) (ξ : ℝ) :
    (1 - cexp (ξ * I)) * ∑' j : ℤ, (g j : ℂ) * cexp (j * ξ * I) =
      ∑' j : ℤ, (bd g j : ℂ) * cexp (j * ξ * I) := by
  have hF : Summable (fun j : ℤ => (g j : ℂ) * cexp (j * ξ * I)) :=
    summable_of_support (A := A) (B := B) (fun j hj => by rw [hg j hj]; simp)
  have hG : Summable (fun j : ℤ => (g ((j : ℝ) - 1) : ℂ) * cexp (j * ξ * I)) := by
    refine summable_of_support (A := A + 1) (B := B + 1) (fun j hj => ?_)
    have h' : (j : ℝ) - 1 < A ∨ B < (j : ℝ) - 1 := by
      rcases hj with hj | hj
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rw [hg _ h']
    simp
  have hshift : ∑' j : ℤ, cexp (ξ * I) * ((g j : ℂ) * cexp (j * ξ * I)) =
      ∑' j : ℤ, (g ((j : ℝ) - 1) : ℂ) * cexp (j * ξ * I) := by
    conv_rhs => rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
    congr 1
    funext j
    simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one, add_sub_cancel_right]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  rw [sub_mul, one_mul, ← tsum_mul_left, hshift, ← hF.tsum_sub hG]
  congr 1
  funext j
  simp only [bd]
  push_cast
  ring

theorem sum_by_parts_iter (k : ℕ) : ∀ (g : ℝ → ℝ) (A B : ℝ), (∀ v, v < A ∨ B < v → g v = 0) →
    ∀ ξ : ℝ, (1 - cexp (ξ * I)) ^ k * ∑' j : ℤ, (g j : ℂ) * cexp (j * ξ * I) =
      ∑' j : ℤ, ((bd^[k] g) j : ℂ) * cexp (j * ξ * I) := by
  induction k with
  | zero => intro g A B _ ξ; simp
  | succ k ih =>
    intro g A B hg ξ
    rw [pow_succ, mul_assoc, sum_by_parts hg ξ, ih (bd g) A (B + 1) (bd_support hg) ξ,
      Function.iterate_succ_apply]

/-- **The lattice-sum bound** (Steps 2 of the proof of Lemma 3.5): for `g ∈ C^k` vanishing off
`[A, B]` with `|g^{(k)}| ≤ M`, `|(1 − e^{iξ})^k Σ_j g(j) e^{ijξ}| ≤ (B − A + k + 1) M`. -/
theorem lattice_sum_bound (k : ℕ) {g : ℝ → ℝ} (hg : ContDiff ℝ k g) {A B : ℝ} (hAB : A ≤ B)
    (hsupp : ∀ v, v < A ∨ B < v → g v = 0) {M : ℝ} (hM : ∀ v, |iteratedDeriv k g v| ≤ M)
    (ξ : ℝ) :
    ‖(1 - cexp (ξ * I)) ^ k * ∑' j : ℤ, (g j : ℂ) * cexp (j * ξ * I)‖ ≤ (B - A + k + 1) * M := by
  rw [sum_by_parts_iter k g A B hsupp ξ]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hh : ∀ x, |(bd^[k] g) x| ≤ M := abs_bd_iter_le k g hg hM
  have hs : ∀ v, v < A ∨ B + k < v → (bd^[k] g) v = 0 := bd_iter_support k g A B hsupp
  set s : Finset ℤ := Finset.Icc ⌈A⌉ ⌊B + k⌋ with hs_def
  have hzero : ∀ j ∉ s, ((bd^[k] g) j : ℂ) * cexp (j * ξ * I) = 0 := by
    intro j hj
    simp only [hs_def, Finset.mem_Icc, not_and_or, not_le] at hj
    have h' : (j : ℝ) < A ∨ B + k < (j : ℝ) := by
      rcases hj with hj | hj
      · exact Or.inl (Int.lt_ceil.mp hj)
      · exact Or.inr (Int.floor_lt.mp hj)
    rw [hs j h']
    simp
  rw [tsum_eq_sum hzero]
  calc ‖∑ j ∈ s, ((bd^[k] g) j : ℂ) * cexp (j * ξ * I)‖
      ≤ ∑ j ∈ s, ‖((bd^[k] g) j : ℂ) * cexp (j * ξ * I)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ s, M := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, show (j : ℂ) * ξ * I = ((j * ξ : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact hh j
    _ = (s.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B - A + k + 1) * M := by
        apply mul_le_mul_of_nonneg_right _ hM0
        rw [hs_def, Int.card_Icc]
        have hf : (⌊B + k⌋ : ℝ) ≤ B + k := Int.floor_le _
        have hc : A ≤ (⌈A⌉ : ℝ) := Int.le_ceil _
        rcases le_or_gt 0 (⌊B + (k : ℝ)⌋ + 1 - ⌈A⌉) with hz | hz
        · have : (((⌊B + (k : ℝ)⌋ + 1 - ⌈A⌉).toNat : ℕ) : ℝ) = ((⌊B + (k : ℝ)⌋ + 1 - ⌈A⌉ : ℤ) : ℝ) := by
            rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]
          rw [this]
          push_cast
          linarith
        · rw [Int.toNat_of_nonpos hz.le]
          push_cast
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith

/-! ## 3. Gaussian derivative bounds (Step 3's `μ_n`) -/

theorem abs_pow_le_one_add (u : ℝ) (i : ℕ) : |u| ^ i ≤ 1 + (u ^ 2) ^ i := by
  rcases le_or_gt |u| 1 with h | h
  · have h1 : |u| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg u) h
    have h2 : 0 ≤ (u ^ 2) ^ i := by positivity
    linarith
  · have h1 : |u| ^ i ≤ (|u| ^ 2) ^ i := by
      apply pow_le_pow_left₀ (abs_nonneg u)
      nlinarith
    rw [sq_abs] at h1
    linarith

theorem abs_pow_mul_exp_le (u : ℝ) (i : ℕ) :
    |u| ^ i * Real.exp (-(u ^ 2 / 4)) ≤ 1 + 4 ^ i * (i.factorial : ℝ) := by
  have hx : 0 ≤ u ^ 2 / 4 := by positivity
  have h1 := Real.pow_div_factorial_le_exp (u ^ 2 / 4) hx i
  have hfac : (0 : ℝ) < i.factorial := by exact_mod_cast Nat.factorial_pos i
  have h1' : (u ^ 2 / 4) ^ i ≤ Real.exp (u ^ 2 / 4) * i.factorial := (div_le_iff₀ hfac).mp h1
  have h2 : (u ^ 2) ^ i ≤ 4 ^ i * (i.factorial : ℝ) * Real.exp (u ^ 2 / 4) := by
    have e : (u ^ 2) ^ i = 4 ^ i * (u ^ 2 / 4) ^ i := by
      rw [div_pow]; field_simp
    rw [e]
    have h4 : (0 : ℝ) ≤ 4 ^ i := by positivity
    calc 4 ^ i * (u ^ 2 / 4) ^ i ≤ 4 ^ i * (Real.exp (u ^ 2 / 4) * i.factorial) :=
          mul_le_mul_of_nonneg_left h1' h4
      _ = 4 ^ i * (i.factorial : ℝ) * Real.exp (u ^ 2 / 4) := by ring
  have hE0 : 0 < Real.exp (-(u ^ 2 / 4)) := Real.exp_pos _
  have hE1 : Real.exp (-(u ^ 2 / 4)) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (u ^ 2 / 4) * Real.exp (-(u ^ 2 / 4)) = 1 := by
    rw [← Real.exp_add]; simp
  calc |u| ^ i * Real.exp (-(u ^ 2 / 4)) ≤ (1 + (u ^ 2) ^ i) * Real.exp (-(u ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_right (abs_pow_le_one_add u i) hE0.le
    _ = Real.exp (-(u ^ 2 / 4)) + (u ^ 2) ^ i * Real.exp (-(u ^ 2 / 4)) := by ring
    _ ≤ 1 + 4 ^ i * (i.factorial : ℝ) * Real.exp (u ^ 2 / 4) * Real.exp (-(u ^ 2 / 4)) :=
        add_le_add hE1 (mul_le_mul_of_nonneg_right h2 hE0.le)
    _ = 1 + 4 ^ i * (i.factorial : ℝ) := by rw [mul_assoc _ (Real.exp _), he, mul_one]

theorem poly_mul_exp_bound (p : Polynomial ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, |Polynomial.aeval u p| * Real.exp (-(u ^ 2 / 4)) ≤ C := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| * (1 + 4 ^ i * (i.factorial : ℝ)),
    Finset.sum_nonneg (fun i _ => by positivity), fun u => ?_⟩
  have hE : 0 ≤ Real.exp (-(u ^ 2 / 4)) := (Real.exp_pos _).le
  rw [Polynomial.aeval_eq_sum_range]
  calc |∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • u ^ i| * Real.exp (-(u ^ 2 / 4))
      ≤ (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i • u ^ i|) * Real.exp (-(u ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hE
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| * (|u| ^ i * Real.exp (-(u ^ 2 / 4))) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [zsmul_eq_mul, abs_mul, abs_pow]
        ring
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| * (1 + 4 ^ i * (i.factorial : ℝ)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (abs_pow_mul_exp_le u i) (abs_nonneg _))

/-- The Gaussian `q₀(y) = e^{−y²/2}`. -/
def q0 (y : ℝ) : ℝ := Real.exp (-(y ^ 2 / 2))

theorem contDiff_q0 : ContDiff ℝ ∞ q0 := by
  unfold q0; fun_prop

/-- `μ_n := sup_u e^{u²/4} |q₀^{(n)}(u)| < ∞` (Step 3), from the Hermite formula. -/
theorem q0_iteratedDeriv_bound (n : ℕ) : ∃ μ : ℝ, 0 ≤ μ ∧ ∀ u : ℝ,
    |iteratedDeriv n q0 u| ≤ μ * Real.exp (-(u ^ 2 / 4)) := by
  obtain ⟨C, hC0, hC⟩ := poly_mul_exp_bound (Polynomial.hermite n)
  refine ⟨C, hC0, fun u => ?_⟩
  have hq : q0 = fun y : ℝ => Real.exp (-(y ^ 2 / 2)) := rfl
  rw [hq, iteratedDeriv_eq_iterate, Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]
  have hsplit : Real.exp (-(u ^ 2 / 2)) = Real.exp (-(u ^ 2 / 4)) * Real.exp (-(u ^ 2 / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (Real.exp_pos _), hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC u) (Real.exp_pos _).le

/-- `q₁(y) = y e^{−y²/2}`, the Gaussian of `Dφ_n` (Lemma 2.2(iii)). -/
def q1 (y : ℝ) : ℝ := y * Real.exp (-(y ^ 2 / 2))

theorem contDiff_q1 : ContDiff ℝ ∞ q1 := by
  unfold q1; fun_prop

theorem hasDerivAt_q0 (y : ℝ) : HasDerivAt q0 (-q1 y) y := by
  have hin : HasDerivAt (fun x : ℝ => -(x ^ 2 / 2)) (-y) y := by
    have h := ((hasDerivAt_pow 2 y).div_const 2).neg
    convert h using 1
    norm_num
  have h := hin.exp
  unfold q0 q1
  convert h using 1
  ring

theorem deriv_q0 : deriv q0 = -q1 := by
  funext y; exact (hasDerivAt_q0 y).deriv

theorem q0_bounds : ∀ i : ℕ, ∃ μ : ℝ, 0 ≤ μ ∧ ∀ u : ℝ,
    |iteratedDeriv i q0 u| ≤ μ * Real.exp (-(u ^ 2 / 4)) := q0_iteratedDeriv_bound

theorem q1_bounds : ∀ i : ℕ, ∃ μ : ℝ, 0 ≤ μ ∧ ∀ u : ℝ,
    |iteratedDeriv i q1 u| ≤ μ * Real.exp (-(u ^ 2 / 4)) := by
  intro i
  obtain ⟨μ, hμ0, hμ⟩ := q0_iteratedDeriv_bound (i + 1)
  refine ⟨μ, hμ0, fun u => ?_⟩
  have e : iteratedDeriv (i + 1) q0 u = -iteratedDeriv i q1 u := by
    rw [iteratedDeriv_succ', deriv_q0, iteratedDeriv_neg]
  have h := hμ u
  rw [e, abs_neg] at h
  exact h

/-! ## 4. Affine reparametrization and the Leibniz bound (Step 3) -/

theorem iteratedDeriv_comp_affine {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ n f) (α a v : ℝ) :
    iteratedDeriv n (fun v => f (α * v - a)) v = α ^ n * iteratedDeriv n f (α * v - a) := by
  have hf' : ContDiff ℝ n (fun y => f (y - a)) := hf.comp (contDiff_id.sub contDiff_const)
  have h := iteratedDeriv_comp_const_mul hf' α
  have h2 := iteratedDeriv_comp_sub_const n f a
  calc iteratedDeriv n (fun v => f (α * v - a)) v
      = α ^ n * iteratedDeriv n (fun y => f (y - a)) (α * v) := congrFun h v
    _ = α ^ n * iteratedDeriv n f (α * v - a) := by rw [h2]

theorem leibniz_affine_bound (k : ℕ) {f₁ f₂ : ℝ → ℝ} (h₁ : ContDiff ℝ ∞ f₁) (h₂ : ContDiff ℝ ∞ f₂)
    (α κ a c v : ℝ) :
    |iteratedDeriv k (fun v => f₁ (α * v - a) * f₂ (κ * v - c)) v| ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (|α| ^ i * |iteratedDeriv i f₁ (α * v - a)|) *
          (|κ| ^ (k - i) * |iteratedDeriv (k - i) f₂ (κ * v - c)|) := by
  have hF : ContDiff ℝ k (fun v => f₁ (α * v - a)) :=
    (contDiff_infty.mp h₁ k).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hG : ContDiff ℝ k (fun v => f₂ (κ * v - c)) :=
    (contDiff_infty.mp h₂ k).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  calc |iteratedDeriv k (fun v => f₁ (α * v - a) * f₂ (κ * v - c)) v|
      = ‖iteratedFDeriv ℝ k (fun y => (fun v => f₁ (α * v - a)) y * (fun v => f₂ (κ * v - c)) y) v‖ := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun v => f₁ (α * v - a)) v‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun v => f₂ (κ * v - c)) v‖ :=
        norm_iteratedFDeriv_mul_le hF hG v le_rfl
    _ = _ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          iteratedDeriv_comp_affine (contDiff_infty.mp h₁ i),
          iteratedDeriv_comp_affine (contDiff_infty.mp h₂ (k - i)),
          Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow]

/-! ## 5. The periodic distance `|u|_P = infDist(u, Pℤ)` -/

theorem infDist_zmultiples_eq (P u : ℝ) :
    Metric.infDist u (AddSubgroup.zmultiples P : Set ℝ) = |u - round (P⁻¹ * u) * P| :=
  (QuotientAddGroup.norm_mk (S := AddSubgroup.zmultiples P) u).symm.trans (AddCircle.norm_eq P)

theorem infDist_zmultiples_le_half {P : ℝ} (hP : 0 < P) (u : ℝ) :
    Metric.infDist u (AddSubgroup.zmultiples P : Set ℝ) ≤ P / 2 := by
  have h := AddCircle.norm_le_half_period P (x := (u : AddCircle P)) hP.ne'
  rw [abs_of_pos hP] at h
  rw [← QuotientAddGroup.norm_mk]
  exact h

theorem infDist_zmultiples_le (P u : ℝ) (m : ℤ) :
    Metric.infDist u (AddSubgroup.zmultiples P : Set ℝ) ≤ |u - m * P| := by
  have hmem : (m : ℝ) * P ∈ (AddSubgroup.zmultiples P : Set ℝ) := by
    rw [SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff]
    exact ⟨m, by rw [zsmul_eq_mul]⟩
  calc _ ≤ dist u ((m : ℝ) * P) := Metric.infDist_le_dist_of_mem hmem
    _ = |u - m * P| := Real.dist_eq _ _

theorem infDist_zmultiples_nonneg (P u : ℝ) : 0 ≤ Metric.infDist u (AddSubgroup.zmultiples P : Set ℝ) :=
  Metric.infDist_nonneg

theorem infDist_zmultiples_mul {c : ℝ} (hc : 0 < c) (P u : ℝ) :
    Metric.infDist (c * u) (AddSubgroup.zmultiples (c * P) : Set ℝ) =
      c * Metric.infDist u (AddSubgroup.zmultiples P : Set ℝ) := by
  rw [← QuotientAddGroup.norm_mk, ← QuotientAddGroup.norm_mk]
  have h := AddCircle.norm_coe_mul P u c
  rw [abs_of_pos hc] at h
  exact h

/-! ## 6. The Jordan bound (Step 4) -/

theorem jordan_infDist (ξ : ℝ) :
    2 / π * Metric.infDist ξ (AddSubgroup.zmultiples (2 * π) : Set ℝ) ≤ ‖1 - cexp (ξ * I)‖ := by
  have hπ : 0 < π := Real.pi_pos
  have hm := infDist_zmultiples_eq (2 * π) ξ
  set m : ℤ := round ((2 * π)⁻¹ * ξ) with hm_def
  have hhalf := infDist_zmultiples_le_half (by positivity : (0 : ℝ) < 2 * π) ξ
  rw [hm] at hhalf ⊢
  set t : ℝ := ξ / 2 - m * π with ht
  have habs : |ξ - m * (2 * π)| = 2 * |t| := by
    rw [ht, show ξ - (m : ℝ) * (2 * π) = 2 * (ξ / 2 - m * π) by ring, abs_mul, abs_two]
  have hnorm : ‖1 - cexp (ξ * I)‖ = 2 * |Real.sin (ξ / 2)| := by
    rw [norm_sub_rev, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
      abs_two]
  have hsin : |Real.sin (ξ / 2)| = |Real.sin t| := by
    rw [ht, Real.sin_sub_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  have ht2 : |t| ≤ π / 2 := by linarith [hhalf, habs]
  have hjordan : 2 / π * |t| ≤ |Real.sin t| := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h] at ht2 ⊢
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith))]
      exact Real.mul_le_sin h ht2
    · rw [abs_of_neg h] at ht2 ⊢
      have h1 := Real.mul_le_sin (by linarith : (0 : ℝ) ≤ -t) ht2
      rw [Real.sin_neg] at h1
      have h2 : Real.sin t ≤ 0 := by
        have : 0 ≤ 2 / π * -t := mul_nonneg (by positivity) (by linarith)
        linarith
      rw [abs_of_nonpos h2]
      linarith
  rw [hnorm, hsin, habs]
  calc 2 / π * (2 * |t|) = 2 * (2 / π * |t|) := by ring
    _ ≤ 2 * |Real.sin t| := by linarith

/-! ## 7. The window for a general profile (Lemma 3.3(i)) -/

/-- `Σ(u) := Σ_{k∈ℤ} η(u − k)²`. -/
def Sig (η : ℝ → ℝ) (u : ℝ) : ℝ := ∑' k : ℤ, η (u - k) ^ 2

/-- The window, the body of `HRTorus.SlotFrame.window`. -/
def win (η : ℝ → ℝ) (u : ℝ) : ℝ := η u * (∑' k : ℤ, η (u - k) ^ 2) ^ (-(1 / 2 : ℝ))

section Window

variable {η : ℝ → ℝ} (hzero : ∀ u : ℝ, 1 ≤ |u| → η u = 0)
include hzero

theorem eta_shift_zero_of_far {u u₀ : ℝ} (hu : |u - u₀| < 1 / 2) {k : ℤ}
    (hk : k ∉ Finset.Icc (⌊u₀⌋ - 1) (⌊u₀⌋ + 2)) : η (u - k) = 0 := by
  apply hzero
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  have h1 : (⌊u₀⌋ : ℝ) ≤ u₀ := Int.floor_le u₀
  have h2 : u₀ < (⌊u₀⌋ : ℝ) + 1 := Int.lt_floor_add_one u₀
  rw [abs_lt] at hu
  rcases hk with hk | hk
  · have hk' : (k : ℝ) ≤ (⌊u₀⌋ : ℝ) - 2 := by
      have : k ≤ ⌊u₀⌋ - 2 := by omega
      exact_mod_cast this
    rw [abs_of_pos (by linarith)]
    linarith
  · have hk' : (⌊u₀⌋ : ℝ) + 3 ≤ (k : ℝ) := by
      have : ⌊u₀⌋ + 3 ≤ k := by omega
      exact_mod_cast this
    rw [abs_of_neg (by linarith)]
    linarith

theorem Sig_eq_sum {u u₀ : ℝ} (hu : |u - u₀| < 1 / 2) :
    Sig η u = ∑ k ∈ Finset.Icc (⌊u₀⌋ - 1) (⌊u₀⌋ + 2), η (u - k) ^ 2 := by
  unfold Sig
  apply tsum_eq_sum
  intro k hk
  rw [eta_shift_zero_of_far hzero hu hk]
  ring

theorem summable_Sig (u : ℝ) : Summable (fun k : ℤ => η (u - k) ^ 2) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc (⌊u⌋ - 1) (⌊u⌋ + 2))
  intro k hk
  rw [eta_shift_zero_of_far hzero (u₀ := u) (by simp) hk]
  ring

omit hzero in
theorem Sig_periodic (u : ℝ) (m : ℤ) : Sig η (u - m) = Sig η u := by
  unfold Sig
  rw [← (Equiv.addLeft m).tsum_eq (fun k : ℤ => η (u - k) ^ 2)]
  congr 1
  funext k
  simp only [Equiv.coe_addLeft, Int.cast_add]
  ring_nf

theorem Sig_pos (hpos : ∀ u : ℝ, |u| < 1 → 0 < η u) (u : ℝ) : 0 < Sig η u := by
  have hr : |u - round u| < 1 := lt_of_le_of_lt (abs_sub_round u) (by norm_num)
  have h1 : 0 < η (u - round u) ^ 2 := by
    have := hpos _ hr
    positivity
  calc (0 : ℝ) < η (u - round u) ^ 2 := h1
    _ ≤ Sig η u := (summable_Sig hzero u).le_tsum (round u) (fun j _ => sq_nonneg _)

theorem Sig_contDiff (hη : ContDiff ℝ ∞ η) : ContDiff ℝ ∞ (Sig η) := by
  rw [contDiff_iff_contDiffAt]
  intro u₀
  have hfin : ContDiff ℝ ∞ (fun u => ∑ k ∈ Finset.Icc (⌊u₀⌋ - 1) (⌊u₀⌋ + 2), η (u - k) ^ 2) := by
    apply ContDiff.sum
    intro k _
    exact (hη.comp (contDiff_id.sub contDiff_const)).pow 2
  apply hfin.contDiffAt.congr_of_eventuallyEq
  have hball : Metric.ball u₀ (1 / 2) ∈ nhds u₀ := Metric.ball_mem_nhds u₀ (by norm_num)
  filter_upwards [hball] with u hu
  rw [Metric.mem_ball, Real.dist_eq] at hu
  exact Sig_eq_sum hzero hu

theorem win_eq_zero {u : ℝ} (hu : 1 ≤ |u|) : win η u = 0 := by
  unfold win; rw [hzero u hu, zero_mul]

theorem win_contDiff (hη : ContDiff ℝ ∞ η) (hpos : ∀ u : ℝ, |u| < 1 → 0 < η u) :
    ContDiff ℝ ∞ (win η) := by
  have h := (Sig_contDiff hzero hη).rpow_const_of_ne (p := -(1 / 2 : ℝ))
    (fun u => (Sig_pos hzero hpos u).ne')
  exact hη.mul h

theorem win_sq_tsum (hpos : ∀ u : ℝ, |u| < 1 → 0 < η u) (u : ℝ) :
    ∑' k : ℤ, win η (u - k) ^ 2 = 1 := by
  have hS := Sig_pos hzero hpos u
  have key : ∀ k : ℤ, win η (u - k) ^ 2 = η (u - k) ^ 2 * (Sig η u)⁻¹ := by
    intro k
    have hper : (∑' j : ℤ, η (u - k - j) ^ 2) = Sig η u := Sig_periodic u k
    unfold win
    rw [hper, mul_pow, ← Real.rpow_natCast ((Sig η u) ^ (-(1 / 2 : ℝ))),
      ← Real.rpow_mul hS.le]
    norm_num [Real.rpow_neg_one]
  rw [tsum_congr key, tsum_mul_right]
  change Sig η u * (Sig η u)⁻¹ = 1
  exact mul_inv_cancel₀ hS.ne'

theorem iteratedDeriv_win_eq_zero (n : ℕ) {u : ℝ} (hu : 1 < |u|) : iteratedDeriv n (win η) u = 0 := by
  have hopen : IsOpen {v : ℝ | 1 < |v|} := isOpen_lt continuous_const continuous_abs
  have hev : win η =ᶠ[nhds u] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hu] with v hv
    exact win_eq_zero hzero (le_of_lt hv)
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const]
  split_ifs <;> rfl

theorem win_iteratedDeriv_bound (hη : ContDiff ℝ ∞ η) (hpos : ∀ u : ℝ, |u| < 1 → 0 < η u) (n : ℕ) :
    ∃ M : ℝ, ∀ u : ℝ, |iteratedDeriv n (win η) u| ≤ M := by
  have hc : Continuous (iteratedDeriv n (win η)) :=
    (win_contDiff hzero hη hpos).continuous_iteratedDeriv n (by exact_mod_cast le_top)
  have hs : HasCompactSupport (iteratedDeriv n (win η)) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro u hu
    apply iteratedDeriv_win_eq_zero hzero n
    simp only [Set.mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact hu
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  exact ⟨C, fun u => by simpa [Real.norm_eq_abs] using hC u⟩

end Window

/-! ## 8. The windowed Gaussian sum over the orbitals of one window (Steps 2–3) -/

section Windowed

variable {η : ℝ → ℝ} (hzero : ∀ u : ℝ, 1 ≤ |u| → η u = 0) (hη : ContDiff ℝ ∞ η)
  (hpos : ∀ u : ℝ, |u| < 1 → 0 < η u)
include hzero hη hpos

/-- For `g(v) = w(αv − a) q₀(κv − c)` with `|κv − c| ≥ ε` wherever `|αv − a| ≤ 1`:
`|(1 − e^{iξ})^n Σ_j g(j) e^{ijξ}| ≤ (2/α + n + 1) K_n (α + κ)^n e^{−ε²/4}`, with `K_n` depending only
on `η` and `n`. -/
theorem windowed_sum_bound {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hqb : ∀ i : ℕ, ∃ μ : ℝ, 0 ≤ μ ∧ ∀ u : ℝ, |iteratedDeriv i q u| ≤ μ * Real.exp (-(u ^ 2 / 4)))
    (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (α κ a c ε ξ : ℝ), 0 < α → 0 < κ → 0 ≤ ε →
    (∀ v : ℝ, |α * v - a| ≤ 1 → ε ≤ |κ * v - c|) →
    ‖(1 - cexp (ξ * I)) ^ n *
        ∑' j : ℤ, ((win η (α * j - a) * q (κ * j - c) : ℝ) : ℂ) * cexp (j * ξ * I)‖ ≤
      (2 / α + n + 1) * (K * (α + κ) ^ n * Real.exp (-(ε ^ 2 / 4))) := by
  choose Mw hMw using fun i => win_iteratedDeriv_bound hzero hη hpos i
  choose μ hμ0 hμ using hqb
  have hMw0 : ∀ i, 0 ≤ Mw i := fun i => le_trans (abs_nonneg _) (hMw i 0)
  set K := ∑ i ∈ Finset.range (n + 1), Mw i * μ (n - i) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun i _ => mul_nonneg (hMw0 i) (hμ0 _))
  refine ⟨K, hK0, fun α κ a c ε ξ hα hκ hε hεv => ?_⟩
  have hwin : ContDiff ℝ ∞ (win η) := win_contDiff hzero hη hpos
  have hgC : ContDiff ℝ n (fun v => win η (α * v - a) * q (κ * v - c)) := by
    have h : ContDiff ℝ ∞ (fun v => win η (α * v - a) * q (κ * v - c)) :=
      (hwin.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
        (hq.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
    exact contDiff_infty.mp h n
  have hAB : (a - 1) / α ≤ (a + 1) / α := by
    apply div_le_div_of_nonneg_right _ hα.le; linarith
  have hsupp : ∀ v, v < (a - 1) / α ∨ (a + 1) / α < v →
      (fun v => win η (α * v - a) * q (κ * v - c)) v = 0 := by
    intro v hv
    have h1 : 1 ≤ |α * v - a| := by
      rcases hv with hv | hv
      · rw [lt_div_iff₀ hα] at hv
        rw [abs_of_neg (by linarith)]; linarith
      · rw [div_lt_iff₀ hα] at hv
        rw [abs_of_pos (by linarith)]; linarith
    simp only [win_eq_zero hzero h1, zero_mul]
  have hEε : ∀ v, |α * v - a| ≤ 1 →
      Real.exp (-((κ * v - c) ^ 2 / 4)) ≤ Real.exp (-(ε ^ 2 / 4)) := by
    intro v hv
    apply Real.exp_le_exp.mpr
    have h1 := hεv v hv
    have h2 : ε ^ 2 ≤ (κ * v - c) ^ 2 := by
      rw [← sq_abs (κ * v - c)]
      exact pow_le_pow_left₀ hε h1 2
    linarith
  have he0 : 0 ≤ Real.exp (-(ε ^ 2 / 4)) := (Real.exp_pos _).le
  have hM : ∀ v, |iteratedDeriv n (fun v => win η (α * v - a) * q (κ * v - c)) v| ≤
      K * (α + κ) ^ n * Real.exp (-(ε ^ 2 / 4)) := by
    intro v
    have hL := leibniz_affine_bound n hwin hq α κ a c v
    rw [abs_of_pos hα, abs_of_pos hκ] at hL
    refine le_trans hL ?_
    rw [add_pow, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rcases le_or_gt |α * v - a| 1 with h1 | h1
    · have hw := hMw i (α * v - a)
      have hq : |iteratedDeriv (n - i) q (κ * v - c)| ≤ μ (n - i) * Real.exp (-(ε ^ 2 / 4)) :=
        le_trans (hμ (n - i) (κ * v - c)) (mul_le_mul_of_nonneg_left (hEε v h1) (hμ0 _))
      have hKi : Mw i * μ (n - i) ≤ K :=
        Finset.single_le_sum (f := fun i => Mw i * μ (n - i))
          (fun j _ => mul_nonneg (hMw0 j) (hμ0 _)) hi
      calc (n.choose i : ℝ) * (α ^ i * |iteratedDeriv i (win η) (α * v - a)|) *
            (κ ^ (n - i) * |iteratedDeriv (n - i) q (κ * v - c)|)
          ≤ (n.choose i : ℝ) * (α ^ i * Mw i) *
              (κ ^ (n - i) * (μ (n - i) * Real.exp (-(ε ^ 2 / 4)))) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by positivity))
                (by positivity)
            · exact mul_le_mul_of_nonneg_left hq (by positivity)
            · positivity
            · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hMw0 i))
        _ = (Mw i * μ (n - i)) * (α ^ i * κ ^ (n - i) * (n.choose i : ℝ)) *
              Real.exp (-(ε ^ 2 / 4)) := by ring
        _ ≤ K * (α ^ i * κ ^ (n - i) * (n.choose i : ℝ)) * Real.exp (-(ε ^ 2 / 4)) := by
            apply mul_le_mul_of_nonneg_right _ he0
            exact mul_le_mul_of_nonneg_right hKi (by positivity)
    · rw [iteratedDeriv_win_eq_zero hzero i h1]
      simp only [abs_zero, mul_zero, zero_mul]
      positivity
  have h := lattice_sum_bound n hgC hAB hsupp hM ξ
  have hBA : (a + 1) / α - (a - 1) / α = 2 / α := by field_simp; ring
  rw [hBA] at h
  exact h

end Windowed

/-! ## 9. Combining the two lattice bounds with Jordan's inequality (Step 4) -/

theorem decay_combine (n : ℕ) {S : ℂ} {ξ κ D B0 Bn : ℝ} (hκ : 0 < κ) (hD : 0 ≤ D)
    (h0 : ‖S‖ ≤ B0) (hn : ‖(1 - cexp (ξ * I)) ^ n * S‖ ≤ Bn)
    (hJ : 2 / π * (κ * D) ≤ ‖1 - cexp (ξ * I)‖) :
    ‖S‖ ≤ 2 ^ n * max B0 ((π / (2 * κ)) ^ n * Bn) * ((1 + D) ^ n)⁻¹ := by
  have hπ := Real.pi_pos
  have hB0 : 0 ≤ B0 := le_trans (norm_nonneg _) h0
  have hBn : 0 ≤ Bn := le_trans (norm_nonneg _) hn
  have hpos : 0 < (1 + D) ^ n := by positivity
  have hX : 0 ≤ max B0 ((π / (2 * κ)) ^ n * Bn) := le_trans hB0 (le_max_left _ _)
  rcases le_or_gt D 1 with hD1 | hD1
  · have h2 : (1 + D) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have hratio : 1 ≤ 2 ^ n * ((1 + D) ^ n)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div hpos]; exact h2
    calc ‖S‖ ≤ max B0 ((π / (2 * κ)) ^ n * Bn) := le_trans h0 (le_max_left _ _)
      _ = max B0 ((π / (2 * κ)) ^ n * Bn) * 1 := (mul_one _).symm
      _ ≤ max B0 ((π / (2 * κ)) ^ n * Bn) * (2 ^ n * ((1 + D) ^ n)⁻¹) :=
          mul_le_mul_of_nonneg_left hratio hX
      _ = 2 ^ n * max B0 ((π / (2 * κ)) ^ n * Bn) * ((1 + D) ^ n)⁻¹ := by ring
  · have hD0 : 0 < D := by linarith
    have hJpos : 0 < 2 / π * (κ * D) := by positivity
    have hpowJ : (2 / π * (κ * D)) ^ n ≤ ‖1 - cexp (ξ * I)‖ ^ n := pow_le_pow_left₀ hJpos.le hJ n
    have hmain : ‖S‖ * (2 / π * (κ * D)) ^ n ≤ Bn := by
      calc ‖S‖ * (2 / π * (κ * D)) ^ n ≤ ‖S‖ * ‖1 - cexp (ξ * I)‖ ^ n :=
            mul_le_mul_of_nonneg_left hpowJ (norm_nonneg _)
        _ = ‖(1 - cexp (ξ * I)) ^ n * S‖ := by rw [norm_mul, norm_pow, mul_comm]
        _ ≤ Bn := hn
    have hS : ‖S‖ ≤ Bn / (2 / π * (κ * D)) ^ n := by
      rw [le_div_iff₀ (by positivity)]; exact hmain
    have hsplit : Bn / (2 / π * (κ * D)) ^ n = (π / (2 * κ)) ^ n * Bn * (D ^ n)⁻¹ := by
      rw [mul_pow, mul_pow, div_pow, div_pow]
      field_simp
      ring
    have h1D : (1 + D) ^ n ≤ 2 ^ n * D ^ n := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) n
    have hinv : (D ^ n)⁻¹ ≤ 2 ^ n * ((1 + D) ^ n)⁻¹ := by
      have h3 : (2 ^ n * D ^ n)⁻¹ ≤ ((1 + D) ^ n)⁻¹ := inv_anti₀ hpos h1D
      have h4 : (D ^ n)⁻¹ = 2 ^ n * (2 ^ n * D ^ n)⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      rw [h4]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have hc0 : 0 ≤ (π / (2 * κ)) ^ n * Bn := by positivity
    calc ‖S‖ ≤ (π / (2 * κ)) ^ n * Bn * (D ^ n)⁻¹ := hsplit ▸ hS
      _ ≤ (π / (2 * κ)) ^ n * Bn * (2 ^ n * ((1 + D) ^ n)⁻¹) :=
          mul_le_mul_of_nonneg_left hinv hc0
      _ = 2 ^ n * ((π / (2 * κ)) ^ n * Bn) * ((1 + D) ^ n)⁻¹ := by ring
      _ ≤ 2 ^ n * max B0 ((π / (2 * κ)) ^ n * Bn) * ((1 + D) ^ n)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

/-! ## 10. The sum over the images `m ∈ ℤ` (Step 6) -/

/-- The image majorant `G(t) := e⁴ (e⁻⁴)^{|t|}`. -/
def Gimg (t : ℤ) : ℝ := Real.exp 4 * Real.exp (-4) ^ t.natAbs

theorem Gimg_nonneg (t : ℤ) : 0 ≤ Gimg t := by unfold Gimg; positivity

theorem summable_Gimg : Summable Gimg := by
  have h0 : 0 ≤ Real.exp (-4) := (Real.exp_pos _).le
  have h1 : Real.exp (-4) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num)
  exact (summable_geom_int h0 h1).mul_left _

theorem hasSum_Gimg_shift (m₀ : ℤ) : HasSum (fun m : ℤ => Gimg (m - m₀)) (∑' t : ℤ, Gimg t) := by
  have h := (Equiv.subRight m₀).hasSum_iff (f := Gimg) (a := ∑' t : ℤ, Gimg t)
  exact h.mpr summable_Gimg.hasSum

theorem image_pointwise {L δ X : ℝ} (hL : 4 ≤ L) (hδ : 0 ≤ δ) (hδL : 2 * δ ≤ L) (m : ℤ) :
    Real.exp (-((max (|X - m * L| - δ) 0) ^ 2 / 4)) ≤
      Real.exp (-((max (Metric.infDist X (AddSubgroup.zmultiples L : Set ℝ) - δ) 0) ^ 2 / 4)) *
        Gimg (m - round (L⁻¹ * X)) := by
  have hLpos : 0 < L := by linarith
  set m₀ : ℤ := round (L⁻¹ * X) with hm₀
  set Δ := Metric.infDist X (AddSubgroup.zmultiples L : Set ℝ) with hΔ
  have hΔeq : Δ = |X - m₀ * L| := infDist_zmultiples_eq L X
  have hΔhalf : Δ ≤ L / 2 := infDist_zmultiples_le_half hLpos X
  have hΔ0 : 0 ≤ Δ := infDist_zmultiples_nonneg L X
  set p := max (Δ - δ) 0 with hp
  have hp0 : 0 ≤ p := le_max_right _ _
  set N : ℕ := (m - m₀).natAbs with hN
  have hNabs : (N : ℝ) = |((m - m₀ : ℤ) : ℝ)| := by rw [hN, Nat.cast_natAbs, Int.cast_abs]
  have hG : Gimg (m - m₀) = Real.exp 4 * Real.exp (-4) ^ N := rfl
  rw [hG, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- the triangle inequality: |X − mL| ≥ N L − Δ
  have htri : (N : ℝ) * L - Δ ≤ |X - m * L| := by
    have e : ((m - m₀ : ℤ) : ℝ) * L = (X - m₀ * L) - (X - m * L) := by push_cast; ring
    have h1 : |((m - m₀ : ℤ) : ℝ) * L| ≤ |X - m₀ * L| + |X - m * L| := by
      rw [e]; exact abs_sub _ _
    rw [abs_mul, abs_of_pos hLpos, ← hNabs, ← hΔeq] at h1
    linarith
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · -- `m = m₀`
    have hmm : m = m₀ := by
      have : (m - m₀).natAbs = 0 := by rw [← hN]; exact hN0
      omega
    rw [hmm, ← hΔeq, hN0]
    simp only [hp, Nat.cast_zero, zero_mul, add_zero]
    linarith
  · obtain ⟨n', hn'⟩ : ∃ n' : ℕ, N = n' + 1 := ⟨N - 1, by omega⟩
    have hn'R : (N : ℝ) = n' + 1 := by rw [hn']; push_cast; ring
    have hsq : (n' : ℝ) ≤ (n' : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n' with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n' := by exact_mod_cast h
        nlinarith
    have hLΔ : p ≤ L - Δ - δ := by
      rw [hp]; apply max_le <;> linarith
    have hε : (n' : ℝ) * L + p ≤ max (|X - m * L| - δ) 0 := by
      apply le_trans _ (le_max_left _ _)
      rw [hn'R] at htri
      linarith
    have hε0 : 0 ≤ (n' : ℝ) * L + p := by positivity
    have hsq2 : ((n' : ℝ) * L + p) ^ 2 ≤ (max (|X - m * L| - δ) 0) ^ 2 :=
      pow_le_pow_left₀ hε0 hε 2
    have hL2 : 16 * (n' : ℝ) ≤ ((n' : ℝ) * L) ^ 2 := by
      have h16 : (16 : ℝ) ≤ L ^ 2 := by nlinarith
      have hn0 : (0 : ℝ) ≤ n' := Nat.cast_nonneg n'
      calc 16 * (n' : ℝ) ≤ 16 * (n' : ℝ) ^ 2 := by nlinarith
        _ ≤ L ^ 2 * (n' : ℝ) ^ 2 := by nlinarith
        _ = ((n' : ℝ) * L) ^ 2 := by ring
    have hcross : 0 ≤ 2 * ((n' : ℝ) * L) * p := by positivity
    rw [hn'R]
    nlinarith

theorem image_sum_bound {L δ X : ℝ} (hL : 4 ≤ L) (hδ : 0 ≤ δ) (hδL : 2 * δ ≤ L) :
    Summable (fun m : ℤ => Real.exp (-((max (|X - m * L| - δ) 0) ^ 2 / 4))) ∧
    ∑' m : ℤ, Real.exp (-((max (|X - m * L| - δ) 0) ^ 2 / 4)) ≤
      Real.exp (-((max (Metric.infDist X (AddSubgroup.zmultiples L : Set ℝ) - δ) 0) ^ 2 / 4)) *
        ∑' t : ℤ, Gimg t := by
  set E := Real.exp (-((max (Metric.infDist X (AddSubgroup.zmultiples L : Set ℝ) - δ) 0) ^ 2 / 4))
  have hmaj : HasSum (fun m : ℤ => E * Gimg (m - round (L⁻¹ * X))) (E * ∑' t : ℤ, Gimg t) :=
    (hasSum_Gimg_shift _).mul_left E
  have hs : Summable (fun m : ℤ => Real.exp (-((max (|X - m * L| - δ) 0) ^ 2 / 4))) :=
    Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) (fun m => image_pointwise hL hδ hδL m)
      hmaj.summable
  refine ⟨hs, ?_⟩
  rw [← hmaj.tsum_eq]
  exact hs.tsum_le_tsum (fun m => image_pointwise hL hδ hδL m) hmaj.summable

/-! ## 11. One-dimensional lattice sums on a circle (for Lemma 3.5(iii)) -/

/-- A sum over integer points of a decreasing function of the distance to `X` is bounded by the
full sum at spacing `c ≤ δ/2`, uniformly in `X`. -/
theorem lattice_sum_le {F : ℝ → ℝ} (hF0 : ∀ u, 0 ≤ F u) (hFanti : AntitoneOn F (Set.Ici 0))
    {δ c : ℝ} (hc : 0 < c) (hcδ : c ≤ δ / 2) (hsum : Summable (fun u : ℤ => F (|(u : ℝ)| * c)))
    (X : ℝ) (S : Finset ℤ) :
    ∑ t ∈ S, F (|X - t * δ|) ≤ ∑' u : ℤ, F (|(u : ℝ)| * c) := by
  have hδ : 0 < δ := by linarith
  set t₀ : ℤ := round (X / δ) with ht₀
  have hround : |X / δ - t₀| ≤ 1 / 2 := abs_sub_round _
  have hX0 : |X - t₀ * δ| ≤ δ / 2 := by
    have e : X - t₀ * δ = δ * (X / δ - t₀) := by field_simp
    rw [e, abs_mul, abs_of_pos hδ]
    nlinarith [hround]
  have hpt : ∀ t : ℤ, F (|X - t * δ|) ≤ F (|((t - t₀ : ℤ) : ℝ)| * c) := by
    intro t
    apply hFanti (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr (abs_nonneg _))
    by_cases h : t = t₀
    · rw [h, sub_self]; simp
    · have h1 : (1 : ℝ) ≤ |((t - t₀ : ℤ) : ℝ)| := by
        have h2 : (t - t₀ : ℤ) ≠ 0 := sub_ne_zero.mpr h
        have h3 := Int.one_le_abs h2
        rw [← Int.cast_abs]
        exact_mod_cast h3
      have htri : |((t - t₀ : ℤ) : ℝ)| * δ ≤ |X - t * δ| + |X - t₀ * δ| := by
        have e : ((t - t₀ : ℤ) : ℝ) * δ = (X - t₀ * δ) - (X - t * δ) := by push_cast; ring
        calc |((t - t₀ : ℤ) : ℝ)| * δ = |((t - t₀ : ℤ) : ℝ) * δ| := by rw [abs_mul, abs_of_pos hδ]
          _ = |(X - t₀ * δ) - (X - t * δ)| := by rw [e]
          _ ≤ |X - t₀ * δ| + |X - t * δ| := abs_sub _ _
          _ = |X - t * δ| + |X - t₀ * δ| := add_comm _ _
      nlinarith
  have hsum' : Summable (fun t : ℤ => F (|((t - t₀ : ℤ) : ℝ)| * c)) :=
    (Equiv.subRight t₀).summable_iff.mpr hsum
  calc ∑ t ∈ S, F (|X - t * δ|) ≤ ∑ t ∈ S, F (|((t - t₀ : ℤ) : ℝ)| * c) :=
        Finset.sum_le_sum (fun t _ => hpt t)
    _ ≤ ∑' t : ℤ, F (|((t - t₀ : ℤ) : ℝ)| * c) :=
        hsum'.sum_le_tsum S (fun t _ => hF0 _)
    _ = ∑' u : ℤ, F (|(u : ℝ)| * c) :=
        (Equiv.subRight t₀).tsum_eq (fun u : ℤ => F (|(u : ℝ)| * c))

/-- The same over the `n` points `aδ` (`a ∈ {0,…,n−1}`) of the circle `ℝ/nδℤ`, with the periodic
distance: the representatives lift injectively to `ℤ`. -/
theorem fin_sum_infDist_le {n : ℕ} (hn : 0 < n) {δ c : ℝ} (hc : 0 < c) (hcδ : c ≤ δ / 2)
    {F : ℝ → ℝ} (hF0 : ∀ u, 0 ≤ F u) (hFanti : AntitoneOn F (Set.Ici 0))
    (hsum : Summable (fun u : ℤ => F (|(u : ℝ)| * c))) (X : ℝ) :
    ∑ a : Fin n, F (Metric.infDist (X - ((a : ℕ) : ℝ) * δ)
        (AddSubgroup.zmultiples ((n : ℝ) * δ) : Set ℝ)) ≤ ∑' u : ℤ, F (|(u : ℝ)| * c) := by
  set t : Fin n → ℤ := fun a => ((a : ℕ) : ℤ) +
    round (((n : ℝ) * δ)⁻¹ * (X - ((a : ℕ) : ℝ) * δ)) * (n : ℤ) with ht_def
  have ht : ∀ a : Fin n, Metric.infDist (X - ((a : ℕ) : ℝ) * δ)
      (AddSubgroup.zmultiples ((n : ℝ) * δ) : Set ℝ) = |X - ((t a : ℤ) : ℝ) * δ| := by
    intro a
    rw [infDist_zmultiples_eq]
    congr 1
    simp only [ht_def]
    push_cast
    ring
  have hmod : ∀ a : Fin n, t a % (n : ℤ) = ((a : ℕ) : ℤ) := by
    intro a
    simp only [ht_def]
    rw [Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast a.isLt)
  have hinj : Set.InjOn t (Finset.univ : Finset (Fin n)) := by
    intro a _ b _ hab
    have h1 : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := by rw [← hmod a, ← hmod b, hab]
    exact Fin.ext (by exact_mod_cast h1)
  calc ∑ a : Fin n, F (Metric.infDist (X - ((a : ℕ) : ℝ) * δ)
          (AddSubgroup.zmultiples ((n : ℝ) * δ) : Set ℝ))
      = ∑ a : Fin n, F (|X - ((t a : ℤ) : ℝ) * δ|) :=
        Finset.sum_congr rfl (fun a _ => by rw [ht a])
    _ = ∑ u ∈ Finset.univ.image t, F (|X - (u : ℝ) * δ|) :=
        (Finset.sum_image (f := fun u : ℤ => F (|X - (u : ℝ) * δ|)) hinj).symm
    _ ≤ ∑' u : ℤ, F (|(u : ℝ)| * c) := lattice_sum_le hF0 hFanti hc hcδ hsum X _

/-- `(1 + p)^k e^{−p²/8}` is bounded on `p ≥ 0`. -/
theorem one_add_pow_mul_exp_le (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ, 0 ≤ p →
    (1 + p) ^ k * Real.exp (-(p ^ 2 / 8)) ≤ K := by
  refine ⟨2 ^ k * (1 + 2 ^ k * (1 + 4 ^ k * (k.factorial : ℝ))), by positivity, fun p hp => ?_⟩
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have h1 : (1 + p) ^ k ≤ 2 ^ k * (1 + p ^ k) := by
    rcases le_or_gt p 1 with h | h
    · have h3 : (1 + p) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      nlinarith [pow_nonneg hp k]
    · have h3 : (1 + p) ^ k ≤ (2 * p) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      rw [mul_pow] at h3
      nlinarith
  have h2 : p ^ k * Real.exp (-(p ^ 2 / 8)) ≤ 2 ^ k * (1 + 4 ^ k * (k.factorial : ℝ)) := by
    have h := abs_pow_mul_exp_le (p / 2) k
    rw [abs_of_nonneg (by positivity)] at h
    have hexp : Real.exp (-(p ^ 2 / 8)) ≤ Real.exp (-((p / 2) ^ 2 / 4)) := by
      apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg p]
    calc p ^ k * Real.exp (-(p ^ 2 / 8)) ≤ p ^ k * Real.exp (-((p / 2) ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left hexp (pow_nonneg hp k)
      _ = 2 ^ k * ((p / 2) ^ k * Real.exp (-((p / 2) ^ 2 / 4))) := by
          have e : (2 : ℝ) ^ k * (p / 2) ^ k = p ^ k := by rw [← mul_pow]; congr 1; ring
          rw [← mul_assoc, e]
      _ ≤ 2 ^ k * (1 + 4 ^ k * (k.factorial : ℝ)) := mul_le_mul_of_nonneg_left h h2k.le
  have hE : 0 ≤ Real.exp (-(p ^ 2 / 8)) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(p ^ 2 / 8)) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  calc (1 + p) ^ k * Real.exp (-(p ^ 2 / 8)) ≤ 2 ^ k * (1 + p ^ k) * Real.exp (-(p ^ 2 / 8)) :=
        mul_le_mul_of_nonneg_right h1 hE
    _ = 2 ^ k * (Real.exp (-(p ^ 2 / 8)) + p ^ k * Real.exp (-(p ^ 2 / 8))) := by ring
    _ ≤ 2 ^ k * (1 + 2 ^ k * (1 + 4 ^ k * (k.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add hE1 h2) h2k.le

/-- The Gaussian-tail majorant is summable over `ℤ`. -/
theorem summable_gauss_tail {c : ℝ} (hc : 0 < c) (A : ℝ) (hA : 0 ≤ A) :
    Summable (fun u : ℤ => Real.exp (-((max (|(u : ℝ)| * c - A) 0) ^ 2 / 8))) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun u => (Real.exp_pos _).le) (fun u => ?_)
    ((summable_geom_int hr0 hr1).mul_left (Real.exp (A + 2)))
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hu : ((u.natAbs : ℕ) : ℝ) = |(u : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hu]
  set v := |(u : ℝ)| * c with hv
  have hv0 : 0 ≤ v := by positivity
  rcases le_or_gt v A with h | h
  · rw [max_eq_right (by linarith)]
    nlinarith
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (v - A - 4)]

/-- The inverse-square majorant is summable over `ℤ`. -/
theorem summable_inv_sq_int {c : ℝ} (hc : 0 < c) :
    Summable (fun u : ℤ => ((1 + |(u : ℝ)| * c) ^ 2)⁻¹) := by
  set m := min 1 c with hm
  have hm0 : 0 < m := lt_min one_pos hc
  have hbase : Summable (fun n : ℕ => (m ^ 2)⁻¹ * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact h.mul_left _
  have hle : ∀ n : ℕ, ((1 + (n : ℝ) * c) ^ 2)⁻¹ ≤ (m ^ 2)⁻¹ * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    have h1 : m * ((n : ℝ) + 1) ≤ 1 + (n : ℝ) * c := by
      have hm1 : m ≤ 1 := min_le_left _ _
      have hmc : m ≤ c := min_le_right _ _
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have h2 : (m * ((n : ℝ) + 1)) ^ 2 ≤ (1 + (n : ℝ) * c) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [show (m ^ 2)⁻¹ * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) = ((m * ((n : ℝ) + 1)) ^ 2)⁻¹ by
      push_cast; rw [mul_pow, mul_inv, one_div]]
    exact inv_anti₀ (by positivity) h2
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
    have h := hle n
    simpa using h
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
    have h := hle n
    simpa using h

end HRTorus.SlotFrame.Analysis
