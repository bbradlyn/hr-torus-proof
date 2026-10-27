import HRTorus.ZeroModes.Upper
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Appendix D: the variational bound at fixed circumference (`ZeroModes.Twist`)

Written by Claude Opus 5.5 (an AI model), 2026-10-27. **Statement phase and proof phase (2026-10-27): the
definitions and statements were written first, every theorem that carries content `sorry`, and reviewed against the
paper before any proof; the proof phase (round one) then proved every statement, the reviewed text unchanged. The
proof devices — the declarations named `_dev`, in marked sections — are not statements of the paper. Written out as a
machine check that the statements connect: the model facts `twist_isDiag`, `chiSing_eq_chiS_dev`, `bcenTerm_eq_cpairD`,
`bcen_eq_tsum_cpairD` (definitional); the one-line derivations `twist_mem_sector`, `E11_le_twistBoundNum`,
`E3_le_twistBoundNum`; and the connecting derivations `twist_bound` (from `twist_bound_explicit`), `E11_le_twistBoundLy`,
`E3_le_twistBoundLy` (from `twist_bound`, the Rayleigh device `rayleigh_dev` and Theorem 2.10's dimensions). Where a
proof takes another route than the paper's, the header of its devices says so: Lemma D.4's occupation bound and
re-indexing, the roots of unity in the proof of Theorem D.1, the determinant argument of Lemma D.5, the threshold of
Corollary D.2.**
The paper: the HR paper, `papers/hr/appendices/D-twist.tex` — Theorem D.1 `thm:twist` with (D.2) `eq:twist-bound`,
Corollary D.2 `cor:alltori`, Lemma D.3 `lem:twists` (i)–(iv) and the remark after its proof, the text before Lemma D.4
(the pair annihilators `c^ν_{n,d}`, `c^{sing}_{n,d}`), Lemma D.4 `lem:twist-energy` with (D.3) `eq:twist-identity` and
(D.4) `eq:twist-energy`, Lemma D.5 `lem:twist-off`, Lemma D.6 `lem:gauss`, and the Gaussian sums (D.1)
`eq:gauss-sums`. The setting: "`Throughout this appendix $N\in\N$, $L_x,L_y>0$ with $L_xL_y=4\pi N$, and $\kappa=2\pi/L_y$, as in Definition~\ref{def:torus}.`"
Not here (not formalized): Remarks D.7–D.10 (`rem:twist-two`, `rem:twist-kernel`, `rem:twist-constants`,
`rem:twist-scope`; commentary that no statement uses), and the unnumbered commentary after Theorem D.1 on the regimes of
`L_y` (its content at bounded `L_y` is the bound `C(L₀)/N` of the proof of Corollary D.2, the device
`twistBoundLy_le_C_dev`).

## The model

* **The torus** is the Lean's rectangular `Torus` (`SlotFrame`): `N = T.N`, `N_φ = T.Nφ = 2N`, `κ = T.κ = 2π/L_y`;
  `T.N ≥ 1` always (`Torus.N_pos`), and `N ≥ 2` is a hypothesis where the paper has it.
* **The twists are defined as the diagonal matrices they are in the occupation-number basis** (`twist`): the entry at
  the configuration `m` is `e^{2πi (Σ_{j : m(j,σ) = 1} j̃)/N_φ}`, `j̃ = j.val ∈ {0, …, N_φ − 1}`, the phase written as
  `thy_orb`'s with `j.val` replaced by the sum over the occupied modes of spin `σ` — the pattern of the pilot's
  `gaugeOp` and `parityOp`, which are given as diagonal matrices and identified with the paper's exponentials by
  `gaugeOp_eq_exp`, `parityOp_eq_exp`. **The paper's definition, the exponential, is the statement `twist_eq_exp`**
  (Mathlib's `NormedSpace.exp` of `(2πi/N_φ) Σ_j j̃ n_{jσ}`), with any set of representatives in `twist_eq_exp_lift`;
  **(iv), the second quantization, is the statement `twist_eq_Ff`** (block A's `Ff` of the one-body unitary
  `twistOneBody`, `θ_y ⊗ |σ⟩⟨σ| + 1 ⊗ (1 − |σ⟩⟨σ|)`). The two-species twist `𝒲_↑𝒲_↓^*` is `twistTwo`.
* **Expectations.** The expectation of `H` at `v` is `(⟪v, toCLM T H v⟫_ℂ).re` (the form of `secEig_HN_nonneg`'s proof;
  the inner product is real for self-adjoint `H`); the identity (D.3) is stated for the complex inner product itself.
* **Lemma D.4's hypothesis** "a unit vector with `N` electrons such that `H_NΥ = 0`" is `Υ ∈ KN T` (block F1-upper's
  `𝒦_N`: the kernel of `H_N` intersected with the sum of the sectors with `n_↑ + n_↓ = N`) and `‖Υ‖ = 1`.
* **The pair annihilators** `c^ν_{n,d}` (`cpairD`) are block C's `cpair` at the orbitals of `bcenTerm`; `bcenTerm` and
  `bcen` are unchanged (`bcenTerm_eq_cpairD`). The singlet spinor `chiSing` is block C's device `PairForm.chiS`
  (`chiSing_eq_chiS_dev`). The inner series of (D.3) is a `tsum` over all `d : ℕ` with the parity condition inside the
  term (`twistTerm`, zero at `d = 0` by the weight `2d`), as `bcen`'s; the angle is `θd` with `θ = π/N_φ` for `𝒲_↑` and
  `θ = 2π/N_φ` for `𝒲_↑𝒲_↓^*`; `cos` and `sin` are `Real.cos`, `Real.sin` of real arguments, cast to `ℂ`. The sum over
  `n ∈ ℤ_{2N_φ}` is over the representatives `0, …, 2N_φ − 1`, as in `localForm_c`; `twistSum_add_two_Nφ` is the
  independence of the representative.
* **The Gaussian sums** `𝖦_k(κ)` (`gaussSum`) are real `tsum`s over `d : ℕ` of the term as the paper writes it,
  `2d^k e^{−κ²d²/4}`, which is `0` at `d = 0` for `k ≥ 1` (`gaussSum_eq_tsum_succ`: the paper's `Σ_{d ≥ 1}`).
* **The order of a root of unity** (Lemma D.5) is Mathlib's `orderOf` in the monoid `ℂ`; for the roots `e^{2πik/N_φ}` it
  is positive (`orderOf_exp_pos`), so it is the paper's least `k ≥ 1` with `ω^k = 1`, and `orderOf ω ∣ d` means what the
  paper's divisibility means.
* **The eigenvalues** are block D's `secEig` (`E11 T`, `hcEig T 𝐧 k` of `Assembly.Main`); Corollary D.2's family of
  all rectangular tori with `L_xL_y = 4πN` is `allTori N` (every `Torus` with `T.N = N`).
-/

open Complex Filter Topology
open scoped Real InnerProductSpace Matrix ComplexOrder

noncomputable section

namespace HRTorus.ZeroModes

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian HRTorus.Assembly
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op)

/-! ## The Gaussian sums (D.1) and Lemma D.6 -/

/-- **(D.1)**: "`For $k\ge1$ let`" "`\mathsf G_k(\kappa):=\sum_{d=1}^\infty2d^k\,e^{-\kappa^2d^2/4}`" — a real `tsum` over
`d : ℕ` of the term as the paper writes it (zero at `d = 0` for `k ≥ 1`; `gaussSum_eq_tsum_succ`). -/
def gaussSum (κ : ℝ) (k : ℕ) : ℝ :=
  ∑' d : ℕ, 2 * (d : ℝ) ^ k * Real.exp (-(κ ^ 2 * (d : ℝ) ^ 2) / 4)

/-- **(D.1)**: "`a convergent series.`" — for `κ > 0`, every `k`. -/
theorem summable_gaussSum {κ : ℝ} (hκ : 0 < κ) (k : ℕ) :
    Summable fun d : ℕ => 2 * (d : ℝ) ^ k * Real.exp (-(κ ^ 2 * (d : ℝ) ^ 2) / 4) := by
  have hr : 0 < κ ^ 2 / 4 := by positivity
  refine Summable.of_nonneg_of_le (fun d => by positivity) (fun d => ?_)
    ((Real.summable_pow_mul_exp_neg_nat_mul k hr).mul_left 2)
  have hd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ d := by exact_mod_cast h
      nlinarith
  have hexp : Real.exp (-(κ ^ 2 * (d : ℝ) ^ 2) / 4) ≤ Real.exp (-(κ ^ 2 / 4) * d) := by
    apply Real.exp_le_exp.mpr
    have hk : 0 ≤ κ ^ 2 := sq_nonneg _
    nlinarith
  calc 2 * (d : ℝ) ^ k * Real.exp (-(κ ^ 2 * (d : ℝ) ^ 2) / 4)
      ≤ 2 * (d : ℝ) ^ k * Real.exp (-(κ ^ 2 / 4) * d) := by gcongr
    _ = 2 * ((d : ℝ) ^ k * Real.exp (-(κ ^ 2 / 4) * d)) := by ring

/-- **(D.1)**: "`\mathsf G_k(\kappa):=\sum_{d=1}^\infty2d^k\,e^{-\kappa^2d^2/4}`" — the paper's sum from `d = 1`, for `k ≥ 1`. -/
theorem gaussSum_eq_tsum_succ (κ : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    gaussSum κ k = ∑' d : ℕ, 2 * ((d + 1 : ℕ) : ℝ) ^ k * Real.exp (-(κ ^ 2 * ((d + 1 : ℕ) : ℝ) ^ 2) / 4) := by
  unfold gaussSum
  set f : ℕ → ℝ := fun d => 2 * (d : ℝ) ^ k * Real.exp (-(κ ^ 2 * (d : ℝ) ^ 2) / 4) with hf
  show ∑' d, f d = ∑' d, f (d + 1)
  by_cases hs : Summable f
  · rw [hs.tsum_eq_zero_add]
    have h0 : f 0 = 0 := by simp [hf, zero_pow (by omega : k ≠ 0)]
    rw [h0, zero_add]
  · rw [tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable]
    exact fun h => hs ((summable_nat_add_iff 1).1 h)

/-! ### Proof devices for Lemma D.6 (proof phase, round one; not statements of the paper)

The proof's function `f(t) = 2t^k e^{−κ²t²/4}` (`gaussTerm_dev`): its derivative `t^{k−1} e^{−κ²t²/4}(2k − κ²t²)` makes it
nondecreasing on `[0, t_*]` and nonincreasing on `[t_*, ∞)`, `t_* = √(2k)/κ` (Mathlib's `monotoneOn_of_deriv_nonneg`,
`antitoneOn_of_deriv_nonpos`); the sum–integral comparison `Σ_{d ≥ 0} f(d) ≤ ∫_0^∞ f + max f` for such a function
(`unimodal_tsum_le_dev`: Mathlib's `MonotoneOn.sum_le_integral` below `⌊t_*⌋`, the paper's argument on
`[⌊t_*⌋, ⌊t_*⌋ + 1]`, and `AntitoneOn.tsum_comp_add_le_integral` beyond); the integrals from Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow` with `Γ(3/2) = √π/2` and `Γ(2) = 1` (the paper's `∫_0^∞ s²e^{−s²} = √π/4`,
`∫_0^∞ s³e^{−s²} = 1/2`); and the maxima `8/(eκ²)`, `2(6/e)^{3/2}/κ³` from `y e^{−y} ≤ e^{−1}` (Mathlib's
`Real.add_one_le_exp`). -/

/-- The term of the Gaussian sums as a function of a real variable. -/
def gaussTerm_dev (κ : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  2 * t ^ k * Real.exp (-(κ ^ 2 * t ^ 2) / 4)

theorem gaussTerm_continuous_dev (κ : ℝ) (k : ℕ) : Continuous (gaussTerm_dev κ k) := by
  unfold gaussTerm_dev
  fun_prop

theorem gaussTerm_nonneg_dev (κ : ℝ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gaussTerm_dev κ k t := by
  unfold gaussTerm_dev
  positivity

theorem gaussTerm_hasDerivAt_dev (κ : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (gaussTerm_dev κ (n + 1))
      (t ^ n * Real.exp (-(κ ^ 2 * t ^ 2) / 4) * (2 * ((n : ℝ) + 1) - κ ^ 2 * t ^ 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t ^ (n + 1)) (2 * (((n + 1 : ℕ) : ℝ) * t ^ n)) t := by
    simpa using (hasDerivAt_pow (n + 1) t).const_mul 2
  have h2 : HasDerivAt (fun t : ℝ => -(κ ^ 2 * t ^ 2) / 4) (-(κ ^ 2 * (2 * t)) / 4) t := by
    have h := ((hasDerivAt_pow 2 t).const_mul (κ ^ 2)).neg.div_const 4
    simpa using h
  have h3 := h1.mul h2.exp
  unfold gaussTerm_dev
  convert h3 using 1
  push_cast
  ring

theorem gaussTerm_monotoneOn_dev {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    MonotoneOn (gaussTerm_dev κ (n + 1)) (Set.Icc 0 (Real.sqrt (2 * ((n : ℝ) + 1)) / κ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (gaussTerm_continuous_dev κ _).continuousOn
  · intro x _
    exact (gaussTerm_hasDerivAt_dev κ n x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(gaussTerm_hasDerivAt_dev κ n x).deriv]
    have hx0 : 0 < x := hx.1
    have hxt : κ * x < Real.sqrt (2 * ((n : ℝ) + 1)) := by
      have := hx.2
      rw [lt_div_iff₀ hκ] at this
      linarith
    have hsq : (κ * x) ^ 2 < 2 * ((n : ℝ) + 1) := by
      have h0 : 0 ≤ κ * x := by positivity
      calc (κ * x) ^ 2 < Real.sqrt (2 * ((n : ℝ) + 1)) ^ 2 := by gcongr
        _ = 2 * ((n : ℝ) + 1) := Real.sq_sqrt (by positivity)
    have h4 : 0 ≤ 2 * ((n : ℝ) + 1) - κ ^ 2 * x ^ 2 := by nlinarith
    exact mul_nonneg (mul_nonneg (pow_nonneg hx0.le n) (Real.exp_pos _).le) h4

theorem gaussTerm_antitoneOn_dev {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    AntitoneOn (gaussTerm_dev κ (n + 1)) (Set.Ici (Real.sqrt (2 * ((n : ℝ) + 1)) / κ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (gaussTerm_continuous_dev κ _).continuousOn
  · intro x _
    exact (gaussTerm_hasDerivAt_dev κ n x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(gaussTerm_hasDerivAt_dev κ n x).deriv]
    have hs0 : 0 ≤ Real.sqrt (2 * ((n : ℝ) + 1)) / κ := by positivity
    have hx0 : 0 < x := lt_of_le_of_lt hs0 hx
    have hxt : Real.sqrt (2 * ((n : ℝ) + 1)) < κ * x := by
      have := hx
      rw [Set.mem_Ioi, div_lt_iff₀ hκ] at this
      linarith
    have hsq : 2 * ((n : ℝ) + 1) < (κ * x) ^ 2 := by
      calc 2 * ((n : ℝ) + 1) = Real.sqrt (2 * ((n : ℝ) + 1)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
        _ < (κ * x) ^ 2 := by gcongr
    have h4 : 2 * ((n : ℝ) + 1) - κ ^ 2 * x ^ 2 ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (pow_nonneg hx0.le n) (Real.exp_pos _).le) h4

theorem gaussTerm_integrableOn_dev {κ : ℝ} (hκ : 0 < κ) (k : ℕ) :
    MeasureTheory.IntegrableOn (gaussTerm_dev κ k) (Set.Ioi 0) := by
  have h : MeasureTheory.IntegrableOn (fun x : ℝ => 2 * (x ^ (k : ℝ) * Real.exp (-(κ ^ 2 / 4) * x ^ (2 : ℝ))))
      (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 2) (b := κ ^ 2 / 4)
      (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) two_pos (by positivity)).const_mul 2
  refine MeasureTheory.IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  simp only [gaussTerm_dev, Real.rpow_natCast, Real.rpow_two]
  ring_nf

theorem gaussTerm_integral_dev {κ : ℝ} (hκ : 0 < κ) (k : ℕ) :
    ∫ t in Set.Ioi 0, gaussTerm_dev κ k t =
      2 * ((κ ^ 2 / 4) ^ (-((k : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((k : ℝ) + 1) / 2)) := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (k : ℝ)) (b := κ ^ 2 / 4) two_pos
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) (by positivity)
  rw [← h, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [gaussTerm_dev, Real.rpow_natCast, Real.rpow_two]
  ring_nf

theorem gaussTerm_integral_two_dev {κ : ℝ} (hκ : 0 < κ) :
    ∫ t in Set.Ioi 0, gaussTerm_dev κ 2 t = 4 * Real.sqrt π / κ ^ 3 := by
  rw [gaussTerm_integral_dev hκ 2]
  have hG : Real.Gamma ((((2 : ℕ) : ℝ) + 1) / 2) = Real.sqrt π / 2 := by
    rw [show (((2 : ℕ) : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have hp : (κ ^ 2 / 4) ^ (-(((2 : ℕ) : ℝ) + 1) / 2) = 8 / κ ^ 3 := by
    rw [show κ ^ 2 / 4 = (κ / 2) ^ (2 : ℝ) by rw [Real.rpow_two]; ring, ← Real.rpow_mul (by positivity),
      show (2 : ℝ) * (-(((2 : ℕ) : ℝ) + 1) / 2) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_natCast]
    field_simp
    ring
  rw [hG, hp]
  ring

theorem gaussTerm_integral_three_dev {κ : ℝ} (hκ : 0 < κ) :
    ∫ t in Set.Ioi 0, gaussTerm_dev κ 3 t = 16 / κ ^ 4 := by
  rw [gaussTerm_integral_dev hκ 3]
  have hG : Real.Gamma ((((3 : ℕ) : ℝ) + 1) / 2) = 1 := by
    rw [show (((3 : ℕ) : ℝ) + 1) / 2 = 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one]
    ring
  have hp : (κ ^ 2 / 4) ^ (-(((3 : ℕ) : ℝ) + 1) / 2) = 16 / κ ^ 4 := by
    rw [show κ ^ 2 / 4 = (κ / 2) ^ (2 : ℝ) by rw [Real.rpow_two]; ring, ← Real.rpow_mul (by positivity),
      show (2 : ℝ) * (-(((3 : ℕ) : ℝ) + 1) / 2) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_natCast]
    field_simp
    ring
  rw [hG, hp]
  ring

theorem gaussTerm_two_le_dev {κ : ℝ} (hκ : 0 < κ) (t : ℝ) : gaussTerm_dev κ 2 t ≤ 8 / (Real.exp 1 * κ ^ 2) := by
  unfold gaussTerm_dev
  set y := κ ^ 2 * t ^ 2 / 4 with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : y * Real.exp (-y) ≤ Real.exp (-1) := by
    have h := Real.add_one_le_exp (y - 1)
    have h2 : y ≤ Real.exp y * Real.exp (-1) := by
      rw [← Real.exp_add]
      have : y - 1 = y + -1 := by ring
      rw [← this]
      linarith
    calc y * Real.exp (-y) ≤ Real.exp y * Real.exp (-1) * Real.exp (-y) := by gcongr
      _ = Real.exp (-1) := by rw [mul_comm (Real.exp y), mul_assoc, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one]
  have hk : (0 : ℝ) < κ ^ 2 := by positivity
  have hE : Real.exp (-(κ ^ 2 * t ^ 2) / 4) = Real.exp (-y) := by
    rw [hy]
    congr 1
    ring
  have ht2 : 2 * t ^ 2 = 8 / κ ^ 2 * y := by
    rw [hy]
    field_simp
    ring
  rw [hE, ht2, mul_assoc, Real.exp_neg 1] at *
  calc 8 / κ ^ 2 * (y * Real.exp (-y)) ≤ 8 / κ ^ 2 * (Real.exp 1)⁻¹ := by gcongr
    _ = 8 / (Real.exp 1 * κ ^ 2) := by field_simp

theorem gaussTerm_three_le_dev {κ : ℝ} (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t) :
    gaussTerm_dev κ 3 t ≤ 2 * (6 / Real.exp 1) ^ (3 / 2 : ℝ) / κ ^ 3 := by
  set y := κ ^ 2 * t ^ 2 / 6 with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : y * Real.exp (-y) ≤ Real.exp (-1) := by
    have h := Real.add_one_le_exp (y - 1)
    have h2 : y ≤ Real.exp y * Real.exp (-1) := by
      rw [← Real.exp_add]
      have : y - 1 = y + -1 := by ring
      rw [← this]
      linarith
    calc y * Real.exp (-y) ≤ Real.exp y * Real.exp (-1) * Real.exp (-y) := by gcongr
      _ = Real.exp (-1) := by rw [mul_comm (Real.exp y), mul_assoc, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one]
  have hk : (0 : ℝ) < κ := hκ
  have hlhs : 0 ≤ gaussTerm_dev κ 3 t := gaussTerm_nonneg_dev κ 3 ht
  have hrhs : 0 ≤ 2 * (6 / Real.exp 1) ^ (3 / 2 : ℝ) / κ ^ 3 := by positivity
  rw [← pow_le_pow_iff_left₀ hlhs hrhs (two_ne_zero)]
  have hsq_l : gaussTerm_dev κ 3 t ^ 2 = 864 / κ ^ 6 * (y * Real.exp (-y)) ^ 3 := by
    unfold gaussTerm_dev
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul, mul_pow, ← Real.exp_nat_mul]
    rw [hy]
    field_simp
    ring_nf
  have hsq_r : (2 * (6 / Real.exp 1) ^ (3 / 2 : ℝ) / κ ^ 3) ^ 2 = 864 / κ ^ 6 * Real.exp (-1) ^ 3 := by
    rw [div_pow, mul_pow, ← Real.rpow_natCast ((6 / Real.exp 1) ^ (3 / 2 : ℝ)) 2,
      ← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, Real.exp_neg 1, div_pow]
    field_simp
    ring
  rw [hsq_l, hsq_r]
  gcongr

/-- The sum–integral comparison for a unimodal function: `Σ_{d ≥ 0} f(d) ≤ ∫_0^∞ f + M`, `M` a bound of `f` on
`[0, ∞)`. -/
theorem unimodal_tsum_le_dev {f : ℝ → ℝ} {t₀ M : ℝ} (ht₀ : 0 ≤ t₀)
    (hmono : MonotoneOn f (Set.Icc 0 t₀)) (hanti : AntitoneOn f (Set.Ici t₀)) (hcont : Continuous f)
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi 0)) (hnn : ∀ t, 0 ≤ t → 0 ≤ f t) (hM : ∀ t, 0 ≤ t → f t ≤ M)
    (hsum : Summable fun d : ℕ => f d) :
    ∑' d : ℕ, f d ≤ (∫ t in Set.Ioi 0, f t) + M := by
  set D := ⌊t₀⌋₊ with hD
  have hD1 : (D : ℝ) ≤ t₀ := Nat.floor_le ht₀
  have hD2 : t₀ < (D : ℝ) + 1 := Nat.lt_floor_add_one t₀
  have hsplit := hsum.sum_add_tsum_nat_add (D + 2)
  rw [← hsplit, Finset.sum_range_succ, Finset.sum_range_succ]
  have hA : ∑ i ∈ Finset.range D, f i ≤ ∫ x in (0 : ℝ)..D, f x := by
    have h := MonotoneOn.sum_le_integral (x₀ := 0) (a := D)
      (hmono.mono (Set.Icc_subset_Icc le_rfl (by simpa using hD1)))
    simpa using h
  have hB : f D + f (D + 1 : ℕ) ≤ M + ∫ x in (D : ℝ)..(D + 1 : ℕ), f x := by
    have hmin : ∀ x ∈ Set.Icc (D : ℝ) ((D + 1 : ℕ) : ℝ), min (f D) (f (D + 1 : ℕ)) ≤ f x := by
      intro x hx
      by_cases hxt : x ≤ t₀
      · exact (min_le_left _ _).trans (hmono ⟨Nat.cast_nonneg D, hD1⟩ ⟨(Nat.cast_nonneg D).trans hx.1, hxt⟩ hx.1)
      · push Not at hxt
        refine (min_le_right _ _).trans (hanti (Set.mem_Ici.2 hxt.le) (Set.mem_Ici.2 ?_) hx.2)
        push_cast
        linarith
    have hle : (D : ℝ) ≤ ((D + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hI : ∫ x in (D : ℝ)..((D + 1 : ℕ) : ℝ), min (f D) (f (D + 1 : ℕ)) ≤ ∫ x in (D : ℝ)..((D + 1 : ℕ) : ℝ), f x :=
      intervalIntegral.integral_mono_on hle intervalIntegrable_const (hcont.intervalIntegrable _ _) hmin
    rw [intervalIntegral.integral_const, smul_eq_mul, show ((D + 1 : ℕ) : ℝ) - D = 1 by push_cast; ring,
      one_mul] at hI
    have hmax : max (f D) (f (D + 1 : ℕ)) ≤ M := max_le (hM _ (Nat.cast_nonneg _)) (hM _ (Nat.cast_nonneg _))
    have := min_add_max (f D) (f (D + 1 : ℕ))
    linarith
  have hC : ∑' n : ℕ, f ((n + (D + 2) : ℕ) : ℝ) ≤ ∫ x in Set.Ioi ((D + 1 : ℕ) : ℝ), f x := by
    have hanti' : AntitoneOn f (Set.Ici ((D + 1 : ℕ) : ℝ)) :=
      hanti.mono (Set.Ici_subset_Ici.2 (by push_cast; linarith))
    have h := AntitoneOn.tsum_comp_add_le_integral (D + 1) hanti'
      (hint.mono_set (Set.Ioi_subset_Ioi (Nat.cast_nonneg _)))
      (fun t ht => hnn t ((Nat.cast_nonneg _).trans (le_of_lt ht)))
    have he : ∀ n : ℕ, n + (D + 1) + 1 = n + (D + 2) := fun n => by ring
    simp only [he] at h
    exact h
  have hint1 : (∫ x in (0 : ℝ)..D, f x) + (∫ x in (D : ℝ)..((D + 1 : ℕ) : ℝ), f x) =
      ∫ x in (0 : ℝ)..((D + 1 : ℕ) : ℝ), f x :=
    intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume) (hcont.intervalIntegrable 0 D)
      (hcont.intervalIntegrable (D : ℝ) ((D + 1 : ℕ) : ℝ))
  have hU := MeasureTheory.setIntegral_union (μ := MeasureTheory.volume) (f := f)
    (s := Set.Ioc (0 : ℝ) ((D + 1 : ℕ) : ℝ)) (t := Set.Ioi ((D + 1 : ℕ) : ℝ))
    Set.Ioc_disjoint_Ioi_same measurableSet_Ioi (hint.mono_set Set.Ioc_subset_Ioi_self)
    (hint.mono_set (Set.Ioi_subset_Ioi (Nat.cast_nonneg _)))
  rw [Set.Ioc_union_Ioi_eq_Ioi (Nat.cast_nonneg _)] at hU
  have hint2 : (∫ x in (0 : ℝ)..((D + 1 : ℕ) : ℝ), f x) + (∫ x in Set.Ioi ((D + 1 : ℕ) : ℝ), f x) =
      ∫ x in Set.Ioi 0, f x := by
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg _), hU]
  linarith [hA, hB, hC, hint1, hint2]

/-- **Lemma D.6** (the first bound): "`For every $\kappa>0$,`" "`\mathsf G_2(\kappa)\le\frac{4\sqrt\pi}{\kappa^3}\Bigl(1+\frac{2\kappa}{e\sqrt\pi}\Bigr)`" -/
theorem gaussSum_two_le {κ : ℝ} (hκ : 0 < κ) :
    gaussSum κ 2 ≤ 4 * Real.sqrt π / κ ^ 3 * (1 + 2 * κ / (Real.exp 1 * Real.sqrt π)) := by
  have h := unimodal_tsum_le_dev (f := gaussTerm_dev κ 2) (t₀ := Real.sqrt (2 * (((1 : ℕ) : ℝ) + 1)) / κ)
    (M := 8 / (Real.exp 1 * κ ^ 2)) (by positivity) (gaussTerm_monotoneOn_dev hκ 1) (gaussTerm_antitoneOn_dev hκ 1)
    (gaussTerm_continuous_dev κ 2) (gaussTerm_integrableOn_dev hκ 2) (fun t ht => gaussTerm_nonneg_dev κ 2 ht)
    (fun t _ => gaussTerm_two_le_dev hκ t) (summable_gaussSum hκ 2)
  rw [gaussTerm_integral_two_dev hκ] at h
  have hgs : gaussSum κ 2 = ∑' d : ℕ, gaussTerm_dev κ 2 d := rfl
  rw [hgs]
  refine h.trans (le_of_eq ?_)
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  field_simp
  ring

/-- **Lemma D.6** (the second bound): "`For every $\kappa>0$,`" "`\mathsf G_3(\kappa)\le\frac{16}{\kappa^4}\Bigl(1+\frac{(6/e)^{3/2}\kappa}8\Bigr)`" -/
theorem gaussSum_three_le {κ : ℝ} (hκ : 0 < κ) :
    gaussSum κ 3 ≤ 16 / κ ^ 4 * (1 + (6 / Real.exp 1) ^ (3 / 2 : ℝ) * κ / 8) := by
  have h := unimodal_tsum_le_dev (f := gaussTerm_dev κ 3) (t₀ := Real.sqrt (2 * (((2 : ℕ) : ℝ) + 1)) / κ)
    (M := 2 * (6 / Real.exp 1) ^ (3 / 2 : ℝ) / κ ^ 3) (by positivity) (gaussTerm_monotoneOn_dev hκ 2)
    (gaussTerm_antitoneOn_dev hκ 2) (gaussTerm_continuous_dev κ 3) (gaussTerm_integrableOn_dev hκ 3)
    (fun t ht => gaussTerm_nonneg_dev κ 3 ht) (fun t ht => gaussTerm_three_le_dev hκ ht) (summable_gaussSum hκ 3)
  rw [gaussTerm_integral_three_dev hκ] at h
  have hgs : gaussSum κ 3 = ∑' d : ℕ, gaussTerm_dev κ 3 d := rfl
  rw [hgs]
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-! ## The twists (Lemma D.3) -/

/-- **Lemma D.3**: "`For $\sigma\in\{\up,\dn\}$ let`" "`\mathcal W_\sigma:=\exp\Bigl(\frac{2\pi\iu}{\Nphi}\sum_{j=0}^{\Nphi-1}j\,n_{[j]\sigma}\Bigr).`"
— **defined as the diagonal matrix it is in the occupation-number basis** (the module docstring): the entry at `m` is
`exp(2πi (Σ_{j : m(j,σ) = 1} j.val)/N_φ)`. The paper's exponential is `twist_eq_exp`, its (iv) is `twist_eq_Ff`. -/
def twist (T : Torus) (σ : Spin) : FockOp T :=
  Matrix.diagonal fun m : Conf (ZMod T.Nφ) =>
    Complex.exp (2 * π * I * (∑ j : ZMod T.Nφ, if m (j, σ) = true then (j.val : ℂ) else 0) / (T.Nφ : ℂ))

/-- **Lemma D.5**: "`let $\mathcal W$ be $\mathcal W_\up$ or $\mathcal W_\up\mathcal W_\dn^*$.`" — the two-species twist
`𝒲_↑𝒲_↓^*`. -/
def twistTwo (T : Torus) : FockOp T :=
  twist T .up * (twist T .dn)ᴴ

/-- **Lemma D.3(iv)**: the one-body unitary "`\thy\otimes\lvert\sigma\rangle\langle\sigma\rvert+\one\otimes(\one-\lvert\sigma\rangle\langle\sigma\rvert)`"
on `𝔨_N`, in the basis `ψ_j ⊗ τ` (Kronecker products, as block A's `thx2`; `|σ⟩⟨σ|` is `Matrix.single σ σ 1`). -/
def twistOneBody (T : Torus) (σ : Spin) : Matrix (Modes T) (Modes T) ℂ :=
  Matrix.kronecker (thyMat T) (Matrix.single σ σ (1 : ℂ)) +
    Matrix.kronecker (1 : Matrix (ZMod T.Nφ) (ZMod T.Nφ) ℂ) (1 - Matrix.single σ σ (1 : ℂ))

/-- **Lemma D.3(iii)**: the occupation `n_σ` of a sector label, "`$\nn=(n_\up,n_\dn)$`": `n_↑ = nn.1`, `n_↓ = nn.2`. -/
def secN {T : Torus} (nn : SectorLabel T) : Spin → ℕ
  | .up => (nn.1 : ℕ)
  | .dn => (nn.2 : ℕ)

/-! ### Proof devices for Lemma D.3: the phases and the exponentials (proof phase, round one; not statements of the paper)

`twistDiag_dev T σ m` is the entry of `𝒲_σ` at the configuration `m`, `twistPhi_dev T σ μ` the phase `e^{2πi j/N_φ}` (or
`1`) that `𝒲_σ` puts on the mode `μ = (j, τ)`; emptying an occupied mode `μ` divides the entry by that phase
(`twistDiag_update_dev`), which is what the pilot's `diagonal_mul_c_mul_conjTranspose` needs for (ii). The exponential
of a diagonal operator is the diagonal of the exponentials (Mathlib's `Matrix.exp_diagonal`, as in the pilot's
`gaugeOp_eq_exp_dev`), and `exp((2πi/N_φ) Σ_j r_j n_{jσ})` has the entry `exp(2πi Σ_{j : m(j,σ)} r_j/N_φ)`, the same for
every lift `r` of the classes since `exp(2πik) = 1` (`twist_eq_exp_lift_dev`, the proof of `twist_eq_exp_lift`, placed
here because `twist_eq_exp` uses it). -/

/-- The entry of `𝒲_σ` at the configuration `m`. -/
def twistDiag_dev (T : Torus) (σ : Spin) (m : Conf (ZMod T.Nφ)) : ℂ :=
  Complex.exp (2 * π * I * (∑ j : ZMod T.Nφ, if m (j, σ) = true then (j.val : ℂ) else 0) / (T.Nφ : ℂ))

/-- The phase that `𝒲_σ` puts on the mode `μ`: `e^{2πi j/N_φ}` for `μ = (j, σ)`, `1` for the other spin. -/
def twistPhi_dev (T : Torus) (σ : Spin) (μ : Modes T) : ℂ :=
  if μ.2 = σ then Complex.exp (2 * π * I * (μ.1.val : ℂ) / (T.Nφ : ℂ)) else 1

theorem twist_eq_diagonal_dev (T : Torus) (σ : Spin) : twist T σ = Matrix.diagonal (twistDiag_dev T σ) :=
  rfl

theorem phase_mul_star_dev (T : Torus) (x : ℂ) (hx : star x = x) :
    Complex.exp (2 * π * I * x / (T.Nφ : ℂ)) * star (Complex.exp (2 * π * I * x / (T.Nφ : ℂ))) = 1 := by
  rw [mul_comm]
  exact star_phase_mul_self T x hx

theorem twistSum_star_dev (T : Torus) (σ : Spin) (m : Conf (ZMod T.Nφ)) :
    star (∑ j : ZMod T.Nφ, if m (j, σ) = true then (j.val : ℂ) else 0) =
      ∑ j : ZMod T.Nφ, if m (j, σ) = true then (j.val : ℂ) else 0 := by
  rw [star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact star_natCast _
  · exact star_zero _

theorem twistDiag_mul_star_dev (T : Torus) (σ : Spin) (m : Conf (ZMod T.Nφ)) :
    twistDiag_dev T σ m * star (twistDiag_dev T σ m) = 1 :=
  phase_mul_star_dev T _ (twistSum_star_dev T σ m)

theorem twistPhi_mul_star_dev (T : Torus) (σ : Spin) (μ : Modes T) :
    twistPhi_dev T σ μ * star (twistPhi_dev T σ μ) = 1 := by
  unfold twistPhi_dev
  split_ifs
  · exact phase_mul_star_dev T _ (star_natCast _)
  · simp

theorem twistDiag_vac_dev (T : Torus) (σ : Spin) : twistDiag_dev T σ vac = 1 := by
  simp [twistDiag_dev, vac]

theorem twistSum_update_dev (T : Torus) (σ : Spin) (μ : Modes T) (m : Conf (ZMod T.Nφ)) (hm : m μ = true) :
    (∑ j : ZMod T.Nφ, if m (j, σ) = true then (j.val : ℂ) else 0) =
      (∑ j : ZMod T.Nφ, if Function.update m μ false (j, σ) = true then (j.val : ℂ) else 0) +
        (if μ.2 = σ then (μ.1.val : ℂ) else 0) := by
  obtain ⟨i, τ⟩ := μ
  by_cases hτ : τ = σ
  · subst hτ
    rw [ite_eq_left rfl, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      Function.update_self]
    simp only [hm, ite_true, Bool.false_eq_true, ite_false, zero_add]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (by intro h; exact Finset.ne_of_mem_erase hk (Prod.ext_iff.1 h).1)]
  · rw [ite_eq_right hτ, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Function.update_of_ne (by intro h; exact hτ ((Prod.ext_iff.1 h).2).symm)]

theorem twistDiag_update_dev (T : Torus) (σ : Spin) (μ : Modes T) (m : Conf (ZMod T.Nφ)) (hm : m μ = true) :
    twistDiag_dev T σ (Function.update m μ false) * star (twistDiag_dev T σ m) = star (twistPhi_dev T σ μ) := by
  have hS := twistSum_update_dev T σ μ m hm
  have hSr := twistSum_star_dev T σ m
  unfold twistDiag_dev twistPhi_dev
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  set S := ∑ j : ZMod T.Nφ, if m (j, σ) = true then (j.val : ℂ) else 0 with hSdef
  set S' := ∑ j : ZMod T.Nφ, if Function.update m μ false (j, σ) = true then (j.val : ℂ) else 0 with hS'def
  have hSr' : (starRingEnd ℂ) S = S := by
    rw [← Complex.star_def]
    exact hSr
  have hconj : (starRingEnd ℂ) (2 * π * I * S / (T.Nφ : ℂ)) = -(2 * π * I * S / (T.Nφ : ℂ)) := by
    rw [map_div₀, map_mul, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast, hSr']
    simp only [map_ofNat]
    ring
  rw [hconj]
  split_ifs with hτ
  · rw [← Complex.exp_conj, map_div₀, map_mul, map_mul, map_mul, Complex.conj_I,
      Complex.conj_ofReal, Complex.conj_natCast, Complex.conj_natCast, hS, ite_eq_left hτ]
    simp only [map_ofNat]
    congr 1
    ring
  · rw [hS, ite_eq_right hτ, add_zero, add_neg_cancel, Complex.exp_zero, map_one]

theorem twist_conjT_c_dev (T : Torus) (σ : Spin) (μ : Modes T) :
    (twist T σ)ᴴ * Fermion.Pilot.JW.c μ * twist T σ = twistPhi_dev T σ μ • Fermion.Pilot.JW.c μ := by
  have e1 : (twist T σ)ᴴ = Matrix.diagonal (star (twistDiag_dev T σ)) := by
    rw [twist_eq_diagonal_dev, Matrix.diagonal_conjTranspose]
  have e2 : twist T σ = (Matrix.diagonal (star (twistDiag_dev T σ)))ᴴ := by
    rw [Matrix.diagonal_conjTranspose, star_star, twist_eq_diagonal_dev]
  rw [e1, e2]
  apply Fermion.Pilot.JW.diagonal_mul_c_mul_conjTranspose
  intro m hm
  have h := twistDiag_update_dev T σ μ m hm
  rw [Pi.star_apply, Pi.star_apply, star_star]
  have h2 := congrArg star h
  rw [star_mul', star_star, star_star] at h2
  exact h2

theorem exp_diagonal_dev (T : Torus) (v : Conf (ZMod T.Nφ) → ℂ) :
    NormedSpace.exp (Matrix.diagonal v : FockOp T) = Matrix.diagonal fun m => Complex.exp (v m) := by
  let _ : NormedAlgebra ℚ ℂ := NormedAlgebra.restrictScalars ℚ ℂ ℂ
  rw [Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext m
  rw [← Complex.exp_eq_exp_ℂ]

theorem smul_sum_njs_dev (T : Torus) (σ : Spin) (c : ZMod T.Nφ → ℂ) (a : ℂ) :
    a • ∑ j : ZMod T.Nφ, c j • njs T j σ =
      Matrix.diagonal fun m => a * ∑ j : ZMod T.Nφ, if m (j, σ) = true then c j else 0 := by
  ext m m'
  simp only [Matrix.smul_apply, Matrix.sum_apply, njs_eq_diag, Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : m = m'
  · subst h
    simp only [ite_true]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · simp [h]

theorem exp_smul_sum_njs_dev (T : Torus) (σ : Spin) (c : ZMod T.Nφ → ℂ) (a : ℂ) :
    NormedSpace.exp (a • ∑ j : ZMod T.Nφ, c j • njs T j σ) =
      Matrix.diagonal fun m => Complex.exp (a * ∑ j : ZMod T.Nφ, if m (j, σ) = true then c j else 0) := by
  rw [smul_sum_njs_dev, exp_diagonal_dev]

theorem exp_smul_Nsig_dev (T : Torus) (σ : Spin) (a : ℂ) :
    NormedSpace.exp (a • Nsig T σ) = Matrix.diagonal fun m => Complex.exp (a * (ctσ T σ m : ℂ)) := by
  rw [Nsig_eq_diag, ← Matrix.diagonal_smul, exp_diagonal_dev]
  rfl

theorem twist_eq_exp_lift_dev (T : Torus) (σ : Spin) (r : ZMod T.Nφ → ℤ) (hr : ∀ j, ((r j : ℤ) : ZMod T.Nφ) = j) :
    twist T σ = NormedSpace.exp ((2 * π * I / (T.Nφ : ℂ)) • ∑ j : ZMod T.Nφ, ((r j : ℤ) : ℂ) • njs T j σ) := by
  rw [exp_smul_sum_njs_dev, twist_eq_diagonal_dev]
  congr 1
  funext m
  unfold twistDiag_dev
  have hq : ∀ j : ZMod T.Nφ, ∃ q : ℤ, r j = (j.val : ℤ) + (T.Nφ : ℤ) * q := by
    intro j
    have h1 : ((j.val : ℤ) : ZMod T.Nφ) = ((r j : ℤ) : ZMod T.Nφ) := by
      rw [hr, Int.cast_natCast, ZMod.natCast_zmod_val]
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
    exact ⟨q, by linarith⟩
  choose q hq using hq
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(∑ j : ZMod T.Nφ, if m (j, σ) = true then q j else 0), ?_⟩
  have hN : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
  have hsum : (∑ j : ZMod T.Nφ, if m (j, σ) = true then ((r j : ℤ) : ℂ) else 0) =
      (∑ j : ZMod T.Nφ, if m (j, σ) = true then (j.val : ℂ) else 0) +
        (T.Nφ : ℂ) * ((∑ j : ZMod T.Nφ, if m (j, σ) = true then q j else 0 : ℤ) : ℂ) := by
    rw [Int.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [hq j]
      push_cast
      ring
    · simp
  rw [hsum]
  push_cast
  field_simp
  ring

/-- **Lemma D.3**, the definition: "`\mathcal W_\sigma:=\exp\Bigl(\frac{2\pi\iu}{\Nphi}\sum_{j=0}^{\Nphi-1}j\,n_{[j]\sigma}\Bigr).`"
— the paper's definition as a statement (Mathlib's `NormedSpace.exp` on the operators, the sum over the integers
`j = 0, …, N_φ − 1` with `n_{[j]σ}`). -/
theorem twist_eq_exp (T : Torus) (σ : Spin) :
    twist T σ = NormedSpace.exp ((2 * π * I / (T.Nφ : ℂ)) •
      ∑ j ∈ Finset.range T.Nφ, ((j : ℕ) : ℂ) • njs T ((j : ℕ) : ZMod T.Nφ) σ) := by
  have hre : (∑ j ∈ Finset.range T.Nφ, ((j : ℕ) : ℂ) • njs T ((j : ℕ) : ZMod T.Nφ) σ) =
      ∑ j : ZMod T.Nφ, (((j.val : ℕ) : ℤ) : ℂ) • njs T j σ := by
    refine Finset.sum_nbij' (fun a => (a : ZMod T.Nφ)) (fun k => k.val) (fun a _ => Finset.mem_univ _)
      (fun k _ => Finset.mem_range.2 (ZMod.val_lt k)) (fun a ha => ZMod.val_cast_of_lt (Finset.mem_range.1 ha))
      (fun k _ => ZMod.natCast_zmod_val k) (fun a ha => ?_)
    rw [Int.cast_natCast, ZMod.val_cast_of_lt (Finset.mem_range.1 ha)]
  rw [hre]
  exact twist_eq_exp_lift_dev T σ (fun j => (j.val : ℤ)) fun j => by rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- **Lemma D.3(i)**: "`$\mathcal W_\sigma$ is unitary`". -/
theorem twist_mem_unitary (T : Torus) (σ : Spin) : twist T σ ∈ unitary (FockOp T) := by
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, twist_eq_diagonal_dev]
  exact ⟨Fermion.Pilot.JW.diagonal_conjTranspose_mul_diagonal (twistDiag_mul_star_dev T σ),
    Fermion.Pilot.JW.diagonal_mul_diagonal_conjTranspose (twistDiag_mul_star_dev T σ)⟩

/-- **Lemma D.3(i)**: "`and diagonal in the occupation-number basis`" (by the definition; written out). -/
theorem twist_isDiag (T : Torus) (σ : Spin) : (twist T σ).IsDiag :=
  Matrix.isDiag_diagonal _

/-- **Lemma D.3(i)**: "`it commutes with $\Nup$, $\Ndn$ and the other twist`" — with `N_↑` and `N_↓`. -/
theorem twist_commute_Nsig (T : Torus) (σ τ : Spin) : Commute (twist T σ) (Nsig T τ) := by
  rw [Nsig_eq_diag]
  exact commute_diagonal_diagonal _ _

/-- **Lemma D.3(i)**: "`it commutes with $\Nup$, $\Ndn$ and the other twist`" — with the other twist. -/
theorem twist_commute_twist (T : Torus) : Commute (twist T .up) (twist T .dn) := by
  exact commute_diagonal_diagonal _ _

/-- **Lemma D.3(i)**: "`so it maps every sector into itself`" — sector-preserving (Definition 2.5). -/
theorem twist_isSectorPreserving (T : Torus) (σ : Spin) : IsSectorPreserving T (twist T σ) := by
  exact ⟨twist_commute_Nsig T σ .up, twist_commute_Nsig T σ .dn⟩

/-- **Lemma D.3(i)**: "`so it maps every sector into itself`" (one line from `twist_isSectorPreserving` and block D's
`toCLM_mem_sector_dev`; written out). -/
theorem twist_mem_sector (T : Torus) (σ : Spin) (nn : SectorLabel T) {v : FockSpace T} (hv : v ∈ sector T nn) :
    toCLM T (twist T σ) v ∈ sector T nn :=
  toCLM_mem_sector_dev (twist_isSectorPreserving T σ) nn hv

/-- **Lemma D.3(i)**: "`and it does not change if the representatives $0,\dots,\Nphi-1$ of the classes in $\Z_{\Nphi}$ are replaced by any other representatives.`"
— for any lift `r : ℤ_{N_φ} → ℤ` of the classes, the exponential with the representatives `r j` is `𝒲_σ`. -/
theorem twist_eq_exp_lift (T : Torus) (σ : Spin) (r : ZMod T.Nφ → ℤ) (hr : ∀ j, ((r j : ℤ) : ZMod T.Nφ) = j) :
    twist T σ = NormedSpace.exp ((2 * π * I / (T.Nφ : ℂ)) • ∑ j : ZMod T.Nφ, ((r j : ℤ) : ℂ) • njs T j σ) := by
  exact twist_eq_exp_lift_dev T σ r hr

/-- **Lemma D.3(ii)**: "`For every $j\in\Z_{\Nphi}$, $\mathcal W_\sigma^*c_{j\sigma}\mathcal W_\sigma=e^{2\pi\iu j/\Nphi}c_{j\sigma}$`"
(the phase with `j.val`, as `thy_orb`'s). -/
theorem twist_conj_cjs (T : Torus) (σ : Spin) (j : ZMod T.Nφ) :
    (twist T σ)ᴴ * cjs T j σ * twist T σ = Complex.exp (2 * π * I * (j.val : ℂ) / (T.Nφ : ℂ)) • cjs T j σ := by
  rw [cjs_eq, twist_conjT_c_dev, twistPhi_dev, ite_eq_left rfl]

/-- **Lemma D.3(ii)**: "`$\mathcal W_\sigma^*c_{j\sigma'}\mathcal W_\sigma=c_{j\sigma'}$ for $\sigma'\ne\sigma$.`" -/
theorem twist_conj_cjs_of_ne (T : Torus) {σ σ' : Spin} (h : σ' ≠ σ) (j : ZMod T.Nφ) :
    (twist T σ)ᴴ * cjs T j σ' * twist T σ = cjs T j σ' := by
  rw [cjs_eq, twist_conjT_c_dev, twistPhi_dev, ite_eq_right h, one_smul]

/-! ### Proof devices for Lemma D.3(iii) (proof phase, round one; not statements of the paper)

The paper's proof: conjugation by the unitary `Θ` commutes with the exponential (Mathlib's `Matrix.exp_conj'`),
`Θ^* n_{jσ} Θ = n_{j+1,σ}` (block A's `Θ_conj_njs`), the sum is re-indexed by `j ↦ j + 1`, and the representatives
`(k − 1).val + 1` of the classes `k` (`lift_shift_dev`) give `𝒲_σ` again by `twist_eq_exp_lift_dev`, the rest being
`−N_σ`; the two diagonal exponentials multiply (`exp_add_diagonal_dev`). -/

theorem Θ_isUnit_dev (T : Torus) : IsUnit (Θ T) :=
  ⟨Unitary.toUnits ⟨Θ T, Θ_mem_unitary T⟩, rfl⟩

theorem Θ_inv_dev (T : Torus) : (Θ T)⁻¹ = (Θ T)ᴴ :=
  Matrix.inv_eq_left_inv (conjTranspose_mul_self_of_mem_unitary (Θ_mem_unitary T))

theorem Θ_conj_exp_dev (T : Torus) (A : FockOp T) :
    (Θ T)ᴴ * NormedSpace.exp A * Θ T = NormedSpace.exp ((Θ T)ᴴ * A * Θ T) := by
  let _ : NormedAlgebra ℚ ℂ := NormedAlgebra.restrictScalars ℚ ℂ ℂ
  rw [← Θ_inv_dev]
  exact (Matrix.exp_conj' (Θ T) A (Θ_isUnit_dev T)).symm

theorem lift_shift_dev (T : Torus) (k : ZMod T.Nφ) : (((((k - 1).val : ℕ) : ℤ) + 1 : ℤ) : ZMod T.Nφ) = k := by
  push_cast
  rw [ZMod.natCast_zmod_val]
  ring

theorem conj_sum_njs_dev (T : Torus) (σ : Spin) (a : ℂ) :
    (Θ T)ᴴ * (a • ∑ j : ZMod T.Nφ, (((j.val : ℕ) : ℤ) : ℂ) • njs T j σ) * Θ T =
      (-a) • Nsig T σ + a • ∑ j : ZMod T.Nφ, (((((j - 1).val : ℕ) : ℤ) + 1 : ℤ) : ℂ) • njs T j σ := by
  have e1 : (Θ T)ᴴ * (a • ∑ j : ZMod T.Nφ, (((j.val : ℕ) : ℤ) : ℂ) • njs T j σ) * Θ T =
      a • ∑ j : ZMod T.Nφ, (((j.val : ℕ) : ℤ) : ℂ) • njs T (j + 1) σ := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, Θ_conj_njs]
  have e2 : (∑ j : ZMod T.Nφ, (((j.val : ℕ) : ℤ) : ℂ) • njs T (j + 1) σ) =
      ∑ k : ZMod T.Nφ, ((((k - 1).val : ℕ) : ℤ) : ℂ) • njs T k σ := by
    rw [← Equiv.sum_comp (Equiv.addRight 1) (fun k : ZMod T.Nφ => ((((k - 1).val : ℕ) : ℤ) : ℂ) • njs T k σ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [e1, e2, Nsig]
  simp only [Int.cast_add, Int.cast_one, add_smul, one_smul, Finset.sum_add_distrib, smul_add, neg_smul]
  abel

theorem exp_add_diagonal_dev (T : Torus) (a b : Conf (ZMod T.Nφ) → ℂ) :
    NormedSpace.exp (Matrix.diagonal a + Matrix.diagonal b : FockOp T) =
      NormedSpace.exp (Matrix.diagonal a : FockOp T) * NormedSpace.exp (Matrix.diagonal b : FockOp T) := by
  rw [Matrix.diagonal_add, exp_diagonal_dev, exp_diagonal_dev, exp_diagonal_dev, Matrix.diagonal_mul_diagonal]
  congr 1
  funext m
  exact Complex.exp_add _ _

/-- **Lemma D.3(iii)**: "`$\Theta^*\mathcal W_\sigma\Theta=e^{-2\pi\iu N_\sigma/\Nphi}\mathcal W_\sigma$.`" — as operators,
`e^{−2πiN_σ/N_φ}` Mathlib's `NormedSpace.exp`. -/
theorem twist_conj_Θ (T : Torus) (σ : Spin) :
    (Θ T)ᴴ * twist T σ * Θ T = NormedSpace.exp ((-(2 * π * I / (T.Nφ : ℂ))) • Nsig T σ) * twist T σ := by
  have hW := twist_eq_exp_lift_dev T σ (fun j => (j.val : ℤ)) fun j => by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hW' := twist_eq_exp_lift_dev T σ (fun k => (((k - 1).val : ℕ) : ℤ) + 1) (lift_shift_dev T)
  conv_lhs => rw [hW, Θ_conj_exp_dev, conj_sum_njs_dev, Nsig_eq_diag, ← Matrix.diagonal_smul, smul_sum_njs_dev,
    exp_add_diagonal_dev, ← smul_sum_njs_dev, ← hW']
  rw [Nsig_eq_diag, ← Matrix.diagonal_smul]

/-! ### Proof devices for the consequences of Lemma D.3(iii) (proof phase, round one; not statements of the paper)

On a sector the diagonal `e^{c N_σ}` acts by `e^{c n_σ}` (`exp_Nsig_sector_dev`); it commutes with the sector-preserving
`Θ` (`commute_diag_ct_dev`), so (iii) gives `Θ 𝒲_σ Θ^* = e^{2πiN_σ/N_φ} 𝒲_σ` (`Θ_twist_conj_inv_dev`), and
`Θ (X v) = (Θ X Θ^*)(Θ v)` (`toCLM_conj_apply_dev`). -/

theorem toCLM_mul_dev (T : Torus) (X Y : FockOp T) : toCLM T (X * Y) = toCLM T X * toCLM T Y :=
  map_mul (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) X Y

theorem toCLM_diagonal_apply_dev (T : Torus) (d : Conf (ZMod T.Nφ) → ℂ) (w : FockSpace T) (m : Conf (ZMod T.Nφ)) :
    toCLM T (Matrix.diagonal d) w m = d m * w m := by
  show (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (Matrix.diagonal d) w).ofLp m = _
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]

theorem toCLM_diagonal_sector_dev (T : Torus) (nn : SectorLabel T) (d : Conf (ZMod T.Nφ) → ℂ) (z : ℂ)
    (hd : ∀ m, secOf T m = nn → d m = z) {w : FockSpace T} (hw : w ∈ sector T nn) :
    toCLM T (Matrix.diagonal d) w = z • w := by
  refine PiLp.ext fun m => ?_
  rw [toCLM_diagonal_apply_dev, PiLp.smul_apply, smul_eq_mul]
  by_cases h : w m = 0
  · rw [h, mul_zero, mul_zero]
  · rw [hd m ((mem_sector_iff T nn w).1 hw m h)]

theorem ctσ_of_secOf_dev (T : Torus) (nn : SectorLabel T) (m : Conf (ZMod T.Nφ)) (h : secOf T m = nn) (σ : Spin) :
    ctσ T σ m = secN nn σ := by
  have h1 := (secOf_eq_iff T m nn).1 h
  cases σ
  · exact h1.1
  · exact h1.2

theorem exp_Nsig_sector_dev (T : Torus) (σ : Spin) (a : ℂ) (nn : SectorLabel T) {w : FockSpace T}
    (hw : w ∈ sector T nn) :
    toCLM T (NormedSpace.exp (a • Nsig T σ)) w = Complex.exp (a * (secN nn σ : ℂ)) • w := by
  rw [exp_smul_Nsig_dev]
  exact toCLM_diagonal_sector_dev T nn _ _ (fun m hm => by rw [ctσ_of_secOf_dev T nn m hm σ]) hw

theorem commute_diag_ct_dev (T : Torus) {A : FockOp T} (hA : IsSectorPreserving T A) (σ : Spin) (g : ℕ → ℂ) :
    Commute A (Matrix.diagonal fun m => g (ctσ T σ m)) := by
  rw [commute_diagonal_iff]
  intro i j
  by_cases h : A i j = 0
  · simp [h]
  · have hs := (isSectorPreserving_iff_entries T A).1 hA i j h
    have h1 := (secOf_eq_iff T i (secOf T j)).1 hs
    have hc : ctσ T σ i = ctσ T σ j := by
      cases σ
      · exact h1.1
      · exact h1.2
    rw [hc, mul_comm]

theorem Θ_twist_conj_inv_dev (T : Torus) (σ : Spin) :
    Θ T * twist T σ * (Θ T)ᴴ = NormedSpace.exp ((2 * π * I / (T.Nφ : ℂ)) • Nsig T σ) * twist T σ := by
  have hE := exp_smul_Nsig_dev T σ (-(2 * π * I / (T.Nφ : ℂ)))
  have hF := exp_smul_Nsig_dev T σ (2 * π * I / (T.Nφ : ℂ))
  have hFE : NormedSpace.exp ((2 * π * I / (T.Nφ : ℂ)) • Nsig T σ) *
      NormedSpace.exp ((-(2 * π * I / (T.Nφ : ℂ))) • Nsig T σ) = 1 := by
    rw [hE, hF, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext m
    rw [← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero]
  have hcomm : Commute (Θ T) (NormedSpace.exp ((-(2 * π * I / (T.Nφ : ℂ))) • Nsig T σ)) := by
    rw [hE]
    exact commute_diag_ct_dev T (Θ_isSectorPreserving T) σ fun n => Complex.exp ((-(2 * π * I / (T.Nφ : ℂ))) * (n : ℂ))
  have hiii := twist_conj_Θ T σ
  have hu2 : Θ T * (Θ T)ᴴ = 1 := mul_conjTranspose_self_of_mem_unitary (Θ_mem_unitary T)
  set F := NormedSpace.exp ((2 * π * I / (T.Nφ : ℂ)) • Nsig T σ) with hFdef
  set E := NormedSpace.exp ((-(2 * π * I / (T.Nφ : ℂ))) • Nsig T σ) with hEdef
  calc Θ T * twist T σ * (Θ T)ᴴ = F * E * (Θ T * twist T σ * (Θ T)ᴴ) := by rw [hFE, one_mul]
    _ = F * ((E * Θ T) * twist T σ * (Θ T)ᴴ) := by simp only [mul_assoc]
    _ = F * (Θ T * (E * twist T σ) * (Θ T)ᴴ) := by rw [← hcomm.eq]; simp only [mul_assoc]
    _ = F * (Θ T * ((Θ T)ᴴ * twist T σ * Θ T) * (Θ T)ᴴ) := by rw [hiii]
    _ = F * twist T σ := by
        rw [show Θ T * ((Θ T)ᴴ * twist T σ * Θ T) * (Θ T)ᴴ = (Θ T * (Θ T)ᴴ) * twist T σ * (Θ T * (Θ T)ᴴ) by
          simp only [mul_assoc], hu2, one_mul, mul_one]

theorem toCLM_conj_apply_dev (T : Torus) (X : FockOp T) (v : FockSpace T) :
    toCLM T (Θ T) (toCLM T X v) = toCLM T (Θ T * X * (Θ T)ᴴ) (toCLM T (Θ T) v) := by
  have hu1 : (Θ T)ᴴ * Θ T = 1 := conjTranspose_mul_self_of_mem_unitary (Θ_mem_unitary T)
  have h : Θ T * X * (Θ T)ᴴ * Θ T = Θ T * X := by rw [mul_assoc, hu1, mul_one]
  calc toCLM T (Θ T) (toCLM T X v) = toCLM T (Θ T * X) v := by rw [toCLM_mul_dev, mul_apply_eq_comp]
    _ = toCLM T (Θ T * X * (Θ T)ᴴ * Θ T) v := by rw [h]
    _ = _ := by rw [toCLM_mul_dev T (Θ T * X * (Θ T)ᴴ) (Θ T), mul_apply_eq_comp]

theorem star_exp_phase_dev (T : Torus) (n : ℕ) :
    star (Complex.exp ((2 * π * I / (T.Nφ : ℂ)) * (n : ℂ))) = Complex.exp (-((2 * π * I / (T.Nφ : ℂ)) * (n : ℂ))) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_div₀, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast,
    Complex.conj_natCast]
  simp only [map_ofNat]
  ring

theorem twistDn_conjT_isSectorPreserving_dev (T : Torus) : IsSectorPreserving T (twist T .dn)ᴴ :=
  ⟨by rw [twist_eq_diagonal_dev, Matrix.diagonal_conjTranspose, Nsig_eq_diag]; exact commute_diagonal_diagonal _ _,
    by rw [twist_eq_diagonal_dev, Matrix.diagonal_conjTranspose, Nsig_eq_diag]; exact commute_diagonal_diagonal _ _⟩

/-- **Lemma D.3(iii)** on every sector: "`$\Theta^*\mathcal W_\sigma\Theta=e^{-2\pi\iu N_\sigma/\Nphi}\mathcal W_\sigma$.`" —
on `v ∈ 𝓗^𝐧`, `Θ^* 𝒲_σ Θ v = e^{−2πi n_σ/N_φ} 𝒲_σ v`. -/
theorem twist_conj_Θ_sector (T : Torus) (σ : Spin) (nn : SectorLabel T) {v : FockSpace T} (hv : v ∈ sector T nn) :
    toCLM T ((Θ T)ᴴ * twist T σ * Θ T) v =
      Complex.exp (-(2 * π * I * (secN nn σ : ℂ) / (T.Nφ : ℂ))) • toCLM T (twist T σ) v := by
  rw [twist_conj_Θ, toCLM_mul_dev, mul_apply_eq_comp, exp_Nsig_sector_dev T σ _ nn (twist_mem_sector T σ nn hv)]
  congr 2
  ring

/-- **Lemma D.3(iii)**: "`Consequently, if $\Upsilon\in\sect\nn$, $\nn=(n_\up,n_\dn)$, and $\Theta\Upsilon=\mu\Upsilon$, then`"
"`\Theta\mathcal W_\up\Upsilon=e^{2\pi\iu n_\up/\Nphi}\mu\,\mathcal W_\up\Upsilon`" -/
theorem Θ_twist_eigen (T : Torus) (nn : SectorLabel T) {Υ : FockSpace T} (hΥ : Υ ∈ sector T nn) {μ : ℂ}
    (hμ : toCLM T (Θ T) Υ = μ • Υ) :
    toCLM T (Θ T) (toCLM T (twist T .up) Υ) =
      (Complex.exp (2 * π * I * ((nn.1 : ℕ) : ℂ) / (T.Nφ : ℂ)) * μ) • toCLM T (twist T .up) Υ := by
  rw [toCLM_conj_apply_dev, Θ_twist_conj_inv_dev, hμ, map_smul, toCLM_mul_dev, mul_apply_eq_comp,
    exp_Nsig_sector_dev T .up _ nn (twist_mem_sector T .up nn hΥ), smul_smul]
  congr 1
  rw [mul_comm]
  congr 2
  simp only [secN]
  ring

/-- **Lemma D.3(iii)**: "`Consequently, if $\Upsilon\in\sect\nn$, $\nn=(n_\up,n_\dn)$, and $\Theta\Upsilon=\mu\Upsilon$, then`"
"`\Theta\mathcal W_\up\mathcal W_\dn^*\Upsilon=e^{2\pi\iu(n_\up-n_\dn)/\Nphi}\mu\,\mathcal W_\up\mathcal W_\dn^*\Upsilon`" -/
theorem Θ_twistTwo_eigen (T : Torus) (nn : SectorLabel T) {Υ : FockSpace T} (hΥ : Υ ∈ sector T nn) {μ : ℂ}
    (hμ : toCLM T (Θ T) Υ = μ • Υ) :
    toCLM T (Θ T) (toCLM T (twistTwo T) Υ) =
      (Complex.exp (2 * π * I * (((nn.1 : ℕ) : ℂ) - ((nn.2 : ℕ) : ℂ)) / (T.Nφ : ℂ)) * μ) •
        toCLM T (twistTwo T) Υ := by
  have hu1 : (Θ T)ᴴ * Θ T = 1 := conjTranspose_mul_self_of_mem_unitary (Θ_mem_unitary T)
  have hsplit : Θ T * twistTwo T * (Θ T)ᴴ =
      (Θ T * twist T .up * (Θ T)ᴴ) * (Θ T * twist T .dn * (Θ T)ᴴ)ᴴ := by
    rw [twistTwo]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]
    rw [← mul_assoc (Θ T)ᴴ (Θ T), hu1, one_mul]
  have hdn : toCLM T (NormedSpace.exp ((2 * π * I / (T.Nφ : ℂ)) • Nsig T .dn))ᴴ Υ =
      star (Complex.exp ((2 * π * I / (T.Nφ : ℂ)) * ((nn.2 : ℕ) : ℂ))) • Υ := by
    rw [exp_smul_Nsig_dev, Matrix.diagonal_conjTranspose]
    exact toCLM_diagonal_sector_dev T nn _ _ (fun m hm => by
      rw [Pi.star_apply, ctσ_of_secOf_dev T nn m hm .dn]
      rfl) hΥ
  have hmem : toCLM T (twist T .up) (toCLM T (twist T .dn)ᴴ Υ) ∈ sector T nn :=
    twist_mem_sector T .up nn (toCLM_mem_sector_dev (twistDn_conjT_isSectorPreserving_dev T) nn hΥ)
  rw [toCLM_conj_apply_dev, hsplit, Θ_twist_conj_inv_dev, Θ_twist_conj_inv_dev, Matrix.conjTranspose_mul, hμ,
    map_smul]
  simp only [toCLM_mul_dev, mul_apply_eq_comp]
  rw [hdn, map_smul, map_smul, map_smul, exp_Nsig_sector_dev T .up _ nn hmem, smul_smul, smul_smul, twistTwo,
    toCLM_mul_dev, mul_apply_eq_comp, star_exp_phase_dev]
  congr 1
  simp only [secN]
  rw [mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  ring

/-! ### Proof devices for Lemma D.3(iv) and the remark after it (proof phase, round one; not statements of the paper)

The one-body matrices are diagonal in the basis `ψ_j ⊗ τ` (`twistOneBody_eq_diagonal_dev`, `thyKron_eq_diagonal_dev`);
a diagonal many-body unitary fixing the vacuum, whose entries change by the phase `φ_μ` when the mode `μ` is emptied, is
block A's `Ff` of the diagonal `φ` (`diag_eq_Ff_dev`, through block A's uniqueness `Ff_unique`: its conjugation sends
`c(f)` to `c(φ f)`). -/

theorem twistOneBody_eq_diagonal_dev (T : Torus) (σ : Spin) :
    twistOneBody T σ = Matrix.diagonal (twistPhi_dev T σ) := by
  ext ⟨i, τ⟩ ⟨k, ρ⟩
  cases τ <;> cases ρ <;> cases σ <;> by_cases h1 : i = k <;> simp [twistOneBody, thyMat, twistPhi_dev, h1]

theorem thyKron_eq_diagonal_dev (T : Torus) :
    Matrix.kronecker (thyMat T) (1 : Matrix Spin Spin ℂ) =
      Matrix.diagonal (fun μ : Modes T => Complex.exp (2 * π * I * (μ.1.val : ℂ) / (T.Nφ : ℂ))) := by
  ext ⟨i, τ⟩ ⟨k, ρ⟩
  cases τ <;> cases ρ <;> by_cases h1 : i = k <;> simp [thyMat, h1]

theorem diag_eq_Ff_dev (T : Torus) (d : Conf (ZMod T.Nφ) → ℂ) (φ : Modes T → ℂ)
    (hd : ∀ m, d m * star (d m) = 1) (hφ : ∀ μ, φ μ * star (φ μ) = 1) (hvac : d vac = 1)
    (hph : ∀ (μ : Modes T) (m : Conf (ZMod T.Nφ)), m μ = true →
      d (Function.update m μ false) * star (d m) = star (φ μ)) :
    Matrix.diagonal d = Ff T (Matrix.diagonal φ) := by
  have hu : Matrix.diagonal φ ∈ unitary (Matrix (Modes T) (Modes T) ℂ) := by
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    constructor
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext μ
      rw [Pi.star_apply, mul_comm, hφ]
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext μ
      rw [Pi.star_apply, hφ]
  have hW : Matrix.diagonal d ∈ unitary (FockOp T) := by
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
    exact ⟨Fermion.Pilot.JW.diagonal_conjTranspose_mul_diagonal hd,
      Fermion.Pilot.JW.diagonal_mul_diagonal_conjTranspose hd⟩
  refine Ff_unique T hu hW (fun f => ?_) ?_
  · have hc : ∀ μ : Modes T, Matrix.diagonal d * Fermion.Pilot.JW.c μ * (Matrix.diagonal d)ᴴ =
        star (φ μ) • Fermion.Pilot.JW.c μ :=
      fun μ => Fermion.Pilot.JW.diagonal_mul_c_mul_conjTranspose fun m hm => hph μ m hm
    simp only [cf, cVec, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hc, smul_smul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal, star_mul', mul_comm]
  · funext m
    rw [Matrix.mulVec_diagonal]
    by_cases h : m = vac
    · subst h
      simp [hvac]
    · simp [h]

/-- **Lemma D.3(iv)**, the proof: "`Let $u$ be the unitary on $\kN$ in the parentheses.`" -/
theorem twistOneBody_mem_unitary (T : Torus) (σ : Spin) :
    twistOneBody T σ ∈ unitary (Matrix (Modes T) (Modes T) ℂ) := by
  rw [twistOneBody_eq_diagonal_dev, Unitary.mem_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  constructor
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext μ
    rw [Pi.star_apply, mul_comm, twistPhi_mul_star_dev]
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext μ
    rw [Pi.star_apply, twistPhi_mul_star_dev]

/-- **Lemma D.3(iv)**: "`the twist $\mathcal W_\sigma$ is the magnetic translation $\thy$ of Lemma~\ref{lem:magtrans}, by $L_y/\Nphi$ along the circumference, applied to the electrons of spin $\sigma$ alone.`"
— the one-body unitary is `θ_y` on `f ⊗ σ` and the identity on `f ⊗ τ`, `τ ≠ σ` (the form of block A's
`thx2_spinTensor`). -/
theorem twistOneBody_spinTensor (T : Torus) (σ τ : Spin) (f : Space T) :
    Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) (twistOneBody T σ) (spinTensor f τ) =
      spinTensor (if τ = σ then thy T f else f) τ := by
  rw [twistOneBody_eq_diagonal_dev]
  refine PiLp.ext fun μ => ?_
  obtain ⟨i, τ'⟩ := μ
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]
  simp only [spinTensor, WithLp.ofLp_toLp, twistPhi_dev]
  by_cases h1 : τ' = τ <;> by_cases h2 : τ = σ
  · subst h1; subst h2; simp [thy_apply]
  · subst h1; simp [h2]
  · simp [h1]
  · simp [h1]

/-- **Lemma D.3(iv)**: "`$\mathcal W_\sigma=\Ff\bigl(\thy\otimes\lvert\sigma\rangle\langle\sigma\rvert+\one\otimes(\one-\lvert\sigma\rangle\langle\sigma\rvert)\bigr)$:`"
— block A's second quantization `Ff`. -/
theorem twist_eq_Ff (T : Torus) (σ : Spin) : twist T σ = Ff T (twistOneBody T σ) := by
  rw [twistOneBody_eq_diagonal_dev, twist_eq_diagonal_dev]
  exact diag_eq_Ff_dev T _ _ (twistDiag_mul_star_dev T σ) (twistPhi_mul_star_dev T σ) (twistDiag_vac_dev T σ)
    (twistDiag_update_dev T σ)

/-- The remark after **Lemma D.3**: "`By (iv), and since $\Ff$ is multiplicative (by the uniqueness in its definition), $\mathcal W_\up\mathcal W_\dn=\Ff(\thy\otimes\one)$ translates all electrons along the circumference`" -/
theorem twist_up_mul_dn (T : Torus) :
    twist T .up * twist T .dn = Ff T (Matrix.kronecker (thyMat T) (1 : Matrix Spin Spin ℂ)) := by
  rw [thyKron_eq_diagonal_dev, twist_eq_diagonal_dev, twist_eq_diagonal_dev, Matrix.diagonal_mul_diagonal]
  refine diag_eq_Ff_dev T _ _ (fun m => ?_) (fun μ => phase_mul_star_dev T _ (star_natCast _))
    (by simp [twistDiag_vac_dev]) (fun μ m hm => ?_)
  · rw [star_mul', mul_mul_mul_comm, twistDiag_mul_star_dev, twistDiag_mul_star_dev, one_mul]
  · rw [star_mul', mul_mul_mul_comm, twistDiag_update_dev T .up μ m hm, twistDiag_update_dev T .dn μ m hm,
      ← star_mul']
    congr 1
    obtain ⟨i, τ⟩ := μ
    cases τ <;> simp [twistPhi_dev]

/-! ## The pair annihilators at distance `d` (the text before Lemma D.4)

"`For $n\in\Z$ and $d\in\N$ with $d\equiv n\pmod2$ put`" — the definitions are made for every `n ∈ ℤ`, `d ∈ ℕ`, with the
orbitals of `bcenTerm`; they are used at `d ≡ n (mod 2)` only. -/

/-- **The text before Lemma D.4**: "`c^\nu_{n,d}:=\cpair\nu\bigl(\psi_{[(n-d)/2]},\psi_{[(n+d)/2]}\bigr)\quad(\nu\in\{+,0,-\})`" -/
def cpairD (T : Torus) (ν : Triplet) (n : ℤ) (d : ℕ) : FockOp T :=
  cpair T ν (orb T (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ)) (orb T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ))

/-- **The text before Lemma D.4**: "`built from the antisymmetric spinor $\chi^{\rm sing}$ with $\chi^{\rm sing}_{\up\dn}=-\chi^{\rm sing}_{\dn\up}=2^{-1/2}$ and zero diagonal`" -/
def chiSing : Matrix Spin Spin ℂ :=
  Matrix.of fun σ σ' => if σ = .up ∧ σ' = .dn then (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    else if σ = .dn ∧ σ' = .up then -(((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0

/-- **The text before Lemma D.4**: "`where $c^{\rm sing}(f,g):=\sum_{\sigma,\sigma'}\overline{\chi^{\rm sing}_{\sigma\sigma'}}\,c(f\otimes\sigma')\,c(g\otimes\sigma)$ is the singlet pair annihilator`"
— the form of block C's `cpair`. -/
def cSing (T : Torus) (f g : Space T) : FockOp T :=
  ∑ σ : Spin, ∑ σ' : Spin, star (chiSing σ σ') • (cf T (spinTensor f σ') * cf T (spinTensor g σ))

/-- **The text before Lemma D.4**: "`c^{\rm sing}_{n,d}:=c^{\rm sing}\bigl(\psi_{[(n-d)/2]},\psi_{[(n+d)/2]}\bigr),`" -/
def cpairSing (T : Torus) (n : ℤ) (d : ℕ) : FockOp T :=
  cSing T (orb T (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ)) (orb T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ))

/-! ### Proof device for the pair annihilators (statement phase; not a statement of the paper): the singlet spinor is
block C's device `PairForm.chiS` ("`(as in the proof of Theorem~\ref{thm:localform})`"), definitionally -/

theorem chiSing_eq_chiS_dev : chiSing = PairForm.chiS :=
  rfl

/-- **The text before Lemma D.4**: "`and $\bcen\nu n=\sum_{d}2d\,e^{-\kappa^2d^2/4}c^\nu_{n,d}$, the sum running over $d\in\N$ with $d\equiv n\pmod2$ (Definition~\ref{def:pairs}).`"
— termwise: `bcenTerm` is the weighted `c^ν_{n,d}` (definitional; written out). -/
theorem bcenTerm_eq_cpairD (T : Torus) (ν : Triplet) (n : ℤ) (d : ℕ) :
    bcenTerm T ν n d = if (d : ℤ) ≡ n [ZMOD 2] then
      ((2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) : ℝ) : ℂ) • cpairD T ν n d else 0 :=
  rfl

/-- **The text before Lemma D.4**: "`and $\bcen\nu n=\sum_{d}2d\,e^{-\kappa^2d^2/4}c^\nu_{n,d}$, the sum running over $d\in\N$ with $d\equiv n\pmod2$ (Definition~\ref{def:pairs}).`"
— the series (definitional; written out). -/
theorem bcen_eq_tsum_cpairD (T : Torus) (ν : Triplet) (n : ℤ) :
    bcen T ν n = ∑' d : ℕ, if (d : ℤ) ≡ n [ZMOD 2] then
      ((2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) : ℝ) : ℂ) • cpairD T ν n d else 0 :=
  rfl

/-- **The text before Lemma D.4**: "`With $j:=[(n-d)/2]$ and $j':=[(n+d)/2]$,`" "`c^+_{n,d}=c_{j\up}c_{j'\up},\qquad c^-_{n,d}=c_{j\dn}c_{j'\dn},`"
"`c^0_{n,d}=2^{-1/2}\bigl(c_{j\dn}c_{j'\up}+c_{j\up}c_{j'\dn}\bigr),\qquad c^{\rm sing}_{n,d}=2^{-1/2}\bigl(c_{j\dn}c_{j'\up}-c_{j\up}c_{j'\dn}\bigr),`" -/
theorem cpairD_eq (T : Torus) (n : ℤ) (d : ℕ) :
    let j : ZMod T.Nφ := ((n - (d : ℤ)) / 2 : ℤ)
    let j' : ZMod T.Nφ := ((n + (d : ℤ)) / 2 : ℤ)
    cpairD T .plus n d = cjs T j .up * cjs T j' .up ∧
      cpairD T .minus n d = cjs T j .dn * cjs T j' .dn ∧
      cpairD T .zero n d =
        (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (cjs T j .dn * cjs T j' .up + cjs T j .up * cjs T j' .dn) ∧
      cpairSing T n d =
        (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (cjs T j .dn * cjs T j' .up - cjs T j .up * cjs T j' .dn) := by
  intro j j'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [cpairD, cpair, chi, cjs, j, j', HRTorus.Fermion.Pilot.JW.sum_spin]
  · simp [cpairD, cpair, chi, cjs, j, j', HRTorus.Fermion.Pilot.JW.sum_spin]
  · simp [cpairD, cpair, chi, cjs, j, j', HRTorus.Fermion.Pilot.JW.sum_spin, smul_add, add_comm]
  · simp [cpairSing, cSing, chiSing, cjs, j, j', HRTorus.Fermion.Pilot.JW.sum_spin, sub_eq_add_neg, add_comm]

/-- "`As in the proof of Proposition~\ref{prop:slotH}(i), $\norm{c^\nu_{n,d}}\le\sqrt2$ and $\norm{c^{\rm sing}_{n,d}}\le\sqrt2$, so all series below converge absolutely in norm.`"
— `‖c^ν_{n,d}‖ ≤ √2` (**the text before Lemma D.4**). -/
theorem norm_cpairD_le (T : Torus) (ν : Triplet) (n : ℤ) (d : ℕ) : ‖toCLM T (cpairD T ν n d)‖ ≤ Real.sqrt 2 := by
  have h1 := norm_cpair_le T ν (orb T (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ))
    (orb T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ))
  simp only [orb, PiLp.norm_single, norm_one, mul_one] at h1
  exact h1

/-! ### Proof devices for the norm of the singlet pair (proof phase, round one; not statements of the paper): block C's
`norm_chatVec_mul_le` for a product of two annihilators of unit vectors -/

theorem toCLM_sub_dev (T : Torus) (X Y : FockOp T) : toCLM T (X - Y) = toCLM T X - toCLM T Y :=
  map_sub (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) X Y

theorem norm_cjs_mul_le_dev (T : Torus) (j j' : ZMod T.Nφ) (σ σ' : Spin) :
    ‖toCLM T (cjs T j σ * cjs T j' σ')‖ ≤ 1 := by
  have h := norm_chatVec_mul_le (S := ZMod T.Nφ) (spinTensor (orb T j) σ) (spinTensor (orb T j') σ')
  rw [norm_spinTensor, norm_spinTensor] at h
  simp only [orb, PiLp.norm_single, norm_one, mul_one] at h
  exact h

/-- "`As in the proof of Proposition~\ref{prop:slotH}(i), $\norm{c^\nu_{n,d}}\le\sqrt2$ and $\norm{c^{\rm sing}_{n,d}}\le\sqrt2$, so all series below converge absolutely in norm.`"
— `‖c^{sing}_{n,d}‖ ≤ √2` (**the text before Lemma D.4**). -/
theorem norm_cpairSing_le (T : Torus) (n : ℤ) (d : ℕ) : ‖toCLM T (cpairSing T n d)‖ ≤ Real.sqrt 2 := by
  have hs : cpairSing T n d = (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      (cjs T (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .dn * cjs T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .up -
        cjs T (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .up * cjs T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .dn) := by
    simp [cpairSing, cSing, chiSing, cjs, HRTorus.Fermion.Pilot.JW.sum_spin, sub_eq_add_neg, add_comm]
  rw [hs, toCLM_smul_dev, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos two_pos _), toCLM_sub_dev]
  calc (2 : ℝ) ^ (-(1 / 2 : ℝ)) * ‖toCLM T (cjs T _ .dn * cjs T _ .up) - toCLM T (cjs T _ .up * cjs T _ .dn)‖
      ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + 1) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (norm_cjs_mul_le_dev T _ _ _ _) (norm_cjs_mul_le_dev T _ _ _ _))
    _ = Real.sqrt 2 := by rw [← two_mul_rpow_neg_half]; ring

/-! ## Lemma D.4: the energy of a twisted zero mode -/

/-- **Lemma D.4**, (D.3): the term of index `d ∈ ℕ` of the inner series at the angle `θd`:
"`2d\,e^{-\kappa^2d^2/4}`" "`\Bigl[\Bigl(\cos\frac{\pi d}\Nphi-1\Bigr)c^0_{n,d}+\iu\sin\frac{\pi d}\Nphi\,c^{\rm sing}_{n,d}\Bigr]`"
with `πd/N_φ` replaced by `θd` (`θ = π/N_φ` for `𝒲_↑`, `θ = 2π/N_φ` for `𝒲_↑𝒲_↓^*`) if `d ≡ n (mod 2)`, and `0`
otherwise (the indexing of `bcenTerm`). -/
def twistTerm (T : Torus) (θ : ℝ) (n : ℤ) (d : ℕ) : FockOp T :=
  if (d : ℤ) ≡ n [ZMOD 2] then
    ((2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) : ℝ) : ℂ) •
      (((Real.cos (θ * d) - 1 : ℝ) : ℂ) • cpairD T .zero n d + (I * ((Real.sin (θ * d) : ℝ) : ℂ)) • cpairSing T n d)
  else 0

/-- **Lemma D.4**, (D.3), the inner series: "`the inner sum running over $d\in\N$ with $d\equiv n\pmod2$`" — the `tsum` of
`twistTerm` over `d ∈ ℕ` (its convergence is `summable_twistTerm`). -/
def twistSum (T : Torus) (θ : ℝ) (n : ℤ) : FockOp T :=
  ∑' d : ℕ, twistTerm T θ n d

/-- **The text before Lemma D.4**: "`so all series below converge absolutely in norm.`" — the inner series of (D.3), absolutely in the operator norm
and in the operators, for every angle. -/
theorem summable_twistTerm (T : Torus) (θ : ℝ) (n : ℤ) :
    Summable (fun d : ℕ => ‖toCLM T (twistTerm T θ n d)‖) ∧ Summable (twistTerm T θ n) := by
  have hκ : 0 < T.κ ^ 2 / 4 := by have := T.κ_pos; positivity
  have hb : ∀ d : ℕ, ‖toCLM T (twistTerm T θ n d)‖ ≤
      2 * (3 * Real.sqrt 2) * ((d : ℝ) ^ 1 * Real.exp (-(T.κ ^ 2 / 4) * d)) := by
    intro d
    unfold twistTerm
    split_ifs
    · rw [toCLM_smul_dev, norm_smul, Complex.norm_real, Real.norm_eq_abs, toCLM_add_dev, toCLM_smul_dev,
        toCLM_smul_dev]
      have hexp : Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) ≤ Real.exp (-(T.κ ^ 2 / 4) * d) := by
        apply Real.exp_le_exp.mpr
        have hd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h | h
          · simp [h]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h
            nlinarith
        have hk : 0 ≤ T.κ ^ 2 := sq_nonneg _
        nlinarith
      have hnn : 0 ≤ 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) := by positivity
      have hin : ‖((Real.cos (θ * d) - 1 : ℝ) : ℂ) • toCLM T (cpairD T .zero n d) +
          (I * ((Real.sin (θ * d) : ℝ) : ℂ)) • toCLM T (cpairSing T n d)‖ ≤ 3 * Real.sqrt 2 := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs]
        have hc : |Real.cos (θ * d) - 1| ≤ 2 := by
          rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos (θ * d), Real.cos_le_one (θ * d)]
        have hs : |Real.sin (θ * d)| ≤ 1 := Real.abs_sin_le_one _
        have h0 := norm_cpairD_le T .zero n d
        have h1 := norm_cpairSing_le T n d
        calc |Real.cos (θ * d) - 1| * ‖toCLM T (cpairD T .zero n d)‖ +
              |Real.sin (θ * d)| * ‖toCLM T (cpairSing T n d)‖
            ≤ 2 * Real.sqrt 2 + 1 * Real.sqrt 2 :=
              add_le_add (mul_le_mul hc h0 (norm_nonneg _) (by norm_num))
                (mul_le_mul hs h1 (norm_nonneg _) (by norm_num))
          _ = 3 * Real.sqrt 2 := by ring
      rw [abs_of_nonneg hnn]
      calc 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) *
            ‖((Real.cos (θ * d) - 1 : ℝ) : ℂ) • toCLM T (cpairD T .zero n d) +
              (I * ((Real.sin (θ * d) : ℝ) : ℂ)) • toCLM T (cpairSing T n d)‖
          ≤ 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) * (3 * Real.sqrt 2) :=
            mul_le_mul_of_nonneg_left hin hnn
        _ ≤ 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 / 4) * d) * (3 * Real.sqrt 2) := by gcongr
        _ = 2 * (3 * Real.sqrt 2) * ((d : ℝ) ^ 1 * Real.exp (-(T.κ ^ 2 / 4) * d)) := by ring
    · rw [toCLM_eq_opCLM, opCLM_zero, norm_zero]; positivity
  have hs : Summable fun d : ℕ => 2 * (3 * Real.sqrt 2) * ((d : ℝ) ^ 1 * Real.exp (-(T.κ ^ 2 / 4) * d)) :=
    (Real.summable_pow_mul_exp_neg_nat_mul 1 hκ).mul_left _
  have h1 : Summable fun d : ℕ => ‖toCLM T (twistTerm T θ n d)‖ :=
    Summable.of_nonneg_of_le (fun d => norm_nonneg _) hb hs
  exact ⟨h1, summable_of_summable_norm_opCLM h1⟩

/-- **Lemma D.4**: "`for any representative of the class $n$; and`" — the inner series is `2N_φ`-periodic in `n`. -/
theorem twistSum_add_two_Nφ (T : Torus) (θ : ℝ) (n : ℤ) :
    twistSum T θ (n + 2 * (T.Nφ : ℤ)) = twistSum T θ n := by
  unfold twistSum
  congr 1
  funext d
  unfold twistTerm cpairD cpairSing
  have hmod : ((d : ℤ) ≡ n + 2 * (T.Nφ : ℤ) [ZMOD 2]) ↔ ((d : ℤ) ≡ n [ZMOD 2]) := by
    simp only [Int.ModEq, Int.add_mul_emod_self_left]
  have e1 : ((n + 2 * (T.Nφ : ℤ) - (d : ℤ)) / 2 : ℤ) = (n - (d : ℤ)) / 2 + T.Nφ := by
    rw [show n + 2 * (T.Nφ : ℤ) - d = (n - d) + T.Nφ * 2 by ring, Int.add_mul_ediv_right _ _ two_ne_zero]
  have e2 : ((n + 2 * (T.Nφ : ℤ) + (d : ℤ)) / 2 : ℤ) = (n + (d : ℤ)) / 2 + T.Nφ := by
    rw [show n + 2 * (T.Nφ : ℤ) + d = (n + d) + T.Nφ * 2 by ring, Int.add_mul_ediv_right _ _ two_ne_zero]
  have hc : ∀ x : ℤ, ((x + (T.Nφ : ℤ) : ℤ) : ZMod T.Nφ) = (x : ZMod T.Nφ) := by
    intro x; push_cast; simp
  simp only [hmod, e1, e2, hc]

/-! ### Proof devices for Lemma D.4 (proof phase, round one; not statements of the paper)

The identity: the twists conjugate each annihilator by a phase (`twistUp_conj_cjs_dev`, `twistTwo_conj_cjs_dev`), hence
each term of `b_ν(n)` (`twistUp_conj_bcenTerm_dev`, `twistTwo_conj_bcenTerm_dev`: the phases `e^{∓iθd}` of the two
orbitals combine into `cos θd` and `i sin θd`, `trig_combo_dev`); the conjugations pass through the `tsum`
(`tsum_conj_dev`, `twistUp_conj_bcen_dev`, `twistTwo_conj_bcen_dev`); `⟨v, Σ A^*A v⟩ = Σ ‖A v‖²` (`inner_smul_sum_dev`)
with `localForm_c` and the positivity of `κ³/√(2π)` gives `H_N Υ = 0 ⇒ b_ν(n) Υ = 0` (`bcen_apply_eq_zero_dev`), and
the identity follows (`energy_identity_dev`). The bound: the weights `twA_dev`, `twB_dev` with `|cos θd − 1| ≤ (θd)²/2`
and `|sin θd| ≤ θd` (`twA_le_dev`, `twB_le_dev`), the Cauchy–Schwarz inequality for nonnegative series (`cs_tsum_dev`),
and the occupation bounds `Σ_{n ≡ d} ‖c^0_{n,d}Υ‖² ≤ N`, `Σ_{n ≡ d} ‖c^{sing}_{n,d}Υ‖² ≤ N` (`occ_sum_dev`). The
occupation bound departs from the route of the paper (`u^*u = n n_2` and `p₁p₂ ≤ (p₁ + p₂)/2`): it uses
`‖c_{jσ} c_{kτ} Υ‖ ≤ ‖c_{kτ} Υ‖` (`‖c_{jσ}‖ ≤ 1`, `norm_cjs_mul_apply_le_dev`), the injective reindexing
`n ↦ k = [(n+d)/2]` (`sum_parity_le_dev`), and `Σ_j (‖c_{j↑}Υ‖² + ‖c_{j↓}Υ‖²) = N` (`sum_norm_cjs_sq_dev`, from the
diagonal `N_σ = Σ_j n_{jσ}`); the constant is the same. -/

theorem toCLM_tsum_apply_dev (T : Torus) {f : ℕ → FockOp T} (hf : Summable f) (v : FockSpace T) :
    toCLM T (∑' d, f d) v = ∑' d, toCLM T (f d) v := by
  let L : FockOp T →ₗ[ℂ] FockSpace T :=
    { toFun := fun A => toCLM T A v
      map_add' := fun A B => by rw [toCLM_add_dev]; rfl
      map_smul' := fun c A => by rw [toCLM_smul_dev]; rfl }
  have hL : Continuous L := L.continuous_of_finiteDimensional
  exact ((hf.hasSum.map L hL).tsum_eq).symm

theorem tsum_conj_dev (T : Torus) (U : FockOp T) {f : ℕ → FockOp T} (hf : Summable f) :
    Uᴴ * (∑' d, f d) * U = ∑' d, Uᴴ * f d * U := by
  rw [← hf.tsum_mul_left, ← (hf.mul_left Uᴴ).tsum_mul_right]

theorem conj_mul_dev (T : Torus) {U : FockOp T} (hU : U * Uᴴ = 1) (X Y : FockOp T) :
    Uᴴ * (X * Y) * U = (Uᴴ * X * U) * (Uᴴ * Y * U) := by
  rw [show Uᴴ * X * U * (Uᴴ * Y * U) = Uᴴ * X * (U * Uᴴ) * Y * U by simp only [mul_assoc], hU, mul_one]
  simp only [mul_assoc]

theorem phase_intCast_dev (T : Torus) (z : ℤ) :
    Complex.exp (2 * π * I * (((z : ZMod T.Nφ).val : ℕ) : ℂ) / (T.Nφ : ℂ)) =
      Complex.exp (2 * π * I * (z : ℂ) / (T.Nφ : ℂ)) := by
  have hN : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(z / (T.Nφ : ℤ)), ?_⟩
  have h1 : (((z : ZMod T.Nφ).val : ℕ) : ℤ) = z % (T.Nφ : ℤ) := ZMod.val_intCast z
  have h2 : (((z : ZMod T.Nφ).val : ℕ) : ℂ) = ((z % (T.Nφ : ℤ) : ℤ) : ℂ) := by exact_mod_cast h1
  rw [h2, Int.emod_def]
  push_cast
  field_simp
  ring

theorem half_cast_dev {n : ℤ} {d : ℕ} (hp : (d : ℤ) ≡ n [ZMOD 2]) :
    ((((n - (d : ℤ)) / 2 : ℤ) : ℂ) = ((n : ℂ) - (d : ℂ)) / 2) ∧
      ((((n + (d : ℤ)) / 2 : ℤ) : ℂ) = ((n : ℂ) + (d : ℂ)) / 2) := by
  have h1 : (2 : ℤ) ∣ n - d := (Int.ModEq.dvd hp)
  have h2 : (2 : ℤ) ∣ n + d := by
    have : n + d = (n - d) + 2 * d := by ring
    rw [this]
    exact dvd_add h1 (dvd_mul_right 2 _)
  have e1 := Int.ediv_mul_cancel h1
  have e2 := Int.ediv_mul_cancel h2
  constructor
  · have : (((n - (d : ℤ)) / 2 : ℤ) : ℂ) * 2 = (n : ℂ) - d := by exact_mod_cast e1
    linear_combination this / 2
  · have : (((n + (d : ℤ)) / 2 : ℤ) : ℂ) * 2 = (n : ℂ) + d := by exact_mod_cast e2
    linear_combination this / 2

theorem twist_conj_c_dev (T : Torus) (σ : Spin) (μ : Modes T) :
    twist T σ * Fermion.Pilot.JW.c μ * (twist T σ)ᴴ = star (twistPhi_dev T σ μ) • Fermion.Pilot.JW.c μ :=
  Fermion.Pilot.JW.diagonal_mul_c_mul_conjTranspose fun m hm => twistDiag_update_dev T σ μ m hm

theorem twistUp_conj_cjs_dev (T : Torus) (j : ZMod T.Nφ) (σ : Spin) :
    (twist T .up)ᴴ * cjs T j σ * twist T .up =
      (if σ = .up then Complex.exp (2 * π * I * (j.val : ℂ) / (T.Nφ : ℂ)) else 1) • cjs T j σ := by
  cases σ
  · rw [ite_eq_left rfl]
    exact twist_conj_cjs T .up j
  · rw [ite_eq_right (by decide), twist_conj_cjs_of_ne T (by decide) j, one_smul]

theorem twistTwo_conj_cjs_dev (T : Torus) (j : ZMod T.Nφ) (σ : Spin) :
    (twistTwo T)ᴴ * cjs T j σ * twistTwo T =
      (if σ = .up then Complex.exp (2 * π * I * (j.val : ℂ) / (T.Nφ : ℂ))
        else star (Complex.exp (2 * π * I * (j.val : ℂ) / (T.Nφ : ℂ)))) • cjs T j σ := by
  have e : (twistTwo T)ᴴ * cjs T j σ * twistTwo T =
      twist T .dn * ((twist T .up)ᴴ * cjs T j σ * twist T .up) * (twist T .dn)ᴴ := by
    rw [twistTwo, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [mul_assoc]
  rw [e, twistUp_conj_cjs_dev, Matrix.mul_smul, Matrix.smul_mul, cjs_eq, twist_conj_c_dev, smul_smul]
  congr 1
  cases σ
  · simp [twistPhi_dev]
  · simp [twistPhi_dev]

theorem conj_cpairD_dev (T : Torus) {U : FockOp T} (hU : U * Uᴴ = 1) (α β : ZMod T.Nφ → ℂ)
    (hα : ∀ j, Uᴴ * cjs T j .up * U = α j • cjs T j .up) (hβ : ∀ j, Uᴴ * cjs T j .dn * U = β j • cjs T j .dn)
    (n : ℤ) (d : ℕ) :
    Uᴴ * cpairD T .plus n d * U =
        (α (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) * α (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ)) • cpairD T .plus n d ∧
      Uᴴ * cpairD T .minus n d * U =
        (β (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) * β (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ)) • cpairD T .minus n d ∧
      Uᴴ * cpairD T .zero n d * U = (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        ((β (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) * α (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ)) •
            (cjs T (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .dn * cjs T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .up) +
          (α (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) * β (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ)) •
            (cjs T (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .up * cjs T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .dn)) := by
  obtain ⟨h1, h2, h3, -⟩ := cpairD_eq T n d
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, conj_mul_dev T hU, hα, hα, smul_mul_smul_comm]
  · rw [h2, conj_mul_dev T hU, hβ, hβ, smul_mul_smul_comm]
  · rw [h3, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, conj_mul_dev T hU,
      conj_mul_dev T hU, hα, hα, hβ, hβ, smul_mul_smul_comm, smul_mul_smul_comm]

theorem trig_combo_dev (T : Torus) (P : ℂ) (x : ℝ) (u v : FockOp T) :
    (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((P * Complex.exp ((x : ℂ) * I)) • u + (P * Complex.exp (-((x : ℂ) * I))) • v) =
      P • (((Real.cos x : ℝ) : ℂ) • ((((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (u + v)) +
        (I * ((Real.sin x : ℝ) : ℂ)) • ((((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (u - v))) := by
  rw [show -((x : ℂ) * I) = ((-x : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  module

theorem toCLM_conjTranspose_inner_dev (T : Torus) (A : FockOp T) (x y : FockSpace T) :
    ⟪toCLM T A x, y⟫_ℂ = ⟪x, toCLM T Aᴴ y⟫_ℂ := by
  rw [show toCLM T Aᴴ = ContinuousLinearMap.adjoint (toCLM T A) by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← toCLM_star_dev, Matrix.star_eq_conjTranspose],
    ContinuousLinearMap.adjoint_inner_right]

theorem twistUp_conj_bcenTerm_dev (T : Torus) (n : ℤ) (d : ℕ) :
    (twist T .up)ᴴ * bcenTerm T .plus n d * twist T .up =
        Complex.exp (2 * π * I * (n : ℂ) / (T.Nφ : ℂ)) • bcenTerm T .plus n d ∧
      (twist T .up)ᴴ * bcenTerm T .minus n d * twist T .up = (1 : ℂ) • bcenTerm T .minus n d ∧
      (twist T .up)ᴴ * bcenTerm T .zero n d * twist T .up =
        Complex.exp (π * I * (n : ℂ) / (T.Nφ : ℂ)) • (bcenTerm T .zero n d + twistTerm T (π / (T.Nφ : ℝ)) n d) := by
  have hU : twist T .up * (twist T .up)ᴴ = 1 := mul_conjTranspose_self_of_mem_unitary (twist_mem_unitary T .up)
  set φ : ZMod T.Nφ → ℂ := fun j => Complex.exp (2 * π * I * (j.val : ℂ) / (T.Nφ : ℂ)) with hφ
  have hα : ∀ j, (twist T .up)ᴴ * cjs T j .up * twist T .up = φ j • cjs T j .up := fun j => by
    rw [twistUp_conj_cjs_dev, ite_eq_left rfl]
  have hβ : ∀ j, (twist T .up)ᴴ * cjs T j .dn * twist T .up = (fun _ => (1 : ℂ)) j • cjs T j .dn := fun j => by
    rw [twistUp_conj_cjs_dev, ite_eq_right (by decide)]
  obtain ⟨hp, hm, hz⟩ := conj_cpairD_dev T hU φ (fun _ => 1) hα hβ n d
  obtain ⟨-, -, h3, h4⟩ := cpairD_eq T n d
  have hN : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
  rw [bcenTerm_eq_cpairD, bcenTerm_eq_cpairD, bcenTerm_eq_cpairD, twistTerm]
  by_cases hpar : (d : ℤ) ≡ n [ZMOD 2]
  · rw [ite_eq_left hpar, ite_eq_left hpar, ite_eq_left hpar, ite_eq_left hpar]
    have hc := half_cast_dev hpar
    have hj : φ (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) = Complex.exp (π * I * (n : ℂ) / (T.Nφ : ℂ)) *
        Complex.exp (-(((π / (T.Nφ : ℝ) * (d : ℝ) : ℝ) : ℂ) * I)) := by
      simp only [hφ]
      rw [phase_intCast_dev, hc.1, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    have hj' : φ (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) = Complex.exp (π * I * (n : ℂ) / (T.Nφ : ℂ)) *
        Complex.exp ((((π / (T.Nφ : ℝ) * (d : ℝ) : ℝ) : ℂ) * I)) := by
      simp only [hφ]
      rw [phase_intCast_dev, hc.2, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
    refine ⟨?_, ?_, ?_⟩
    · have hpp : φ (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) * φ (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) =
          Complex.exp (2 * π * I * (n : ℂ) / (T.Nφ : ℂ)) := by
        simp only [hφ]
        rw [phase_intCast_dev, phase_intCast_dev, ← Complex.exp_add, hc.1, hc.2]
        congr 1
        ring
      rw [Matrix.mul_smul, Matrix.smul_mul, hp, smul_comm]
      congr 1
    · rw [Matrix.mul_smul, Matrix.smul_mul, hm, one_mul, smul_comm]
    · rw [Matrix.mul_smul, Matrix.smul_mul, hz, one_mul, mul_one, hj, hj', trig_combo_dev, ← h3, ← h4]
      module
  · rw [ite_eq_right hpar, ite_eq_right hpar, ite_eq_right hpar, ite_eq_right hpar]
    simp

theorem twistTwo_conj_bcenTerm_dev (T : Torus) (n : ℤ) (d : ℕ) :
    (twistTwo T)ᴴ * bcenTerm T .plus n d * twistTwo T =
        Complex.exp (2 * π * I * (n : ℂ) / (T.Nφ : ℂ)) • bcenTerm T .plus n d ∧
      (twistTwo T)ᴴ * bcenTerm T .minus n d * twistTwo T =
        Complex.exp (-(2 * π * I * (n : ℂ) / (T.Nφ : ℂ))) • bcenTerm T .minus n d ∧
      (twistTwo T)ᴴ * bcenTerm T .zero n d * twistTwo T =
        (1 : ℂ) • (bcenTerm T .zero n d + twistTerm T (2 * π / (T.Nφ : ℝ)) n d) := by
  have hU : twistTwo T * (twistTwo T)ᴴ = 1 := by
    have h1 := mul_conjTranspose_self_of_mem_unitary (twist_mem_unitary T .up)
    have h2 := conjTranspose_mul_self_of_mem_unitary (twist_mem_unitary T .dn)
    rw [twistTwo, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      show twist T .up * (twist T .dn)ᴴ * (twist T .dn * (twist T .up)ᴴ) =
        twist T .up * ((twist T .dn)ᴴ * twist T .dn) * (twist T .up)ᴴ by simp only [mul_assoc], h2, mul_one, h1]
  set φ : ZMod T.Nφ → ℂ := fun j => Complex.exp (2 * π * I * (j.val : ℂ) / (T.Nφ : ℂ)) with hφ
  have hα : ∀ j, (twistTwo T)ᴴ * cjs T j .up * twistTwo T = φ j • cjs T j .up := fun j => by
    rw [twistTwo_conj_cjs_dev, ite_eq_left rfl]
  have hβ : ∀ j, (twistTwo T)ᴴ * cjs T j .dn * twistTwo T = (fun j => star (φ j)) j • cjs T j .dn := fun j => by
    rw [twistTwo_conj_cjs_dev, ite_eq_right (by decide)]
  obtain ⟨hp, hm, hz⟩ := conj_cpairD_dev T hU φ (fun j => star (φ j)) hα hβ n d
  obtain ⟨-, -, h3, h4⟩ := cpairD_eq T n d
  have hN : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
  have hstar : ∀ z : ℤ, star (φ ((z : ℤ) : ZMod T.Nφ)) = Complex.exp (-(2 * π * I * (z : ℂ) / (T.Nφ : ℂ))) := by
    intro z
    simp only [hφ]
    rw [phase_intCast_dev, Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_div₀, map_mul, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast,
      map_natCast]
    simp only [map_ofNat]
    ring
  rw [bcenTerm_eq_cpairD, bcenTerm_eq_cpairD, bcenTerm_eq_cpairD, twistTerm]
  by_cases hpar : (d : ℤ) ≡ n [ZMOD 2]
  · rw [ite_eq_left hpar, ite_eq_left hpar, ite_eq_left hpar, ite_eq_left hpar]
    have hc := half_cast_dev hpar
    have hφz : ∀ z : ℤ, φ ((z : ℤ) : ZMod T.Nφ) = Complex.exp (2 * π * I * (z : ℂ) / (T.Nφ : ℂ)) := fun z => by
      simp only [hφ]
      rw [phase_intCast_dev]
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.mul_smul, Matrix.smul_mul, hp, smul_comm, hφz, hφz, ← Complex.exp_add, hc.1, hc.2]
      congr 2
      field_simp
      ring
    · rw [Matrix.mul_smul, Matrix.smul_mul, hm, smul_comm, hstar, hstar, ← Complex.exp_add, hc.1, hc.2]
      congr 2
      field_simp
      ring
    · have e1 : star (φ (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ)) * φ (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) =
          1 * Complex.exp ((((2 * π / (T.Nφ : ℝ) * (d : ℝ) : ℝ) : ℂ) * I)) := by
        rw [hstar, hφz, ← Complex.exp_add, hc.1, hc.2, one_mul]
        congr 1
        push_cast
        field_simp
        ring
      have e2 : φ (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) * star (φ (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ)) =
          1 * Complex.exp (-((((2 * π / (T.Nφ : ℝ) * (d : ℝ) : ℝ) : ℂ) * I))) := by
        rw [hstar, hφz, ← Complex.exp_add, hc.1, hc.2, one_mul]
        congr 1
        push_cast
        field_simp
        ring
      rw [Matrix.mul_smul, Matrix.smul_mul, hz, e1, e2, trig_combo_dev, ← h3, ← h4]
      module
  · rw [ite_eq_right hpar, ite_eq_right hpar, ite_eq_right hpar, ite_eq_right hpar]
    simp

theorem toCLM_sum_apply_dev (T : Torus) {ι : Type*} (s : Finset ι) (f : ι → FockOp T) (v : FockSpace T) :
    toCLM T (∑ i ∈ s, f i) v = ∑ i ∈ s, toCLM T (f i) v := by
  let L : FockOp T →ₗ[ℂ] FockSpace T :=
    { toFun := fun A => toCLM T A v
      map_add' := fun A B => by rw [toCLM_add_dev]; rfl
      map_smul' := fun c A => by rw [toCLM_smul_dev]; rfl }
  exact map_sum L f s

theorem inner_conjTranspose_mul_dev (T : Torus) (X : FockOp T) (v : FockSpace T) :
    ⟪v, toCLM T (Xᴴ * X) v⟫_ℂ = ((‖toCLM T X v‖ ^ 2 : ℝ) : ℂ) := by
  rw [toCLM_mul_dev, mul_apply_eq_comp, ← toCLM_conjTranspose_inner_dev, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem conj_conjTranspose_mul_dev (T : Torus) {U : FockOp T} (hU : U * Uᴴ = 1) (B : FockOp T) :
    Uᴴ * (Bᴴ * B) * U = (Uᴴ * B * U)ᴴ * (Uᴴ * B * U) := by
  rw [conj_mul_dev T hU, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

theorem conj_HN_dev (T : Torus) {U : FockOp T} (hU : U * Uᴴ = 1) :
    Uᴴ * HN T * U = ((T.κ ^ 3 / Real.sqrt (2 * π) : ℝ) : ℂ) •
      ∑ n ∈ Finset.range (2 * T.Nφ), ∑ ν : Triplet, (Uᴴ * bcen T ν (n : ℤ) * U)ᴴ * (Uᴴ * bcen T ν (n : ℤ) * U) := by
  rw [localForm_c, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun ν _ => conj_conjTranspose_mul_dev T hU _

theorem inner_smul_sum_dev (T : Torus) (r : ℝ) (s : Finset ℕ) (X : ℕ → Triplet → FockOp T) (v : FockSpace T) :
    ⟪v, toCLM T ((r : ℂ) • ∑ n ∈ s, ∑ ν : Triplet, (X n ν)ᴴ * X n ν) v⟫_ℂ =
      ((r * ∑ n ∈ s, ∑ ν : Triplet, ‖toCLM T (X n ν) v‖ ^ 2 : ℝ) : ℂ) := by
  rw [toCLM_smul_dev, smul_apply, inner_smul_right, toCLM_sum_apply_dev, inner_sum]
  simp only [toCLM_sum_apply_dev, inner_sum, inner_conjTranspose_mul_dev]
  push_cast
  rfl

theorem toCLM_HN_eq_zero_dev (T : Torus) {Υ : FockSpace T} (hΥ : Υ ∈ KN T) : toCLM T (HN T) Υ = 0 := by
  have h := (Submodule.mem_inf.1 hΥ).1
  rw [LinearMap.mem_ker, toEuclideanLin_apply_dev] at h
  exact h

theorem bcen_apply_eq_zero_dev (T : Torus) {Υ : FockSpace T} (hΥ : Υ ∈ KN T) (ν : Triplet) {n : ℕ}
    (hn : n ∈ Finset.range (2 * T.Nφ)) : toCLM T (bcen T ν (n : ℤ)) Υ = 0 := by
  have h0 : ⟪Υ, toCLM T (HN T) Υ⟫_ℂ = 0 := by rw [toCLM_HN_eq_zero_dev T hΥ, inner_zero_right]
  rw [localForm_c, inner_smul_sum_dev T _ _ (fun n ν => bcen T ν (n : ℤ))] at h0
  have hc : 0 < T.κ ^ 3 / Real.sqrt (2 * π) := by have := T.κ_pos; positivity
  have hsum : ∑ n ∈ Finset.range (2 * T.Nφ), ∑ ν : Triplet, ‖toCLM T (bcen T ν (n : ℤ)) Υ‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 (Complex.ofReal_eq_zero.1 h0) with h | h
    · exact absurd h hc.ne'
    · exact h
  have hn0 := (Finset.sum_eq_zero_iff_of_nonneg (fun n _ => Finset.sum_nonneg fun ν _ => sq_nonneg _)).1 hsum n hn
  have hν := (Finset.sum_eq_zero_iff_of_nonneg (fun ν _ => sq_nonneg _)).1 hn0 ν (Finset.mem_univ _)
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hν)

theorem twistUp_conj_bcen_dev (T : Torus) (n : ℤ) :
    (twist T .up)ᴴ * bcen T .plus n * twist T .up =
        Complex.exp (2 * π * I * (n : ℂ) / (T.Nφ : ℂ)) • bcen T .plus n ∧
      (twist T .up)ᴴ * bcen T .minus n * twist T .up = (1 : ℂ) • bcen T .minus n ∧
      (twist T .up)ᴴ * bcen T .zero n * twist T .up =
        Complex.exp (π * I * (n : ℂ) / (T.Nφ : ℂ)) • (bcen T .zero n + twistSum T (π / (T.Nφ : ℝ)) n) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bcen, tsum_conj_dev T _ (summable_bcenTerm T .plus n).2,
      tsum_congr fun d => (twistUp_conj_bcenTerm_dev T n d).1, (summable_bcenTerm T .plus n).2.tsum_const_smul _]
  · rw [bcen, tsum_conj_dev T _ (summable_bcenTerm T .minus n).2,
      tsum_congr fun d => (twistUp_conj_bcenTerm_dev T n d).2.1, (summable_bcenTerm T .minus n).2.tsum_const_smul _]
  · rw [bcen, tsum_conj_dev T _ (summable_bcenTerm T .zero n).2,
      tsum_congr fun d => (twistUp_conj_bcenTerm_dev T n d).2.2,
      ((summable_bcenTerm T .zero n).2.add (summable_twistTerm T _ n).2).tsum_const_smul _,
      (summable_bcenTerm T .zero n).2.tsum_add (summable_twistTerm T _ n).2]
    rfl

theorem twistTwo_conj_bcen_dev (T : Torus) (n : ℤ) :
    (twistTwo T)ᴴ * bcen T .plus n * twistTwo T =
        Complex.exp (2 * π * I * (n : ℂ) / (T.Nφ : ℂ)) • bcen T .plus n ∧
      (twistTwo T)ᴴ * bcen T .minus n * twistTwo T =
        Complex.exp (-(2 * π * I * (n : ℂ) / (T.Nφ : ℂ))) • bcen T .minus n ∧
      (twistTwo T)ᴴ * bcen T .zero n * twistTwo T =
        (1 : ℂ) • (bcen T .zero n + twistSum T (2 * π / (T.Nφ : ℝ)) n) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bcen, tsum_conj_dev T _ (summable_bcenTerm T .plus n).2,
      tsum_congr fun d => (twistTwo_conj_bcenTerm_dev T n d).1, (summable_bcenTerm T .plus n).2.tsum_const_smul _]
  · rw [bcen, tsum_conj_dev T _ (summable_bcenTerm T .minus n).2,
      tsum_congr fun d => (twistTwo_conj_bcenTerm_dev T n d).2.1, (summable_bcenTerm T .minus n).2.tsum_const_smul _]
  · rw [bcen, tsum_conj_dev T _ (summable_bcenTerm T .zero n).2,
      tsum_congr fun d => (twistTwo_conj_bcenTerm_dev T n d).2.2,
      ((summable_bcenTerm T .zero n).2.add (summable_twistTerm T _ n).2).tsum_const_smul _,
      (summable_bcenTerm T .zero n).2.tsum_add (summable_twistTerm T _ n).2]
    rfl

theorem energy_identity_dev (T : Torus) {U : FockOp T} (hU : U * Uᴴ = 1) {θ : ℝ} {Υ : FockSpace T}
    (hΥ : Υ ∈ KN T) (ap am P : ℤ → ℂ) (hP : ∀ n, ‖P n‖ = 1)
    (hconj : ∀ n : ℤ, Uᴴ * bcen T .plus n * U = ap n • bcen T .plus n ∧
      Uᴴ * bcen T .minus n * U = am n • bcen T .minus n ∧
      Uᴴ * bcen T .zero n * U = P n • (bcen T .zero n + twistSum T θ n)) :
    ⟪toCLM T U Υ, toCLM T (HN T) (toCLM T U Υ)⟫_ℂ =
      ((T.κ ^ 3 / Real.sqrt (2 * π) *
        ∑ n ∈ Finset.range (2 * T.Nφ), ‖toCLM T (twistSum T θ (n : ℤ)) Υ‖ ^ 2 : ℝ) : ℂ) := by
  have e : toCLM T Uᴴ (toCLM T (HN T) (toCLM T U Υ)) = toCLM T (Uᴴ * HN T * U) Υ := by
    rw [toCLM_mul_dev, toCLM_mul_dev, mul_apply_eq_comp, mul_apply_eq_comp]
  rw [toCLM_conjTranspose_inner_dev, e, conj_HN_dev T hU,
    inner_smul_sum_dev T _ _ (fun n ν => Uᴴ * bcen T ν (n : ℤ) * U)]
  congr 2
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hp, hm, hz⟩ := hconj (n : ℤ)
  rw [HRTorus.Hamiltonian.PairForm.sum_triplet]
  try dsimp only
  rw [hp, hm, hz, toCLM_smul_dev, toCLM_smul_dev, toCLM_smul_dev, toCLM_add_dev, smul_apply,
    smul_apply, smul_apply, add_apply,
    bcen_apply_eq_zero_dev T hΥ .plus hn, bcen_apply_eq_zero_dev T hΥ .minus hn,
    bcen_apply_eq_zero_dev T hΥ .zero hn, smul_zero, smul_zero, zero_add, norm_smul, hP, one_mul, norm_zero]
  ring

theorem s_sq_dev : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / 2 := by
  have h := two_mul_rpow_neg_half
  have h2 : (2 : ℝ) ^ 2 * ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 2 := by
    rw [← mul_pow, h, Real.sq_sqrt (by norm_num)]
  linarith

theorem norm_s_smul_sq_le_dev {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (x y : E) :
    ‖(((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (x + y)‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 ∧
      ‖(((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (x - y)‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have hs : 0 < (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos two_pos _
  have hs2 := s_sq_dev
  rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  constructor
  · calc ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * ‖x + y‖) ^ 2 ≤ ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * (‖x‖ + ‖y‖)) ^ 2 := by
          gcongr
          exact norm_add_le _ _
      _ = 1 / 2 * (‖x‖ + ‖y‖) ^ 2 := by rw [mul_pow, hs2]
      _ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  · calc ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * ‖x - y‖) ^ 2 ≤ ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * (‖x‖ + ‖y‖)) ^ 2 := by
          gcongr
          exact norm_sub_le _ _
      _ = 1 / 2 * (‖x‖ + ‖y‖) ^ 2 := by rw [mul_pow, hs2]
      _ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem norm_cjs_le_dev (T : Torus) (j : ZMod T.Nφ) (σ : Spin) : ‖toCLM T (cjs T j σ)‖ ≤ 1 := by
  have h := norm_chatVec' (S := ZMod T.Nφ) (spinTensor (orb T j) σ)
  rw [norm_spinTensor] at h
  simp only [orb, PiLp.norm_single, norm_one] at h
  exact h.le

theorem norm_cjs_mul_apply_le_dev (T : Torus) (j k : ZMod T.Nφ) (σ τ : Spin) (v : FockSpace T) :
    ‖toCLM T (cjs T j σ * cjs T k τ) v‖ ≤ ‖toCLM T (cjs T k τ) v‖ := by
  rw [toCLM_mul_dev, mul_apply_eq_comp]
  calc ‖toCLM T (cjs T j σ) (toCLM T (cjs T k τ) v)‖ ≤ ‖toCLM T (cjs T j σ)‖ * ‖toCLM T (cjs T k τ) v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖toCLM T (cjs T k τ) v‖ := mul_le_mul_of_nonneg_right (norm_cjs_le_dev T j σ) (norm_nonneg _)
    _ = _ := one_mul _

theorem norm_pair_apply_sq_le_dev (T : Torus) (n : ℤ) (d : ℕ) (Υ : FockSpace T) :
    ‖toCLM T (cpairD T .zero n d) Υ‖ ^ 2 ≤
        ‖toCLM T (cjs T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .up) Υ‖ ^ 2 +
          ‖toCLM T (cjs T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .dn) Υ‖ ^ 2 ∧
      ‖toCLM T (cpairSing T n d) Υ‖ ^ 2 ≤
        ‖toCLM T (cjs T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .up) Υ‖ ^ 2 +
          ‖toCLM T (cjs T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .dn) Υ‖ ^ 2 := by
  obtain ⟨-, -, h3, h4⟩ := cpairD_eq T n d
  constructor
  · rw [h3, toCLM_smul_dev, smul_apply, toCLM_add_dev, add_apply]
    refine (norm_s_smul_sq_le_dev _ _).1.trans ?_
    gcongr
    · exact norm_cjs_mul_apply_le_dev T _ _ _ _ _
    · exact norm_cjs_mul_apply_le_dev T _ _ _ _ _
  · rw [h4, toCLM_smul_dev, smul_apply, toCLM_sub_dev, sub_apply]
    refine (norm_s_smul_sq_le_dev _ _).2.trans ?_
    gcongr
    · exact norm_cjs_mul_apply_le_dev T _ _ _ _ _
    · exact norm_cjs_mul_apply_le_dev T _ _ _ _ _

theorem inner_diagonal_dev (T : Torus) (f : Conf (ZMod T.Nφ) → ℂ) (v : FockSpace T) :
    ⟪v, toCLM T (Matrix.diagonal f) v⟫_ℂ = ∑ m, f m * ((‖v m‖ ^ 2 : ℝ) : ℂ) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [toCLM_diagonal_apply_dev]
  show ⟪v m, f m • v m⟫_ℂ = _
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem sum_norm_cjs_sq_dev (T : Torus) {Υ : FockSpace T} (hΥ : Υ ∈ KN T) (h1 : ‖Υ‖ = 1) :
    ∑ j : ZMod T.Nφ, (‖toCLM T (cjs T j .up) Υ‖ ^ 2 + ‖toCLM T (cjs T j .dn) Υ‖ ^ 2) = T.N := by
  have hsupp := KN_support_dev T (Submodule.mem_inf.1 hΥ).2
  have key : ∀ σ : Spin, ∑ j : ZMod T.Nφ, ‖toCLM T (cjs T j σ) Υ‖ ^ 2 =
      ∑ m, (ctσ T σ m : ℝ) * ‖Υ m‖ ^ 2 := by
    intro σ
    apply Complex.ofReal_injective
    have e := inner_diagonal_dev T (fun m => (ctσ T σ m : ℂ)) Υ
    rw [← Nsig_eq_diag, Nsig, toCLM_sum_apply_dev, inner_sum] at e
    simp only [njs, inner_conjTranspose_mul_dev] at e
    push_cast at e ⊢
    exact e
  rw [Finset.sum_add_distrib, key, key, ← Finset.sum_add_distrib]
  have hN : ∀ m, (ctσ T .up m : ℝ) * ‖Υ m‖ ^ 2 + (ctσ T .dn m : ℝ) * ‖Υ m‖ ^ 2 = (T.N : ℝ) * ‖Υ m‖ ^ 2 := by
    intro m
    by_cases hm : Υ m = 0
    · simp [hm]
    · have e : ctσ T .up m + ctσ T .dn m = T.N := hsupp m hm
      rw [← add_mul]
      congr 1
      exact_mod_cast e
  rw [Finset.sum_congr rfl fun m _ => hN m, ← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, h1, one_pow, mul_one]

theorem sum_parity_le_dev (T : Torus) (d : ℕ) (g : ZMod T.Nφ → ℝ) (hg : ∀ j, 0 ≤ g j) :
    ∑ n ∈ Finset.range (2 * T.Nφ),
        (if (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2] then g (((((n : ℕ) : ℤ) + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) else 0) ≤
      ∑ j : ZMod T.Nφ, g j := by
  classical
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun n : ℕ => (((((n : ℕ) : ℤ) + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ))
      ((Finset.range (2 * T.Nφ)).filter fun n : ℕ => (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2]) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
    obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hab
    have hpa : (d : ℤ) % 2 = (a : ℤ) % 2 := ha.2
    have hpb : (d : ℤ) % 2 = (b : ℤ) % 2 := hb.2
    have ea : (((a : ℤ) + d) / 2) * 2 = a + d := by omega
    have eb : (((b : ℤ) + d) / 2) * 2 = b + d := by omega
    have hdiff : (b : ℤ) - a = (2 * (T.Nφ : ℤ)) * t := by linarith
    have hz : (b : ℤ) - a = 0 := Int.eq_zero_of_abs_lt_dvd ⟨t, hdiff⟩ (by
      rw [abs_lt]
      have := ha.1
      have := hb.1
      constructor <;> omega)
    omega
  calc ∑ n ∈ (Finset.range (2 * T.Nφ)).filter (fun n : ℕ => (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2]),
        g (((((n : ℕ) : ℤ) + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ)
      = ∑ j ∈ ((Finset.range (2 * T.Nφ)).filter (fun n : ℕ => (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2])).image
          (fun n : ℕ => (((((n : ℕ) : ℤ) + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ)), g j := (Finset.sum_image hinj).symm
    _ ≤ ∑ j, g j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hg j

theorem occ_sum_dev (T : Torus) {Υ : FockSpace T} (hΥ : Υ ∈ KN T) (h1 : ‖Υ‖ = 1) (d : ℕ) :
    ∑ n ∈ Finset.range (2 * T.Nφ), (if (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2] then
        ‖toCLM T (cpairD T .zero ((n : ℕ) : ℤ) d) Υ‖ ^ 2 else 0) ≤ T.N ∧
      ∑ n ∈ Finset.range (2 * T.Nφ), (if (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2] then
        ‖toCLM T (cpairSing T ((n : ℕ) : ℤ) d) Υ‖ ^ 2 else 0) ≤ T.N := by
  set g : ZMod T.Nφ → ℝ := fun j => ‖toCLM T (cjs T j .up) Υ‖ ^ 2 + ‖toCLM T (cjs T j .dn) Υ‖ ^ 2 with hg
  have hg0 : ∀ j, 0 ≤ g j := fun j => by positivity
  have hsum : ∑ j, g j = T.N := sum_norm_cjs_sq_dev T hΥ h1
  have hle := sum_parity_le_dev T d g hg0
  constructor
  · refine le_trans (Finset.sum_le_sum fun n _ => ?_) (hle.trans hsum.le)
    split_ifs
    · exact (norm_pair_apply_sq_le_dev T _ d Υ).1
    · exact le_rfl
  · refine le_trans (Finset.sum_le_sum fun n _ => ?_) (hle.trans hsum.le)
    split_ifs
    · exact (norm_pair_apply_sq_le_dev T _ d Υ).2
    · exact le_rfl

theorem cs_tsum_dev {a b : ℕ → ℝ} (ha : ∀ d, 0 ≤ a d) (hsa : Summable a) (hb : ∀ d, 0 ≤ b d) {M : ℝ}
    (hbM : ∀ d, b d ≤ M) :
    (∑' d, a d * b d) ^ 2 ≤ (∑' d, a d) * ∑' d, a d * b d ^ 2 := by
  have hs2 : Summable fun d => a d * b d ^ 2 :=
    Summable.of_nonneg_of_le (fun d => mul_nonneg (ha d) (sq_nonneg _))
      (fun d => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hb d) (hbM d) 2) (ha d)) (hsa.mul_right (M ^ 2))
  have hA : 0 ≤ ∑' d, a d := tsum_nonneg ha
  have hB : 0 ≤ ∑' d, a d * b d ^ 2 := tsum_nonneg fun d => mul_nonneg (ha d) (sq_nonneg _)
  have hS : 0 ≤ ∑' d, a d * b d := tsum_nonneg fun d => mul_nonneg (ha d) (hb d)
  have hfin : ∀ s : Finset ℕ, ∑ d ∈ s, a d * b d ≤ Real.sqrt ((∑' d, a d) * ∑' d, a d * b d ^ 2) := by
    intro s
    apply Real.le_sqrt_of_sq_le
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun d => Real.sqrt (a d)) (fun d => Real.sqrt (a d) * b d)
    have e1 : ∀ d, Real.sqrt (a d) * (Real.sqrt (a d) * b d) = a d * b d := fun d => by
      rw [← mul_assoc, Real.mul_self_sqrt (ha d)]
    have e2 : ∀ d, Real.sqrt (a d) ^ 2 = a d := fun d => Real.sq_sqrt (ha d)
    have e3 : ∀ d, (Real.sqrt (a d) * b d) ^ 2 = a d * b d ^ 2 := fun d => by rw [mul_pow, e2]
    simp only [e1, e2, e3] at hcs
    calc (∑ d ∈ s, a d * b d) ^ 2 ≤ (∑ d ∈ s, a d) * ∑ d ∈ s, a d * b d ^ 2 := hcs
      _ ≤ (∑' d, a d) * ∑' d, a d * b d ^ 2 :=
        mul_le_mul (hsa.sum_le_tsum s fun d _ => ha d)
          (hs2.sum_le_tsum s fun d _ => mul_nonneg (ha d) (sq_nonneg _))
          (Finset.sum_nonneg fun d _ => mul_nonneg (ha d) (sq_nonneg _)) hA
  have h : ∑' d, a d * b d ≤ Real.sqrt ((∑' d, a d) * ∑' d, a d * b d ^ 2) :=
    tsum_le_of_sum_le' (Real.sqrt_nonneg _) hfin
  calc (∑' d, a d * b d) ^ 2 ≤ (Real.sqrt ((∑' d, a d) * ∑' d, a d * b d ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hS h 2
    _ = (∑' d, a d) * ∑' d, a d * b d ^ 2 := Real.sq_sqrt (mul_nonneg hA hB)

def twW_dev (T : Torus) (d : ℕ) : ℝ := 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4)

def twA_dev (T : Torus) (θ : ℝ) (n : ℤ) (d : ℕ) : ℝ :=
  if (d : ℤ) ≡ n [ZMOD 2] then twW_dev T d * |Real.cos (θ * d) - 1| else 0

def twB_dev (T : Torus) (θ : ℝ) (n : ℤ) (d : ℕ) : ℝ :=
  if (d : ℤ) ≡ n [ZMOD 2] then twW_dev T d * |Real.sin (θ * d)| else 0

theorem twW_nonneg_dev (T : Torus) (d : ℕ) : 0 ≤ twW_dev T d := by unfold twW_dev; positivity

theorem twistTerm_apply_le_dev (T : Torus) (θ : ℝ) (n : ℤ) (d : ℕ) (Υ : FockSpace T) :
    ‖toCLM T (twistTerm T θ n d) Υ‖ ≤
      twA_dev T θ n d * ‖toCLM T (cpairD T .zero n d) Υ‖ + twB_dev T θ n d * ‖toCLM T (cpairSing T n d) Υ‖ := by
  unfold twistTerm twA_dev twB_dev twW_dev
  split_ifs with h
  · have hnn : 0 ≤ 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) := by positivity
    rw [toCLM_smul_dev, smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn,
      toCLM_add_dev, add_apply, toCLM_smul_dev, toCLM_smul_dev, smul_apply, smul_apply]
    have hin : ‖((Real.cos (θ * d) - 1 : ℝ) : ℂ) • toCLM T (cpairD T .zero n d) Υ +
        (I * ((Real.sin (θ * d) : ℝ) : ℂ)) • toCLM T (cpairSing T n d) Υ‖ ≤
        |Real.cos (θ * d) - 1| * ‖toCLM T (cpairD T .zero n d) Υ‖ +
          |Real.sin (θ * d)| * ‖toCLM T (cpairSing T n d) Υ‖ := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
    calc 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) *
          ‖((Real.cos (θ * d) - 1 : ℝ) : ℂ) • toCLM T (cpairD T .zero n d) Υ +
            (I * ((Real.sin (θ * d) : ℝ) : ℂ)) • toCLM T (cpairSing T n d) Υ‖
        ≤ 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) *
          (|Real.cos (θ * d) - 1| * ‖toCLM T (cpairD T .zero n d) Υ‖ +
            |Real.sin (θ * d)| * ‖toCLM T (cpairSing T n d) Υ‖) :=
          mul_le_mul_of_nonneg_left hin hnn
      _ = _ := by ring
  · rw [toCLM_eq_opCLM, opCLM_zero]
    simp

theorem norm_cpair_apply_le_dev (T : Torus) (n : ℤ) (d : ℕ) {Υ : FockSpace T} (h1 : ‖Υ‖ = 1) :
    ‖toCLM T (cpairD T .zero n d) Υ‖ ≤ Real.sqrt 2 ∧ ‖toCLM T (cpairSing T n d) Υ‖ ≤ Real.sqrt 2 := by
  constructor
  · calc _ ≤ ‖toCLM T (cpairD T .zero n d)‖ * ‖Υ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Real.sqrt 2 := by rw [h1, mul_one]; exact norm_cpairD_le T .zero n d
  · calc _ ≤ ‖toCLM T (cpairSing T n d)‖ * ‖Υ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Real.sqrt 2 := by rw [h1, mul_one]; exact norm_cpairSing_le T n d

theorem twA_le_dev (T : Torus) (θ : ℝ) (n : ℤ) (d : ℕ) :
    0 ≤ twA_dev T θ n d ∧
      twA_dev T θ n d ≤ θ ^ 2 / 2 * (2 * (d : ℝ) ^ 3 * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4)) := by
  unfold twA_dev
  have hw := twW_nonneg_dev T d
  split_ifs
  · refine ⟨mul_nonneg hw (abs_nonneg _), ?_⟩
    have hc : |Real.cos (θ * d) - 1| ≤ (θ * d) ^ 2 / 2 := by
      rw [abs_of_nonpos (by linarith [Real.cos_le_one (θ * d)])]
      linarith [Real.one_sub_sq_div_two_le_cos (x := θ * d)]
    calc twW_dev T d * |Real.cos (θ * d) - 1| ≤ twW_dev T d * ((θ * d) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hc hw
      _ = _ := by unfold twW_dev; ring
  · exact ⟨le_rfl, by positivity⟩

theorem twB_le_dev (T : Torus) {θ : ℝ} (hθ : 0 ≤ θ) (n : ℤ) (d : ℕ) :
    0 ≤ twB_dev T θ n d ∧
      twB_dev T θ n d ≤ θ * (2 * (d : ℝ) ^ 2 * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4)) := by
  unfold twB_dev
  have hw := twW_nonneg_dev T d
  split_ifs
  · refine ⟨mul_nonneg hw (abs_nonneg _), ?_⟩
    have hs : |Real.sin (θ * d)| ≤ θ * d := by
      have h := Real.abs_sin_le_abs (x := θ * d)
      rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ θ * d)] at h
    calc twW_dev T d * |Real.sin (θ * d)| ≤ twW_dev T d * (θ * d) := mul_le_mul_of_nonneg_left hs hw
      _ = _ := by unfold twW_dev; ring
  · exact ⟨le_rfl, by positivity⟩

theorem twistSum_apply_sq_le_dev (T : Torus) {θ : ℝ} (hθ : 0 ≤ θ) (n : ℤ) {Υ : FockSpace T} (h1 : ‖Υ‖ = 1) :
    ‖toCLM T (twistSum T θ n) Υ‖ ^ 2 ≤
      2 * (θ ^ 2 / 2 * gaussSum T.κ 3) * ∑' d, twA_dev T θ n d * ‖toCLM T (cpairD T .zero n d) Υ‖ ^ 2 +
        2 * (θ * gaussSum T.κ 2) * ∑' d, twB_dev T θ n d * ‖toCLM T (cpairSing T n d) Υ‖ ^ 2 := by
  have hκ := T.κ_pos
  have hs3 := summable_gaussSum hκ 3
  have hs2 := summable_gaussSum hκ 2
  have hA0 : ∀ d, 0 ≤ twA_dev T θ n d := fun d => (twA_le_dev T θ n d).1
  have hB0 : ∀ d, 0 ≤ twB_dev T θ n d := fun d => (twB_le_dev T hθ n d).1
  have hsA : Summable (twA_dev T θ n) :=
    Summable.of_nonneg_of_le hA0 (fun d => (twA_le_dev T θ n d).2) (hs3.mul_left _)
  have hsB : Summable (twB_dev T θ n) :=
    Summable.of_nonneg_of_le hB0 (fun d => (twB_le_dev T hθ n d).2) (hs2.mul_left _)
  have hX : ∀ d, ‖toCLM T (cpairD T .zero n d) Υ‖ ≤ Real.sqrt 2 := fun d => (norm_cpair_apply_le_dev T n d h1).1
  have hY : ∀ d, ‖toCLM T (cpairSing T n d) Υ‖ ≤ Real.sqrt 2 := fun d => (norm_cpair_apply_le_dev T n d h1).2
  have hsAX : Summable fun d => twA_dev T θ n d * ‖toCLM T (cpairD T .zero n d) Υ‖ :=
    Summable.of_nonneg_of_le (fun d => mul_nonneg (hA0 d) (norm_nonneg _))
      (fun d => mul_le_mul_of_nonneg_left (hX d) (hA0 d)) (hsA.mul_right _)
  have hsBY : Summable fun d => twB_dev T θ n d * ‖toCLM T (cpairSing T n d) Υ‖ :=
    Summable.of_nonneg_of_le (fun d => mul_nonneg (hB0 d) (norm_nonneg _))
      (fun d => mul_le_mul_of_nonneg_left (hY d) (hB0 d)) (hsB.mul_right _)
  have hsT : Summable fun d => ‖toCLM T (twistTerm T θ n d) Υ‖ :=
    Summable.of_nonneg_of_le (fun d => norm_nonneg _) (fun d => twistTerm_apply_le_dev T θ n d Υ) (hsAX.add hsBY)
  have hS : ‖toCLM T (twistSum T θ n) Υ‖ ≤ ∑' d, twA_dev T θ n d * ‖toCLM T (cpairD T .zero n d) Υ‖ +
      ∑' d, twB_dev T θ n d * ‖toCLM T (cpairSing T n d) Υ‖ := by
    rw [twistSum, toCLM_tsum_apply_dev T (summable_twistTerm T θ n).2, ← hsAX.tsum_add hsBY]
    exact (norm_tsum_le_tsum_norm hsT).trans
      (hsT.tsum_le_tsum (fun d => twistTerm_apply_le_dev T θ n d Υ) (hsAX.add hsBY))
  have hcsA := cs_tsum_dev hA0 hsA (fun d => norm_nonneg _) hX
  have hcsB := cs_tsum_dev hB0 hsB (fun d => norm_nonneg _) hY
  have hA : ∑' d, twA_dev T θ n d ≤ θ ^ 2 / 2 * gaussSum T.κ 3 := by
    rw [gaussSum, ← hs3.tsum_mul_left]
    exact hsA.tsum_le_tsum (fun d => (twA_le_dev T θ n d).2) (hs3.mul_left _)
  have hB : ∑' d, twB_dev T θ n d ≤ θ * gaussSum T.κ 2 := by
    rw [gaussSum, ← hs2.tsum_mul_left]
    exact hsB.tsum_le_tsum (fun d => (twB_le_dev T hθ n d).2) (hs2.mul_left _)
  have hAX2 : 0 ≤ ∑' d, twA_dev T θ n d * ‖toCLM T (cpairD T .zero n d) Υ‖ ^ 2 :=
    tsum_nonneg fun d => mul_nonneg (hA0 d) (sq_nonneg _)
  have hBY2 : 0 ≤ ∑' d, twB_dev T θ n d * ‖toCLM T (cpairSing T n d) Υ‖ ^ 2 :=
    tsum_nonneg fun d => mul_nonneg (hB0 d) (sq_nonneg _)
  have hP : 0 ≤ ∑' d, twA_dev T θ n d * ‖toCLM T (cpairD T .zero n d) Υ‖ :=
    tsum_nonneg fun d => mul_nonneg (hA0 d) (norm_nonneg _)
  have hQ : 0 ≤ ∑' d, twB_dev T θ n d * ‖toCLM T (cpairSing T n d) Υ‖ :=
    tsum_nonneg fun d => mul_nonneg (hB0 d) (norm_nonneg _)
  have hA2 := mul_le_mul_of_nonneg_right hA hAX2
  have hB2 := mul_le_mul_of_nonneg_right hB hBY2
  set P := ∑' d, twA_dev T θ n d * ‖toCLM T (cpairD T .zero n d) Υ‖ with hPdef
  set Q := ∑' d, twB_dev T θ n d * ‖toCLM T (cpairSing T n d) Υ‖ with hQdef
  have hSq : ‖toCLM T (twistSum T θ n) Υ‖ ^ 2 ≤ (P + Q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hS 2
  nlinarith [sq_nonneg (P - Q)]

theorem twistSum_sum_sq_le_dev (T : Torus) {θ : ℝ} (hθ : 0 ≤ θ) {Υ : FockSpace T} (hΥ : Υ ∈ KN T)
    (h1 : ‖Υ‖ = 1) :
    ∑ n ∈ Finset.range (2 * T.Nφ), ‖toCLM T (twistSum T θ ((n : ℕ) : ℤ)) Υ‖ ^ 2 ≤
      2 * (θ ^ 2 / 2 * gaussSum T.κ 3) ^ 2 * T.N + 2 * (θ * gaussSum T.κ 2) ^ 2 * T.N := by
  have hκ := T.κ_pos
  have hs3 := summable_gaussSum hκ 3
  have hs2 := summable_gaussSum hκ 2
  have hG3 : 0 ≤ gaussSum T.κ 3 := tsum_nonneg fun d => by positivity
  have hG2 : 0 ≤ gaussSum T.κ 2 := tsum_nonneg fun d => by positivity
  have hocc : ∀ (Z c : ℤ → ℕ → ℝ) (e : ℕ → ℝ), Summable e → (∀ d, 0 ≤ e d) →
      (∀ n d, 0 ≤ c n d) → (∀ n d, c n d ≤ (if (d : ℤ) ≡ n [ZMOD 2] then e d else 0)) →
      (∀ n d, 0 ≤ Z n d) → (∀ n d, Z n d ≤ 2) →
      (∀ d : ℕ, ∑ n ∈ Finset.range (2 * T.Nφ),
        (if (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2] then Z ((n : ℕ) : ℤ) d else 0) ≤ T.N) →
      ∑ n ∈ Finset.range (2 * T.Nφ), ∑' d, c ((n : ℕ) : ℤ) d * Z ((n : ℕ) : ℤ) d ≤ (∑' d, e d) * T.N := by
    intro Z c e hse he hc hce hZ hZ2 hZN
    have hsum_n : ∀ n : ℕ, Summable fun d =>
        e d * (if (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2] then Z ((n : ℕ) : ℤ) d else 0) := by
      intro n
      refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) (hse.mul_right 2)
      · split_ifs
        · exact mul_nonneg (he d) (hZ _ d)
        · simp
      · split_ifs
        · exact mul_le_mul_of_nonneg_left (hZ2 _ d) (he d)
        · simp only [mul_zero]
          exact mul_nonneg (he d) (by norm_num)
    have hle_n : ∀ n : ℕ, ∀ d, c ((n : ℕ) : ℤ) d * Z ((n : ℕ) : ℤ) d ≤
        e d * (if (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2] then Z ((n : ℕ) : ℤ) d else 0) := by
      intro n d
      have h := hce ((n : ℕ) : ℤ) d
      split_ifs at h ⊢ with hp
      · exact mul_le_mul_of_nonneg_right h (hZ _ d)
      · have : c ((n : ℕ) : ℤ) d = 0 := le_antisymm h (hc _ d)
        rw [this, zero_mul, mul_zero]
    have hsum_c : ∀ n : ℕ, Summable fun d => c ((n : ℕ) : ℤ) d * Z ((n : ℕ) : ℤ) d := fun n =>
      Summable.of_nonneg_of_le (fun d => mul_nonneg (hc _ d) (hZ _ d)) (hle_n n) (hsum_n n)
    have hinner : ∀ d : ℕ, 0 ≤ ∑ n ∈ Finset.range (2 * T.Nφ),
        (if (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2] then Z ((n : ℕ) : ℤ) d else 0) := fun d =>
      Finset.sum_nonneg fun n _ => by split_ifs; exacts [hZ _ d, le_rfl]
    calc ∑ n ∈ Finset.range (2 * T.Nφ), ∑' d, c ((n : ℕ) : ℤ) d * Z ((n : ℕ) : ℤ) d
        ≤ ∑ n ∈ Finset.range (2 * T.Nφ), ∑' d,
            e d * (if (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2] then Z ((n : ℕ) : ℤ) d else 0) :=
          Finset.sum_le_sum fun n _ => (hsum_c n).tsum_le_tsum (hle_n n) (hsum_n n)
      _ = ∑' d, ∑ n ∈ Finset.range (2 * T.Nφ),
            e d * (if (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2] then Z ((n : ℕ) : ℤ) d else 0) :=
          (Summable.tsum_finsetSum fun n _ => hsum_n n).symm
      _ = ∑' d, e d * ∑ n ∈ Finset.range (2 * T.Nφ),
            (if (d : ℤ) ≡ ((n : ℕ) : ℤ) [ZMOD 2] then Z ((n : ℕ) : ℤ) d else 0) := by
          congr 1
          funext d
          rw [Finset.mul_sum]
      _ ≤ ∑' d, e d * T.N := by
          refine Summable.tsum_le_tsum (fun d => mul_le_mul_of_nonneg_left (hZN d) (he d)) ?_ (hse.mul_right _)
          exact Summable.of_nonneg_of_le (fun d => mul_nonneg (he d) (hinner d))
            (fun d => mul_le_mul_of_nonneg_left (hZN d) (he d)) (hse.mul_right _)
      _ = (∑' d, e d) * T.N := hse.tsum_mul_right _
  have hceA : ∀ n d, twA_dev T θ n d ≤ (if (d : ℤ) ≡ n [ZMOD 2] then
      θ ^ 2 / 2 * (2 * (d : ℝ) ^ 3 * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4)) else 0) := by
    intro n d
    have h := (twA_le_dev T θ n d).2
    unfold twA_dev at h ⊢
    split_ifs at h ⊢
    · exact h
    · exact le_rfl
  have hceB : ∀ n d, twB_dev T θ n d ≤ (if (d : ℤ) ≡ n [ZMOD 2] then
      θ * (2 * (d : ℝ) ^ 2 * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4)) else 0) := by
    intro n d
    have h := (twB_le_dev T hθ n d).2
    unfold twB_dev at h ⊢
    split_ifs at h ⊢
    · exact h
    · exact le_rfl
  have hX2 : ∀ (n : ℤ) d, ‖toCLM T (cpairD T .zero n d) Υ‖ ^ 2 ≤ 2 := fun n d => by
    have h := (norm_cpair_apply_le_dev T n d h1).1
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [norm_nonneg (toCLM T (cpairD T .zero n d) Υ)]
  have hY2 : ∀ (n : ℤ) d, ‖toCLM T (cpairSing T n d) Υ‖ ^ 2 ≤ 2 := fun n d => by
    have h := (norm_cpair_apply_le_dev T n d h1).2
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [norm_nonneg (toCLM T (cpairSing T n d) Υ)]
  have hA := hocc (fun n d => ‖toCLM T (cpairD T .zero n d) Υ‖ ^ 2) (twA_dev T θ)
    (fun d => θ ^ 2 / 2 * (2 * (d : ℝ) ^ 3 * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4))) (hs3.mul_left _)
    (fun d => by positivity) (fun n d => (twA_le_dev T θ n d).1) hceA (fun n d => sq_nonneg _) hX2
    (fun d => (occ_sum_dev T hΥ h1 d).1)
  have hB := hocc (fun n d => ‖toCLM T (cpairSing T n d) Υ‖ ^ 2) (twB_dev T θ)
    (fun d => θ * (2 * (d : ℝ) ^ 2 * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4))) (hs2.mul_left _)
    (fun d => by positivity) (fun n d => (twB_le_dev T hθ n d).1) hceB (fun n d => sq_nonneg _) hY2
    (fun d => (occ_sum_dev T hΥ h1 d).2)
  rw [hs3.tsum_mul_left] at hA
  rw [hs2.tsum_mul_left] at hB
  have hA3 : ∑ n ∈ Finset.range (2 * T.Nφ), ∑' d, twA_dev T θ ((n : ℕ) : ℤ) d *
      ‖toCLM T (cpairD T .zero ((n : ℕ) : ℤ) d) Υ‖ ^ 2 ≤ θ ^ 2 / 2 * gaussSum T.κ 3 * T.N := hA
  have hB3 : ∑ n ∈ Finset.range (2 * T.Nφ), ∑' d, twB_dev T θ ((n : ℕ) : ℤ) d *
      ‖toCLM T (cpairSing T ((n : ℕ) : ℤ) d) Υ‖ ^ 2 ≤ θ * gaussSum T.κ 2 * T.N := hB
  have ha : 0 ≤ 2 * (θ ^ 2 / 2 * gaussSum T.κ 3) := by positivity
  have hb : 0 ≤ 2 * (θ * gaussSum T.κ 2) := by positivity
  calc ∑ n ∈ Finset.range (2 * T.Nφ), ‖toCLM T (twistSum T θ ((n : ℕ) : ℤ)) Υ‖ ^ 2
      ≤ ∑ n ∈ Finset.range (2 * T.Nφ),
          (2 * (θ ^ 2 / 2 * gaussSum T.κ 3) * ∑' d, twA_dev T θ ((n : ℕ) : ℤ) d *
              ‖toCLM T (cpairD T .zero ((n : ℕ) : ℤ) d) Υ‖ ^ 2 +
            2 * (θ * gaussSum T.κ 2) * ∑' d, twB_dev T θ ((n : ℕ) : ℤ) d *
              ‖toCLM T (cpairSing T ((n : ℕ) : ℤ) d) Υ‖ ^ 2) :=
        Finset.sum_le_sum fun n _ => twistSum_apply_sq_le_dev T hθ _ h1
    _ = 2 * (θ ^ 2 / 2 * gaussSum T.κ 3) * ∑ n ∈ Finset.range (2 * T.Nφ), ∑' d, twA_dev T θ ((n : ℕ) : ℤ) d *
              ‖toCLM T (cpairD T .zero ((n : ℕ) : ℤ) d) Υ‖ ^ 2 +
          2 * (θ * gaussSum T.κ 2) * ∑ n ∈ Finset.range (2 * T.Nφ), ∑' d, twB_dev T θ ((n : ℕ) : ℤ) d *
              ‖toCLM T (cpairSing T ((n : ℕ) : ℤ) d) Υ‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (θ ^ 2 / 2 * gaussSum T.κ 3) * (θ ^ 2 / 2 * gaussSum T.κ 3 * T.N) +
          2 * (θ * gaussSum T.κ 2) * (θ * gaussSum T.κ 2 * T.N) :=
        add_le_add (mul_le_mul_of_nonneg_left hA3 ha) (mul_le_mul_of_nonneg_left hB3 hb)
    _ = _ := by ring

/-- **Lemma D.4**, (D.3): "`Let $\Upsilon$ be a unit vector with $N$ electrons such that $H_N\Upsilon=0$. Then`"
"`\ip{\mathcal W_\up\Upsilon}{H_N\mathcal W_\up\Upsilon}=\frac{\kappa^3}{\sqrt{2\pi}}\sum_{n\in\Z_{2\Nphi}}\Bigl\lVert\sum_{d}2d\,e^{-\kappa^2d^2/4} \Bigl[\Bigl(\cos\frac{\pi d}\Nphi-1\Bigr)c^0_{n,d}+\iu\sin\frac{\pi d}\Nphi\,c^{\rm sing}_{n,d}\Bigr]\Upsilon\Bigr\rVert^2`"
"`the inner sum running over $d\in\N$ with $d\equiv n\pmod2$, for any representative of the class $n$; and`" -/
theorem twist_energy_identity (T : Torus) {Υ : FockSpace T} (hΥ : Υ ∈ KN T) (h1 : ‖Υ‖ = 1) :
    ⟪toCLM T (twist T .up) Υ, toCLM T (HN T) (toCLM T (twist T .up) Υ)⟫_ℂ =
      ((T.κ ^ 3 / Real.sqrt (2 * π) *
        ∑ n ∈ Finset.range (2 * T.Nφ), ‖toCLM T (twistSum T (π / (T.Nφ : ℝ)) (n : ℤ)) Υ‖ ^ 2 : ℝ) : ℂ) := by
  refine energy_identity_dev T (mul_conjTranspose_self_of_mem_unitary (twist_mem_unitary T .up)) hΥ
    (fun n => Complex.exp (2 * π * I * (n : ℂ) / (T.Nφ : ℂ))) (fun _ => 1)
    (fun n => Complex.exp (π * I * (n : ℂ) / (T.Nφ : ℂ))) (fun n => ?_) (twistUp_conj_bcen_dev T)
  rw [show (π : ℂ) * I * (n : ℂ) / (T.Nφ : ℂ) = ((π * n / T.Nφ : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Lemma D.4**, (D.4): "`Let $\Upsilon$ be a unit vector with $N$ electrons such that $H_N\Upsilon=0$. Then`"
"`\ip{\mathcal W_\up\Upsilon}{H_N\mathcal W_\up\Upsilon}\le\frac{\kappa^3}{\sqrt{2\pi}}\Bigl(\frac{\pi^2\,\mathsf G_2(\kappa)^2}{2N} +\frac{\pi^4\,\mathsf G_3(\kappa)^2}{32N^3}\Bigr).`" -/
theorem twist_energy_le (T : Torus) {Υ : FockSpace T} (hΥ : Υ ∈ KN T) (h1 : ‖Υ‖ = 1) :
    (⟪toCLM T (twist T .up) Υ, toCLM T (HN T) (toCLM T (twist T .up) Υ)⟫_ℂ).re ≤
      T.κ ^ 3 / Real.sqrt (2 * π) *
        (π ^ 2 * gaussSum T.κ 2 ^ 2 / (2 * (T.N : ℝ)) + π ^ 4 * gaussSum T.κ 3 ^ 2 / (32 * (T.N : ℝ) ^ 3)) := by
  rw [twist_energy_identity T hΥ h1, Complex.ofReal_re]
  have hc : 0 ≤ T.κ ^ 3 / Real.sqrt (2 * π) := by have := T.κ_pos; positivity
  have hθ : (0 : ℝ) ≤ π / (T.Nφ : ℝ) := by positivity
  have h := twistSum_sum_sq_le_dev T hθ hΥ h1
  have hNpos : (0 : ℝ) < T.N := by exact_mod_cast T.N_pos
  have hNφ : (T.Nφ : ℝ) = 2 * (T.N : ℝ) := by rw [Torus.Nφ]; push_cast; ring
  refine (mul_le_mul_of_nonneg_left h hc).trans (le_of_eq ?_)
  rw [hNφ]
  field_simp
  ring

/-- **Lemma D.4**, the two-species twist, (D.3): "`For the two-species twist $\mathcal W_\up\mathcal W_\dn^*$ in place of $\mathcal W_\up$, \eqref{eq:twist-identity} holds with $\pi d/\Nphi$ replaced by $2\pi d/\Nphi$, and \eqref{eq:twist-energy} with its first term multiplied by four and its second term by sixteen.`" -/
theorem twistTwo_energy_identity (T : Torus) {Υ : FockSpace T} (hΥ : Υ ∈ KN T) (h1 : ‖Υ‖ = 1) :
    ⟪toCLM T (twistTwo T) Υ, toCLM T (HN T) (toCLM T (twistTwo T) Υ)⟫_ℂ =
      ((T.κ ^ 3 / Real.sqrt (2 * π) *
        ∑ n ∈ Finset.range (2 * T.Nφ), ‖toCLM T (twistSum T (2 * π / (T.Nφ : ℝ)) (n : ℤ)) Υ‖ ^ 2 : ℝ) : ℂ) := by
  have hU : twistTwo T * (twistTwo T)ᴴ = 1 := by
    have h1 := mul_conjTranspose_self_of_mem_unitary (twist_mem_unitary T .up)
    have h2 := conjTranspose_mul_self_of_mem_unitary (twist_mem_unitary T .dn)
    rw [twistTwo, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      show twist T .up * (twist T .dn)ᴴ * (twist T .dn * (twist T .up)ᴴ) =
        twist T .up * ((twist T .dn)ᴴ * twist T .dn) * (twist T .up)ᴴ by simp only [mul_assoc], h2, mul_one, h1]
  exact energy_identity_dev T hU hΥ
    (fun n => Complex.exp (2 * π * I * (n : ℂ) / (T.Nφ : ℂ))) (fun n => Complex.exp (-(2 * π * I * (n : ℂ) / (T.Nφ : ℂ))))
    (fun _ => 1) (fun _ => norm_one) (twistTwo_conj_bcen_dev T)

/-- **Lemma D.4**, the two-species twist, (D.4): "`For the two-species twist $\mathcal W_\up\mathcal W_\dn^*$ in place of $\mathcal W_\up$, \eqref{eq:twist-identity} holds with $\pi d/\Nphi$ replaced by $2\pi d/\Nphi$, and \eqref{eq:twist-energy} with its first term multiplied by four and its second term by sixteen.`" -/
theorem twistTwo_energy_le (T : Torus) {Υ : FockSpace T} (hΥ : Υ ∈ KN T) (h1 : ‖Υ‖ = 1) :
    (⟪toCLM T (twistTwo T) Υ, toCLM T (HN T) (toCLM T (twistTwo T) Υ)⟫_ℂ).re ≤
      T.κ ^ 3 / Real.sqrt (2 * π) *
        (4 * (π ^ 2 * gaussSum T.κ 2 ^ 2 / (2 * (T.N : ℝ))) +
          16 * (π ^ 4 * gaussSum T.κ 3 ^ 2 / (32 * (T.N : ℝ) ^ 3))) := by
  rw [twistTwo_energy_identity T hΥ h1, Complex.ofReal_re]
  have hc : 0 ≤ T.κ ^ 3 / Real.sqrt (2 * π) := by have := T.κ_pos; positivity
  have hθ : (0 : ℝ) ≤ 2 * π / (T.Nφ : ℝ) := by positivity
  have h := twistSum_sum_sq_le_dev T hθ hΥ h1
  have hNpos : (0 : ℝ) < T.N := by exact_mod_cast T.N_pos
  have hNφ : (T.Nφ : ℝ) = 2 * (T.N : ℝ) := by rw [Torus.Nφ]; push_cast; ring
  refine (mul_le_mul_of_nonneg_left h hc).trans (le_of_eq ?_)
  rw [hNφ]
  field_simp
  ring

/-! ## Lemma D.5: a zero mode twisted off the kernel -/

/-- **Lemma D.5**: "`the root of unity $e^{2\pi\iu n_\up/\Nphi}$, respectively $e^{2\pi\iu(n_\up-n_\dn)/\Nphi}$`" — for every
integer `k`, `e^{2πik/N_φ}` has positive order, so `orderOf` is the paper's "`(the least $k\ge1$ for which its $k$-th power is $1$)`". -/
theorem orderOf_exp_pos (T : Torus) (k : ℤ) : 0 < orderOf (Complex.exp (2 * π * I * (k : ℂ) / (T.Nφ : ℂ))) := by
  rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
  refine ⟨T.Nφ, T.Nφ_pos, ?_⟩
  rw [← Complex.exp_nat_mul]
  have hN : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
  rw [show (T.Nφ : ℂ) * (2 * π * I * (k : ℂ) / (T.Nφ : ℂ)) = (k : ℂ) * (2 * π * I) by field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-! ### Proof devices for Lemma D.5 (proof phase, round one; not statements of the paper)

On the sector, `Θ 𝒲 v = ω 𝒲 Θ v` for both twists (`Θ_twist_apply_dev`, `Θ_twistTwo_apply_dev`, from Lemma D.3(iii)).
The proof of `twist_off_kernel` replaces the paper's count of the dimensions along the `ω`-orbits by an equivalent
determinant argument on `K = 𝒦_N ∩ 𝓗^𝐧`: `Θ` and `Θ^*` preserve `K`, so `Θ` commutes with the orthogonal projection onto
`K`, and the compression `C = Π_K 𝒲|_K` satisfies `Θ C = ω C Θ` on `K`. If `ker C = 0`, `C` is invertible and the
determinants give `ω^{dim K} = 1`, so the order of `ω` divides `dim K`, against the hypothesis; otherwise `ker C` is a
nonzero `Θ`-invariant subspace, on which `Θ` has an eigenvector (`Θ^{N_φ} = 1` and F1-upper's finite-Fourier
projectors `Qop_dev` of `ZeroModes.Spaces`), and for it `𝒲Υ` is orthogonal to `K`, hence (it lies in the sector) to
`𝒦_N`. -/

theorem Θ_twist_apply_dev (T : Torus) (nn : SectorLabel T) {v : FockSpace T} (hv : v ∈ sector T nn) :
    toCLM T (Θ T) (toCLM T (twist T .up) v) =
      Complex.exp (2 * π * I * ((nn.1 : ℕ) : ℂ) / (T.Nφ : ℂ)) • toCLM T (twist T .up) (toCLM T (Θ T) v) := by
  have hΘv : toCLM T (Θ T) v ∈ sector T nn := toCLM_mem_sector_dev (Θ_isSectorPreserving T) nn hv
  rw [toCLM_conj_apply_dev, Θ_twist_conj_inv_dev, toCLM_mul_dev, mul_apply_eq_comp,
    exp_Nsig_sector_dev T .up _ nn (twist_mem_sector T .up nn hΘv)]
  congr 2
  simp only [secN]
  ring

theorem Θ_twistTwo_apply_dev (T : Torus) (nn : SectorLabel T) {v : FockSpace T} (hv : v ∈ sector T nn) :
    toCLM T (Θ T) (toCLM T (twistTwo T) v) =
      Complex.exp (2 * π * I * (((nn.1 : ℕ) : ℂ) - ((nn.2 : ℕ) : ℂ)) / (T.Nφ : ℂ)) •
        toCLM T (twistTwo T) (toCLM T (Θ T) v) := by
  have hu1 : (Θ T)ᴴ * Θ T = 1 := conjTranspose_mul_self_of_mem_unitary (Θ_mem_unitary T)
  have hΘv : toCLM T (Θ T) v ∈ sector T nn := toCLM_mem_sector_dev (Θ_isSectorPreserving T) nn hv
  have hsplit : Θ T * twistTwo T * (Θ T)ᴴ =
      (Θ T * twist T .up * (Θ T)ᴴ) * (Θ T * twist T .dn * (Θ T)ᴴ)ᴴ := by
    rw [twistTwo]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]
    rw [← mul_assoc (Θ T)ᴴ (Θ T), hu1, one_mul]
  have hdn : toCLM T (NormedSpace.exp ((2 * π * I / (T.Nφ : ℂ)) • Nsig T .dn))ᴴ (toCLM T (Θ T) v) =
      star (Complex.exp ((2 * π * I / (T.Nφ : ℂ)) * ((nn.2 : ℕ) : ℂ))) • toCLM T (Θ T) v := by
    rw [exp_smul_Nsig_dev, Matrix.diagonal_conjTranspose]
    exact toCLM_diagonal_sector_dev T nn _ _ (fun m hm => by
      rw [Pi.star_apply, ctσ_of_secOf_dev T nn m hm .dn]
      rfl) hΘv
  have hmem : toCLM T (twist T .up) (toCLM T (twist T .dn)ᴴ (toCLM T (Θ T) v)) ∈ sector T nn :=
    twist_mem_sector T .up nn (toCLM_mem_sector_dev (twistDn_conjT_isSectorPreserving_dev T) nn hΘv)
  rw [toCLM_conj_apply_dev, hsplit, Θ_twist_conj_inv_dev, Θ_twist_conj_inv_dev, Matrix.conjTranspose_mul]
  simp only [toCLM_mul_dev, mul_apply_eq_comp]
  rw [hdn, map_smul, map_smul, map_smul, exp_Nsig_sector_dev T .up _ nn hmem, smul_smul, twistTwo,
    toCLM_mul_dev, mul_apply_eq_comp, star_exp_phase_dev]
  congr 1
  simp only [secN]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- **Lemma D.5**: "`Let $\nn=(n_\up,n_\dn)$ be a sector with $n_\up+n_\dn=N$, and let $\mathcal W$ be $\mathcal W_\up$ or $\mathcal W_\up\mathcal W_\dn^*$.`"
"`Suppose that the dimension of $\mathcal K_N\cap\sect\nn$ is not divisible by the order of the root of unity $e^{2\pi\iu n_\up/\Nphi}$, respectively $e^{2\pi\iu(n_\up-n_\dn)/\Nphi}$ (the least $k\ge1$ for which its $k$-th power is $1$).`"
"`Then there is a unit vector $\Upsilon\in\mathcal K_N\cap\sect\nn$, an eigenvector of $\Theta$, such that $\mathcal W\Upsilon$ is orthogonal to $\mathcal K_N$.`"
— the order is `orderOf ω` (positive: `orderOf_exp_pos`). -/
theorem twist_off_kernel (T : Torus) (nn : SectorLabel T) (hN : (nn.1 : ℕ) + (nn.2 : ℕ) = T.N)
    {W : FockOp T} {ω : ℂ}
    (hW : (W = twist T .up ∧ ω = Complex.exp (2 * π * I * ((nn.1 : ℕ) : ℂ) / (T.Nφ : ℂ))) ∨
      (W = twistTwo T ∧ ω = Complex.exp (2 * π * I * (((nn.1 : ℕ) : ℂ) - ((nn.2 : ℕ) : ℂ)) / (T.Nφ : ℂ))))
    (hord : ¬ orderOf ω ∣ Module.finrank ℂ ↥(KN T ⊓ sector T nn)) :
    ∃ Υ ∈ KN T ⊓ sector T nn, ‖Υ‖ = 1 ∧ (∃ μ : ℂ, toCLM T (Θ T) Υ = μ • Υ) ∧ toCLM T W Υ ∈ (KN T)ᗮ := by
  classical
  set K := KN T ⊓ sector T nn with hKdef
  have hKeq : K = LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T nn := KN_inf_sector T nn hN
  have hWrel : ∀ v ∈ sector T nn, toCLM T (Θ T) (toCLM T W v) = ω • toCLM T W (toCLM T (Θ T) v) := by
    rcases hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fun v hv => Θ_twist_apply_dev T nn hv
    · exact fun v hv => Θ_twistTwo_apply_dev T nn hv
  have hWsec : ∀ v ∈ sector T nn, toCLM T W v ∈ sector T nn := by
    rcases hW with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact fun v hv => twist_mem_sector T .up nn hv
    · intro v hv
      rw [twistTwo, toCLM_mul_dev, mul_apply_eq_comp]
      exact twist_mem_sector T .up nn (toCLM_mem_sector_dev (twistDn_conjT_isSectorPreserving_dev T) nn hv)
  have hω : ω ≠ 0 := by
    rcases hW with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact Complex.exp_ne_zero _
  have hΘH : Commute (Θ T) (HN T) := commute_Θ_HN T
  have hu1 : (Θ T)ᴴ * Θ T = 1 := conjTranspose_mul_self_of_mem_unitary (Θ_mem_unitary T)
  have hu2 : Θ T * (Θ T)ᴴ = 1 := mul_conjTranspose_self_of_mem_unitary (Θ_mem_unitary T)
  have hΘhH : Commute (Θ T)ᴴ (HN T) := by
    show (Θ T)ᴴ * HN T = HN T * (Θ T)ᴴ
    calc (Θ T)ᴴ * HN T = (Θ T)ᴴ * HN T * (Θ T * (Θ T)ᴴ) := by rw [hu2, mul_one]
      _ = (Θ T)ᴴ * (HN T * Θ T) * (Θ T)ᴴ := by simp only [mul_assoc]
      _ = (Θ T)ᴴ * (Θ T * HN T) * (Θ T)ᴴ := by rw [hΘH.eq]
      _ = HN T * (Θ T)ᴴ := by rw [← mul_assoc, hu1, one_mul]
  have hΘhsec : IsSectorPreserving T (Θ T)ᴴ := by
    obtain ⟨h1, h2⟩ := Θ_isSectorPreserving T
    refine ⟨?_, ?_⟩
    · have := congrArg Matrix.conjTranspose h1.eq
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Nsig_conjTranspose] at this
      exact this.symm
    · have := congrArg Matrix.conjTranspose h2.eq
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Nsig_conjTranspose] at this
      exact this.symm
  have hpres : ∀ {A : FockOp T}, Commute A (HN T) → IsSectorPreserving T A → ∀ v ∈ K, toCLM T A v ∈ K := by
    intro A hAH hAs v hv
    rw [hKeq] at hv ⊢
    obtain ⟨hk, hs⟩ := Submodule.mem_inf.1 hv
    refine Submodule.mem_inf.2 ⟨?_, toCLM_mem_sector_dev hAs nn hs⟩
    rw [LinearMap.mem_ker, toEuclideanLin_apply_dev] at hk ⊢
    rw [← mul_apply_eq_comp, ← toCLM_mul_dev, ← hAH.eq, toCLM_mul_dev, mul_apply_eq_comp, hk, map_zero]
  have hΘK : ∀ v ∈ K, toCLM T (Θ T) v ∈ K := hpres hΘH (Θ_isSectorPreserving T)
  have hΘhK : ∀ v ∈ K, toCLM T (Θ T)ᴴ v ∈ K := hpres hΘhH hΘhsec
  have hKsec : ∀ v ∈ K, v ∈ sector T nn := fun v hv => (Submodule.mem_inf.1 hv).2
  have hPΘ : ∀ x : FockSpace T, K.starProjection (toCLM T (Θ T) x) = toCLM T (Θ T) (K.starProjection x) := by
    intro x
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hΘK _ (K.starProjection_apply_mem x)) fun w hw => ?_
    rw [← map_sub, toCLM_conjTranspose_inner_dev]
    exact Submodule.starProjection_inner_eq_zero x _ (hΘhK w hw)
  let C : K →ₗ[ℂ] K := (K.orthogonalProjectionOnto : FockSpace T →ₗ[ℂ] K) ∘ₗ
    ((toCLM T W : FockSpace T →ₗ[ℂ] FockSpace T) ∘ₗ K.subtype)
  let ΘK : K →ₗ[ℂ] K := (toCLM T (Θ T) : FockSpace T →ₗ[ℂ] FockSpace T).restrict hΘK
  have hC : ∀ v : K, ((C v : K) : FockSpace T) = K.starProjection (toCLM T W v) := by
    intro v
    rw [Submodule.starProjection_apply]
    rfl
  have hΘKapp : ∀ v : K, ((ΘK v : K) : FockSpace T) = toCLM T (Θ T) v := fun v => rfl
  have hrel : ΘK ∘ₗ C = ω • (C ∘ₗ ΘK) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_smul]
    rw [hΘKapp, hC, hC, hΘKapp, ← hPΘ, hWrel _ (hKsec _ v.2), map_smul]
  by_cases hker : LinearMap.ker C = ⊥
  · exfalso
    have hCu : IsUnit C := (LinearMap.isUnit_iff_ker_eq_bot C).2 hker
    have hΘu : IsUnit ΘK := by
      rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have h0 : toCLM T (Θ T) (v : FockSpace T) = 0 := by
        have := congrArg Subtype.val hv
        simpa [ΘK] using this
      have h1 : toCLM T (Θ T)ᴴ (toCLM T (Θ T) (v : FockSpace T)) = (v : FockSpace T) := by
        rw [← mul_apply_eq_comp, ← toCLM_mul_dev, hu1]
        simp
      rw [h0, map_zero] at h1
      exact Subtype.ext h1.symm
    have hdet := congrArg LinearMap.det hrel
    rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_comp] at hdet
    have hdC := LinearMap.isUnit_det C hCu
    have hdΘ := LinearMap.isUnit_det ΘK hΘu
    have hne : LinearMap.det ΘK * LinearMap.det C ≠ 0 := (hdΘ.mul hdC).ne_zero
    have hpow : ω ^ Module.finrank ℂ K = 1 := by
      have h2 : (ω ^ Module.finrank ℂ K - 1) * (LinearMap.det ΘK * LinearMap.det C) = 0 := by
        linear_combination -hdet
      rcases mul_eq_zero.1 h2 with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h hne
    exact hord (orderOf_dvd_of_pow_eq_one hpow)
  · have hinv : ∀ x ∈ LinearMap.ker C, ΘK x ∈ LinearMap.ker C := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have h := LinearMap.congr_fun hrel x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, hx, map_zero] at h
      exact (smul_eq_zero.1 h.symm).resolve_left hω
    let ΘC : Module.End ℂ (LinearMap.ker C) := ΘK.restrict hinv
    have hΘCapp : ∀ z : LinearMap.ker C, (((ΘC z : LinearMap.ker C) : K) : FockSpace T) =
        toCLM T (Θ T) ((z : K) : FockSpace T) := fun z => rfl
    have hΘCpow : ∀ (n : ℕ) (z : LinearMap.ker C), ((((ΘC ^ n) z : LinearMap.ker C) : K) : FockSpace T) =
        toCLM T (Θ T ^ n) ((z : K) : FockSpace T) := by
      intro n z
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, hΘCapp, ih, pow_succ', toCLM_mul_dev, mul_apply_eq_comp]
    obtain ⟨x0, hx0mem, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hpowx : (ΘC ^ T.Nφ) ⟨x0, hx0mem⟩ = ⟨x0, hx0mem⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hΘCpow, Θ_pow]
      simp
    have hsum : ∑ j : Fin T.Nφ, Qop_dev T.Nφ j ΘC ⟨x0, hx0mem⟩ =
        (T.Nφ : ℂ) • (⟨x0, hx0mem⟩ : LinearMap.ker C) := by
      rw [← LinearMap.sum_apply, sum_Qop_dev T.Nφ_pos]
      rfl
    have hsne : (T.Nφ : ℂ) • (⟨x0, hx0mem⟩ : LinearMap.ker C) ≠ 0 := by
      refine smul_ne_zero (by exact_mod_cast T.Nφ_pos.ne') fun h => hx00 ?_
      exact congrArg Subtype.val h
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum ▸ hsne)
    set x := Qop_dev T.Nφ j ΘC ⟨x0, hx0mem⟩ with hxdef
    have hx0 : x ≠ 0 := hj
    set c : ℂ := Complex.exp (2 * π * I * ((j : ℕ) : ℂ) / (T.Nφ : ℂ)) with hcdef
    have hxe : ΘC x = c • x := Qop_eigen_dev T.Nφ_pos j ΘC hpowx
    set y : FockSpace T := ((x : K) : FockSpace T) with hy
    have hyK : y ∈ K := (x : K).2
    have hy0 : y ≠ 0 := by
      intro h
      apply hx0
      apply Subtype.ext
      apply Subtype.ext
      exact h
    have hΘy : toCLM T (Θ T) y = c • y := by
      have := congrArg (fun z : LinearMap.ker C => ((z : K) : FockSpace T)) hxe
      simpa [ΘC, ΘK] using this
    have hCy : K.starProjection (toCLM T W y) = 0 := by
      rw [← hC]
      have := x.2
      rw [LinearMap.mem_ker] at this
      rw [this]
      rfl
    have hWy : toCLM T W y ∈ Kᗮ := (Submodule.starProjection_apply_eq_zero_iff K).1 hCy
    have hny : 0 < ‖y‖ := norm_pos_iff.2 hy0
    refine ⟨((‖y‖ : ℝ)⁻¹ : ℂ) • y, K.smul_mem _ hyK, ?_, ⟨c, ?_⟩, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hny, inv_mul_cancel₀ hny.ne']
    · rw [map_smul, hΘy, smul_comm]
    · rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      intro u hu
      have hsec : toCLM T W y ∈ sector T nn := hWsec y (hKsec y hyK)
      have hPu : toCLM T (Psec T nn) u ∈ K := by
        rw [hKeq]
        exact Psec_mem_ker_sector_dev T nn (Submodule.mem_inf.1 hu).1
      have hself : toCLM T (Psec T nn) (toCLM T W y) = toCLM T W y := (mem_sector_iff_Psec_dev nn _).1 hsec
      rw [← hself, toCLM_Psec_dev, ← Submodule.inner_starProjection_left_eq_right, ← toCLM_Psec_dev]
      exact Submodule.inner_right_of_mem_orthogonal hPu hWy

/-! ## Theorem D.1 -/

/-- **(D.2)**, the left-hand side: "`\frac{\kappa^3}{\sqrt{2\pi}}\Bigl(\frac{\pi^2\,\mathsf G_2(\kappa)^2}{2N}+\frac{\pi^4\,\mathsf G_3(\kappa)^2}{32N^3}\Bigr)`" -/
def twistBound (T : Torus) : ℝ :=
  T.κ ^ 3 / Real.sqrt (2 * π) *
    (π ^ 2 * gaussSum T.κ 2 ^ 2 / (2 * (T.N : ℝ)) + π ^ 4 * gaussSum T.κ 3 ^ 2 / (32 * (T.N : ℝ) ^ 3))

/-- **(D.2)**, the right-hand side: "`\le\frac1{\sqrt{2\pi}}\Bigl(1+\frac{2\kappa}{e\sqrt\pi}\Bigr)^2\frac{L_y^3}N +\frac1{4\pi\sqrt{2\pi}}\Bigl(1+\frac{(6/e)^{3/2}\kappa}8\Bigr)^2\frac{L_y^5}{N^3}.`" -/
def twistBoundLy (T : Torus) : ℝ :=
  1 / Real.sqrt (2 * π) * (1 + 2 * T.κ / (Real.exp 1 * Real.sqrt π)) ^ 2 * (T.Ly ^ 3 / (T.N : ℝ)) +
    1 / (4 * π * Real.sqrt (2 * π)) * (1 + (6 / Real.exp 1) ^ (3 / 2 : ℝ) * T.κ / 8) ^ 2 *
      (T.Ly ^ 5 / (T.N : ℝ) ^ 3)

/-- **Theorem D.1**, the numerical form: "`0.40\,(1+0.42\,\kappa)^2\,\frac{L_y^3}N+0.032\,(1+0.41\,\kappa)^2\,\frac{L_y^5}{N^3}.`" -/
def twistBoundNum (T : Torus) : ℝ :=
  0.40 * (1 + 0.42 * T.κ) ^ 2 * (T.Ly ^ 3 / (T.N : ℝ)) + 0.032 * (1 + 0.41 * T.κ) ^ 2 * (T.Ly ^ 5 / (T.N : ℝ) ^ 3)

/-! ### Proof device for Theorem D.1 (proof phase, round one; not a statement of the paper)

The roots of Lemma D.5 at the sectors of Theorem D.1: `ω^p ≠ 1` for `ω = e^{2πik/N_φ}` unless `N_φ ∣ pk`
(`exp_pow_ne_one_dev`). At even `N`, `ω = e^{2πi(N/2)/(2N)} = i` and `ω^{10} ≠ 1`, so its order does not divide ten; at odd
`N ≥ 3`, `ω = e^{2πi((N±1)/2)/(2N)}` and `ω² ≠ 1` (`0 < (N±1)/2 < N`), so its order does not divide two. -/

theorem exp_pow_ne_one_dev (T : Torus) (k p : ℕ) (h : ¬ T.Nφ ∣ p * k) :
    Complex.exp (2 * π * I * (k : ℂ) / (T.Nφ : ℂ)) ^ p ≠ 1 := by
  intro hp
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at hp
  obtain ⟨z, hz⟩ := hp
  have hN0 : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
  have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have e : (p : ℂ) * (2 * π * I * (k : ℂ) / (T.Nφ : ℂ)) = (2 * π * I) * ((p : ℂ) * (k : ℂ)) / (T.Nφ : ℂ) := by
    ring
  rw [e, div_eq_iff hN0] at hz
  have h2 : (2 * π * I : ℂ) * ((p : ℂ) * (k : ℂ) - (z : ℂ) * (T.Nφ : ℂ)) = 0 := by linear_combination hz
  have h3 : ((p * k : ℕ) : ℤ) = z * (T.Nφ : ℤ) := by
    rcases mul_eq_zero.1 h2 with h0 | h0
    · exact absurd h0 hpi
    · have h4 : ((p * k : ℕ) : ℂ) = ((z * (T.Nφ : ℤ) : ℤ) : ℂ) := by push_cast; linear_combination h0
      exact_mod_cast h4
  apply h
  have h5 : (T.Nφ : ℤ) ∣ ((p * k : ℕ) : ℤ) := ⟨z, by rw [h3]; ring⟩
  exact_mod_cast h5

/-- **Theorem D.1**, the sentence after it: "`The unit vector of the theorem is $\mathcal W_\up\Upsilon$ for a suitable zero mode $\Upsilon\in\mathcal K_N\cap\sect\nn$, with the twist $\mathcal W_\up$ of Lemma~\ref{lem:twists} below.`"
— the content of Theorem D.1's first claim (Lemmas D.5 and D.4 with Theorem 2.10). -/
theorem twist_bound_explicit (T : Torus) (hN : 2 ≤ T.N) (nn : SectorLabel T)
    (hnn : (Even T.N ∧ nn = halfSector T) ∨ (Odd T.N ∧ (nn = oddSectorPlus T ∨ nn = oddSectorMinus T))) :
    ∃ Υ ∈ KN T ⊓ sector T nn, ‖Υ‖ = 1 ∧ toCLM T (twist T .up) Υ ∈ (KN T)ᗮ ∧
      (⟪toCLM T (twist T .up) Υ, toCLM T (HN T) (toCLM T (twist T .up) Υ)⟫_ℂ).re ≤ twistBound T := by
  have hNφ : T.Nφ = 2 * T.N := rfl
  have hsum : (nn.1 : ℕ) + (nn.2 : ℕ) = T.N := by
    rcases hnn with ⟨⟨r, hr⟩, rfl⟩ | ⟨⟨m, hm⟩, rfl | rfl⟩
    · show T.N / 2 + T.N / 2 = T.N
      omega
    · show (T.N + 1) / 2 + (T.N - 1) / 2 = T.N
      omega
    · show (T.N - 1) / 2 + (T.N + 1) / 2 = T.N
      omega
  have hord : ¬ orderOf (Complex.exp (2 * π * I * ((nn.1 : ℕ) : ℂ) / (T.Nφ : ℂ))) ∣
      Module.finrank ℂ ↥(KN T ⊓ sector T nn) := by
    rw [KN_inf_sector T nn hsum, orderOf_dvd_iff_pow_eq_one]
    rcases hnn with ⟨heven, rfl⟩ | ⟨hodd, rfl | rfl⟩
    · rw [finrank_kernel_half T heven]
      refine exp_pow_ne_one_dev T (T.N / 2) 10 ?_
      obtain ⟨r, hr⟩ := heven
      have hr0 : 0 < r := by omega
      rw [show T.Nφ = 4 * r by omega, show T.N / 2 = r by omega, Nat.mul_dvd_mul_iff_right hr0]
      decide
    · rw [(finrank_kernel_odd T hodd).1]
      refine exp_pow_ne_one_dev T ((T.N + 1) / 2) 2 ?_
      intro hd
      obtain ⟨m, hm⟩ := hodd
      have h0 : 0 < 2 * ((T.N + 1) / 2) := by omega
      have := Nat.le_of_dvd h0 hd
      omega
    · rw [(finrank_kernel_odd T hodd).2]
      refine exp_pow_ne_one_dev T ((T.N - 1) / 2) 2 ?_
      intro hd
      obtain ⟨m, hm⟩ := hodd
      have h0 : 0 < 2 * ((T.N - 1) / 2) := by omega
      have := Nat.le_of_dvd h0 hd
      omega
  obtain ⟨Υ, hΥ, h1, -, hort⟩ := twist_off_kernel T nn hsum (Or.inl ⟨rfl, rfl⟩) hord
  exact ⟨Υ, hΥ, h1, hort, twist_energy_le T (Submodule.mem_inf.1 hΥ).1 h1⟩

/-- **Theorem D.1**: "`Let $N\ge2$. If $N$ is even, let $\nn:=(N/2,N/2)$; if $N$ is odd, let $\nn$ be $((N+1)/2,(N-1)/2)$ or $((N-1)/2,(N+1)/2)$. Then $\sect\nn$ contains a unit vector, orthogonal to $\mathcal K_N$, at which the expectation of $H_N$ is at most`"
the left-hand side of (D.2) (`twistBound`). Derived from `twist_bound_explicit` (the vector `𝒲_↑Υ`: in the sector by
`twist_mem_sector`, a unit vector by `twist_mem_unitary`; written out). -/
theorem twist_bound (T : Torus) (hN : 2 ≤ T.N) (nn : SectorLabel T)
    (hnn : (Even T.N ∧ nn = halfSector T) ∨ (Odd T.N ∧ (nn = oddSectorPlus T ∨ nn = oddSectorMinus T))) :
    ∃ v ∈ sector T nn, ‖v‖ = 1 ∧ v ∈ (KN T)ᗮ ∧ (⟪v, toCLM T (HN T) v⟫_ℂ).re ≤ twistBound T := by
  obtain ⟨Υ, hΥ, h1, hort, hle⟩ := twist_bound_explicit T hN nn hnn
  refine ⟨toCLM T (twist T .up) Υ, twist_mem_sector T .up nn (Submodule.mem_inf.1 hΥ).2, ?_, hort, hle⟩
  rw [ContinuousLinearMap.norm_map_of_mem_unitary (toCLM_mem_unitary T (twist_mem_unitary T .up)), h1]

/-- **Theorem D.1**, (D.2): "`\frac{\kappa^3}{\sqrt{2\pi}}\Bigl(\frac{\pi^2\,\mathsf G_2(\kappa)^2}{2N}+\frac{\pi^4\,\mathsf G_3(\kappa)^2}{32N^3}\Bigr)`"
"`\le\frac1{\sqrt{2\pi}}\Bigl(1+\frac{2\kappa}{e\sqrt\pi}\Bigr)^2\frac{L_y^3}N +\frac1{4\pi\sqrt{2\pi}}\Bigl(1+\frac{(6/e)^{3/2}\kappa}8\Bigr)^2\frac{L_y^5}{N^3}.`"
— on every torus (the inequality does not use `N ≥ 2`). -/
theorem twistBound_le_twistBoundLy (T : Torus) : twistBound T ≤ twistBoundLy T := by
  have hκ := T.κ_pos
  have hG2 := gaussSum_two_le hκ
  have hG3 := gaussSum_three_le hκ
  have hG2n : 0 ≤ gaussSum T.κ 2 := tsum_nonneg fun d => by positivity
  have hG3n : 0 ≤ gaussSum T.κ 3 := tsum_nonneg fun d => by positivity
  have hN : (0 : ℝ) < T.N := by exact_mod_cast T.N_pos
  have hLy : T.Ly = 2 * π / T.κ := by
    have := T.κ_mul_Ly
    field_simp
    linarith
  have hsq : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have hs2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hs2n : Real.sqrt (2 * π) ≠ 0 := hs2.ne'
  unfold twistBound twistBoundLy
  set a := 1 + 2 * T.κ / (Real.exp 1 * Real.sqrt π) with ha
  set b := 1 + (6 / Real.exp 1) ^ (3 / 2 : ℝ) * T.κ / 8 with hb
  have h2 : gaussSum T.κ 2 ^ 2 ≤ (4 * Real.sqrt π / T.κ ^ 3 * a) ^ 2 := pow_le_pow_left₀ hG2n hG2 2
  have h3 : gaussSum T.κ 3 ^ 2 ≤ (16 / T.κ ^ 4 * b) ^ 2 := pow_le_pow_left₀ hG3n hG3 2
  have hX : (4 * Real.sqrt π / T.κ ^ 3 * a) ^ 2 = 16 * π / T.κ ^ 6 * a ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, hsq]
    ring
  rw [hX] at h2
  have hc : 0 ≤ T.κ ^ 3 / Real.sqrt (2 * π) := by positivity
  have hstep : π ^ 2 * gaussSum T.κ 2 ^ 2 / (2 * (T.N : ℝ)) + π ^ 4 * gaussSum T.κ 3 ^ 2 / (32 * (T.N : ℝ) ^ 3) ≤
      π ^ 2 * (16 * π / T.κ ^ 6 * a ^ 2) / (2 * (T.N : ℝ)) +
        π ^ 4 * (16 / T.κ ^ 4 * b) ^ 2 / (32 * (T.N : ℝ) ^ 3) := by
    have e1 : π ^ 2 * gaussSum T.κ 2 ^ 2 ≤ π ^ 2 * (16 * π / T.κ ^ 6 * a ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e2 : π ^ 4 * gaussSum T.κ 3 ^ 2 ≤ π ^ 4 * (16 / T.κ ^ 4 * b) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    exact add_le_add (div_le_div_of_nonneg_right e1 (by positivity)) (div_le_div_of_nonneg_right e2 (by positivity))
  refine (mul_le_mul_of_nonneg_left hstep hc).trans (le_of_eq ?_)
  rw [hLy]
  field_simp
  ring

/-! ### Proof devices for the Rayleigh bound (proof phase, round one; not statements of the paper)

For a positive sector-preserving `H` the ordered eigenvalues are nonnegative (`secEig_nonneg_dev`, the argument of block
D's `secEig_HN_nonneg`), and the first `k = dim(ker H ∩ 𝓗^𝐧)` of them vanish (`secEig_zero_of_le_dev`, from block D's
`card_secEig_eq` at `μ = 0`). The proof of `rayleigh_dev` expands the vector in the eigenvector basis of
`secCompr_isSymmetric_dev`: the components along the kernel vanish, the others carry eigenvalues `E_j` with `j ≥ k + 1`. -/

theorem secEig_nonneg_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (hpos : H.PosSemidef) (nn : SectorLabel T) (k : ℕ) : 0 ≤ secEig T H nn k := by
  by_cases hd : Module.finrank ℂ (sector T nn) = 0
  · rw [secEig_of_finrank_eq_zero_dev hd]
  rw [secEig_congr_dev (b := min (max k 1) (Module.finrank ℂ (sector T nn))) (by omega)]
  obtain ⟨v, -, hv0, hHv⟩ := secEig_hasEigenvector hH hHs nn
    (k := min (max k 1) (Module.finrank ℂ (sector T nn))) (by omega) (min_le_right _ _)
  set μ := secEig T H nn (min (max k 1) (Module.finrank ℂ (sector T nn)))
  have hP : 0 ≤ (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re := by
    simpa using (Complex.le_def.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hpos).2 (WithLp.ofLp v))).1
  have e : star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v) = ⟪v, toCLM T H v⟫_ℂ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM, dotProduct_comm]
  rw [e, hHv, inner_smul_right, Complex.re_ofReal_mul] at hP
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hvv : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  have h2 : (0 : ℝ) ≤ μ * ‖v‖ ^ 2 := by
    rw [hvv] at hP
    exact hP
  by_contra hneg
  push Not at hneg
  nlinarith [mul_neg_of_neg_of_pos hneg (pow_pos hv 2)]

theorem secEig_zero_of_le_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (hpos : H.PosSemidef) (nn : SectorLabel T) {k : ℕ}
    (hk : Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) H) ⊓ sector T nn) = k)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) : secEig T H nn j = 0 := by
  classical
  have hcard := card_secEig_eq hH hHs nn 0
  rw [Complex.ofReal_zero, Module.End.eigenspace_zero, hk] at hcard
  by_contra hne
  have hpos_j : 0 < secEig T H nn j := lt_of_le_of_ne (secEig_nonneg_dev hH hHs hpos nn j) (Ne.symm hne)
  have hsub : ((Finset.Icc 1 (Module.finrank ℂ (sector T nn))).filter fun i => secEig T H nn i = 0) ⊆
      Finset.Icc 1 (j - 1) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    refine ⟨hi.1.1, ?_⟩
    by_contra h
    push Not at h
    have := secEig_mono T H nn (show j ≤ i by omega)
    linarith [hi.2]
  have := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at this
  omega

/-! ### Proof device for Theorem D.1 (statement phase; not a statement of the paper): the Rayleigh bound

The proof of Theorem D.1: "`expanding in an orthonormal basis of eigenvectors, every unit vector of $\sect\nn$ orthogonal to $\mathcal K_N$ has expectation at least $E_{11}(N)$`".
For `H` self-adjoint, sector-preserving and positive with `dim(ker H ∩ 𝓗^𝐧) = k`, a unit vector of the sector orthogonal
to `ker H ∩ 𝓗^𝐧` has expectation at least `E_{k+1}` (the index clamped as in `secEig`; at `k = dim 𝓗^𝐧` there is no
such vector). -/

theorem rayleigh_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (hpos : H.PosSemidef) (nn : SectorLabel T) {k : ℕ}
    (hk : Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) H) ⊓ sector T nn) = k)
    {v : FockSpace T} (hv : v ∈ sector T nn) (hv1 : ‖v‖ = 1)
    (hvo : v ∈ (LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) H) ⊓ sector T nn)ᗮ) :
    secEig T H nn (k + 1) ≤ (⟪v, toCLM T H v⟫_ℂ).re := by
  classical
  have hA := secCompr_isSymmetric_dev hH hHs nn
  set b := hA.eigenvectorBasis rfl with hb
  set w : sector T nn := ⟨v, hv⟩ with hw
  set c : Fin (Module.finrank ℂ (sector T nn)) → ℂ := fun i => ⟪(b i : FockSpace T), v⟫_ℂ with hc
  have hexp : v = ∑ i, c i • (b i : FockSpace T) := by
    have h := b.sum_repr' w
    have h2 := congrArg Subtype.val h
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul, Submodule.coe_inner, hw] at h2
    exact h2.symm
  have hHv : toCLM T H v = ∑ i, (c i * (secEigDesc T H nn i : ℂ)) • (b i : FockSpace T) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, apply_eigenvector_dev hH hHs nn i, smul_smul]
  have hnorm : ∑ i, ‖c i‖ ^ 2 = 1 := by
    have h := b.sum_sq_norm_inner_right w
    simp only [Submodule.coe_inner, hw] at h
    rw [h]
    show ‖v‖ ^ 2 = 1
    rw [hv1, one_pow]
  have hinner : (⟪v, toCLM T H v⟫_ℂ).re = ∑ i, secEigDesc T H nn i * ‖c i‖ ^ 2 := by
    rw [hHv, inner_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : ⟪v, (b i : FockSpace T)⟫_ℂ = (starRingEnd ℂ) (c i) := (inner_conj_symm _ _).symm
    rw [inner_smul_right, e, mul_comm (c i), mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  have hd0 : ∀ i, secEigDesc T H nn i = 0 → c i = 0 := by
    intro i hi
    have hmem : (b i : FockSpace T) ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) H) ⊓ sector T nn := by
      refine Submodule.mem_inf.2 ⟨?_, (b i).2⟩
      rw [LinearMap.mem_ker, toEuclideanLin_apply_dev, apply_eigenvector_dev hH hHs nn i, hi]
      simp
    exact Submodule.inner_right_of_mem_orthogonal hmem hvo
  have hterm : ∀ i, secEig T H nn (k + 1) * ‖c i‖ ^ 2 ≤ secEigDesc T H nn i * ‖c i‖ ^ 2 := by
    intro i
    by_cases hci : c i = 0
    · simp [hci]
    · have hne : secEigDesc T H nn i ≠ 0 := fun h => hci (hd0 i h)
      have hi2 := i.2
      have hdpos : 0 < Module.finrank ℂ (sector T nn) := by omega
      have heq : secEig T H nn (Module.finrank ℂ (sector T nn) - i.val) = secEigDesc T H nn i := by
        rw [secEig_eq_dev hdpos (by omega) (by omega)]
        congr 1
        ext
        simp only
        omega
      have hgt : k + 1 ≤ Module.finrank ℂ (sector T nn) - i.val := by
        by_contra h
        push Not at h
        exact hne (heq ▸ secEig_zero_of_le_dev hH hHs hpos nn hk (by omega) (by omega))
      have hmono := secEig_mono T H nn hgt
      rw [heq] at hmono
      exact mul_le_mul_of_nonneg_right hmono (by positivity)
  rw [hinner]
  calc secEig T H nn (k + 1) = ∑ i, secEig T H nn (k + 1) * ‖c i‖ ^ 2 := by
        rw [← Finset.mul_sum, hnorm, mul_one]
    _ ≤ ∑ i, secEigDesc T H nn i * ‖c i‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i

/-- **Theorem D.1**: "`Consequently, if $N$ is even, $E_{11}(N)$ is at most the right-hand side of \eqref{eq:twist-bound}`"
— derived from `twist_bound`, `rayleigh_dev` at `k = 10` (`finrank_kernel_half`; the vector is orthogonal to
`ker H_N ∩ 𝓗^{(N/2,N/2)} ⊆ 𝒦_N`, `KN_inf_sector`) and `twistBound_le_twistBoundLy` (written out). -/
theorem E11_le_twistBoundLy (T : Torus) (hN : 2 ≤ T.N) (heven : Even T.N) : E11 T ≤ twistBoundLy T := by
  obtain ⟨v, hv, hv1, hvo, hle⟩ := twist_bound T hN (halfSector T) (Or.inl ⟨heven, rfl⟩)
  have hNs : ((halfSector T).1 : ℕ) + ((halfSector T).2 : ℕ) = T.N := by
    obtain ⟨r, hr⟩ := heven
    show T.N / 2 + T.N / 2 = T.N
    omega
  have hsub : LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ))
      (HN T)) ⊓ sector T (halfSector T) ≤ KN T := by
    rw [← KN_inf_sector T (halfSector T) hNs]
    exact inf_le_left
  exact (rayleigh_dev (HN_isSelfAdjoint T) (HN_isSectorPreserving T) (HN_posSemidef T) (halfSector T)
    (finrank_kernel_half T heven) hv hv1 (Submodule.orthogonal_le hsub hvo)).trans
      (hle.trans (twistBound_le_twistBoundLy T))

/-- **Theorem D.1**: "`and if $N$ is odd, so is $E_3(N)$ in each of the two sectors $((N\pm1)/2,(N\mp1)/2)$.`" —
derived as `E11_le_twistBoundLy`, with `rayleigh_dev` at `k = 2` (`finrank_kernel_odd`; written out). -/
theorem E3_le_twistBoundLy (T : Torus) (hN : 2 ≤ T.N) (hodd : Odd T.N) :
    hcEig T (oddSectorPlus T) 3 ≤ twistBoundLy T ∧ hcEig T (oddSectorMinus T) 3 ≤ twistBoundLy T := by
  have key : ∀ nn : SectorLabel T, (nn = oddSectorPlus T ∨ nn = oddSectorMinus T) →
      ((nn.1 : ℕ) + (nn.2 : ℕ) = T.N) →
      Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T nn) = 2 → hcEig T nn 3 ≤ twistBoundLy T := by
    intro nn hnn hNs hfr
    obtain ⟨v, hv, hv1, hvo, hle⟩ := twist_bound T hN nn (Or.inr ⟨hodd, hnn⟩)
    have hsub : LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ))
        (HN T)) ⊓ sector T nn ≤ KN T := by
      rw [← KN_inf_sector T nn hNs]
      exact inf_le_left
    exact (rayleigh_dev (HN_isSelfAdjoint T) (HN_isSectorPreserving T) (HN_posSemidef T) nn hfr hv hv1
      (Submodule.orthogonal_le hsub hvo)).trans (hle.trans (twistBound_le_twistBoundLy T))
  obtain ⟨m, hm⟩ := hodd
  refine ⟨key _ (Or.inl rfl) ?_ (finrank_kernel_odd T ⟨m, hm⟩).1,
    key _ (Or.inr rfl) ?_ (finrank_kernel_odd T ⟨m, hm⟩).2⟩
  · show (T.N + 1) / 2 + (T.N - 1) / 2 = T.N
    omega
  · show (T.N - 1) / 2 + (T.N + 1) / 2 = T.N
    omega

/-! ### Proof devices for the numbers of Theorem D.1 (proof phase, round one; not statements of the paper)

The four constants, from Mathlib's `Real.pi_gt_d2` (`3.14 < π`) and `Real.exp_one_gt_d9` (`2.7182818283 < e`) — the
statement phase's scratch check, copied. -/

theorem const_one_dev : 1 / Real.sqrt (2 * π) ≤ 0.40 := by
  have hπ := Real.pi_gt_d2
  have h1 : (2.5 : ℝ) ≤ Real.sqrt (2 * π) := by
    rw [show (2.5 : ℝ) = Real.sqrt (2.5 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem const_two_dev : 2 / (Real.exp 1 * Real.sqrt π) ≤ 0.42 := by
  have hπ := Real.pi_gt_d2
  have he := Real.exp_one_gt_d9
  have h1 : (1.77 : ℝ) ≤ Real.sqrt π := by
    rw [show (1.77 : ℝ) = Real.sqrt (1.77 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem const_three_dev : 1 / (4 * π * Real.sqrt (2 * π)) ≤ 0.032 := by
  have hπ := Real.pi_gt_d2
  have h1 : (2.5 : ℝ) ≤ Real.sqrt (2 * π) := by
    rw [show (2.5 : ℝ) = Real.sqrt (2.5 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem const_four_dev : (6 / Real.exp 1) ^ (3 / 2 : ℝ) / 8 ≤ 0.41 := by
  have he := Real.exp_one_gt_d9
  have hx0 : 0 < 6 / Real.exp 1 := by positivity
  have hx : 6 / Real.exp 1 ≤ 2.2072767 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hs : Real.sqrt (6 / Real.exp 1) ≤ 1.4857 := by
    rw [show (1.4857 : ℝ) = Real.sqrt (1.4857 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hr : (6 / Real.exp 1) ^ (3 / 2 : ℝ) = (6 / Real.exp 1) * Real.sqrt (6 / Real.exp 1) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hr]
  have hs0 : 0 ≤ Real.sqrt (6 / Real.exp 1) := Real.sqrt_nonneg _
  nlinarith

/-- **Theorem D.1**, the numbers: "`$1/\sqrt{2\pi}=0.39894\ldots$, $2/(e\sqrt\pi)=0.41510\ldots$, $1/(4\pi\sqrt{2\pi})=0.031746\ldots$ and $(6/e)^{3/2}/8=0.40991\ldots$`"
— the right-hand side of (D.2) is at most the numerical form, on every torus. -/
theorem twistBoundLy_le_twistBoundNum (T : Torus) : twistBoundLy T ≤ twistBoundNum T := by
  have hκ := T.κ_pos
  have hc1 := const_one_dev
  have ha1 := const_two_dev
  have hc2 := const_three_dev
  have ha2 := const_four_dev
  have hLy := T.Ly_pos
  have hN : (0 : ℝ) < T.N := by exact_mod_cast T.N_pos
  unfold twistBoundLy twistBoundNum
  have e1 : 2 * T.κ / (Real.exp 1 * Real.sqrt π) = 2 / (Real.exp 1 * Real.sqrt π) * T.κ := by ring
  have e2 : (6 / Real.exp 1) ^ (3 / 2 : ℝ) * T.κ / 8 = (6 / Real.exp 1) ^ (3 / 2 : ℝ) / 8 * T.κ := by ring
  rw [e1, e2]
  gcongr

/-- **Theorem D.1**: "`In particular both are at most`" "`0.40\,(1+0.42\,\kappa)^2\,\frac{L_y^3}N+0.032\,(1+0.41\,\kappa)^2\,\frac{L_y^5}{N^3}.`"
— `E_{11}` at even `N` (one line from `E11_le_twistBoundLy` and `twistBoundLy_le_twistBoundNum`; written out). -/
theorem E11_le_twistBoundNum (T : Torus) (hN : 2 ≤ T.N) (heven : Even T.N) : E11 T ≤ twistBoundNum T :=
  (E11_le_twistBoundLy T hN heven).trans (twistBoundLy_le_twistBoundNum T)

/-- **Theorem D.1**: "`In particular both are at most`" "`0.40\,(1+0.42\,\kappa)^2\,\frac{L_y^3}N+0.032\,(1+0.41\,\kappa)^2\,\frac{L_y^5}{N^3}.`"
— `E_3` in both odd sectors (one line from `E3_le_twistBoundLy` and `twistBoundLy_le_twistBoundNum`; written out). -/
theorem E3_le_twistBoundNum (T : Torus) (hN : 2 ≤ T.N) (hodd : Odd T.N) :
    hcEig T (oddSectorPlus T) 3 ≤ twistBoundNum T ∧ hcEig T (oddSectorMinus T) 3 ≤ twistBoundNum T :=
  ⟨(E3_le_twistBoundLy T hN hodd).1.trans (twistBoundLy_le_twistBoundNum T),
    (E3_le_twistBoundLy T hN hodd).2.trans (twistBoundLy_le_twistBoundNum T)⟩

/-! ## Corollary D.2: all rectangular tori -/

/-- **Corollary D.2**: "`where the supremum runs over all rectangular tori with $L_xL_y=4\pi N$.`" — every `Torus` with
`T.N = N` (its field `area` is `L_xL_y = 4πN`). -/
def allTori (N : ℕ) : Set Torus :=
  {T | T.N = N}

/-! ### Proof device for Corollary D.2 (statement phase; not a statement of the paper): the constant of its proof

"`$C:=(2\pi)^{-1/2}(L_0+4\sqrt\pi/e)^2L_0+(4\pi\sqrt{2\pi})^{-1}(L_0+\pi(6/e)^{3/2}/4)^2L_0^3$, which depends only on $L_0$.`" —
for `L_y ≤ L`, the right-hand side of (D.2) is at most `C(L)/N` (through `κL_y = 2π`, the two monotone expressions of
the proof, and `N³ ≥ N`). -/

theorem twistBoundLy_le_C_dev (T : Torus) {L : ℝ} (hL : T.Ly ≤ L) :
    twistBoundLy T ≤ ((2 * π) ^ (-(1 / 2 : ℝ)) * (L + 4 * Real.sqrt π / Real.exp 1) ^ 2 * L +
      (4 * π * Real.sqrt (2 * π))⁻¹ * (L + π * (6 / Real.exp 1) ^ (3 / 2 : ℝ) / 4) ^ 2 * L ^ 3) / (T.N : ℝ) := by
  have hLy := T.Ly_pos
  have hκLy := T.κ_mul_Ly
  have hN1 : (1 : ℝ) ≤ T.N := by exact_mod_cast T.N_pos
  have hN : (0 : ℝ) < T.N := by linarith
  have hsq : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have hs2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hrp : (2 * π) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (2 * π) := by
    rw [Real.rpow_neg (by positivity), Real.sqrt_eq_rpow, inv_eq_one_div]
  have hLL : 0 < L := lt_of_lt_of_le hLy hL
  set c1 := 4 * Real.sqrt π / Real.exp 1 with hc1
  set c2 := π * (6 / Real.exp 1) ^ (3 / 2 : ℝ) / 4 with hc2
  have hc1n : 0 ≤ c1 := by positivity
  have hc2n : 0 ≤ c2 := by positivity
  have i1 : (1 + 2 * T.κ / (Real.exp 1 * Real.sqrt π)) * T.Ly = T.Ly + c1 := by
    have h2 : 2 * T.κ / (Real.exp 1 * Real.sqrt π) * T.Ly = c1 := by
      rw [hc1, show 2 * T.κ / (Real.exp 1 * Real.sqrt π) * T.Ly =
        2 * (T.κ * T.Ly) / (Real.exp 1 * Real.sqrt π) by ring, hκLy, div_eq_div_iff (by positivity) (by positivity)]
      linear_combination (-4 * Real.exp 1) * hsq
    rw [add_mul, one_mul, h2]
  have i2 : (1 + (6 / Real.exp 1) ^ (3 / 2 : ℝ) * T.κ / 8) * T.Ly = T.Ly + c2 := by
    have h2 : (6 / Real.exp 1) ^ (3 / 2 : ℝ) * T.κ / 8 * T.Ly = c2 := by
      rw [hc2, show (6 / Real.exp 1) ^ (3 / 2 : ℝ) * T.κ / 8 * T.Ly =
        (6 / Real.exp 1) ^ (3 / 2 : ℝ) * (T.κ * T.Ly) / 8 by ring, hκLy]
      ring
    rw [add_mul, one_mul, h2]
  have e1 : (1 + 2 * T.κ / (Real.exp 1 * Real.sqrt π)) ^ 2 * T.Ly ^ 3 = (T.Ly + c1) ^ 2 * T.Ly := by
    rw [← i1]
    ring
  have e2 : (1 + (6 / Real.exp 1) ^ (3 / 2 : ℝ) * T.κ / 8) ^ 2 * T.Ly ^ 5 = (T.Ly + c2) ^ 2 * T.Ly ^ 3 := by
    rw [← i2]
    ring
  have m1 : (T.Ly + c1) ^ 2 * T.Ly ≤ (L + c1) ^ 2 * L := by gcongr
  have m2 : (T.Ly + c2) ^ 2 * T.Ly ^ 3 ≤ (L + c2) ^ 2 * L ^ 3 := by gcongr
  have hN3 : (T.N : ℝ) ≤ (T.N : ℝ) ^ 3 := by
    have h11 : (1 : ℝ) ≤ (T.N : ℝ) * T.N := by nlinarith
    nlinarith [mul_nonneg hN.le (sub_nonneg.2 h11)]
  unfold twistBoundLy
  have t1 : 1 / Real.sqrt (2 * π) * ((T.Ly + c1) ^ 2 * T.Ly) / T.N ≤
      1 / Real.sqrt (2 * π) * ((L + c1) ^ 2 * L) / T.N :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left m1 (by positivity)) hN.le
  have t2 : 1 / (4 * π * Real.sqrt (2 * π)) * ((T.Ly + c2) ^ 2 * T.Ly ^ 3) / T.N ^ 3 ≤
      1 / (4 * π * Real.sqrt (2 * π)) * ((L + c2) ^ 2 * L ^ 3) / T.N := by
    have hX : 0 ≤ 1 / (4 * π * Real.sqrt (2 * π)) * ((T.Ly + c2) ^ 2 * T.Ly ^ 3) := by positivity
    calc _ ≤ 1 / (4 * π * Real.sqrt (2 * π)) * ((T.Ly + c2) ^ 2 * T.Ly ^ 3) / T.N :=
          div_le_div_of_nonneg_left hX hN hN3
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left m2 (by positivity)) hN.le
  calc 1 / Real.sqrt (2 * π) * (1 + 2 * T.κ / (Real.exp 1 * Real.sqrt π)) ^ 2 * (T.Ly ^ 3 / (T.N : ℝ)) +
        1 / (4 * π * Real.sqrt (2 * π)) * (1 + (6 / Real.exp 1) ^ (3 / 2 : ℝ) * T.κ / 8) ^ 2 *
          (T.Ly ^ 5 / (T.N : ℝ) ^ 3)
      = 1 / Real.sqrt (2 * π) * ((T.Ly + c1) ^ 2 * T.Ly) / T.N +
          1 / (4 * π * Real.sqrt (2 * π)) * ((T.Ly + c2) ^ 2 * T.Ly ^ 3) / T.N ^ 3 := by
        rw [← e1, ← e2]
        ring
    _ ≤ 1 / Real.sqrt (2 * π) * ((L + c1) ^ 2 * L) / T.N +
          1 / (4 * π * Real.sqrt (2 * π)) * ((L + c2) ^ 2 * L ^ 3) / T.N := add_le_add t1 t2
    _ = _ := by
        rw [hrp]
        ring

/-! ### Proof device for Corollary D.2 (proof phase, round one; not a statement of the paper)

Theorem D.1 with the constant `C(L)`: at even `N ≥ 2`, a torus with `L_y ≤ L`, or with `L_x ≤ L` after the exchange of
Lemma 8.3 (`secEig_swap`), has `E_{11} ≤ C(L)/N` (`E11_le_C_dev`). The threshold of `alltori_E11_eventually` departs from
the paper's proof, which takes `N ≥ L₀²/(4π)`: the Lean needs only `N ≥ 2` and `N > C(L₀)/ε`, since
`uniform_E11_eventually_unconditional` covers every torus of `𝒯_N` for `N` large (vacuously where `𝒯_N` is empty) and
`N > C(L₀)/ε` gives the strict inequality on the others. -/

theorem E11_le_C_dev (T : Torus) (hN : 2 ≤ T.N) (heven : Even T.N) {L : ℝ} (hL : T.Ly ≤ L ∨ T.Lx ≤ L) :
    E11 T ≤ ((2 * π) ^ (-(1 / 2 : ℝ)) * (L + 4 * Real.sqrt π / Real.exp 1) ^ 2 * L +
      (4 * π * Real.sqrt (2 * π))⁻¹ * (L + π * (6 / Real.exp 1) ^ (3 / 2 : ℝ) / 4) ^ 2 * L ^ 3) / (T.N : ℝ) := by
  rcases hL with hy | hx
  · exact (E11_le_twistBoundLy T hN heven).trans (twistBoundLy_le_C_dev T hy)
  · have hsw : E11 (swapTorus T) = E11 T := secEig_swap T (halfSector T) 11
    rw [← hsw]
    exact (E11_le_twistBoundLy (swapTorus T) hN heven).trans (twistBoundLy_le_C_dev (swapTorus T) hx)

/-- **Corollary D.2** without the supremum: "`For even $N$ and a rectangular torus $\Tor$ with $L_xL_y=4\pi N$, let $E_{11}(N;\Tor)$ be the eleventh eigenvalue of the hollow-core Hamiltonian of $\Tor$ in the sector $(N/2,N/2)$. Then $\sup_\Tor E_{11}(N;\Tor)\to0$ as $N\to\infty$ through the even integers, where the supremum runs over all rectangular tori with $L_xL_y=4\pi N$.`"
— for every `ε > 0`, for all large even `N`, every rectangular torus with `L_xL_y = 4πN` has `E_{11}(N; 𝕋) < ε` (the form of
`uniform_E11_eventually_unconditional`, with `allTori N` in place of `tauSet N`). -/
theorem alltori_E11_eventually :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop ⊓ 𝓟 {N : ℕ | Even N}, ∀ T ∈ allTori N, E11 T < ε := by
  intro ε hε
  set C := (2 * π) ^ (-(1 / 2 : ℝ)) * (L0std + 4 * Real.sqrt π / Real.exp 1) ^ 2 * L0std +
      (4 * π * Real.sqrt (2 * π))⁻¹ * (L0std + π * (6 / Real.exp 1) ^ (3 / 2 : ℝ) / 4) ^ 2 * L0std ^ 3 with hC
  have hth : ∀ᶠ (N : ℕ) in atTop ⊓ 𝓟 {N : ℕ | Even N}, 2 ≤ N ∧ C / ε < (N : ℝ) := by
    apply Filter.Eventually.filter_mono inf_le_left
    filter_upwards [Filter.eventually_ge_atTop 2, Filter.eventually_gt_atTop ⌈C / ε⌉₊] with N h2 hC2
    exact ⟨h2, (Nat.le_ceil _).trans_lt (by exact_mod_cast hC2)⟩
  have hevenF : ∀ᶠ N in atTop ⊓ 𝓟 {N : ℕ | Even N}, Even N :=
    Filter.mem_inf_of_right (Filter.mem_principal_self _)
  filter_upwards [uniform_E11_eventually_unconditional ε hε, hth, hevenF] with N hN hth2 heven
  intro T hT
  have hTN : T.N = N := hT
  by_cases hmin : L0std ≤ min T.Lx T.Ly
  · exact hN T ⟨hTN, hmin⟩
  · push Not at hmin
    have hL : T.Ly ≤ L0std ∨ T.Lx ≤ L0std := by
      rcases min_lt_iff.1 hmin with h | h
      · exact Or.inr h.le
      · exact Or.inl h.le
    have h1 := E11_le_C_dev T (hTN ▸ hth2.1) (hTN ▸ heven) hL
    rw [hTN] at h1
    have hNpos : (0 : ℝ) < N := by have := hth2.1; positivity
    have h2 : C < ε * N := by
      have := hth2.2
      rw [div_lt_iff₀ hε] at this
      linarith
    calc E11 T ≤ C / N := h1
      _ < ε := by rw [div_lt_iff₀ hNpos]; linarith

/-- **Corollary D.2**: "`Then $\sup_\Tor E_{11}(N;\Tor)\to0$ as $N\to\infty$ through the even integers, where the supremum runs over all rectangular tori with $L_xL_y=4\pi N$.`"
— the supremum is a real supremum: `E_{11}` is bounded above on the family at every even `N` (by `‖H_N‖` on the tori of
`𝒯_N`, by Theorem D.1 on the others after the exchange of Lemma 8.3). -/
theorem E11_bddAbove_allTori {N : ℕ} (hN : Even N) : BddAbove (E11 '' allTori N) := by
  set C := (2 * π) ^ (-(1 / 2 : ℝ)) * (L0std + 4 * Real.sqrt π / Real.exp 1) ^ 2 * L0std +
      (4 * π * Real.sqrt (2 * π))⁻¹ * (L0std + π * (6 / Real.exp 1) ^ (3 / 2 : ℝ) / 4) ^ 2 * L0std ^ 3 with hC
  refine ⟨max (ChHC * (4 * π * N)) (C / N), ?_⟩
  rintro _ ⟨T, hT, rfl⟩
  have hTN : T.N = N := hT
  by_cases hmin : L0std ≤ min T.Lx T.Ly
  · have hL : 4 ≤ min T.Lx T.Ly := le_trans (le_max_left 4 _) hmin
    have h1 := secEig_le_norm_dev (HN_isSelfAdjoint T) (HN_isSectorPreserving T) (halfSector T) 11
    have h2 := norm_HN_le_dev T hL
    rw [hTN] at h2
    exact (h1.trans h2).trans (le_max_left _ _)
  · push Not at hmin
    have hL : T.Ly ≤ L0std ∨ T.Lx ≤ L0std := by
      rcases min_lt_iff.1 hmin with h | h
      · exact Or.inr h.le
      · exact Or.inl h.le
    have h2N : 2 ≤ T.N := by
      obtain ⟨r, hr⟩ := hN
      have := T.N_pos
      omega
    have h1 := E11_le_C_dev T h2N (hTN ▸ hN) hL
    rw [hTN] at h1
    exact h1.trans (le_max_right _ _)

/-- **Corollary D.2**: "`Then $\sup_\Tor E_{11}(N;\Tor)\to0$ as $N\to\infty$ through the even integers, where the supremum runs over all rectangular tori with $L_xL_y=4\pi N$.`"
— the form of `uniform_E11_tendsto_unconditional`, with `allTori N` in place of `tauSet N` (the supremum is the real
supremum at even `N`: `E11_bddAbove_allTori`). -/
theorem alltori_E11_tendsto :
    Tendsto (fun N => sSup (E11 '' allTori N)) (atTop ⊓ 𝓟 {N : ℕ | Even N}) (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Filter.Eventually.of_forall fun N => lt_of_lt_of_le ha ?_, fun a ha => ?_⟩
  · refine Real.sSup_nonneg fun x hx => ?_
    obtain ⟨T, -, rfl⟩ := hx
    exact secEig_HN_nonneg T (halfSector T) 11
  · filter_upwards [alltori_E11_eventually (a / 2) (by linarith)] with N hN
    have h : sSup (E11 '' allTori N) ≤ a / 2 := by
      refine Real.sSup_le (fun x hx => ?_) (by linarith)
      obtain ⟨T, hT, rfl⟩ := hx
      exact (hN T hT).le
    linarith

end HRTorus.ZeroModes

end -- noncomputable section
