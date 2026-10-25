import HRTorus.Hamiltonian.Pairs
import HRTorus.Fock.Hamiltonian

/-!
# The exact local form of the hollow-core Hamiltonian (T-0056 block C, `Hamiltonian.LocalForm`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **The definitions and statements were written first and
reviewed against the paper before any proof (review L9a, accepted with no change); the proof phase proved every
theorem of this module — there is no `sorry` here, and nothing here depends on an open statement. Theorem 4.2(a)
(`localForm_a`) is proved by the paper's route through two devices: the Fock-space reduction
`localForm_a_of_pairFormIdentity` (the matrix entries of both sides as sums of a form on antisymmetric pair amplitudes,
and polarization, in place of the paper's Step 6) and the scalar identity `PairForm.pairFormIdentity` (Steps 1–5, with
Lemma 4.3). Theorem 4.2(c) (`localForm_c`), `HD_univ`, `commute_Θ_HN` and block A's `HRTorus.Fock.HN_posSemidef`
(moved here) are proved from (a); Theorem 4.2(b) (`localForm_b`) and the device `opIntegral_hR_eq_bcen` (the
computation of (c) from (b): `∫_{𝕋_N} h_R dR = (κ³/√(2π)) Σ_n Σ_ν b_ν(n)^* b_ν(n)`) without it. The proof devices are
in sections (or docstrings) marked as such.**
The paper: the HR paper, `papers/hr/sections/04-hamiltonian.tex` — Theorem 4.2 `thm:localform` (a)–(c) and the last
clause of Lemma 4.5 `lem:covariance`; and from `papers/hr/sections/02-setting.tex`, §2.4, the paragraph after
Definition 2.7 (`H_N ≥ 0`, which the paper derives from Theorem 4.2(a)).

## The model

* `H_N` is block A's `HN` (Definition 2.7, the coefficients `V_abcd` by the integrals (2.6)); `B_ν`, `h_R`, `b_ν(n)` and
  the entrywise operator integral `opIntegral` are `HRTorus.Hamiltonian.Pairs`'s.
* `∫_{𝕋_N}` is the integral over block A's fundamental domain `[0, L_x) × [0, L_y)`.
* Theorem 4.2(b) is a `HasSum` over `n ∈ ℤ` (the series and its value at once), in the topology of the operators.
* Theorem 4.2(c)'s sum over `n ∈ ℤ_{2N_φ}` is the sum over the representatives `n ∈ {0, …, 2N_φ − 1}` (by
  `bcen_add_two_Nφ` any set of representatives gives the same sum).
* `H_N ≥ 0` is block A's `HRTorus.Fock.HN_posSemidef`, moved here by ruling 1 of review L9a with its docstring and header
  verbatim (its name and namespace unchanged; the paper derives it from Theorem 4.2(a), which `Fock.Hamiltonian` cannot
  import). `commute_Θ_HN` is Lemma 4.5's route to `[Θ, H_N] = 0`; block A's `HN_commute_Θ` is the same statement, proved
  by another route (the shift of the coefficients).
-/

open MeasureTheory
open scoped InnerProductSpace Matrix Real ComplexOrder
open Complex (I)

noncomputable section

namespace HRTorus.Hamiltonian

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op IsEven)

/-! ### Proof devices for Theorem 4.2(b) (phase (b); not statements of the paper) -/

/-- Device: `φ_j(R) (Dφ_{n−j})(R)` in closed form, the proof of Theorem 4.2(b):
"`Completing the square, $(R_x-\kappa j_1)^2+(R_x-\kappa j_2)^2=2(R_x-\kappa n/2)^2+\kappa^2d^2/2$`", and
"`$-(R_x-\kappa j_2)=\frac{\kappa d}2-(R_x-\frac{\kappa n}2)$`". -/
theorem phi_mul_Dphi (T : Torus) (n j : ℤ) (R : ℝ × ℝ) :
    phi T j R * Dphi T (n - j) R =
      ((1 / (T.Ly * Real.sqrt π) * Real.exp (-(R.1 - T.κ * (n : ℝ) / 2) ^ 2) : ℝ) : ℂ) *
        Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (R.2 : ℂ)) *
        ((((T.κ / 2) * ((n - 2 * j : ℤ) : ℝ) - (R.1 - T.κ * (n : ℝ) / 2)) *
          Real.exp (-(T.κ ^ 2 * ((n - 2 * j : ℤ) : ℝ) ^ 2) / 4) : ℝ) : ℂ) := by
  have hc := c0_sq_eq T
  have hexp : Complex.exp (((T.κ * j * R.2 : ℝ) : ℂ) * I) *
      Complex.exp (((T.κ * ((n - j : ℤ) : ℝ) * R.2 : ℝ) : ℂ) * I) =
      Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (R.2 : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hreal : Real.exp (-((R.1 - T.κ * j) ^ 2) / 2) * Real.exp (-((R.1 - T.κ * ((n - j : ℤ) : ℝ)) ^ 2) / 2) =
      Real.exp (-(R.1 - T.κ * (n : ℝ) / 2) ^ 2) * Real.exp (-(T.κ ^ 2 * ((n - 2 * j : ℤ) : ℝ) ^ 2) / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [Dphi, phi_eq, phi_eq]
  calc _ = ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))) ^ 2 * (Real.exp (-((R.1 - T.κ * j) ^ 2) / 2) *
          Real.exp (-((R.1 - T.κ * ((n - j : ℤ) : ℝ)) ^ 2) / 2)) * (-(R.1 - T.κ * ((n - j : ℤ) : ℝ))) : ℝ) : ℂ) *
        (Complex.exp (((T.κ * j * R.2 : ℝ) : ℂ) * I) *
          Complex.exp (((T.κ * ((n - j : ℤ) : ℝ) * R.2 : ℝ) : ℂ) * I)) := by
        push_cast
        ring
    _ = _ := by
        rw [hreal, hexp, hc]
        push_cast
        ring

theorem summable_norm_phi (T : Torus) (R : ℝ × ℝ) : Summable (fun j : ℤ => ‖phi T j R‖) := by
  refine ((Analysis.summable_gauss_int T.κ_pos R.1).mul_left
    ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)))).congr fun j => ?_
  rw [norm_phi, mul_comm T.κ]

theorem summable_norm_Dphi (T : Torus) (R : ℝ × ℝ) : Summable (fun j : ℤ => ‖Dphi T j R‖) := by
  have hc : 0 ≤ (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (mul_nonneg T.Ly_pos.le (Real.sqrt_nonneg _)) _
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    ((Analysis.summable_gauss_int (L := T.κ / 2) (by linarith [T.κ_pos]) (R.1 / 2)).mul_left
      ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))))
  rw [Dphi, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, norm_phi]
  have h1 := abs_le_exp_sq_div_four (R.1 - T.κ * j)
  calc |R.1 - T.κ * j| * ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-((R.1 - T.κ * j) ^ 2) / 2))
      ≤ Real.exp ((R.1 - T.κ * j) ^ 2 / 4) *
        ((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-((R.1 - T.κ * j) ^ 2) / 2)) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hc (Real.exp_pos _).le)
    _ = (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) *
        Real.exp ((R.1 - T.κ * j) ^ 2 / 4 + -((R.1 - T.κ * j) ^ 2) / 2) := by
        rw [Real.exp_add]; ring
    _ ≤ (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-((R.1 / 2 - j * (T.κ / 2)) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (R.1 - T.κ * j)])) hc

/-- Device: `e^{−κ²D²/4}`. -/
def gE (T : Torus) (D : ℤ) : ℝ := Real.exp (-(T.κ ^ 2 * (D : ℝ) ^ 2) / 4)

theorem summable_gE (T : Torus) : Summable (gE T) := by
  refine Summable.of_nonneg_of_le (fun D => (Real.exp_pos _).le) (fun D => ?_)
    (Analysis.summable_gauss_int (L := T.κ / 2) (by linarith [T.κ_pos]) 0)
  unfold gE
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (T.κ * D)]

theorem summable_abs_gE (T : Torus) : Summable (fun D : ℤ => |(D : ℝ)| * gE T D) := by
  have hκ := T.κ_pos
  refine Summable.of_nonneg_of_le (fun D => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (fun D => ?_)
    ((Analysis.summable_gauss_int (L := T.κ / 2) (by linarith) 0).mul_left (2 / T.κ))
  have h1 := abs_le_exp_sq_div_four (T.κ * D / 2)
  rw [abs_div, abs_mul, abs_of_pos hκ, abs_two] at h1
  have h2 : |(D : ℝ)| ≤ 2 / T.κ * Real.exp ((T.κ * D / 2) ^ 2 / 4) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
    linarith
  unfold gE
  calc |(D : ℝ)| * Real.exp (-(T.κ ^ 2 * (D : ℝ) ^ 2) / 4)
      ≤ 2 / T.κ * Real.exp ((T.κ * D / 2) ^ 2 / 4) * Real.exp (-(T.κ ^ 2 * (D : ℝ) ^ 2) / 4) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 2 / T.κ * Real.exp ((T.κ * D / 2) ^ 2 / 4 + -(T.κ ^ 2 * (D : ℝ) ^ 2) / 4) := by
        rw [Real.exp_add]; ring
    _ ≤ 2 / T.κ * Real.exp (-((0 - D * (T.κ / 2)) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (T.κ * D)]))
          (div_pos two_pos hκ).le

/-- Device: the summand of the orbital double series of `B_ν(R)`, entrywise. -/
def bQ (T : Torus) (R : ℝ × ℝ) (y : ZMod T.Nφ → ZMod T.Nφ → ℂ) (p : ℤ × ℤ) : ℂ :=
  phi T p.1 R * Dphi T p.2 R * y (p.1 : ZMod T.Nφ) (p.2 : ZMod T.Nφ)

/-- Device: the relabelling `(n, j₁) ↦ (j₁, n − j₁)` (fibres `j₁ + j₂ = n`). -/
def fiberEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, p.1 - p.2)
  invFun q := (q.1 + q.2, q.1)
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

/-- Device: the `κd/2`-part of the fibre `n`. -/
def fA (T : Torus) (y : ZMod T.Nφ → ZMod T.Nφ → ℂ) (n j : ℤ) : ℂ :=
  ((n - 2 * j : ℤ) : ℂ) * (gE T (n - 2 * j) : ℂ) * y (j : ZMod T.Nφ) ((n - j : ℤ) : ZMod T.Nφ)

/-- Device: the `(R_x − κn/2)`-part of the fibre `n`. -/
def fB (T : Torus) (y : ZMod T.Nφ → ZMod T.Nφ → ℂ) (n j : ℤ) : ℂ :=
  (gE T (n - 2 * j) : ℂ) * y (j : ZMod T.Nφ) ((n - j : ℤ) : ZMod T.Nφ)

/-- Device: the fibre `n` indexed by `D = j₂ − j₁ = n − 2j₁` (zero off the parity class of `n`). -/
def fK (T : Torus) (y : ZMod T.Nφ → ZMod T.Nφ → ℂ) (n D : ℤ) : ℂ :=
  if D ≡ n [ZMOD 2] then (D : ℂ) * (gE T D : ℂ) * y (((n - D) / 2 : ℤ) : ZMod T.Nφ) (((n + D) / 2 : ℤ) : ZMod T.Nφ)
  else 0

theorem fK_neg (T : Torus) (y : ZMod T.Nφ → ZMod T.Nφ → ℂ) (hy : ∀ j j', y j' j = -y j j') (n D : ℤ) :
    fK T y n (-D) = fK T y n D := by
  unfold fK
  have hpar : ((-D) ≡ n [ZMOD 2]) ↔ (D ≡ n [ZMOD 2]) := by simp only [Int.ModEq, Int.neg_emod_two]
  have hg : gE T (-D) = gE T D := by simp [gE]
  by_cases h : D ≡ n [ZMOD 2]
  · rw [ite_eq_left (hpar.mpr h), ite_eq_left h, hg, sub_neg_eq_add, ← sub_eq_add_neg, hy]
    push_cast
    ring
  · rw [ite_eq_right (mt hpar.mp h), ite_eq_right h]

theorem fK_comp (T : Torus) (y : ZMod T.Nφ → ZMod T.Nφ → ℂ) (n j : ℤ) : fK T y n (n - 2 * j) = fA T y n j := by
  unfold fK fA
  have hpar : (n - 2 * j) ≡ n [ZMOD 2] := by simp only [Int.ModEq]; omega
  rw [ite_eq_left hpar, show (n - (n - 2 * j)) / 2 = j by omega, show (n + (n - 2 * j)) / 2 = n - j by omega]

theorem fB_swap (T : Torus) (y : ZMod T.Nφ → ZMod T.Nφ → ℂ) (hy : ∀ j j', y j' j = -y j j') (n j : ℤ) :
    fB T y n (n - j) = -fB T y n j := by
  unfold fB
  have hg : gE T (n - 2 * (n - j)) = gE T (n - 2 * j) := by
    unfold gE; congr 2; push_cast; ring
  rw [hg, show n - (n - j) = j by ring, hy]
  ring

/-- Device: the entrywise form of Theorem 4.2(b): for antisymmetric coefficients `y`, the orbital double series
`Σ_{j,j'} ψ_j(R)(Dψ_{j'})(R) y_{jj'}` regrouped by `n = j₁ + j₂` (the proof of Theorem 4.2(b)). -/
theorem localForm_b_scalar (T : Torus) (R : ℝ × ℝ) (y : ZMod T.Nφ → ZMod T.Nφ → ℂ)
    (hy : ∀ j j', y j' j = -y j j') :
    HasSum (fun n : ℤ => (((T.κ / (2 * T.Ly * Real.sqrt π) : ℝ) : ℂ) *
        (Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (R.2 : ℂ)) *
          ((Real.exp (-(R.1 - T.κ * (n : ℝ) / 2) ^ 2) : ℝ) : ℂ))) *
        ∑' d : ℕ, (if (d : ℤ) ≡ n [ZMOD 2] then
          ((2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) : ℝ) : ℂ) *
            y (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) else 0))
      (∑ j, ∑ j', (psi T j R * Dcov (psi T j') R) * y j j') := by
  -- the bound on the coefficients
  have hCy0 : 0 ≤ ∑ j, ∑ j', ‖y j j'‖ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hy_le : ∀ j j', ‖y j j'‖ ≤ ∑ j, ∑ j', ‖y j j'‖ := fun j j' => by
    calc ‖y j j'‖ ≤ ∑ j'', ‖y j j''‖ := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j')
      _ ≤ ∑ j, ∑ j', ‖y j j'‖ := Finset.single_le_sum (f := fun j => ∑ j'', ‖y j j''‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have hcast : ∀ (j : ZMod T.Nφ) (m : ℤ), ((((j.val : ℤ) + m * (T.Nφ : ℤ)) : ℤ) : ZMod T.Nφ) = j := fun j m => by
    simp
  have hφ := summable_norm_phi T R
  have hDφ := summable_norm_Dphi T R
  -- the double series over `ℤ²`
  have hQ : Summable (bQ T R y) := by
    refine Summable.of_norm_bounded ((hφ.mul_of_nonneg hDφ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left
      (∑ j, ∑ j', ‖y j j'‖)) fun p => ?_
    simp only [bQ, norm_mul]
    calc ‖phi T p.1 R‖ * ‖Dphi T p.2 R‖ * ‖y (p.1 : ZMod T.Nφ) (p.2 : ZMod T.Nφ)‖
        ≤ ‖phi T p.1 R‖ * ‖Dphi T p.2 R‖ * ∑ j, ∑ j', ‖y j j'‖ :=
          mul_le_mul_of_nonneg_left (hy_le _ _) (by positivity)
      _ = (∑ j, ∑ j', ‖y j j'‖) * (‖phi T p.1 R‖ * ‖Dphi T p.2 R‖) := by ring
  -- unfolding the orbitals (`ψ_j = Σ_m φ_{j̃+mN_φ}`)
  have hin : ∀ j : ZMod T.Nφ, ∑ j', Dcov (psi T j') R * y j j' =
      ∑' j2 : ℤ, Dphi T j2 R * y j (j2 : ZMod T.Nφ) := by
    intro j
    have hF : Summable (fun j2 : ℤ => Dphi T j2 R * y j (j2 : ZMod T.Nφ)) := by
      refine Summable.of_norm_bounded (hDφ.mul_right (∑ j, ∑ j', ‖y j j'‖)) fun j2 => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hy_le _ _) (norm_nonneg _)
    rw [← sum_zmod_tsum (N := T.Nφ) _ hF]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Dcov_psi_val, ← tsum_mul_right]
    exact tsum_congr fun m => by rw [hcast]
  have hout : ∀ G : ZMod T.Nφ → ℂ, ∑ j, psi T j R * G j = ∑' j1 : ℤ, phi T j1 R * G (j1 : ZMod T.Nφ) := by
    intro G
    have hG_le : ∀ j, ‖G j‖ ≤ ∑ j, ‖G j‖ := fun j =>
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    have hF : Summable (fun j1 : ℤ => phi T j1 R * G (j1 : ZMod T.Nφ)) := by
      refine Summable.of_norm_bounded (hφ.mul_right (∑ j, ‖G j‖)) fun j1 => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hG_le _) (norm_nonneg _)
    rw [← sum_zmod_tsum (N := T.Nφ) _ hF]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [psi, ← tsum_mul_right]
    exact tsum_congr fun m => by rw [hcast]
  have hK1 : ∑ j, ∑ j', (psi T j R * Dcov (psi T j') R) * y j j' = ∑' p : ℤ × ℤ, bQ T R y p := by
    have e1 : ∀ j, ∑ j', (psi T j R * Dcov (psi T j') R) * y j j' =
        psi T j R * ∑' j2 : ℤ, Dphi T j2 R * y j (j2 : ZMod T.Nφ) := by
      intro j
      rw [← hin j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j' _ => by ring
    simp only [e1]
    rw [hout (fun j => ∑' j2 : ℤ, Dphi T j2 R * y j (j2 : ZMod T.Nφ)), hQ.tsum_prod]
    refine tsum_congr fun j1 => ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun j2 => by simp only [bQ]; ring
  -- the fibres `j₁ + j₂ = n`
  have hQe : Summable (fun p => bQ T R y (fiberEquiv p)) := fiberEquiv.summable_iff.mpr hQ
  have hfib : HasSum (fun n : ℤ => ∑' j1 : ℤ, bQ T R y (fiberEquiv (n, j1))) (∑' p, bQ T R y p) := by
    have h := hQe.hasSum.prod_fiberwise (fun n => (hQe.prod_factor n).hasSum)
    rwa [fiberEquiv.tsum_eq (bQ T R y)] at h
  rw [hK1]
  convert hfib using 1
  funext n
  -- the fibre `n`
  have hsK : Summable (fK T y n) := by
    refine Summable.of_norm_bounded ((summable_abs_gE T).mul_left (∑ j, ∑ j', ‖y j j'‖)) fun D => ?_
    unfold fK
    split_ifs
    · rw [norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < gE T D from Real.exp_pos _)]
      calc |(D : ℝ)| * gE T D * ‖y _ _‖ ≤ |(D : ℝ)| * gE T D * ∑ j, ∑ j', ‖y j j'‖ :=
            mul_le_mul_of_nonneg_left (hy_le _ _) (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
        _ = (∑ j, ∑ j', ‖y j j'‖) * (|(D : ℝ)| * gE T D) := by ring
    · rw [norm_zero]
      exact mul_nonneg hCy0 (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  have hg_inj : Function.Injective (fun j : ℤ => n - 2 * j) := fun a b h => by
    simp only at h
    omega
  have hsA : Summable (fA T y n) := (hsK.comp_injective hg_inj).congr (fK_comp T y n)
  have hsB : Summable (fB T y n) := by
    refine Summable.of_norm_bounded (((summable_gE T).comp_injective hg_inj).mul_left
      (∑ j, ∑ j', ‖y j j'‖)) fun j => ?_
    simp only [fB, norm_mul, Complex.norm_real, Real.norm_eq_abs, Function.comp]
    rw [abs_of_pos (show (0 : ℝ) < gE T (n - 2 * j) from Real.exp_pos _)]
    calc gE T (n - 2 * j) * ‖y _ _‖ ≤ gE T (n - 2 * j) * ∑ j, ∑ j', ‖y j j'‖ :=
          mul_le_mul_of_nonneg_left (hy_le _ _) (Real.exp_pos _).le
      _ = (∑ j, ∑ j', ‖y j j'‖) * gE T (n - 2 * j) := by ring
  -- the `(R_x − κn/2)`-part vanishes (the exchange `j₁ ↔ j₂`)
  have hB0 : ∑' j1 : ℤ, fB T y n j1 = 0 := by
    have hrefl : ∑' j1 : ℤ, fB T y n j1 = ∑' j1 : ℤ, fB T y n (n - j1) :=
      ((Equiv.subLeft n).tsum_eq (fB T y n)).symm
    rw [tsum_congr (fB_swap T y hy n), tsum_neg] at hrefl
    exact CharZero.eq_neg_self_iff.mp hrefl
  -- the `κd/2`-part is `b_ν(n)`
  have hA : ∑' j1 : ℤ, fA T y n j1 =
      ∑' d : ℕ, (if (d : ℤ) ≡ n [ZMOD 2] then
        ((2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) : ℝ) : ℂ) *
          y (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) else 0) := by
    have hsupp : Function.support (fK T y n) ⊆ Set.range (fun j : ℤ => n - 2 * j) := by
      intro D hD
      have h : D ≡ n [ZMOD 2] := by
        by_contra h
        exact hD (by simp [fK, h])
      refine ⟨(n - D) / 2, ?_⟩
      simp only [Int.ModEq] at h
      show n - 2 * ((n - D) / 2) = D
      omega
    have e1 : ∑' j1 : ℤ, fA T y n j1 = ∑' D : ℤ, fK T y n D := by
      rw [← hg_inj.tsum_eq hsupp]
      exact tsum_congr fun j => (fK_comp T y n j).symm
    have hs1 : Summable (fun d : ℕ => fK T y n d) := hsK.comp_injective Nat.cast_injective
    have hs2 : Summable (fun d : ℕ => fK T y n (-((d : ℤ) + 1))) :=
      hsK.comp_injective fun a b h => by simpa using h
    have e2 : ∀ d : ℕ, fK T y n (-((d : ℤ) + 1)) = fK T y n ((d + 1 : ℕ) : ℤ) := by
      intro d
      rw [fK_neg T y hy]
      push_cast
      rfl
    have h0 : fK T y n ((0 : ℕ) : ℤ) = 0 := by simp [fK]
    have hz := hs1.tsum_eq_zero_add
    rw [h0, zero_add] at hz
    have ht : ∀ d : ℕ, (if (d : ℤ) ≡ n [ZMOD 2] then
        ((2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) : ℝ) : ℂ) *
          y (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ) else 0) =
        2 * fK T y n d := by
      intro d
      unfold fK gE
      split_ifs <;> push_cast <;> ring
    rw [e1, tsum_of_nat_of_neg_add_one hs1 hs2, tsum_congr e2, ← hz, ← two_mul, ← tsum_mul_left]
    exact tsum_congr fun d => (ht d).symm
  -- the closed form of the fibre
  have h1 : ∀ j1 : ℤ, bQ T R y (fiberEquiv (n, j1)) =
      ((1 / (T.Ly * Real.sqrt π) * Real.exp (-(R.1 - T.κ * (n : ℝ) / 2) ^ 2) : ℝ) : ℂ) *
        Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (R.2 : ℂ)) *
        (((T.κ / 2 : ℝ) : ℂ) * fA T y n j1 - ((R.1 - T.κ * (n : ℝ) / 2 : ℝ) : ℂ) * fB T y n j1) := by
    intro j1
    show phi T j1 R * Dphi T (n - j1) R * y (j1 : ZMod T.Nφ) ((n - j1 : ℤ) : ZMod T.Nφ) = _
    rw [phi_mul_Dphi]
    simp only [fA, fB, gE]
    push_cast
    ring
  rw [tsum_congr h1, tsum_mul_left, Summable.tsum_sub (hsA.mul_left _) (hsB.mul_left _), tsum_mul_left,
    tsum_mul_left, hB0, hA]
  push_cast
  ring

/-! ### Proof devices for Theorem 4.2(c) (phase (b); not statements of the paper) -/

/-- Device: the Gaussian coefficient of Theorem 4.2(b), `(κ/(2L_y√π)) e^{iκnR_y} e^{−(R_x−κn/2)²}`. -/
def Wb (T : Torus) (R : ℝ × ℝ) (n : ℤ) : ℂ :=
  ((T.κ / (2 * T.Ly * Real.sqrt π) : ℝ) : ℂ) *
    (Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (R.2 : ℂ)) * ((Real.exp (-(R.1 - T.κ * (n : ℝ) / 2) ^ 2) : ℝ) : ℂ))

theorem cW_pos (T : Torus) : 0 < T.κ / (2 * T.Ly * Real.sqrt π) :=
  div_pos T.κ_pos (mul_pos (mul_pos two_pos T.Ly_pos) (Real.sqrt_pos.mpr Real.pi_pos))

theorem norm_Wb (T : Torus) (R : ℝ × ℝ) (n : ℤ) :
    ‖Wb T R n‖ = T.κ / (2 * T.Ly * Real.sqrt π) * Real.exp (-(R.1 - T.κ * (n : ℝ) / 2) ^ 2) := by
  have hph : ‖Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (R.2 : ℂ))‖ = 1 := by
    rw [show I * (T.κ : ℂ) * (n : ℂ) * (R.2 : ℂ) = ((T.κ * n * R.2 : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [Wb, norm_mul, norm_mul, hph, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (cW_pos T)]

theorem continuous_Wb (T : Torus) (n : ℤ) : Continuous fun R : ℝ × ℝ => Wb T R n := by
  unfold Wb
  fun_prop

theorem norm_Wb_le (T : Torus) (R : ℝ × ℝ) (n : ℤ) :
    ‖Wb T R n‖ ≤ T.κ / (2 * T.Ly * Real.sqrt π) * Real.exp (-((R.1 - n * (T.κ / 2)) ^ 2) / 2) := by
  rw [norm_Wb]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (cW_pos T).le
  nlinarith [sq_nonneg (R.1 - T.κ * (n : ℝ) / 2)]

theorem norm_Wb_le_fd (T : Torus) (R : ℝ × ℝ) (hR : R ∈ fundDom T) (n : ℤ) :
    ‖Wb T R n‖ ≤ T.κ / (2 * T.Ly * Real.sqrt π) *
      (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - n * (T.κ / 4)) ^ 2) / 2)) := by
  rw [norm_Wb]
  refine mul_le_mul_of_nonneg_left ?_ (cW_pos T).le
  have h := gauss_strip_bound (T.κ * (n : ℝ) / 2) R.1 T.Lx hR.1.1 hR.1.2.le
  have e : Real.exp (-((0 - n * (T.κ / 4)) ^ 2) / 2) = Real.exp (-((T.κ * (n : ℝ) / 2) ^ 2 / 4) / 2) := by
    congr 1; ring
  rw [e]
  refine le_trans (Real.exp_le_exp.mpr ?_) h
  nlinarith [sq_nonneg (R.1 - T.κ * (n : ℝ) / 2)]

theorem summable_Wb_bound (T : Torus) :
    Summable (fun n : ℤ => T.κ / (2 * T.Ly * Real.sqrt π) *
      (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - n * (T.κ / 4)) ^ 2) / 2))) :=
  ((Analysis.summable_gauss_int (L := T.κ / 4) (by linarith [T.κ_pos]) 0).mul_left _).mul_left _

theorem star_Wb_mul_Wb (T : Torus) (n n' : ℤ) (x y : ℝ) :
    star (Wb T (x, y) n) * Wb T (x, y) n' =
      (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) *
        Real.exp (-(x - T.κ * (n' : ℝ) / 2) ^ 2) : ℝ) : ℂ) *
      Complex.exp ((I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ)) := by
  have hs : ∀ r : ℝ, star (r : ℂ) = r := fun r => Complex.conj_ofReal r
  have hse : ∀ z : ℂ, star (Complex.exp z) = Complex.exp (star z) := fun z => (Complex.exp_conj z).symm
  have hsI : star I = -I := Complex.conj_I
  simp only [Wb, star_mul', hs, hse, hsI, star_intCast]
  rw [show (I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ) =
      -I * (T.κ : ℂ) * (n : ℂ) * (y : ℂ) + I * (T.κ : ℂ) * (n' : ℂ) * (y : ℂ) by push_cast; ring,
    Complex.exp_add]
  push_cast
  ring

theorem integral_star_Wb_mul_Wb (T : Torus) (n n' : ℤ) :
    ∫ r in fundDom T, star (Wb T r n) * Wb T r n' =
      (∫ x in Set.Ico 0 T.Lx, (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) *
        Real.exp (-(x - T.κ * (n' : ℝ) / 2) ^ 2) : ℝ) : ℂ)) * (if n' - n = 0 then (T.Ly : ℂ) else 0) := by
  have e : (fun r : ℝ × ℝ => star (Wb T r n) * Wb T r n') = fun r =>
      (fun x : ℝ => (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) *
        Real.exp (-(x - T.κ * (n' : ℝ) / 2) ^ 2) : ℝ) : ℂ)) r.1 *
      (fun y : ℝ => Complex.exp ((I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ))) r.2 :=
    funext fun r => star_Wb_mul_Wb T n n' r.1 r.2
  calc ∫ r in fundDom T, star (Wb T r n) * Wb T r n'
      = ∫ r in Set.Ico 0 T.Lx ×ˢ Set.Ico 0 T.Ly,
          (fun x : ℝ => (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) *
            Real.exp (-(x - T.κ * (n' : ℝ) / 2) ^ 2) : ℝ) : ℂ)) r.1 *
          (fun y : ℝ => Complex.exp ((I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ))) r.2
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
        rw [← Measure.volume_eq_prod, e]
        rfl
    _ = (∫ x in Set.Ico 0 T.Lx, (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
            Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) * Real.exp (-(x - T.κ * (n' : ℝ) / 2) ^ 2) : ℝ) : ℂ)) *
          ∫ y in Set.Ico 0 T.Ly, Complex.exp ((I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ)) :=
        setIntegral_prod_mul (fun x : ℝ => (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
            Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) * Real.exp (-(x - T.κ * (n' : ℝ) / 2) ^ 2) : ℝ) : ℂ))
          (fun y : ℝ => Complex.exp ((I * ((T.κ * ((n' - n : ℤ) : ℝ) : ℝ) : ℂ)) * (y : ℂ)))
          (Set.Ico 0 T.Lx) (Set.Ico 0 T.Ly)
    _ = _ := by rw [integral_exp_y]

/-- Device: "`$\sum_{q\in\Z}\int_0^{L_x}e^{-2(R_x-\kappa n_0/2-qL_x)^2}\dd R_x=\int_\R e^{-2t^2}\dd t=\sqrt{\pi/2}$`" (block A's
`gauss_unfold` at the Gaussian `e^{−2t²}`). -/
theorem gauss_unfold2 (T : Torus) (a : ℝ) :
    ∑' m : ℤ, ∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - (a + m * T.Lx)) ^ 2) = Real.sqrt (π / 2) := by
  have hfd := isAddFundamentalDomain_Ioc T.Lx_pos 0 (μ := (volume : Measure ℝ))
  have hint : Integrable (fun x : ℝ => Real.exp (-2 * (x - a) ^ 2)) :=
    (integrable_exp_neg_mul_sq (b := 2) two_pos).comp_sub_right a
  have hgauss : ∫ x : ℝ, Real.exp (-2 * (x - a) ^ 2) = Real.sqrt (π / 2) := by
    rw [integral_sub_right_eq_self (fun x : ℝ => Real.exp (-2 * x ^ 2)) a]
    exact integral_gaussian 2
  rw [← hgauss, hfd.integral_eq_tsum' _ hint]
  have hinj : Function.Injective (fun m : ℤ => (⟨m • T.Lx, AddSubgroup.zsmul_mem_zmultiples T.Lx m⟩ :
      AddSubgroup.zmultiples T.Lx)) := by
    intro m m' h
    have h1 : m • T.Lx = m' • T.Lx := congrArg Subtype.val h
    rw [zsmul_eq_mul, zsmul_eq_mul] at h1
    exact_mod_cast mul_right_cancel₀ T.Lx_pos.ne' h1
  have hsupp : Function.support (fun g : AddSubgroup.zmultiples T.Lx =>
      ∫ x in Set.Ioc 0 (0 + T.Lx), Real.exp (-2 * ((-g +ᵥ x) - a) ^ 2)) ⊆ Set.range (fun m : ℤ =>
        (⟨m • T.Lx, AddSubgroup.zsmul_mem_zmultiples T.Lx m⟩ : AddSubgroup.zmultiples T.Lx)) := by
    rintro ⟨g, hg⟩ _
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
    exact ⟨m, rfl⟩
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun m => ?_
  rw [integral_Ico_eq_integral_Ioc, zero_add]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (-2 * (x - (a + m * T.Lx)) ^ 2) = Real.exp (-2 * ((-(m • T.Lx) + x) - a) ^ 2)
  rw [zsmul_eq_mul]
  ring_nf

/-- Device: a sequence of period `K` is bounded by the sum of its values on `{0, …, K − 1}`. -/
theorem periodic_norm_le {K : ℕ} (hK : 0 < K) (u : ℤ → ℂ) (hu : ∀ n, u (n + K) = u n) (n : ℤ) :
    ‖u n‖ ≤ ∑ i ∈ Finset.range K, ‖u i‖ := by
  have hper : ∀ q : ℤ, ∀ n : ℤ, u (n + q * K) = u n := by
    intro q
    induction q using Int.induction_on with
    | zero => intro n; simp
    | succ q ih => intro n; rw [show n + ((q : ℤ) + 1) * K = (n + q * K) + K by ring, hu, ih]
    | pred q ih =>
        intro n
        have := hu (n + (-(q : ℤ) - 1) * K)
        rw [show n + (-(q : ℤ) - 1) * K + K = n + (-(q : ℤ)) * K by ring, ih] at this
        exact this.symm
  have hKz : (0 : ℤ) < K := by exact_mod_cast hK
  have h1 : u n = u ((n % K).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hKz.ne'), ← hper (n / K) (n % K), Int.emod_add_ediv_mul]
  rw [h1]
  refine Finset.single_le_sum (f := fun i : ℕ => ‖u i‖) (fun _ _ => norm_nonneg _) ?_
  rw [Finset.mem_range]
  have := Int.emod_lt_of_pos n hKz
  omega

/-- Device: `Σ_{n₀ < K} Σ_q F(n₀ + qK) = Σ_n F(n)` for summable `F : ℤ → ℂ`. -/
theorem sum_range_tsum {K : ℕ} (hK : 0 < K) (F : ℤ → ℂ) (hF : Summable F) :
    ∑ n0 ∈ Finset.range K, ∑' q : ℤ, F (n0 + q * K) = ∑' n : ℤ, F n := by
  have : NeZero K := ⟨hK.ne'⟩
  rw [← sum_zmod_tsum (N := K) F hF]
  refine (Finset.sum_bij (fun (i : ℕ) _ => (i : ZMod K)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_)
  · intro a ha b hb h
    rw [Finset.mem_range] at ha hb
    have := congrArg ZMod.val h
    rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at this
  · intro j _
    exact ⟨j.val, Finset.mem_range.mpr (ZMod.val_lt j), ZMod.natCast_zmod_val j⟩
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [ZMod.val_cast_of_lt hi]

/-- Device: the integral over `𝕋_N` of `conj(Σ_n W_R(n) u_n) · Σ_n W_R(n) v_n` for `2N_φ`-periodic `u, v` (the proof
of Theorem 4.2(c)). -/
theorem integral_star_tsum_Wb (T : Torus) (u v : ℤ → ℂ) (hu : ∀ n, u (n + (2 * T.Nφ : ℕ)) = u n)
    (hv : ∀ n, v (n + (2 * T.Nφ : ℕ)) = v n) :
    ∫ R in fundDom T, star (∑' n : ℤ, Wb T R n * u n) * ∑' n : ℤ, Wb T R n * v n =
      (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * T.Ly * Real.sqrt (π / 2) : ℝ) : ℂ) *
        ∑ n ∈ Finset.range (2 * T.Nφ), star (u n) * v n := by
  have hK : 0 < 2 * T.Nφ := by have := T.Nφ_pos; omega
  have hub := periodic_norm_le hK u hu
  have hvb := periodic_norm_le hK v hv
  set Cu := ∑ i ∈ Finset.range (2 * T.Nφ), ‖u i‖ with hCu
  set Cv := ∑ i ∈ Finset.range (2 * T.Nφ), ‖v i‖ with hCv
  have hCu0 : 0 ≤ Cu := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hCv0 : 0 ≤ Cv := Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- pointwise summability and the product expansion
  have hsW : ∀ (R : ℝ × ℝ) (w : ℤ → ℂ) (C : ℝ), (∀ n, ‖w n‖ ≤ C) → Summable (fun n => ‖Wb T R n * w n‖) := by
    intro R w C hw
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (((Analysis.summable_gauss_int (L := T.κ / 2) (by linarith [T.κ_pos]) R.1).mul_left
        (T.κ / (2 * T.Ly * Real.sqrt π))).mul_right C)
    rw [norm_mul]
    exact mul_le_mul (norm_Wb_le T R n) (hw n) (norm_nonneg _)
      (mul_nonneg (cW_pos T).le (Real.exp_pos _).le)
  have hpt : ∀ R : ℝ × ℝ, star (∑' n : ℤ, Wb T R n * u n) * ∑' n : ℤ, Wb T R n * v n =
      ∑' p : ℤ × ℤ, star (Wb T R p.1 * u p.1) * (Wb T R p.2 * v p.2) := by
    intro R
    rw [tsum_star]
    exact tsum_mul_tsum_of_summable_norm (by simpa only [norm_star] using hsW R u Cu hub) (hsW R v Cv hvb)
  simp_rw [hpt]
  have hmeas : MeasurableSet (fundDom T) := measurableSet_Ico.prod measurableSet_Ico
  have hint : ∀ p : ℤ × ℤ, Integrable (fun r => star (Wb T r p.1 * u p.1) * (Wb T r p.2 * v p.2))
      (volume.restrict (fundDom T)) := by
    intro p
    have hc : Continuous (fun r => star (Wb T r p.1 * u p.1) * (Wb T r p.2 * v p.2)) :=
      (((continuous_Wb T p.1).mul continuous_const).star).mul ((continuous_Wb T p.2).mul continuous_const)
    exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ico_subset_Icc_self Set.Ico_subset_Icc_self)
  have hsum : Summable (fun p : ℤ × ℤ => ∫ r in fundDom T, ‖star (Wb T r p.1 * u p.1) * (Wb T r p.2 * v p.2)‖) := by
    have hB := summable_Wb_bound T
    have hB' : Summable (fun n : ℤ => ‖T.κ / (2 * T.Ly * Real.sqrt π) *
        (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - n * (T.κ / 4)) ^ 2) / 2))‖) :=
      hB.congr fun n => (Real.norm_of_nonneg (mul_nonneg (cW_pos T).le (by positivity))).symm
    have hprod := ((summable_mul_of_summable_norm hB' hB').mul_left (Cu * Cv)).mul_left (volume.real (fundDom T))
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun r => norm_nonneg _) (fun p => ?_) hprod
    have hcst : IntegrableOn (fun _ : ℝ × ℝ => Cu * Cv * (T.κ / (2 * T.Ly * Real.sqrt π) *
        (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - p.1 * (T.κ / 4)) ^ 2) / 2)) *
        (T.κ / (2 * T.Ly * Real.sqrt π) *
        (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - p.2 * (T.κ / 4)) ^ 2) / 2))))) (fundDom T) :=
      (continuous_const.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Set.Ico_subset_Icc_self Set.Ico_subset_Icc_self)
    refine (setIntegral_mono_on (hint p).norm hcst hmeas fun r hr => ?_).trans_eq ?_
    · rw [norm_mul, norm_star, norm_mul, norm_mul]
      have h1 := norm_Wb_le_fd T r hr p.1
      have h2 := norm_Wb_le_fd T r hr p.2
      have h3 := hub p.1
      have h4 := hvb p.2
      calc ‖Wb T r p.1‖ * ‖u p.1‖ * (‖Wb T r p.2‖ * ‖v p.2‖)
          = (‖Wb T r p.1‖ * ‖Wb T r p.2‖) * (‖u p.1‖ * ‖v p.2‖) := by ring
        _ ≤ ((T.κ / (2 * T.Ly * Real.sqrt π) *
              (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - p.1 * (T.κ / 4)) ^ 2) / 2))) *
            (T.κ / (2 * T.Ly * Real.sqrt π) *
              (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - p.2 * (T.κ / 4)) ^ 2) / 2)))) * (Cu * Cv) :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (cW_pos T).le (by positivity)))
              (mul_le_mul h3 h4 (norm_nonneg _) hCu0) (by positivity)
              (mul_nonneg (mul_nonneg (cW_pos T).le (by positivity)) (mul_nonneg (cW_pos T).le (by positivity)))
        _ = _ := by ring
    · rw [setIntegral_const, smul_eq_mul]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  -- each term
  have hterm : ∀ p : ℤ × ℤ, ∫ r in fundDom T, star (Wb T r p.1 * u p.1) * (Wb T r p.2 * v p.2) =
      star (u p.1) * v p.2 * ((∫ x in Set.Ico 0 T.Lx, (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
        Real.exp (-(x - T.κ * (p.1 : ℝ) / 2) ^ 2) * Real.exp (-(x - T.κ * (p.2 : ℝ) / 2) ^ 2) : ℝ) : ℂ)) *
          (if p.2 - p.1 = 0 then (T.Ly : ℂ) else 0)) := by
    intro p
    rw [← integral_star_Wb_mul_Wb, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [star_mul']
    ring
  simp_rw [hterm]
  have hdiag : ∀ p : ℤ × ℤ, (p.2 - p.1 = 0) ↔ p.1 = p.2 := fun p => by rw [sub_eq_zero, eq_comm]
  simp_rw [hdiag]
  have e0 : ∀ p : ℤ × ℤ, star (u p.1) * v p.2 * ((∫ x in Set.Ico 0 T.Lx, (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
        Real.exp (-(x - T.κ * (p.1 : ℝ) / 2) ^ 2) * Real.exp (-(x - T.κ * (p.2 : ℝ) / 2) ^ 2) : ℝ) : ℂ)) *
          (if p.1 = p.2 then (T.Ly : ℂ) else 0)) =
      if p.1 = p.2 then star (u p.1) * v p.1 * ((∫ x in Set.Ico 0 T.Lx, (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
        Real.exp (-(x - T.κ * (p.1 : ℝ) / 2) ^ 2) * Real.exp (-(x - T.κ * (p.1 : ℝ) / 2) ^ 2) : ℝ) : ℂ)) *
          (T.Ly : ℂ)) else 0 := by
    intro p
    split_ifs with h
    · rw [← h]
    · rw [mul_zero, mul_zero]
  simp_rw [e0]
  rw [tsum_diag (fun n : ℤ => star (u n) * v n * ((∫ x in Set.Ico 0 T.Lx, (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
    Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) * Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) : ℝ) : ℂ)) * (T.Ly : ℂ)))]
  -- the diagonal terms
  have e1 : ∀ n : ℤ, (∫ x in Set.Ico 0 T.Lx, (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
        Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) * Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) : ℝ) : ℂ)) =
      (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
        ∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - T.κ * (n : ℝ) / 2) ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [integral_complex_ofReal, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) *
        Real.exp (-(x - T.κ * (n : ℝ) / 2) ^ 2) = (T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
        Real.exp (-2 * (x - T.κ * (n : ℝ) / 2) ^ 2)
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [e1]
  -- the sum over `n ∈ ℤ` by residues mod `2N_φ`
  have hJ : ∀ (n0 : ℕ) (q : ℤ), (∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - T.κ * (((n0 : ℤ) + q * (2 * T.Nφ : ℕ) : ℤ) : ℝ) / 2) ^ 2)) =
      ∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - (T.κ * (n0 : ℝ) / 2 + q * T.Lx)) ^ 2) := by
    intro n0 q
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Real.exp (-2 * (x - T.κ * (((n0 : ℤ) + q * (2 * T.Nφ : ℕ) : ℤ) : ℝ) / 2) ^ 2) =
      Real.exp (-2 * (x - (T.κ * (n0 : ℝ) / 2 + q * T.Lx)) ^ 2)
    rw [Torus.Lx_eq]
    push_cast
    ring_nf
  have hFs : Summable (fun n : ℤ => star (u n) * v n * ((((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
      ∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - T.κ * (n : ℝ) / 2) ^ 2) : ℝ) : ℂ) * (T.Ly : ℂ))) := by
    have hdom : Summable (fun n : ℤ => Cu * Cv * ((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * T.Lx * T.Ly *
        (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - n * (T.κ / 4)) ^ 2) / 2)))) :=
      (((Analysis.summable_gauss_int (L := T.κ / 4) (by linarith [T.κ_pos]) 0).mul_left
        (Real.exp (T.Lx ^ 2 / 2))).mul_left ((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * T.Lx * T.Ly)).mul_left (Cu * Cv)
    refine Summable.of_norm_bounded hdom fun n => ?_
    rw [norm_mul, norm_mul, norm_mul, norm_star, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos T.Ly_pos]
    have hI0 : 0 ≤ ∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - T.κ * (n : ℝ) / 2) ^ 2) :=
      integral_nonneg fun x => (Real.exp_pos _).le
    have hIle : ∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - T.κ * (n : ℝ) / 2) ^ 2) ≤
        T.Lx * (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - n * (T.κ / 4)) ^ 2) / 2)) := by
      have hb : ∀ x ∈ Set.Ico 0 T.Lx, Real.exp (-2 * (x - T.κ * (n : ℝ) / 2) ^ 2) ≤
          Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - n * (T.κ / 4)) ^ 2) / 2) := by
        intro x hx
        have h := gauss_strip_bound (T.κ * (n : ℝ) / 2) x T.Lx hx.1 hx.2.le
        have e : Real.exp (-((0 - n * (T.κ / 4)) ^ 2) / 2) = Real.exp (-((T.κ * (n : ℝ) / 2) ^ 2 / 4) / 2) := by
          congr 1; ring
        rw [e]
        refine le_trans (Real.exp_le_exp.mpr ?_) h
        nlinarith [sq_nonneg (x - T.κ * (n : ℝ) / 2)]
      calc ∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - T.κ * (n : ℝ) / 2) ^ 2)
          ≤ ∫ x in Set.Ico 0 T.Lx, Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - n * (T.κ / 4)) ^ 2) / 2) :=
            setIntegral_mono_on
              ((Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ico_subset_Icc_self)
              ((Continuous.integrableOn_Icc continuous_const).mono_set Set.Ico_subset_Icc_self)
              measurableSet_Ico hb
        _ = T.Lx * (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - n * (T.κ / 4)) ^ 2) / 2)) := by
            rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal
              (by linarith [T.Lx_pos]), sub_zero]
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hI0)]
    calc ‖u n‖ * ‖v n‖ * ((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
          (∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - T.κ * (n : ℝ) / 2) ^ 2)) * T.Ly)
        ≤ Cu * Cv * ((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
          (T.Lx * (Real.exp (T.Lx ^ 2 / 2) * Real.exp (-((0 - n * (T.κ / 4)) ^ 2) / 2))) * T.Ly) :=
          mul_le_mul (mul_le_mul (hub n) (hvb n) (norm_nonneg _) hCu0)
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIle (sq_nonneg _)) T.Ly_pos.le)
            (mul_nonneg (mul_nonneg (sq_nonneg _) hI0) T.Ly_pos.le) (mul_nonneg hCu0 hCv0)
      _ = _ := by ring
  rw [← sum_range_tsum hK _ hFs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n0 _ => ?_
  have hu' : ∀ q : ℤ, u ((n0 : ℤ) + q * (2 * T.Nφ : ℕ)) = u n0 := by
    intro q
    induction q using Int.induction_on with
    | zero => simp
    | succ q ih => rw [show (n0 : ℤ) + ((q : ℤ) + 1) * (2 * T.Nφ : ℕ) =
        ((n0 : ℤ) + q * (2 * T.Nφ : ℕ)) + (2 * T.Nφ : ℕ) by ring, hu, ih]
    | pred q ih =>
        have := hu ((n0 : ℤ) + (-(q : ℤ) - 1) * (2 * T.Nφ : ℕ))
        rw [show (n0 : ℤ) + (-(q : ℤ) - 1) * (2 * T.Nφ : ℕ) + (2 * T.Nφ : ℕ) =
          (n0 : ℤ) + (-(q : ℤ)) * (2 * T.Nφ : ℕ) by ring, ih] at this
        exact this.symm
  have hv' : ∀ q : ℤ, v ((n0 : ℤ) + q * (2 * T.Nφ : ℕ)) = v n0 := by
    intro q
    induction q using Int.induction_on with
    | zero => simp
    | succ q ih => rw [show (n0 : ℤ) + ((q : ℤ) + 1) * (2 * T.Nφ : ℕ) =
        ((n0 : ℤ) + q * (2 * T.Nφ : ℕ)) + (2 * T.Nφ : ℕ) by ring, hv, ih]
    | pred q ih =>
        have := hv ((n0 : ℤ) + (-(q : ℤ) - 1) * (2 * T.Nφ : ℕ))
        rw [show (n0 : ℤ) + (-(q : ℤ) - 1) * (2 * T.Nφ : ℕ) + (2 * T.Nφ : ℕ) =
          (n0 : ℤ) + (-(q : ℤ)) * (2 * T.Nφ : ℕ) by ring, ih] at this
        exact this.symm
  simp_rw [hu', hv', hJ]
  have hJs : ∑' q : ℤ, ((((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
      ∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - (T.κ * (n0 : ℝ) / 2 + q * T.Lx)) ^ 2) : ℝ) : ℂ) * (T.Ly : ℂ)) =
      (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * T.Ly * Real.sqrt (π / 2) : ℝ) : ℂ) := by
    rw [tsum_mul_right, ← Complex.ofReal_tsum, tsum_mul_left, gauss_unfold2]
    push_cast
    ring
  rw [show (∑' q : ℤ, star (u n0) * v n0 * ((((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
      ∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - (T.κ * (n0 : ℝ) / 2 + q * T.Lx)) ^ 2) : ℝ) : ℂ) * (T.Ly : ℂ))) =
      star (u n0) * v n0 * ∑' q : ℤ, ((((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 *
      ∫ x in Set.Ico 0 T.Lx, Real.exp (-2 * (x - (T.κ * (n0 : ℝ) / 2 + q * T.Lx)) ^ 2) : ℝ) : ℂ) * (T.Ly : ℂ)) from
    tsum_mul_left, hJs]
  ring

/-! ### Proof devices for Theorem 4.2(a): a reduction (phase (b); not statements of the paper)

The reduction of Theorem 4.2(a): `localForm_a_of_pairFormIdentity` derives both equalities of (a) from the device
statement `PairFormIdentity`, which the next section proves (`PairForm.pairFormIdentity`).
`PairFormIdentity` says that for every antisymmetric pair amplitude `u : Modes × Modes → ℂ` the form of `H_N`,
`½ Σ_{σσ'} Σ_{abcd} V_{abcd} \bar u((a,σ),(b,σ')) u((c,σ),(d,σ'))`, equals that of `8π ∫ Σ_ν B_ν^* B_ν`,
`8π Σ_ν ∫_{𝕋_N} |A_ν(R, u)|² dR` with `A_ν(R, u) = Σ_{jj'σσ'} ψ_j(R) (Dψ_{j'})(R) \bar χ^ν_{σσ'} u((j',σ),(j,σ'))` —
the paper's Steps 2–5 (the two-particle computation), with `u` in the place of `√2 υ`. The reduction replaces the
paper's Step 6: the matrix entry `(m, m')` of each side is a sum over `k` of the form at the amplitudes
`u_{km}(μ, μ') := (c_{μ'} c_μ)_{km}` and `u_{km'}`, which are antisymmetric by the CAR, and the sesquilinear identity at
two amplitudes follows from the quadratic one by polarization. -/

section Devices42a

variable (T : Torus)

/-- Device: a pair amplitude, a complex function of two modes. -/
abbrev PairAmp : Type := Modes T → Modes T → ℂ

/-- Device: the pair amplitude of the matrix entry `(k, m)`, `u(μ, μ') := (c_{μ'} c_μ)_{k m}`. -/
def pairAmpOf (k m : Conf (ZMod T.Nφ)) : PairAmp T := fun μ μ' => (cjs T μ'.1 μ'.2 * cjs T μ.1 μ.2) k m

/-- Device: `A_ν(R, u) := Σ_{j j'} ψ_j(R) (Dψ_{j'})(R) Σ_{σ σ'} \bar χ^ν_{σσ'} u((j', σ), (j, σ'))`. -/
def tripletAmp (ν : Triplet) (R : ℝ × ℝ) (u : PairAmp T) : ℂ :=
  ∑ j : ZMod T.Nφ, ∑ j' : ZMod T.Nφ, (psi T j R * Dcov (psi T j') R) *
    ∑ σ : Spin, ∑ σ' : Spin, star (chi ν σ σ') * u (j', σ) (j, σ')

/-- Device: the sesquilinear form of `H_N` on pair amplitudes. -/
def formHN (u u' : PairAmp T) : ℂ :=
  (1 / 2 : ℂ) * ∑ σ : Spin, ∑ σ' : Spin, ∑ a : ZMod T.Nφ, ∑ b : ZMod T.Nφ, ∑ c : ZMod T.Nφ, ∑ d : ZMod T.Nφ,
    Vcoef T a b c d * (star (u (a, σ) (b, σ')) * u' (c, σ) (d, σ'))

/-- Device: the sesquilinear form of `8π ∫_{𝕋_N} Σ_ν B_ν(R)^* B_ν(R) dR` on pair amplitudes. -/
def formLocal (u u' : PairAmp T) : ℂ :=
  ((8 * π : ℝ) : ℂ) * ∑ ν : Triplet, ∫ R in fundDom T, star (tripletAmp T ν R u) * tripletAmp T ν R u'

/-- Device (proved in the next section, `PairForm.pairFormIdentity`; the analytic core of Theorem 4.2(a), the paper's
Steps 2–5): for every antisymmetric pair amplitude the two quadratic forms agree. -/
def PairFormIdentity : Prop :=
  ∀ u : PairAmp T, (∀ μ μ' : Modes T, u μ' μ = -u μ μ') → formHN T u u = formLocal T u u

theorem sum_comm7_dev {A₁ A₂ A₃ A₄ A₅ A₆ K : Type*} [Fintype A₁] [Fintype A₂] [Fintype A₃] [Fintype A₄]
    [Fintype A₅] [Fintype A₆] [Fintype K] (g : A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → K → ℂ) :
    ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, ∑ a₅, ∑ a₆, ∑ k, g a₁ a₂ a₃ a₄ a₅ a₆ k =
      ∑ k, ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, ∑ a₅, ∑ a₆, g a₁ a₂ a₃ a₄ a₅ a₆ k := by
  symm
  calc ∑ k, ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, ∑ a₅, ∑ a₆, g a₁ a₂ a₃ a₄ a₅ a₆ k
      = ∑ a₁, ∑ k, ∑ a₂, ∑ a₃, ∑ a₄, ∑ a₅, ∑ a₆, g a₁ a₂ a₃ a₄ a₅ a₆ k := Finset.sum_comm
    _ = ∑ a₁, ∑ a₂, ∑ k, ∑ a₃, ∑ a₄, ∑ a₅, ∑ a₆, g a₁ a₂ a₃ a₄ a₅ a₆ k :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a₁, ∑ a₂, ∑ a₃, ∑ k, ∑ a₄, ∑ a₅, ∑ a₆, g a₁ a₂ a₃ a₄ a₅ a₆ k :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, ∑ k, ∑ a₅, ∑ a₆, g a₁ a₂ a₃ a₄ a₅ a₆ k :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_comm
    _ = ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, ∑ a₅, ∑ k, ∑ a₆, g a₁ a₂ a₃ a₄ a₅ a₆ k :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, ∑ a₅, ∑ a₆, ∑ k, g a₁ a₂ a₃ a₄ a₅ a₆ k :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Device: polarization, for two forms with the sesquilinear expansion, on a set of vectors closed under
`u + c • v`. -/
theorem polarization_dev {V : Type*} [AddCommGroup V] [Module ℂ V] (P : V → Prop)
    (hP : ∀ (u v : V) (c : ℂ), P u → P v → P (u + c • v)) (S1 S2 : V → V → ℂ)
    (h1 : ∀ (u v : V) (c : ℂ), S1 (u + c • v) (u + c • v) =
      S1 u u + c * S1 u v + star c * S1 v u + star c * c * S1 v v)
    (h2 : ∀ (u v : V) (c : ℂ), S2 (u + c • v) (u + c • v) =
      S2 u u + c * S2 u v + star c * S2 v u + star c * c * S2 v v)
    (h : ∀ u, P u → S1 u u = S2 u u) {u v : V} (hu : P u) (hv : P v) : S1 u v = S2 u v := by
  have q : ∀ c : ℂ, S1 (u + c • v) (u + c • v) = S2 (u + c • v) (u + c • v) := fun c => h _ (hP u v c hu hv)
  have hsI : star I = -I := Complex.conj_I
  have a1 := h1 u v 1
  have a2 := h1 u v (-1)
  have a3 := h1 u v I
  have a4 := h1 u v (-I)
  have b1 := h2 u v 1
  have b2 := h2 u v (-1)
  have b3 := h2 u v I
  have b4 := h2 u v (-I)
  have q1 := q 1
  have q2 := q (-1)
  have q3 := q I
  have q4 := q (-I)
  simp only [star_one, star_neg, hsI] at a1 a2 a3 a4 b1 b2 b3 b4
  linear_combination (-(1 / 4 : ℂ)) * (a1 - a2 - I * (a3 - a4)) + (1 / 4 : ℂ) * (b1 - b2 - I * (b3 - b4)) +
    (1 / 4 : ℂ) * (q1 - q2 - I * (q3 - q4)) +
    (((S1 u v - S2 u v) - (S1 v u - S2 v u)) / 2) * Complex.I_sq

theorem formHN_expand (u v : PairAmp T) (c : ℂ) :
    formHN T (u + c • v) (u + c • v) =
      formHN T u u + c * formHN T u v + star c * formHN T v u + star c * c * formHN T v v := by
  simp only [formHN, Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul', Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem tripletAmp_add_smul (ν : Triplet) (R : ℝ × ℝ) (u v : PairAmp T) (c : ℂ) :
    tripletAmp T ν R (u + c • v) = tripletAmp T ν R u + c * tripletAmp T ν R v := by
  simp only [tripletAmp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun σ _ =>
    Finset.sum_congr rfl fun σ' _ => ?_
  ring

theorem tripletAmp_continuous (ν : Triplet) (u : PairAmp T) : Continuous fun R => tripletAmp T ν R u := by
  unfold tripletAmp
  refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun j' _ => ?_
  exact ((psi_contDiff T j).continuous.mul (contDiff_Dcov (psi_contDiff T j')).continuous).mul continuous_const

theorem integrable_tripletAmp (ν : Triplet) (u u' : PairAmp T) :
    Integrable (fun R => star (tripletAmp T ν R u) * tripletAmp T ν R u') (volume.restrict (fundDom T)) := by
  have h := integrableOn_inter_fundDom
    ((tripletAmp_continuous T ν u).star.mul (tripletAmp_continuous T ν u')) T Set.univ
  rw [Set.univ_inter] at h
  exact h

theorem formLocal_expand (u v : PairAmp T) (c : ℂ) :
    formLocal T (u + c • v) (u + c • v) =
      formLocal T u u + c * formLocal T u v + star c * formLocal T v u + star c * c * formLocal T v v := by
  have e : ∀ ν : Triplet,
      ∫ R in fundDom T, star (tripletAmp T ν R (u + c • v)) * tripletAmp T ν R (u + c • v) =
      (∫ R in fundDom T, star (tripletAmp T ν R u) * tripletAmp T ν R u) +
        c * (∫ R in fundDom T, star (tripletAmp T ν R u) * tripletAmp T ν R v) +
        star c * (∫ R in fundDom T, star (tripletAmp T ν R v) * tripletAmp T ν R u) +
        star c * c * (∫ R in fundDom T, star (tripletAmp T ν R v) * tripletAmp T ν R v) := by
    intro ν
    have hf1 : Integrable (fun R => star (tripletAmp T ν R u) * tripletAmp T ν R u) (volume.restrict (fundDom T)) :=
      integrable_tripletAmp T ν u u
    have hf2 : Integrable (fun R => c * (star (tripletAmp T ν R u) * tripletAmp T ν R v))
        (volume.restrict (fundDom T)) :=
      (integrable_tripletAmp T ν u v).const_mul c
    have hf3 : Integrable (fun R => star c * (star (tripletAmp T ν R v) * tripletAmp T ν R u))
        (volume.restrict (fundDom T)) :=
      (integrable_tripletAmp T ν v u).const_mul (star c)
    have hf4 : Integrable (fun R => star c * c * (star (tripletAmp T ν R v) * tripletAmp T ν R v))
        (volume.restrict (fundDom T)) :=
      (integrable_tripletAmp T ν v v).const_mul (star c * c)
    have hf12 : Integrable (fun R => star (tripletAmp T ν R u) * tripletAmp T ν R u +
        c * (star (tripletAmp T ν R u) * tripletAmp T ν R v)) (volume.restrict (fundDom T)) := hf1.add hf2
    have hf123 : Integrable (fun R => star (tripletAmp T ν R u) * tripletAmp T ν R u +
        c * (star (tripletAmp T ν R u) * tripletAmp T ν R v) +
        star c * (star (tripletAmp T ν R v) * tripletAmp T ν R u)) (volume.restrict (fundDom T)) := hf12.add hf3
    calc _ = ∫ R in fundDom T, (star (tripletAmp T ν R u) * tripletAmp T ν R u +
          c * (star (tripletAmp T ν R u) * tripletAmp T ν R v) +
          star c * (star (tripletAmp T ν R v) * tripletAmp T ν R u) +
          star c * c * (star (tripletAmp T ν R v) * tripletAmp T ν R v)) := by
          congr 1
          funext R
          rw [tripletAmp_add_smul]
          simp only [star_add, star_mul']
          ring
      _ = _ := by
          rw [integral_add hf123 hf4, integral_add hf12 hf3, integral_add hf1 hf2, integral_const_mul,
            integral_const_mul, integral_const_mul]
  simp only [formLocal, e, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem pairAmpOf_anti (k m : Conf (ZMod T.Nφ)) (μ μ' : Modes T) :
    pairAmpOf T k m μ' μ = -pairAmpOf T k m μ μ' := by
  have h := cf_anticomm T (spinTensor (orb T μ.1) μ.2) (spinTensor (orb T μ'.1) μ'.2)
  have h2 : cjs T μ.1 μ.2 * cjs T μ'.1 μ'.2 = -(cjs T μ'.1 μ'.2 * cjs T μ.1 μ.2) := eq_neg_of_add_eq_zero_left h
  simp only [pairAmpOf, h2, Matrix.neg_apply]

theorem HN_apply_eq_sum_formHN (m m' : Conf (ZMod T.Nφ)) :
    HN T m m' = ∑ k : Conf (ZMod T.Nφ), formHN T (pairAmpOf T k m) (pairAmpOf T k m') := by
  have e : ∀ (a b c d : ZMod T.Nφ) (σ σ' : Spin),
      ((cjs T a σ)ᴴ * (cjs T b σ')ᴴ * cjs T d σ' * cjs T c σ) m m' =
        ∑ k, star (pairAmpOf T k m (a, σ) (b, σ')) * pairAmpOf T k m' (c, σ) (d, σ') := by
    intro a b c d σ σ'
    rw [show (cjs T a σ)ᴴ * (cjs T b σ')ᴴ * cjs T d σ' * cjs T c σ =
      (cjs T b σ' * cjs T a σ)ᴴ * (cjs T d σ' * cjs T c σ) by
        rw [Matrix.conjTranspose_mul]
        simp only [mul_assoc]]
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, pairAmpOf]
  simp only [HN, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, e, formHN, Finset.mul_sum]
  exact sum_comm7_dev _

theorem Bν_apply_eq_tripletAmp (ν : Triplet) (R : ℝ × ℝ) (k m : Conf (ZMod T.Nφ)) :
    Bν T ν R k m = tripletAmp T ν R (pairAmpOf T k m) := by
  rw [Bν_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, tripletAmp, pairAmpOf, cpair]
  rfl

theorem localIntegral_apply_eq_sum_formLocal (m m' : Conf (ZMod T.Nφ)) :
    (((8 * π : ℝ) : ℂ) • opIntegral (fundDom T) (fun R => ∑ ν : Triplet, (Bν T ν R)ᴴ * Bν T ν R)) m m' =
      ∑ k : Conf (ZMod T.Nφ), formLocal T (pairAmpOf T k m) (pairAmpOf T k m') := by
  have e : ∀ R, (∑ ν : Triplet, (Bν T ν R)ᴴ * Bν T ν R) m m' =
      ∑ ν : Triplet, ∑ k : Conf (ZMod T.Nφ),
        star (tripletAmp T ν R (pairAmpOf T k m)) * tripletAmp T ν R (pairAmpOf T k m') := by
    intro R
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Bν_apply_eq_tripletAmp]
  have hint : ∀ (ν : Triplet) (k : Conf (ZMod T.Nφ)),
      Integrable (fun R => star (tripletAmp T ν R (pairAmpOf T k m)) * tripletAmp T ν R (pairAmpOf T k m'))
        (volume.restrict (fundDom T)) := fun ν k => integrable_tripletAmp T ν _ _
  simp only [Matrix.smul_apply, opIntegral, Matrix.of_apply, smul_eq_mul, e, formLocal]
  rw [integral_finsetSum _ (fun ν _ => integrable_finsetSum _ (fun k _ => hint ν k)),
    Finset.sum_congr rfl fun ν _ => integral_finsetSum _ fun k _ => hint ν k, Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- Device: **Theorem 4.2(a) from the scalar identity `PairFormIdentity`** (the reduction; the identity is
`PairForm.pairFormIdentity`). -/
theorem localForm_a_of_pairFormIdentity (h : PairFormIdentity T) :
    HN T = ((8 * π : ℝ) : ℂ) • opIntegral (fundDom T) (fun R => ∑ ν : Triplet, (Bν T ν R)ᴴ * Bν T ν R) ∧
      HN T = opIntegral (fundDom T) (hR T) := by
  have hsesq : ∀ u v : PairAmp T, (∀ μ μ' : Modes T, u μ' μ = -u μ μ') →
      (∀ μ μ' : Modes T, v μ' μ = -v μ μ') → formHN T u v = formLocal T u v := by
    intro u v hu hv
    exact polarization_dev (fun w : PairAmp T => ∀ μ μ' : Modes T, w μ' μ = -w μ μ')
      (fun u v c hu hv μ μ' => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu μ μ', hv μ μ']
        ring)
      (formHN T) (formLocal T) (formHN_expand T) (formLocal_expand T) h hu hv
  have h1 : HN T = ((8 * π : ℝ) : ℂ) • opIntegral (fundDom T) (fun R => ∑ ν : Triplet, (Bν T ν R)ᴴ * Bν T ν R) := by
    ext m m'
    rw [HN_apply_eq_sum_formHN, localIntegral_apply_eq_sum_formLocal]
    exact Finset.sum_congr rfl fun k _ => hsesq _ _ (pairAmpOf_anti T k m) (pairAmpOf_anti T k m')
  refine ⟨h1, ?_⟩
  rw [h1]
  ext m m'
  simp only [Matrix.smul_apply, opIntegral, Matrix.of_apply, hR, smul_eq_mul]
  rw [integral_const_mul]

end Devices42a

/-! ### Proof devices for Theorem 4.2(a): the scalar identity `PairFormIdentity` (phase (b); not statements of the paper)

The paper's Steps 1–5, in the namespace `HRTorus.Hamiltonian.PairForm`. For an antisymmetric pair amplitude `u`:
`Υ_{σσ'}(r₁, r₂) := Σ_{jj'} u((j,σ),(j',σ')) ψ_j(r₁) ψ_{j'}(r₂)` (`ups`, an orbital pair function `opf`, smooth and of
the lowest Landau level in each variable); Step 2, `formHN u u = 2π ∫ Σ_{σσ'} [|Υ_{σσ'}|²(r,r) + (∇₁²|Υ_{σσ'}|²)(r,r)]`
(`formHN_eq`); Step 4's spin decomposition `Σ_{σσ'} |Υ_{σσ'}|² = Σ_ν |f_ν|² + |f_{sing}|²` (`spin_decomp`, with the
singlet spinor `chiS`), `f_ν` antisymmetric and `f_{sing}` symmetric; Step 3, `(∇₁²N)(R,R) = ¼ ∇²_R[N(R,R)] + (∇²N_R)(0)`
for a smooth symmetric `N` (`step3`, through second derivatives along lines), with `∫_{𝕋_N} ∇²_R[N(R,R)] dR = 0` by
periodicity (`integral_lap_eq_zero`, the device `rectFT_lap` of `HRTorus.LLL.Theta` at `q = 0`); Lemma 4.3
(`jets_antisymm`, `jets_symm`) for each spin component; and Step 5, `(D₁f_ν)(R,R) = A_ν(R, u)` (`D1_comp`). The result
is `pairFormIdentity`. -/

namespace PairForm

open scoped ContDiff

variable (T : Torus)

/-! #### Proof devices: orbital pair functions `Φ(r₁, r₂) = Σ_{j j'} w_{j j'} ψ_j(r₁) ψ_{j'}(r₂)` -/

def opf (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  ∑ j : ZMod T.Nφ, ∑ j' : ZMod T.Nφ, w j j' * (psi T j p.1 * psi T j' p.2)

theorem psi_diffAt_x (j : ZMod T.Nφ) (x y : ℝ) : DifferentiableAt ℝ (fun x' : ℝ => psi T j (x', y)) x :=
  ((psi_contDiff T j).differentiable (by simp)).differentiableAt.comp x
    (differentiableAt_id.prodMk (differentiableAt_const y))

theorem psi_diffAt_y (j : ZMod T.Nφ) (x y : ℝ) : DifferentiableAt ℝ (fun y' : ℝ => psi T j (x, y')) y :=
  ((psi_contDiff T j).differentiable (by simp)).differentiableAt.comp y
    ((differentiableAt_const x).prodMk differentiableAt_id)

theorem Dx_sum (c : ZMod T.Nφ → ℂ) (r : ℝ × ℝ) :
    Dx (fun r' => ∑ j, c j * psi T j r') r = ∑ j, c j * Dx (psi T j) r := by
  simp only [Dx]
  rw [deriv_fun_sum (fun j _ => (psi_diffAt_x T j r.1 r.2).const_mul (c j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deriv_const_mul _ (psi_diffAt_x T j r.1 r.2)]

theorem Dy_sum (c : ZMod T.Nφ → ℂ) (r : ℝ × ℝ) :
    Dy (fun r' => ∑ j, c j * psi T j r') r = ∑ j, c j * Dy (psi T j) r := by
  simp only [Dy]
  rw [deriv_fun_sum (fun j _ => (psi_diffAt_y T j r.1 r.2).const_mul (c j)), Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deriv_const_mul _ (psi_diffAt_y T j r.1 r.2)]
  ring

theorem opf_slice1 (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (r₂ : ℝ × ℝ) :
    (fun r₁ => opf T w (r₁, r₂)) = fun r₁ => ∑ j, (∑ j', w j j' * psi T j' r₂) * psi T j r₁ := by
  funext r₁
  simp only [opf, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  ring

theorem opf_slice2 (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (r₁ : ℝ × ℝ) :
    (fun r₂ => opf T w (r₁, r₂)) = fun r₂ => ∑ j', (∑ j, w j j' * psi T j r₁) * psi T j' r₂ := by
  funext r₂
  simp only [opf, Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun j _ => by ring)

theorem opf_D1x (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    D1x (opf T w) p = ∑ j, (∑ j', w j j' * psi T j' p.2) * Dx (psi T j) p.1 := by
  rw [D1x, opf_slice1, Dx_sum]

theorem opf_D1y (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    D1y (opf T w) p = ∑ j, (∑ j', w j j' * psi T j' p.2) * Dy (psi T j) p.1 := by
  rw [D1y, opf_slice1, Dy_sum]

theorem opf_D2x (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    D2x (opf T w) p = ∑ j', (∑ j, w j j' * psi T j p.1) * Dx (psi T j') p.2 := by
  rw [D2x, opf_slice2, Dx_sum]

theorem opf_D2y (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    D2y (opf T w) p = ∑ j', (∑ j, w j j' * psi T j p.1) * Dy (psi T j') p.2 := by
  rw [D2y, opf_slice2, Dy_sum]

theorem opf_lll₁ (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    D1x (opf T w) p + I * D1y (opf T w) p = 0 := by
  rw [opf_D1x, opf_D1y, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h := psi_lll_eq T j p.1
  linear_combination (∑ j', w j j' * psi T j' p.2) * h

theorem opf_lll₂ (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    D2x (opf T w) p + I * D2y (opf T w) p = 0 := by
  rw [opf_D2x, opf_D2y, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j' _ => ?_
  have h := psi_lll_eq T j' p.2
  linear_combination (∑ j, w j j' * psi T j p.1) * h

theorem opf_contDiff (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) : ContDiff ℝ ∞ (opf T w) := by
  unfold opf
  refine ContDiff.sum fun j _ => ContDiff.sum fun j' _ => ?_
  exact contDiff_const.mul (((psi_contDiff T j).comp contDiff_fst).mul ((psi_contDiff T j').comp contDiff_snd))

theorem opf_swap (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (r₁ r₂ : ℝ × ℝ) :
    opf T w (r₂, r₁) = opf T (fun j j' => w j' j) (r₁, r₂) := by
  simp only [opf]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)

theorem opf_D1 (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    D1 (opf T w) p = ∑ j, (∑ j', w j j' * psi T j' p.2) * Dcov (psi T j) p.1 := by
  rw [D1, opf_D1x, opf_D1y, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Dcov (psi T j) p.1 = (1 / 2 : ℂ) * (Dx (psi T j) p.1 - I * Dy (psi T j) p.1) from rfl]
  ring

/-! #### Proof devices: spin components -/

/-- the singlet spinor `χ^{sing}`: `χ_{↑↓} = −χ_{↓↑} = 2^{-1/2}`, zero diagonal -/
def chiS : Matrix Spin Spin ℂ :=
  Matrix.of fun σ σ' => if σ = .up ∧ σ' = .dn then (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    else if σ = .dn ∧ σ' = .up then -(((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0

/-- the four spinors: `some ν ↦ χ^ν`, `none ↦ χ^{sing}` -/
def chiO : Option Triplet → Matrix Spin Spin ℂ
  | some ν => chi ν
  | none => chiS

/-- the orbital coefficients of the spin component along `χ_o`: `Σ_{σσ'} \bar χ_{σσ'} u((j,σ),(j',σ'))` -/
def wOf (u : PairAmp T) (o : Option Triplet) (j j' : ZMod T.Nφ) : ℂ :=
  ∑ σ : Spin, ∑ σ' : Spin, star (chiO o σ σ') * u (j, σ) (j', σ')

/-- the pair wave function `Υ_{σσ'}` -/
def ups (u : PairAmp T) (σ σ' : Spin) : (ℝ × ℝ) × (ℝ × ℝ) → ℂ :=
  opf T (fun j j' => u (j, σ) (j', σ'))

theorem opf_wOf (u : PairAmp T) (o : Option Triplet) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    opf T (wOf T u o) p = ∑ σ : Spin, ∑ σ' : Spin, star (chiO o σ σ') * ups T u σ σ' p := by
  simp only [opf, wOf, ups, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ j : ZMod T.Nφ, ∑ σ : Spin, ∑ j' : ZMod T.Nφ, ∑ σ' : Spin,
        star (chiO o σ σ') * u (j, σ) (j', σ') * (psi T j p.1 * psi T j' p.2) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ σ : Spin, ∑ j : ZMod T.Nφ, ∑ j' : ZMod T.Nφ, ∑ σ' : Spin,
        star (chiO o σ σ') * u (j, σ) (j', σ') * (psi T j p.1 * psi T j' p.2) := Finset.sum_comm
    _ = ∑ σ : Spin, ∑ j : ZMod T.Nφ, ∑ σ' : Spin, ∑ j' : ZMod T.Nφ,
        star (chiO o σ σ') * u (j, σ) (j', σ') * (psi T j p.1 * psi T j' p.2) :=
        Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ σ : Spin, ∑ σ' : Spin, ∑ j : ZMod T.Nφ, ∑ j' : ZMod T.Nφ,
        star (chiO o σ σ') * u (j, σ) (j', σ') * (psi T j p.1 * psi T j' p.2) :=
        Finset.sum_congr rfl fun σ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ =>
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring

theorem rpow_half_sq : ((((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * ((((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = 1 / 2 := by
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem star_s : star ((((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
  Complex.conj_ofReal _

theorem sum_triplet {M : Type*} [AddCommMonoid M] (g : Triplet → M) :
    ∑ ν : Triplet, g ν = g .plus + g .zero + g .minus := by
  rw [show (Finset.univ : Finset Triplet) = {Triplet.plus, Triplet.zero, Triplet.minus} from rfl]
  simp [Finset.sum_insert, add_assoc]

theorem comp_plus (u : PairAmp T) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    opf T (wOf T u (some .plus)) p = ups T u .up .up p := by
  rw [opf_wOf, HRTorus.Fermion.Pilot.JW.sum_spin, HRTorus.Fermion.Pilot.JW.sum_spin,
    HRTorus.Fermion.Pilot.JW.sum_spin]
  simp only [chiO, chi, Matrix.of_apply, reduceCtorEq,
    and_self, and_true, and_false, ↓reduceIte, star_zero, star_one,
    zero_mul, one_mul, add_zero]

theorem comp_minus (u : PairAmp T) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    opf T (wOf T u (some .minus)) p = ups T u .dn .dn p := by
  rw [opf_wOf, HRTorus.Fermion.Pilot.JW.sum_spin, HRTorus.Fermion.Pilot.JW.sum_spin,
    HRTorus.Fermion.Pilot.JW.sum_spin]
  simp only [chiO, chi, Matrix.of_apply, reduceCtorEq,
    and_self, and_true, and_false, ↓reduceIte, star_zero, star_one,
    zero_mul, one_mul, add_zero, zero_add]

theorem comp_zero (u : PairAmp T) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    opf T (wOf T u (some .zero)) p = (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ups T u .up .dn p +
      (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ups T u .dn .up p := by
  rw [opf_wOf, HRTorus.Fermion.Pilot.JW.sum_spin, HRTorus.Fermion.Pilot.JW.sum_spin,
    HRTorus.Fermion.Pilot.JW.sum_spin]
  simp only [chiO, chi, Matrix.of_apply, ne_eq, reduceCtorEq, not_true_eq_false,
    not_false_eq_true, ↓reduceIte, star_zero,
    star_s, zero_mul, add_zero, zero_add]

theorem comp_sing (u : PairAmp T) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    opf T (wOf T u none) p = (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ups T u .up .dn p -
      (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ups T u .dn .up p := by
  rw [opf_wOf, HRTorus.Fermion.Pilot.JW.sum_spin, HRTorus.Fermion.Pilot.JW.sum_spin,
    HRTorus.Fermion.Pilot.JW.sum_spin]
  simp only [chiO, chiS, Matrix.of_apply, reduceCtorEq,
    and_self, and_true, and_false, ↓reduceIte, star_zero,
    star_neg, star_s, zero_mul, add_zero, zero_add, neg_mul]
  ring

/-- `Σ_{σσ'} |Υ_{σσ'}|² = Σ_ν |f_ν|² + |f_{sing}|²` pointwise -/
theorem spin_decomp (u : PairAmp T) (p : (ℝ × ℝ) × (ℝ × ℝ)) :
    ∑ σ : Spin, ∑ σ' : Spin, star (ups T u σ σ' p) * ups T u σ σ' p =
      ∑ o : Option Triplet, star (opf T (wOf T u o) p) * opf T (wOf T u o) p := by
  rw [Fintype.sum_option, sum_triplet, comp_plus, comp_minus, comp_zero, comp_sing,
    HRTorus.Fermion.Pilot.JW.sum_spin, HRTorus.Fermion.Pilot.JW.sum_spin, HRTorus.Fermion.Pilot.JW.sum_spin]
  simp only [star_add, star_sub, star_mul', star_s]
  have h2 := rpow_half_sq
  linear_combination (-2 : ℂ) * (star (ups T u Spin.up Spin.dn p) * ups T u Spin.up Spin.dn p +
    star (ups T u Spin.dn Spin.up p) * ups T u Spin.dn Spin.up p) * h2


/-! #### Proof devices: (anti)symmetry and the jets -/

theorem chiS_anti (σ σ' : Spin) : chiS σ' σ = -chiS σ σ' := by
  cases σ <;> cases σ' <;> simp [chiS]

theorem wOf_anti (u : PairAmp T) (hu : ∀ μ μ' : Modes T, u μ' μ = -u μ μ') (ν : Triplet) (j j' : ZMod T.Nφ) :
    wOf T u (some ν) j' j = -wOf T u (some ν) j j' := by
  simp only [wOf, chiO]
  rw [← Finset.sum_neg_distrib, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hu (j, a) (j', b), chi_symm_apply]
  ring

theorem wOf_symm (u : PairAmp T) (hu : ∀ μ μ' : Modes T, u μ' μ = -u μ μ') (j j' : ZMod T.Nφ) :
    wOf T u none j' j = wOf T u none j j' := by
  simp only [wOf, chiO]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hu (j, a) (j', b), chiS_anti]
  simp only [star_neg]
  ring

theorem opf_neg_swap (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (hw : ∀ j j', w j' j = -w j j') (r₁ r₂ : ℝ × ℝ) :
    opf T w (r₁, r₂) = -opf T w (r₂, r₁) := by
  rw [opf_swap]
  simp only [opf]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [hw j j']
  ring

theorem opf_eq_swap (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (hw : ∀ j j', w j' j = w j j') (r₁ r₂ : ℝ × ℝ) :
    opf T w (r₁, r₂) = opf T w (r₂, r₁) := by
  rw [opf_swap]
  simp only [opf]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [hw j j']

theorem jets_comp_triplet (u : PairAmp T) (hu : ∀ μ μ' : Modes T, u μ' μ = -u μ μ') (ν : Triplet) (R : ℝ × ℝ) :
    jetF (opf T (wOf T u (some ν))) R 0 = 0 ∧
      lapR (jetF (opf T (wOf T u (some ν))) R) 0 = 4 * ‖D1 (opf T (wOf T u (some ν))) (R, R)‖ ^ 2 :=
  jets_antisymm isOpen_univ (fun _ => Set.mem_univ _) (opf_contDiff T _).contDiffOn
    (fun p _ => opf_lll₁ T _ p) (fun p _ => opf_lll₂ T _ p)
    (fun r₁ r₂ _ _ => opf_neg_swap T _ (wOf_anti T u hu ν) r₁ r₂) R

theorem jets_comp_sing (u : PairAmp T) (hu : ∀ μ μ' : Modes T, u μ' μ = -u μ μ') (R : ℝ × ℝ) :
    jetF (opf T (wOf T u none)) R 0 + lapR (jetF (opf T (wOf T u none)) R) 0 = 0 :=
  jets_symm isOpen_univ (fun _ => Set.mem_univ _) (opf_contDiff T _).contDiffOn
    (fun p _ => opf_lll₁ T _ p) (fun p _ => opf_lll₂ T _ p)
    (fun r₁ r₂ _ _ => opf_eq_swap T _ (wOf_symm T u hu) r₁ r₂) R

theorem D1_comp (u : PairAmp T) (ν : Triplet) (R : ℝ × ℝ) :
    D1 (opf T (wOf T u (some ν))) (R, R) = tripletAmp T ν R u := by
  rw [opf_D1]
  simp only [tripletAmp, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  simp only [wOf, chiO]
  ring

/-! #### Proof devices: linearity of the Laplacian -/

theorem diffAt_x {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (y x : ℝ) :
    DifferentiableAt ℝ (fun x' => g (x', y)) x :=
  (hg.differentiable (by simp)).differentiableAt.comp x (differentiableAt_id.prodMk (differentiableAt_const y))

theorem diffAt_y {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (x y : ℝ) :
    DifferentiableAt ℝ (fun y' => g (x, y')) y :=
  (hg.differentiable (by simp)).differentiableAt.comp y ((differentiableAt_const x).prodMk differentiableAt_id)

theorem diffAt_xx {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (y x : ℝ) :
    DifferentiableAt ℝ (fun x => deriv (fun x' => g (x', y)) x) x :=
  ((contDiff_px hg).differentiable (by simp)).differentiableAt.comp x
    (differentiableAt_id.prodMk (differentiableAt_const y))

theorem diffAt_yy {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (x y : ℝ) :
    DifferentiableAt ℝ (fun y => deriv (fun y' => g (x, y')) y) y :=
  ((contDiff_py hg).differentiable (by simp)).differentiableAt.comp y
    ((differentiableAt_const x).prodMk differentiableAt_id)

theorem lap_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ × ℝ → ℂ) (hg : ∀ i, ContDiff ℝ ∞ (g i)) (r : ℝ × ℝ) :
    lap (fun r' => ∑ i ∈ s, g i r') r = ∑ i ∈ s, lap (g i) r := by
  simp only [lap]
  have e1 : (fun x => deriv (fun x' => ∑ i ∈ s, g i (x', r.2)) x) =
      fun x => ∑ i ∈ s, deriv (fun x' => g i (x', r.2)) x :=
    funext fun x => deriv_fun_sum fun i _ => diffAt_x (hg i) r.2 x
  have e2 : (fun y => deriv (fun y' => ∑ i ∈ s, g i (r.1, y')) y) =
      fun y => ∑ i ∈ s, deriv (fun y' => g i (r.1, y')) y :=
    funext fun y => deriv_fun_sum fun i _ => diffAt_y (hg i) r.1 y
  rw [e1, e2, deriv_fun_sum fun i _ => diffAt_xx (hg i) r.2 r.1,
    deriv_fun_sum fun i _ => diffAt_yy (hg i) r.1 r.2, ← Finset.sum_add_distrib]

theorem lap_const_mul (c : ℂ) {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (r : ℝ × ℝ) :
    lap (fun r' => c * g r') r = c * lap g r := by
  simp only [lap]
  have e1 : (fun x => deriv (fun x' => c * g (x', r.2)) x) = fun x => c * deriv (fun x' => g (x', r.2)) x :=
    funext fun x => deriv_const_mul c (diffAt_x hg r.2 x)
  have e2 : (fun y => deriv (fun y' => c * g (r.1, y')) y) = fun y => c * deriv (fun y' => g (r.1, y')) y :=
    funext fun y => deriv_const_mul c (diffAt_y hg r.1 y)
  rw [e1, e2, deriv_const_mul c (diffAt_xx hg r.2 r.1), deriv_const_mul c (diffAt_yy hg r.1 r.2)]
  ring

theorem lap_sum4 (C : ZMod T.Nφ → ZMod T.Nφ → ZMod T.Nφ → ZMod T.Nφ → ℂ) (g : ZMod T.Nφ → ZMod T.Nφ → ℝ × ℝ → ℂ)
    (hg : ∀ a c, ContDiff ℝ ∞ (g a c)) (r : ℝ × ℝ) :
    lap (fun r' => ∑ a, ∑ b, ∑ c, ∑ d, C a b c d * g a c r') r =
      ∑ a, ∑ b, ∑ c, ∑ d, C a b c d * lap (g a c) r := by
  rw [lap_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [lap_sum]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [lap_sum]
      · refine Finset.sum_congr rfl fun c _ => ?_
        rw [lap_sum]
        · exact Finset.sum_congr rfl fun d _ => lap_const_mul _ (hg a c) r
        · exact fun d => contDiff_const.mul (hg a c)
      · exact fun c => ContDiff.sum fun d _ => contDiff_const.mul (hg a c)
    · exact fun b => ContDiff.sum fun c _ => ContDiff.sum fun d _ => contDiff_const.mul (hg a c)
  · exact fun a => ContDiff.sum fun b _ => ContDiff.sum fun c _ => ContDiff.sum fun d _ => contDiff_const.mul (hg a c)

theorem pairDensity_contDiff (a c : ZMod T.Nφ) : ContDiff ℝ ∞ (pairDensity T a c) :=
  (contDiff_star' (psi_contDiff T a)).mul (psi_contDiff T c)

theorem lap_continuous {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) : Continuous (lap g) :=
  ((contDiff_px (contDiff_px hg)).add (contDiff_py (contDiff_py hg))).continuous

/-! #### Proof devices: Step 2, the form of `H_N` through `|Υ|²` -/

theorem ups_normSq (u : PairAmp T) (σ σ' : Spin) (r₁ r₂ : ℝ × ℝ) :
    star (ups T u σ σ' (r₁, r₂)) * ups T u σ σ' (r₁, r₂) =
      ∑ a, ∑ b, ∑ c, ∑ d, (star (u (a, σ) (b, σ')) * u (c, σ) (d, σ')) *
        (pairDensity T a c r₁ * pairDensity T b d r₂) := by
  simp only [ups, opf, star_sum, Finset.sum_mul, Finset.mul_sum]
  refine (sum4_swap _).trans (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_)
  simp only [pairDensity, star_mul']
  ring

theorem ups_lap (u : PairAmp T) (σ σ' : Spin) (r : ℝ × ℝ) :
    lap (fun r₁ => star (ups T u σ σ' (r₁, r)) * ups T u σ σ' (r₁, r)) r =
      ∑ a, ∑ b, ∑ c, ∑ d, (star (u (a, σ) (b, σ')) * u (c, σ) (d, σ')) *
        (pairDensity T b d r * lap (pairDensity T a c) r) := by
  have e : (fun r₁ => star (ups T u σ σ' (r₁, r)) * ups T u σ σ' (r₁, r)) = fun r₁ =>
      ∑ a, ∑ b, ∑ c, ∑ d, ((star (u (a, σ) (b, σ')) * u (c, σ) (d, σ')) * pairDensity T b d r) *
        pairDensity T a c r₁ := by
    funext r₁
    rw [ups_normSq]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [e, lap_sum4 T _ (fun a c => pairDensity T a c) (pairDensity_contDiff T)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  ring

theorem integrable_of_continuous {g : ℝ × ℝ → ℂ} (hg : Continuous g) :
    Integrable g (volume.restrict (fundDom T)) := by
  have h := integrableOn_inter_fundDom hg T Set.univ
  rw [Set.univ_inter] at h
  exact h

theorem VK_eq (u : PairAmp T) (σ σ' : Spin) (a b c d : ZMod T.Nφ) :
    Vcoef T a b c d * (star (u (a, σ) (b, σ')) * u (c, σ) (d, σ')) =
      (4 * π : ℂ) * ∫ r in fundDom T, (star (u (a, σ) (b, σ')) * u (c, σ) (d, σ')) *
        (pairDensity T a c r * pairDensity T b d r + pairDensity T b d r * lap (pairDensity T a c) r) := by
  have h1 : Continuous fun r => pairDensity T a c r * pairDensity T b d r :=
    (pairDensity_contDiff T a c).continuous.mul (pairDensity_contDiff T b d).continuous
  have h2 : Continuous fun r => pairDensity T b d r * lap (pairDensity T a c) r :=
    (pairDensity_contDiff T b d).continuous.mul (lap_continuous (pairDensity_contDiff T a c))
  rw [integral_const_mul, integral_add (integrable_of_continuous T h1) (integrable_of_continuous T h2)]
  simp only [Vcoef, torusIntegral]
  ring

theorem TI_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ × ℝ → ℂ) (hF : ∀ i, Continuous (F i)) :
    ∫ r in fundDom T, ∑ i ∈ s, F i r = ∑ i ∈ s, ∫ r in fundDom T, F i r :=
  integral_finsetSum _ fun i _ => integrable_of_continuous T (hF i)

theorem cont_term (u : PairAmp T) (σ σ' : Spin) (a b c d : ZMod T.Nφ) :
    Continuous fun r => (star (u (a, σ) (b, σ')) * u (c, σ) (d, σ')) *
      (pairDensity T a c r * pairDensity T b d r + pairDensity T b d r * lap (pairDensity T a c) r) :=
  continuous_const.mul (((pairDensity_contDiff T a c).continuous.mul (pairDensity_contDiff T b d).continuous).add
    ((pairDensity_contDiff T b d).continuous.mul (lap_continuous (pairDensity_contDiff T a c))))

/-- Step 2: `⟨H_N⟩ = 2π ∫ Σ_{σσ'} [|Υ_{σσ'}|²(r,r) + (∇₁²|Υ_{σσ'}|²)(r,r)] dr` (with `u` for `√2 υ`) -/
theorem formHN_eq (u : PairAmp T) :
    formHN T u u = (2 * π : ℂ) * ∫ r in fundDom T, ∑ σ : Spin, ∑ σ' : Spin,
      (star (ups T u σ σ' (r, r)) * ups T u σ σ' (r, r) +
        lap (fun r₁ => star (ups T u σ σ' (r₁, r)) * ups T u σ σ' (r₁, r)) r) := by
  have hpt : ∀ r : ℝ × ℝ, ∑ σ : Spin, ∑ σ' : Spin,
      (star (ups T u σ σ' (r, r)) * ups T u σ σ' (r, r) +
        lap (fun r₁ => star (ups T u σ σ' (r₁, r)) * ups T u σ σ' (r₁, r)) r) =
      ∑ σ : Spin, ∑ σ' : Spin, ∑ a, ∑ b, ∑ c, ∑ d, (star (u (a, σ) (b, σ')) * u (c, σ) (d, σ')) *
        (pairDensity T a c r * pairDensity T b d r + pairDensity T b d r * lap (pairDensity T a c) r) := by
    intro r
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
    rw [ups_normSq, ups_lap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  simp_rw [hpt]
  rw [TI_sum T _ _ (fun σ => continuous_finsetSum _ fun σ' _ => continuous_finsetSum _ fun a _ =>
    continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ =>
      cont_term T u σ σ' a b c d)]
  simp only [formHN, VK_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [TI_sum T _ _ (fun σ' => continuous_finsetSum _ fun a _ =>
    continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ =>
      cont_term T u σ σ' a b c d), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  rw [TI_sum T _ _ (fun a => continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ =>
    continuous_finsetSum _ fun d _ => cont_term T u σ σ' a b c d), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [TI_sum T _ _ (fun b => continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ =>
    cont_term T u σ σ' a b c d), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [TI_sum T _ _ (fun c => continuous_finsetSum _ fun d _ => cont_term T u σ σ' a b c d), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [TI_sum T _ _ (fun d => cont_term T u σ σ' a b c d), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-! #### Proof devices: Step 3, relative coordinates -/

theorem line2 {N : (ℝ × ℝ) × (ℝ × ℝ) → ℂ} (hN : ContDiff ℝ ∞ N) (p v : (ℝ × ℝ) × (ℝ × ℝ)) :
    deriv (deriv (fun s : ℝ => N (p + s • v))) 0 = fderiv ℝ (fderiv ℝ N) p v v := by
  have e : deriv (fun s : ℝ => N (p + s • v)) = fun s => fderiv ℝ N (p + s • v) v := by
    funext s
    exact (((hN.differentiable (by simp)) (p + s • v)).hasFDerivAt.comp_hasDerivAt s
      (jets_hasDerivAt_line p v s)).deriv
  rw [e]
  have h := (jets_hasDerivAt_fderiv isOpen_univ hN.contDiffOn (Set.mem_univ p) v v).deriv
  exact h

theorem deriv2_shift (φ : ℝ → ℂ) (a : ℝ) :
    deriv (fun x => deriv (fun x' => φ (x' - a)) x) a = deriv (deriv φ) 0 := by
  have e : (fun x => deriv (fun x' => φ (x' - a)) x) = fun x => deriv φ (x - a) :=
    funext fun x => deriv_comp_sub_const φ a x
  rw [e, deriv_comp_sub_const (deriv φ) a a, sub_self]

theorem restr {N : (ℝ × ℝ) × (ℝ × ℝ) → ℂ} (hN : ContDiff ℝ ∞ N) (p v : (ℝ × ℝ) × (ℝ × ℝ)) (a : ℝ)
    (g : ℝ → ℂ) (hg : ∀ x, g x = N (p + (x - a) • v)) :
    deriv (fun x => deriv g x) a = fderiv ℝ (fderiv ℝ N) p v v := by
  have e : g = fun x => N (p + (x - a) • v) := funext hg
  subst e
  exact (deriv2_shift (fun s => N (p + s • v)) a).trans (line2 hN p v)

theorem step3 {N : (ℝ × ℝ) × (ℝ × ℝ) → ℂ} (hN : ContDiff ℝ ∞ N) (hsym : ∀ r₁ r₂, N (r₁, r₂) = N (r₂, r₁))
    (R : ℝ × ℝ) :
    lap (fun r₁ => N (r₁, R)) R =
      (1 / 4 : ℂ) * lap (fun R' => N (R', R')) R +
        lap (fun ρ => N (R + (1 / 2 : ℝ) • ρ, R - (1 / 2 : ℝ) • ρ)) 0 := by
  set D := fderiv ℝ (fderiv ℝ N) (R, R) with hD
  set e1x : (ℝ × ℝ) × (ℝ × ℝ) := ((1, 0), (0, 0)) with he1x
  set e2x : (ℝ × ℝ) × (ℝ × ℝ) := ((0, 0), (1, 0)) with he2x
  set e1y : (ℝ × ℝ) × (ℝ × ℝ) := ((0, 1), (0, 0)) with he1y
  set e2y : (ℝ × ℝ) × (ℝ × ℝ) := ((0, 0), (0, 1)) with he2y
  have h1x : deriv (fun x => deriv (fun x' => N ((x', R.2), R)) x) R.1 = D e1x e1x :=
    restr hN (R, R) e1x R.1 _ fun x => by
      rw [show (R, R) + (x - R.1) • e1x = ((x, R.2), R) by ext <;> simp [he1x]]
  have h1y : deriv (fun y => deriv (fun y' => N ((R.1, y'), R)) y) R.2 = D e1y e1y :=
    restr hN (R, R) e1y R.2 _ fun y => by
      rw [show (R, R) + (y - R.2) • e1y = ((R.1, y), R) by ext <;> simp [he1y]]
  have hdx : deriv (fun x => deriv (fun x' => N ((x', R.2), (x', R.2))) x) R.1 = D (e1x + e2x) (e1x + e2x) :=
    restr hN (R, R) (e1x + e2x) R.1 _ fun x => by
      rw [show (R, R) + (x - R.1) • (e1x + e2x) = ((x, R.2), (x, R.2)) by ext <;> simp [he1x, he2x]]
  have hdy : deriv (fun y => deriv (fun y' => N ((R.1, y'), (R.1, y'))) y) R.2 = D (e1y + e2y) (e1y + e2y) :=
    restr hN (R, R) (e1y + e2y) R.2 _ fun y => by
      rw [show (R, R) + (y - R.2) • (e1y + e2y) = ((R.1, y), (R.1, y)) by ext <;> simp [he1y, he2y]]
  have hjx : deriv (fun x => deriv (fun x' => N (R + (1 / 2 : ℝ) • (x', (0 : ℝ)), R - (1 / 2 : ℝ) • (x', (0 : ℝ))))
      x) 0 = D ((1 / 2 : ℝ) • e1x - (1 / 2 : ℝ) • e2x) ((1 / 2 : ℝ) • e1x - (1 / 2 : ℝ) • e2x) :=
    restr hN (R, R) ((1 / 2 : ℝ) • e1x - (1 / 2 : ℝ) • e2x) 0 _ fun x => by
      rw [show (R, R) + (x - 0) • ((1 / 2 : ℝ) • e1x - (1 / 2 : ℝ) • e2x) =
        (R + (1 / 2 : ℝ) • (x, (0 : ℝ)), R - (1 / 2 : ℝ) • (x, (0 : ℝ))) by
          ext <;> simp [he1x, he2x] <;> ring]
  have hjy : deriv (fun y => deriv (fun y' => N (R + (1 / 2 : ℝ) • ((0 : ℝ), y'), R - (1 / 2 : ℝ) • ((0 : ℝ), y')))
      y) 0 = D ((1 / 2 : ℝ) • e1y - (1 / 2 : ℝ) • e2y) ((1 / 2 : ℝ) • e1y - (1 / 2 : ℝ) • e2y) :=
    restr hN (R, R) ((1 / 2 : ℝ) • e1y - (1 / 2 : ℝ) • e2y) 0 _ fun y => by
      rw [show (R, R) + (y - 0) • ((1 / 2 : ℝ) • e1y - (1 / 2 : ℝ) • e2y) =
        (R + (1 / 2 : ℝ) • ((0 : ℝ), y), R - (1 / 2 : ℝ) • ((0 : ℝ), y)) by
          ext <;> simp [he1y, he2y] <;> ring]
  have hsx : D e2x e2x = D e1x e1x := by
    have hs : (fun s : ℝ => N ((R, R) + s • e2x)) = fun s => N ((R, R) + s • e1x) := by
      funext s
      rw [show (R, R) + s • e2x = (R, R + s • ((1 : ℝ), (0 : ℝ))) by ext <;> simp [he2x],
        show (R, R) + s • e1x = (R + s • ((1 : ℝ), (0 : ℝ)), R) by ext <;> simp [he1x], hsym]
    exact (line2 hN (R, R) e2x).symm.trans ((congrArg (fun F => deriv (deriv F) 0) hs).trans
      (line2 hN (R, R) e1x))
  have hsy : D e2y e2y = D e1y e1y := by
    have hs : (fun s : ℝ => N ((R, R) + s • e2y)) = fun s => N ((R, R) + s • e1y) := by
      funext s
      rw [show (R, R) + s • e2y = (R, R + s • ((0 : ℝ), (1 : ℝ))) by ext <;> simp [he2y],
        show (R, R) + s • e1y = (R + s • ((0 : ℝ), (1 : ℝ)), R) by ext <;> simp [he1y], hsym]
    exact (line2 hN (R, R) e2y).symm.trans ((congrArg (fun F => deriv (deriv F) 0) hs).trans
      (line2 hN (R, R) e1y))
  simp only [lap, Prod.fst_zero, Prod.snd_zero]
  rw [h1x, h1y, hdx, hdy, hjx, hjy]
  simp only [map_add, map_sub, map_smul, add_apply, sub_apply,
    smul_apply, Complex.real_smul]
  rw [hsx, hsy]
  push_cast
  ring

/-! #### Proof devices: the diagonal, the jets, and the assembly -/

theorem starmul_eq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_pow]
  exact Complex.conj_mul' z

theorem deriv_ofReal (g : ℝ → ℝ) (x : ℝ) : deriv (fun t => (g t : ℂ)) x = ((deriv g x : ℝ) : ℂ) := by
  by_cases hg : DifferentiableAt ℝ g x
  · exact hg.hasDerivAt.ofReal_comp.deriv
  · have hn : ¬ DifferentiableAt ℝ (fun t => (g t : ℂ)) x := fun h => hg (by
      have h2 := Complex.reCLM.differentiableAt.comp x h
      simpa [Function.comp_def] using h2)
    rw [deriv_zero_of_not_differentiableAt hn, deriv_zero_of_not_differentiableAt hg, Complex.ofReal_zero]

theorem lap_ofReal (h : ℝ × ℝ → ℝ) (r : ℝ × ℝ) : lap (fun r' => (h r' : ℂ)) r = ((lapR h r : ℝ) : ℂ) := by
  simp only [lap, lapR, deriv_ofReal, Complex.ofReal_add]

theorem N_contDiff (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) :
    ContDiff ℝ ∞ (fun p => star (opf T w p) * opf T w p) := by
  have h := opf_contDiff T w
  have hs : ContDiff ℝ ∞ (fun p => star (opf T w p)) := by
    have e : (fun p => star (opf T w p)) = fun p => Complex.conjCLE (opf T w p) := by
      funext p
      simp
    rw [e]
    exact Complex.conjCLE.contDiff.comp h
  exact hs.mul h

theorem slice_contDiff (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (r : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun r' => star (opf T w (r', r)) * opf T w (r', r)) :=
  (N_contDiff T w).comp (contDiff_id.prodMk contDiff_const)

theorem diag_contDiff (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) :
    ContDiff ℝ ∞ (fun R => star (opf T w (R, R)) * opf T w (R, R)) :=
  (N_contDiff T w).comp (contDiff_id.prodMk contDiff_id)

theorem opf_diag_add_Lx (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (x y : ℝ) :
    opf T w ((x + T.Lx, y), (x + T.Lx, y)) =
      (Complex.exp (I * (T.Lx : ℂ) * (y : ℂ)) * Complex.exp (I * (T.Lx : ℂ) * (y : ℂ))) * opf T w ((x, y), (x, y)) := by
  simp only [opf, psi_add_Lx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  ring

theorem opf_diag_add_Ly (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (x y : ℝ) :
    opf T w ((x, y + T.Ly), (x, y + T.Ly)) = opf T w ((x, y), (x, y)) := by
  simp only [opf, psi_add_Ly]

theorem diag_px (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (x y : ℝ) :
    (fun R => star (opf T w (R, R)) * opf T w (R, R)) (x + T.Lx, y) =
      (fun R => star (opf T w (R, R)) * opf T w (R, R)) (x, y) := by
  simp only []
  rw [opf_diag_add_Lx]
  have h := phase_star_mul_self (z := I * (T.Lx : ℂ) * (y : ℂ)) (by simp)
  simp only [star_mul']
  linear_combination (star (opf T w ((x, y), (x, y))) * opf T w ((x, y), (x, y))) *
    (star (Complex.exp (I * ↑T.Lx * ↑y)) * Complex.exp (I * ↑T.Lx * ↑y) + 1) * h

theorem diag_py (w : ZMod T.Nφ → ZMod T.Nφ → ℂ) (x y : ℝ) :
    (fun R => star (opf T w (R, R)) * opf T w (R, R)) (x, y + T.Ly) =
      (fun R => star (opf T w (R, R)) * opf T w (R, R)) (x, y) := by
  simp only []
  rw [opf_diag_add_Ly]

theorem integral_lap_eq_zero {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hx : ∀ x y, g (x + T.Lx, y) = g (x, y))
    (hy : ∀ x y, g (x, y + T.Ly) = g (x, y)) : ∫ r in fundDom T, lap g r = 0 := by
  have h := rectFT_lap T.Lx_pos T.Ly_pos hg hx hy (0, 0)
  simpa [rectFT, lap, fundDom] using h

theorem N_symm (u : PairAmp T) (hu : ∀ μ μ' : Modes T, u μ' μ = -u μ μ') (o : Option Triplet) (r₁ r₂ : ℝ × ℝ) :
    star (opf T (wOf T u o) (r₁, r₂)) * opf T (wOf T u o) (r₁, r₂) =
      star (opf T (wOf T u o) (r₂, r₁)) * opf T (wOf T u o) (r₂, r₁) := by
  cases o with
  | none => rw [opf_eq_swap T _ (wOf_symm T u hu) r₁ r₂]
  | some ν =>
      rw [opf_neg_swap T _ (wOf_anti T u hu ν) r₁ r₂, star_neg]
      ring

theorem per_o (u : PairAmp T) (hu : ∀ μ μ' : Modes T, u μ' μ = -u μ μ') (o : Option Triplet) (r : ℝ × ℝ) :
    star (opf T (wOf T u o) (r, r)) * opf T (wOf T u o) (r, r) +
        lap (fun r₁ => star (opf T (wOf T u o) (r₁, r)) * opf T (wOf T u o) (r₁, r)) r =
      ((jetF (opf T (wOf T u o)) r 0 + lapR (jetF (opf T (wOf T u o)) r) 0 : ℝ) : ℂ) +
        (1 / 4 : ℂ) * lap (fun R' => star (opf T (wOf T u o) (R', R')) * opf T (wOf T u o) (R', R')) r := by
  have h3 := step3 (N_contDiff T (wOf T u o)) (fun r₁ r₂ => N_symm T u hu o r₁ r₂) r
  have hj0 : star (opf T (wOf T u o) (r, r)) * opf T (wOf T u o) (r, r) =
      ((jetF (opf T (wOf T u o)) r 0 : ℝ) : ℂ) := by
    simp only [jetF, smul_zero, add_zero, sub_zero]
    rw [starmul_eq]
  have hjl : lap (fun ρ => star (opf T (wOf T u o) (r + (1 / 2 : ℝ) • ρ, r - (1 / 2 : ℝ) • ρ)) *
      opf T (wOf T u o) (r + (1 / 2 : ℝ) • ρ, r - (1 / 2 : ℝ) • ρ)) 0 =
      ((lapR (jetF (opf T (wOf T u o)) r) 0 : ℝ) : ℂ) := by
    rw [show (fun ρ => star (opf T (wOf T u o) (r + (1 / 2 : ℝ) • ρ, r - (1 / 2 : ℝ) • ρ)) *
        opf T (wOf T u o) (r + (1 / 2 : ℝ) • ρ, r - (1 / 2 : ℝ) • ρ)) =
        fun ρ => ((jetF (opf T (wOf T u o)) r ρ : ℝ) : ℂ) from funext fun ρ => by
          simp only [jetF]
          rw [starmul_eq]]
    exact lap_ofReal _ _
  rw [h3, hj0, hjl]
  push_cast
  ring

theorem integrand_eq (u : PairAmp T) (hu : ∀ μ μ' : Modes T, u μ' μ = -u μ μ') (r : ℝ × ℝ) :
    ∑ σ : Spin, ∑ σ' : Spin, (star (ups T u σ σ' (r, r)) * ups T u σ σ' (r, r) +
        lap (fun r₁ => star (ups T u σ σ' (r₁, r)) * ups T u σ σ' (r₁, r)) r) =
      ∑ ν : Triplet, 4 * (star (tripletAmp T ν r u) * tripletAmp T ν r u) +
        (1 / 4 : ℂ) * ∑ o : Option Triplet,
          lap (fun R' => star (opf T (wOf T u o) (R', R')) * opf T (wOf T u o) (R', R')) r := by
  have hc : ∑ σ : Spin, ∑ σ' : Spin, lap (fun r₁ => star (ups T u σ σ' (r₁, r)) * ups T u σ σ' (r₁, r)) r =
      ∑ o : Option Triplet, lap (fun r₁ => star (opf T (wOf T u o) (r₁, r)) * opf T (wOf T u o) (r₁, r)) r := by
    rw [← lap_sum _ _ (fun o => slice_contDiff T (wOf T u o) r)]
    rw [show (fun r' => ∑ o : Option Triplet, star (opf T (wOf T u o) (r', r)) * opf T (wOf T u o) (r', r)) =
      fun r' => ∑ σ : Spin, ∑ σ' : Spin, star (ups T u σ σ' (r', r)) * ups T u σ σ' (r', r) from
        funext fun r' => (spin_decomp T u (r', r)).symm]
    rw [lap_sum Finset.univ (fun σ r' => ∑ σ' : Spin, star (ups T u σ σ' (r', r)) * ups T u σ σ' (r', r))
      (fun σ => ContDiff.sum fun σ' _ => slice_contDiff T (fun j j' => u (j, σ) (j', σ')) r) r]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lap_sum Finset.univ (fun σ' r' => star (ups T u σ σ' (r', r)) * ups T u σ σ' (r', r))
      (fun σ' => slice_contDiff T (fun j j' => u (j, σ) (j', σ')) r) r]
  simp only [Finset.sum_add_distrib]
  rw [spin_decomp T u (r, r), hc, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun o _ => per_o T u hu o r, Finset.sum_add_distrib, Fintype.sum_option,
    ← Finset.mul_sum, jets_comp_sing T u hu r, Complex.ofReal_zero, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  obtain ⟨h0, h1⟩ := jets_comp_triplet T u hu ν r
  rw [h0, h1, D1_comp, zero_add, starmul_eq]
  push_cast
  ring

/-- **The scalar identity**: `PairFormIdentity` holds. -/
theorem pairFormIdentity : PairFormIdentity T := by
  intro u hu
  rw [formHN_eq]
  simp_rw [integrand_eq T u hu]
  have hA : Continuous fun r => ∑ ν : Triplet, 4 * (star (tripletAmp T ν r u) * tripletAmp T ν r u) :=
    continuous_finsetSum _ fun ν _ => continuous_const.mul
      ((tripletAmp_continuous T ν u).star.mul (tripletAmp_continuous T ν u))
  have hB : Continuous fun r => (1 / 4 : ℂ) * ∑ o : Option Triplet,
      lap (fun R' => star (opf T (wOf T u o) (R', R')) * opf T (wOf T u o) (R', R')) r :=
    continuous_const.mul (continuous_finsetSum _ fun o _ => lap_continuous (diag_contDiff T _))
  rw [integral_add (integrable_of_continuous T hA) (integrable_of_continuous T hB)]
  have hB0 : ∫ r in fundDom T, (1 / 4 : ℂ) * ∑ o : Option Triplet,
      lap (fun R' => star (opf T (wOf T u o) (R', R')) * opf T (wOf T u o) (R', R')) r = 0 := by
    rw [integral_const_mul, TI_sum T _ _ (fun o => lap_continuous (diag_contDiff T _)),
      Finset.sum_eq_zero fun o _ => integral_lap_eq_zero T (diag_contDiff T _) (diag_px T _) (diag_py T _),
      mul_zero]
  rw [hB0, add_zero, TI_sum T Finset.univ (fun ν r => 4 * (star (tripletAmp T ν r u) * tripletAmp T ν r u))
    (fun ν => continuous_const.mul ((tripletAmp_continuous T ν u).star.mul (tripletAmp_continuous T ν u)))]
  simp only [formLocal, integral_const_mul]
  rw [← Finset.mul_sum]
  push_cast
  ring

end PairForm

/-! ## Theorem 4.2 -/

/-- **Theorem 4.2(a)**: "`For every torus as in Definition~\ref{def:torus}:`"
"`$H_N=8\pi\int_{\Tor_N}\sum_\nu B_\nu(R)^*B_\nu(R)\,\dd R=\int_{\Tor_N}h_R\,\dd R$, as operators on $\Fock$.`" -/
theorem localForm_a (T : Torus) :
    HN T = ((8 * π : ℝ) : ℂ) • opIntegral (fundDom T) (fun R => ∑ ν : Triplet, (Bν T ν R)ᴴ * Bν T ν R) ∧
      HN T = opIntegral (fundDom T) (hR T) := by
  -- block C's proof (L9): the reduction `localForm_a_of_pairFormIdentity` (in place of the paper's Step 6) and the
  -- scalar identity `PairForm.pairFormIdentity` (Steps 1–5)
  exact localForm_a_of_pairFormIdentity T (PairForm.pairFormIdentity T)

/-- **Theorem 4.2(b)**: "`For $R=(R_x,R_y)\in\R^2$,`"
"`B_\nu(R)=\frac{\kappa}{2L_y\sqrt\pi}\sum_{n\in\Z}e^{\iu\kappa nR_y}e^{-(R_x-\kappa n/2)^2}\,\bcen\nu n .`" -/
theorem localForm_b (T : Torus) (ν : Triplet) (R : ℝ × ℝ) :
    HasSum (fun n : ℤ => (((T.κ / (2 * T.Ly * Real.sqrt π) : ℝ) : ℂ) *
        (Complex.exp (I * (T.κ : ℂ) * (n : ℂ) * (R.2 : ℂ)) *
          ((Real.exp (-(R.1 - T.κ * (n : ℝ) / 2) ^ 2) : ℝ) : ℂ))) • bcen T ν n) (Bν T ν R) := by
  -- entrywise, by `localForm_b_scalar` with the antisymmetric coefficients `c_ν(ψ_j, ψ_{j'})_{mm'}`
  refine Pi.hasSum.mpr fun m => Pi.hasSum.mpr fun m' => ?_
  have key := localForm_b_scalar T R (fun j j' => cpair T ν (orb T j) (orb T j') m m') (fun j j' => by
    show cpair T ν (orb T j') (orb T j) m m' = -cpair T ν (orb T j) (orb T j') m m'
    rw [cpair_swap]
    rfl)
  convert key using 1
  · funext n
    have hs := (summable_bcenTerm T ν n).2
    have hb : (bcen T ν n) m m' = ∑' d, bcenTerm T ν n d m m' :=
      ((Pi.hasSum.mp (Pi.hasSum.mp hs.hasSum m) m').tsum_eq).symm
    rw [Matrix.smul_apply, smul_eq_mul, hb]
    congr 1
    refine tsum_congr fun d => ?_
    unfold bcenTerm
    split_ifs <;> simp [Matrix.smul_apply]
  · rw [Bν_eq_sum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- Device: the computation of the proof of Theorem 4.2(c) from (b), without (a):
`∫_{𝕋_N} h_R dR = (κ³/√(2π)) Σ_{n ∈ ℤ_{2N_φ}} Σ_ν b_ν(n)^* b_ν(n)` ("`using $L_y=2\pi/\kappa$`"). -/
theorem opIntegral_hR_eq_bcen (T : Torus) :
    opIntegral (fundDom T) (hR T) = ((T.κ ^ 3 / Real.sqrt (2 * π) : ℝ) : ℂ) •
      ∑ n ∈ Finset.range (2 * T.Nφ), ∑ ν : Triplet, (bcen T ν (n : ℤ))ᴴ * bcen T ν (n : ℤ) := by
  -- entrywise, from Theorem 4.2(b) (`localForm_b`)
  have hconst : ((8 * π : ℝ) : ℂ) * (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * T.Ly * Real.sqrt (π / 2) : ℝ) : ℂ) =
      ((T.κ ^ 3 / Real.sqrt (2 * π) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    have hs0 : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    have ht0 : 0 < Real.sqrt 2 := by positivity
    have hLy0 : T.Ly ≠ 0 := T.Ly_pos.ne'
    have hκLy := T.κ_mul_Ly
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), eq_div_iff (by positivity)]
    have h1 : (T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * T.Ly * (Real.sqrt π / Real.sqrt 2) *
        (Real.sqrt 2 * Real.sqrt π) = T.κ ^ 2 / (4 * T.Ly) := by
      field_simp
      ring
    calc 8 * π * ((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * T.Ly * (Real.sqrt π / Real.sqrt 2)) *
          (Real.sqrt 2 * Real.sqrt π) = 8 * π * (T.κ ^ 2 / (4 * T.Ly)) := by rw [← h1]; ring
      _ = T.κ ^ 3 := by
          field_simp
          linear_combination (-4 * T.κ ^ 2) * hκLy
  have hBent : ∀ (ν : Triplet) (R : ℝ × ℝ) (k l : Conf (ZMod T.Nφ)),
      Bν T ν R k l = ∑' n : ℤ, Wb T R n * bcen T ν n k l := fun ν R k l =>
    (Pi.hasSum.mp (Pi.hasSum.mp (localForm_b T ν R) k) l).tsum_eq.symm
  have hint : ∀ (ν : Triplet) (k l l' : Conf (ZMod T.Nφ)),
      Integrable (fun R => star (Bν T ν R k l) * Bν T ν R k l') (volume.restrict (fundDom T)) := by
    intro ν k l l'
    have hc : Continuous (fun R => star (Bν T ν R k l) * Bν T ν R k l') :=
      ((Bν_contDiff T ν k l).continuous.star).mul (Bν_contDiff T ν k l').continuous
    have := integrableOn_inter_fundDom hc T Set.univ
    rwa [Set.univ_inter] at this
  have hνk : ∀ (ν : Triplet) (k l l' : Conf (ZMod T.Nφ)),
      ∫ R in fundDom T, star (Bν T ν R k l) * Bν T ν R k l' =
        (((T.κ / (2 * T.Ly * Real.sqrt π)) ^ 2 * T.Ly * Real.sqrt (π / 2) : ℝ) : ℂ) *
          ∑ n ∈ Finset.range (2 * T.Nφ), star (bcen T ν (n : ℤ) k l) * bcen T ν (n : ℤ) k l' := by
    intro ν k l l'
    have e : (fun R => star (Bν T ν R k l) * Bν T ν R k l') = fun R =>
        star (∑' n : ℤ, Wb T R n * bcen T ν n k l) * ∑' n : ℤ, Wb T R n * bcen T ν n k l' :=
      funext fun R => by rw [hBent ν R k l, hBent ν R k l']
    rw [e]
    have hper : ∀ (l'' : Conf (ZMod T.Nφ)) (n : ℤ),
        bcen T ν (n + ((2 * T.Nφ : ℕ) : ℤ)) k l'' = bcen T ν n k l'' := by
      intro l'' n
      rw [show (n + ((2 * T.Nφ : ℕ) : ℤ)) = n + 2 * (T.Nφ : ℤ) by push_cast; ring, bcen_add_two_Nφ]
    exact integral_star_tsum_Wb T _ _ (hper l) (hper l')
  have hhR : opIntegral (fundDom T) (hR T) =
      ((8 * π : ℝ) : ℂ) • opIntegral (fundDom T) (fun R => ∑ ν : Triplet, (Bν T ν R)ᴴ * Bν T ν R) := by
    ext m m'
    simp only [opIntegral, hR, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    exact integral_const_mul _ _
  rw [hhR]
  ext m m'
  simp only [Matrix.smul_apply, smul_eq_mul, opIntegral, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [integral_finsetSum _ (fun ν _ => integrable_finsetSum _ (fun k _ => hint ν k m m')),
    Finset.sum_congr rfl fun ν _ => integral_finsetSum _ fun k _ => hint ν k m m']
  simp_rw [hνk]
  rw [← hconst]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range (2 * T.Nφ))]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm (s := Finset.range (2 * T.Nφ))]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun n _ => by ring

/-- **Theorem 4.2(c)**: "`$H_N=\dfrac{\kappa^3}{\sqrt{2\pi}}\displaystyle\sum_{n\in\Z_{2\Nphi}}\sum_\nu(\bcen\nu n)^*\,\bcen\nu n$.`" -/
theorem localForm_c (T : Torus) :
    HN T = ((T.κ ^ 3 / Real.sqrt (2 * π) : ℝ) : ℂ) •
      ∑ n ∈ Finset.range (2 * T.Nφ), ∑ ν : Triplet, (bcen T ν (n : ℤ))ᴴ * bcen T ν (n : ℤ) := by
  -- from (a) (`localForm_a`) and the computation `opIntegral_hR_eq_bcen` from (b), as in the paper
  rw [(localForm_a T).2, opIntegral_hR_eq_bcen]

/-! ## The consequences for `H_N` -/

/-- The proof of **Lemma 4.5**: "`For $\mathcal D=\Tor_N$, Theorem~\ref{thm:localform}(a) gives $\Theta^*H_N\Theta=H_N$`" —
`H_{𝕋_N} = H_N` (`𝕋_N` is all of `ℝ²` as a periodic set). -/
theorem HD_univ (T : Torus) : HD T Set.univ = HN T := by
  -- from Theorem 4.2(a) (`localForm_a`), as in the paper
  rw [HD, Set.univ_inter, ← (localForm_a T).2]

/-- **Lemma 4.5**: "`in particular $[\Theta,H_N]=0$`" — by Lemma 4.5's route ("`and since $\Theta$ is unitary, $[\Theta,H_N]=0$`");
the same statement as block A's `HRTorus.Fock.HN_commute_Θ`. -/
theorem commute_Θ_HN (T : Torus) : Commute (Θ T) (HN T) := by
  -- Lemma 4.5 for `𝒟 = 𝕋_N` and `HD_univ` (so from Theorem 4.2(a)), and `Θ` unitary
  have hU := Θ_mem_unitary T
  have huniv : IsTorusSet T Set.univ := ⟨MeasurableSet.univ, fun _ => by simp, fun _ => by simp⟩
  have h := Θ_conj_HD T huniv
  rw [Set.vadd_set_univ, HD_univ] at h
  have h1 : Θ T * (Θ T)ᴴ = 1 := mul_conjTranspose_self_of_mem_unitary hU
  show Θ T * HN T = HN T * Θ T
  calc Θ T * HN T = Θ T * ((Θ T)ᴴ * HN T * Θ T) := by rw [h]
    _ = Θ T * (Θ T)ᴴ * HN T * Θ T := by simp only [Matrix.mul_assoc]
    _ = HN T * Θ T := by rw [h1, Matrix.one_mul]

/-! ### Proof devices for `H_N ≥ 0` (phase (b); not statements of the paper) -/

/-- Device: the entrywise integral of positive semidefinite operators with integrable entries is positive
semidefinite. -/
theorem opIntegral_posSemidef {S : Type*} [Fintype S] [DecidableEq S] (D : Set (ℝ × ℝ)) (h : ℝ × ℝ → Op S)
    (hint : ∀ m m' : Conf S, IntegrableOn (fun R => h R m m') D) (hpsd : ∀ R, (h R).PosSemidef) :
    (opIntegral D h).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · show (opIntegral D h)ᴴ = opIntegral D h
    ext m m'
    rw [Matrix.conjTranspose_apply]
    simp only [opIntegral, Matrix.of_apply]
    have hc : ∀ R, (starRingEnd ℂ) (h R m' m) = h R m m' := fun R => (hpsd R).1.apply m m'
    rw [Complex.star_def, ← integral_conj]
    simp_rw [hc]
  · intro x
    have e : star x ⬝ᵥ (opIntegral D h *ᵥ x) = ∫ R in D, star x ⬝ᵥ (h R *ᵥ x) := by
      simp only [dotProduct, Matrix.mulVec, opIntegral, Matrix.of_apply, Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j _ => ((hint i j).mul_const _).const_mul _))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => ((hint i j).mul_const _).const_mul _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_mul_const]
    have hq : ∀ R, 0 ≤ star x ⬝ᵥ (h R *ᵥ x) := fun R => (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hpsd R)).2 x
    have hq' : ∀ R, star x ⬝ᵥ (h R *ᵥ x) = (((star x ⬝ᵥ (h R *ᵥ x)).re : ℝ) : ℂ) := fun R =>
      Complex.ext (by simp) (by simp [← (Complex.nonneg_iff.mp (hq R)).2])
    rw [e, show (fun R => star x ⬝ᵥ (h R *ᵥ x)) = fun R => (((star x ⬝ᵥ (h R *ᵥ x)).re : ℝ) : ℂ) from
      funext hq', integral_complex_ofReal]
    exact Complex.zero_le_real.mpr (integral_nonneg fun R => (Complex.nonneg_iff.mp (hq R)).1)

/-- Device: `h_R ≥ 0`, since `h_R = 8π Σ_ν B_ν(R)^* B_ν(R)` (Definition 4.1). -/
theorem hR_posSemidef (T : Torus) (R : ℝ × ℝ) : (hR T R).PosSemidef := by
  unfold hR
  exact (Matrix.posSemidef_sum _ fun ν _ => Matrix.posSemidef_conjTranspose_mul_self _).smul
    (Complex.zero_le_real.mpr (by positivity))

end HRTorus.Hamiltonian

/-! ## `H_N ≥ 0`, moved here from block A's `Fock.Hamiltonian` (review L9a, ruling 1)

Block A's statement, its docstring and header verbatim, in its own namespace and with its section variable `T`, so that
its name `HRTorus.Fock.HN_posSemidef` is unchanged; the paper derives it from Theorem 4.2(a) (`localForm_a`), which
`Fock.Hamiltonian` cannot import. -/

namespace HRTorus.Fock

open HRTorus.SlotFrame

variable (T : Torus)

/-- **§2.4**: "`in particular $H_N\ge0$`" (the paper derives it from Theorem 4.2(a), §4). -/
theorem HN_posSemidef : (HN T).PosSemidef := by
  -- block C's proof (L9): from Theorem 4.2(a) (`localForm_a`), `h_R ≥ 0` and the positivity of the integral
  rw [(HRTorus.Hamiltonian.localForm_a T).2]
  refine HRTorus.Hamiltonian.opIntegral_posSemidef _ _ (fun m m' => ?_) (HRTorus.Hamiltonian.hR_posSemidef T)
  have := HRTorus.Hamiltonian.integrableOn_inter_fundDom (HRTorus.Hamiltonian.hR_contDiff T m m').continuous T
    Set.univ
  rwa [Set.univ_inter] at this

end HRTorus.Fock
