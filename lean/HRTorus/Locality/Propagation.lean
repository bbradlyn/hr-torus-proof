import HRTorus.Locality.LiebRobinson
import HRTorus.Hamiltonian.SlotLocal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Propagation from a set and of almost-supported operators (T-0056 block D, `Locality.Propagation`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **Proof phase, rounds one and two (recruit L10, 2026-10-24/25):
every theorem is proved on the standard axioms; there is no `sorry` in this module. Theorem 5.3(a) `propagation_master`
in round two, by the paper's Steps 0–4 with one change in Step 4 (the paper's exact integral over the plane is replaced
by a bound through shells of width `λ`, inside the paper's constant), the disc measure of the torus through Mathlib's
`Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls`; Theorem 5.3(b) `propagation_lightCone`, Theorem 5.3(c)
`propagation_polynomial` and Lemma 5.5 `setNorm_dyn_le` in round one, from the statement of (a), as the paper derives
them. The proofs add devices, each marked as a device.** The paper: the HR paper,
`papers/hr/sections/05-locality.tex` — the opening paragraph of §5 (the standing assumption, `Ĥ_N`, `τ_t`, the
convention on constants), Theorem 5.3 `thm:propagation` with the claims of Step 0 of its proof (the canonical
approximants `h̃_{R,r}`, which the proof of Lemma 5.7 reuses), and Lemma 5.5 `lem:almostinputs`. Remark 5.4
`rem:propagation` is prose and is not stated; "We fix the light-cone exponent `α := 4`" is a convention of the later
proofs.

## The model

* **The standing assumption** "`$(\Tor_N)_{N\in\mathcal N}$ are admissible tori and $H=(H_N)$ satisfies (H1)`" is a block B
  `Ts : TorusSeq δ₀` and block C (H1) data `d : H1Data η δ₀ Ts H`, with `IsProfile η` and `0 < δ₀` for the embedding.
  `Ĥ_N := ι(H_N)` is `Hhat η δ₀ Ts H N`; `τ_t` on `𝔉_𝒮` is `dyn (Hhat …) t`, on `𝔉` it is `dyn (H N) t` (the module
  `LiebRobinson`).
* **The constants.** Where the paper fixes them, they are definitions in the paper's form: `c_k` (`ck`), `r_j` (`rj`),
  `C_1` (`C1`, a `tsum`, with its summability and the paper's bound as theorems), `C_lc(β)` (`ClcBeta`), the order
  `k = 2 + ⌈(k'+3)/β⌉` (`kLc`) and `C_{k',β}` (`CkBeta`), each a function of the values `C_h = d.Ch`, `C^H_k = d.CH k` and
  `C_vol = Cvol δ₀` it uses — so the dependence on finitely many `C^H_k` is visible in the arguments. Where the paper
  says "there are `C_lc` and `C_k` depending only on …" (Theorem 5.3(c), Lemma 5.5), the constants are existential,
  quantified **after** `δ₀`, the orders and the values `C_h`, `C^H = (C^H_k)_k` they may depend on and **before** the
  profile, the torus sequence, the Hamiltonian and its (H1) data (which are then required to have those `C_h`, `C^H`),
  `N` and the operators: they cannot depend on `N`.
* **Theorem 5.3(a) is stated existentially**: for every `N` and every dyadic `λ = 2^{j₀}` there is a family
  `Y ↦ Ĥ_{λ,Y}` of self-adjoint operators with `Ĥ_{λ,Y} ∈ Alg(Y)` — depending on `N`, `λ` and `Y` only, as in the
  paper — whose dynamics satisfies the master inequality and the parity clause for every `k ≥ 3`, `ρ > 0`, `X`,
  `A ∈ CAR(X)` and `t`. The construction (the dyadic decomposition of the canonical approximants) is the proof's,
  where the paper puts it ("`constructed in the proof`"); its Step 0 objects `h̃_{R,r} := 𝔼_{Ball(r,R)}(ι(h_R))` are
  definitions here (`hTilde`) because Lemma 5.7's proof uses them.
* **The infima** of Theorem 5.3(b)–(c) are real infima over the subtypes `CARpar (X^{(ρ)}) A` and `Alg(X^{(ρ)})` —
  nonempty (they contain `0`) and bounded below by `0` — as in the pilot's Lemma 5.1 and inside block B's set norm.
  "Of the parity of `A`" is `CARpar`: even if `A` is even, odd if `A` is odd.
* **Lemma 5.5** is stated in block B's set norm (`ℝ≥0∞`; the right side may be `⊤`).
-/

open scoped InnerProductSpace Matrix ENNReal Real
open Complex (I)

noncomputable section

namespace HRTorus.Locality

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op c chat parityOp IsEven CAR Alg condExp)

/-! ## The setting of §5 -/

section Setting

variable {η : ℝ → ℝ} {δ₀ : ℝ} {Ts : TorusSeq δ₀}

/-- §5: "`We write $\Hhat=\Hhat_N:=\iota(H_N)=\int\iota(h_R)\,\dd R$`". -/
abbrev Hhat (η : ℝ → ℝ) (δ₀ : ℝ) (Ts : TorusSeq δ₀) (H : (N : ℕ) → FockOp (Ts.T N)) (N : ℕ) :
    Op (Slot δ₀ (Ts.T N)) :=
  iota η δ₀ (Ts.T N) (H N)

/-- §5: "`By Lemma~\ref{lem:embedding}(ii), $\tau_t(\iota(A))=\iota(e^{\iu tH_N}Ae^{-\iu tH_N})$ for operators $A$ on $\Fock$`"
(for self-adjoint `H`, as block B's `iota_conj_exp`). -/
theorem dyn_iota {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀)
    {H : FockOp T} (hH : IsSelfAdjoint H) (A : FockOp T) (t : ℝ) :
    dyn (iota η δ₀ T H) t (iota η δ₀ T A) = iota η δ₀ T (dyn H t A) := by
  simp only [dyn]
  exact (iota_conj_exp hη hδ₀ hT hH A t).symm

variable {H : (N : ℕ) → FockOp (Ts.T N)}

/-! ### Proof devices for the setting (phase (b); not statements of the paper) -/

theorem integrableOn_h (d : H1Data η δ₀ Ts H) {N : ℕ} (hN : N ∈ Ts.idx) :
    ∀ m m' : Conf (ZMod (Ts.T N).Nφ), MeasureTheory.IntegrableOn (fun R => d.h N R m m') (fundDom (Ts.T N)) := by
  intro m m'
  refine MeasureTheory.Measure.integrableOn_of_bounded (volume_fundDom_ne_top (Ts.T N))
    (d.h_measurable N hN m m').aestronglyMeasurable (M := d.Ch) ?_
  exact Filter.Eventually.of_forall fun R => (norm_entry_le _ m m').trans (d.norm_h_le N hN R)

theorem isEven_H (d : H1Data η δ₀ Ts H) {N : ℕ} (hN : N ∈ Ts.idx) : IsEven (H N) := by
  show H N * parityOp = parityOp * H N
  have h1 := opIntegral_map (LinearMap.mulRight ℂ (parityOp : Op (ZMod (Ts.T N).Nφ))) (fundDom (Ts.T N)) (d.h N)
    (integrableOn_h d hN)
  have h2 := opIntegral_map (LinearMap.mulLeft ℂ (parityOp : Op (ZMod (Ts.T N).Nφ))) (fundDom (Ts.T N)) (d.h N)
    (integrableOn_h d hN)
  simp only [LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at h1 h2
  rw [d.eq_opIntegral N hN, h1, h2]
  congr 1
  funext R
  exact (d.h_isEven N hN R).eq

/-- §5: "`$\Hhat=\Hhat_N:=\iota(H_N)=\int\iota(h_R)\,\dd R$`" — under (H1). -/
theorem Hhat_eq_opIntegral (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, Hhat η δ₀ Ts H N = opIntegral (fundDom (Ts.T N)) fun R => iota η δ₀ (Ts.T N) (d.h N R) := by
  intro N hN
  rw [Hhat, d.eq_opIntegral N hN]
  exact iota_opIntegral hη hδ₀ (Ts.admissible N hN) _ _ (integrableOn_h d hN)

/-- Under (H1), `Ĥ_N` is self-adjoint. -/
theorem isSelfAdjoint_Hhat (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, IsSelfAdjoint (Hhat η δ₀ Ts H N) := by
  intro N hN
  have h := (d.H_isSelfAdjoint N hN).map (iotaHom hη hδ₀ (Ts.admissible N hN))
  rwa [iotaHom_apply] at h

/-- The proof of Lemma 5.6: "`because $\Hhat$ is even (Lemma~\ref{lem:sectors}(ii) and Lemma~\ref{lem:embedding}(i))`". -/
theorem isEven_Hhat (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, IsEven (Hhat η δ₀ Ts H N) := by
  intro N hN
  exact iota_isEven hη hδ₀ (Ts.admissible N hN) (isEven_H d hN)

end Setting

/-! ## The constants of Theorem 5.3 -/

section Constants

/-- **Theorem 5.3**: "`Let $c_k:=2^k\max\{C_h,4C^H_k\}$`" (as a function of the values `C_h`, `C^H_k`). -/
def ck (Ch CHk : ℝ) (k : ℕ) : ℝ :=
  2 ^ k * max Ch (4 * CHk)

/-- **Theorem 5.3**: "`$r_j:=2^j$ for $j\ge0$`". -/
def rj (j : ℕ) : ℝ :=
  2 ^ j

/-- **Theorem 5.3**: "`C_1:=e^2\Cvol\sum_{j\ge0}c_5(1+r_j)^{-5}\,\pi r_j^2\,(1+2r_j)^2`" (a `tsum`; `summable_C1`). -/
def C1 (δ₀ Ch CH5 : ℝ) : ℝ :=
  Real.exp 2 * Cvol δ₀ *
    ∑' j : ℕ, ck Ch CH5 5 * (1 + rj j) ^ (-(5 : ℝ)) * (π * rj j ^ 2) * (1 + 2 * rj j) ^ 2

/-! ### Proof devices for `C_1` (phase (b); not statements of the paper)

The `j`-th term of the series with `u = r_j` is at most `4π c_5/(1 + u)` ("`the $j$-th term of the series is at most $4\pi c_5(1+2^j)^{-1}$`"),
hence at most `4π|c_5| 2^{−j}`; for the bound, the term `j = 0` is at most `2πc_5` and the others sum to at most `4πc_5`. -/

theorem C1_term_le {c u : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) :
    c * (1 + u) ^ (-(5 : ℝ)) * (π * u ^ 2) * (1 + 2 * u) ^ 2 ≤ 4 * π * c / (1 + u) := by
  have hpos : 0 < 1 + u := by linarith
  have h1 : (1 + u) ^ (-(5 : ℝ)) = ((1 + u) ^ 5)⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    try norm_cast
  have key : u ^ 2 * (1 + 2 * u) ^ 2 ≤ 4 * (1 + u) ^ 4 := by
    have h2 : u * (1 + 2 * u) ≤ 2 * (1 + u) ^ 2 := by nlinarith
    have h3 : (u * (1 + 2 * u)) ^ 2 ≤ (2 * (1 + u) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    calc u ^ 2 * (1 + 2 * u) ^ 2 = (u * (1 + 2 * u)) ^ 2 := by ring
      _ ≤ (2 * (1 + u) ^ 2) ^ 2 := h3
      _ = 4 * (1 + u) ^ 4 := by ring
  rw [h1]
  have hinv : 0 ≤ ((1 + u) ^ 5)⁻¹ := inv_nonneg.mpr (by positivity)
  calc c * ((1 + u) ^ 5)⁻¹ * (π * u ^ 2) * (1 + 2 * u) ^ 2
      = (c * π) * (u ^ 2 * (1 + 2 * u) ^ 2) * ((1 + u) ^ 5)⁻¹ := by ring
    _ ≤ (c * π) * (4 * (1 + u) ^ 4) * ((1 + u) ^ 5)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (mul_nonneg hc Real.pi_pos.le)) hinv
    _ = 4 * π * c / (1 + u) := by
        field_simp

theorem rj_nonneg (j : ℕ) : 0 ≤ rj j := by
  unfold rj
  positivity

theorem C1_term_abs_le (Ch CH5 : ℝ) (j : ℕ) :
    ‖ck Ch CH5 5 * (1 + rj j) ^ (-(5 : ℝ)) * (π * rj j ^ 2) * (1 + 2 * rj j) ^ 2‖ ≤
      4 * π * |ck Ch CH5 5| * (1 / 2 : ℝ) ^ j := by
  have hu := rj_nonneg j
  have h0 : 0 ≤ (1 + rj j) ^ (-(5 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have h1 : 0 ≤ π * rj j ^ 2 := mul_nonneg Real.pi_pos.le (pow_nonneg hu 2)
  have h2 : 0 ≤ (1 + 2 * rj j) ^ 2 := pow_nonneg (by linarith) 2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1, abs_of_nonneg h2]
  refine (C1_term_le (abs_nonneg _) hu).trans ?_
  rw [div_eq_mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [one_div_pow]
  refine one_div_le_one_div_of_le (by positivity) ?_
  unfold rj
  linarith

/-- The series of `C_1` converges (the proof's "`the $j$-th term of the series is at most $4\pi c_5(1+2^j)^{-1}$`"). -/
theorem summable_C1 (Ch CH5 : ℝ) :
    Summable fun j : ℕ => ck Ch CH5 5 * (1 + rj j) ^ (-(5 : ℝ)) * (π * rj j ^ 2) * (1 + 2 * rj j) ^ 2 := by
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
    (C1_term_abs_le Ch CH5)

/-- **Theorem 5.3**: "`\ \le\ 192\pi e^2\,\Cvol\max\{C_h,4C^H_5\}.`" (for `C_h ≥ 0`, as under (H1)). -/
theorem C1_le (δ₀ : ℝ) {Ch : ℝ} (hCh : 0 ≤ Ch) (CH5 : ℝ) :
    C1 δ₀ Ch CH5 ≤ 192 * π * Real.exp 2 * Cvol δ₀ * max Ch (4 * CH5) := by
  set M := max Ch (4 * CH5) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left hCh
  have hc : ck Ch CH5 5 = 32 * M := by
    rw [ck, hM]
    norm_num
  have hc0 : 0 ≤ ck Ch CH5 5 := by rw [hc]; positivity
  have hCvol : 0 ≤ Cvol δ₀ := by
    unfold Cvol
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (le_trans zero_le_one (le_max_left _ _))
  have hsum := summable_C1 Ch CH5
  rw [C1, hsum.tsum_eq_zero_add]
  have hterm0 : ck Ch CH5 5 * (1 + rj 0) ^ (-(5 : ℝ)) * (π * rj 0 ^ 2) * (1 + 2 * rj 0) ^ 2 ≤
      2 * π * ck Ch CH5 5 := by
    refine (C1_term_le hc0 (rj_nonneg 0)).trans (le_of_eq ?_)
    rw [show rj 0 = 1 by simp [rj]]
    ring
  have hshift : Summable fun j : ℕ =>
      ck Ch CH5 5 * (1 + rj (j + 1)) ^ (-(5 : ℝ)) * (π * rj (j + 1) ^ 2) * (1 + 2 * rj (j + 1)) ^ 2 :=
    (summable_nat_add_iff 1).mpr hsum
  have hgeo : Summable fun j : ℕ => 4 * π * ck Ch CH5 5 * ((1 / 2 : ℝ) ^ (j + 1)) :=
    ((summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (4 * π * ck Ch CH5 5 * (1 / 2))).congr fun j => by rw [pow_succ]; ring
  have hle : ∀ j : ℕ, ck Ch CH5 5 * (1 + rj (j + 1)) ^ (-(5 : ℝ)) * (π * rj (j + 1) ^ 2) * (1 + 2 * rj (j + 1)) ^ 2 ≤
      4 * π * ck Ch CH5 5 * ((1 / 2 : ℝ) ^ (j + 1)) := by
    intro j
    have h := C1_term_abs_le Ch CH5 (j + 1)
    rw [abs_of_nonneg hc0] at h
    exact (le_abs_self _).trans h
  have htail : ∑' j : ℕ, ck Ch CH5 5 * (1 + rj (j + 1)) ^ (-(5 : ℝ)) * (π * rj (j + 1) ^ 2) *
      (1 + 2 * rj (j + 1)) ^ 2 ≤ 4 * π * ck Ch CH5 5 := by
    refine (hshift.tsum_le_tsum hle hgeo).trans (le_of_eq ?_)
    rw [tsum_mul_left]
    have : ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) = 1 := by
      have h2 := tsum_geometric_two
      have e : (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) = fun j => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ j := by
        funext j; rw [pow_succ]; ring
      rw [e, tsum_mul_left, h2]
      norm_num
    rw [this, mul_one]
  have hE : 0 ≤ Real.exp 2 * Cvol δ₀ := mul_nonneg (Real.exp_pos _).le hCvol
  calc Real.exp 2 * Cvol δ₀ * (ck Ch CH5 5 * (1 + rj 0) ^ (-(5 : ℝ)) * (π * rj 0 ^ 2) * (1 + 2 * rj 0) ^ 2 +
        ∑' j : ℕ, ck Ch CH5 5 * (1 + rj (j + 1)) ^ (-(5 : ℝ)) * (π * rj (j + 1) ^ 2) * (1 + 2 * rj (j + 1)) ^ 2)
      ≤ Real.exp 2 * Cvol δ₀ * (2 * π * ck Ch CH5 5 + 4 * π * ck Ch CH5 5) :=
        mul_le_mul_of_nonneg_left (add_le_add hterm0 htail) hE
    _ = 192 * π * Real.exp 2 * Cvol δ₀ * M := by rw [hc]; ring

/-- **Theorem 5.3(b)**: "`put $C_{\rm lc}(\beta):=\max\{1,(4C_1)^{1/(1-\beta)}\}$`". -/
def ClcBeta (C1v β : ℝ) : ℝ :=
  max 1 ((4 * C1v) ^ (1 / (1 - β)))

/-- **Theorem 5.3(b)**: "`and $k:=2+\lceil(k'+3)/\beta\rceil$`". -/
def kLc (k' β : ℝ) : ℕ :=
  2 + ⌈(k' + 3) / β⌉₊

/-- **Theorem 5.3(b)**: "`C_{k',\beta}:=\frac{16\pi c_k2^{k-2}}{3C_1}\Bigl(\frac{\max\{1,C_1\}}{4C_1}\Bigr)^3+\Bigl(\frac{2k'}{e(1-\beta)}\Bigr)^{k'/(1-\beta)}.`"
with `k = kLc k' β` and `c_k` from `C_h`, `C^H_k` (the argument `C1v` is `C_1`). -/
def CkBeta (Ch : ℝ) (CH : ℕ → ℝ) (C1v k' β : ℝ) : ℝ :=
  16 * π * ck Ch (CH (kLc k' β)) (kLc k' β) * 2 ^ (kLc k' β - 2) / (3 * C1v) * (max 1 C1v / (4 * C1v)) ^ 3 +
    (2 * k' / (Real.exp 1 * (1 - β))) ^ (k' / (1 - β))

end Constants

/-! ## Step 0 of the proof of Theorem 5.3: the canonical approximants -/

section CanonicalApproximants

variable {η : ℝ → ℝ} {δ₀ : ℝ} {Ts : TorusSeq δ₀} {H : (N : ℕ) → FockOp (Ts.T N)}

/-- The proof of Theorem 5.3, Step 0: "`For $R\in\Tor_N$ and $r\ge0$ put`" "`\tilde h_{R,r}:=\CE_{\Ball rR}\bigl(\iota(h_R)\bigr).`" -/
def hTilde (d : H1Data η δ₀ Ts H) (N : ℕ) (R : ℝ × ℝ) (r : ℝ) : Op (Slot δ₀ (Ts.T N)) :=
  condExp (slotBall δ₀ (Ts.T N) R r) (iota η δ₀ (Ts.T N) (d.h N R))

/-! ### Proof devices for Step 0 (phase (b); not statements of the paper) -/

theorem measurableSet_slotBall_eq (δ₀ : ℝ) (T : Torus) (r : ℝ) (Y₀ : Finset (Slot δ₀ T)) :
    MeasurableSet {R : ℝ × ℝ | slotBall δ₀ T R r = Y₀} := by
  have hs : ∀ s, MeasurableSet {R : ℝ × ℝ | s ∈ slotBall δ₀ T R r} := by
    intro s
    have : {R : ℝ × ℝ | s ∈ slotBall δ₀ T R r} = {R | flatDist T (centre δ₀ T s) R ≤ r} := by
      ext R; simp [slotBall]
    rw [this]
    exact measurableSet_le (continuous_flatDist_right T _).measurable measurable_const
  have e : {R : ℝ × ℝ | slotBall δ₀ T R r = Y₀} = ⋂ s, {R | s ∈ slotBall δ₀ T R r ↔ s ∈ Y₀} := by
    ext R
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff]
  rw [e]
  refine MeasurableSet.iInter fun s => ?_
  by_cases h : s ∈ Y₀
  · simp only [h, iff_true]
    exact hs s
  · simp only [h, iff_false]
    exact (hs s).compl

theorem measurable_iota_entry {T : Torus} (hT : T.Admissible δ₀) (hη : IsProfile η) (hδ₀ : 0 < δ₀)
    {h : ℝ × ℝ → FockOp T} (hh : ∀ m m', Measurable fun R => h R m m') :
    ∀ m m' : Conf (Slot δ₀ T), Measurable fun R => iota η δ₀ T (h R) m m' := by
  intro k k'
  have e : (fun R => iota η δ₀ T (h R) k k') =
      fun R => ∑ n, ∑ n', h R n n' * iota η δ₀ T (Matrix.single n n' (1 : ℂ)) k k' := by
    funext R
    have h1 : h R = ∑ n, ∑ n', (h R n n') • Matrix.single n n' (1 : ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single (h R)]
      simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    conv_lhs => rw [h1, ← iotaHom_apply hη hδ₀ hT]
    simp only [map_sum, map_smul, iotaHom_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [e]
  exact Finset.measurable_sum _ fun n _ => Finset.measurable_sum _ fun n' _ => (hh n n').mul_const _

/-- Step 0: "`$\tilde h_{R,r}\in\Alg(\Ball rR)$`". -/
theorem hTilde_mem_Alg (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, ∀ (R : ℝ × ℝ) (r : ℝ), hTilde d N R r ∈ Alg (slotBall δ₀ (Ts.T N) R r) := by
  intro N hN R r
  exact Fermion.Pilot.JW.condExp_mem_Alg _ (iota_isEven hη hδ₀ (Ts.admissible N hN) (d.h_isEven N hN R))

/-- Step 0: "`is self-adjoint`". -/
theorem hTilde_isSelfAdjoint (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, ∀ (R : ℝ × ℝ) (r : ℝ), IsSelfAdjoint (hTilde d N R r) := by
  intro N hN R r
  have hT := Ts.admissible N hN
  have hh : (d.h N R)ᴴ = d.h N R := d.h_isSelfAdjoint N hN R
  have hsa : (iota η δ₀ (Ts.T N) (d.h N R))ᴴ = iota η δ₀ (Ts.T N) (d.h N R) := by
    rw [← iota_conjTranspose hη hδ₀ hT, hh]
  show star (hTilde d N R r) = hTilde d N R r
  rw [Matrix.star_eq_conjTranspose, hTilde, ← Fermion.Pilot.JW.condExp_conjTranspose, hsa]

/-- Step 0: "`$\norm{\tilde h_{R,r}}\le\norm{h_R}\le C_h$`". -/
theorem norm_hTilde_le (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, ∀ (R : ℝ × ℝ) (r : ℝ),
      ‖opCLM (hTilde d N R r)‖ ≤ ‖toCLM (Ts.T N) (d.h N R)‖ ∧ ‖toCLM (Ts.T N) (d.h N R)‖ ≤ d.Ch := by
  intro N hN R r
  have hT := Ts.admissible N hN
  refine ⟨?_, d.norm_h_le N hN R⟩
  rw [hTilde, ← norm_iota hη hδ₀ hT]
  open scoped Matrix.Norms.L2Operator in
  · rw [norm_opCLM_eq_l2, norm_opCLM_eq_l2]
    exact Fermion.Pilot.JW.norm_condExp_le _ _

/-- Step 0: "`and $\norm{\iota(h_R)-\tilde h_{R,r}}\le2C^H_k(1+r)^{-k}$ for every $k$ at once`". -/
theorem norm_iota_sub_hTilde_le (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, ∀ (R : ℝ × ℝ) (r : ℝ), 0 ≤ r → ∀ k : ℕ,
      ‖opCLM (iota η δ₀ (Ts.T N) (d.h N R) - hTilde d N R r)‖ ≤ 2 * d.CH k * (1 + r) ^ (-(k : ℝ)) := by
  intro N hN R r hr k
  have hT := Ts.admissible N hN
  obtain ⟨A', hA'm, hA'⟩ := d.approx k N hN R r hr
  have heven := iota_isEven hη hδ₀ hT (d.h_isEven N hN R)
  rw [hTilde]
  open scoped Matrix.Norms.L2Operator in
  · have h1 := Fermion.Pilot.JW.norm_sub_condExp_le (slotBall δ₀ (Ts.T N) R r) heven
    have hbdd : BddBelow (Set.range fun A'' : Alg (slotBall δ₀ (Ts.T N) R r) =>
        ‖iota η δ₀ (Ts.T N) (d.h N R) - (A'' : Op (Slot δ₀ (Ts.T N)))‖) :=
      ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
    have h2 := ciInf_le hbdd ⟨A', hA'm⟩
    rw [norm_opCLM_eq_l2]
    rw [norm_opCLM_eq_l2] at hA'
    calc _ ≤ 2 * ⨅ A'' : Alg (slotBall δ₀ (Ts.T N) R r),
          ‖iota η δ₀ (Ts.T N) (d.h N R) - (A'' : Op (Slot δ₀ (Ts.T N)))‖ := h1
      _ ≤ 2 * ‖iota η δ₀ (Ts.T N) (d.h N R) - A'‖ := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 2 * (d.CH k * (1 + r) ^ (-(k : ℝ))) := mul_le_mul_of_nonneg_left hA' (by norm_num)
      _ = _ := by ring

/-- Step 0: "`by Lemma~\ref{lem:condexp}, $R\mapsto\tilde h_{R,r}$ is Borel`" (entrywise). -/
theorem hTilde_measurable (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, ∀ r : ℝ, ∀ m m' : Conf (Slot δ₀ (Ts.T N)), Measurable fun R : ℝ × ℝ => hTilde d N R r m m' := by
  intro N hN r m m'
  exact measurable_condExp (measurable_iota_entry (Ts.admissible N hN) hη hδ₀ (d.h_measurable N hN))
    (measurableSet_slotBall_eq δ₀ (Ts.T N) r) m m'

end CanonicalApproximants

/-! ### Proof devices for Theorem 5.3(a) (phase (b); not statements of the paper)

The paper's Steps 0–4 at one torus, for the data of Step 0 bundled as `MSData` (built from (H1) by `msdata`):
* Step 1: the dyadic pieces `ĥ^{(j)}_R` (`piece`) and the multiscale interaction `Ψ_λ` (`PsiL`: operator integrals of
  `[Ball(r_j, R) = Z] ĥ^{(j)}_R`, summed over `j ≤ j₀`; the pieces with `j > j_max` vanish, so the paper's
  `min{j₀, j_max}` is not needed); `Ĥ_λ = ∫ h̃_{R,r_{j₀}} dR` (`hamTot_PsiL`) and `Ĥ_{λ,Y} := Σ_{Z⊆Y} Ψ_λ(Z)` (`hamOn`).
* Step 2: `C(Ψ_λ, λ) ≤ C_1` (`chainWeight_PsiL_le`), with the disc of the torus of measure at most `πr²` as the image of
  a planar disc under the covering map (`volume_fundDom_inter_disc_le`: Mathlib's `Complex.volume_closedBall` carried by
  `Complex.volume_preserving_equiv_real_prod`, the translates of the fundamental domain being disjoint).
* Step 3: the localization for any even interaction with `C(Ψ, λ) ≤ C_1` (`norm_dyn_sub_dyn_fat_le`), for `t < 0`
  through `(−Ψ, −t)` (`norm_dyn_sub_dyn_fat_le_abs`).
* Step 4: Duhamel for both signs of the time (`norm_dyn_sub_dyn_le_of_bound`) and the per-time bound
  `‖[Ĥ − Ĥ_λ, τ^λ_{t'}(A)]‖ ≤ 16π c_k ‖A‖ |X| λ^{−(k−2)} (1 + C_1|t'|)²` (`norm_comm_tail_le`), with one change: the
  paper's exact integral `∫ e^{−(|ξ|−q)_+/λ} dξ = π(q² + 2qλ + 2λ²)` is replaced by shells of width `λ` (`shellFn`,
  `integral_shells_le`: at most `6.5π r_j² (1 + C_1|t'|)²`, inside the paper's `8π r_j² (1 + C_1|t'|)²`), the torus
  integral being bounded through the same disc measure; the scales above `λ` are summed up to a top scale at which
  `h̃_{R,r} = ι(h_R)` (`MSData.top`).
* The case `C_h = 0` (where `C_1` may vanish and the stated `16πc_k/(3C_1)` is `0` by Lean's division) is the trivial
  case `Ĥ = Ĥ_λ = 0` (`master_bound`).

Round one's device `C1_nonneg` stands here because these devices use it. -/

section MasterDevices

open MeasureTheory Filter Set Real Topology

theorem C1_nonneg (δ₀ : ℝ) {Ch : ℝ} (hCh : 0 ≤ Ch) (CH5 : ℝ) : 0 ≤ C1 δ₀ Ch CH5 := by
  have hc0 : 0 ≤ ck Ch CH5 5 := by
    unfold ck
    exact mul_nonneg (by positivity) (le_max_of_le_left hCh)
  have hCvol : 0 ≤ Cvol δ₀ := by
    unfold Cvol
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (le_trans zero_le_one (le_max_left _ _))
  unfold C1
  refine mul_nonneg (mul_nonneg (Real.exp_pos _).le hCvol) (tsum_nonneg fun j => ?_)
  have hu := rj_nonneg j
  exact mul_nonneg (mul_nonneg (mul_nonneg hc0 (Real.rpow_nonneg (by linarith) _))
    (mul_nonneg Real.pi_pos.le (pow_nonneg hu 2))) (pow_nonneg (by linarith) 2)


open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op c chat parityOp IsEven CAR Alg condExp)

section Duhamel

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem continuous_opCLM_dyn_comp' (H : Op S) {Y : ℝ → Op S} (hY : Continuous fun u => opCLM (Y u)) :
    Continuous fun u => opCLM (dyn H u (Y u)) := by
  set L : Op S := (I : ℂ) • H with hL
  have hfun : (fun u => opCLM (dyn H u (Y u))) =
      fun u => NormedSpace.exp (u • opCLM L) * opCLM (Y u) * NormedSpace.exp (u • (-opCLM L)) := by
    funext u; rw [dyn, opCLM_mul', opCLM_mul', opCLM_expI, opCLM_expI_neg]
  rw [hfun]
  have h1 : Continuous fun u : ℝ => NormedSpace.exp (u • opCLM L) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (opCLM L) u).continuousAt
  have h2 : Continuous fun u : ℝ => NormedSpace.exp (u • (-opCLM L)) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-opCLM L) u).continuousAt
  exact (h1.mul hY).mul h2

/-- Device (Duhamel): `‖τ^H_t(A) − τ^{H'}_t(A)‖ ≤ ∫_0^t ‖[H − H', τ^{H'}_{t−u}(A)]‖ du` for `t ≥ 0`, `H` self-adjoint. -/
theorem norm_dyn_sub_dyn_le {H H' : Op S} (hH : IsSelfAdjoint H) (A : Op S) {t : ℝ} (ht : 0 ≤ t) :
    ‖opCLM (dyn H t A - dyn H' t A)‖ ≤
      ∫ u in (0 : ℝ)..t, ‖opCLM ((H - H') * dyn H' (t - u) A - dyn H' (t - u) A * (H - H'))‖ := by
  set Y : ℝ → Op S := fun u => dyn H' (t - u) A with hYdef
  set F : ℝ → (EuclideanSpace ℂ (Conf S) →L[ℂ] EuclideanSpace ℂ (Conf S)) := fun u => opCLM (dyn H u (Y u)) with hF
  set F' : ℝ → (EuclideanSpace ℂ (Conf S) →L[ℂ] EuclideanSpace ℂ (Conf S)) :=
    fun u => opCLM (dyn H u ((I : ℂ) • ((H - H') * Y u - Y u * (H - H')))) with hF'
  have hderiv : ∀ u, HasDerivAt F (F' u) u := by
    intro u
    have h := hasDerivAt_opCLM_dyn_comp H (hasDerivAt_opCLM_dyn_sub H' A t u)
    refine h.congr_deriv ?_
    simp only [hF', hYdef]
    congr 2
    rw [Matrix.sub_mul, Matrix.mul_sub]
    module
  have hYc : Continuous fun u => opCLM (Y u) := by
    have := (continuous_opCLM_dyn H' A).comp (continuous_const.sub continuous_id : Continuous fun u : ℝ => t - u)
    exact this
  have hF'c : Continuous F' := by
    refine continuous_opCLM_dyn_comp' H ?_
    have e : (fun u => opCLM ((I : ℂ) • ((H - H') * Y u - Y u * (H - H')))) =
        fun u => (I : ℂ) • (opCLM (H - H') * opCLM (Y u) - opCLM (Y u) * opCLM (H - H')) := by
      funext u; rw [opCLM_smul', opCLM_sub', opCLM_mul', opCLM_mul']
    rw [e]
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) (hF'c.intervalIntegrable 0 t)
  have hF0 : F 0 = opCLM (dyn H' t A) := by simp only [hF, hYdef, sub_zero, dyn_time_zero]
  have hFt : F t = opCLM (dyn H t A) := by simp only [hF, hYdef, sub_self, dyn_time_zero]
  have hnorm : ∀ u, ‖F' u‖ = ‖opCLM ((H - H') * Y u - Y u * (H - H'))‖ := by
    intro u
    simp only [hF']
    rw [norm_dyn hH, opCLM_smul', norm_smul, Complex.norm_I, one_mul]
  rw [opCLM_sub', ← hFt, ← hF0, ← hFTC]
  calc ‖∫ u in (0 : ℝ)..t, F' u‖ ≤ ∫ u in (0 : ℝ)..t, ‖F' u‖ := intervalIntegral.norm_integral_le_integral_norm ht
    _ = _ := by simp only [hnorm, hYdef]

end Duhamel

section MatrixExp

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Device: the entries of `u ↦ e^{u N}` have derivative `(e^{u N} N)_{s s'}`. -/
theorem hasDerivAt_exp_smul_apply (N : Matrix S S ℝ) (s s' : S) (u : ℝ) :
    HasDerivAt (fun v : ℝ => NormedSpace.exp (v • N) s s') ((NormedSpace.exp (u • N) * N) s s') u := by
  letI : NormedRing (Matrix S S ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix S S ℝ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) N u
  have hc : N * NormedSpace.exp (u • N) = NormedSpace.exp (u • N) * N :=
    ((Commute.refl N).smul_right u).exp_right.eq
  have h' := h.congr_deriv hc
  let Φ : Matrix S S ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ s s')
  have h2 := Φ.hasFDerivAt.comp_hasDerivAt u h'
  exact h2

end MatrixExp

section Localization

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem integral_exp_smul_mul_apply (N : Matrix S S ℝ) (s s' : S) (t : ℝ) :
    ∫ u in (0 : ℝ)..t, (NormedSpace.exp (u • N) * N) s s' = NormedSpace.exp (t • N) s s' - (1 : Matrix S S ℝ) s s' := by
  have hc : ∀ s₁ s₂ : S, Continuous fun u : ℝ => NormedSpace.exp (u • N) s₁ s₂ := fun s₁ s₂ =>
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_exp_smul_apply N s₁ s₂ u).continuousAt
  have hcont : Continuous fun u : ℝ => (NormedSpace.exp (u • N) * N) s s' := by
    simp only [Matrix.mul_apply]
    exact continuous_finsetSum _ fun s'' _ => (hc s s'').mul continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_exp_smul_apply N s s' u)
    (hcont.intervalIntegrable 0 t), zero_smul, NormedSpace.exp_zero]

/-- Device: the interaction with its terms not inside `Y` set to zero. -/
def restrictInteraction (Ψ : Finset S → Op S) (Y : Finset S) : Finset S → Op S :=
  fun Z => if Z ⊆ Y then Ψ Z else 0

theorem restrictInteraction_eq (Ψ : Finset S → Op S) (Y : Finset S) (Z : Finset S) :
    restrictInteraction Ψ Y Z = Ψ Z ∨ restrictInteraction Ψ Y Z = 0 := by
  unfold restrictInteraction
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem hamTot_restrictInteraction (Ψ : Finset S → Op S) (Y : Finset S) :
    hamTot (restrictInteraction Ψ Y) = hamOn Ψ Y := by
  simp only [hamTot, hamOn, restrictInteraction]
  rw [← Finset.sum_filter]
  congr 1
  ext Z
  simp

theorem hamTot_sub_hamOn (Ψ : Finset S → Op S) (Y : Finset S) :
    hamTot Ψ - hamOn Ψ Y = ∑ Z ∈ Finset.univ.filter (fun Z => ¬ Z ⊆ Y), Ψ Z := by
  rw [hamTot, hamOn, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun Z => Z ⊆ Y)]
  have h : Finset.univ.filter (fun Z => Z ⊆ Y) = Y.powerset := by
    ext Z
    simp
  rw [h]
  abel

theorem chainMatrix_symm (Ψ : Finset S → Op S) (s s' : S) : chainMatrix Ψ s s' = chainMatrix Ψ s' s := by
  simp only [chainMatrix, Matrix.of_apply]
  congr 1
  ext Z
  simp [and_comm]

/-- Device: the combinatorial step of Step 3 of Theorem 5.3. -/
theorem sum_not_subset_le (Ψ : Finset S → Op S) (Y : Finset S) {f : S → ℝ} (hf : ∀ s, 0 ≤ f s) :
    ∑ Z ∈ Finset.univ.filter (fun Z => ¬ Z ⊆ Y), ‖opCLM (Ψ Z)‖ * ∑ s'' ∈ Z, f s'' ≤
      ∑ s' ∈ Yᶜ, ∑ s'' : S, chainMatrix Ψ s' s'' * f s'' := by
  set c : Finset S → ℝ := fun Z => ‖opCLM (Ψ Z)‖ * ∑ s'' ∈ Z, f s'' with hc
  have hc0 : ∀ Z, 0 ≤ c Z := fun Z => mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun s _ => hf s)
  have e1 : ∀ s s'', chainMatrix Ψ s s'' * f s'' =
      ∑ Z : Finset S, if s ∈ Z ∧ s'' ∈ Z then ‖opCLM (Ψ Z)‖ * f s'' else 0 := by
    intro s s''
    rw [chainMatrix, Matrix.of_apply, Finset.sum_mul, Finset.sum_filter]
  have e2 : ∀ (Z : Finset S) (s : S), (∑ s'' : S, if s ∈ Z ∧ s'' ∈ Z then ‖opCLM (Ψ Z)‖ * f s'' else 0) =
      if s ∈ Z then c Z else 0 := by
    intro Z s
    by_cases hs : s ∈ Z
    · simp only [hs, true_and, if_true, hc]
      rw [Finset.mul_sum, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    · simp [hs]
  have hM : ∑ s ∈ Yᶜ, ∑ s'' : S, chainMatrix Ψ s s'' * f s'' = ∑ Z : Finset S, ((Yᶜ ∩ Z).card : ℝ) * c Z := by
    calc ∑ s ∈ Yᶜ, ∑ s'' : S, chainMatrix Ψ s s'' * f s''
        = ∑ s ∈ Yᶜ, ∑ s'' : S, ∑ Z : Finset S,
            (if s ∈ Z ∧ s'' ∈ Z then ‖opCLM (Ψ Z)‖ * f s'' else 0) := by simp_rw [e1]
      _ = ∑ s ∈ Yᶜ, ∑ Z : Finset S, ∑ s'' : S,
            (if s ∈ Z ∧ s'' ∈ Z then ‖opCLM (Ψ Z)‖ * f s'' else 0) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ Z : Finset S, ∑ s ∈ Yᶜ, ∑ s'' : S,
            (if s ∈ Z ∧ s'' ∈ Z then ‖opCLM (Ψ Z)‖ * f s'' else 0) := Finset.sum_comm
      _ = ∑ Z : Finset S, ((Yᶜ ∩ Z).card : ℝ) * c Z := by
          refine Finset.sum_congr rfl fun Z _ => ?_
          simp_rw [e2]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter]
  calc ∑ Z ∈ Finset.univ.filter (fun Z => ¬ Z ⊆ Y), c Z
      ≤ ∑ Z ∈ Finset.univ.filter (fun Z => ¬ Z ⊆ Y), ((Yᶜ ∩ Z).card : ℝ) * c Z := by
        refine Finset.sum_le_sum fun Z hZ => ?_
        rw [Finset.mem_filter] at hZ
        have hne : (Yᶜ ∩ Z).Nonempty := by
          obtain ⟨x, hxZ, hxY⟩ := Finset.not_subset.mp hZ.2
          exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hxY, hxZ⟩⟩
        have h1 : (1 : ℝ) ≤ (Yᶜ ∩ Z).card := by exact_mod_cast Finset.card_pos.mpr hne
        exact le_mul_of_one_le_left (hc0 Z) h1
    _ ≤ ∑ Z : Finset S, ((Yᶜ ∩ Z).card : ℝ) * c Z :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun Z _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (hc0 Z)
    _ = _ := hM.symm

theorem norm_comm_swap (P Q : Op S) : ‖opCLM (P * Q - Q * P)‖ = ‖opCLM (Q * P - P * Q)‖ := by
  rw [← neg_sub, opCLM_neg', norm_neg]

end Localization

section LocalizationSlots

variable {δ₀ : ℝ} {T : Torus}

theorem slotDist_comm_m (s s' : Slot δ₀ T) : slotDist δ₀ T s s' = slotDist δ₀ T s' s := by
  simp only [slotDist, flatDist]
  rw [← neg_sub (centre δ₀ T s).1, ← neg_sub (centre δ₀ T s).2, pdist_neg, pdist_neg]

theorem expNegDiv_compl_fat_le {lam : ℝ} (hlam : 0 < lam) {X : Finset (Slot δ₀ T)} {ρ : ℝ} (hρ : 0 < ρ)
    {s : Slot δ₀ T} (hs : s ∈ X) : expNegDiv (slotSetDist {s} (fat X ρ)ᶜ) lam ≤ Real.exp (-ρ / lam) := by
  rcases Finset.eq_empty_or_nonempty (fat X ρ)ᶜ with hW | hW
  · rw [hW, slotSetDist_empty_right, expNegDiv, if_pos rfl]
    exact (Real.exp_pos _).le
  · rw [slotSetDist_eq_inf' (Finset.singleton_nonempty s) hW]
    have hgt : ρ < ({s} ×ˢ (fat X ρ)ᶜ).inf' ((Finset.singleton_nonempty s).product hW)
        (fun p => slotDist δ₀ T p.1 p.2) := by
      rw [Finset.lt_inf'_iff]
      rintro ⟨a, b⟩ hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      rw [Finset.mem_singleton] at ha
      subst ha
      rw [Finset.mem_compl] at hb
      by_contra hle
      push_neg at hle
      apply hb
      rw [mem_fat]
      exact ⟨a, hs, by rw [slotDist_comm_m]; exact hle⟩
    rw [expNegDiv_ofReal (by linarith)]
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right hgt.le hlam.le

/-- Device (Step 3 of Theorem 5.3): localization of the dynamics of an even interaction with bounded chain weight. -/
theorem norm_dyn_sub_dyn_fat_le {Ψ : Finset (Slot δ₀ T) → Op (Slot δ₀ T)} (hΨ : IsEvenInteraction Ψ)
    {lam C₁ : ℝ} (hlam : 0 < lam) (hC : chainWeight Ψ lam ≤ C₁) {ρ : ℝ} (hρ : 0 < ρ)
    {X : Finset (Slot δ₀ T)} {A : Op (Slot δ₀ T)} (hA : A ∈ CAR X) {t : ℝ} (ht : 0 ≤ t) :
    ‖opCLM (dyn (hamTot Ψ) t A - dyn (hamOn Ψ (fat X ρ)) t A)‖ ≤
      ‖opCLM A‖ * X.card * (Real.exp (-ρ / lam) * (Real.exp (2 * C₁ * t) - 1)) := by
  set Y := fat X ρ with hY
  set M := chainMatrix Ψ with hMdef
  have hM0 : ∀ s s', 0 ≤ M s s' := chainMatrix_nonneg Ψ
  have hE0 : ∀ (v : ℝ) (s s' : Slot δ₀ T), 0 ≤ v → 0 ≤ NormedSpace.exp (v • M) s s' := by
    intro v s s' hv
    have h := hasSum_exp_matrix_apply (v • M) s s'
    refine h.nonneg fun n => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
    rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (pow_nonneg hv _) (pow_apply_nonneg hM0 n s s')
  have h1 := norm_dyn_sub_dyn_le (H' := hamOn Ψ Y) (isSelfAdjoint_hamTot hΨ) A ht
  -- the integrand
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) t,
      ‖opCLM ((hamTot Ψ - hamOn Ψ Y) * dyn (hamOn Ψ Y) (t - u) A - dyn (hamOn Ψ Y) (t - u) A * (hamTot Ψ - hamOn Ψ Y))‖ ≤
        2 * ‖opCLM A‖ * ∑ s ∈ X, ∑ s' ∈ Yᶜ, (NormedSpace.exp ((t - u) • ((2 : ℝ) • M)) * ((2 : ℝ) • M)) s s' / 2 := by
    intro u hu
    have htu : 0 ≤ t - u := by linarith [hu.2]
    rw [hamTot_sub_hamOn, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, opCLM_sum']
    refine (norm_sum_le _ _).trans ?_
    have hLR : ∀ Z ∈ Finset.univ.filter (fun Z => ¬ Z ⊆ Y),
        ‖opCLM (Ψ Z * dyn (hamOn Ψ Y) (t - u) A - dyn (hamOn Ψ Y) (t - u) A * Ψ Z)‖ ≤
          2 * ‖opCLM A‖ * (‖opCLM (Ψ Z)‖ *
            ∑ s'' ∈ Z, ∑ s ∈ X, NormedSpace.exp ((2 * (t - u)) • M) s s'') := by
      intro Z _
      have h := (lieb_robinson_of_terms_zero hΨ (restrictInteraction_eq Ψ Y) (Or.inl ⟨hA, (hΨ Z).2⟩) (t - u)).1
      rw [hamTot_restrictInteraction, abs_of_nonneg htu, ← hMdef] at h
      rw [norm_comm_swap]
      refine h.trans (le_of_eq ?_)
      rw [Finset.sum_comm]
      ring
    refine (Finset.sum_le_sum hLR).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hcomb := sum_not_subset_le Ψ Y (f := fun s'' => ∑ s ∈ X, NormedSpace.exp ((2 * (t - u)) • M) s s'')
      (fun s'' => Finset.sum_nonneg fun s _ => hE0 _ s s'' (by linarith))
    refine hcomb.trans (le_of_eq ?_)
    -- `Σ_{s'∉Y} Σ_{s''} M_{s's''} Σ_{s∈X} E_{ss''} = Σ_{s∈X} Σ_{s'∉Y} (E (2M))_{ss'} / 2`
    have e3 : ∀ s s', (NormedSpace.exp ((t - u) • ((2 : ℝ) • M)) * ((2 : ℝ) • M)) s s' / 2 =
        ∑ s'' : Slot δ₀ T, NormedSpace.exp ((2 * (t - u)) • M) s s'' * M s'' s' := by
      intro s s'
      rw [smul_smul, mul_comm (t - u) 2, Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
      ring
    simp only [e3]
    calc ∑ s' ∈ Yᶜ, ∑ s'' : Slot δ₀ T, chainMatrix Ψ s' s'' *
          ∑ s ∈ X, NormedSpace.exp ((2 * (t - u)) • M) s s''
        = ∑ s' ∈ Yᶜ, ∑ s ∈ X, ∑ s'' : Slot δ₀ T,
            chainMatrix Ψ s' s'' * NormedSpace.exp ((2 * (t - u)) • M) s s'' := by
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [Finset.sum_congr rfl fun s'' _ => Finset.mul_sum _ _ _]
          exact Finset.sum_comm
      _ = ∑ s ∈ X, ∑ s' ∈ Yᶜ, ∑ s'' : Slot δ₀ T,
            chainMatrix Ψ s' s'' * NormedSpace.exp ((2 * (t - u)) • M) s s'' := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ =>
            Finset.sum_congr rfl fun s'' _ => ?_
          rw [hMdef, chainMatrix_symm Ψ s' s'']
          ring
  have hgc : Continuous fun u => ‖opCLM ((hamTot Ψ - hamOn Ψ Y) * dyn (hamOn Ψ Y) (t - u) A -
      dyn (hamOn Ψ Y) (t - u) A * (hamTot Ψ - hamOn Ψ Y))‖ := by
    have hc : Continuous fun u : ℝ => opCLM (dyn (hamOn Ψ Y) (t - u) A) :=
      (continuous_opCLM_dyn (hamOn Ψ Y) A).comp (continuous_const.sub continuous_id)
    have e : (fun u => ‖opCLM ((hamTot Ψ - hamOn Ψ Y) * dyn (hamOn Ψ Y) (t - u) A -
        dyn (hamOn Ψ Y) (t - u) A * (hamTot Ψ - hamOn Ψ Y))‖) =
        fun u => ‖opCLM (hamTot Ψ - hamOn Ψ Y) * opCLM (dyn (hamOn Ψ Y) (t - u) A) -
          opCLM (dyn (hamOn Ψ Y) (t - u) A) * opCLM (hamTot Ψ - hamOn Ψ Y)‖ := by
      funext u; rw [opCLM_sub', opCLM_mul', opCLM_mul']
    rw [e]
    fun_prop
  have hEc : ∀ s s', Continuous fun v : ℝ => (NormedSpace.exp (v • ((2 : ℝ) • M)) * ((2 : ℝ) • M)) s s' := by
    intro s s'
    have hc : ∀ s₁ s₂ : Slot δ₀ T, Continuous fun u : ℝ => NormedSpace.exp (u • ((2 : ℝ) • M)) s₁ s₂ :=
      fun s₁ s₂ => continuous_iff_continuousAt.mpr fun u => (hasDerivAt_exp_smul_apply _ s₁ s₂ u).continuousAt
    simp only [Matrix.mul_apply]
    exact continuous_finsetSum _ fun s'' _ => (hc s s'').mul continuous_const
  have hEc' : ∀ s s', Continuous fun u : ℝ =>
      (NormedSpace.exp ((t - u) • ((2 : ℝ) • M)) * ((2 : ℝ) • M)) s s' / 2 := fun s s' =>
    ((hEc s s').comp (continuous_const.sub continuous_id)).div_const _
  have hGc : Continuous fun u : ℝ => 2 * ‖opCLM A‖ * ∑ s ∈ X, ∑ s' ∈ Yᶜ,
      (NormedSpace.exp ((t - u) • ((2 : ℝ) • M)) * ((2 : ℝ) • M)) s s' / 2 :=
    continuous_const.mul (continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun s' _ => hEc' s s')
  have h2 := intervalIntegral.integral_mono_on ht (hgc.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    (hGc.intervalIntegrable (μ := MeasureTheory.volume) 0 t) hpt
  have hone : ∀ s s', ∫ u in (0 : ℝ)..t, (NormedSpace.exp ((t - u) • ((2 : ℝ) • M)) * ((2 : ℝ) • M)) s s' / 2 =
      (NormedSpace.exp ((2 * t) • M) - 1) s s' / 2 := by
    intro s s'
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_comp_sub_left (fun v => (NormedSpace.exp (v • ((2 : ℝ) • M)) * ((2 : ℝ) • M)) s s'),
      sub_self, sub_zero, integral_exp_smul_mul_apply, Matrix.sub_apply, smul_smul, mul_comm t 2]
  have hint : ∫ u in (0 : ℝ)..t, 2 * ‖opCLM A‖ * ∑ s ∈ X, ∑ s' ∈ Yᶜ,
      (NormedSpace.exp ((t - u) • ((2 : ℝ) • M)) * ((2 : ℝ) • M)) s s' / 2 =
      ‖opCLM A‖ * ∑ s ∈ X, ∑ s' ∈ Yᶜ, (NormedSpace.exp ((2 * t) • M) - 1) s s' := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      (fun s _ => (continuous_finsetSum _ fun s' _ => hEc' s s').intervalIntegrable 0 t)]
    simp only [fun s => intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume) (a := 0) (b := t)
      (s := Yᶜ) (fun s' _ => (hEc' s s').intervalIntegrable 0 t), hone]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  have hrow : ∀ s ∈ X, ∑ s' ∈ Yᶜ, (NormedSpace.exp ((2 * t) • M) - 1) s s' ≤
      Real.exp (-ρ / lam) * (Real.exp (2 * C₁ * t) - 1) := by
    intro s hs
    have h := (rowSum_exp_chainMatrix_le Ψ hlam s Yᶜ t).2
    rw [abs_of_nonneg ht, ← hMdef] at h
    refine h.trans ?_
    have hCw := chainWeight_nonneg Ψ lam
    have he1 : Real.exp (2 * t * chainWeight Ψ lam) - 1 ≤ Real.exp (2 * C₁ * t) - 1 := by
      have : 2 * t * chainWeight Ψ lam ≤ 2 * C₁ * t := by nlinarith
      linarith [Real.exp_le_exp.mpr this]
    have he0 : 0 ≤ Real.exp (2 * t * chainWeight Ψ lam) - 1 := by
      have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * t * chainWeight Ψ lam)
      linarith
    rw [mul_comm (Real.exp (-ρ / lam))]
    exact mul_le_mul he1 (expNegDiv_compl_fat_le hlam hρ hs) (expNegDiv_nonneg _ _) (he0.trans he1)
  calc ‖opCLM (dyn (hamTot Ψ) t A - dyn (hamOn Ψ Y) t A)‖ ≤ _ := h1
    _ ≤ _ := h2
    _ = ‖opCLM A‖ * ∑ s ∈ X, ∑ s' ∈ Yᶜ, (NormedSpace.exp ((2 * t) • M) - 1) s s' := hint
    _ ≤ ‖opCLM A‖ * ∑ s ∈ X, Real.exp (-ρ / lam) * (Real.exp (2 * C₁ * t) - 1) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end LocalizationSlots


open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op c chat parityOp IsEven CAR Alg condExp)

section DiscDevices

/-- Device: the closed Euclidean disc of radius `r` about `0` in `ℝ × ℝ`. -/
def discE (r : ℝ) : Set (ℝ × ℝ) := {ξ | ξ.1 ^ 2 + ξ.2 ^ 2 ≤ r ^ 2}

theorem measurableSet_discE (r : ℝ) : MeasurableSet (discE r) :=
  measurableSet_le ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)) measurable_const

theorem volume_discE {r : ℝ} (hr : 0 ≤ r) : volume (discE r) = ENNReal.ofReal (π * r ^ 2) := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage (measurableSet_discE r).nullMeasurableSet
  rw [← h]
  have e : Complex.measurableEquivRealProd ⁻¹' discE r = Metric.closedBall (0 : ℂ) r := by
    ext z
    simp only [Set.mem_preimage, discE, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    show z.re ^ 2 + z.im ^ 2 ≤ r ^ 2 ↔ ‖z‖ ≤ r
    rw [← sq_le_sq₀ (norm_nonneg z) hr, Complex.sq_norm, Complex.normSq_apply]
    constructor <;> intro h <;> nlinarith
  rw [e, Complex.volume_closedBall, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  ring

theorem int_eq_of_mem_Ico {a b : ℤ} {L x : ℝ} (hL : 0 < L) (h1 : 0 ≤ x - a * L) (h2 : x - a * L < L)
    (h3 : 0 ≤ x - b * L) (h4 : x - b * L < L) : a = b := by
  have e1 : ((a : ℝ) - b) * L = (x - b * L) - (x - a * L) := by ring
  have e2 : ((b : ℝ) - a) * L = (x - a * L) - (x - b * L) := by ring
  have h5 : ((a : ℝ) - b) * L < L := by rw [e1]; linarith
  have h6 : ((b : ℝ) - a) * L < L := by rw [e2]; linarith
  have h7 : (a : ℝ) - b < 1 := by nlinarith
  have h8 : (b : ℝ) - a < 1 := by nlinarith
  have h9 : a - b < 1 := by exact_mod_cast h7
  have h10 : b - a < 1 := by exact_mod_cast h8
  omega

/-- Device (the proof of Theorem 5.3: the disc of radius `r` of the torus "`has measure at most $\pi r^2$, being the image
of a planar disc of radius $r$ under the covering map`"), for the part of the disc in the fundamental domain. -/
theorem volume_fundDom_inter_disc_le (T : Torus) (c : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (fundDom T ∩ {R | flatDist T c R ≤ r}) ≤ ENNReal.ofReal (π * r ^ 2) := by
  set v : ℤ × ℤ → ℝ × ℝ := fun p => ((p.1 : ℝ) * T.Lx, (p.2 : ℝ) * T.Ly) with hv
  set A : ℤ × ℤ → Set (ℝ × ℝ) := fun p => fundDom T ∩ {R | R - (c - v p) ∈ discE r} with hA
  set G : ℤ × ℤ → Set (ℝ × ℝ) := fun p => {ξ | (c - v p) + ξ ∈ fundDom T} ∩ discE r with hG
  have hcover : fundDom T ∩ {R | flatDist T c R ≤ r} ⊆ ⋃ p, A p := by
    rintro R ⟨hRD, hR⟩
    simp only [Set.mem_setOf_eq] at hR
    have e1 : pdist T.Lx (c.1 - R.1) = |(c.1 - R.1) - round (T.Lx⁻¹ * (c.1 - R.1)) * T.Lx| := by
      unfold pdist
      exact HRTorus.SlotFrame.Analysis.infDist_zmultiples_eq _ _
    have e2 : pdist T.Ly (c.2 - R.2) = |(c.2 - R.2) - round (T.Ly⁻¹ * (c.2 - R.2)) * T.Ly| := by
      unfold pdist
      exact HRTorus.SlotFrame.Analysis.infDist_zmultiples_eq _ _
    have hsq : pdist T.Lx (c.1 - R.1) ^ 2 + pdist T.Ly (c.2 - R.2) ^ 2 ≤ r ^ 2 := by
      have h0 : 0 ≤ pdist T.Lx (c.1 - R.1) ^ 2 + pdist T.Ly (c.2 - R.2) ^ 2 := by positivity
      have h1 := Real.sq_sqrt h0
      unfold flatDist at hR
      rw [← h1]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hR 2
    rw [e1, e2, sq_abs, sq_abs] at hsq
    refine Set.mem_iUnion.mpr ⟨(round (T.Lx⁻¹ * (c.1 - R.1)), round (T.Ly⁻¹ * (c.2 - R.2))), hRD, ?_⟩
    simp only [Set.mem_setOf_eq, discE, hv, Prod.fst_sub, Prod.snd_sub]
    nlinarith
  have hmeasA : ∀ p, volume (A p) = volume (G p) := by
    intro p
    rw [← measure_preimage_add volume (c - v p) (A p)]
    congr 1
    ext ξ
    simp only [hA, hG, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, add_sub_cancel_left]
  have hdisj : Pairwise (Function.onFun Disjoint G) := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    rintro ξ ⟨hp, -⟩ ⟨hq, -⟩
    apply hpq
    simp only [Set.mem_setOf_eq, fundDom, Set.mem_prod, Set.mem_Ico, hv, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub] at hp hq
    have h1 : p.1 = q.1 := int_eq_of_mem_Ico (x := c.1 + ξ.1) T.Lx_pos (by linarith [hp.1.1]) (by linarith [hp.1.2])
      (by linarith [hq.1.1]) (by linarith [hq.1.2])
    have h2 : p.2 = q.2 := int_eq_of_mem_Ico (x := c.2 + ξ.2) T.Ly_pos (by linarith [hp.2.1]) (by linarith [hp.2.2])
      (by linarith [hq.2.1]) (by linarith [hq.2.2])
    exact Prod.ext h1 h2
  have hmeasG : ∀ p, MeasurableSet (G p) := by
    intro p
    refine MeasurableSet.inter ?_ (measurableSet_discE r)
    exact (measurable_const_add (c - v p)) ((measurableSet_Ico).prod measurableSet_Ico)
  calc volume (fundDom T ∩ {R | flatDist T c R ≤ r}) ≤ volume (⋃ p, A p) := measure_mono hcover
    _ ≤ ∑' p, volume (A p) := measure_iUnion_le _
    _ = ∑' p, volume (G p) := by simp only [hmeasA]
    _ = volume (⋃ p, G p) := (measure_iUnion hdisj hmeasG).symm
    _ ≤ volume (discE r) := measure_mono (Set.iUnion_subset fun p => Set.inter_subset_right)
    _ = ENNReal.ofReal (π * r ^ 2) := volume_discE hr

theorem measureReal_fundDom_inter_disc_le (T : Torus) (c : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (fundDom T ∩ {R | flatDist T c R ≤ r}) ≤ π * r ^ 2 :=
  ENNReal.toReal_le_of_le_ofReal (by positivity) (volume_fundDom_inter_disc_le T c hr)

end DiscDevices

section NumericDevices

theorem exp_neg_one_le_two_fifths : Real.exp (-1) ≤ 2 / 5 := by
  have h := Real.exp_one_gt_d9
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  norm_num
  linarith

/-- Device (Step 4): `Σ_{n<K} e^{−n}(n+3)² ≤ 26`. -/
theorem sum_exp_neg_mul_sq_le (K : ℕ) :
    ∑ n ∈ Finset.range K, Real.exp (-(n : ℝ)) * ((n : ℝ) + 3) ^ 2 ≤ 26 := by
  have he := exp_neg_one_le_two_fifths
  have key : ∀ K : ℕ, ∑ n ∈ Finset.range K, Real.exp (-(n : ℝ)) * ((n : ℝ) + 3) ^ 2 +
      Real.exp (-(K : ℝ)) * (2 * (K : ℝ) ^ 2 + 13 * K + 26) ≤ 26 := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have h1 : Real.exp (-((K + 1 : ℕ) : ℝ)) = Real.exp (-(K : ℝ)) * Real.exp (-1) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [h1]
      have hK : 0 < Real.exp (-(K : ℝ)) := Real.exp_pos _
      have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have hp : 0 ≤ Real.exp (-(K : ℝ)) * (2 * ((K : ℝ) + 1) ^ 2 + 13 * ((K : ℝ) + 1) + 26) := by positivity
      have hm := mul_le_mul_of_nonneg_left he hp
      push_cast
      nlinarith [mul_nonneg hK.le (sq_nonneg (K : ℝ)), mul_nonneg hK.le hK0]
  have := key K
  have h0 : 0 ≤ Real.exp (-(K : ℝ)) * (2 * (K : ℝ) ^ 2 + 13 * K + 26) := by positivity
  linarith

/-- Device (Step 4): `Σ_{j₀<j≤J} ρ^j ≤ ρ^{j₀}` for `0 ≤ ρ ≤ 1/2`. -/
theorem sum_Ioc_pow_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 2) (j₀ J : ℕ) :
    ∑ j ∈ Finset.Ioc j₀ J, ρ ^ j ≤ ρ ^ j₀ := by
  have key : ∀ d : ℕ, ∑ j ∈ Finset.Ioc j₀ (j₀ + d), ρ ^ j ≤ ρ ^ j₀ - ρ ^ (j₀ + d) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega), pow_succ]
      have hp : 0 ≤ ρ ^ (j₀ + d) := pow_nonneg h0 _
      nlinarith
  rcases le_or_gt J j₀ with h | h
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    exact pow_nonneg h0 _
  · have := key (J - j₀)
    rw [show j₀ + (J - j₀) = J by omega] at this
    have hp : 0 ≤ ρ ^ J := pow_nonneg h0 _
    linarith

/-- Device (Step 4): the shell domination `min{1, e^{−(d−q)/λ}} ≤ Σ_{n<K} e^{−n}[d ≤ q + (n+1)λ]` for `d ≤ q + Kλ`. -/
theorem min_one_exp_le_shells {q lam d : ℝ} (hlam : 0 < lam) {K : ℕ} (hK : 1 ≤ K) (hd : d ≤ q + K * lam) :
    min 1 (Real.exp (-(d - q) / lam)) ≤
      ∑ n ∈ Finset.range K, Real.exp (-(n : ℝ)) * (if d ≤ q + (n + 1) * lam then 1 else 0) := by
  obtain ⟨x, hx⟩ : ∃ x, x = (d - q) / lam := ⟨_, rfl⟩
  have hxl : x * lam = d - q := by rw [hx, div_mul_cancel₀ _ hlam.ne']
  have hex : -(d - q) / lam = -x := by rw [hx, neg_div]
  rw [hex]
  obtain ⟨m, hm⟩ : ∃ m, m = min ⌊x⌋₊ (K - 1) := ⟨_, rfl⟩
  have hmK : m ∈ Finset.range K := by
    rw [Finset.mem_range, hm]
    have := min_le_right ⌊x⌋₊ (K - 1)
    omega
  have hnn : ∀ n ∈ Finset.range K, 0 ≤ Real.exp (-(n : ℝ)) * (if d ≤ q + (n + 1) * lam then 1 else 0) := by
    intro n _
    refine mul_nonneg (Real.exp_pos _).le ?_
    split_ifs <;> norm_num
  have hdm : d ≤ q + ((m : ℝ) + 1) * lam := by
    rcases le_total ⌊x⌋₊ (K - 1) with h | h
    · rw [hm, min_eq_left h]
      have h1 := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one x) hlam
      linarith
    · rw [hm, min_eq_right h]
      have e : ((K - 1 : ℕ) : ℝ) + 1 = K := by
        rw [Nat.cast_sub hK]
        push_cast
        ring
      rw [e]
      exact hd
  have hwm : min 1 (Real.exp (-x)) ≤ Real.exp (-(m : ℝ)) := by
    rcases le_or_gt x 0 with hx0 | hx0
    · have hm0 : m = 0 := by
        rw [hm, Nat.floor_eq_zero.mpr (by linarith)]
        simp
      rw [hm0, Nat.cast_zero, neg_zero, Real.exp_zero]
      exact min_le_left _ _
    · have h1 : (m : ℝ) ≤ x := by
        have h2 : (m : ℝ) ≤ ⌊x⌋₊ := by
          rw [hm]
          exact_mod_cast min_le_left _ _
        exact h2.trans (Nat.floor_le hx0.le)
      exact (min_le_right _ _).trans (Real.exp_le_exp.mpr (by linarith))
  calc min 1 (Real.exp (-x)) ≤ Real.exp (-(m : ℝ)) * (if d ≤ q + (m + 1) * lam then 1 else 0) := by
        rw [if_pos hdm, mul_one]
        exact hwm
    _ ≤ _ := Finset.single_le_sum hnn hmK

end NumericDevices

section ParityDevices

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem isOdd_dyn {H A : Op S} (hH : IsEven H) (hA : IsOdd A) (s : ℝ) : IsOdd (dyn H s A) := by
  have h1 : Commute (NormedSpace.exp ((I * (s : ℂ)) • H)) parityOp := (hH.smul_left _).exp_left
  have h2 : Commute (NormedSpace.exp ((-(I * (s : ℂ))) • H)) parityOp := (hH.smul_left _).exp_left
  show dyn H s A * parityOp = -(parityOp * dyn H s A)
  simp only [dyn]
  set E1 := NormedSpace.exp ((I * (s : ℂ)) • H)
  set E2 := NormedSpace.exp ((-(I * (s : ℂ))) • H)
  have hA' : A * parityOp = -(parityOp * A) := hA
  calc E1 * A * E2 * parityOp = E1 * A * (E2 * parityOp) := by rw [mul_assoc]
    _ = E1 * A * (parityOp * E2) := by rw [h2.eq]
    _ = E1 * (A * parityOp) * E2 := by simp only [mul_assoc]
    _ = E1 * (-(parityOp * A)) * E2 := by rw [hA']
    _ = -((E1 * parityOp) * A * E2) := by simp only [mul_neg, neg_mul, mul_assoc]
    _ = -((parityOp * E1) * A * E2) := by rw [h1.eq]
    _ = -(parityOp * (E1 * A * E2)) := by simp only [mul_assoc]

end ParityDevices

section OpIntegralDevicesP

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem ms_integrableOn_entry {f : ℝ × ℝ → Op S} (hf : ∀ m m', Measurable fun R => f R m m') {C : ℝ}
    (hC : ∀ R, ‖opCLM (f R)‖ ≤ C) (T : Torus) : ∀ m m', IntegrableOn (fun R => f R m m') (fundDom T) := by
  intro m m'
  refine Measure.integrableOn_of_bounded (volume_fundDom_ne_top T) (hf m m').aestronglyMeasurable (M := C) ?_
  exact Filter.Eventually.of_forall fun R => (norm_entry_le _ m m').trans (hC R)

theorem ms_integrableOn_ite_const (T : Torus) {p : ℝ × ℝ → Prop} [DecidablePred p] (hp : MeasurableSet {R | p R})
    (c : ℝ) : IntegrableOn (fun R => if p R then c else 0) (fundDom T) := by
  refine Measure.integrableOn_of_bounded (volume_fundDom_ne_top T)
    (Measurable.ite hp measurable_const measurable_const).aestronglyMeasurable (M := |c|) ?_
  exact Filter.Eventually.of_forall fun R => by split_ifs <;> simp

theorem ms_setIntegral_ite_const (D : Set (ℝ × ℝ)) {p : ℝ × ℝ → Prop} [DecidablePred p]
    (hp : MeasurableSet {R | p R}) (c : ℝ) :
    ∫ R in D, (if p R then c else 0) = volume.real (D ∩ {R | p R}) * c := by
  have e : (fun R => if p R then c else 0) = {R | p R}.indicator (fun _ => c) := by
    funext R
    by_cases h : p R <;> simp [h]
  rw [e, setIntegral_indicator hp, setIntegral_const, smul_eq_mul]

theorem ms_opIntegral_sum {ι : Type*} (s : Finset ι) (D : Set (ℝ × ℝ)) (f : ι → ℝ × ℝ → Op S)
    (hf : ∀ i ∈ s, ∀ m m' : Conf S, IntegrableOn (fun R => f i R m m') D) :
    opIntegral D (fun R => ∑ i ∈ s, f i R) = ∑ i ∈ s, opIntegral D (f i) := by
  ext m m'
  simp only [opIntegral, Matrix.of_apply, Matrix.sum_apply]
  exact integral_finset_sum s fun i hi => hf i hi m m'

theorem ms_opIntegral_sub (D : Set (ℝ × ℝ)) (f g : ℝ × ℝ → Op S)
    (hf : ∀ m m' : Conf S, IntegrableOn (fun R => f R m m') D) (hg : ∀ m m' : Conf S, IntegrableOn (fun R => g R m m') D) :
    opIntegral D (fun R => f R - g R) = opIntegral D f - opIntegral D g := by
  ext m m'
  simp only [opIntegral, Matrix.of_apply, Matrix.sub_apply]
  exact integral_sub (hf m m') (hg m m')

theorem ms_opIntegral_comm (D : Set (ℝ × ℝ)) (f : ℝ × ℝ → Op S) (X : Op S)
    (hf : ∀ m m' : Conf S, IntegrableOn (fun R => f R m m') D) :
    opIntegral D (fun R => f R * X - X * f R) = opIntegral D f * X - X * opIntegral D f := by
  have h := opIntegral_map (LinearMap.mulRight ℂ X - LinearMap.mulLeft ℂ X) D f hf
  simp only [LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at h
  exact h.symm

theorem ms_opIntegral_conjTranspose (D : Set (ℝ × ℝ)) (f : ℝ × ℝ → Op S) :
    (opIntegral D f)ᴴ = opIntegral D fun R => (f R)ᴴ := by
  ext m m'
  simp only [opIntegral, Matrix.conjTranspose_apply, Matrix.of_apply]
  exact (integral_conj (f := fun R => f R m' m)).symm

theorem ms_isSelfAdjoint_opIntegral (D : Set (ℝ × ℝ)) {f : ℝ × ℝ → Op S} (hf : ∀ R, IsSelfAdjoint (f R)) :
    IsSelfAdjoint (opIntegral D f) := by
  show star (opIntegral D f) = opIntegral D f
  rw [Matrix.star_eq_conjTranspose, ms_opIntegral_conjTranspose]
  congr 1
  funext R
  rw [← Matrix.star_eq_conjTranspose]
  exact (hf R).star_eq

/-- Device: the conditional expectation `𝔼_Y` as a linear map (for the operator integrals of Theorem 5.3). -/
def condExpLMp (Y : Finset S) : Op S →ₗ[ℂ] Op S :=
  IsLinearMap.mk' (condExp Y) (Fermion.Pilot.JW.condExp_isLinearMap Y)

theorem ms_opIntegral_mem_Alg (D : Set (ℝ × ℝ)) (hDm : MeasurableSet D) (f : ℝ × ℝ → Op S)
    (hf : ∀ m m' : Conf S, IntegrableOn (fun R => f R m m') D) {Y : Finset S} (hY : ∀ R ∈ D, f R ∈ Alg Y) :
    opIntegral D f ∈ Alg Y := by
  have hE : condExp Y (opIntegral D f) = opIntegral D f := by
    have h := opIntegral_map (condExpLMp Y) D f hf
    simp only [condExpLMp, IsLinearMap.mk'_apply] at h
    rw [h]
    ext m m'
    simp only [opIntegral, Matrix.of_apply]
    refine setIntegral_congr_fun hDm fun R hR => ?_
    rw [Fermion.Pilot.JW.condExp_of_mem (hY R hR).1]
  have hP : opIntegral D f * parityOp = parityOp * opIntegral D f := by
    have h1 := opIntegral_map (LinearMap.mulRight ℂ (parityOp : Op S)) D f hf
    have h2 := opIntegral_map (LinearMap.mulLeft ℂ (parityOp : Op S)) D f hf
    simp only [LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at h1 h2
    rw [h1, h2]
    ext m m'
    simp only [opIntegral, Matrix.of_apply]
    refine setIntegral_congr_fun hDm fun R hR => ?_
    rw [(hY R hR).2.eq]
  refine ⟨?_, hP⟩
  rw [← hE]
  exact Fermion.Pilot.JW.condExp_mem Y _

theorem measurableSet_fundDom (T : Torus) : MeasurableSet (fundDom T) :=
  measurableSet_Ico.prod measurableSet_Ico

end OpIntegralDevicesP

section MultiscaleDevices

variable {δ₀ : ℝ} {T : Torus}

/-- Device: the inputs of Steps 1–4 of the proof of Theorem 5.3 at one torus: `g R = ι(h_R)` and the canonical
approximants `ht R r = h̃_{R,r}` with the properties of Step 0. -/
structure MSData (δ₀ : ℝ) (T : Torus) where
  g : ℝ × ℝ → Op (Slot δ₀ T)
  ht : ℝ × ℝ → ℝ → Op (Slot δ₀ T)
  Ch : ℝ
  CH : ℕ → ℝ
  g_sa : ∀ R, IsSelfAdjoint (g R)
  ht_mem : ∀ R r, ht R r ∈ Alg (slotBall δ₀ T R r)
  ht_sa : ∀ R r, IsSelfAdjoint (ht R r)
  ht_meas : ∀ r m m', Measurable fun R => ht R r m m'
  g_meas : ∀ m m', Measurable fun R => g R m m'
  ht_norm : ∀ R r, ‖opCLM (ht R r)‖ ≤ Ch
  g_norm : ∀ R, ‖opCLM (g R)‖ ≤ Ch
  approx : ∀ R r, 0 ≤ r → ∀ k : ℕ, ‖opCLM (g R - ht R r)‖ ≤ 2 * CH k * (1 + r) ^ (-(k : ℝ))
  top : ∃ J : ℕ, ∀ R j, J ≤ j → ht R (rj j) = g R

/-- Device: the dyadic pieces of Step 1, `ĥ^{(0)}_R := h̃_{R,r_0}` and `ĥ^{(j)}_R := h̃_{R,r_j} − h̃_{R,r_{j−1}}`. -/
def piece (ht : ℝ × ℝ → ℝ → Op (Slot δ₀ T)) (R : ℝ × ℝ) : ℕ → Op (Slot δ₀ T)
  | 0 => ht R (rj 0)
  | j + 1 => ht R (rj (j + 1)) - ht R (rj j)

theorem sum_piece (ht : ℝ × ℝ → ℝ → Op (Slot δ₀ T)) (R : ℝ × ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), piece ht R j = ht R (rj n) := by
  induction n with
  | zero => simp [piece]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [piece]
    abel

theorem rj_succ (j : ℕ) : rj (j + 1) = 2 * rj j := by
  unfold rj
  ring

theorem rj_pos (j : ℕ) : 0 < rj j := by
  unfold rj
  positivity

theorem rpow_neg_nat_eq {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : x ^ (-(k : ℝ)) = (x ^ k)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

theorem mem_slotBall' {R : ℝ × ℝ} {r : ℝ} {s : Slot δ₀ T} :
    s ∈ slotBall δ₀ T R r ↔ flatDist T (centre δ₀ T s) R ≤ r := by
  simp [slotBall]

theorem piece_mem (M : MSData δ₀ T) (R : ℝ × ℝ) (j : ℕ) : piece M.ht R j ∈ Alg (slotBall δ₀ T R (rj j)) := by
  cases j with
  | zero => exact M.ht_mem R _
  | succ j =>
    have hsub : slotBall δ₀ T R (rj j) ⊆ slotBall δ₀ T R (rj (j + 1)) := by
      intro s hs
      rw [mem_slotBall'] at hs ⊢
      rw [rj_succ]
      linarith [rj_pos j]
    have h1 := M.ht_mem R (rj (j + 1))
    have h2 := Alg_mono hsub (M.ht_mem R (rj j))
    exact ⟨sub_mem h1.1 h2.1, h1.2.sub_left h2.2⟩

theorem piece_sa (M : MSData δ₀ T) (R : ℝ × ℝ) (j : ℕ) : IsSelfAdjoint (piece M.ht R j) := by
  cases j with
  | zero => exact M.ht_sa R _
  | succ j => exact (M.ht_sa R _).sub (M.ht_sa R _)

theorem piece_meas (M : MSData δ₀ T) (j : ℕ) : ∀ m m', Measurable fun R => piece M.ht R j m m' := by
  intro m m'
  cases j with
  | zero => exact M.ht_meas _ m m'
  | succ j =>
    simp only [piece, Matrix.sub_apply]
    exact (M.ht_meas _ m m').sub (M.ht_meas _ m m')

theorem MSData.CH_nonneg (M : MSData δ₀ T) (k : ℕ) : 0 ≤ M.CH k := by
  have h := M.approx 0 0 le_rfl k
  rw [add_zero, Real.one_rpow, mul_one] at h
  linarith [norm_nonneg (opCLM (M.g 0 - M.ht 0 0))]

theorem MSData.Ch_nonneg (M : MSData δ₀ T) : 0 ≤ M.Ch := (norm_nonneg _).trans (M.g_norm 0)

theorem norm_piece_le_two (M : MSData δ₀ T) (R : ℝ × ℝ) (j : ℕ) : ‖opCLM (piece M.ht R j)‖ ≤ 2 * M.Ch := by
  have h0 := M.Ch_nonneg
  cases j with
  | zero => exact (M.ht_norm R _).trans (by linarith)
  | succ j =>
    simp only [piece]
    rw [opCLM_sub']
    exact (norm_sub_le _ _).trans (by linarith [M.ht_norm R (rj (j + 1)), M.ht_norm R (rj j)])

/-- Device (Step 1, the paper's `eq:loc-pieces`): `‖ĥ^{(j)}_R‖ ≤ c_k (1 + r_j)^{−k}`. -/
theorem norm_piece_le (M : MSData δ₀ T) (R : ℝ × ℝ) (j k : ℕ) :
    ‖opCLM (piece M.ht R j)‖ ≤ ck M.Ch (M.CH k) k * (1 + rj j) ^ (-(k : ℝ)) := by
  have hpos : ∀ i, 0 < 1 + rj i := fun i => by linarith [rj_pos i]
  rw [rpow_neg_nat_eq (hpos j).le]
  unfold ck
  have hCH := M.CH_nonneg k
  have hP : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  cases j with
  | zero =>
    have h1 : (1 : ℝ) + rj 0 = 2 := by
      unfold rj
      norm_num
    rw [h1]
    have h2 : (2 : ℝ) ^ k * max M.Ch (4 * M.CH k) * ((2 : ℝ) ^ k)⁻¹ = max M.Ch (4 * M.CH k) := by
      field_simp
    rw [h2]
    exact (M.ht_norm R _).trans (le_max_left _ _)
  | succ i =>
    have e : piece M.ht R (i + 1) = (M.g R - M.ht R (rj i)) - (M.g R - M.ht R (rj (i + 1))) := by
      simp only [piece]
      abel
    rw [e, opCLM_sub']
    have h1 := M.approx R (rj i) (rj_pos i).le k
    have h2 := M.approx R (rj (i + 1)) (rj_pos (i + 1)).le k
    rw [rpow_neg_nat_eq (hpos i).le] at h1
    rw [rpow_neg_nat_eq (hpos (i + 1)).le] at h2
    set a := (1 + rj i) ^ k with ha
    set b := (1 + rj (i + 1)) ^ k with hb
    have ha0 : 0 < a := pow_pos (hpos i) k
    have hb0 : 0 < b := pow_pos (hpos (i + 1)) k
    have h4 : b ≤ 2 ^ k * a := by
      rw [ha, hb, ← mul_pow]
      exact pow_le_pow_left₀ (hpos _).le (by rw [rj_succ]; linarith) k
    have h3 : a⁻¹ ≤ 2 ^ k * b⁻¹ := by
      have e2 : a⁻¹ = 2 ^ k * (2 ^ k * a)⁻¹ := by
        field_simp
      rw [e2]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hb0 h4) (by positivity)
    have hbinv : 0 ≤ b⁻¹ := (inv_pos.mpr hb0).le
    have h5 : M.CH k * a⁻¹ ≤ M.CH k * (2 ^ k * b⁻¹) := mul_le_mul_of_nonneg_left h3 hCH
    have h6 : 4 * M.CH k * (2 ^ k * b⁻¹) ≤ max M.Ch (4 * M.CH k) * (2 ^ k * b⁻¹) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have h7 : M.CH k * b⁻¹ ≤ M.CH k * (2 ^ k * b⁻¹) := by
      have : b⁻¹ ≤ 2 ^ k * b⁻¹ := le_mul_of_one_le_left hbinv hP
      exact mul_le_mul_of_nonneg_left this hCH
    calc ‖opCLM (M.g R - M.ht R (rj i)) - opCLM (M.g R - M.ht R (rj (i + 1)))‖
        ≤ ‖opCLM (M.g R - M.ht R (rj i))‖ + ‖opCLM (M.g R - M.ht R (rj (i + 1)))‖ := norm_sub_le _ _
      _ ≤ 2 * M.CH k * a⁻¹ + 2 * M.CH k * b⁻¹ := add_le_add h1 h2
      _ ≤ 4 * M.CH k * (2 ^ k * b⁻¹) := by nlinarith
      _ ≤ max M.Ch (4 * M.CH k) * (2 ^ k * b⁻¹) := h6
      _ = 2 ^ k * max M.Ch (4 * M.CH k) * b⁻¹ := by ring

/-- Device: the integrand `R ↦ [Ball(r_j, R) = Z] ĥ^{(j)}_R` of `Ψ_λ(Z)`. -/
def psiIntegrand (M : MSData δ₀ T) (j : ℕ) (Z : Finset (Slot δ₀ T)) (R : ℝ × ℝ) : Op (Slot δ₀ T) :=
  if slotBall δ₀ T R (rj j) = Z then piece M.ht R j else 0

/-- Device (Step 1): the multiscale interaction `Ψ_λ(Z) := Σ_{j ≤ j₀} ∫ [Ball(r_j, R) = Z] ĥ^{(j)}_R dR` for
`λ = r_{j₀}` (the paper sums to `min{j₀, j_max}`; the pieces with `j > j_max` vanish). -/
def PsiL (M : MSData δ₀ T) (j₀ : ℕ) (Z : Finset (Slot δ₀ T)) : Op (Slot δ₀ T) :=
  ∑ j ∈ Finset.range (j₀ + 1), opIntegral (fundDom T) (psiIntegrand M j Z)

theorem psiIntegrand_meas (M : MSData δ₀ T) (j : ℕ) (Z : Finset (Slot δ₀ T)) :
    ∀ m m', Measurable fun R => psiIntegrand M j Z R m m' := by
  intro m m'
  have e : (fun R => psiIntegrand M j Z R m m') =
      fun R => if slotBall δ₀ T R (rj j) = Z then piece M.ht R j m m' else 0 := by
    funext R
    unfold psiIntegrand
    split_ifs <;> simp
  rw [e]
  exact Measurable.ite (measurableSet_slotBall_eq δ₀ T (rj j) Z) (piece_meas M j m m') measurable_const

theorem norm_psiIntegrand_le (M : MSData δ₀ T) (j : ℕ) (Z : Finset (Slot δ₀ T)) (R : ℝ × ℝ) (k : ℕ) :
    ‖opCLM (psiIntegrand M j Z R)‖ ≤
      if slotBall δ₀ T R (rj j) = Z then ck M.Ch (M.CH k) k * (1 + rj j) ^ (-(k : ℝ)) else 0 := by
  unfold psiIntegrand
  split_ifs
  · exact norm_piece_le M R j k
  · simp [opCLM_zero']

theorem norm_psiIntegrand_le_two (M : MSData δ₀ T) (j : ℕ) (Z : Finset (Slot δ₀ T)) (R : ℝ × ℝ) :
    ‖opCLM (psiIntegrand M j Z R)‖ ≤ 2 * M.Ch := by
  unfold psiIntegrand
  split_ifs
  · exact norm_piece_le_two M R j
  · simp only [opCLM_zero', norm_zero]
    linarith [M.Ch_nonneg]

theorem psiIntegrand_int (M : MSData δ₀ T) (j : ℕ) (Z : Finset (Slot δ₀ T)) :
    ∀ m m', IntegrableOn (fun R => psiIntegrand M j Z R m m') (fundDom T) :=
  ms_integrableOn_entry (psiIntegrand_meas M j Z) (norm_psiIntegrand_le_two M j Z) T

theorem piece_int (M : MSData δ₀ T) (j : ℕ) :
    ∀ m m', IntegrableOn (fun R => piece M.ht R j m m') (fundDom T) :=
  ms_integrableOn_entry (piece_meas M j) (fun R => norm_piece_le_two M R j) T

/-- Device (Step 1): "`so $\Psi$ and $\Psi_\lambda$ are even interactions`". -/
theorem PsiL_isEvenInteraction (M : MSData δ₀ T) (j₀ : ℕ) : IsEvenInteraction (PsiL M j₀) := by
  intro Z
  refine ⟨isSelfAdjoint_sum _ fun j _ => ms_isSelfAdjoint_opIntegral _ fun R => ?_,
    Alg_sum_mem _ _ fun j _ => ?_⟩
  · unfold psiIntegrand
    split_ifs
    · exact piece_sa M R j
    · exact IsSelfAdjoint.zero _
  · refine ms_opIntegral_mem_Alg _ (measurableSet_fundDom T) _ (psiIntegrand_int M j Z) fun R _ => ?_
    unfold psiIntegrand
    split_ifs with h
    · rw [← h]
      exact piece_mem M R j
    · exact Alg_zero_mem Z

/-- Device (Step 1): "`Put $\Hhat_\lambda:=\sum_Z\Psi_\lambda(Z)=\int\tilde h_{R,r_{\min\{j_0,j_{\max}\}}}\dd R$`". -/
theorem hamTot_PsiL (M : MSData δ₀ T) (j₀ : ℕ) :
    hamTot (PsiL M j₀) = opIntegral (fundDom T) fun R => M.ht R (rj j₀) := by
  unfold hamTot PsiL
  rw [Finset.sum_comm]
  have h1 : ∀ j, ∑ Z : Finset (Slot δ₀ T), opIntegral (fundDom T) (psiIntegrand M j Z) =
      opIntegral (fundDom T) (fun R => piece M.ht R j) := by
    intro j
    rw [← ms_opIntegral_sum _ _ _ fun Z _ => psiIntegrand_int M j Z]
    congr 1
    funext R
    simp only [psiIntegrand]
    rw [Finset.sum_ite_eq]
    simp
  simp only [h1]
  rw [← ms_opIntegral_sum _ _ _ fun j _ => piece_int M j]
  congr 1
  funext R
  exact sum_piece M.ht R j₀

theorem flatDist_comm_p (T : Torus) (a b : ℝ × ℝ) : flatDist T a b = flatDist T b a := by
  simp only [flatDist]
  rw [← neg_sub a.1, ← neg_sub a.2, pdist_neg, pdist_neg]

/-- Device (Step 2): `M_{ss'} ≤ Σ_{j ≤ j₀} c_5 (1 + r_j)^{−5} π r_j² [d(s, s') ≤ 2r_j]`. -/
theorem chainMatrix_PsiL_le (M : MSData δ₀ T) (j₀ : ℕ) (s s' : Slot δ₀ T) :
    chainMatrix (PsiL M j₀) s s' ≤
      ∑ j ∈ Finset.range (j₀ + 1), ck M.Ch (M.CH 5) 5 * (1 + rj j) ^ (-(5 : ℝ)) * (π * rj j ^ 2) *
        (if slotDist δ₀ T s s' ≤ 2 * rj j then 1 else 0) := by
  set c : ℕ → ℝ := fun j => ck M.Ch (M.CH 5) 5 * (1 + rj j) ^ (-(5 : ℝ)) with hc
  have hc0 : ∀ j, 0 ≤ c j := by
    intro j
    simp only [hc, ck]
    have := M.Ch_nonneg
    exact mul_nonneg (mul_nonneg (by positivity) (le_max_of_le_left this))
      (Real.rpow_nonneg (by linarith [rj_pos j]) _)
  set F := Finset.univ.filter (fun Z : Finset (Slot δ₀ T) => s ∈ Z ∧ s' ∈ Z) with hF
  have hZj : ∀ j (Z : Finset (Slot δ₀ T)), ‖opCLM (opIntegral (fundDom T) (psiIntegrand M j Z))‖ ≤
      ∫ R in fundDom T, (if slotBall δ₀ T R (rj j) = Z then c j else 0) := by
    intro j Z
    rw [opCLM_opIntegral _ _ (psiIntegrand_int M j Z)]
    exact norm_integral_le_of_norm_le (ms_integrableOn_ite_const T (measurableSet_slotBall_eq δ₀ T (rj j) Z) (c j))
      (Filter.Eventually.of_forall fun R => norm_psiIntegrand_le M j Z R 5)
  have hZ : ∀ Z : Finset (Slot δ₀ T), ‖opCLM (PsiL M j₀ Z)‖ ≤
      ∑ j ∈ Finset.range (j₀ + 1), ∫ R in fundDom T, (if slotBall δ₀ T R (rj j) = Z then c j else 0) := by
    intro Z
    unfold PsiL
    rw [opCLM_sum']
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hZj j Z)
  have hmeasE : ∀ j, MeasurableSet {R : ℝ × ℝ | slotBall δ₀ T R (rj j) ∈ F} := by
    intro j
    have e : {R : ℝ × ℝ | slotBall δ₀ T R (rj j) ∈ F} =
        {R | flatDist T (centre δ₀ T s) R ≤ rj j} ∩ {R | flatDist T (centre δ₀ T s') R ≤ rj j} := by
      ext R
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and, mem_slotBall', Set.mem_setOf_eq,
        Set.mem_inter_iff]
    rw [e]
    exact (measurableSet_le (continuous_flatDist_right T _).measurable measurable_const).inter
      (measurableSet_le (continuous_flatDist_right T _).measurable measurable_const)
  have hvol : ∀ j, volume.real (fundDom T ∩ {R : ℝ × ℝ | slotBall δ₀ T R (rj j) ∈ F}) ≤
      π * rj j ^ 2 * (if slotDist δ₀ T s s' ≤ 2 * rj j then 1 else 0) := by
    intro j
    split_ifs with hd
    · rw [mul_one]
      refine (measureReal_mono ?_ ?_).trans (measureReal_fundDom_inter_disc_le T (centre δ₀ T s) (rj_pos j).le)
      · intro R hR
        refine ⟨hR.1, ?_⟩
        have h2 := hR.2
        simp only [hF, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and, mem_slotBall'] at h2
        exact h2.1
      · exact (measure_mono Set.inter_subset_left).trans_lt (volume_fundDom_ne_top T).lt_top |>.ne
    · rw [mul_zero]
      have hempty : fundDom T ∩ {R : ℝ × ℝ | slotBall δ₀ T R (rj j) ∈ F} = ∅ := by
        ext R
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ h2
        simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and, mem_slotBall'] at h2
        apply hd
        have h3 := flatDist_triangle (T := T) (centre δ₀ T s) R (centre δ₀ T s')
        rw [flatDist_comm_p T R (centre δ₀ T s')] at h3
        unfold slotDist
        linarith [h2.1, h2.2]
      rw [hempty, measureReal_empty]
  calc chainMatrix (PsiL M j₀) s s' = ∑ Z ∈ F, ‖opCLM (PsiL M j₀ Z)‖ := by
        simp only [chainMatrix, Matrix.of_apply, hF]
    _ ≤ ∑ Z ∈ F, ∑ j ∈ Finset.range (j₀ + 1),
          ∫ R in fundDom T, (if slotBall δ₀ T R (rj j) = Z then c j else 0) := Finset.sum_le_sum fun Z _ => hZ Z
    _ = ∑ j ∈ Finset.range (j₀ + 1), ∑ Z ∈ F,
          ∫ R in fundDom T, (if slotBall δ₀ T R (rj j) = Z then c j else 0) := Finset.sum_comm
    _ = ∑ j ∈ Finset.range (j₀ + 1), ∫ R in fundDom T, (if slotBall δ₀ T R (rj j) ∈ F then c j else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← integral_finset_sum _ fun Z _ =>
          ms_integrableOn_ite_const T (measurableSet_slotBall_eq δ₀ T (rj j) Z) (c j)]
        congr 1
        funext R
        rw [Finset.sum_ite_eq]
    _ = ∑ j ∈ Finset.range (j₀ + 1), volume.real (fundDom T ∩ {R : ℝ × ℝ | slotBall δ₀ T R (rj j) ∈ F}) * c j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact ms_setIntegral_ite_const _ (hmeasE j) (c j)
    _ ≤ ∑ j ∈ Finset.range (j₀ + 1), π * rj j ^ 2 * (if slotDist δ₀ T s s' ≤ 2 * rj j then 1 else 0) * c j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hvol j) (hc0 j)
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hc]
        ring

/-- Device (Step 2, the paper's `eq:loc-C1`): `C(Ψ_λ, λ) ≤ C_1`, uniformly in `λ` and `N`. -/
theorem chainWeight_PsiL_le (M : MSData δ₀ T) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (j₀ : ℕ) :
    chainWeight (PsiL M j₀) (2 ^ j₀) ≤ C1 δ₀ M.Ch (M.CH 5) := by
  have hCh := M.Ch_nonneg
  set c : ℕ → ℝ := fun j => ck M.Ch (M.CH 5) 5 * (1 + rj j) ^ (-(5 : ℝ)) * (π * rj j ^ 2) with hc
  have hc0 : ∀ j, 0 ≤ c j := by
    intro j
    simp only [hc, ck]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (le_max_of_le_left hCh))
      (Real.rpow_nonneg (by linarith [rj_pos j]) _)) (mul_nonneg Real.pi_pos.le (sq_nonneg _))
  have hlam : (0 : ℝ) < 2 ^ j₀ := by positivity
  have hCvol : 0 ≤ Cvol δ₀ := by
    unfold Cvol
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (le_trans zero_le_one (le_max_left _ _))
  refine Real.iSup_le (fun s => ?_) (C1_nonneg δ₀ hCh _)
  -- the row of `s`
  have hrow : ∀ s' : Slot δ₀ T, chainMatrix (PsiL M j₀) s s' * Real.exp (slotDist δ₀ T s s' / 2 ^ j₀) ≤
      ∑ j ∈ Finset.range (j₀ + 1), c j * Real.exp 2 * (if slotDist δ₀ T s s' ≤ 2 * rj j then 1 else 0) := by
    intro s'
    have h1 := chainMatrix_PsiL_le M j₀ s s'
    have he0 := Real.exp_pos (slotDist δ₀ T s s' / 2 ^ j₀)
    calc chainMatrix (PsiL M j₀) s s' * Real.exp (slotDist δ₀ T s s' / 2 ^ j₀)
        ≤ (∑ j ∈ Finset.range (j₀ + 1), c j * (if slotDist δ₀ T s s' ≤ 2 * rj j then 1 else 0)) *
            Real.exp (slotDist δ₀ T s s' / 2 ^ j₀) := mul_le_mul_of_nonneg_right h1 he0.le
      _ = ∑ j ∈ Finset.range (j₀ + 1), c j * ((if slotDist δ₀ T s s' ≤ 2 * rj j then 1 else 0) *
            Real.exp (slotDist δ₀ T s s' / 2 ^ j₀)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ ∑ j ∈ Finset.range (j₀ + 1), c j * (Real.exp 2 * (if slotDist δ₀ T s s' ≤ 2 * rj j then 1 else 0)) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (hc0 j)
          split_ifs with hd
          · rw [one_mul, mul_one]
            refine Real.exp_le_exp.mpr ?_
            have hjj : rj j ≤ 2 ^ j₀ := by
              unfold rj
              exact pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
            rw [div_le_iff₀ hlam]
            linarith
          · simp
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  have hcard : ∀ j, (Finset.univ.filter (fun s' : Slot δ₀ T => slotDist δ₀ T s s' ≤ 2 * rj j)).card ≤
      Cvol δ₀ * (1 + 2 * rj j) ^ 2 := by
    intro j
    have e : Finset.univ.filter (fun s' : Slot δ₀ T => slotDist δ₀ T s s' ≤ 2 * rj j) =
        slotBall δ₀ T (centre δ₀ T s) (2 * rj j) := by
      ext s'
      rw [Finset.mem_filter, mem_slotBall']
      simp only [Finset.mem_univ, true_and]
      unfold slotDist
      rw [flatDist_comm_p]
    rw [e]
    have h := card_slotBall_le hδ₀ hT (centre δ₀ T s) (by linarith [rj_pos j] : (0 : ℝ) ≤ 2 * rj j)
    exact h.1.trans h.2
  calc ∑ s' : Slot δ₀ T, chainMatrix (PsiL M j₀) s s' * Real.exp (slotDist δ₀ T s s' / 2 ^ j₀)
      ≤ ∑ s' : Slot δ₀ T, ∑ j ∈ Finset.range (j₀ + 1),
          c j * Real.exp 2 * (if slotDist δ₀ T s s' ≤ 2 * rj j then 1 else 0) := Finset.sum_le_sum fun s' _ => hrow s'
    _ = ∑ j ∈ Finset.range (j₀ + 1), c j * Real.exp 2 *
          ((Finset.univ.filter (fun s' : Slot δ₀ T => slotDist δ₀ T s s' ≤ 2 * rj j)).card : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum, Finset.sum_boole]
    _ ≤ ∑ j ∈ Finset.range (j₀ + 1), c j * Real.exp 2 * (Cvol δ₀ * (1 + 2 * rj j) ^ 2) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcard j) (mul_nonneg (hc0 j) (Real.exp_pos _).le)
    _ = Real.exp 2 * Cvol δ₀ * ∑ j ∈ Finset.range (j₀ + 1), c j * (1 + 2 * rj j) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ C1 δ₀ M.Ch (M.CH 5) := by
        unfold C1
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.exp_pos _).le hCvol)
        exact (summable_C1 _ _).sum_le_tsum _ (fun j _ => mul_nonneg (hc0 j) (sq_nonneg _))

end MultiscaleDevices

section Step4Devices

variable {δ₀ : ℝ} {T : Torus}

theorem flatDist_le_add (T : Torus) (a b : ℝ × ℝ) : flatDist T a b ≤ T.Lx + T.Ly := by
  unfold flatDist
  have h1 : pdist T.Lx (a.1 - b.1) ≤ T.Lx / 2 := by
    unfold pdist
    exact HRTorus.SlotFrame.Analysis.infDist_zmultiples_le_half T.Lx_pos _
  have h2 : pdist T.Ly (a.2 - b.2) ≤ T.Ly / 2 := by
    unfold pdist
    exact HRTorus.SlotFrame.Analysis.infDist_zmultiples_le_half T.Ly_pos _
  have h0 := pdist_nonneg T.Lx (a.1 - b.1)
  have h0' := pdist_nonneg T.Ly (a.2 - b.2)
  have hx := T.Lx_pos
  have hy := T.Ly_pos
  calc Real.sqrt (pdist T.Lx (a.1 - b.1) ^ 2 + pdist T.Ly (a.2 - b.2) ^ 2) ≤ Real.sqrt ((T.Lx + T.Ly) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = T.Lx + T.Ly := Real.sqrt_sq (by linarith)

theorem sum_Ioc_piece (ht : ℝ × ℝ → ℝ → Op (Slot δ₀ T)) (R : ℝ × ℝ) (j₀ d : ℕ) :
    ∑ j ∈ Finset.Ioc j₀ (j₀ + d), piece ht R j = ht R (rj (j₀ + d)) - ht R (rj j₀) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega), ih]
    simp only [piece]
    abel

theorem two_pow_rpow_eq (j₀ : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    ((2 : ℝ) ^ j₀) ^ (-((k : ℝ) - 2)) = (((2 : ℝ) ^ (k - 2))⁻¹) ^ j₀ := by
  have e : ((k : ℝ) - 2) = ((k - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk]
    norm_num
  rw [e, Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow, ← pow_mul, ← pow_mul, mul_comm]

theorem rho_le_half {k : ℕ} (hk : 3 ≤ k) : ((2 : ℝ) ^ (k - 2))⁻¹ ≤ 1 / 2 := by
  have h : (2 : ℝ) ≤ 2 ^ (k - 2) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [one_div]
  exact inv_anti₀ (by norm_num) h

theorem rpow_piece_le (j : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    (1 + rj j) ^ (-(k : ℝ)) * rj j ^ 2 ≤ (((2 : ℝ) ^ (k - 2))⁻¹) ^ j := by
  have hr := rj_pos j
  have hr0 : rj j ≠ 0 := hr.ne'
  rw [rpow_neg_nat_eq (by linarith)]
  have h1 : ((1 + rj j) ^ k)⁻¹ ≤ (rj j ^ k)⁻¹ :=
    inv_anti₀ (pow_pos hr k) (pow_le_pow_left₀ hr.le (by linarith) k)
  have h2 : (rj j ^ k)⁻¹ * rj j ^ 2 = (rj j ^ (k - 2))⁻¹ := by
    have e : rj j ^ k = rj j ^ (k - 2) * rj j ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    rw [e]
    field_simp
  have h3 : (rj j ^ (k - 2))⁻¹ = (((2 : ℝ) ^ (k - 2))⁻¹) ^ j := by
    unfold rj
    rw [inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  calc ((1 + rj j) ^ k)⁻¹ * rj j ^ 2 ≤ (rj j ^ k)⁻¹ * rj j ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = _ := by rw [h2, h3]

theorem min_one_sum_le {ι : Type*} (X : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    min 1 (∑ i ∈ X, a i) ≤ ∑ i ∈ X, min 1 (a i) := by
  by_cases h : ∃ i ∈ X, 1 ≤ a i
  · obtain ⟨i, hi, h1⟩ := h
    calc min 1 (∑ i ∈ X, a i) ≤ 1 := min_le_left _ _
      _ = min 1 (a i) := (min_eq_left h1).symm
      _ ≤ ∑ i ∈ X, min 1 (a i) :=
          Finset.single_le_sum (f := fun i => min 1 (a i)) (fun i _ => le_min zero_le_one (ha i)) hi
  · push_neg at h
    calc min 1 (∑ i ∈ X, a i) ≤ ∑ i ∈ X, a i := min_le_right _ _
      _ = ∑ i ∈ X, min 1 (a i) := Finset.sum_congr rfl fun i hi => (min_eq_right (h i hi).le).symm

/-- Device: the shell function `Σ_{n<K} e^{−n}[d(c, R) ≤ (r + aλ) + (n+1)λ]` of Step 4. -/
def shellFn (T : Torus) (lam a r : ℝ) (Kn : ℕ) (cpt R : ℝ × ℝ) : ℝ :=
  ∑ n ∈ Finset.range Kn, Real.exp (-(n : ℝ)) * (if flatDist T cpt R ≤ (r + a * lam) + (n + 1) * lam then 1 else 0)

theorem shellFn_integrable (T : Torus) (lam a r : ℝ) (Kn : ℕ) (cpt : ℝ × ℝ) :
    Integrable (shellFn T lam a r Kn cpt) (volume.restrict (fundDom T)) := by
  rw [show shellFn T lam a r Kn cpt = fun R => ∑ n ∈ Finset.range Kn, Real.exp (-(n : ℝ)) *
      (if flatDist T cpt R ≤ (r + a * lam) + (n + 1) * lam then (1 : ℝ) else 0) from rfl]
  refine integrable_finsetSum _ fun n _ => ?_
  exact Integrable.const_mul (ms_integrableOn_ite_const T
    (measurableSet_le (continuous_flatDist_right T _).measurable measurable_const) 1) _

/-- Device (Step 4): `min{1, e^{2C_1|t'|} e^{−d(s, Ball(r_j, R))/λ}} ≤ Σ_{n<K} e^{−n}[d(s, R) ≤ q + (n+1)λ]` with
`q := r_j + 2C_1|t'|λ`, for `K λ ≥ L_x + L_y`. -/
theorem min_le_shells_slot {lam a : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) {Kn : ℕ} (hKn : 1 ≤ Kn)
    (hKl : T.Lx + T.Ly ≤ Kn * lam) (s : Slot δ₀ T) (R : ℝ × ℝ) (r : ℝ) :
    min 1 (Real.exp a * expNegDiv (slotSetDist {s} (slotBall δ₀ T R r)) lam) ≤
      shellFn T lam a r Kn (centre δ₀ T s) R := by
  unfold shellFn
  have hnn : 0 ≤ ∑ n ∈ Finset.range Kn, Real.exp (-(n : ℝ)) *
      (if flatDist T (centre δ₀ T s) R ≤ (r + a * lam) + (n + 1) * lam then 1 else 0) := by
    refine Finset.sum_nonneg fun n _ => mul_nonneg (Real.exp_pos _).le ?_
    split_ifs <;> norm_num
  rcases Finset.eq_empty_or_nonempty (slotBall δ₀ T R r) with hb | hb
  · rw [hb, slotSetDist_empty_right, expNegDiv, if_pos rfl, mul_zero, min_eq_right zero_le_one]
    exact hnn
  · rw [slotSetDist_eq_inf' (Finset.singleton_nonempty s) hb]
    set x := ({s} ×ˢ slotBall δ₀ T R r).inf' ((Finset.singleton_nonempty s).product hb)
      (fun p => slotDist δ₀ T p.1 p.2) with hx
    have hx0 : 0 ≤ x := by
      rw [hx, Finset.le_inf'_iff]
      intro p _
      exact slotDist_nonneg' _ _
    have hxd : flatDist T (centre δ₀ T s) R - r ≤ x := by
      rw [hx, Finset.le_inf'_iff]
      rintro ⟨p1, p2⟩ hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
      simp only [Finset.mem_singleton] at h1 h2
      simp only
      rw [h1]
      rw [mem_slotBall'] at h2
      have h3 := flatDist_triangle (T := T) (centre δ₀ T s) (centre δ₀ T p2) R
      unfold slotDist
      linarith
    rw [expNegDiv_ofReal hx0]
    have hd : flatDist T (centre δ₀ T s) R ≤ (r + a * lam) + Kn * lam := by
      have h1 := flatDist_le_add T (centre δ₀ T s) R
      have h2 : 0 ≤ r + a * lam := by
        obtain ⟨s', hs'⟩ := hb
        rw [mem_slotBall'] at hs'
        have h0 : 0 ≤ flatDist T (centre δ₀ T s') R := Real.sqrt_nonneg _
        nlinarith [mul_nonneg ha hlam.le]
      linarith
    have hlam0 : lam ≠ 0 := hlam.ne'
    have he : Real.exp a * Real.exp (-x / lam) ≤ Real.exp (-(flatDist T (centre δ₀ T s) R - (r + a * lam)) / lam) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have e1 : -(flatDist T (centre δ₀ T s) R - (r + a * lam)) / lam =
          a - (flatDist T (centre δ₀ T s) R - r) / lam := by
        field_simp
        ring
      rw [e1, neg_div]
      have : (flatDist T (centre δ₀ T s) R - r) / lam ≤ x / lam := div_le_div_of_nonneg_right hxd hlam.le
      linarith
    exact (min_le_min_left 1 he).trans (min_one_exp_le_shells hlam hKn hd)

/-- Device (Step 4): the shell integral `∫_{𝕋_N} Σ_n e^{−n}[d(s,R) ≤ q + (n+1)λ] dR ≤ 8π r² (1 + x)²` for
`q = r + 2xλ`, `2λ ≤ r`, `x ≥ 0` (the paper's `2π(q+λ)² ≤ 8π r_j² (1 + C_1|t'|)²` with the exact integral replaced by
shells of width `λ`). -/
theorem integral_shells_le (T : Torus) (cpt : ℝ × ℝ) {lam rr x : ℝ} (hlam : 0 < lam) (h2 : 2 * lam ≤ rr)
    (hx : 0 ≤ x) (Kn : ℕ) :
    ∫ R in fundDom T, shellFn T lam (2 * x) rr Kn cpt R ≤ 8 * π * rr ^ 2 * (1 + x) ^ 2 := by
  simp only [shellFn]
  have hmeas : ∀ n : ℕ, MeasurableSet {R : ℝ × ℝ | flatDist T cpt R ≤ (rr + 2 * x * lam) + (n + 1) * lam} :=
    fun n => measurableSet_le (continuous_flatDist_right T _).measurable measurable_const
  have hint : ∀ n ∈ Finset.range Kn, Integrable (fun R => Real.exp (-(n : ℝ)) *
      (if flatDist T cpt R ≤ (rr + 2 * x * lam) + (n + 1) * lam then (1 : ℝ) else 0)) (volume.restrict (fundDom T)) :=
    fun n _ => (ms_integrableOn_ite_const T (hmeas n) 1).const_mul _
  rw [integral_finset_sum _ hint]
  have hrr : 0 < rr := by linarith
  have hterm : ∀ n ∈ Finset.range Kn, ∫ R in fundDom T, Real.exp (-(n : ℝ)) *
      (if flatDist T cpt R ≤ (rr + 2 * x * lam) + (n + 1) * lam then (1 : ℝ) else 0) ≤
      Real.exp (-(n : ℝ)) * ((n : ℝ) + 3) ^ 2 * (π * rr ^ 2 * (1 + x) ^ 2 / 4) := by
    intro n _
    rw [integral_const_mul, ms_setIntegral_ite_const _ (hmeas n), mul_one]
    have hq0 : 0 ≤ (rr + 2 * x * lam) + (n + 1) * lam := by positivity
    have hv := measureReal_fundDom_inter_disc_le T cpt hq0
    have hq : (rr + 2 * x * lam) + (n + 1) * lam ≤ rr * (1 + x) * ((n : ℝ) + 3) / 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [mul_le_mul_of_nonneg_left h2 hx, mul_nonneg hx hn, mul_nonneg hx hrr.le, mul_nonneg hn hrr.le,
        mul_nonneg (mul_nonneg hx hn) hrr.le]
    have hsq : ((rr + 2 * x * lam) + (n + 1) * lam) ^ 2 ≤ (rr * (1 + x) * ((n : ℝ) + 3) / 2) ^ 2 :=
      pow_le_pow_left₀ hq0 hq 2
    have he := Real.exp_pos (-(n : ℝ))
    calc Real.exp (-(n : ℝ)) * volume.real (fundDom T ∩
          {R : ℝ × ℝ | flatDist T cpt R ≤ (rr + 2 * x * lam) + (n + 1) * lam})
        ≤ Real.exp (-(n : ℝ)) * (π * ((rr + 2 * x * lam) + (n + 1) * lam) ^ 2) :=
          mul_le_mul_of_nonneg_left hv he.le
      _ ≤ Real.exp (-(n : ℝ)) * (π * (rr * (1 + x) * ((n : ℝ) + 3) / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq Real.pi_pos.le) he.le
      _ = Real.exp (-(n : ℝ)) * ((n : ℝ) + 3) ^ 2 * (π * rr ^ 2 * (1 + x) ^ 2 / 4) := by ring
  calc ∑ n ∈ Finset.range Kn, ∫ R in fundDom T, Real.exp (-(n : ℝ)) *
        (if flatDist T cpt R ≤ (rr + 2 * x * lam) + (n + 1) * lam then (1 : ℝ) else 0)
      ≤ ∑ n ∈ Finset.range Kn, Real.exp (-(n : ℝ)) * ((n : ℝ) + 3) ^ 2 * (π * rr ^ 2 * (1 + x) ^ 2 / 4) :=
        Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.range Kn, Real.exp (-(n : ℝ)) * ((n : ℝ) + 3) ^ 2) * (π * rr ^ 2 * (1 + x) ^ 2 / 4) := by
        rw [Finset.sum_mul]
    _ ≤ 26 * (π * rr ^ 2 * (1 + x) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right (sum_exp_neg_mul_sq_le Kn) (by positivity)
    _ ≤ 8 * π * rr ^ 2 * (1 + x) ^ 2 := by
        have : 0 ≤ π * rr ^ 2 * (1 + x) ^ 2 := by positivity
        nlinarith

theorem ms_int_comm {S : Type*} [Fintype S] [DecidableEq S] {D : Set (ℝ × ℝ)} {f : ℝ × ℝ → Op S}
    (hf : ∀ m m' : Conf S, IntegrableOn (fun R => f R m m') D) (X : Op S) :
    ∀ m m' : Conf S, IntegrableOn (fun R => (f R * X - X * f R) m m') D := by
  intro m m'
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  exact (integrable_finsetSum _ fun l _ => (hf m l).mul_const _).sub
    (integrable_finsetSum _ fun l _ => (hf l m').const_mul _)

/-- Device (Step 4): the commutator of a local piece `P ∈ Alg(Y)` with `τ^λ_{t'}(A)`, by the weighted bound of Theorem 5.2
and the trivial bound: `‖[P, τ^λ_{t'}(A)]‖ ≤ 2‖A‖ c_P Σ_{s∈X} min{1, e^{2C_1|t'|} e^{−d(s,Y)/λ}}`. -/
theorem comm_piece_le {Ψ : Finset (Slot δ₀ T) → Op (Slot δ₀ T)} (hΨ : IsEvenInteraction Ψ) {lam : ℝ} (hlam : 0 < lam)
    {C₁ : ℝ} (hCw : chainWeight Ψ lam ≤ C₁) {X : Finset (Slot δ₀ T)} {A : Op (Slot δ₀ T)} (hA : A ∈ CAR X) (τ : ℝ)
    {P : Op (Slot δ₀ T)} {Y : Finset (Slot δ₀ T)} (hP : P ∈ Alg Y) {cP : ℝ} (hcP : ‖opCLM P‖ ≤ cP) :
    ‖opCLM (P * dyn (hamTot Ψ) τ A - dyn (hamTot Ψ) τ A * P)‖ ≤
      2 * ‖opCLM A‖ * cP * ∑ s ∈ X, min 1 (Real.exp (2 * (C₁ * |τ|)) * expNegDiv (slotSetDist {s} Y) lam) := by
  have hB : ‖opCLM (dyn (hamTot Ψ) τ A)‖ = ‖opCLM A‖ := norm_dyn (isSelfAdjoint_hamTot hΨ) τ A
  have hA0 := norm_nonneg (opCLM A)
  have hP0 := norm_nonneg (opCLM P)
  have hcP0 : 0 ≤ cP := hP0.trans hcP
  have hAP : 0 ≤ 2 * ‖opCLM A‖ * ‖opCLM P‖ := mul_nonneg (mul_nonneg zero_le_two hA0) hP0
  have hAc : 0 ≤ 2 * ‖opCLM A‖ := mul_nonneg zero_le_two hA0
  have hE0 : ∀ s, 0 ≤ Real.exp (2 * (C₁ * |τ|)) * expNegDiv (slotSetDist {s} Y) lam :=
    fun s => mul_nonneg (Real.exp_pos _).le (expNegDiv_nonneg _ _)
  have h1 : ‖opCLM (P * dyn (hamTot Ψ) τ A - dyn (hamTot Ψ) τ A * P)‖ ≤ 2 * ‖opCLM A‖ * ‖opCLM P‖ * 1 := by
    have := norm_comm_le P (dyn (hamTot Ψ) τ A)
    rw [hB] at this
    linarith
  have h2 : ‖opCLM (P * dyn (hamTot Ψ) τ A - dyn (hamTot Ψ) τ A * P)‖ ≤
      2 * ‖opCLM A‖ * ‖opCLM P‖ * ∑ s ∈ X, Real.exp (2 * (C₁ * |τ|)) * expNegDiv (slotSetDist {s} Y) lam := by
    rw [norm_comm_swap]
    refine (lieb_robinson_weighted hΨ (Or.inl ⟨hA, hP⟩) hlam τ).trans ?_
    have hexp : Real.exp (2 * |τ| * chainWeight Ψ lam) ≤ Real.exp (2 * (C₁ * |τ|)) := by
      refine Real.exp_le_exp.mpr ?_
      have := abs_nonneg τ
      nlinarith
    have hs0 : 0 ≤ ∑ s ∈ X, expNegDiv (slotSetDist {s} Y) lam := Finset.sum_nonneg fun s _ => expNegDiv_nonneg _ _
    rw [← Finset.mul_sum]
    calc 2 * ‖opCLM A‖ * ‖opCLM P‖ * Real.exp (2 * |τ| * chainWeight Ψ lam) *
          ∑ s ∈ X, expNegDiv (slotSetDist {s} Y) lam
        ≤ 2 * ‖opCLM A‖ * ‖opCLM P‖ * Real.exp (2 * (C₁ * |τ|)) * ∑ s ∈ X, expNegDiv (slotSetDist {s} Y) lam :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hAP) hs0
      _ = _ := by ring
  have h3 : ‖opCLM (P * dyn (hamTot Ψ) τ A - dyn (hamTot Ψ) τ A * P)‖ ≤
      2 * ‖opCLM A‖ * ‖opCLM P‖ *
        min 1 (∑ s ∈ X, Real.exp (2 * (C₁ * |τ|)) * expNegDiv (slotSetDist {s} Y) lam) := by
    rw [mul_min_of_nonneg _ _ hAP]
    exact le_min h1 h2
  have h4 := min_one_sum_le X _ hE0
  have h5 : 0 ≤ min 1 (∑ s ∈ X, Real.exp (2 * (C₁ * |τ|)) * expNegDiv (slotSetDist {s} Y) lam) :=
    le_min zero_le_one (Finset.sum_nonneg fun s _ => hE0 s)
  calc _ ≤ _ := h3
    _ ≤ 2 * ‖opCLM A‖ * cP * ∑ s ∈ X, min 1 (Real.exp (2 * (C₁ * |τ|)) * expNegDiv (slotSetDist {s} Y) lam) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcP hAc) h4 h5 (mul_nonneg hAc hcP0)

/-- Device (Step 4, the per-time bound): for every `t'`,
`‖[Ĥ − Ĥ_λ, τ^λ_{t'}(A)]‖ ≤ 16π c_k ‖A‖ |X| λ^{−(k−2)} (1 + C_1|t'|)²`. -/
theorem norm_comm_tail_le (M : MSData δ₀ T) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (j₀ : ℕ) {k : ℕ} (hk : 3 ≤ k)
    {X : Finset (Slot δ₀ T)} {A : Op (Slot δ₀ T)} (hA : A ∈ CAR X) (τ : ℝ) :
    ‖opCLM ((opIntegral (fundDom T) M.g - hamTot (PsiL M j₀)) * dyn (hamTot (PsiL M j₀)) τ A -
        dyn (hamTot (PsiL M j₀)) τ A * (opIntegral (fundDom T) M.g - hamTot (PsiL M j₀)))‖ ≤
      16 * π * ck M.Ch (M.CH k) k * ‖opCLM A‖ * X.card * ((2 : ℝ) ^ j₀) ^ (-((k : ℝ) - 2)) *
        (1 + C1 δ₀ M.Ch (M.CH 5) * |τ|) ^ 2 := by
  have hΨ := PsiL_isEvenInteraction M j₀
  have hlam : (0 : ℝ) < 2 ^ j₀ := by positivity
  have hCh := M.Ch_nonneg
  have hC₁0 : 0 ≤ C1 δ₀ M.Ch (M.CH 5) := C1_nonneg δ₀ hCh _
  have hCw := chainWeight_PsiL_le M hδ₀ hT j₀
  have hck : 0 ≤ ck M.Ch (M.CH k) k := by
    unfold ck
    exact mul_nonneg (by positivity) (le_max_of_le_left hCh)
  have hx0 : 0 ≤ C1 δ₀ M.Ch (M.CH 5) * |τ| := mul_nonneg hC₁0 (abs_nonneg τ)
  have ha0 : 0 ≤ 2 * (C1 δ₀ M.Ch (M.CH 5) * |τ|) := by positivity
  have hA0 := norm_nonneg (opCLM A)
  obtain ⟨J, hJ⟩ := M.top
  obtain ⟨Kn, hKn1, hKl⟩ : ∃ Kn : ℕ, 1 ≤ Kn ∧ T.Lx + T.Ly ≤ Kn * (2 : ℝ) ^ j₀ := by
    refine ⟨⌈(T.Lx + T.Ly) / 2 ^ j₀⌉₊ + 1, Nat.le_add_left 1 _, ?_⟩
    have h1 := Nat.le_ceil ((T.Lx + T.Ly) / 2 ^ j₀)
    rw [div_le_iff₀ hlam] at h1
    push_cast
    nlinarith
  have hcj : ∀ j : ℕ, 0 ≤ ck M.Ch (M.CH k) k * (1 + rj j) ^ (-(k : ℝ)) :=
    fun j => mul_nonneg hck (Real.rpow_nonneg (by linarith [rj_pos j]) _)
  have hKint : ∀ m m', IntegrableOn (fun R => (∑ j ∈ Finset.Ioc j₀ (j₀ + J), piece M.ht R j) m m') (fundDom T) := by
    intro m m'
    simp only [Matrix.sum_apply]
    exact integrable_finsetSum _ fun j _ => piece_int M j m m'
  have htail : opIntegral (fundDom T) M.g - hamTot (PsiL M j₀) =
      opIntegral (fundDom T) (fun R => ∑ j ∈ Finset.Ioc j₀ (j₀ + J), piece M.ht R j) := by
    rw [hamTot_PsiL, ← ms_opIntegral_sub _ _ _ (ms_integrableOn_entry M.g_meas M.g_norm T)
      (ms_integrableOn_entry (M.ht_meas _) (fun R => M.ht_norm R _) T)]
    congr 1
    funext R
    rw [sum_Ioc_piece, hJ R (j₀ + J) (by omega)]
  rw [htail, ← ms_opIntegral_comm _ _ _ hKint, opCLM_opIntegral _ _ (ms_int_comm hKint _)]
  have hGint : Integrable (fun R => ∑ j ∈ Finset.Ioc j₀ (j₀ + J), ∑ s ∈ X,
      2 * ‖opCLM A‖ * (ck M.Ch (M.CH k) k * (1 + rj j) ^ (-(k : ℝ))) *
        shellFn T (2 ^ j₀) (2 * (C1 δ₀ M.Ch (M.CH 5) * |τ|)) (rj j) Kn (centre δ₀ T s) R)
      (volume.restrict (fundDom T)) :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun s _ => (shellFn_integrable T _ _ _ Kn _).const_mul _
  have hpt : ∀ R, ‖opCLM ((∑ j ∈ Finset.Ioc j₀ (j₀ + J), piece M.ht R j) * dyn (hamTot (PsiL M j₀)) τ A -
      dyn (hamTot (PsiL M j₀)) τ A * ∑ j ∈ Finset.Ioc j₀ (j₀ + J), piece M.ht R j)‖ ≤
      ∑ j ∈ Finset.Ioc j₀ (j₀ + J), ∑ s ∈ X, 2 * ‖opCLM A‖ * (ck M.Ch (M.CH k) k * (1 + rj j) ^ (-(k : ℝ))) *
        shellFn T (2 ^ j₀) (2 * (C1 δ₀ M.Ch (M.CH 5) * |τ|)) (rj j) Kn (centre δ₀ T s) R := by
    intro R
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, opCLM_sum']
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have h1 := comm_piece_le hΨ hlam hCw hA τ (piece_mem M R j) (norm_piece_le M R j k)
    refine h1.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (hcj j))
    exact min_le_shells_slot hlam ha0 hKn1 hKl s R (rj j)
  refine (norm_integral_le_of_norm_le hGint (Filter.Eventually.of_forall hpt)).trans ?_
  beta_reduce
  rw [integral_finset_sum _ fun j _ => integrable_finsetSum _ fun s _ => (shellFn_integrable T _ _ _ Kn _).const_mul _]
  have hrho := rho_le_half hk
  have hrho0 : 0 ≤ ((2 : ℝ) ^ (k - 2))⁻¹ := by positivity
  calc ∑ j ∈ Finset.Ioc j₀ (j₀ + J), ∫ R in fundDom T, ∑ s ∈ X, 2 * ‖opCLM A‖ *
          (ck M.Ch (M.CH k) k * (1 + rj j) ^ (-(k : ℝ))) *
          shellFn T (2 ^ j₀) (2 * (C1 δ₀ M.Ch (M.CH 5) * |τ|)) (rj j) Kn (centre δ₀ T s) R
      ≤ ∑ j ∈ Finset.Ioc j₀ (j₀ + J), ∑ s ∈ X, 2 * ‖opCLM A‖ * (ck M.Ch (M.CH k) k * (1 + rj j) ^ (-(k : ℝ))) *
          (8 * π * rj j ^ 2 * (1 + C1 δ₀ M.Ch (M.CH 5) * |τ|) ^ 2) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [integral_finset_sum _ fun s _ => (shellFn_integrable T _ _ _ Kn _).const_mul _]
        refine Finset.sum_le_sum fun s _ => ?_
        rw [integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (hcj j))
        have hj' : j₀ + 1 ≤ j := (Finset.mem_Ioc.mp hj).1
        have h2 : 2 * (2 : ℝ) ^ j₀ ≤ rj j := by
          unfold rj
          calc (2 : ℝ) * 2 ^ j₀ = 2 ^ (j₀ + 1) := by ring
            _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj'
        exact integral_shells_le T (centre δ₀ T s) hlam h2 hx0 Kn
    _ = ∑ j ∈ Finset.Ioc j₀ (j₀ + J), 16 * π * ck M.Ch (M.CH k) k * ‖opCLM A‖ * X.card *
          (1 + C1 δ₀ M.Ch (M.CH 5) * |τ|) ^ 2 * ((1 + rj j) ^ (-(k : ℝ)) * rj j ^ 2) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ j ∈ Finset.Ioc j₀ (j₀ + J), 16 * π * ck M.Ch (M.CH k) k * ‖opCLM A‖ * X.card *
          (1 + C1 δ₀ M.Ch (M.CH 5) * |τ|) ^ 2 * (((2 : ℝ) ^ (k - 2))⁻¹) ^ j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (rpow_piece_le j (by omega)) (by positivity)
    _ = 16 * π * ck M.Ch (M.CH k) k * ‖opCLM A‖ * X.card * (1 + C1 δ₀ M.Ch (M.CH 5) * |τ|) ^ 2 *
          ∑ j ∈ Finset.Ioc j₀ (j₀ + J), (((2 : ℝ) ^ (k - 2))⁻¹) ^ j := by rw [Finset.mul_sum]
    _ ≤ 16 * π * ck M.Ch (M.CH k) k * ‖opCLM A‖ * X.card * (1 + C1 δ₀ M.Ch (M.CH 5) * |τ|) ^ 2 *
          (((2 : ℝ) ^ (k - 2))⁻¹) ^ j₀ :=
        mul_le_mul_of_nonneg_left (sum_Ioc_pow_le hrho0 hrho j₀ (j₀ + J)) (by positivity)
    _ = _ := by
        rw [two_pow_rpow_eq j₀ (by omega : 2 ≤ k)]
        ring

end Step4Devices

section AssemblyDevices

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem continuous_norm_comm_dyn_shift (P H' A : Op S) (g : ℝ → ℝ) (hg : Continuous g) :
    Continuous fun u => ‖opCLM (P * dyn H' (g u) A - dyn H' (g u) A * P)‖ := by
  have hc : Continuous fun u => opCLM (dyn H' (g u) A) := (continuous_opCLM_dyn H' A).comp hg
  have e : (fun u => ‖opCLM (P * dyn H' (g u) A - dyn H' (g u) A * P)‖) =
      fun u => ‖opCLM P * opCLM (dyn H' (g u) A) - opCLM (dyn H' (g u) A) * opCLM P‖ := by
    funext u
    rw [opCLM_sub', opCLM_mul', opCLM_mul']
  rw [e]
  fun_prop

/-- Device (Duhamel for both signs of the time, Steps 3–4: "`for $t<0$ the same estimates hold with $\int_0^t$ replaced
by $\int_t^0$`"): if `‖[H − H', τ^{H'}_τ(A)]‖ ≤ f(|τ|)` for all `τ`, then `‖τ^H_t(A) − τ^{H'}_t(A)‖ ≤ ∫_0^{|t|} f(|t| − u) du`. -/
theorem norm_dyn_sub_dyn_le_of_bound {H H' : Op S} (hH : IsSelfAdjoint H) (A : Op S) {f : ℝ → ℝ} (hf : Continuous f)
    (hb : ∀ τ : ℝ, ‖opCLM ((H - H') * dyn H' τ A - dyn H' τ A * (H - H'))‖ ≤ f |τ|) (t : ℝ) :
    ‖opCLM (dyn H t A - dyn H' t A)‖ ≤ ∫ u in (0 : ℝ)..|t|, f (|t| - u) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    refine (norm_dyn_sub_dyn_le hH A ht).trans ?_
    refine intervalIntegral.integral_mono_on ht
      ((continuous_norm_comm_dyn_shift _ H' A _ (continuous_const.sub continuous_id)).intervalIntegrable _ _)
      ((hf.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _) fun u hu => ?_
    have h := hb (t - u)
    rwa [abs_of_nonneg (by linarith [hu.2])] at h
  · have ht' : 0 ≤ -t := by linarith
    have h := norm_dyn_sub_dyn_le (H' := -H') hH.neg A ht'
    rw [dyn_neg_neg, dyn_neg_neg] at h
    rw [abs_of_neg ht]
    refine h.trans ?_
    refine intervalIntegral.integral_mono_on ht'
      ((continuous_norm_comm_dyn_shift _ (-H') A _ (continuous_const.sub continuous_id)).intervalIntegrable _ _)
      ((hf.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _) fun u hu => ?_
    have e1 : dyn (-H') (-t - u) A = dyn H' (t + u) A := by
      rw [show -t - u = -(t + u) by ring, dyn_neg_neg]
    have e2 : (-H - -H') * dyn H' (t + u) A - dyn H' (t + u) A * (-H - -H') =
        -((H - H') * dyn H' (t + u) A - dyn H' (t + u) A * (H - H')) := by noncomm_ring
    rw [e1, e2, opCLM_neg', norm_neg]
    have h2 := hb (t + u)
    rwa [abs_of_nonpos (by linarith [hu.2]), show -(t + u) = -t - u by ring] at h2

/-- Device (Step 4): `∫_0^{T} (1 + C_1 (T − u))² du ≤ (1 + C_1 T)³ / (3C_1)`. -/
theorem integral_one_add_mul_sq_le {C₁ Tt : ℝ} (hC : 0 < C₁) :
    ∫ u in (0 : ℝ)..Tt, (1 + C₁ * (Tt - u)) ^ 2 ≤ (1 + C₁ * Tt) ^ 3 / (3 * C₁) := by
  have hC0 : C₁ ≠ 0 := hC.ne'
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) Tt,
      HasDerivAt (fun u => -(1 + C₁ * (Tt - u)) ^ 3 / (3 * C₁)) ((1 + C₁ * (Tt - u)) ^ 2) u := by
    intro u _
    have h1 : HasDerivAt (fun u => 1 + C₁ * (Tt - u)) (C₁ * (-1)) u := by
      have := (((hasDerivAt_id u).const_sub Tt).const_mul C₁).const_add 1
      simpa using this
    have h2 := ((h1.pow 3).neg).div_const (3 * C₁)
    convert h2 using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun u => (1 + C₁ * (Tt - u)) ^ 2) MeasureTheory.volume 0 Tt := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  show -(1 + C₁ * (Tt - Tt)) ^ 3 / (3 * C₁) - -(1 + C₁ * (Tt - 0)) ^ 3 / (3 * C₁) ≤ (1 + C₁ * Tt) ^ 3 / (3 * C₁)
  have e : -(1 + C₁ * (Tt - Tt)) ^ 3 / (3 * C₁) - -(1 + C₁ * (Tt - 0)) ^ 3 / (3 * C₁) =
      (1 + C₁ * Tt) ^ 3 / (3 * C₁) - 1 / (3 * C₁) := by ring
  rw [e]
  have : 0 < 1 / (3 * C₁) := by positivity
  linarith

theorem op_eq_zero_of_norm_le_zero {X : Op S} (h : ‖opCLM X‖ ≤ 0) : X = 0 := by
  ext m m'
  have h1 := (norm_entry_le X m m').trans h
  rw [Matrix.zero_apply]
  exact norm_le_zero_iff.mp h1

theorem dyn_zero_ham (t : ℝ) (A : Op S) : dyn (0 : Op S) t A = A := by
  simp [dyn]

end AssemblyDevices

section AssemblySlots

variable {δ₀ : ℝ} {T : Torus}

/-- Device (Step 3 for both signs of the time): the localization bound with `|t|`. -/
theorem norm_dyn_sub_dyn_fat_le_abs {Ψ : Finset (Slot δ₀ T) → Op (Slot δ₀ T)} (hΨ : IsEvenInteraction Ψ)
    {lam C₁ : ℝ} (hlam : 0 < lam) (hC : chainWeight Ψ lam ≤ C₁) {ρ : ℝ} (hρ : 0 < ρ)
    {X : Finset (Slot δ₀ T)} {A : Op (Slot δ₀ T)} (hA : A ∈ CAR X) (t : ℝ) :
    ‖opCLM (dyn (hamTot Ψ) t A - dyn (hamOn Ψ (fat X ρ)) t A)‖ ≤
      ‖opCLM A‖ * X.card * (Real.exp (-ρ / lam) * (Real.exp (2 * C₁ * |t|) - 1)) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact norm_dyn_sub_dyn_fat_le hΨ hlam hC hρ hA ht
  · have hCn : chainWeight (fun Z => -Ψ Z) lam ≤ C₁ := by
      have e : chainWeight (fun Z => -Ψ Z) lam = chainWeight Ψ lam := by
        unfold chainWeight
        rw [chainMatrix_neg]
      rw [e]
      exact hC
    have h := norm_dyn_sub_dyn_fat_le (isEvenInteraction_neg hΨ) hlam hCn hρ hA (by linarith : (0 : ℝ) ≤ -t)
    have e2 : hamOn (fun Z => -Ψ Z) (fat X ρ) = -hamOn Ψ (fat X ρ) := by
      simp only [hamOn, Finset.sum_neg_distrib]
    rw [hamTot_neg, e2, dyn_neg_neg, dyn_neg_neg] at h
    rw [abs_of_neg ht]
    exact h

theorem C1_pos (δ₀ : ℝ) {Ch : ℝ} (hCh : 0 < Ch) (CH5 : ℝ) : 0 < C1 δ₀ Ch CH5 := by
  have hc0 : 0 < ck Ch CH5 5 := by
    unfold ck
    exact mul_pos (by norm_num) (lt_max_of_lt_left hCh)
  have hCvol : 0 < Cvol δ₀ := by
    unfold Cvol
    exact mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hnn : ∀ j, 0 ≤ ck Ch CH5 5 * (1 + rj j) ^ (-(5 : ℝ)) * (π * rj j ^ 2) * (1 + 2 * rj j) ^ 2 := fun j => by
    have hu := rj_nonneg j
    exact mul_nonneg (mul_nonneg (mul_nonneg hc0.le (Real.rpow_nonneg (by linarith) _))
      (mul_nonneg Real.pi_pos.le (pow_nonneg hu 2))) (pow_nonneg (by linarith) 2)
  have hterm : 0 < ck Ch CH5 5 * (1 + rj 0) ^ (-(5 : ℝ)) * (π * rj 0 ^ 2) * (1 + 2 * rj 0) ^ 2 := by
    have h1 : rj 0 = 1 := by
      unfold rj
      norm_num
    rw [h1]
    have h2 : 0 < (1 + (1 : ℝ)) ^ (-(5 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    exact mul_pos (mul_pos (mul_pos hc0 h2) (mul_pos Real.pi_pos (by norm_num))) (by norm_num)
  have hle := (summable_C1 Ch CH5).le_tsum 0 (fun j _ => hnn j)
  unfold C1
  exact mul_pos (mul_pos (Real.exp_pos _) hCvol) (lt_of_lt_of_le hterm hle)

/-- Device (Theorem 5.3(a), Steps 3 and 4 added): the master inequality for the data `M` at one torus. -/
theorem master_bound (M : MSData δ₀ T) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (j₀ : ℕ) {k : ℕ} (hk : 3 ≤ k)
    {ρ : ℝ} (hρ : 0 < ρ) {X : Finset (Slot δ₀ T)} {A : Op (Slot δ₀ T)} (hA : A ∈ CAR X) (t : ℝ) :
    ‖opCLM (dyn (opIntegral (fundDom T) M.g) t A - dyn (hamOn (PsiL M j₀) (fat X ρ)) t A)‖ ≤
      ‖opCLM A‖ * (X.card : ℝ) *
        (16 * π * ck M.Ch (M.CH k) k / (3 * C1 δ₀ M.Ch (M.CH 5)) * ((2 : ℝ) ^ j₀) ^ (-((k : ℝ) - 2)) *
            (1 + C1 δ₀ M.Ch (M.CH 5) * |t|) ^ 3 +
          Real.exp (-ρ / (2 : ℝ) ^ j₀) * (Real.exp (2 * C1 δ₀ M.Ch (M.CH 5) * |t|) - 1)) := by
  have hΨ := PsiL_isEvenInteraction M j₀
  have hlam : (0 : ℝ) < 2 ^ j₀ := by positivity
  have hCw := chainWeight_PsiL_le M hδ₀ hT j₀
  have hCh := M.Ch_nonneg
  have hC₁0 : 0 ≤ C1 δ₀ M.Ch (M.CH 5) := C1_nonneg δ₀ hCh _
  have hck : 0 ≤ ck M.Ch (M.CH k) k := by
    unfold ck
    exact mul_nonneg (by positivity) (le_max_of_le_left hCh)
  have hA0 := norm_nonneg (opCLM A)
  have hX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  have hpow0 : 0 ≤ ((2 : ℝ) ^ j₀) ^ (-((k : ℝ) - 2)) := Real.rpow_nonneg hlam.le _
  have hone : 0 ≤ 1 + C1 δ₀ M.Ch (M.CH 5) * |t| := by
    have := mul_nonneg hC₁0 (abs_nonneg t)
    linarith
  have h3 := norm_dyn_sub_dyn_fat_le_abs hΨ hlam hCw hρ hA t
  have h4 : ‖opCLM (dyn (opIntegral (fundDom T) M.g) t A - dyn (hamTot (PsiL M j₀)) t A)‖ ≤
      ‖opCLM A‖ * X.card * (16 * π * ck M.Ch (M.CH k) k / (3 * C1 δ₀ M.Ch (M.CH 5)) *
        ((2 : ℝ) ^ j₀) ^ (-((k : ℝ) - 2)) * (1 + C1 δ₀ M.Ch (M.CH 5) * |t|) ^ 3) := by
    rcases eq_or_lt_of_le hCh with h0 | hpos
    · have hg0 : ∀ R, M.g R = 0 := fun R => op_eq_zero_of_norm_le_zero (by rw [h0]; exact M.g_norm R)
      have ht0 : ∀ R r, M.ht R r = 0 := fun R r => op_eq_zero_of_norm_le_zero (by rw [h0]; exact M.ht_norm R r)
      have hI0 : opIntegral (fundDom T) M.g = 0 := by
        ext m m'
        simp [opIntegral, hg0]
      have hL0 : hamTot (PsiL M j₀) = 0 := by
        rw [hamTot_PsiL]
        ext m m'
        simp [opIntegral, ht0]
      rw [hI0, hL0, dyn_zero_ham, sub_self, opCLM_zero', norm_zero]
      have hdiv : 0 ≤ 16 * π * ck M.Ch (M.CH k) k / (3 * C1 δ₀ M.Ch (M.CH 5)) :=
        div_nonneg (mul_nonneg (by positivity) hck) (by linarith)
      exact mul_nonneg (mul_nonneg hA0 hX0) (mul_nonneg (mul_nonneg hdiv hpow0) (pow_nonneg hone 3))
    · have hC₁ := C1_pos δ₀ hpos (M.CH 5)
      have hHs : IsSelfAdjoint (opIntegral (fundDom T) M.g) := ms_isSelfAdjoint_opIntegral _ M.g_sa
      have hCst : 0 ≤ 16 * π * ck M.Ch (M.CH k) k * ‖opCLM A‖ * X.card * ((2 : ℝ) ^ j₀) ^ (-((k : ℝ) - 2)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hck) hA0) hX0) hpow0
      have hD := norm_dyn_sub_dyn_le_of_bound hHs A
        (f := fun v => 16 * π * ck M.Ch (M.CH k) k * ‖opCLM A‖ * X.card * ((2 : ℝ) ^ j₀) ^ (-((k : ℝ) - 2)) *
          (1 + C1 δ₀ M.Ch (M.CH 5) * v) ^ 2) (by fun_prop)
        (fun τ => norm_comm_tail_le M hδ₀ hT j₀ hk hA τ) t
      refine hD.trans ?_
      beta_reduce
      rw [intervalIntegral.integral_const_mul]
      have hI := integral_one_add_mul_sq_le (Tt := |t|) hC₁
      calc 16 * π * ck M.Ch (M.CH k) k * ‖opCLM A‖ * X.card * ((2 : ℝ) ^ j₀) ^ (-((k : ℝ) - 2)) *
            ∫ u in (0 : ℝ)..|t|, (1 + C1 δ₀ M.Ch (M.CH 5) * (|t| - u)) ^ 2
          ≤ 16 * π * ck M.Ch (M.CH k) k * ‖opCLM A‖ * X.card * ((2 : ℝ) ^ j₀) ^ (-((k : ℝ) - 2)) *
            ((1 + C1 δ₀ M.Ch (M.CH 5) * |t|) ^ 3 / (3 * C1 δ₀ M.Ch (M.CH 5))) :=
            mul_le_mul_of_nonneg_left hI hCst
        _ = _ := by ring
  calc ‖opCLM (dyn (opIntegral (fundDom T) M.g) t A - dyn (hamOn (PsiL M j₀) (fat X ρ)) t A)‖
      = ‖opCLM (dyn (opIntegral (fundDom T) M.g) t A - dyn (hamTot (PsiL M j₀)) t A) +
          opCLM (dyn (hamTot (PsiL M j₀)) t A - dyn (hamOn (PsiL M j₀) (fat X ρ)) t A)‖ := by
        rw [← opCLM_add', sub_add_sub_cancel]
    _ ≤ ‖opCLM (dyn (opIntegral (fundDom T) M.g) t A - dyn (hamTot (PsiL M j₀)) t A)‖ +
          ‖opCLM (dyn (hamTot (PsiL M j₀)) t A - dyn (hamOn (PsiL M j₀) (fat X ρ)) t A)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add h4 h3
    _ = _ := by ring

end AssemblySlots

section AssemblyData

variable {η : ℝ → ℝ} {δ₀ : ℝ} {Ts : TorusSeq δ₀} {H : (N : ℕ) → FockOp (Ts.T N)}

/-- Device: the data of Steps 1–4 at `N` from (H1): `g R = ι(h_R)` and the canonical approximants `h̃_{R,r}`. -/
def msdata (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) (N : ℕ) (hN : N ∈ Ts.idx) :
    MSData δ₀ (Ts.T N) where
  g R := iota η δ₀ (Ts.T N) (d.h N R)
  ht R r := hTilde d N R r
  Ch := d.Ch
  CH := d.CH
  g_sa R := by
    have hT := Ts.admissible N hN
    have hh : (d.h N R)ᴴ = d.h N R := d.h_isSelfAdjoint N hN R
    show star (iota η δ₀ (Ts.T N) (d.h N R)) = iota η δ₀ (Ts.T N) (d.h N R)
    rw [Matrix.star_eq_conjTranspose, ← iota_conjTranspose hη hδ₀ hT, hh]
  ht_mem R r := hTilde_mem_Alg hη hδ₀ d N hN R r
  ht_sa R r := hTilde_isSelfAdjoint hη hδ₀ d N hN R r
  ht_meas r := hTilde_measurable hη hδ₀ d N hN r
  g_meas := measurable_iota_entry (Ts.admissible N hN) hη hδ₀ (d.h_measurable N hN)
  ht_norm R r := (norm_hTilde_le hη hδ₀ d N hN R r).1.trans (norm_hTilde_le hη hδ₀ d N hN R r).2
  g_norm R := by
    rw [norm_iota hη hδ₀ (Ts.admissible N hN)]
    exact d.norm_h_le N hN R
  approx R r hr k := norm_iota_sub_hTilde_le hη hδ₀ d N hN R r hr k
  top := by
    refine ⟨⌈(Ts.T N).Lx + (Ts.T N).Ly⌉₊, fun R j hj => ?_⟩
    have hball : slotBall δ₀ (Ts.T N) R (rj j) = Finset.univ := by
      ext s
      simp only [Finset.mem_univ, iff_true]
      rw [mem_slotBall']
      have h1 := flatDist_le_add (Ts.T N) (centre δ₀ (Ts.T N) s) R
      have h2 : ((⌈(Ts.T N).Lx + (Ts.T N).Ly⌉₊ : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
      have h3 : (j : ℝ) < rj j := by
        unfold rj
        exact_mod_cast Nat.lt_two_pow_self (n := j)
      have h4 := Nat.le_ceil ((Ts.T N).Lx + (Ts.T N).Ly)
      linarith
    show condExp (slotBall δ₀ (Ts.T N) R (rj j)) (iota η δ₀ (Ts.T N) (d.h N R)) = iota η δ₀ (Ts.T N) (d.h N R)
    rw [hball]
    refine Fermion.Pilot.JW.condExp_of_mem ?_
    rw [Fermion.Pilot.JW.CAR_univ]
    exact StarSubalgebra.mem_top

end AssemblyData

end MasterDevices

/-! ## Theorem 5.3 -/

section Propagation

variable {η : ℝ → ℝ} {δ₀ : ℝ} {Ts : TorusSeq δ₀} {H : (N : ℕ) → FockOp (Ts.T N)}

/-- **Theorem 5.3(a)** (master inequality): "`For every dyadic $\lambda=r_{j_0}\ge1$, every $k\ge3$, $\rho>0$, $X\subset\Slots$, $A\in\CAR(X)$ and $t\in\R$,`"
"`\bigl\lVert\tau_t(A)-\tau^{\lambda,\fat X\rho}_t(A)\bigr\rVert\le\norm A\abs X\Bigl[\frac{16\pi c_k}{3C_1}\lambda^{-(k-2)} (1+C_1\abs t)^3+e^{-\rho/\lambda}\bigl(e^{2C_1\abs t}-1\bigr)\Bigr],`"
"`where, for $Y\subset\Slots$, $\tau^{\lambda,Y}$ is the dynamics generated by a self-adjoint operator $\Hhat_{\lambda,Y}\in\Alg(Y)$ constructed in the proof; in particular $\tau^{\lambda,\fat X\rho}_t(A)\in\CAR(\fat X\rho)$ has the parity of $A$.`"
— existential in the family `Y ↦ Ĥ_{λ,Y}`, which depends on `N` and `λ = 2^{j₀}` only (the module docstring). -/
theorem propagation_master (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, ∀ j₀ : ℕ, ∃ Hl : Finset (Slot δ₀ (Ts.T N)) → Op (Slot δ₀ (Ts.T N)),
      (∀ Y : Finset (Slot δ₀ (Ts.T N)), IsSelfAdjoint (Hl Y) ∧ Hl Y ∈ Alg Y) ∧
      ∀ k : ℕ, 3 ≤ k → ∀ ρ : ℝ, 0 < ρ → ∀ (X : Finset (Slot δ₀ (Ts.T N))) (A : Op (Slot δ₀ (Ts.T N))),
        A ∈ CAR X → ∀ t : ℝ,
          ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - dyn (Hl (fat X ρ)) t A)‖ ≤
              ‖opCLM A‖ * (X.card : ℝ) *
                (16 * π * ck d.Ch (d.CH k) k / (3 * C1 δ₀ d.Ch (d.CH 5)) * ((2 : ℝ) ^ j₀) ^ (-((k : ℝ) - 2)) *
                    (1 + C1 δ₀ d.Ch (d.CH 5) * |t|) ^ 3 +
                  Real.exp (-ρ / (2 : ℝ) ^ j₀) * (Real.exp (2 * C1 δ₀ d.Ch (d.CH 5) * |t|) - 1)) ∧
            dyn (Hl (fat X ρ)) t A ∈ CAR (fat X ρ) ∧
            (IsEven A → IsEven (dyn (Hl (fat X ρ)) t A)) ∧ (IsOdd A → IsOdd (dyn (Hl (fat X ρ)) t A)) := by
  intro N hN j₀
  have hT := Ts.admissible N hN
  have hΨ := PsiL_isEvenInteraction (msdata hη hδ₀ d N hN) j₀
  refine ⟨hamOn (PsiL (msdata hη hδ₀ d N hN) j₀), fun Y => ⟨isSelfAdjoint_hamOn (fun Z => (hΨ Z).1) Y,
    hamOn_mem_CAR hΨ Y, isEven_hamOn hΨ Y⟩, ?_⟩
  intro k hk ρ hρ X A hA t
  have hAY : A ∈ CAR (fat X ρ) := CAR_mono' (subset_fat X hρ.le) hA
  refine ⟨?_, dyn_mem_CAR (hamOn_mem_CAR hΨ _) hAY t, fun he => isEven_dyn (isEven_hamOn hΨ _) he t,
    fun ho => isOdd_dyn (isEven_hamOn hΨ _) ho t⟩
  rw [Hhat_eq_opIntegral hη hδ₀ d N hN]
  exact master_bound (msdata hη hδ₀ d N hN) hδ₀ hT j₀ hk hρ hA t

/-! ### Proof devices for Theorem 5.3(b)–(c) (phase (b); not statements of the paper)

(b) is derived from the statement of (a), as the paper does: the scale `λ = 2^{⌊β log₂ ρ⌋}` with `ρ^β/2 < λ ≤ ρ^β`,
`ρ^{1−β} ≥ 4C_1(1+|t|)`, the two terms of (a) bounded separately, the second through `max_{x>0} x^b e^{−x/2} = (2b/e)^b`. -/

theorem exp_neg_half_le {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    Real.exp (-x / 2) ≤ (2 * b / Real.exp 1) ^ b * x ^ (-b) := by
  have hy : 0 < x / (2 * b) := by positivity
  have h1 : x / (2 * b) ≤ Real.exp (x / (2 * b) - 1) := by
    have := Real.add_one_le_exp (x / (2 * b) - 1)
    linarith
  have h2 : (x / (2 * b)) ^ b ≤ Real.exp (x / 2 - b) := by
    calc (x / (2 * b)) ^ b ≤ (Real.exp (x / (2 * b) - 1)) ^ b := Real.rpow_le_rpow hy.le h1 hb.le
      _ = Real.exp ((x / (2 * b) - 1) * b) := by rw [← Real.exp_mul]
      _ = Real.exp (x / 2 - b) := by
          congr 1
          field_simp
  have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx b
  have h2b : 0 < (2 * b) ^ b := Real.rpow_pos_of_pos (by positivity) b
  have e1 : (2 * b / Real.exp 1) ^ b * x ^ (-b) = Real.exp (-b) / (x / (2 * b)) ^ b := by
    rw [Real.rpow_neg hx.le, Real.div_rpow (by positivity) (Real.exp_pos 1).le, Real.div_rpow hx.le (by positivity),
      Real.exp_one_rpow, Real.exp_neg]
    field_simp
  rw [e1, le_div_iff₀ (Real.rpow_pos_of_pos hy b)]
  calc Real.exp (-x / 2) * (x / (2 * b)) ^ b ≤ Real.exp (-x / 2) * Real.exp (x / 2 - b) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (-b) := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem dyadic_scale {ρ β : ℝ} (hρ : 1 ≤ ρ) (hβ : 0 < β) :
    (2 : ℝ) ^ ⌊β * Real.log ρ / Real.log 2⌋₊ ≤ ρ ^ β ∧ ρ ^ β < 2 * (2 : ℝ) ^ ⌊β * Real.log ρ / Real.log 2⌋₊ := by
  have hρ0 : 0 < ρ := by linarith
  have hlog : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hx : 0 ≤ β * Real.log ρ / Real.log 2 := div_nonneg (mul_nonneg hβ.le hlog) hlog2.le
  have hρβ : ρ ^ β = (2 : ℝ) ^ (β * Real.log ρ / Real.log 2) := by
    rw [Real.rpow_def_of_pos hρ0, Real.rpow_def_of_pos two_pos]
    congr 1
    field_simp
  rw [hρβ]
  constructor
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hx)
  · have h := Nat.lt_floor_add_one (β * Real.log ρ / Real.log 2)
    calc (2 : ℝ) ^ (β * Real.log ρ / Real.log 2) < (2 : ℝ) ^ ((⌊β * Real.log ρ / Real.log 2⌋₊ : ℝ) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
      _ = 2 * (2 : ℝ) ^ ⌊β * Real.log ρ / Real.log 2⌋₊ := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_natCast]
          ring

theorem lightCone_T2 {C₁ ρ β lam k' t : ℝ} (hC₁ : 0 ≤ C₁) (hρ : 1 ≤ ρ) (hβ1 : β < 1) (hk' : 0 < k')
    (hlam0 : 0 < lam) (hlam : lam ≤ ρ ^ β) (h4 : 4 * C₁ * (1 + |t|) ≤ ρ ^ (1 - β)) :
    Real.exp (-ρ / lam) * (Real.exp (2 * C₁ * |t|) - 1) ≤
      (2 * k' / (Real.exp 1 * (1 - β))) ^ (k' / (1 - β)) * ρ ^ (-k') := by
  have hρ0 : 0 < ρ := by linarith
  have hx : 0 < ρ ^ (1 - β) := Real.rpow_pos_of_pos hρ0 _
  have hρl : ρ ^ (1 - β) ≤ ρ / lam := by
    rw [le_div_iff₀ hlam0]
    calc ρ ^ (1 - β) * lam ≤ ρ ^ (1 - β) * ρ ^ β := mul_le_mul_of_nonneg_left hlam hx.le
      _ = ρ := by rw [← Real.rpow_add hρ0]; simp
  have h1 : Real.exp (-ρ / lam) ≤ Real.exp (-ρ ^ (1 - β)) := Real.exp_le_exp.mpr (by rw [neg_div]; linarith)
  have hta : 0 ≤ |t| := abs_nonneg t
  have h2 : Real.exp (2 * C₁ * |t|) - 1 ≤ Real.exp (ρ ^ (1 - β) / 2) := by
    have h3 : 2 * C₁ * |t| ≤ ρ ^ (1 - β) / 2 := by nlinarith
    have h5 := Real.exp_le_exp.mpr h3
    linarith
  have hnn : 0 ≤ Real.exp (2 * C₁ * |t|) - 1 := by
    have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * C₁ * |t|)
    linarith
  have h3 : Real.exp (-ρ / lam) * (Real.exp (2 * C₁ * |t|) - 1) ≤ Real.exp (-ρ ^ (1 - β) / 2) := by
    calc _ ≤ Real.exp (-ρ ^ (1 - β)) * Real.exp (ρ ^ (1 - β) / 2) := mul_le_mul h1 h2 hnn (Real.exp_pos _).le
      _ = Real.exp (-ρ ^ (1 - β) / 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
  refine h3.trans ?_
  have hb : 0 < k' / (1 - β) := div_pos hk' (by linarith)
  have h5 := exp_neg_half_le hb hx
  have e : (ρ ^ (1 - β)) ^ (-(k' / (1 - β))) = ρ ^ (-k') := by
    rw [← Real.rpow_mul hρ0.le]
    congr 1
    have : (1 - β) ≠ 0 := by linarith
    field_simp
  have e2 : 2 * (k' / (1 - β)) / Real.exp 1 = 2 * k' / (Real.exp 1 * (1 - β)) := by
    have : (1 - β) ≠ 0 := by linarith
    field_simp
  rw [e, e2] at h5
  exact h5

theorem lightCone_T1 {C₁ ck ρ β lam k' t : ℝ} {k : ℕ} (hC₁ : 0 < C₁) (hck : 0 ≤ ck) (hρ : 1 ≤ ρ)
    (hβ : 0 < β) (hβ1 : β < 1) (hlam : ρ ^ β / 2 ≤ lam) (hk : 2 ≤ k) (hkβ : k' + 3 ≤ β * ((k : ℝ) - 2))
    (ht : 1 + C₁ * |t| ≤ max 1 C₁ / (4 * C₁) * ρ ^ (1 - β)) :
    16 * π * ck / (3 * C₁) * lam ^ (-((k : ℝ) - 2)) * (1 + C₁ * |t|) ^ 3 ≤
      16 * π * ck * 2 ^ (k - 2) / (3 * C₁) * (max 1 C₁ / (4 * C₁)) ^ 3 * ρ ^ (-k') := by
  have hρ0 : 0 < ρ := by linarith
  have hρβ : 0 < ρ ^ β / 2 := by have := Real.rpow_pos_of_pos hρ0 β; linarith
  have hk2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub hk]
    norm_num
  have hl1 : lam ^ (-((k : ℝ) - 2)) ≤ (ρ ^ β / 2) ^ (-((k : ℝ) - 2)) :=
    Real.rpow_le_rpow_of_nonpos hρβ hlam (by linarith)
  have hl2 : (ρ ^ β / 2) ^ (-((k : ℝ) - 2)) = 2 ^ (k - 2) * ρ ^ (-(β * ((k : ℝ) - 2))) := by
    rw [Real.div_rpow (Real.rpow_nonneg hρ0.le _) (by norm_num), ← Real.rpow_mul hρ0.le, Real.rpow_neg (by norm_num),
      ← hcast, Real.rpow_natCast]
    rw [div_inv_eq_mul, mul_comm]
    congr 2
    ring
  have hM0 : 0 ≤ max 1 C₁ / (4 * C₁) := div_nonneg (le_trans zero_le_one (le_max_left _ _)) (by positivity)
  have ht0 : 0 ≤ 1 + C₁ * |t| := by have := abs_nonneg t; nlinarith
  have hx : 0 ≤ ρ ^ (1 - β) := Real.rpow_nonneg hρ0.le _
  have ht3 : (1 + C₁ * |t|) ^ 3 ≤ (max 1 C₁ / (4 * C₁)) ^ 3 * ρ ^ (3 * (1 - β)) := by
    calc (1 + C₁ * |t|) ^ 3 ≤ (max 1 C₁ / (4 * C₁) * ρ ^ (1 - β)) ^ 3 := pow_le_pow_left₀ ht0 ht 3
      _ = (max 1 C₁ / (4 * C₁)) ^ 3 * ρ ^ (3 * (1 - β)) := by
          rw [mul_pow, mul_comm (3 : ℝ), Real.rpow_mul hρ0.le, Real.rpow_ofNat]
  have hK0 : 0 ≤ 16 * π * ck / (3 * C₁) := by positivity
  have hexp : ρ ^ (-(β * ((k : ℝ) - 2))) * ρ ^ (3 * (1 - β)) ≤ ρ ^ (-k') := by
    rw [← Real.rpow_add hρ0]
    apply Real.rpow_le_rpow_of_exponent_le hρ
    nlinarith
  calc 16 * π * ck / (3 * C₁) * lam ^ (-((k : ℝ) - 2)) * (1 + C₁ * |t|) ^ 3
      ≤ 16 * π * ck / (3 * C₁) * (2 ^ (k - 2) * ρ ^ (-(β * ((k : ℝ) - 2)))) *
          ((max 1 C₁ / (4 * C₁)) ^ 3 * ρ ^ (3 * (1 - β))) := by
        rw [← hl2]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hl1 hK0) ht3 (pow_nonneg ht0 3)
          (mul_nonneg hK0 (Real.rpow_nonneg hρβ.le _))
    _ = 16 * π * ck * 2 ^ (k - 2) / (3 * C₁) * (max 1 C₁ / (4 * C₁)) ^ 3 *
          (ρ ^ (-(β * ((k : ℝ) - 2))) * ρ ^ (3 * (1 - β))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

theorem Ch_nonneg {η : ℝ → ℝ} {δ₀ : ℝ} {Ts : TorusSeq δ₀} {H : (N : ℕ) → FockOp (Ts.T N)} (d : H1Data η δ₀ Ts H)
    {N : ℕ} (hN : N ∈ Ts.idx) : 0 ≤ d.Ch :=
  (norm_nonneg _).trans (d.norm_h_le N hN 0)

/-- **Theorem 5.3(b)** (light cone): "`For $\beta\in(0,1)$ and $k'>0$ put $C_{\rm lc}(\beta):=\max\{1,(4C_1)^{1/(1-\beta)}\}$, $\lambda:=2^{\lfloor\beta\log_2\rho\rfloor}$ and $k:=2+\lceil(k'+3)/\beta\rceil$. Whenever $\rho\ge C_{\rm lc}(\beta)(1+\abs t)^{1/(1-\beta)}$,`"
"`\inf\bigl\{\norm{\tau_t(A)-A'}:A'\in\CAR(\fat X\rho)\text{ of the parity of }A\bigr\}\le C_{k',\beta}\norm A\abs X\rho^{-k'},`"
— for `A ∈ CAR(X)` as in (a); `λ` enters only the proof. -/
theorem propagation_lightCone (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, ∀ β : ℝ, 0 < β → β < 1 → ∀ k' : ℝ, 0 < k' →
      ∀ (X : Finset (Slot δ₀ (Ts.T N))) (A : Op (Slot δ₀ (Ts.T N))), A ∈ CAR X → ∀ t ρ : ℝ,
        ClcBeta (C1 δ₀ d.Ch (d.CH 5)) β * (1 + |t|) ^ (1 / (1 - β)) ≤ ρ →
          ⨅ A' : CARpar (fat X ρ) A, ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - (A' : Op (Slot δ₀ (Ts.T N))))‖ ≤
            CkBeta d.Ch d.CH (C1 δ₀ d.Ch (d.CH 5)) k' β * ‖opCLM A‖ * (X.card : ℝ) * ρ ^ (-k') := by
  intro N hN β hβ hβ1 k' hk' X A hA t ρ hρ
  have hCh := Ch_nonneg d hN
  have hC₁0 := C1_nonneg δ₀ hCh (d.CH 5)
  have hta : 0 ≤ |t| := abs_nonneg t
  have h1β : 0 < 1 - β := by linarith
  have hγ : 0 < 1 / (1 - β) := by positivity
  have ht1 : 1 ≤ (1 + |t|) ^ (1 / (1 - β)) := Real.one_le_rpow (by linarith) hγ.le
  have hClc1 : 1 ≤ ClcBeta (C1 δ₀ d.Ch (d.CH 5)) β := le_max_left _ _
  have hρ1 : 1 ≤ ρ := by nlinarith
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨hl1, hl2⟩ := dyadic_scale hρ1 hβ
  have hlam0 : (0 : ℝ) < (2 : ℝ) ^ ⌊β * Real.log ρ / Real.log 2⌋₊ := by positivity
  have hlam : ρ ^ β / 2 ≤ (2 : ℝ) ^ ⌊β * Real.log ρ / Real.log 2⌋₊ := by linarith
  -- `4 C_1 (1 + |t|) ≤ ρ^{1−β}`
  have h4 : 4 * C1 δ₀ d.Ch (d.CH 5) * (1 + |t|) ≤ ρ ^ (1 - β) := by
    have hbase : 0 ≤ 4 * C1 δ₀ d.Ch (d.CH 5) * (1 + |t|) := by positivity
    have hle : (4 * C1 δ₀ d.Ch (d.CH 5) * (1 + |t|)) ^ (1 / (1 - β)) ≤ ρ := by
      rw [Real.mul_rpow (by positivity) (by linarith)]
      refine le_trans ?_ hρ
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
    calc 4 * C1 δ₀ d.Ch (d.CH 5) * (1 + |t|)
        = ((4 * C1 δ₀ d.Ch (d.CH 5) * (1 + |t|)) ^ (1 - β)⁻¹) ^ (1 - β) := by
          rw [Real.rpow_inv_rpow hbase h1β.ne']
      _ ≤ ρ ^ (1 - β) := by
          rw [← one_div]
          exact Real.rpow_le_rpow (Real.rpow_nonneg hbase _) hle h1β.le
  obtain ⟨Hl, _, hmain⟩ := propagation_master hη hδ₀ d N hN ⌊β * Real.log ρ / Real.log 2⌋₊
  have hceil : (k' + 3) / β ≤ (⌈(k' + 3) / β⌉₊ : ℝ) := Nat.le_ceil _
  have hceil1 : 1 ≤ ⌈(k' + 3) / β⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  have hk3 : 3 ≤ kLc k' β := by unfold kLc; omega
  have hk2 : 2 ≤ kLc k' β := by omega
  have hkβ : k' + 3 ≤ β * (((kLc k' β : ℕ) : ℝ) - 2) := by
    have e : (((kLc k' β : ℕ) : ℝ) - 2) = (⌈(k' + 3) / β⌉₊ : ℝ) := by unfold kLc; push_cast; ring
    rw [e]
    have := (div_le_iff₀' hβ).mp hceil
    linarith
  obtain ⟨hbound, hmem, heven, hodd⟩ := hmain (kLc k' β) hk3 ρ hρ0 X A hA t
  have hbdd : BddBelow (Set.range fun A' : CARpar (fat X ρ) A =>
      ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - (A' : Op (Slot δ₀ (Ts.T N))))‖) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
  refine (ciInf_le hbdd ⟨dyn (Hl (fat X ρ)) t A, hmem, heven, hodd⟩).trans (hbound.trans ?_)
  have hck : 0 ≤ ck d.Ch (d.CH (kLc k' β)) (kLc k' β) := by
    unfold ck
    exact mul_nonneg (by positivity) (le_max_of_le_left hCh)
  have hT1 : 16 * π * ck d.Ch (d.CH (kLc k' β)) (kLc k' β) / (3 * C1 δ₀ d.Ch (d.CH 5)) *
        ((2 : ℝ) ^ ⌊β * Real.log ρ / Real.log 2⌋₊) ^ (-((kLc k' β : ℝ) - 2)) * (1 + C1 δ₀ d.Ch (d.CH 5) * |t|) ^ 3 ≤
      16 * π * ck d.Ch (d.CH (kLc k' β)) (kLc k' β) * 2 ^ (kLc k' β - 2) / (3 * C1 δ₀ d.Ch (d.CH 5)) *
        (max 1 (C1 δ₀ d.Ch (d.CH 5)) / (4 * C1 δ₀ d.Ch (d.CH 5))) ^ 3 * ρ ^ (-k') := by
    rcases hC₁0.lt_or_eq with hpos | hzero
    · refine lightCone_T1 hpos hck hρ1 hβ hβ1 hlam hk2 hkβ ?_
      have hm1 : 1 ≤ max 1 (C1 δ₀ d.Ch (d.CH 5)) := le_max_left _ _
      have hm2 : C1 δ₀ d.Ch (d.CH 5) ≤ max 1 (C1 δ₀ d.Ch (d.CH 5)) := le_max_right _ _
      have hs : 1 + |t| ≤ ρ ^ (1 - β) / (4 * C1 δ₀ d.Ch (d.CH 5)) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      calc 1 + C1 δ₀ d.Ch (d.CH 5) * |t| ≤ max 1 (C1 δ₀ d.Ch (d.CH 5)) * (1 + |t|) := by nlinarith
        _ ≤ max 1 (C1 δ₀ d.Ch (d.CH 5)) * (ρ ^ (1 - β) / (4 * C1 δ₀ d.Ch (d.CH 5))) :=
            mul_le_mul_of_nonneg_left hs (by linarith)
        _ = max 1 (C1 δ₀ d.Ch (d.CH 5)) / (4 * C1 δ₀ d.Ch (d.CH 5)) * ρ ^ (1 - β) := by ring
    · rw [← hzero]
      simp
  have hT2 := lightCone_T2 hC₁0 hρ1 hβ1 hk' hlam0 hl1 h4
  have hAX : 0 ≤ ‖opCLM A‖ * (X.card : ℝ) := by positivity
  calc ‖opCLM A‖ * (X.card : ℝ) *
        (16 * π * ck d.Ch (d.CH (kLc k' β)) (kLc k' β) / (3 * C1 δ₀ d.Ch (d.CH 5)) *
            ((2 : ℝ) ^ ⌊β * Real.log ρ / Real.log 2⌋₊) ^ (-((kLc k' β : ℝ) - 2)) * (1 + C1 δ₀ d.Ch (d.CH 5) * |t|) ^ 3 +
          Real.exp (-ρ / (2 : ℝ) ^ ⌊β * Real.log ρ / Real.log 2⌋₊) * (Real.exp (2 * C1 δ₀ d.Ch (d.CH 5) * |t|) - 1))
      ≤ ‖opCLM A‖ * (X.card : ℝ) *
        (16 * π * ck d.Ch (d.CH (kLc k' β)) (kLc k' β) * 2 ^ (kLc k' β - 2) / (3 * C1 δ₀ d.Ch (d.CH 5)) *
            (max 1 (C1 δ₀ d.Ch (d.CH 5)) / (4 * C1 δ₀ d.Ch (d.CH 5))) ^ 3 * ρ ^ (-k') +
          (2 * k' / (Real.exp 1 * (1 - β))) ^ (k' / (1 - β)) * ρ ^ (-k')) :=
        mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) hAX
    _ = _ := by
        unfold CkBeta
        ring

/-- **Theorem 5.3(c)** (every light-cone exponent above one): "`Consequently, for every $\alpha>1$ and $k>0$ there are $C_{\rm lc}$ and $C_k$, depending only on $\alpha$, $k$, $\Cvol$, $C_h$ and finitely many $C^H_{k'}$, such that for all $N$, $X\subset\Slots$, even $A\in\Alg(X)$, $t\in\R$ and $\rho\ge C_{\rm lc}(1+\abs t)^\alpha$,`"
"`\inf\{\norm{\tau_t(A)-A'}:A'\in\Alg(\fat X\rho)\}\le C_k\norm A\abs X\rho^{-k};`"
— the constants after `δ₀`, `α`, `k`, `C_h`, `C^H` and before everything else (the module docstring). -/
theorem propagation_polynomial {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {α : ℝ} (hα : 1 < α) {k : ℝ} (hk : 0 < k) (Ch : ℝ)
    (CH : ℕ → ℝ) :
    ∃ Clc Ck : ℝ, ∀ (η : ℝ → ℝ), IsProfile η → ∀ (Ts : TorusSeq δ₀) (H : (N : ℕ) → FockOp (Ts.T N))
      (d : H1Data η δ₀ Ts H), d.Ch = Ch → d.CH = CH →
        ∀ N ∈ Ts.idx, ∀ (X : Finset (Slot δ₀ (Ts.T N))) (A : Op (Slot δ₀ (Ts.T N))), A ∈ Alg X →
          ∀ t ρ : ℝ, Clc * (1 + |t|) ^ α ≤ ρ →
            ⨅ A' : Alg (fat X ρ), ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - (A' : Op (Slot δ₀ (Ts.T N))))‖ ≤
              Ck * ‖opCLM A‖ * (X.card : ℝ) * ρ ^ (-k) := by
  have hα0 : 0 < α := by linarith
  have hβ : 0 < 1 - 1 / α := by
    rw [sub_pos, div_lt_one hα0]
    exact hα
  have hβ1 : 1 - 1 / α < 1 := by
    have : 0 < 1 / α := by positivity
    linarith
  have he : 1 / (1 - (1 - 1 / α)) = α := by
    field_simp
    ring
  refine ⟨ClcBeta (C1 δ₀ Ch (CH 5)) (1 - 1 / α), CkBeta Ch CH (C1 δ₀ Ch (CH 5)) k (1 - 1 / α), ?_⟩
  intro η hη Ts H d hCh hCH N hN X A hA t ρ hρ
  rw [← hCh, ← hCH] at hρ ⊢
  have hρ' : ClcBeta (C1 δ₀ d.Ch (d.CH 5)) (1 - 1 / α) * (1 + |t|) ^ (1 / (1 - (1 - 1 / α))) ≤ ρ := by
    rw [he]
    exact hρ
  have hb := propagation_lightCone hη hδ₀ d N hN (1 - 1 / α) hβ hβ1 k hk X A hA.1 t ρ hρ'
  refine le_trans ?_ hb
  have : Nonempty (CARpar (fat X ρ) A) :=
    ⟨⟨0, zero_mem _, fun _ => Commute.zero_left _, fun _ => by simp [IsOdd]⟩⟩
  have hbdd : BddBelow (Set.range fun A' : Alg (fat X ρ) =>
      ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - (A' : Op (Slot δ₀ (Ts.T N))))‖) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
  exact le_ciInf fun A' => ciInf_le hbdd ⟨(A' : Op (Slot δ₀ (Ts.T N))), A'.2.1, A'.2.2.1 hA.2⟩

/-! ### Proof devices for Theorem 5.3(c) with `k = 0` (phase (b); not statements of the paper) -/

theorem fat_empty_prop {T : Torus} (r : ℝ) : fat (∅ : Finset (Slot δ₀ T)) r = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun s hs => ?_
  obtain ⟨s', hs', _⟩ := mem_fat.mp hs
  exact Finset.notMem_empty s' hs'

theorem dyn_eq_of_commute {S : Type*} [Fintype S] [DecidableEq S] {H A : Op S} (h : Commute A H) (t : ℝ) :
    dyn H t A = A := by
  have hc : Commute A (NormedSpace.exp ((I * (t : ℂ)) • H)) := (h.smul_right _).exp_right
  rw [dyn, ← hc.eq, Matrix.mul_assoc, expI_mul_expI_neg, Matrix.mul_one]

/-- **Theorem 5.3(c)**: "`for $k=0$ the same bound holds with the constant $1$ in place of $C_k$.`" — for every `ρ` (the
proof's approximants `0` and `A`; stronger than under the light-cone hypothesis only). -/
theorem propagation_polynomial_zero (hη : IsProfile η) (hδ₀ : 0 < δ₀) (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, ∀ (X : Finset (Slot δ₀ (Ts.T N))) (A : Op (Slot δ₀ (Ts.T N))), A ∈ Alg X → ∀ t ρ : ℝ,
      ⨅ A' : Alg (fat X ρ), ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - (A' : Op (Slot δ₀ (Ts.T N))))‖ ≤
        1 * ‖opCLM A‖ * (X.card : ℝ) := by
  intro N hN X A hA t ρ
  have hHsa := isSelfAdjoint_Hhat hη hδ₀ d N hN
  have hbdd : BddBelow (Set.range fun A' : Alg (fat X ρ) =>
      ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - (A' : Op (Slot δ₀ (Ts.T N))))‖) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
  rcases Finset.eq_empty_or_nonempty X with hX | hX
  · subst hX
    have hHC : Hhat η δ₀ Ts H N ∈ CAR (Finset.univ : Finset (Slot δ₀ (Ts.T N))) := by
      rw [Fermion.Pilot.JW.CAR_univ]; exact StarSubalgebra.mem_top
    have hcomm : Commute A (Hhat η δ₀ Ts H N) :=
      commute_of_mem_Alg_of_mem_CAR (Finset.disjoint_empty_left _) hA hHC
    have hmem : A ∈ Alg (fat (∅ : Finset (Slot δ₀ (Ts.T N))) ρ) := by
      rw [fat_empty_prop]; exact hA
    refine (ciInf_le hbdd ⟨A, hmem⟩).trans ?_
    rw [dyn_eq_of_commute hcomm, sub_self, opCLM_zero', norm_zero, Finset.card_empty, Nat.cast_zero, mul_zero]
  · refine (ciInf_le hbdd ⟨0, zero_mem _, Commute.zero_left _⟩).trans ?_
    rw [sub_zero, norm_dyn hHsa]
    have h1 : (1 : ℝ) ≤ X.card := by exact_mod_cast hX.card_pos
    nlinarith [norm_nonneg (opCLM A)]

end Propagation

/-! ## Lemma 5.5 -/

/-! ### Proof devices for Lemma 5.5 (phase (b); not statements of the paper)

**A modelling decision of the proof**: instead of the paper's dyadic decomposition `A = Σ_j A^{(j)}`, one best
approximant `B ∈ Alg(X^{(r/2)})` of `A` is propagated with Theorem 5.3(c) at decay order `k + 2` (not `k`); the two
extra orders absorb `|X^{(r/2)}| ≤ C_vol(1 + r/2)²|X|`, which the paper's decomposition absorbs instead by the decay
`(1+2^j)^{−k̄}`, `k̄ ≥ 3`, of the pieces. The constant is then `max{3^{k+2}|C^τ_{k+2}|C_vol + 2^{k̄}, (3 max{C_lc,1})^k}` —
still determined by `δ₀`, `k`, `C_h` and finitely many `C^H_{k'}`, as the statement requires; it is not the paper's
constant, which the statement does not name. -/

theorem le_zero_of_forall_le_inv' {v c : ℝ} (hc : 0 ≤ c) (h : ∀ r : ℝ, 0 ≤ r → v ≤ c * (1 + r)⁻¹) : v ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have h1 := h (c / v) (div_nonneg hc hpos.le)
  have h2 : c * (1 + c / v)⁻¹ < v := by
    have hv : 0 < 1 + c / v := by positivity
    rw [← div_eq_mul_inv, div_lt_iff₀ hv, mul_add, mul_one, mul_div_cancel₀ _ hpos.ne']
    nlinarith
  linarith

theorem exists_nearest_le_iInf {S : Type*} [Fintype S] [DecidableEq S] (Y : Finset S) (x : Op S) :
    ∃ B ∈ Alg Y, ‖opCLM (x - B)‖ ≤ ⨅ A' : Alg Y, ‖opCLM (x - (A' : Op S))‖ := by
  obtain ⟨B, hB, hmin⟩ := exists_nearest_opCLM (Alg Y) (isClosed_Alg Y) ⟨0, zero_mem _, Commute.zero_left _⟩ x
  have : Nonempty (Alg Y) := ⟨⟨0, zero_mem _, Commute.zero_left _⟩⟩
  exact ⟨B, hB, le_ciInf fun A' => hmin A' A'.2⟩

theorem exists_approx_of_setNorm {δ₀ : ℝ} {T : Torus} {A : Op (Slot δ₀ T)} {X : Finset (Slot δ₀ T)} {kb : ℝ}
    (hfin : setNorm A X kb ≠ ⊤) {r : ℝ} (hr : 0 ≤ r) :
    ∃ B ∈ Alg (fat X r), ‖opCLM (A - B)‖ ≤ (setNorm A X kb).toReal * (1 + r) ^ (-kb) := by
  obtain ⟨B, hB, hinf⟩ := exists_nearest_le_iInf (fat X r) A
  refine ⟨B, hB, ?_⟩
  have hle : ENNReal.ofReal ((1 + r) ^ kb * ⨅ A' : Alg (fat X r), ‖opCLM (A - (A' : Op (Slot δ₀ T)))‖) ≤
      setNorm A X kb := by
    unfold setNorm
    exact le_iSup₂ (f := fun (r : ℝ) (_ : 0 ≤ r) =>
      ENNReal.ofReal ((1 + r) ^ kb * ⨅ A' : Alg (fat X r), ‖opCLM (A - (A' : Op (Slot δ₀ T)))‖)) r hr
  rw [← ENNReal.ofReal_toReal hfin, ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at hle
  have hpos : 0 < (1 + r) ^ kb := Real.rpow_pos_of_pos (by linarith) _
  refine hinf.trans ?_
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

theorem card_fat_le {δ₀ : ℝ} {T : Torus} (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (X : Finset (Slot δ₀ T)) {r : ℝ}
    (hr : 0 ≤ r) : ((fat X r).card : ℝ) ≤ Cvol δ₀ * (1 + r) ^ 2 * X.card := by
  have hsub : fat X r ⊆ X.biUnion fun s => slotBall δ₀ T (centre δ₀ T s) r := by
    intro s' hs'
    obtain ⟨s, hs, hd⟩ := mem_fat.mp hs'
    rw [Finset.mem_biUnion]
    refine ⟨s, hs, ?_⟩
    simp only [slotBall, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hd
  calc ((fat X r).card : ℝ) ≤ ((X.biUnion fun s => slotBall δ₀ T (centre δ₀ T s) r).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ s ∈ X, ((slotBall δ₀ T (centre δ₀ T s) r).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ s ∈ X, Cvol δ₀ * (1 + r) ^ 2 := Finset.sum_le_sum fun s _ =>
        (card_slotBall_le hδ₀ hT (centre δ₀ T s) hr).1.trans (card_slotBall_le hδ₀ hT (centre δ₀ T s) hr).2
    _ = Cvol δ₀ * (1 + r) ^ 2 * X.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
theorem large_radius_arith1 {k ρ : ℝ} (hk : 0 ≤ k) (hρ : 1 ≤ ρ) :
    (1 + 2 * ρ) ^ k * (1 + ρ) ^ (2 : ℝ) * ρ ^ (-(k + 2)) ≤ (3 : ℝ) ^ (k + 2) := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : (1 + 2 * ρ) ^ k ≤ (3 * ρ) ^ k := Real.rpow_le_rpow (by linarith) (by linarith) hk
  have h2 : (1 + ρ) ^ (2 : ℝ) ≤ (3 * ρ) ^ (2 : ℝ) := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hpos : 0 ≤ ρ ^ (-(k + 2)) := Real.rpow_nonneg hρ0.le _
  calc (1 + 2 * ρ) ^ k * (1 + ρ) ^ (2 : ℝ) * ρ ^ (-(k + 2))
      ≤ (3 * ρ) ^ k * (3 * ρ) ^ (2 : ℝ) * ρ ^ (-(k + 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _)
          (Real.rpow_nonneg (by linarith) _)) hpos
    _ = (3 * ρ) ^ (k + 2) * ρ ^ (-(k + 2)) := by
        rw [← Real.rpow_add (by linarith : (0 : ℝ) < 3 * ρ)]
    _ = (3 : ℝ) ^ (k + 2) * (ρ ^ (k + 2) * ρ ^ (-(k + 2))) := by
        rw [Real.mul_rpow (by norm_num) hρ0.le]
        ring
    _ = (3 : ℝ) ^ (k + 2) := by
        rw [← Real.rpow_add hρ0, add_neg_cancel, Real.rpow_zero, mul_one]

theorem large_radius_arith2 {k kb ρ : ℝ} (hk : 0 ≤ k) (hkkb : k ≤ kb) (hρ : 0 ≤ ρ) :
    (1 + 2 * ρ) ^ k * (1 + ρ) ^ (-kb) ≤ (2 : ℝ) ^ kb := by
  have h1 : (1 + 2 * ρ) ^ k ≤ (2 * (1 + ρ)) ^ k := Real.rpow_le_rpow (by linarith) (by linarith) hk
  have h3 : (1 + ρ) ^ (k - kb) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have h4 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ kb := Real.rpow_le_rpow_of_exponent_le (by norm_num) hkkb
  calc (1 + 2 * ρ) ^ k * (1 + ρ) ^ (-kb) ≤ (2 * (1 + ρ)) ^ k * (1 + ρ) ^ (-kb) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by linarith) _)
    _ = (2 : ℝ) ^ k * (1 + ρ) ^ (k - kb) := by
        rw [Real.mul_rpow (by norm_num) (by linarith), sub_eq_add_neg, Real.rpow_add (by linarith)]
        ring
    _ ≤ (2 : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (2 : ℝ) ^ kb := by rw [mul_one]; exact h4

theorem large_radius_final {Cτ Cv x a S k kb r Ck q I : ℝ} (hCv : 0 ≤ Cv) (hx : 1 ≤ x) (ha : 0 ≤ a)
    (hS : 0 ≤ S) (hk : 0 ≤ k) (hkkb : k ≤ kb) (hr : 2 ≤ r) (hCk : 3 ^ (k + 2) * |Cτ| * Cv + 2 ^ kb ≤ Ck)
    (hq : 1 ≤ q)
    (hI : I ≤ |Cτ| * (a + S) * (Cv * (1 + r / 2) ^ (2 : ℝ) * x) * (r / 2) ^ (-(k + 2)) + S * (1 + r / 2) ^ (-kb)) :
    (1 + r) ^ k * I ≤ Ck * q * x * (a + S) := by
  have hρ1 : 1 ≤ r / 2 := by linarith
  have hρ0 : 0 ≤ r / 2 := by linarith
  have ha1 := large_radius_arith1 hk hρ1
  have ha2 := large_radius_arith2 hk hkkb hρ0
  rw [show (1 : ℝ) + 2 * (r / 2) = 1 + r by ring] at ha1 ha2
  have hkr : 0 ≤ (1 + r) ^ k := Real.rpow_nonneg (by linarith) _
  have haS : 0 ≤ a + S := add_nonneg ha hS
  have hx0 : 0 ≤ x := by linarith
  have hP : 0 ≤ |Cτ| * Cv * x * (a + S) := mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hCv) hx0) haS
  have h2kb : 0 ≤ (2 : ℝ) ^ kb := Real.rpow_nonneg (by norm_num) _
  have h3k : 0 ≤ (3 : ℝ) ^ (k + 2) := Real.rpow_nonneg (by norm_num) _
  have hSx : S ≤ x * (a + S) := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) haS]
  have hCk0 : 0 ≤ 3 ^ (k + 2) * |Cτ| * Cv + 2 ^ kb :=
    add_nonneg (mul_nonneg (mul_nonneg h3k (abs_nonneg _)) hCv) h2kb
  have hCkq : 3 ^ (k + 2) * |Cτ| * Cv + 2 ^ kb ≤ Ck * q :=
    hCk.trans (le_mul_of_one_le_right (hCk0.trans hCk) hq)
  calc (1 + r) ^ k * I
      ≤ (1 + r) ^ k * (|Cτ| * (a + S) * (Cv * (1 + r / 2) ^ (2 : ℝ) * x) * (r / 2) ^ (-(k + 2)) +
          S * (1 + r / 2) ^ (-kb)) := mul_le_mul_of_nonneg_left hI hkr
    _ = |Cτ| * Cv * x * (a + S) * ((1 + r) ^ k * (1 + r / 2) ^ (2 : ℝ) * (r / 2) ^ (-(k + 2))) +
          S * ((1 + r) ^ k * (1 + r / 2) ^ (-kb)) := by ring
    _ ≤ |Cτ| * Cv * x * (a + S) * (3 : ℝ) ^ (k + 2) + S * (2 : ℝ) ^ kb :=
        add_le_add (mul_le_mul_of_nonneg_left ha1 hP) (mul_le_mul_of_nonneg_left ha2 hS)
    _ ≤ |Cτ| * Cv * x * (a + S) * (3 : ℝ) ^ (k + 2) + x * (a + S) * (2 : ℝ) ^ kb :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hSx h2kb)
    _ = (3 ^ (k + 2) * |Cτ| * Cv + 2 ^ kb) * (x * (a + S)) := by ring
    _ ≤ (Ck * q) * (x * (a + S)) := mul_le_mul_of_nonneg_right hCkq (mul_nonneg hx0 haS)
    _ = Ck * q * x * (a + S) := by ring

theorem small_radius_final {M t r k Ck a S x I : ℝ} (hM : 1 ≤ M) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (hsmall : r < 2 * M * (1 + |t|) ^ (4 : ℝ)) (hCk : (3 * M) ^ k ≤ Ck) (hx : 1 ≤ x) (ha : 0 ≤ a)
    (hS : 0 ≤ S) (hI : I ≤ a) : (1 + r) ^ k * I ≤ Ck * (1 + |t|) ^ (4 * k) * x * (a + S) := by
  have hta : 0 ≤ |t| := abs_nonneg t
  have ht4 : (1 : ℝ) ≤ (1 + |t|) ^ (4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hM4 : 1 ≤ M * (1 + |t|) ^ (4 : ℝ) := one_le_mul_of_one_le_of_one_le hM ht4
  have hr3 : 1 + r ≤ 3 * M * (1 + |t|) ^ (4 : ℝ) := by linarith
  have hpk : (1 + r) ^ k ≤ (3 * M) ^ k * (1 + |t|) ^ (4 * k) := by
    calc (1 + r) ^ k ≤ (3 * M * (1 + |t|) ^ (4 : ℝ)) ^ k := Real.rpow_le_rpow (by linarith) hr3 hk
      _ = (3 * M) ^ k * (1 + |t|) ^ (4 * k) := by
          rw [Real.mul_rpow (by linarith) (by linarith), ← Real.rpow_mul (by linarith)]
  have hkr : 0 ≤ (1 + r) ^ k := Real.rpow_nonneg (by linarith) _
  have ht0 : 0 ≤ (1 + |t|) ^ (4 * k) := Real.rpow_nonneg (by linarith) _
  have h3M : 0 ≤ (3 * M) ^ k := Real.rpow_nonneg (by linarith) _
  have hax : a ≤ x * (a + S) := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (add_nonneg ha hS)]
  calc (1 + r) ^ k * I ≤ (1 + r) ^ k * a := mul_le_mul_of_nonneg_left hI hkr
    _ ≤ (3 * M) ^ k * (1 + |t|) ^ (4 * k) * a := mul_le_mul_of_nonneg_right hpk ha
    _ ≤ Ck * (1 + |t|) ^ (4 * k) * a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCk ht0) ha
    _ ≤ Ck * (1 + |t|) ^ (4 * k) * (x * (a + S)) :=
        mul_le_mul_of_nonneg_left hax (mul_nonneg (h3M.trans hCk) ht0)
    _ = Ck * (1 + |t|) ^ (4 * k) * x * (a + S) := by ring

/-- **Lemma 5.5**: "`For every $k\ge0$ there is $C_k$ such that for every even operator $A$ on $\FockS$, every $X\subset\Slots$ and every $t\in\R$,`"
"`\norm{\tau_t(A)}_{X;k}\le C_k(1+\abs t)^{4k}\abs X\bigl(\norm A+\norm A_{X;\max\{k,3\}}\bigr).`"
— in block B's set norm (`ℝ≥0∞`); `k` real; the constant after `δ₀`, `k`, `C_h`, `C^H` ("`which depends only on $k$, $\Cvol$, $C_h$ and finitely many $C^H_{k'}$`").
**For `A` with `n_A := ‖A‖ + ‖A‖_{X;max{k,3}} < ∞`** — the proof's "`We may assume $n_A<\infty$`": when `n_A = ∞` the
paper's right side is `+∞`, but in `ℝ≥0∞` `0 · ⊤ = 0`, so for `X = ∅` and an even non-scalar `A` the unrestricted
transcription would be false (its left side is `⊤`). -/
theorem setNorm_dyn_le {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {k : ℝ} (hk : 0 ≤ k) (Ch : ℝ) (CH : ℕ → ℝ) :
    ∃ Ck : ℝ, ∀ (η : ℝ → ℝ), IsProfile η → ∀ (Ts : TorusSeq δ₀) (H : (N : ℕ) → FockOp (Ts.T N))
      (d : H1Data η δ₀ Ts H), d.Ch = Ch → d.CH = CH →
        ∀ N ∈ Ts.idx, ∀ A : Op (Slot δ₀ (Ts.T N)), IsEven A → ∀ (X : Finset (Slot δ₀ (Ts.T N))) (t : ℝ),
          setNorm A X (max k 3) ≠ ⊤ →
          setNorm (dyn (Hhat η δ₀ Ts H N) t A) X k ≤
            ENNReal.ofReal (Ck * (1 + |t|) ^ (4 * k) * (X.card : ℝ)) *
              (ENNReal.ofReal ‖opCLM A‖ + setNorm A X (max k 3)) := by
  obtain ⟨Clc, Cτ, hc⟩ := propagation_polynomial hδ₀ (by norm_num : (1 : ℝ) < 4) (by linarith : (0 : ℝ) < k + 2)
    Ch CH
  refine ⟨max (3 ^ (k + 2) * |Cτ| * Cvol δ₀ + 2 ^ max k 3) ((3 * max Clc 1) ^ k), ?_⟩
  intro η hη Ts H d hCh hCH N hN A hA X t hfin
  have hT := Ts.admissible N hN
  have hHsa := isSelfAdjoint_Hhat hη hδ₀ d N hN
  have hHC : Hhat η δ₀ Ts H N ∈ CAR (Finset.univ : Finset (Slot δ₀ (Ts.T N))) := by
    rw [Fermion.Pilot.JW.CAR_univ]; exact StarSubalgebra.mem_top
  have hS0 : 0 ≤ (setNorm A X (max k 3)).toReal := ENNReal.toReal_nonneg
  have hM1 : (1 : ℝ) ≤ max Clc 1 := le_max_right _ _
  have hCvol : 0 ≤ Cvol δ₀ := by
    unfold Cvol
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (le_trans zero_le_one (le_max_left _ _))
  have hCk0 : 0 ≤ max (3 ^ (k + 2) * |Cτ| * Cvol δ₀ + 2 ^ max k 3) ((3 * max Clc 1) ^ k) :=
    le_trans (Real.rpow_nonneg (by linarith) _) (le_max_right _ _)
  have ht1 : (1 : ℝ) ≤ (1 + |t|) ^ (4 * k) := Real.one_le_rpow (by linarith [abs_nonneg t]) (by linarith)
  have hp0 : 0 ≤ max (3 ^ (k + 2) * |Cτ| * Cvol δ₀ + 2 ^ max k 3) ((3 * max Clc 1) ^ k) *
      (1 + |t|) ^ (4 * k) * (X.card : ℝ) :=
    mul_nonneg (mul_nonneg hCk0 (by linarith)) (Nat.cast_nonneg _)
  have e1 : ENNReal.ofReal ‖opCLM A‖ + setNorm A X (max k 3) =
      ENNReal.ofReal (‖opCLM A‖ + (setNorm A X (max k 3)).toReal) := by
    rw [ENNReal.ofReal_add (norm_nonneg _) hS0, ENNReal.ofReal_toReal hfin]
  have hRHS : ENNReal.ofReal (max (3 ^ (k + 2) * |Cτ| * Cvol δ₀ + 2 ^ max k 3) ((3 * max Clc 1) ^ k) *
        (1 + |t|) ^ (4 * k) * (X.card : ℝ)) * (ENNReal.ofReal ‖opCLM A‖ + setNorm A X (max k 3)) =
      ENNReal.ofReal (max (3 ^ (k + 2) * |Cτ| * Cvol δ₀ + 2 ^ max k 3) ((3 * max Clc 1) ^ k) *
        (1 + |t|) ^ (4 * k) * (X.card : ℝ) * (‖opCLM A‖ + (setNorm A X (max k 3)).toReal)) := by
    rw [ENNReal.ofReal_mul hp0, e1]
  rw [hRHS]
  rcases Finset.eq_empty_or_nonempty X with hX | hX
  · -- `X = ∅`: `A` is a scalar and both sides vanish
    subst hX
    obtain ⟨B₀, hB₀, hB₀inf⟩ := exists_nearest_le_iInf (∅ : Finset (Slot δ₀ (Ts.T N))) A
    have hbdd0 : BddBelow (Set.range fun A' : Alg (∅ : Finset (Slot δ₀ (Ts.T N))) =>
        ‖opCLM (A - (A' : Op (Slot δ₀ (Ts.T N))))‖) := ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
    have hle : ∀ r : ℝ, 0 ≤ r → ‖opCLM (A - B₀)‖ ≤ (setNorm A ∅ (max k 3)).toReal * (1 + r)⁻¹ := by
      intro r hr
      obtain ⟨B, hB, hAB⟩ := exists_approx_of_setNorm hfin hr
      rw [fat_empty_prop] at hB
      have h1 : ‖opCLM (A - B₀)‖ ≤ ‖opCLM (A - B)‖ := hB₀inf.trans (ciInf_le hbdd0 ⟨B, hB⟩)
      have h2 : (1 + r) ^ (-(max k 3)) ≤ (1 + r)⁻¹ := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [le_max_right k 3])
      calc ‖opCLM (A - B₀)‖ ≤ ‖opCLM (A - B)‖ := h1
        _ ≤ (setNorm A ∅ (max k 3)).toReal * (1 + r) ^ (-(max k 3)) := hAB
        _ ≤ (setNorm A ∅ (max k 3)).toReal * (1 + r)⁻¹ := mul_le_mul_of_nonneg_left h2 hS0
    have h0 := le_zero_of_forall_le_inv' hS0 hle
    have h0' : ‖opCLM (A - B₀)‖ = 0 := le_antisymm h0 (norm_nonneg _)
    have hAB₀ : A - B₀ = 0 := by
      open scoped Matrix.Norms.L2Operator in
      (rw [norm_opCLM_eq_l2] at h0'; exact norm_eq_zero.mp h0')
    have hA0 : A ∈ Alg (∅ : Finset (Slot δ₀ (Ts.T N))) := by
      rw [sub_eq_zero.mp hAB₀]; exact hB₀
    have hdyn : dyn (Hhat η δ₀ Ts H N) t A = A :=
      dyn_eq_of_commute (commute_of_mem_Alg_of_mem_CAR (Finset.disjoint_empty_left _) hA0 hHC) t
    rw [hdyn, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, ENNReal.ofReal_zero]
    unfold setNorm
    refine iSup₂_le fun r _ => ?_
    have hmem : A ∈ Alg (fat (∅ : Finset (Slot δ₀ (Ts.T N))) r) := by rw [fat_empty_prop]; exact hA0
    have hbdd : BddBelow (Set.range fun A' : Alg (fat (∅ : Finset (Slot δ₀ (Ts.T N))) r) =>
        ‖opCLM (A - (A' : Op (Slot δ₀ (Ts.T N))))‖) := ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
    have h1 := ciInf_le hbdd ⟨A, hmem⟩
    simp only [sub_self, opCLM_zero', norm_zero] at h1
    rw [ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by positivity) _) h1)]
  · -- `X ≠ ∅`
    have hX1 : (1 : ℝ) ≤ X.card := by exact_mod_cast hX.card_pos
    unfold setNorm
    refine iSup₂_le fun r hr => ENNReal.ofReal_le_ofReal ?_
    have hbdd : BddBelow (Set.range fun A' : Alg (fat X r) =>
        ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - (A' : Op (Slot δ₀ (Ts.T N))))‖) :=
      ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
    have ht4 : (1 : ℝ) ≤ (1 + |t|) ^ (4 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
    by_cases hlarge : 2 * max Clc 1 * (1 + |t|) ^ (4 : ℝ) ≤ r
    · -- large radii: one approximant propagated at order `k + 2`
      have hM4 : 1 ≤ max Clc 1 * (1 + |t|) ^ (4 : ℝ) := one_le_mul_of_one_le_of_one_le hM1 ht4
      have hr2 : 2 ≤ r := by linarith
      have hρ0 : 0 ≤ r / 2 := by linarith
      obtain ⟨B, hB, hAB⟩ := exists_approx_of_setNorm hfin hρ0
      have hClc : Clc * (1 + |t|) ^ (4 : ℝ) ≤ r / 2 := by
        have h1 : Clc * (1 + |t|) ^ (4 : ℝ) ≤ max Clc 1 * (1 + |t|) ^ (4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
        linarith
      have hcB := hc η hη Ts H d hCh hCH N hN (fat X (r / 2)) B hB t (r / 2) hClc
      obtain ⟨B', hB', hB'inf⟩ := exists_nearest_le_iInf (fat (fat X (r / 2)) (r / 2))
        (dyn (Hhat η δ₀ Ts H N) t B)
      have hB'r : B' ∈ Alg (fat X r) := by
        refine Alg_mono ?_ hB'
        have h := fat_fat_subset X (r / 2) (r / 2)
        rwa [show r / 2 + r / 2 = r by ring] at h
      have hdec : dyn (Hhat η δ₀ Ts H N) t A - B' =
          (dyn (Hhat η δ₀ Ts H N) t B - B') + dyn (Hhat η δ₀ Ts H N) t (A - B) := by
        rw [dyn_sub]
        abel
      have hρle : (1 + r / 2) ^ (-(max k 3)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith [le_max_right k 3])
      have hBn : ‖opCLM B‖ ≤ ‖opCLM A‖ + (setNorm A X (max k 3)).toReal := by
        have e : B = A - (A - B) := by abel
        calc ‖opCLM B‖ = ‖opCLM A - opCLM (A - B)‖ := by rw [← opCLM_sub', ← e]
          _ ≤ ‖opCLM A‖ + ‖opCLM (A - B)‖ := norm_sub_le _ _
          _ ≤ ‖opCLM A‖ + (setNorm A X (max k 3)).toReal * 1 :=
              add_le_add le_rfl (hAB.trans (mul_le_mul_of_nonneg_left hρle hS0))
          _ = _ := by rw [mul_one]
      have hcard := card_fat_le hδ₀ hT X hρ0
      have hpow0 : 0 ≤ (r / 2) ^ (-(k + 2)) := Real.rpow_nonneg hρ0 _
      have hτB : ‖opCLM (dyn (Hhat η δ₀ Ts H N) t B - B')‖ ≤
          |Cτ| * (‖opCLM A‖ + (setNorm A X (max k 3)).toReal) * (Cvol δ₀ * (1 + r / 2) ^ (2 : ℝ) * X.card) *
            (r / 2) ^ (-(k + 2)) := by
        refine hB'inf.trans (hcB.trans ?_)
        rw [show (1 + r / 2) ^ (2 : ℝ) = (1 + r / 2) ^ (2 : ℕ) by norm_cast]
        refine mul_le_mul_of_nonneg_right ?_ hpow0
        refine mul_le_mul (mul_le_mul (le_abs_self _) hBn (norm_nonneg _) (abs_nonneg _)) hcard (Nat.cast_nonneg _)
          (mul_nonneg (abs_nonneg _) (add_nonneg (norm_nonneg _) hS0))
      have hsplit : ⨅ A' : Alg (fat X r), ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - (A' : Op (Slot δ₀ (Ts.T N))))‖ ≤
          ‖opCLM ((dyn (Hhat η δ₀ Ts H N) t B - B') + dyn (Hhat η δ₀ Ts H N) t (A - B))‖ := by
        rw [← hdec]
        exact ciInf_le hbdd ⟨B', hB'r⟩
      have hnorm : ‖opCLM ((dyn (Hhat η δ₀ Ts H N) t B - B') + dyn (Hhat η δ₀ Ts H N) t (A - B))‖ ≤
          ‖opCLM (dyn (Hhat η δ₀ Ts H N) t B - B')‖ + ‖opCLM (A - B)‖ := by
        rw [opCLM_add', ← norm_dyn hHsa t (A - B)]
        exact norm_add_le _ _
      exact large_radius_final hCvol hX1 (norm_nonneg _) hS0 hk (le_max_left k 3) hr2 (le_max_left _ _) ht1
        (hsplit.trans (hnorm.trans (add_le_add hτB hAB)))
    · -- small radii: the approximant `0`
      have hsmall : r < 2 * max Clc 1 * (1 + |t|) ^ (4 : ℝ) := lt_of_not_ge hlarge
      have h0 := ciInf_le hbdd ⟨0, zero_mem _, Commute.zero_left _⟩
      simp only [sub_zero] at h0
      rw [norm_dyn hHsa] at h0
      exact small_radius_final hM1 hk hr hsmall (le_max_right _ _) hX1 (norm_nonneg _) hS0 h0

end HRTorus.Locality
