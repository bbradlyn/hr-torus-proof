import HRTorus.Locality.LiebRobinson
import HRTorus.Hamiltonian.BandCharges

/-!
# The locality calculus and the bookkeeping (T-0056 block D, `Locality.Calculus`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **Proof phase, rounds one and two (recruit L10, 2026-10-24/25):
every theorem is proved on the standard axioms; there is no `sorry` in this module. Lemma 5.12(a)
`norm_comm_le_of_disjoint`, Lemma 5.12(b) `almostSupported_add_star_mul` and both conclusions of Lemma 5.13
(`bookkeeping_comm`, `IsONegInf.sum_mul_mul`) in round one; Lemma 5.12(c) `ordExp_almostSupported` in round two by an
energy estimate against a projection onto `Alg(X^{(r)})` (no second equation is solved, and the continuity hypothesis
in `u` is not used), Lemma 5.12(d) `exp_Qband_add_almostSupported` from (c) and block C's Lemma 4.11(iii). The proofs
add devices, each marked as a device.** The paper: the HR paper,
`papers/hr/sections/05-locality.tex` — Lemma 5.12 `lem:calculus` (a)–(d) and Lemma 5.13 `lem:bookkeeping`; Remark 5.14
`rem:bookkeeping` is prose and is not stated. This module is upstream of `Locality.Filters` because the proof of
Proposition 5.11 cites Lemma 5.12(b); it uses no Hamiltonian (Lemma 5.12 assumes only admissible tori).

## The model

* Sequences of operators on `𝔉`, almost-supported sequences and their constants are block B's (`TorusSeq`,
  `ASBound … m C`, the norms `‖toCLM ·‖`); the distance `d(X_N, Y_N)` is `slotSetDist` (module `LiebRobinson`, in
  `ℝ≥0∞`, `⊤` when a set is empty), so Lemma 5.12(a)'s factor `(1 + d)^{−k}` is the `ℝ≥0∞` power `((1 + d)⁻¹)^k` and the
  bound is stated in `ℝ≥0∞` (its right side is `0` when a set is empty and `k ≥ 1`: the commutator vanishes then, since
  an operator almost supported in `∅` is a scalar).
* **"Depending only on the constants of …"** is the quantifier order, as in block C's Lemma 4.11(iii): the new
  constants are chosen after the data they may depend on and before the profile, `δ₀`, the tori and the sequences.
* **Lemma 5.12(c)** is stated for a **given** solution `V_N` of `V_N'(u) = iV_N(u)G_N(u)`, `V_N(0) = 1`, on `[0, u₀]`,
  the derivative taken in the normed space of continuous linear maps (`toCLM`), within `[0, u₀]`.
* **`O(N^{−∞})`** (`IsONegInf`): a family `a_p = (a_{p,N})_N` of operators on `𝔉`, indexed by a parameter `p` in any
  type, with, for every `k ∈ ℕ`, one constant `C_k` such that `‖a_{p,N}‖ ≤ C_k N^{−k}` for all `p` and `N ∈ 𝒩` ("uniformly
  in the parameter"; a parameter-free sequence is the case `P = Unit`).
* **Lemma 5.13**: the first conclusion for any two families `O`, `O'` of the finite set `𝒪` (the set enters only through
  the common bounds `C`, `m_*`), with the result's constants after `c`, `C`, `m_*` and the constants of `O`, `O'`; the
  hypothesis `L_x ≥ c_*√N` kept literally ("`The hypothesis $L_x\ge c_*\sqrt N$ enters only through the assumed separations.`").
  The second conclusion is a statement about a finite family of `O(N^{−∞})` commutators — sums, over a finite index set
  independent of `N`, of products `L_i c_i R_i` with operators of norm at most `CN^m` — the form of §6's uses (sums of
  `±` commutators in the proof of Lemma 6.13(iii), `P[·]P` in the proof of Lemma 6.14).
-/

open scoped InnerProductSpace Matrix ENNReal Real
open Complex (I)

noncomputable section

namespace HRTorus.Locality

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op c chat parityOp IsEven CAR Alg condExp)

/-! ## Lemma 5.12 -/

/-! ### Proof devices for Lemmas 5.12(a)–(b) and 5.13 (phase (b); not statements of the paper) -/

theorem one_le_of_mem_idx {δ₀ : ℝ} (Ts : TorusSeq δ₀) {N : ℕ} (hN : N ∈ Ts.idx) : (1 : ℝ) ≤ N := by
  have h := (Ts.T N).N_pos
  rw [Ts.T_N N hN] at h
  exact_mod_cast h

theorem toCLM_mul' (T : Torus) (X Y : FockOp T) : toCLM T (X * Y) = toCLM T X * toCLM T Y :=
  map_mul (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) X Y

theorem toCLM_sub' (T : Torus) (X Y : FockOp T) : toCLM T (X - Y) = toCLM T X - toCLM T Y :=
  map_sub (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) X Y

theorem toCLM_sum' (T : Torus) {ι : Type*} (F : Finset ι) (X : ι → FockOp T) :
    toCLM T (∑ i ∈ F, X i) = ∑ i ∈ F, toCLM T (X i) :=
  map_sum (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) X F

theorem iota_sub' {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀)
    (A B : FockOp T) : iota η δ₀ T (A - B) = iota η δ₀ T A - iota η δ₀ T B := by
  rw [← iotaHom_apply hη hδ₀ hT, ← iotaHom_apply hη hδ₀ hT, ← iotaHom_apply hη hδ₀ hT, map_sub]

theorem Alg_add_mem' {S : Type*} [Fintype S] [DecidableEq S] {X : Finset S} {A B : Op S} (hA : A ∈ Alg X)
    (hB : B ∈ Alg X) : A + B ∈ Alg X :=
  ⟨add_mem hA.1 hB.1, hA.2.add_left hB.2⟩

theorem Alg_conjTranspose_mem' {S : Type*} [Fintype S] [DecidableEq S] {X : Finset S} {A : Op S}
    (hA : A ∈ Alg X) : Aᴴ ∈ Alg X := by
  refine ⟨?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact star_mem hA.1
  · have h := hA.2.star_star
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, parityOp_conjTranspose] at h
    exact h

/-- `‖A'‖ ≤ ‖A‖ + ‖ι(A) − A'‖`. -/
theorem norm_approx_le {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) (A : FockOp T) (A' : Op (Slot δ₀ T)) :
    ‖opCLM A'‖ ≤ ‖toCLM T A‖ + ‖opCLM (iota η δ₀ T A - A')‖ := by
  have e : A' = iota η δ₀ T A - (iota η δ₀ T A - A') := by abel
  calc ‖opCLM A'‖ = ‖opCLM (iota η δ₀ T A) - opCLM (iota η δ₀ T A - A')‖ := by rw [← opCLM_sub', ← e]
    _ ≤ ‖opCLM (iota η δ₀ T A)‖ + ‖opCLM (iota η δ₀ T A - A')‖ := norm_sub_le _ _
    _ = _ := by rw [norm_iota hη hδ₀ hT]

theorem rpow_le_rpow_of_one_le {x a b : ℝ} (hx : 1 ≤ x) (hab : a ≤ b) : x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_le hx hab

theorem rpow_mul_rpow_le {x a b c : ℝ} (hx : 1 ≤ x) (habc : a + b ≤ c) : x ^ a * x ^ b ≤ x ^ c := by
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hx habc

theorem one_add_rpow_neg_le_one {r : ℝ} (hr : 0 ≤ r) (k : ℕ) : (1 + r) ^ (-(k : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simp)

theorem one_add_rpow_neg_nonneg {r : ℝ} (hr : 0 ≤ r) (k : ℕ) : 0 ≤ (1 + r) ^ (-(k : ℝ)) :=
  Real.rpow_nonneg (by linarith) _

theorem slotDist_comm' {δ₀ : ℝ} {T : Torus} (s s' : Slot δ₀ T) : slotDist δ₀ T s s' = slotDist δ₀ T s' s := by
  simp only [slotDist, flatDist]
  rw [← neg_sub (centre δ₀ T s).1, ← neg_sub (centre δ₀ T s).2, pdist_neg, pdist_neg]

theorem fat_empty' {δ₀ : ℝ} {T : Torus} (r : ℝ) : fat (∅ : Finset (Slot δ₀ T)) r = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun s hs => ?_
  obtain ⟨s', hs', _⟩ := mem_fat.mp hs
  exact Finset.notMem_empty s' hs'

/-- The arithmetic of Lemma 5.12(a). -/
theorem comm_arith {ea eb nB nA' a b α β x y P ρ : ℝ} (hea0 : 0 ≤ ea) (heb0 : 0 ≤ eb) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hx : 0 ≤ x) (hy : 0 ≤ y) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hxP : x ≤ P) (hyP : y ≤ P) (hxy : x * y ≤ P) (hea : ea ≤ α * x * ρ) (heb : eb ≤ β * y * ρ)
    (hnB : nB = b) (hnA' : nA' ≤ a + α * x * ρ) :
    2 * ea * nB + 2 * nA' * eb ≤ (2 * α + 2 * β + 2 * α * β) * P * (1 + a + b) * ρ := by
  rw [hnB]
  have hP : 0 ≤ P := hx.trans hxP
  have hαx : 0 ≤ α * x * ρ := mul_nonneg (mul_nonneg hα hx) hρ0
  have h1 : 2 * ea * b ≤ 2 * (α * x * ρ) * b :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hea (by norm_num)) hb
  have h2 : 2 * nA' * eb ≤ 2 * (a + α * x * ρ) * (β * y * ρ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hnA' (by norm_num)) heb heb0
      (mul_nonneg (by norm_num) (add_nonneg ha hαx))
  have hρρ : ρ * ρ ≤ ρ := by
    calc ρ * ρ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hρ1 hρ0
      _ = ρ := mul_one ρ
  have h3 : 2 * (α * x * ρ) * b ≤ 2 * α * P * ρ * b := by
    calc 2 * (α * x * ρ) * b = (2 * α * ρ * b) * x := by ring
      _ ≤ (2 * α * ρ * b) * P :=
          mul_le_mul_of_nonneg_left hxP (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα) hρ0) hb)
      _ = 2 * α * P * ρ * b := by ring
  have h4 : 2 * (a + α * x * ρ) * (β * y * ρ) ≤ 2 * β * P * ρ * a + 2 * α * β * P * ρ := by
    have e : 2 * (a + α * x * ρ) * (β * y * ρ) = (2 * β * ρ * a) * y + (2 * α * β) * (x * y) * (ρ * ρ) := by
      ring
    rw [e]
    have h5 : (2 * β * ρ * a) * y ≤ (2 * β * ρ * a) * P :=
      mul_le_mul_of_nonneg_left hyP (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hβ) hρ0) ha)
    have h6 : (2 * α * β) * (x * y) * (ρ * ρ) ≤ (2 * α * β) * P * ρ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hxy (mul_nonneg (mul_nonneg (by norm_num) hα) hβ)) hρρ
        (mul_nonneg hρ0 hρ0) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hα) hβ) hP)
    calc (2 * β * ρ * a) * y + (2 * α * β) * (x * y) * (ρ * ρ) ≤ (2 * β * ρ * a) * P + (2 * α * β) * P * ρ :=
          add_le_add h5 h6
      _ = 2 * β * P * ρ * a + 2 * α * β * P * ρ := by ring
  have hαP : 0 ≤ α * P * ρ := mul_nonneg (mul_nonneg hα hP) hρ0
  have hβP : 0 ≤ β * P * ρ := mul_nonneg (mul_nonneg hβ hP) hρ0
  have hαβP : 0 ≤ α * β * P * ρ := mul_nonneg (mul_nonneg (mul_nonneg hα hβ) hP) hρ0
  have h7 : 2 * α * P * ρ * b + (2 * β * P * ρ * a + 2 * α * β * P * ρ) ≤
      (2 * α + 2 * β + 2 * α * β) * P * (1 + a + b) * ρ := by
    nlinarith [mul_nonneg hαP ha, mul_nonneg hβP hb, mul_nonneg hαβP ha, mul_nonneg hαβP hb]
  linarith

/-- The core of Lemma 5.12(a): the estimate at a radius `r` whose fattenings are disjoint. -/
theorem norm_comm_le_of_fat_disjoint {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {Ts : TorusSeq δ₀}
    {X Y : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))} {A B : (N : ℕ) → FockOp (Ts.T N)} {mA mB : ℝ} {CA CB : ℕ → ℝ}
    (hA : ASBound η δ₀ Ts X A mA CA) (hB : ASBound η δ₀ Ts Y B mB CB) (k : ℕ) {N : ℕ} (hN : N ∈ Ts.idx)
    {r : ℝ} (hr : 0 ≤ r) (hdisj : Disjoint (fat (X N) r) (fat (Y N) r)) :
    ‖toCLM (Ts.T N) (A N * B N - B N * A N)‖ ≤
      (2 * |CA k| + 2 * |CB k| + 2 * |CA k| * |CB k|) * (N : ℝ) ^ (mA + mB) *
        (1 + ‖toCLM (Ts.T N) (A N)‖ + ‖toCLM (Ts.T N) (B N)‖) * (1 + r) ^ (-(k : ℝ)) := by
  obtain ⟨hmA, hA⟩ := hA
  obtain ⟨hmB, hB⟩ := hB
  obtain ⟨A', hA'm, hA'⟩ := hA k N hN r hr
  obtain ⟨B', hB'm, hB'⟩ := hB k N hN r hr
  have hT := Ts.admissible N hN
  have hN1 := one_le_of_mem_idx Ts hN
  have hρ := one_add_rpow_neg_nonneg hr k
  have hρ1 := one_add_rpow_neg_le_one hr k
  have hx0 : 0 ≤ (N : ℝ) ^ mA := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hy0 : 0 ≤ (N : ℝ) ^ mB := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hxP : (N : ℝ) ^ mA ≤ (N : ℝ) ^ (mA + mB) := rpow_le_rpow_of_one_le hN1 (by linarith)
  have hyP : (N : ℝ) ^ mB ≤ (N : ℝ) ^ (mA + mB) := rpow_le_rpow_of_one_le hN1 (by linarith)
  have hxy : (N : ℝ) ^ mA * (N : ℝ) ^ mB ≤ (N : ℝ) ^ (mA + mB) := rpow_mul_rpow_le hN1 le_rfl
  have hea1 : ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A')‖ ≤ |CA k| * (N : ℝ) ^ mA * (1 + r) ^ (-(k : ℝ)) :=
    hA'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hx0) hρ)
  have heb1 : ‖opCLM (iota η δ₀ (Ts.T N) (B N) - B')‖ ≤ |CB k| * (N : ℝ) ^ mB * (1 + r) ^ (-(k : ℝ)) :=
    hB'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) hρ)
  have hnA' : ‖opCLM A'‖ ≤ ‖toCLM (Ts.T N) (A N)‖ + |CA k| * (N : ℝ) ^ mA * (1 + r) ^ (-(k : ℝ)) :=
    (norm_approx_le hη hδ₀ hT (A N) A').trans (add_le_add le_rfl hea1)
  have hc : A' * B' - B' * A' = 0 := by
    rw [(commute_of_mem_Alg_of_mem_Alg hdisj hA'm hB'm).eq, sub_self]
  have e : iota η δ₀ (Ts.T N) (A N * B N - B N * A N) =
      ((iota η δ₀ (Ts.T N) (A N) - A') * iota η δ₀ (Ts.T N) (B N) -
          iota η δ₀ (Ts.T N) (B N) * (iota η δ₀ (Ts.T N) (A N) - A')) +
        (A' * (iota η δ₀ (Ts.T N) (B N) - B') - (iota η δ₀ (Ts.T N) (B N) - B') * A') +
        (A' * B' - B' * A') := by
    rw [iota_sub' hη hδ₀ hT, iota_mul hη hδ₀ hT, iota_mul hη hδ₀ hT]
    noncomm_ring
  rw [← norm_iota hη hδ₀ hT, e, hc, add_zero, opCLM_add']
  calc _ ≤ ‖opCLM ((iota η δ₀ (Ts.T N) (A N) - A') * iota η δ₀ (Ts.T N) (B N) -
          iota η δ₀ (Ts.T N) (B N) * (iota η δ₀ (Ts.T N) (A N) - A'))‖ +
        ‖opCLM (A' * (iota η δ₀ (Ts.T N) (B N) - B') - (iota η δ₀ (Ts.T N) (B N) - B') * A')‖ :=
        norm_add_le _ _
    _ ≤ 2 * ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A')‖ * ‖opCLM (iota η δ₀ (Ts.T N) (B N))‖ +
        2 * ‖opCLM A'‖ * ‖opCLM (iota η δ₀ (Ts.T N) (B N) - B')‖ :=
        add_le_add (norm_comm_le _ _) (norm_comm_le _ _)
    _ ≤ _ := comm_arith (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (abs_nonneg _)
          (abs_nonneg _) hx0 hy0 hρ hρ1 hxP hyP hxy hea1 heb1 (norm_iota hη hδ₀ hT _) hnA'

/-- If `v ≤ c (1 + r)⁻¹` for every `r ≥ 0`, with `c ≥ 0`, then `v ≤ 0`. -/
theorem le_zero_of_forall_le_inv {v c : ℝ} (hc : 0 ≤ c) (h : ∀ r : ℝ, 0 ≤ r → v ≤ c * (1 + r)⁻¹) : v ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have h1 := h (c / v) (div_nonneg hc hpos.le)
  have h2 : c * (1 + c / v)⁻¹ < v := by
    have hv : 0 < 1 + c / v := by positivity
    rw [← div_eq_mul_inv, div_lt_iff₀ hv, mul_add, mul_one, mul_div_cancel₀ _ hpos.ne']
    nlinarith
  linarith

theorem one_add_div_three_rpow_le {δ : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    (1 + δ / 3) ^ (-(k : ℝ)) ≤ 3 ^ k * (1 + δ) ^ (-(k : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_natCast,
    ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by linarith) k

theorem ennreal_inv_pow_eq {δ : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    (1 + ENNReal.ofReal δ)⁻¹ ^ k = ENNReal.ofReal ((1 + δ) ^ (-(k : ℝ))) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow,
    ENNReal.ofReal_pow (inv_nonneg.mpr (by positivity)), ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_add zero_le_one hδ, ENNReal.ofReal_one]

theorem disjoint_fat_third {δ₀ : ℝ} {T : Torus} {X Y : Finset (Slot δ₀ T)} (hXY : Disjoint X Y)
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    Disjoint (fat X (((X ×ˢ Y).inf' (hX.product hY) fun p => slotDist δ₀ T p.1 p.2) / 3))
      (fat Y (((X ×ˢ Y).inf' (hX.product hY) fun p => slotDist δ₀ T p.1 p.2) / 3)) := by
  set δ := (X ×ˢ Y).inf' (hX.product hY) fun p => slotDist δ₀ T p.1 p.2 with hδ
  have hδ0 : 0 ≤ δ := Finset.le_inf' _ _ fun p _ => slotDist_nonneg' _ _
  rcases hδ0.lt_or_eq with hpos | hzero
  · rw [Finset.disjoint_left]
    intro s hsX hsY
    obtain ⟨x, hx, hdx⟩ := mem_fat.mp hsX
    obtain ⟨y, hy, hdy⟩ := mem_fat.mp hsY
    have hmem : ((x, y) : Slot δ₀ T × Slot δ₀ T) ∈ X ×ˢ Y := Finset.mem_product.mpr ⟨hx, hy⟩
    have hle : δ ≤ slotDist δ₀ T x y := Finset.inf'_le (fun p : Slot δ₀ T × Slot δ₀ T => slotDist δ₀ T p.1 p.2) hmem
    have htri := slotDist_triangle x s y
    rw [slotDist_comm' x s] at htri
    linarith
  · rw [← hzero, zero_div, fat_zero, fat_zero]
    exact hXY

/-- **Lemma 5.12(a)** (far-apart operators almost commute): "`If $A\in\AS_X$ and $B\in\AS_Y$ are even, with prefactor exponents $m_A$ and $m_B$, then for every $k$ there is $C_k$, depending only on the constants of $A$ and $B$, with`"
"`\norm{[A_N,B_N]}\le C_kN^{m_A+m_B}\bigl(1+\norm{A_N}+\norm{B_N}\bigr)\bigl(1+d(X_N,Y_N)\bigr)^{-k}`"
"`for every $N$ with $X_N\cap Y_N=\emptyset$.`" — in `ℝ≥0∞` (the module docstring); the constant after the constants
`C^A`, `C^B` and `k` only. -/
theorem norm_comm_le_of_disjoint (CA CB : ℕ → ℝ) (k : ℕ) :
    ∃ Ck : ℝ, ∀ (η : ℝ → ℝ) (δ₀ : ℝ), IsProfile η → 0 < δ₀ → ∀ (Ts : TorusSeq δ₀)
      (X Y : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))) (A B : (N : ℕ) → FockOp (Ts.T N)) (mA mB : ℝ),
      (∀ N ∈ Ts.idx, IsEven (A N)) → (∀ N ∈ Ts.idx, IsEven (B N)) →
      ASBound η δ₀ Ts X A mA CA → ASBound η δ₀ Ts Y B mB CB →
      ∀ N ∈ Ts.idx, Disjoint (X N) (Y N) →
        ENNReal.ofReal ‖toCLM (Ts.T N) (A N * B N - B N * A N)‖ ≤
          ENNReal.ofReal (Ck * (N : ℝ) ^ (mA + mB) *
              (1 + ‖toCLM (Ts.T N) (A N)‖ + ‖toCLM (Ts.T N) (B N)‖)) *
            (1 + slotSetDist (X N) (Y N))⁻¹ ^ k := by
  refine ⟨3 ^ k * (2 * |CA k| + 2 * |CB k| + 2 * |CA k| * |CB k|), ?_⟩
  intro η δ₀ hη hδ₀ Ts X Y A B mA mB _ _ hA hB N hN hXY
  have hK0 : 0 ≤ 2 * |CA k| + 2 * |CB k| + 2 * |CA k| * |CB k| := by positivity
  have hQ0 : 0 ≤ (N : ℝ) ^ (mA + mB) * (1 + ‖toCLM (Ts.T N) (A N)‖ + ‖toCLM (Ts.T N) (B N)‖) := by positivity
  have hbound := fun (r : ℝ) (hr : 0 ≤ r) (hd : Disjoint (fat (X N) r) (fat (Y N) r)) =>
    norm_comm_le_of_fat_disjoint hη hδ₀ hA hB k hN hr hd
  by_cases hd : slotSetDist (X N) (Y N) = ⊤
  · have hempty : X N = ∅ ∨ Y N = ∅ := by
      rcases Finset.eq_empty_or_nonempty (X N) with hX | hX
      · exact Or.inl hX
      rcases Finset.eq_empty_or_nonempty (Y N) with hY | hY
      · exact Or.inr hY
      rw [slotSetDist_eq_inf' hX hY] at hd
      exact absurd hd ENNReal.ofReal_ne_top
    have hall : ∀ r : ℝ, Disjoint (fat (X N) r) (fat (Y N) r) := by
      intro r
      rcases hempty with h | h
      · rw [h, fat_empty']; exact Finset.disjoint_empty_left _
      · rw [h, fat_empty']; exact Finset.disjoint_empty_right _
    rw [hd, add_top, ENNReal.inv_top]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [pow_zero, mul_one, one_mul]
      apply ENNReal.ofReal_le_ofReal
      have h := hbound 0 le_rfl (hall 0)
      simp only [add_zero, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one, pow_zero, one_mul] at h ⊢
      linarith
    · rw [zero_pow hk.ne', mul_zero]
      have h0 : ‖toCLM (Ts.T N) (A N * B N - B N * A N)‖ ≤ 0 := by
        refine le_zero_of_forall_le_inv (mul_nonneg hK0 hQ0) fun r hr => ?_
        refine (hbound r hr (hall r)).trans ?_
        have hk1 : (1 + r) ^ (-(k : ℝ)) ≤ (1 + r)⁻¹ := by
          rw [← Real.rpow_neg_one]
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          have : (1 : ℝ) ≤ k := by exact_mod_cast hk
          linarith
        calc (2 * |CA k| + 2 * |CB k| + 2 * |CA k| * |CB k|) * (N : ℝ) ^ (mA + mB) *
              (1 + ‖toCLM (Ts.T N) (A N)‖ + ‖toCLM (Ts.T N) (B N)‖) * (1 + r) ^ (-(k : ℝ))
            = ((2 * |CA k| + 2 * |CB k| + 2 * |CA k| * |CB k|) *
              ((N : ℝ) ^ (mA + mB) * (1 + ‖toCLM (Ts.T N) (A N)‖ + ‖toCLM (Ts.T N) (B N)‖))) *
                (1 + r) ^ (-(k : ℝ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hk1 (mul_nonneg hK0 hQ0)
      rw [le_antisymm h0 (norm_nonneg _), ENNReal.ofReal_zero]
  · have hX : (X N).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro h
      rw [h, slotSetDist_empty_left] at hd
      exact hd rfl
    have hY : (Y N).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro h
      rw [h, slotSetDist_empty_right] at hd
      exact hd rfl
    have hδ0 : 0 ≤ (X N ×ˢ Y N).inf' (hX.product hY) (fun p => slotDist δ₀ (Ts.T N) p.1 p.2) :=
      Finset.le_inf' _ _ fun p _ => slotDist_nonneg' _ _
    have hb := hbound _ (div_nonneg hδ0 (by norm_num)) (disjoint_fat_third hXY hX hY)
    rw [slotSetDist_eq_inf' hX hY, ennreal_inv_pow_eq hδ0, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    refine hb.trans ?_
    have hρ := one_add_div_three_rpow_le hδ0 k
    calc (2 * |CA k| + 2 * |CB k| + 2 * |CA k| * |CB k|) * (N : ℝ) ^ (mA + mB) *
          (1 + ‖toCLM (Ts.T N) (A N)‖ + ‖toCLM (Ts.T N) (B N)‖) *
          (1 + (X N ×ˢ Y N).inf' (hX.product hY) (fun p => slotDist δ₀ (Ts.T N) p.1 p.2) / 3) ^ (-(k : ℝ))
        ≤ (2 * |CA k| + 2 * |CB k| + 2 * |CA k| * |CB k|) * (N : ℝ) ^ (mA + mB) *
          (1 + ‖toCLM (Ts.T N) (A N)‖ + ‖toCLM (Ts.T N) (B N)‖) *
          (3 ^ k * (1 + (X N ×ˢ Y N).inf' (hX.product hY) (fun p => slotDist δ₀ (Ts.T N) p.1 p.2)) ^ (-(k : ℝ))) :=
          mul_le_mul_of_nonneg_left hρ (by positivity)
      _ = _ := by ring

theorem norm_opCLM_conjTranspose' {S : Type*} [Fintype S] [DecidableEq S] (X : Op S) :
    ‖opCLM Xᴴ‖ = ‖opCLM X‖ := by
  open scoped Matrix.Norms.L2Operator in
  rw [norm_opCLM_eq_l2, norm_opCLM_eq_l2, Matrix.l2_opNorm_conjTranspose]

/-- The arithmetic of the product estimate. -/
theorem prod_arith {ea eb nB nA' α β γ x y z P ρ : ℝ} (heb0 : 0 ≤ eb) (hnB0 : 0 ≤ nB)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hxz : x * z ≤ P) (hzy : z * y ≤ P) (hxy : x * y ≤ P) (hea : ea ≤ α * x * ρ) (heb : eb ≤ β * y * ρ)
    (hnB : nB ≤ γ * z) (hnA' : nA' ≤ γ * z + α * x * ρ) :
    ea * nB + nA' * eb ≤ (γ * α + γ * β + α * β) * P * ρ := by
  have hP : 0 ≤ P := (mul_nonneg hx hy).trans hxy
  have hαx : 0 ≤ α * x * ρ := mul_nonneg (mul_nonneg hα hx) hρ0
  have hβy : 0 ≤ β * y * ρ := mul_nonneg (mul_nonneg hβ hy) hρ0
  have hγz : 0 ≤ γ * z := mul_nonneg hγ hz
  have h1 : ea * nB ≤ (α * x * ρ) * (γ * z) := mul_le_mul hea hnB hnB0 hαx
  have h2 : nA' * eb ≤ (γ * z + α * x * ρ) * (β * y * ρ) := mul_le_mul hnA' heb heb0 (add_nonneg hγz hαx)
  have h3 : (α * x * ρ) * (γ * z) ≤ γ * α * P * ρ := by
    calc (α * x * ρ) * (γ * z) = (γ * α * ρ) * (x * z) := by ring
      _ ≤ (γ * α * ρ) * P := mul_le_mul_of_nonneg_left hxz (mul_nonneg (mul_nonneg hγ hα) hρ0)
      _ = γ * α * P * ρ := by ring
  have h4 : (γ * z + α * x * ρ) * (β * y * ρ) ≤ γ * β * P * ρ + α * β * P * ρ := by
    have hρρ : ρ * ρ ≤ ρ := by
      calc ρ * ρ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hρ1 hρ0
        _ = ρ := mul_one ρ
    calc (γ * z + α * x * ρ) * (β * y * ρ) = (γ * β * ρ) * (z * y) + (α * β) * (x * y) * (ρ * ρ) := by ring
      _ ≤ (γ * β * ρ) * P + (α * β) * P * ρ := by
          refine add_le_add (mul_le_mul_of_nonneg_left hzy (mul_nonneg (mul_nonneg hγ hβ) hρ0)) ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_left hxy (mul_nonneg hα hβ)) hρρ (mul_nonneg hρ0 hρ0)
            (mul_nonneg (mul_nonneg hα hβ) hP)
      _ = γ * β * P * ρ + α * β * P * ρ := by ring
  calc ea * nB + nA' * eb ≤ γ * α * P * ρ + (γ * β * P * ρ + α * β * P * ρ) :=
        add_le_add (h1.trans h3) (h2.trans h4)
    _ = (γ * α + γ * β + α * β) * P * ρ := by ring

theorem asBound_add {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {Ts : TorusSeq δ₀}
    {X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))} {A B : (N : ℕ) → FockOp (Ts.T N)} {mA mB : ℝ} {CA CB : ℕ → ℝ}
    (hA : ASBound η δ₀ Ts X A mA CA) (hB : ASBound η δ₀ Ts X B mB CB) :
    ASBound η δ₀ Ts X (fun N => A N + B N) (max mA mB) fun k => |CA k| + |CB k| := by
  obtain ⟨hmA, hA⟩ := hA
  obtain ⟨hmB, hB⟩ := hB
  refine ⟨le_max_of_le_left hmA, ?_⟩
  intro k N hN r hr
  obtain ⟨A', hA'm, hA'⟩ := hA k N hN r hr
  obtain ⟨B', hB'm, hB'⟩ := hB k N hN r hr
  refine ⟨A' + B', Alg_add_mem' hA'm hB'm, ?_⟩
  have hT := Ts.admissible N hN
  have hN1 := one_le_of_mem_idx Ts hN
  have hρ := one_add_rpow_neg_nonneg hr k
  have hx : (N : ℝ) ^ mA ≤ (N : ℝ) ^ max mA mB := rpow_le_rpow_of_one_le hN1 (le_max_left _ _)
  have hy : (N : ℝ) ^ mB ≤ (N : ℝ) ^ max mA mB := rpow_le_rpow_of_one_le hN1 (le_max_right _ _)
  have hx0 : 0 ≤ (N : ℝ) ^ mA := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hy0 : 0 ≤ (N : ℝ) ^ mB := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : CA k * (N : ℝ) ^ mA * (1 + r) ^ (-(k : ℝ)) ≤
      |CA k| * (N : ℝ) ^ max mA mB * (1 + r) ^ (-(k : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hx hx0 (abs_nonneg _)) hρ
  have h2 : CB k * (N : ℝ) ^ mB * (1 + r) ^ (-(k : ℝ)) ≤
      |CB k| * (N : ℝ) ^ max mA mB * (1 + r) ^ (-(k : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hy hy0 (abs_nonneg _)) hρ
  show ‖opCLM (iota η δ₀ (Ts.T N) (A N + B N) - (A' + B'))‖ ≤ _
  rw [iota_add hη hδ₀ hT, add_sub_add_comm, opCLM_add']
  calc _ ≤ ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A')‖ + ‖opCLM (iota η δ₀ (Ts.T N) (B N) - B')‖ :=
        norm_add_le _ _
    _ ≤ |CA k| * (N : ℝ) ^ max mA mB * (1 + r) ^ (-(k : ℝ)) +
        |CB k| * (N : ℝ) ^ max mA mB * (1 + r) ^ (-(k : ℝ)) :=
        add_le_add (hA'.trans h1) (hB'.trans h2)
    _ = _ := by ring

theorem asBound_star {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {Ts : TorusSeq δ₀}
    {X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))} {A : (N : ℕ) → FockOp (Ts.T N)} {mA : ℝ} {CA : ℕ → ℝ}
    (hA : ASBound η δ₀ Ts X A mA CA) : ASBound η δ₀ Ts X (fun N => (A N)ᴴ) mA CA := by
  obtain ⟨hmA, hA⟩ := hA
  refine ⟨hmA, ?_⟩
  intro k N hN r hr
  obtain ⟨A', hA'm, hA'⟩ := hA k N hN r hr
  refine ⟨A'ᴴ, Alg_conjTranspose_mem' hA'm, ?_⟩
  have hT := Ts.admissible N hN
  show ‖opCLM (iota η δ₀ (Ts.T N) (A N)ᴴ - A'ᴴ)‖ ≤ _
  rw [iota_conjTranspose hη hδ₀ hT, ← Matrix.conjTranspose_sub, norm_opCLM_conjTranspose']
  exact hA'

theorem asBound_mul {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {Ts : TorusSeq δ₀}
    {X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))} {A B : (N : ℕ) → FockOp (Ts.T N)} {mA mB m' C : ℝ} {CA CB : ℕ → ℝ}
    (hm' : 0 ≤ m') (hA : ASBound η δ₀ Ts X A mA CA) (hB : ASBound η δ₀ Ts X B mB CB)
    (hAB : ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (A N)‖ ≤ C * (N : ℝ) ^ m' ∧ ‖toCLM (Ts.T N) (B N)‖ ≤ C * (N : ℝ) ^ m') :
    ASBound η δ₀ Ts X (fun N => A N * B N) (mA + mB + m')
      fun k => |C| * |CA k| + |C| * |CB k| + |CA k| * |CB k| := by
  obtain ⟨hmA, hA⟩ := hA
  obtain ⟨hmB, hB⟩ := hB
  refine ⟨by linarith, ?_⟩
  intro k N hN r hr
  obtain ⟨A', hA'm, hA'⟩ := hA k N hN r hr
  obtain ⟨B', hB'm, hB'⟩ := hB k N hN r hr
  refine ⟨A' * B', Alg_mul_mem hA'm hB'm, ?_⟩
  have hT := Ts.admissible N hN
  have hN1 := one_le_of_mem_idx Ts hN
  have hρ := one_add_rpow_neg_nonneg hr k
  have hρ1 := one_add_rpow_neg_le_one hr k
  obtain ⟨hAn, hBn⟩ := hAB N hN
  have hx0 : 0 ≤ (N : ℝ) ^ mA := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hy0 : 0 ≤ (N : ℝ) ^ mB := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hz0 : 0 ≤ (N : ℝ) ^ m' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hxz : (N : ℝ) ^ mA * (N : ℝ) ^ m' ≤ (N : ℝ) ^ (mA + mB + m') := rpow_mul_rpow_le hN1 (by linarith)
  have hzy : (N : ℝ) ^ m' * (N : ℝ) ^ mB ≤ (N : ℝ) ^ (mA + mB + m') := rpow_mul_rpow_le hN1 (by linarith)
  have hxy : (N : ℝ) ^ mA * (N : ℝ) ^ mB ≤ (N : ℝ) ^ (mA + mB + m') := rpow_mul_rpow_le hN1 (by linarith)
  have hea1 : ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A')‖ ≤ |CA k| * (N : ℝ) ^ mA * (1 + r) ^ (-(k : ℝ)) :=
    hA'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hx0) hρ)
  have heb1 : ‖opCLM (iota η δ₀ (Ts.T N) (B N) - B')‖ ≤ |CB k| * (N : ℝ) ^ mB * (1 + r) ^ (-(k : ℝ)) :=
    hB'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) hρ)
  have hnB : ‖opCLM (iota η δ₀ (Ts.T N) (B N))‖ ≤ |C| * (N : ℝ) ^ m' := by
    rw [norm_iota hη hδ₀ hT]
    exact hBn.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hz0)
  have hnA' : ‖opCLM A'‖ ≤ |C| * (N : ℝ) ^ m' + |CA k| * (N : ℝ) ^ mA * (1 + r) ^ (-(k : ℝ)) := by
    have h := norm_approx_le hη hδ₀ hT (A N) A'
    have hAn' : ‖toCLM (Ts.T N) (A N)‖ ≤ |C| * (N : ℝ) ^ m' :=
      hAn.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hz0)
    linarith
  have e : iota η δ₀ (Ts.T N) (A N * B N) - A' * B' =
      (iota η δ₀ (Ts.T N) (A N) - A') * iota η δ₀ (Ts.T N) (B N) +
        A' * (iota η δ₀ (Ts.T N) (B N) - B') := by
    rw [iota_mul hη hδ₀ hT]
    noncomm_ring
  show ‖opCLM (iota η δ₀ (Ts.T N) (A N * B N) - A' * B')‖ ≤ _
  rw [e, opCLM_add', opCLM_mul', opCLM_mul']
  calc _ ≤ ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A') * opCLM (iota η δ₀ (Ts.T N) (B N))‖ +
        ‖opCLM A' * opCLM (iota η δ₀ (Ts.T N) (B N) - B')‖ := norm_add_le _ _
    _ ≤ ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A')‖ * ‖opCLM (iota η δ₀ (Ts.T N) (B N))‖ +
        ‖opCLM A'‖ * ‖opCLM (iota η δ₀ (Ts.T N) (B N) - B')‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (|C| * |CA k| + |C| * |CB k| + |CA k| * |CB k|) * (N : ℝ) ^ (mA + mB + m') * (1 + r) ^ (-(k : ℝ)) :=
        prod_arith (norm_nonneg _) (norm_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hx0 hy0 hz0 hρ hρ1
          hxz hzy hxy hea1 heb1 hnB hnA'

/-- **Lemma 5.12(b)** (sums, products, adjoints): "`Let $A,B\in\AS_X$ have prefactor exponents $m_A$ and $m_B$, and let $\norm{A_N},\norm{B_N}\le CN^{m'}$. Then $A+B$, $A^*$ and $AB$ are in $\AS_X$, with prefactor exponents $\max\{m_A,m_B\}$, $m_A$ and $m_A+m_B+m'$, respectively.`"
— with `m' ≥ 0` (prefactor exponents are nonnegative, Definition 3.11; the proof's bound `N^{m_A+m_B} ≤ N^{m_A+m_B+m'}`
uses it), the new constants after `C`, `C^A`, `C^B` and the exponents. -/
theorem almostSupported_add_star_mul (C : ℝ) (CA CB : ℕ → ℝ) (mA mB m' : ℝ) (hm' : 0 ≤ m') :
    ∃ Cs Ca Cp : ℕ → ℝ, ∀ (η : ℝ → ℝ) (δ₀ : ℝ), IsProfile η → 0 < δ₀ → ∀ (Ts : TorusSeq δ₀)
      (X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))) (A B : (N : ℕ) → FockOp (Ts.T N)),
      ASBound η δ₀ Ts X A mA CA → ASBound η δ₀ Ts X B mB CB →
      (∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (A N)‖ ≤ C * (N : ℝ) ^ m' ∧ ‖toCLM (Ts.T N) (B N)‖ ≤ C * (N : ℝ) ^ m') →
        ASBound η δ₀ Ts X (fun N => A N + B N) (max mA mB) Cs ∧
          ASBound η δ₀ Ts X (fun N => (A N)ᴴ) mA Ca ∧
          ASBound η δ₀ Ts X (fun N => A N * B N) (mA + mB + m') Cp := by
  refine ⟨fun k => |CA k| + |CB k|, CA, fun k => |C| * |CA k| + |C| * |CB k| + |CA k| * |CB k|, ?_⟩
  intro η δ₀ hη hδ₀ Ts X A B hA hB hAB
  exact ⟨asBound_add hη hδ₀ hA hB, asBound_star hη hδ₀ hA, asBound_mul hη hδ₀ hm' hA hB hAB⟩

/-! ### Proof devices for Lemma 5.12(c) (phase (b); not statements of the paper)

The paper's comparison with the ordered exponential of a local generator, without solving a second equation: with
`Π := 𝔼_Y ∘ (even part)` (`projAlg`, a device definition: contractive, the identity on `Alg(Y)`, `Π(X B) = Π(X) B` for
`B ∈ Alg(Y)`, `Y = X^{(r)}`), `Z := ι(V) − Π(ι(V))` solves `Z' = i(Z G'_u + S_u)` with `G'_u ∈ Alg(Y)` a self-adjoint
approximant of `ι(G_u)` chosen at each `u` (no regularity in `u` is needed) and `‖S_u‖ ≤ 2‖ι(G_u) − G'_u‖`
(`‖ι(V)‖ ≤ 1`: `V V* = 1`). For every vector `ψ`, `f = Z*ψ` has `Re⟨f, f'⟩ ≤ 2ε‖ψ‖‖f‖` (the `G'` term is
skew), hence `‖f(u₀)‖ ≤ 2ε‖ψ‖u₀` (`√(‖f‖² + η²)` has derivative at most `2ε‖ψ‖`, then `η → 0`): `‖Z(u₀)‖ ≤ 2u₀ε`, the
paper's constant `2u₀ C^G_k`. -/

section OrdExpDevices

open MeasureTheory Filter Set Real Topology
/-- (device) the energy estimate: if `f(0) = 0` and `Re⟨f, f'⟩ ≤ c‖f‖` on `[0, u₀]`, then `‖f(u₀)‖ ≤ c u₀`. -/
theorem norm_le_of_re_inner_deriv_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {f f' : ℝ → E} {u₀ c : ℝ} (hu₀ : 0 ≤ u₀) (hc : 0 ≤ c) (hf0 : f 0 = 0)
    (hf : ∀ u ∈ Set.Icc 0 u₀, HasDerivWithinAt f (f' u) (Set.Icc 0 u₀) u)
    (hb : ∀ u ∈ Set.Icc 0 u₀, (inner ℂ (f u) (f' u)).re ≤ c * ‖f u‖) :
    ‖f u₀‖ ≤ c * u₀ := by
  have hmain : ∀ η : ℝ, 0 < η → Real.sqrt (‖f u₀‖ ^ 2 + η ^ 2) ≤ η + c * u₀ := by
    intro η hη
    have hpos : ∀ u, 0 < ‖f u‖ ^ 2 + η ^ 2 := fun u => by positivity
    have hφ : ∀ u ∈ Set.Icc 0 u₀, HasDerivWithinAt (fun u => ‖f u‖ ^ 2 + η ^ 2)
        (2 * (inner ℂ (f u) (f' u)).re) (Set.Icc 0 u₀) u := by
      intro u hu
      have h1 := (hf u hu).inner ℂ (hf u hu)
      have h2 : HasDerivWithinAt (fun t => (inner ℂ (f t) (f t)).re)
          ((inner ℂ (f u) (f' u) + inner ℂ (f' u) (f u)).re) (Set.Icc 0 u₀) u :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt u h1
      have e1 : (fun t => (inner ℂ (f t) (f t)).re) = fun t => ‖f t‖ ^ 2 := by
        funext t; rw [inner_self_eq_norm_sq_to_K]; norm_cast
      have e2 : (inner ℂ (f u) (f' u) + inner ℂ (f' u) (f u)).re = 2 * (inner ℂ (f u) (f' u)).re := by
        rw [Complex.add_re, ← inner_conj_symm (f' u) (f u), Complex.conj_re]; ring
      rw [e1, e2] at h2
      exact h2.add_const _
    have hψ : ∀ u ∈ Set.Icc 0 u₀, HasDerivWithinAt (fun u => Real.sqrt (‖f u‖ ^ 2 + η ^ 2))
        (2 * (inner ℂ (f u) (f' u)).re / (2 * Real.sqrt (‖f u‖ ^ 2 + η ^ 2))) (Set.Icc 0 u₀) u :=
      fun u hu => (hφ u hu).sqrt (hpos u).ne'
    have hle : ∀ u ∈ Set.Icc 0 u₀, 2 * (inner ℂ (f u) (f' u)).re / (2 * Real.sqrt (‖f u‖ ^ 2 + η ^ 2)) ≤ c := by
      intro u hu
      have hs : 0 < Real.sqrt (‖f u‖ ^ 2 + η ^ 2) := Real.sqrt_pos.mpr (hpos u)
      have hfs : ‖f u‖ ≤ Real.sqrt (‖f u‖ ^ 2 + η ^ 2) :=
        Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg η])
      rw [div_le_iff₀ (by positivity)]
      have := hb u hu
      nlinarith [norm_nonneg (f u)]
    have hcont : ContinuousOn (fun u => Real.sqrt (‖f u‖ ^ 2 + η ^ 2)) (Set.Icc 0 u₀) :=
      fun u hu => (hψ u hu).continuousWithinAt
    have key := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := u₀) hcont
      (fun u hu => (hψ u (Set.Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hu.1, hu.2⟩))
      (B := fun u => η + c * u) (B' := fun _ => c)
      (by simp [hf0, Real.sqrt_sq hη.le])
      (by fun_prop)
      (fun u _ => by simpa using ((hasDerivAt_id u).const_mul c).const_add η |>.hasDerivWithinAt)
      (fun u hu => hle u (Set.Ico_subset_Icc_self hu))
    exact key ⟨hu₀, le_rfl⟩
  by_contra hcon
  push_neg at hcon
  set δ := ‖f u₀‖ - c * u₀ with hδ
  have hδ0 : 0 < δ := by linarith
  have h1 := hmain (δ / 2) (by linarith)
  have h2 : ‖f u₀‖ ≤ Real.sqrt (‖f u₀‖ ^ 2 + (δ / 2) ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (δ / 2)])
  linarith

/-- (device) the adjoint on `E →L[ℂ] E` as a real continuous linear map. -/
noncomputable def starRCLM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E) where
  toFun := star
  map_add' := star_add
  map_smul' := fun r X => by
    rw [RingHom.id_apply, ← Complex.coe_smul, star_smul, Complex.star_def, Complex.conj_ofReal, Complex.coe_smul]
  cont := continuous_star

theorem starRCLM_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (X : E →L[ℂ] E) : starRCLM E X = star X := rfl

theorem norm_star_clm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (X : E →L[ℂ] E) : ‖star X‖ = ‖X‖ := by
  rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]

/-- (device) the abstract form of Lemma 5.12(c): with a contractive `ℂ`-linear `P` (`P 1 = 1`) and, at every `u`, a
self-adjoint `g'(u)` within `ε` of `ĝ(u)` with `P(X g'(u)) = P(X) g'(u)`, a solution `w' = i w ĝ`, `w(0) = 1`,
`‖w‖ ≤ 1`, satisfies `‖w(u₀) − P(w(u₀))‖ ≤ 2ε u₀`. -/
theorem norm_sub_proj_le_of_ode {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {u₀ ε : ℝ} (hu₀ : 0 ≤ u₀) (hε : 0 ≤ ε) (P : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E))
    (hP : ∀ X, ‖P X‖ ≤ ‖X‖) (hP1 : P 1 = 1)
    {w ĝ g' : ℝ → E →L[ℂ] E} (hw0 : w 0 = 1) (hw1 : ∀ u ∈ Set.Icc 0 u₀, ‖w u‖ ≤ 1)
    (hw : ∀ u ∈ Set.Icc 0 u₀, HasDerivWithinAt w ((I : ℂ) • (w u * ĝ u)) (Set.Icc 0 u₀) u)
    (hg'sa : ∀ u ∈ Set.Icc 0 u₀, IsSelfAdjoint (g' u))
    (hPg : ∀ u ∈ Set.Icc 0 u₀, ∀ X, P (X * g' u) = P X * g' u)
    (hgε : ∀ u ∈ Set.Icc 0 u₀, ‖ĝ u - g' u‖ ≤ ε) :
    ‖w u₀ - P (w u₀)‖ ≤ 2 * ε * u₀ := by
  set z : ℝ → E →L[ℂ] E := fun u => w u - P (w u) with hz
  have hz' : ∀ u ∈ Set.Icc 0 u₀, HasDerivWithinAt z
      ((I : ℂ) • (z u * g' u + (w u * (ĝ u - g' u) - P (w u * (ĝ u - g' u))))) (Set.Icc 0 u₀) u := by
    intro u hu
    have h1 := ((P.restrictScalars ℝ).hasFDerivAt).comp_hasDerivWithinAt u (hw u hu)
    have h2 := (hw u hu).sub h1
    refine h2.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]
    have e : w u * ĝ u = w u * g' u + w u * (ĝ u - g' u) := by rw [mul_sub]; abel
    rw [e, map_add, hPg u hu, hz]
    simp only
    rw [sub_mul]
    module
  have hzs : ∀ u ∈ Set.Icc 0 u₀, ‖w u * (ĝ u - g' u) - P (w u * (ĝ u - g' u))‖ ≤ 2 * ε := by
    intro u hu
    have h1 : ‖w u * (ĝ u - g' u)‖ ≤ ε :=
      (norm_mul_le _ _).trans ((mul_le_mul (hw1 u hu) (hgε u hu) (norm_nonneg _) zero_le_one).trans (by rw [one_mul]))
    calc ‖w u * (ĝ u - g' u) - P (w u * (ĝ u - g' u))‖ ≤ ‖w u * (ĝ u - g' u)‖ + ‖P (w u * (ĝ u - g' u))‖ :=
          norm_sub_le _ _
      _ ≤ ε + ε := add_le_add h1 ((hP _).trans h1)
      _ = 2 * ε := by ring
  have hz0 : z 0 = 0 := by simp only [hz, hw0, hP1, sub_self]
  have hmain : ∀ ψ : E, ‖star (z u₀) ψ‖ ≤ 2 * ε * u₀ * ‖ψ‖ := by
    intro ψ
    set f : ℝ → E := fun u => star (z u) ψ with hf
    set S : ℝ → E →L[ℂ] E := fun u => w u * (ĝ u - g' u) - P (w u * (ĝ u - g' u)) with hS
    have hf' : ∀ u ∈ Set.Icc 0 u₀, HasDerivWithinAt f
        (star ((I : ℂ) • (z u * g' u + S u)) ψ) (Set.Icc 0 u₀) u := by
      intro u hu
      have h1 := (starRCLM E).hasFDerivAt.comp_hasDerivWithinAt u (hz' u hu)
      exact ((ContinuousLinearMap.apply ℂ E ψ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt u h1
    have hb : ∀ u ∈ Set.Icc 0 u₀, (inner ℂ (f u) (star ((I : ℂ) • (z u * g' u + S u)) ψ)).re ≤
        (2 * ε * ‖ψ‖) * ‖f u‖ := by
      intro u hu
      have hgs : star (g' u) = g' u := hg'sa u hu
      have e1 : star ((I : ℂ) • (z u * g' u + S u)) ψ = (-I : ℂ) • (g' u (f u) + star (S u) ψ) := by
        rw [star_smul, star_add, star_mul, hgs]
        simp only [hf, Complex.star_def, Complex.conj_I, smul_apply,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply]
      rw [e1, inner_smul_right, inner_add_right, mul_add, Complex.add_re]
      have h0 : (-I * inner ℂ (f u) (g' u (f u))).re = 0 := by
        have hsym : (g' u : E →ₗ[ℂ] E).IsSymmetric :=
          ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hg'sa u hu)
        have him : (inner ℂ (f u) (g' u (f u))).im = 0 := hsym.im_inner_self_apply (f u)
        rw [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im, him]
        ring
      rw [h0, zero_add]
      calc (-I * inner ℂ (f u) (star (S u) ψ)).re ≤ ‖-I * inner ℂ (f u) (star (S u) ψ)‖ := Complex.re_le_norm _
        _ = ‖inner ℂ (f u) (star (S u) ψ)‖ := by rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
        _ ≤ ‖f u‖ * ‖star (S u) ψ‖ := norm_inner_le_norm _ _
        _ ≤ ‖f u‖ * (‖star (S u)‖ * ‖ψ‖) := mul_le_mul_of_nonneg_left ((star (S u)).le_opNorm ψ) (norm_nonneg _)
        _ ≤ ‖f u‖ * (2 * ε * ‖ψ‖) := by
            rw [norm_star_clm]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hzs u hu) (norm_nonneg _)) (norm_nonneg _)
        _ = 2 * ε * ‖ψ‖ * ‖f u‖ := by ring
    have hf0 : f 0 = 0 := by simp only [hf, hz0, star_zero, ContinuousLinearMap.zero_apply]
    have := norm_le_of_re_inner_deriv_le hu₀ (by positivity) hf0 hf' hb
    calc ‖star (z u₀) ψ‖ = ‖f u₀‖ := rfl
      _ ≤ 2 * ε * ‖ψ‖ * u₀ := this
      _ = 2 * ε * u₀ * ‖ψ‖ := by ring
  have h := ContinuousLinearMap.opNorm_le_bound _ (by positivity) hmain
  rw [norm_star_clm] at h
  exact h

section ProjAlg

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op c chat parityOp IsEven CAR Alg condExp)

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- (device) the even part `½(A + θAθ)`. -/
noncomputable def evenPart (A : Op S) : Op S := (1 / 2 : ℂ) • (A + (parityOp : Op S) * A * parityOp)

/-- (device) the projection onto `Alg Y`: the conditional expectation of the even part. -/
noncomputable def projAlg (Y : Finset S) (A : Op S) : Op S := condExp Y (evenPart A)

theorem evenPart_isEven (A : Op S) : IsEven (evenPart A) := by
  show evenPart A * parityOp = parityOp * evenPart A
  simp only [evenPart, smul_mul_assoc, mul_smul_comm, add_mul, mul_add]
  congr 1
  rw [mul_assoc, mul_assoc, Fermion.Pilot.JW.parityOp_mul_parityOp, mul_one, ← mul_assoc, ← mul_assoc,
    Fermion.Pilot.JW.parityOp_mul_parityOp, one_mul]
  abel

theorem evenPart_of_isEven {A : Op S} (hA : IsEven A) : evenPart A = A := by
  have h : (parityOp : Op S) * A * parityOp = A := by
    rw [mul_assoc, hA.eq, ← mul_assoc, Fermion.Pilot.JW.parityOp_mul_parityOp, one_mul]
  rw [evenPart, h, ← two_smul ℂ A, smul_smul]
  norm_num

theorem evenPart_mul_of_isEven (X : Op S) {B : Op S} (hB : IsEven B) : evenPart (X * B) = evenPart X * B := by
  have h : (parityOp : Op S) * (X * B) * parityOp = parityOp * X * parityOp * B := by
    calc (parityOp : Op S) * (X * B) * parityOp = parityOp * X * (B * parityOp) := by simp only [mul_assoc]
      _ = parityOp * X * (parityOp * B) := by rw [hB.eq]
      _ = parityOp * X * parityOp * B := by simp only [mul_assoc]
  rw [evenPart, evenPart, h, smul_mul_assoc, add_mul]

open scoped Matrix.Norms.L2Operator in
theorem norm_parity_conj (A : Op S) : ‖opCLM ((parityOp : Op S) * A * (parityOp : Op S))‖ = ‖opCLM A‖ := by
  have hU : (parityOp : Op S) ∈ unitary (Op S) := parityOp_mem_unitary
  rw [norm_opCLM_eq_l2, norm_opCLM_eq_l2, CStarRing.norm_mul_mem_unitary _ hU, CStarRing.norm_mem_unitary_mul _ hU]

theorem norm_evenPart_le (A : Op S) : ‖opCLM (evenPart A)‖ ≤ ‖opCLM A‖ := by
  rw [evenPart, opCLM_smul', norm_smul, opCLM_add']
  have h := norm_add_le (opCLM A) (opCLM ((parityOp : Op S) * A * (parityOp : Op S)))
  rw [norm_parity_conj] at h
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [this]
  linarith

theorem norm_condExp_le_c (Y : Finset S) (A : Op S) : ‖opCLM (condExp Y A)‖ ≤ ‖opCLM A‖ := by
  open scoped Matrix.Norms.L2Operator in
  (rw [norm_opCLM_eq_l2, norm_opCLM_eq_l2]; exact Fermion.Pilot.JW.norm_condExp_le Y A)

theorem projAlg_mem (Y : Finset S) (A : Op S) : projAlg Y A ∈ Alg Y :=
  Fermion.Pilot.JW.condExp_mem_Alg Y (evenPart_isEven A)

theorem projAlg_of_mem {Y : Finset S} {A : Op S} (hA : A ∈ Alg Y) : projAlg Y A = A := by
  rw [projAlg, evenPart_of_isEven hA.2, Fermion.Pilot.JW.condExp_of_mem hA.1]

theorem projAlg_mul (Y : Finset S) (X : Op S) {B : Op S} (hB : B ∈ Alg Y) :
    projAlg Y (X * B) = projAlg Y X * B := by
  rw [projAlg, projAlg, evenPart_mul_of_isEven X hB.2]
  have := Fermion.Pilot.JW.condExp_mul_mul (Y := Y) (B := 1) (C := B) (CAR Y).one_mem hB.1 (evenPart X)
  rwa [one_mul, one_mul] at this

theorem norm_projAlg_le (Y : Finset S) (A : Op S) : ‖opCLM (projAlg Y A)‖ ≤ ‖opCLM A‖ :=
  (norm_condExp_le_c Y _).trans (norm_evenPart_le A)

theorem projAlg_one (Y : Finset S) : projAlg Y 1 = 1 :=
  projAlg_of_mem ⟨(CAR Y).one_mem, Commute.one_left _⟩

theorem projAlg_add (Y : Finset S) (A B : Op S) : projAlg Y (A + B) = projAlg Y A + projAlg Y B := by
  have hl := Fermion.Pilot.JW.condExp_isLinearMap Y
  simp only [projAlg, evenPart, mul_add, add_mul]
  rw [← hl.map_add]
  congr 1
  module

theorem projAlg_smul (Y : Finset S) (a : ℂ) (A : Op S) : projAlg Y (a • A) = a • projAlg Y A := by
  have hl := Fermion.Pilot.JW.condExp_isLinearMap Y
  simp only [projAlg, evenPart]
  rw [← hl.map_smul]
  congr 1
  rw [mul_smul_comm, smul_mul_assoc, smul_comm, ← smul_add]

/-- (device) the projection at the level of continuous linear maps. -/
noncomputable def projCLM (Y : Finset S) :
    (EuclideanSpace ℂ (Conf S) →L[ℂ] EuclideanSpace ℂ (Conf S)) →L[ℂ]
      (EuclideanSpace ℂ (Conf S) →L[ℂ] EuclideanSpace ℂ (Conf S)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => opCLM (projAlg Y ((Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)).symm X))
      map_add' := fun X X' => by simp only [map_add, projAlg_add]
      map_smul' := fun a X => by simp only [map_smul, projAlg_smul, RingHom.id_apply] }

theorem projCLM_opCLM (Y : Finset S) (A : Op S) : projCLM Y (opCLM A) = opCLM (projAlg Y A) := by
  simp [projCLM]

end ProjAlg

section OrdExp

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op c chat parityOp IsEven CAR Alg condExp)

/-- (device) `toCLM T A ↦ opCLM (ι A)` as a continuous linear map. -/
noncomputable def iotaCLM {η : ℝ → ℝ} {δ₀ : ℝ} {T : Torus} (hη : IsProfile η) (hδ₀ : 0 < δ₀)
    (hT : T.Admissible δ₀) :
    (FockSpace T →L[ℂ] FockSpace T) →L[ℂ]
      (EuclideanSpace ℂ (Conf (Slot δ₀ T)) →L[ℂ] EuclideanSpace ℂ (Conf (Slot δ₀ T))) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => opCLM (iota η δ₀ T ((Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)).symm X))
      map_add' := fun X X' => by simp only [map_add, iota_add hη hδ₀ hT]
      map_smul' := fun a X => by simp only [map_smul, iota_smul hη hδ₀ hT, RingHom.id_apply] }

theorem iotaCLM_toCLM {η : ℝ → ℝ} {δ₀ : ℝ} {T : Torus} (hη : IsProfile η) (hδ₀ : 0 < δ₀)
    (hT : T.Admissible δ₀) (A : FockOp T) : iotaCLM hη hδ₀ hT (toCLM T A) = opCLM (iota η δ₀ T A) := by
  simp [iotaCLM]

/-- (device) a solution of `v' = i v g` with self-adjoint `g` and `v(0) = 1` has `‖v‖ ≤ 1` (`v v* = 1`). -/
theorem norm_le_one_of_ode {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {u₀ : ℝ} {v g : ℝ → E →L[ℂ] E} (hv0 : v 0 = 1) (hgsa : ∀ u ∈ Set.Icc 0 u₀, IsSelfAdjoint (g u))
    (hv : ∀ u ∈ Set.Icc 0 u₀, HasDerivWithinAt v ((I : ℂ) • (v u * g u)) (Set.Icc 0 u₀) u) :
    ∀ u ∈ Set.Icc 0 u₀, ‖v u‖ ≤ 1 := by
  have hQ : ∀ u ∈ Set.Icc 0 u₀, HasDerivWithinAt (fun u => v u * star (v u)) 0 (Set.Icc 0 u₀) u := by
    intro u hu
    have h1 := hv u hu
    have h2 := (starRCLM E).hasFDerivAt.comp_hasDerivWithinAt u h1
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    have hg : star (g u) = g u := (hgsa u hu).star_eq
    simp only [Function.comp_apply, starRCLM_apply, star_smul, star_mul, hg, Complex.star_def, Complex.conj_I]
    rw [smul_mul_assoc, mul_smul_comm, neg_smul, ← sub_eq_add_neg, mul_assoc]
    exact sub_self _
  have hcont : ContinuousOn (fun u => v u * star (v u)) (Set.Icc 0 u₀) :=
    fun u hu => (hQ u hu).continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont fun x hx =>
    (hQ x (Set.Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ⟨hx.1, hx.2⟩)
  intro u hu
  have h := hconst u hu
  simp only [hv0, star_one, mul_one] at h
  have h2 : ‖v u‖ * ‖v u‖ ≤ 1 := by
    rw [← CStarRing.norm_self_mul_star, h]
    exact ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg (v u)]

end OrdExp

end OrdExpDevices

/-- **Lemma 5.12(c)** (ordered exponentials): "`Let $G_N(u)$, $u\in[0,u_0]$, be self-adjoint and continuous in $u$, and let $G=(G_N(u))_N$ be in $\AS_X$ uniformly in $u$. Then the solution of $V_N'(u)=\iu V_N(u)G_N(u)$, $V_N(0)=\one$, satisfies $V_N(u_0)\in\AS_X$, with the same prefactor exponent and constants multiplied by $2u_0$.`"
— for a given solution `V_N` (the module docstring); "uniformly in `u`" is one `m` and one `C^G` for all `u ∈ [0, u₀]`. -/
theorem ordExp_almostSupported {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {Ts : TorusSeq δ₀}
    {X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))} {u₀ : ℝ} (hu₀ : 0 ≤ u₀) {m : ℝ} {CG : ℕ → ℝ}
    (G : ℝ → (N : ℕ) → FockOp (Ts.T N)) (hGsa : ∀ N ∈ Ts.idx, ∀ u ∈ Set.Icc 0 u₀, IsSelfAdjoint (G u N))
    (hGc : ∀ N ∈ Ts.idx, ContinuousOn (fun u => G u N) (Set.Icc 0 u₀))
    (hG : ∀ u ∈ Set.Icc 0 u₀, ASBound η δ₀ Ts X (G u) m CG)
    (V : (N : ℕ) → ℝ → FockOp (Ts.T N)) (hV0 : ∀ N ∈ Ts.idx, V N 0 = 1)
    (hV : ∀ N ∈ Ts.idx, ∀ u ∈ Set.Icc 0 u₀,
      HasDerivWithinAt (fun v => toCLM (Ts.T N) (V N v)) (toCLM (Ts.T N) ((I : ℂ) • (V N u * G u N)))
        (Set.Icc 0 u₀) u) :
    ASBound η δ₀ Ts X (fun N => V N u₀) m fun k => 2 * u₀ * CG k := by
  have hm0 : 0 ≤ m := (hG 0 ⟨le_rfl, hu₀⟩).1
  refine ⟨hm0, fun k N hN r hr => ?_⟩
  have hT := Ts.admissible N hN
  set Y := fat (X N) r with hY
  set ε := CG k * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ)) with hε
  have happ : ∀ u ∈ Set.Icc 0 u₀, ∃ A' ∈ Alg Y, ‖opCLM (iota η δ₀ (Ts.T N) (G u N) - A')‖ ≤ ε :=
    fun u hu => (hG u hu).2 k N hN r hr
  have hε0 : 0 ≤ ε := by
    obtain ⟨A', _, hA'⟩ := happ 0 ⟨le_rfl, hu₀⟩
    exact (norm_nonneg _).trans hA'
  choose! A' hA'mem hA'le using happ
  have hθ : star (parityOp : Op (Slot δ₀ (Ts.T N))) = parityOp := by
    rw [Matrix.star_eq_conjTranspose, parityOp_conjTranspose]
  set Gs : ℝ → Op (Slot δ₀ (Ts.T N)) := fun u => (1 / 2 : ℂ) • (A' u + star (A' u)) with hGs
  have hGsmem : ∀ u ∈ Set.Icc 0 u₀, Gs u ∈ Alg Y := by
    intro u hu
    obtain ⟨h1, h2⟩ := hA'mem u hu
    have hs : IsEven (star (A' u)) := by
      have := h2.star_star
      rwa [hθ] at this
    have h1s : star (A' u) ∈ CAR Y := star_mem h1
    exact ⟨(CAR Y).smul_mem (add_mem h1 h1s) _, (h2.add_left hs).smul_left _⟩
  have hGssa : ∀ u, IsSelfAdjoint (Gs u) := by
    intro u
    show star (Gs u) = Gs u
    simp only [hGs, star_smul, star_add, star_star]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, add_comm]
  have hιsa : ∀ u ∈ Set.Icc 0 u₀, star (iota η δ₀ (Ts.T N) (G u N)) = iota η δ₀ (Ts.T N) (G u N) := by
    intro u hu
    rw [Matrix.star_eq_conjTranspose, ← iota_conjTranspose hη hδ₀ hT, ← Matrix.star_eq_conjTranspose,
      (hGsa N hN u hu).star_eq]
  have hGsle : ∀ u ∈ Set.Icc 0 u₀, ‖opCLM (iota η δ₀ (Ts.T N) (G u N) - Gs u)‖ ≤ ε := by
    intro u hu
    have e : iota η δ₀ (Ts.T N) (G u N) - Gs u = (1 / 2 : ℂ) • ((iota η δ₀ (Ts.T N) (G u N) - A' u) +
        star (iota η δ₀ (Ts.T N) (G u N) - A' u)) := by
      rw [star_sub, hιsa u hu, hGs]
      simp only
      module
    rw [e, opCLM_smul', norm_smul, opCLM_add']
    have h1 := hA'le u hu
    have h2 : ‖opCLM (star (iota η δ₀ (Ts.T N) (G u N) - A' u))‖ ≤ ε := by
      rw [opCLM_star', norm_star_clm]; exact h1
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    have h3 := norm_add_le (opCLM (iota η δ₀ (Ts.T N) (G u N) - A' u))
      (opCLM (star (iota η δ₀ (Ts.T N) (G u N) - A' u)))
    linarith
  -- the hypotheses of the abstract lemma
  have hP : ∀ Z, ‖projCLM Y Z‖ ≤ ‖Z‖ := by
    intro Z
    have hZ : Z = opCLM ((Matrix.toEuclideanCLM (n := Conf (Slot δ₀ (Ts.T N))) (𝕜 := ℂ)).symm Z) := by simp
    rw [hZ, projCLM_opCLM]
    exact norm_projAlg_le Y _
  have hP1 : projCLM Y 1 = 1 := by
    have : (1 : EuclideanSpace ℂ (Conf (Slot δ₀ (Ts.T N))) →L[ℂ] _) = opCLM 1 :=
      (map_one (Matrix.toEuclideanCLM (n := Conf (Slot δ₀ (Ts.T N))) (𝕜 := ℂ))).symm
    rw [this, projCLM_opCLM, projAlg_one]
  have hPg : ∀ u ∈ Set.Icc 0 u₀, ∀ Z, projCLM Y (Z * opCLM (Gs u)) = projCLM Y Z * opCLM (Gs u) := by
    intro u hu Z
    have hZ : Z = opCLM ((Matrix.toEuclideanCLM (n := Conf (Slot δ₀ (Ts.T N))) (𝕜 := ℂ)).symm Z) := by simp
    rw [hZ, ← opCLM_mul', projCLM_opCLM, projCLM_opCLM, projAlg_mul Y _ (hGsmem u hu), opCLM_mul']
  have hw0 : opCLM (iota η δ₀ (Ts.T N) (V N 0)) = 1 := by
    rw [hV0 N hN, iota_one hη hδ₀ hT]
    exact map_one (Matrix.toEuclideanCLM (n := Conf (Slot δ₀ (Ts.T N))) (𝕜 := ℂ))
  have hw1 : ∀ u ∈ Set.Icc 0 u₀, ‖opCLM (iota η δ₀ (Ts.T N) (V N u))‖ ≤ 1 := by
    intro u hu
    rw [norm_iota hη hδ₀ hT]
    refine norm_le_one_of_ode (v := fun v => toCLM (Ts.T N) (V N v)) (g := fun v => toCLM (Ts.T N) (G v N))
      (by simp only [hV0 N hN]; exact map_one (Matrix.toEuclideanCLM (n := Conf (ZMod (Ts.T N).Nφ)) (𝕜 := ℂ)))
      (fun u hu => (hGsa N hN u hu).map _) (fun u hu => ?_) u hu
    refine (hV N hN u hu).congr_deriv ?_
    simp only [map_smul, map_mul]
  have hw : ∀ u ∈ Set.Icc 0 u₀, HasDerivWithinAt (fun v => opCLM (iota η δ₀ (Ts.T N) (V N v)))
      ((I : ℂ) • (opCLM (iota η δ₀ (Ts.T N) (V N u)) * opCLM (iota η δ₀ (Ts.T N) (G u N)))) (Set.Icc 0 u₀) u := by
    intro u hu
    have h := ((iotaCLM hη hδ₀ hT).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt u (hV N hN u hu)
    have e : ((iotaCLM hη hδ₀ hT).restrictScalars ℝ) ∘ (fun v => toCLM (Ts.T N) (V N v)) =
        fun v => opCLM (iota η δ₀ (Ts.T N) (V N v)) := by
      funext v; simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', iotaCLM_toCLM]
    rw [e] at h
    refine h.congr_deriv ?_
    rw [ContinuousLinearMap.coe_restrictScalars', iotaCLM_toCLM, iota_smul hη hδ₀ hT, iota_mul hη hδ₀ hT,
      opCLM_smul', opCLM_mul']
  have hg'sa : ∀ u ∈ Set.Icc 0 u₀, IsSelfAdjoint (opCLM (Gs u)) := fun u _ => (hGssa u).map _
  have hgε : ∀ u ∈ Set.Icc 0 u₀, ‖opCLM (iota η δ₀ (Ts.T N) (G u N)) - opCLM (Gs u)‖ ≤ ε := by
    intro u hu
    rw [← opCLM_sub']
    exact hGsle u hu
  have key := norm_sub_proj_le_of_ode hu₀ hε0 (projCLM Y) hP hP1 hw0 hw1 hw hg'sa hPg hgε
  refine ⟨projAlg Y (iota η δ₀ (Ts.T N) (V N u₀)), projAlg_mem Y _, ?_⟩
  rw [projCLM_opCLM, ← opCLM_sub'] at key
  calc ‖opCLM (iota η δ₀ (Ts.T N) (V N u₀) - projAlg Y (iota η δ₀ (Ts.T N) (V N u₀)))‖ ≤ 2 * ε * u₀ := key
    _ = 2 * u₀ * CG k * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ)) := by rw [hε]; ring

/-! ### Proof device for Lemma 5.12(d) (phase (b); not a statement of the paper)

Lemma 5.12(c) with `G_u := e^{iuQ} A e^{-iuQ}` (Lemma 4.11(iii) gives its `𝒜𝒮` bound uniformly in `u` and the bands) and
`V(u) := e^{iu(Q+A)} e^{-iuQ}` (`V' = i V G_u`); the constants `2φ C'_k ≤ 4π |C'_k|` for `φ ∈ [0, 2π]`. -/

theorem asBound_mono_const {η : ℝ → ℝ} {δ₀ : ℝ} {Ts : TorusSeq δ₀} {X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))}
    {A : (N : ℕ) → FockOp (Ts.T N)} {m : ℝ} {C C₂ : ℕ → ℝ} (h : ASBound η δ₀ Ts X A m C)
    (hC : ∀ k, C k ≤ C₂ k) : ASBound η δ₀ Ts X A m C₂ := by
  refine ⟨h.1, fun k N hN r hr => ?_⟩
  obtain ⟨A', hA', hb⟩ := h.2 k N hN r hr
  refine ⟨A', hA', hb.trans ?_⟩
  have hN1 := one_le_of_mem_idx Ts hN
  have : 0 ≤ (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ)) := by positivity
  calc C k * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ)) = C k * ((N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ))) := by ring
    _ ≤ C₂ k * ((N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ))) := mul_le_mul_of_nonneg_right (hC k) this
    _ = C₂ k * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ)) := by ring

/-- **Lemma 5.12(d)** (conjugation by band charges): "`Let $Z_N=\Str(I_N)$ with $I_N$ open intervals of length at least $2\delta_x$, let $A=(A_N)\in\AS_Z$ be self-adjoint with prefactor exponent $m$ and $\norm{A_N}\le CN^m$, and let $\mathcal B_N$ be bands. Then $e^{\iu\varphi(Q_{\mathcal B_N}+A_N)}e^{-\iu\varphi Q_{\mathcal B_N}}\in\AS_Z$ with prefactor exponent $m$, uniformly in $\varphi\in[0,2\pi]$ and in the bands.`"
— in block C's form of Lemma 4.11(iii) (`I_N` the image of `(a_N, b_N)`, `b_N − a_N ≥ 2δ_x`); the new constants after
`δ₀`, `C` and the constants of `A`, before everything else, hence uniform in `φ` and the bands. -/
theorem exp_Qband_add_almostSupported {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (C : ℝ) (CA : ℕ → ℝ) :
    ∃ C' : ℕ → ℝ, ∀ (η : ℝ → ℝ), IsProfile η → ∀ (Ts : TorusSeq δ₀) (a b : ℕ → ℝ),
      (∀ N ∈ Ts.idx, 2 * δx δ₀ (Ts.T N) ≤ b N - a N) →
      ∀ (A : (N : ℕ) → FockOp (Ts.T N)) (m : ℝ),
        ASBound η δ₀ Ts (fun N => strip δ₀ (Ts.T N) (circImage (Ts.T N).Lx (Set.Ioo (a N) (b N)))) A m CA →
        (∀ N ∈ Ts.idx, IsSelfAdjoint (A N)) →
        (∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (A N)‖ ≤ C * (N : ℝ) ^ m) →
        ∀ (B : (N : ℕ) → Finset (ZMod (Ts.T N).Nφ)) (φ : ℝ), φ ∈ Set.Icc 0 (2 * π) →
          ASBound η δ₀ Ts (fun N => strip δ₀ (Ts.T N) (circImage (Ts.T N).Lx (Set.Ioo (a N) (b N))))
            (fun N => NormedSpace.exp ((I * (φ : ℂ)) • (Qband (Ts.T N) (B N) + A N)) *
              NormedSpace.exp ((-(I * (φ : ℂ))) • Qband (Ts.T N) (B N))) m C' := by
  obtain ⟨C', hC'⟩ := exists_almostSupported_exp_Qband_conj hδ₀ C CA
  refine ⟨fun k => 4 * π * |C' k|, ?_⟩
  intro η hη Ts a b hab A m hAS hAsa hAn B φ hφ
  set G : ℝ → (N : ℕ) → FockOp (Ts.T N) := fun u N =>
    NormedSpace.exp ((I * (u : ℂ)) • Qband (Ts.T N) (B N)) * A N *
      NormedSpace.exp ((-(I * (u : ℂ))) • Qband (Ts.T N) (B N)) with hGdef
  set V : (N : ℕ) → ℝ → FockOp (Ts.T N) := fun N u =>
    NormedSpace.exp ((I * (u : ℂ)) • (Qband (Ts.T N) (B N) + A N)) *
      NormedSpace.exp ((-(I * (u : ℂ))) • Qband (Ts.T N) (B N)) with hVdef
  have hGsa : ∀ N ∈ Ts.idx, ∀ u ∈ Set.Icc 0 φ, IsSelfAdjoint (G u N) := by
    intro N hN u _
    have hQ := Qband_isSelfAdjoint (Ts.T N) (B N)
    show (G u N)ᴴ = G u N
    simp only [hGdef, Matrix.conjTranspose_mul, exp_smul_conjTranspose hQ]
    have h2 : (NormedSpace.exp ((-(I * (u : ℂ))) • Qband (Ts.T N) (B N)))ᴴ =
        NormedSpace.exp ((I * (u : ℂ)) • Qband (Ts.T N) (B N)) := by
      have := exp_smul_conjTranspose hQ (-u)
      simp only [Complex.ofReal_neg, mul_neg, neg_neg] at this
      exact this
    rw [h2, show (A N)ᴴ = A N from hAsa N hN, Matrix.mul_assoc]
  have hGc : ∀ N ∈ Ts.idx, ContinuousOn (fun u => G u N) (Set.Icc 0 φ) := by
    intro N _
    refine Continuous.continuousOn ?_
    set e := (Matrix.toEuclideanCLM (n := Conf (ZMod (Ts.T N).Nφ)) (𝕜 := ℂ))
    have hsymm : Continuous e.symm :=
      LinearMap.continuous_of_finiteDimensional e.symm.toAlgEquiv.toLinearEquiv.toLinearMap
    have hfun : (fun u => G u N) = fun u : ℝ => e.symm (NormedSpace.exp (u • opCLM ((I : ℂ) • Qband (Ts.T N) (B N))) *
        opCLM (A N) * NormedSpace.exp (u • (-opCLM ((I : ℂ) • Qband (Ts.T N) (B N))))) := by
      funext u
      rw [← opCLM_expI, ← opCLM_expI_neg, ← opCLM_mul', ← opCLM_mul']
      exact (e.symm_apply_apply _).symm
    rw [hfun]
    refine hsymm.comp ?_
    have hexp : ∀ Y : EuclideanSpace ℂ (Conf (ZMod (Ts.T N).Nφ)) →L[ℂ] EuclideanSpace ℂ (Conf (ZMod (Ts.T N).Nφ)),
        Continuous fun u : ℝ => NormedSpace.exp (u • Y) :=
      fun Y => continuous_iff_continuousAt.mpr fun u => (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y u).continuousAt
    exact ((hexp _).mul continuous_const).mul (hexp _)
  have hG : ∀ u ∈ Set.Icc 0 φ, ASBound η δ₀ Ts
      (fun N => strip δ₀ (Ts.T N) (circImage (Ts.T N).Lx (Set.Ioo (a N) (b N)))) (G u) m C' :=
    fun u _ => hC' η hη Ts a b hab A m hAS hAn B u
  have hV0 : ∀ N ∈ Ts.idx, V N 0 = 1 := by
    intro N _
    simp only [hVdef, Complex.ofReal_zero, mul_zero, neg_zero, zero_smul, NormedSpace.exp_zero, mul_one]
  have hV : ∀ N ∈ Ts.idx, ∀ u ∈ Set.Icc 0 φ,
      HasDerivWithinAt (fun v => toCLM (Ts.T N) (V N v)) (toCLM (Ts.T N) ((I : ℂ) • (V N u * G u N)))
        (Set.Icc 0 φ) u := by
    intro N _ u _
    set Q := Qband (Ts.T N) (B N) with hQdef
    set X₁ := opCLM ((I : ℂ) • (Q + A N)) with hX₁
    set X₂ := opCLM ((I : ℂ) • Q) with hX₂
    have e : (fun v => toCLM (Ts.T N) (V N v)) =
        fun v : ℝ => NormedSpace.exp (v • X₁) * NormedSpace.exp (v • (-X₂)) := by
      funext v
      simp only [hVdef, opCLM_mul', opCLM_expI, opCLM_expI_neg]
      rfl
    rw [e]
    have hd := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X₁ u).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-X₂) u)
    refine hd.hasDerivWithinAt.congr_deriv ?_
    -- the matrix identity `i V G = e₁ (iA) e₂`
    have hM : (I : ℂ) • (V N u * G u N) = NormedSpace.exp ((I * (u : ℂ)) • (Q + A N)) * ((I : ℂ) • A N) *
        NormedSpace.exp ((-(I * (u : ℂ))) • Q) := by
      have hinv := expI_neg_mul_expI Q u
      simp only [hVdef, hGdef]
      rw [show NormedSpace.exp ((I * (u : ℂ)) • (Q + A N)) * NormedSpace.exp ((-(I * (u : ℂ))) • Q) *
          (NormedSpace.exp ((I * (u : ℂ)) • Q) * A N * NormedSpace.exp ((-(I * (u : ℂ))) • Q)) =
          NormedSpace.exp ((I * (u : ℂ)) • (Q + A N)) *
            (NormedSpace.exp ((-(I * (u : ℂ))) • Q) * NormedSpace.exp ((I * (u : ℂ)) • Q)) * A N *
              NormedSpace.exp ((-(I * (u : ℂ))) • Q) by simp only [Matrix.mul_assoc], hinv, Matrix.mul_one,
        Matrix.mul_smul, Matrix.smul_mul]
    have hX : X₁ - X₂ = opCLM ((I : ℂ) • A N) := by
      rw [hX₁, hX₂, ← opCLM_sub', smul_add, add_sub_cancel_left]
    rw [hM, toCLM_eq_opCLM, opCLM_mul', opCLM_mul', opCLM_expI, opCLM_expI_neg, ← hX]
    noncomm_ring
  have h := ordExp_almostSupported hη hδ₀ hφ.1 G hGsa hGc hG V hV0 hV
  refine asBound_mono_const h fun k => ?_
  have hφ2 : φ ≤ 2 * π := hφ.2
  calc 2 * φ * C' k ≤ 2 * φ * |C' k| := mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith [hφ.1])
    _ ≤ 2 * (2 * π) * |C' k| := by
        have := abs_nonneg (C' k)
        nlinarith [hφ.1]
    _ = 4 * π * |C' k| := by ring

/-! ## `O(N^{−∞})` and Lemma 5.13 -/

/-- "`$\Onf$, $\eqN$ & bounded by $C_kN^{-k}$ for every $k$; equality up to $\Onf$`" (the paper's notation table): a family
of sequences of operators on `𝔉`, indexed by a parameter, is `O(N^{−∞})` uniformly in the parameter if for every
`k ∈ ℕ` one constant `C_k` bounds `N^k ‖a_{p,N}‖` for all `p` and `N ∈ 𝒩`. -/
def IsONegInf {δ₀ : ℝ} (Ts : TorusSeq δ₀) {P : Type*} (a : P → (N : ℕ) → FockOp (Ts.T N)) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ p : P, ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (a p N)‖ ≤ C * (N : ℝ) ^ (-(k : ℝ))

/-! ### Proof devices for Lemma 5.13 (phase (b); not statements of the paper)

The first conclusion: for `N` with `c√N/2 ≥ |C|` the sets are at distance at least `c√N/2 > 0`, hence disjoint, and
Lemma 5.12(a) at order `k' ≥ 2(k + 3m_*)` gives `C N^{3m_* − k'/2} ≤ C N^{−k}`; for the other `N`, `N < (2|C|/c)²` and
the trivial bound `2C²N^{2m_*}` is at most `2C²((2|C|/c)²)^{2m_*+k} N^{−k}`. -/

theorem slotSetDist_le_of_mem {δ₀ : ℝ} {T : Torus} {X Y : Finset (Slot δ₀ T)} {x y : Slot δ₀ T} (hx : x ∈ X)
    (hy : y ∈ Y) : slotSetDist X Y ≤ ENNReal.ofReal (slotDist δ₀ T x y) := by
  have hmem : ((x, y) : Slot δ₀ T × Slot δ₀ T) ∈ X ×ˢ Y := Finset.mem_product.mpr ⟨hx, hy⟩
  rw [slotSetDist, Finset.inf_le_iff ENNReal.ofReal_lt_top]
  exact ⟨(x, y), hmem, le_rfl⟩

theorem disjoint_of_pos_le_slotSetDist {δ₀ : ℝ} {T : Torus} {X Y : Finset (Slot δ₀ T)} {a : ℝ} (ha : 0 < a)
    (h : ENNReal.ofReal a ≤ slotSetDist X Y) : Disjoint X Y := by
  rw [Finset.disjoint_left]
  intro s hsX hsY
  have h1 := h.trans (slotSetDist_le_of_mem hsX hsY)
  rw [slotDist_self, ENNReal.ofReal_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
  linarith

theorem half_sqrt_rpow_eq {c : ℝ} (hc : 0 < c) {N : ℝ} (hN : 0 ≤ N) (n : ℕ) :
    (c * Real.sqrt N / 2) ^ (-(n : ℝ)) = (2 / c) ^ n * N ^ (-(n : ℝ) / 2) := by
  have e1 : c * Real.sqrt N / 2 = (c / 2) * Real.sqrt N := by ring
  rw [e1, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hN,
    Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow, inv_div]
  congr 2
  ring

/-- **Lemma 5.13**, the first conclusion: "`Let $(\Tor_N)_{N\in\mathcal N}$ be admissible with $L_x\ge c_*\sqrt N$. Let $\mathcal O$ be a finite set, independent of $N$, of sequences of even operators $O=(O_N)$, possibly depending on a parameter, such that for some $m_*\ge0$ every $O\in\mathcal O$ satisfies $\norm{O_N}\le CN^{m_*}$ and $O\in\AS_{Z_O}$ with prefactor exponent at most $m_*$, uniformly in the parameter. If $O,O'\in\mathcal O$ and $d(Z_{O,N},Z_{O',N})\ge c\sqrt N-C$ for all $N$, with $c>0$, then $[O_N,O'_N]=\Onf$ uniformly in the parameter.`"
— for two families `O`, `O'` (the module docstring), the result's constants `C_k` explicit and chosen after `c`, `C`,
`m_*` and the constants `C^O`, `C^{O'}` ("`those of Lemma~\ref{lem:bookkeeping} on $c$, $C$ and $m_*$`" and on "`those of the sequences in $\mathcal O$`"). -/
theorem bookkeeping_comm.{u} {c : ℝ} (hc : 0 < c) (C mstar : ℝ) (hmstar : 0 ≤ mstar) (CO CO' : ℕ → ℝ) :
    ∃ Cr : ℕ → ℝ, ∀ (η : ℝ → ℝ) (δ₀ : ℝ), IsProfile η → 0 < δ₀ → ∀ (Ts : TorusSeq δ₀) (cstar : ℝ),
      (∀ N ∈ Ts.idx, cstar * Real.sqrt N ≤ (Ts.T N).Lx) →
      ∀ (P : Type u) (Z Z' : P → (N : ℕ) → Finset (Slot δ₀ (Ts.T N))) (O O' : P → (N : ℕ) → FockOp (Ts.T N)),
        (∀ p, ∀ N ∈ Ts.idx, IsEven (O p N) ∧ IsEven (O' p N)) →
        (∀ p, ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (O p N)‖ ≤ C * (N : ℝ) ^ mstar ∧
          ‖toCLM (Ts.T N) (O' p N)‖ ≤ C * (N : ℝ) ^ mstar) →
        (∃ m, m ≤ mstar ∧ ∀ p, ASBound η δ₀ Ts (Z p) (O p) m CO) →
        (∃ m, m ≤ mstar ∧ ∀ p, ASBound η δ₀ Ts (Z' p) (O' p) m CO') →
        (∀ p, ∀ N ∈ Ts.idx, ENNReal.ofReal (c * Real.sqrt N - C) ≤ slotSetDist (Z p N) (Z' p N)) →
          ∀ k : ℕ, ∀ p, ∀ N ∈ Ts.idx,
            ‖toCLM (Ts.T N) (O p N * O' p N - O' p N * O p N)‖ ≤ Cr k * (N : ℝ) ^ (-(k : ℝ)) := by
  have hk' : ∀ k : ℕ, ∃ k' : ℕ, 2 * ((k : ℝ) + 3 * mstar) ≤ k' := fun k => ⟨_, Nat.le_ceil _⟩
  choose kk hkk using hk'
  choose Ck hCk using fun k => norm_comm_le_of_disjoint CO CO' (kk k)
  refine ⟨fun k => |Ck k| * (1 + 2 * |C|) * (2 / c) ^ (kk k) + 2 * C ^ 2 * ((2 * |C| / c) ^ 2) ^ (2 * mstar + k), ?_⟩
  intro η δ₀ hη hδ₀ Ts cstar _ P Z Z' O O' hE hn hO hO' hd k p N hN
  obtain ⟨m, hm, hO⟩ := hO
  obtain ⟨m', hm', hO'⟩ := hO'
  have hmO := (hO p).1
  have hmO' := (hO' p).1
  have hN1 := one_le_of_mem_idx Ts hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hsqrt1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  obtain ⟨hOn, hO'n⟩ := hn p N hN
  have hCN : 0 ≤ C * (N : ℝ) ^ mstar := (norm_nonneg _).trans hOn
  have hNm1 : 1 ≤ (N : ℝ) ^ mstar := Real.one_le_rpow hN1 hmstar
  have hNk : 0 ≤ (N : ℝ) ^ (-(k : ℝ)) := Real.rpow_nonneg hNpos.le _
  have hT1 : 0 ≤ |Ck k| * (1 + 2 * |C|) * (2 / c) ^ (kk k) := by positivity
  have hT2 : 0 ≤ 2 * C ^ 2 * ((2 * |C| / c) ^ 2) ^ (2 * mstar + k) := by positivity
  by_cases hcase : |C| ≤ c * Real.sqrt N / 2
  · -- far: Lemma 5.12(a)
    have hhalf : 0 < c * Real.sqrt N / 2 := by positivity
    have hdist : ENNReal.ofReal (c * Real.sqrt N / 2) ≤ slotSetDist (Z p N) (Z' p N) := by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hd p N hN)
      have := le_abs_self C
      linarith
    have hdisj := disjoint_of_pos_le_slotSetDist hhalf hdist
    have ha := hCk k η δ₀ hη hδ₀ Ts (Z p) (Z' p) (O p) (O' p) m m' (fun N hN => (hE p N hN).1)
      (fun N hN => (hE p N hN).2) (hO p) (hO' p) N hN hdisj
    have hinv : (1 + slotSetDist (Z p N) (Z' p N))⁻¹ ^ (kk k) ≤
        ENNReal.ofReal ((1 + c * Real.sqrt N / 2) ^ (-(kk k : ℝ))) := by
      rw [← ennreal_inv_pow_eq hhalf.le]
      exact pow_le_pow_left₀ (by positivity) (ENNReal.inv_le_inv.mpr (add_le_add le_rfl hdist)) _
    have hQ0 : 0 ≤ (N : ℝ) ^ (m + m') * (1 + ‖toCLM (Ts.T N) (O p N)‖ + ‖toCLM (Ts.T N) (O' p N)‖) := by
      positivity
    have hreal : ‖toCLM (Ts.T N) (O p N * O' p N - O' p N * O p N)‖ ≤
        |Ck k| * ((N : ℝ) ^ (m + m') * (1 + ‖toCLM (Ts.T N) (O p N)‖ + ‖toCLM (Ts.T N) (O' p N)‖)) *
          (1 + c * Real.sqrt N / 2) ^ (-(kk k : ℝ)) := by
      have h1 := ha.trans (mul_le_mul (ENNReal.ofReal_le_ofReal (by
          calc Ck k * (N : ℝ) ^ (m + m') * (1 + ‖toCLM (Ts.T N) (O p N)‖ + ‖toCLM (Ts.T N) (O' p N)‖)
              = Ck k * ((N : ℝ) ^ (m + m') * (1 + ‖toCLM (Ts.T N) (O p N)‖ + ‖toCLM (Ts.T N) (O' p N)‖)) := by ring
            _ ≤ |Ck k| * ((N : ℝ) ^ (m + m') * (1 + ‖toCLM (Ts.T N) (O p N)‖ + ‖toCLM (Ts.T N) (O' p N)‖)) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) hQ0)) hinv (by positivity) (by positivity))
      rw [← ENNReal.ofReal_mul (by positivity)] at h1
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    refine hreal.trans ?_
    have hexp : (N : ℝ) ^ (m + m') ≤ (N : ℝ) ^ (2 * mstar) := rpow_le_rpow_of_one_le hN1 (by linarith)
    have hnorms : 1 + ‖toCLM (Ts.T N) (O p N)‖ + ‖toCLM (Ts.T N) (O' p N)‖ ≤ (1 + 2 * |C|) * (N : ℝ) ^ mstar := by
      have h1 : C * (N : ℝ) ^ mstar ≤ |C| * (N : ℝ) ^ mstar :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      nlinarith
    have hρ : (1 + c * Real.sqrt N / 2) ^ (-(kk k : ℝ)) ≤ (2 / c) ^ (kk k) * (N : ℝ) ^ (-(kk k : ℝ) / 2) := by
      rw [← half_sqrt_rpow_eq hc hNpos.le]
      exact Real.rpow_le_rpow_of_nonpos hhalf (by linarith) (by simp)
    have hfin : (N : ℝ) ^ (2 * mstar) * (N : ℝ) ^ mstar * (N : ℝ) ^ (-(kk k : ℝ) / 2) ≤ (N : ℝ) ^ (-(k : ℝ)) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      apply rpow_le_rpow_of_one_le hN1
      have := hkk k
      linarith
    have hA0 : 0 ≤ (N : ℝ) ^ (2 * mstar) := Real.rpow_nonneg hNpos.le _
    have hB0 : 0 ≤ (N : ℝ) ^ (-(kk k : ℝ) / 2) := Real.rpow_nonneg hNpos.le _
    calc |Ck k| * ((N : ℝ) ^ (m + m') * (1 + ‖toCLM (Ts.T N) (O p N)‖ + ‖toCLM (Ts.T N) (O' p N)‖)) *
          (1 + c * Real.sqrt N / 2) ^ (-(kk k : ℝ))
        ≤ |Ck k| * ((N : ℝ) ^ (2 * mstar) * ((1 + 2 * |C|) * (N : ℝ) ^ mstar)) *
          ((2 / c) ^ (kk k) * (N : ℝ) ^ (-(kk k : ℝ) / 2)) := by
          gcongr
      _ = (|Ck k| * (1 + 2 * |C|) * (2 / c) ^ (kk k)) *
          ((N : ℝ) ^ (2 * mstar) * (N : ℝ) ^ mstar * (N : ℝ) ^ (-(kk k : ℝ) / 2)) := by ring
      _ ≤ (|Ck k| * (1 + 2 * |C|) * (2 / c) ^ (kk k)) * (N : ℝ) ^ (-(k : ℝ)) :=
          mul_le_mul_of_nonneg_left hfin hT1
      _ ≤ _ := by nlinarith
  · -- near: the trivial bound
    push_neg at hcase
    have hNlt : (N : ℝ) ≤ (2 * |C| / c) ^ 2 := by
      have h1 : Real.sqrt N ≤ 2 * |C| / c := by
        rw [le_div_iff₀ hc]
        linarith
      calc (N : ℝ) = Real.sqrt N ^ 2 := (Real.sq_sqrt hNpos.le).symm
        _ ≤ (2 * |C| / c) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    have htriv : ‖toCLM (Ts.T N) (O p N * O' p N - O' p N * O p N)‖ ≤ 2 * C ^ 2 * (N : ℝ) ^ (2 * mstar) := by
      calc ‖toCLM (Ts.T N) (O p N * O' p N - O' p N * O p N)‖
          ≤ 2 * ‖toCLM (Ts.T N) (O p N)‖ * ‖toCLM (Ts.T N) (O' p N)‖ := norm_comm_le _ _
        _ ≤ 2 * (C * (N : ℝ) ^ mstar) * (C * (N : ℝ) ^ mstar) := by
            gcongr
        _ = 2 * C ^ 2 * ((N : ℝ) ^ mstar * (N : ℝ) ^ mstar) := by ring
        _ = 2 * C ^ 2 * (N : ℝ) ^ (2 * mstar) := by rw [← Real.rpow_add hNpos]; ring_nf
    have hsplit : (N : ℝ) ^ (2 * mstar) = (N : ℝ) ^ (2 * mstar + k) * (N : ℝ) ^ (-(k : ℝ)) := by
      rw [← Real.rpow_add hNpos]
      ring_nf
    have hmono : (N : ℝ) ^ (2 * mstar + k) ≤ ((2 * |C| / c) ^ 2) ^ (2 * mstar + k) :=
      Real.rpow_le_rpow hNpos.le hNlt (by positivity)
    calc ‖toCLM (Ts.T N) (O p N * O' p N - O' p N * O p N)‖ ≤ 2 * C ^ 2 * (N : ℝ) ^ (2 * mstar) := htriv
      _ = 2 * C ^ 2 * ((N : ℝ) ^ (2 * mstar + k) * (N : ℝ) ^ (-(k : ℝ))) := by rw [hsplit]
      _ ≤ 2 * C ^ 2 * (((2 * |C| / c) ^ 2) ^ (2 * mstar + k) * (N : ℝ) ^ (-(k : ℝ))) := by
          gcongr
      _ ≤ _ := by nlinarith

/-- **Lemma 5.13**, the second conclusion: "`Any expression obtained from finitely many such commutators, independently of $N$, by sums and by products with operators of norm at most $CN^m$ is $\Onf$ uniformly in the parameter.`"
— for a finite family `c_i` of `O(N^{−∞})` families (the first conclusion's commutators) and operators `L_i`, `R_i` of
norm at most `CN^m`: `Σ_i L_i c_i R_i` is `O(N^{−∞})` uniformly in the parameter ("`a sum, with a number of terms independent of $N$, of products each containing one such commutator`";
a product of finitely many operators of norm at most `CN^m` on either side has norm at most `C'N^{m'}`). -/
theorem IsONegInf.sum_mul_mul {δ₀ : ℝ} {Ts : TorusSeq δ₀} {P : Type*} {ι : Type*} [Fintype ι]
    {cc L R : ι → P → (N : ℕ) → FockOp (Ts.T N)} (hc : ∀ i, IsONegInf Ts (cc i)) {C m : ℝ}
    (hL : ∀ i p, ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (L i p N)‖ ≤ C * (N : ℝ) ^ m)
    (hR : ∀ i p, ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (R i p N)‖ ≤ C * (N : ℝ) ^ m) :
    IsONegInf Ts fun p N => ∑ i, L i p N * cc i p N * R i p N := by
  intro k
  choose Cc hCc using fun i => hc i (k + ⌈2 * max m 0⌉₊)
  refine ⟨∑ i, C ^ 2 * |Cc i|, fun p N hN => ?_⟩
  have hN1 := one_le_of_mem_idx Ts hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hpow : (N : ℝ) ^ m * (N : ℝ) ^ m * (N : ℝ) ^ (-((k + ⌈2 * max m 0⌉₊ : ℕ) : ℝ)) ≤ (N : ℝ) ^ (-(k : ℝ)) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have h1 : 2 * max m 0 ≤ (⌈2 * max m 0⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : m ≤ max m 0 := le_max_left _ _
    push_cast
    linarith
  have hterm : ∀ i, ‖toCLM (Ts.T N) (L i p N * cc i p N * R i p N)‖ ≤ C ^ 2 * |Cc i| * (N : ℝ) ^ (-(k : ℝ)) := by
    intro i
    have hLi := hL i p N hN
    have hRi := hR i p N hN
    have hci := hCc i p N hN
    have hNm : 0 ≤ (N : ℝ) ^ m := by positivity
    have hCN : 0 ≤ C * (N : ℝ) ^ m := (norm_nonneg _).trans hLi
    have hNk : 0 ≤ (N : ℝ) ^ (-((k + ⌈2 * max m 0⌉₊ : ℕ) : ℝ)) := by positivity
    rw [toCLM_mul', toCLM_mul']
    calc ‖toCLM (Ts.T N) (L i p N) * toCLM (Ts.T N) (cc i p N) * toCLM (Ts.T N) (R i p N)‖
        ≤ ‖toCLM (Ts.T N) (L i p N)‖ * ‖toCLM (Ts.T N) (cc i p N)‖ * ‖toCLM (Ts.T N) (R i p N)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (C * (N : ℝ) ^ m) * (|Cc i| * (N : ℝ) ^ (-((k + ⌈2 * max m 0⌉₊ : ℕ) : ℝ))) * (C * (N : ℝ) ^ m) := by
          gcongr
          exact hci.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hNk)
      _ = C ^ 2 * |Cc i| * ((N : ℝ) ^ m * (N : ℝ) ^ m * (N : ℝ) ^ (-((k + ⌈2 * max m 0⌉₊ : ℕ) : ℝ))) := by ring
      _ ≤ C ^ 2 * |Cc i| * (N : ℝ) ^ (-(k : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  calc ‖toCLM (Ts.T N) (∑ i, L i p N * cc i p N * R i p N)‖
      ≤ ∑ i, ‖toCLM (Ts.T N) (L i p N * cc i p N * R i p N)‖ := by
        rw [toCLM_sum']
        exact norm_sum_le _ _
    _ ≤ ∑ i, C ^ 2 * |Cc i| * (N : ℝ) ^ (-(k : ℝ)) := Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, C ^ 2 * |Cc i|) * (N : ℝ) ^ (-(k : ℝ)) := by rw [Finset.sum_mul]

end HRTorus.Locality
