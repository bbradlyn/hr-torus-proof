import HRTorus.Hamiltonian.LocalForm
import HRTorus.Locality.Basic
import HRTorus.Hamiltonian.BandCharges

/-!
# The Hamiltonian in the slot lattice and the class of slot-local covariant Hamiltonians (`Hamiltonian.SlotLocal`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **The definitions and statements were written first and
reviewed against the paper before any proof (review L9a, accepted with no change); the proof phase proved every
theorem of this module — there is no `sorry` here, and nothing here depends on an open statement — with the proof
devices in a section marked as such, among them one device definition, `MEnt`. Two theorems use Theorem 4.2(a)
(`localForm_a`) for `H_N = ∫ h_R dR`, as the paper does: `iota_HN_eq_opIntegral` and Corollary 4.8
(`hollowCore_mem_class`). The constant of Proposition 4.4(ii) is produced by a different route from the paper's
`C^H_k := 55 C_k`: `C^H_k = 8π · 3 · 2 · (√2 · √2 · 2 · C_k)` with `C_k` Lemma 3.5's, from the bounds
`‖e_R‖, ‖e^D_R‖ ≤ 1` (the existential statement is unchanged).**
The paper: the HR paper, `papers/hr/sections/04-hamiltonian.tex` — Proposition 4.4 `prop:slotH` with the claims of its
proof the later statements cite, the sentence after it (`Ĥ_N = ∫ι(h_R)dR`), Definition 4.6 `def:class` and the
paragraph after it, and Corollary 4.8 `cor:hc-in-class`. Remark 4.7 `rem:class-discrete` ("`We do not use this.`") and
the computation of `‖h_R‖` after the proof of Proposition 4.4 ("`Nothing below uses this value`") are not stated.

## The model

* `B^{(r)}_ν(R)` and `h_{R,r}` (`BνR`, `hRr`) are the paper's, with block A's `1_X` (`slotProj`), `𝒮` (`analysis`) and
  block B's `Ball(r, R)` (`slotBall`); `C_h := 7/π` is `ChHC`.
* **"`C^H_k` depending only on `k`, `η` and `δ₀`"**: the constant is existential, quantified after `η`, `δ₀`, `k` and
  before the torus, `R` and `r` — the shape of Lemma 3.5 (`localization_iii_analysis`), whose constant it multiplies
  (`C^H_k := 55 C_k`, so `k` is real, `k ≥ 0`, as there).
* **Definition 4.6 with the data explicit**: `H1Data η δ₀ Ts H` bundles, for a block B `TorusSeq δ₀` and a sequence
  `H N` of operators on the `N`-th physical Fock space, the local terms `h N R` (functions of `R ∈ ℝ²`, periodic, i.e.
  functions on `𝕋_N`), the bound `Ch` and the constants `CH : ℕ → ℝ` (data), and the properties of (H1) (fields, `Prop`s);
  the approximants `h_{R,r}` are existential inside the fields, as in block B's `ASBound`. The constants are fields of
  the structure, not functions of `N`: "`the constants $C_h$ and $C^H_k$ do not depend on $N$`". The order `k` of (H1)
  is a natural number (Definition 3.11's `k ∈ ℕ`, and §5's use). (H2) is a property of the local terms of given (H1) data
  (`H1Data.H2`: "`if, in addition`"); `SatisfiesH1` and `SatisfiesH1H2` are the `Prop` forms (existence of the data).
* Borel measurability of `R ↦ h_R` is entrywise (`Pairs`); the integral is the entrywise `opIntegral` over block A's
  `fundDom`.
-/

open MeasureTheory
open scoped InnerProductSpace Matrix Real ComplexOrder ContDiff
open Complex (I)

noncomputable section

namespace HRTorus.Hamiltonian

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Locality
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op IsEven CAR Alg)

/-! ## Proposition 4.4: definitions -/

/-- **Proposition 4.4(i)**: "`with $C_h:=7/\pi$`". -/
def ChHC : ℝ := 7 / π

/-- **Proposition 4.4(ii)**: "`For $r\ge0$ let $B^{(r)}_\nu(R):=\cpairhat\nu\bigl(\one_{\Ball rR}\Sa\ev R,\one_{\Ball rR}\Sa\evD R\bigr)$ and $h_{R,r}:=8\pi\sum_\nu B^{(r)}_\nu(R)^*B^{(r)}_\nu(R)$.`"
— `B^{(r)}_ν(R)`. -/
def BνR (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (ν : Triplet) (R : ℝ × ℝ) (r : ℝ) : Op (Slot δ₀ T) :=
  cpairHat ν (slotProj δ₀ T (slotBall δ₀ T R r) (analysis η δ₀ T (ev T R)))
    (slotProj δ₀ T (slotBall δ₀ T R r) (analysis η δ₀ T (evD T R)))

/-- **Proposition 4.4(ii)**: `h_{R,r} := 8π Σ_ν B^{(r)}_ν(R)^* B^{(r)}_ν(R)`. -/
def hRr (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (R : ℝ × ℝ) (r : ℝ) : Op (Slot δ₀ T) :=
  ((8 * π : ℝ) : ℂ) • ∑ ν : Triplet, (BνR η δ₀ T ν R r)ᴴ * BνR η δ₀ T ν R r

/-! ## Proof devices for Proposition 4.4 and Definition 4.6 (phase (b); not statements of the paper) -/

section DevicesSL

theorem sum_triplet {M : Type*} [AddCommMonoid M] (f : Triplet → M) :
    ∑ ν : Triplet, f ν = f .plus + f .zero + f .minus := by
  rw [show (Finset.univ : Finset Triplet) = {.plus, .zero, .minus} from rfl]
  simp [Finset.sum_insert, add_assoc]

theorem four_le_min_of_admissible {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) :
    4 ≤ min T.Lx T.Ly := by
  refine le_min (by linarith [hT.2]) (le_trans (le_max_left _ _) hT.1)

theorem norm_ev_sq_le {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (R : ℝ × ℝ) :
    2 * π * ‖ev T R‖ ^ 2 ≤ 1.08 := by
  have h := norm_ev_sq_bound T (four_le_min_of_admissible hδ₀ hT) R
  have := (abs_le.mp (h.1.trans h.2)).2
  linarith

theorem norm_evD_sq_le {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (R : ℝ × ℝ) :
    4 * π * ‖evD T R‖ ^ 2 ≤ 1.62 := by
  have h := norm_evD_sq_bound T (four_le_min_of_admissible hδ₀ hT) R
  have := (abs_le.mp (h.1.trans h.2)).2
  linarith

theorem norm_ev_le_one {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (R : ℝ × ℝ) :
    ‖ev T R‖ ≤ 1 := by
  have h := norm_ev_sq_le hδ₀ hT R
  have hπ : 3 < π := Real.pi_gt_three
  have h2 : ‖ev T R‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖ev T R‖]
  nlinarith [norm_nonneg (ev T R)]

theorem norm_evD_le_one {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (R : ℝ × ℝ) :
    ‖evD T R‖ ≤ 1 := by
  have h := norm_evD_sq_le hδ₀ hT R
  have hπ : 3 < π := Real.pi_gt_three
  have h2 : ‖evD T R‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖evD T R‖]
  nlinarith [norm_nonneg (evD T R)]

theorem isEven_cpairHat {S : Type*} [Fintype S] [DecidableEq S] (ν : Triplet) (h h' : EuclideanSpace ℂ S) :
    IsEven (cpairHat ν h h') := by
  have hP : (Fermion.Pilot.JW.parityOp : Op S) * Fermion.Pilot.JW.parityOp = 1 :=
    Fermion.Pilot.JW.parityOp_mul_parityOp
  have hc : ∀ g : EuclideanSpace ℂ (Mode S), Fermion.Pilot.JW.parityOp * chatVec g * Fermion.Pilot.JW.parityOp =
      -chatVec g := fun g => parityOp_mul_cVec_mul_parityOp _
  have hconj : Fermion.Pilot.JW.parityOp * cpairHat ν h h' * Fermion.Pilot.JW.parityOp = cpairHat ν h h' := by
    simp only [cpairHat, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
    congr 1
    calc Fermion.Pilot.JW.parityOp * (chatVec (spinTensor h σ') * chatVec (spinTensor h' σ)) *
          Fermion.Pilot.JW.parityOp
        = (Fermion.Pilot.JW.parityOp * chatVec (spinTensor h σ') * Fermion.Pilot.JW.parityOp) *
          (Fermion.Pilot.JW.parityOp * chatVec (spinTensor h' σ) * Fermion.Pilot.JW.parityOp) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Fermion.Pilot.JW.parityOp Fermion.Pilot.JW.parityOp, hP, Matrix.one_mul]
      _ = _ := by rw [hc, hc, neg_mul_neg]
  show cpairHat ν h h' * Fermion.Pilot.JW.parityOp = Fermion.Pilot.JW.parityOp * cpairHat ν h h'
  calc cpairHat ν h h' * Fermion.Pilot.JW.parityOp
      = Fermion.Pilot.JW.parityOp * cpairHat ν h h' * Fermion.Pilot.JW.parityOp *
          Fermion.Pilot.JW.parityOp := by rw [hconj]
    _ = Fermion.Pilot.JW.parityOp * cpairHat ν h h' := by rw [Matrix.mul_assoc _ Fermion.Pilot.JW.parityOp, hP,
          Matrix.mul_one]

theorem cpairHat_mem_CAR {S : Type*} [Fintype S] [DecidableEq S] (ν : Triplet) (X : Finset S)
    (h h' : EuclideanSpace ℂ S) (hh : ∀ s, s ∉ X → h s = 0) (hh' : ∀ s, s ∉ X → h' s = 0) :
    cpairHat ν h h' ∈ CAR X := by
  have hmem : ∀ (g : EuclideanSpace ℂ S) (σ : Spin), (∀ s, s ∉ X → g s = 0) → chatVec (spinTensor g σ) ∈ CAR X := by
    intro g σ hg
    refine chatVec_mem_CAR X _ fun μ hμ => ?_
    simp only [spinTensor, WithLp.ofLp_toLp]
    split_ifs
    · exact hg _ hμ
    · rfl
  refine sum_mem fun σ _ => sum_mem fun σ' _ => ?_
  exact SMulMemClass.smul_mem _ (mul_mem (hmem h σ' hh) (hmem h' σ hh'))

theorem slotProj_support (δ₀ : ℝ) (T : Torus) (X : Finset (Slot δ₀ T)) (g : SlotSpace δ₀ T) :
    ∀ s, s ∉ X → slotProj δ₀ T X g s = 0 := fun s hs => by rw [slotProj_apply, ite_eq_right hs]

theorem norm_slotProj_le (δ₀ : ℝ) (T : Torus) (X : Finset (Slot δ₀ T)) (g : SlotSpace δ₀ T) :
    ‖slotProj δ₀ T X g‖ ≤ ‖g‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun s _ => ?_
  rw [slotProj_apply]
  split_ifs
  · rfl
  · simp

theorem slotProj_add_compl (δ₀ : ℝ) (T : Torus) (R : ℝ × ℝ) (r : ℝ) (g : SlotSpace δ₀ T) :
    g - slotProj δ₀ T (slotBall δ₀ T R r) g = slotProj δ₀ T (ballCompl δ₀ T R r) g := by
  refine PiLp.ext fun s => ?_
  rw [PiLp.sub_apply, slotProj_apply, slotProj_apply]
  have hb : s ∈ slotBall δ₀ T R r ↔ s ∉ ballCompl δ₀ T R r := by rw [slotBall_eq_compl, Finset.mem_compl]
  by_cases h : s ∈ ballCompl δ₀ T R r
  · rw [ite_eq_right (fun h' => (hb.mp h') h), ite_eq_left h, sub_zero]
  · rw [ite_eq_left (hb.mpr h), ite_eq_right h, sub_self]

theorem cpairHat_sub_sub {S : Type*} [Fintype S] [DecidableEq S] (ν : Triplet) (f g f' g' : EuclideanSpace ℂ S) :
    cpairHat ν f g - cpairHat ν f' g' = cpairHat ν (f - f') g + cpairHat ν f' (g - g') := by
  have e1 : cpairHat ν f g = cpairHat ν (f - f') g + cpairHat ν f' g := by
    rw [← cpairHat_add_left, sub_add_cancel]
  have e2 : cpairHat ν f' g = cpairHat ν f' (g - g') + cpairHat ν f' g' := by
    rw [← cpairHat_add_right, sub_add_cancel]
  rw [e1, e2]; abel

theorem norm_cpairHat_le_sqrt {S : Type*} [Fintype S] [DecidableEq S] (ν : Triplet) (h h' : EuclideanSpace ℂ S) :
    ‖opCLM (cpairHat ν h h')‖ ≤ Real.sqrt 2 * ‖h‖ * ‖h'‖ := by
  have h1 := norm_cpairHat_le' ν h h'
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  split_ifs at h1
  · exact h1
  · calc _ ≤ 1 * ‖h‖ * ‖h'‖ := h1
      _ ≤ Real.sqrt 2 * ‖h‖ * ‖h'‖ := by gcongr

theorem norm_star_mul_sub_le {S : Type*} [Fintype S] [DecidableEq S] (X Y : Op S) :
    ‖opCLM (Xᴴ * X - Yᴴ * Y)‖ ≤ ‖opCLM X‖ * ‖opCLM (X - Y)‖ + ‖opCLM (X - Y)‖ * ‖opCLM Y‖ := by
  have e : Xᴴ * X - Yᴴ * Y = Xᴴ * (X - Y) + (X - Y)ᴴ * Y := by
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [e, opCLM_add, opCLM_mul, opCLM_mul, opCLM_conjTranspose, opCLM_conjTranspose]
  calc _ ≤ ‖star (opCLM X) * opCLM (X - Y)‖ + ‖star (opCLM (X - Y)) * opCLM Y‖ := norm_add_le _ _
    _ ≤ ‖star (opCLM X)‖ * ‖opCLM (X - Y)‖ + ‖star (opCLM (X - Y))‖ * ‖opCLM Y‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map,
        LinearIsometryEquiv.norm_map]

/-- Measurable entries, for matrix-valued functions. -/
def MEnt {S : Type*} [Fintype S] [DecidableEq S] (F : ℝ × ℝ → Op S) : Prop :=
  ∀ m m', Measurable fun R => F R m m'

theorem MEnt.add {S : Type*} [Fintype S] [DecidableEq S] {F G : ℝ × ℝ → Op S} (hF : MEnt F) (hG : MEnt G) :
    MEnt fun R => F R + G R := fun m m' => by
  simp only [Matrix.add_apply]; exact (hF m m').add (hG m m')

theorem MEnt.mul {S : Type*} [Fintype S] [DecidableEq S] {F G : ℝ × ℝ → Op S} (hF : MEnt F) (hG : MEnt G) :
    MEnt fun R => F R * G R := fun m m' => by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hF m k).mul (hG k m')

theorem MEnt.smul_const {S : Type*} [Fintype S] [DecidableEq S] {F : ℝ × ℝ → Op S} (c : ℂ) (hF : MEnt F) :
    MEnt fun R => c • F R := fun m m' => by
  simp only [Matrix.smul_apply, smul_eq_mul]; exact measurable_const.mul (hF m m')

theorem MEnt.conjTranspose {S : Type*} [Fintype S] [DecidableEq S] {F : ℝ × ℝ → Op S} (hF : MEnt F) :
    MEnt fun R => (F R)ᴴ := fun m m' => by
  simp only [Matrix.conjTranspose_apply]; exact continuous_star.measurable.comp (hF m' m)

theorem MEnt.sum {S : Type*} [Fintype S] [DecidableEq S] {ι : Type*} (s : Finset ι) {F : ι → ℝ × ℝ → Op S}
    (hF : ∀ i ∈ s, MEnt (F i)) : MEnt fun R => ∑ i ∈ s, F i R := fun m m' => by
  simp only [Matrix.sum_apply]; exact Finset.measurable_sum _ fun i hi => hF i hi m m'

theorem MEnt_chatVec {S : Type*} [Fintype S] [DecidableEq S] {g : ℝ × ℝ → EuclideanSpace ℂ (Mode S)}
    (hg : ∀ μ, Measurable fun R => g R μ) : MEnt fun R => HRTorus.Fock.chatVec (g R) := fun m m' => by
  simp only [HRTorus.Fock.chatVec, HRTorus.Fock.cVec, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun μ _ => (continuous_star.measurable.comp (hg μ)).mul measurable_const

theorem measurable_spinTensor_apply {S : Type*} [Fintype S] {g : ℝ × ℝ → EuclideanSpace ℂ S}
    (hg : ∀ s, Measurable fun R => g R s) (σ : Spin) (μ : Mode S) : Measurable fun R => spinTensor (g R) σ μ := by
  simp only [spinTensor, WithLp.ofLp_toLp]
  split_ifs
  · exact hg _
  · exact measurable_const

theorem MEnt_cpairHat {S : Type*} [Fintype S] [DecidableEq S] (ν : Triplet) {g g' : ℝ × ℝ → EuclideanSpace ℂ S}
    (hg : ∀ s, Measurable fun R => g R s) (hg' : ∀ s, Measurable fun R => g' R s) :
    MEnt fun R => cpairHat ν (g R) (g' R) := by
  unfold HRTorus.Hamiltonian.cpairHat
  refine MEnt.sum _ fun σ _ => MEnt.sum _ fun σ' _ => MEnt.smul_const _ (MEnt.mul ?_ ?_)
  · exact MEnt_chatVec (measurable_spinTensor_apply hg σ')
  · exact MEnt_chatVec (measurable_spinTensor_apply hg' σ)

theorem continuous_flatDist_right (T : Torus) (c : ℝ × ℝ) : Continuous fun R : ℝ × ℝ => flatDist T c R := by
  unfold flatDist pdist
  exact Real.continuous_sqrt.comp ((((Metric.continuous_infDist_pt _).comp
    (continuous_const.sub continuous_fst)).pow 2).add (((Metric.continuous_infDist_pt _).comp
      (continuous_const.sub continuous_snd)).pow 2))

theorem continuous_frame (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (s : Slot δ₀ T) : Continuous (frame η δ₀ T s) := by
  unfold frame
  exact continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_const.mul (psi_continuous T _))

theorem contDiff_frame (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (s : Slot δ₀ T) : ContDiff ℝ ∞ (frame η δ₀ T s) := by
  unfold frame
  exact contDiff_const.mul (ContDiff.sum fun j _ => contDiff_const.mul (psi_contDiff T _))

theorem measurable_slotProj_ball_apply (δ₀ : ℝ) (T : Torus) (r : ℝ) {v : ℝ × ℝ → SlotSpace δ₀ T}
    (hv : ∀ s, Measurable fun R => v R s) (s : Slot δ₀ T) :
    Measurable fun R => slotProj δ₀ T (slotBall δ₀ T R r) (v R) s := by
  simp only [slotProj_apply]
  have hset : MeasurableSet {R : ℝ × ℝ | s ∈ slotBall δ₀ T R r} := by
    have : {R : ℝ × ℝ | s ∈ slotBall δ₀ T R r} = {R | flatDist T (centre δ₀ T s) R ≤ r} := by
      ext R; simp [slotBall]
    rw [this]
    exact measurableSet_le (continuous_flatDist_right T _).measurable measurable_const
  exact Measurable.ite hset (hv s) measurable_const

theorem flatDist_add_Lx (T : Torus) (c R : ℝ × ℝ) : flatDist T c (R + (T.Lx, 0)) = flatDist T c R := by
  unfold flatDist
  have h1 : c.1 - (R + (T.Lx, 0)).1 = (c.1 - R.1) + ((-1 : ℤ) : ℝ) * T.Lx := by simp; ring
  have h2 : c.2 - (R + (T.Lx, 0)).2 = c.2 - R.2 := by simp
  rw [h1, h2, pdist_add_int_mul]

theorem flatDist_add_Ly (T : Torus) (c R : ℝ × ℝ) : flatDist T c (R + (0, T.Ly)) = flatDist T c R := by
  unfold flatDist
  have h1 : c.1 - (R + (0, T.Ly)).1 = c.1 - R.1 := by simp
  have h2 : c.2 - (R + (0, T.Ly)).2 = (c.2 - R.2) + ((-1 : ℤ) : ℝ) * T.Ly := by simp; ring
  rw [h1, h2, pdist_add_int_mul]

theorem slotBall_add_Lx (δ₀ : ℝ) (T : Torus) (R : ℝ × ℝ) (r : ℝ) :
    slotBall δ₀ T (R + (T.Lx, 0)) r = slotBall δ₀ T R r := by
  ext s
  simp only [slotBall, Finset.mem_filter, Finset.mem_univ, true_and, flatDist_add_Lx]

theorem slotBall_add_Ly (δ₀ : ℝ) (T : Torus) (R : ℝ × ℝ) (r : ℝ) :
    slotBall δ₀ T (R + (0, T.Ly)) r = slotBall δ₀ T R r := by
  ext s
  simp only [slotBall, Finset.mem_filter, Finset.mem_univ, true_and, flatDist_add_Ly]

theorem norm_entry_le {S : Type*} [Fintype S] [DecidableEq S] (A : Op S) (m m' : Conf S) :
    ‖A m m'‖ ≤ ‖opCLM A‖ := by
  have h1 : (opCLM A (EuclideanSpace.single m' 1)) m = A m m' := by
    rw [show (opCLM A (EuclideanSpace.single m' 1)) m = (A *ᵥ (EuclideanSpace.single m' (1 : ℂ)).ofLp) m from rfl]
    simp [Matrix.mulVec, dotProduct]
  calc ‖A m m'‖ = ‖(opCLM A (EuclideanSpace.single m' 1)) m‖ := by rw [h1]
    _ ≤ ‖opCLM A (EuclideanSpace.single m' 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖opCLM A‖ * ‖EuclideanSpace.single m' (1 : ℂ)‖ := (opCLM A).le_opNorm _
    _ = ‖opCLM A‖ := by simp

theorem volume_fundDom_ne_top (T : Torus) : MeasureTheory.volume (fundDom T) ≠ ⊤ := by
  rw [fundDom, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
  simp [Real.volume_Ico, ENNReal.mul_eq_top]

/-! ### Proof devices for Proposition 4.4(i) under `4 ≤ min{L_x, L_y}` (end-of-stage cleanup; not statements of the paper) -/

/-- **Device**: the bounds of Proposition 4.4(i) on `‖h_R‖` (`norm_hR_le`) for every torus with
`4 ≤ min{L_x, L_y}`, admissible or not — the proof of `norm_hR_le`, which uses admissibility only through this
inequality (block A's `norm_ev_sq_bound` and `norm_evD_sq_bound`). Block E needed this form (`Assembly.Main`'s
`norm_HN_le_dev`), because a torus of `𝒯_N` need not be admissible for any `δ₀`; `norm_hR_le` is this device at an
admissible torus (`four_le_min_of_admissible`). -/
theorem norm_hR_le_of_four_le (T : Torus) (hL : 4 ≤ min T.Lx T.Ly) (R : ℝ × ℝ) :
    ‖toCLM T (hR T R)‖ ≤ 32 * π * ‖ev T R‖ ^ 2 * ‖evD T R‖ ^ 2 ∧
      32 * π * ‖ev T R‖ ^ 2 * ‖evD T R‖ ^ 2 ≤ ChHC := by
  have hb : ∀ ν : Triplet, ‖toCLM T ((Bν T ν R)ᴴ * Bν T ν R)‖ ≤
      (if ν = .zero then 2 else 1) * (‖ev T R‖ ^ 2 * ‖evD T R‖ ^ 2) := by
    intro ν
    rw [toCLM_eq_opCLM, norm_opCLM_conjTranspose_mul_self, Bν, cpair_eq_cpairHat]
    have h1 := norm_cpairHat_le' ν (ev T R) (evD T R)
    have h0 := norm_nonneg (opCLM (cpairHat ν (ev T R) (evD T R)))
    split_ifs at h1 ⊢ with hν
    · calc _ ≤ (Real.sqrt 2 * ‖ev T R‖ * ‖evD T R‖) * (Real.sqrt 2 * ‖ev T R‖ * ‖evD T R‖) :=
            mul_le_mul h1 h1 h0 (by positivity)
        _ = (Real.sqrt 2 * Real.sqrt 2) * (‖ev T R‖ ^ 2 * ‖evD T R‖ ^ 2) := by ring
        _ = 2 * (‖ev T R‖ ^ 2 * ‖evD T R‖ ^ 2) := by rw [Real.mul_self_sqrt (by norm_num)]
    · calc _ ≤ (1 * ‖ev T R‖ * ‖evD T R‖) * (1 * ‖ev T R‖ * ‖evD T R‖) := mul_le_mul h1 h1 h0 (by positivity)
        _ = 1 * (‖ev T R‖ ^ 2 * ‖evD T R‖ ^ 2) := by ring
  have hpi : (0 : ℝ) ≤ 8 * π := by positivity
  refine ⟨?_, ?_⟩
  · rw [hR, toCLM_eq_opCLM, opCLM_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpi,
      opCLM_sum]
    calc 8 * π * ‖∑ ν : Triplet, opCLM ((Bν T ν R)ᴴ * Bν T ν R)‖
        ≤ 8 * π * ∑ ν : Triplet, ‖opCLM ((Bν T ν R)ᴴ * Bν T ν R)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hpi
      _ ≤ 8 * π * ∑ ν : Triplet, (if ν = .zero then (2 : ℝ) else 1) * (‖ev T R‖ ^ 2 * ‖evD T R‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ν _ => hb ν) hpi
      _ = 32 * π * ‖ev T R‖ ^ 2 * ‖evD T R‖ ^ 2 := by
          rw [sum_triplet]; simp only [reduceCtorEq, ite_false, ite_true]; ring
  · have h1 : 2 * π * ‖ev T R‖ ^ 2 ≤ 1.08 := by
      have h := norm_ev_sq_bound T hL R
      have := (abs_le.mp (h.1.trans h.2)).2
      linarith
    have h2 : 4 * π * ‖evD T R‖ ^ 2 ≤ 1.62 := by
      have h := norm_evD_sq_bound T hL R
      have := (abs_le.mp (h.1.trans h.2)).2
      linarith
    have hπ : 0 < π := Real.pi_pos
    have ha : 0 ≤ 2 * π * ‖ev T R‖ ^ 2 := by positivity
    have hb' : 0 ≤ 4 * π * ‖evD T R‖ ^ 2 := by positivity
    have key : 32 * π * ‖ev T R‖ ^ 2 * ‖evD T R‖ ^ 2 =
        4 * (2 * π * ‖ev T R‖ ^ 2) * (4 * π * ‖evD T R‖ ^ 2) / π := by
      field_simp; ring
    rw [key, ChHC, div_le_div_iff_of_pos_right hπ]
    nlinarith [mul_le_mul h1 h2 hb' (by norm_num)]

end DevicesSL

/-! ## Proposition 4.4: statements -/

/-- **Proposition 4.4(i)**: "`For every admissible torus and every $R\in\R^2$:`"
"`$\norm{B_\nu(R)}\le\sqrt2\,\norm{\ev R}\norm{\evD R}$, and $\norm{h_R}\le32\pi\norm{\ev R}^2\norm{\evD R}^2\le C_h$ with $C_h:=7/\pi$.`"
— the first. -/
theorem norm_Bν_le {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (ν : Triplet) (R : ℝ × ℝ) :
    ‖toCLM T (Bν T ν R)‖ ≤ Real.sqrt 2 * ‖ev T R‖ * ‖evD T R‖ := by
  rw [Bν, toCLM_eq_opCLM, cpair_eq_cpairHat]
  exact norm_cpairHat_le_sqrt ν _ _

/-- **Proposition 4.4(i)**, the second: `‖h_R‖ ≤ 32π ‖e_R‖² ‖e'_R‖² ≤ C_h = 7/π`. -/
theorem norm_hR_le {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (R : ℝ × ℝ) :
    ‖toCLM T (hR T R)‖ ≤ 32 * π * ‖ev T R‖ ^ 2 * ‖evD T R‖ ^ 2 ∧
      32 * π * ‖ev T R‖ ^ 2 * ‖evD T R‖ ^ 2 ≤ ChHC :=
  norm_hR_le_of_four_le T (four_le_min_of_admissible hδ₀ hT) R

/-- **Proposition 4.4(ii)**: "`Then $h_{R,r}\in\Alg(\Ball rR)$ is self-adjoint and commutes with $\Nhat\up$ and $\Nhat\dn$`" —
`h_{R,r} ∈ Alg(Ball(r, R))`. -/
theorem hRr_mem_Alg (η : ℝ → ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (R : ℝ × ℝ) {r : ℝ}
    (hr : 0 ≤ r) : hRr η δ₀ T R r ∈ Alg (slotBall δ₀ T R r) := by
  refine Alg_smul_mem _ (Alg_sum_mem _ _ fun ν _ => ?_)
  have hB : BνR η δ₀ T ν R r ∈ Alg (slotBall δ₀ T R r) :=
    ⟨cpairHat_mem_CAR ν _ _ _ (slotProj_support δ₀ T _ _) (slotProj_support δ₀ T _ _), isEven_cpairHat ν _ _⟩
  have hBH : (BνR η δ₀ T ν R r)ᴴ ∈ Alg (slotBall δ₀ T R r) := by
    refine ⟨Fermion.Pilot.JW.conjTranspose_mem_CAR hB.1, ?_⟩
    have := hB.2
    show (BνR η δ₀ T ν R r)ᴴ * Fermion.Pilot.JW.parityOp = Fermion.Pilot.JW.parityOp * (BνR η δ₀ T ν R r)ᴴ
    have hPsa : (Fermion.Pilot.JW.parityOp : Op (Slot δ₀ T))ᴴ = Fermion.Pilot.JW.parityOp := parityOp_conjTranspose
    rw [← hPsa, ← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, this.eq]
  exact Alg_mul_mem hBH hB

/-- **Proposition 4.4(ii)**: `h_{R,r}` is self-adjoint. -/
theorem hRr_isSelfAdjoint (η : ℝ → ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (R : ℝ × ℝ)
    {r : ℝ} (hr : 0 ≤ r) : IsSelfAdjoint (hRr η δ₀ T R r) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  simp only [hRr, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  simp [Complex.conj_ofReal]

/-- **Proposition 4.4(ii)**: `h_{R,r}` commutes with `N̂_↑` and `N̂_↓` (block B's `IsSectorPreservingS`). -/
theorem hRr_isSectorPreservingS (η : ℝ → ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀)
    (R : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) : IsSectorPreservingS (hRr η δ₀ T R r) := by
  rw [hRr]
  exact isSectorPreservingS_smul_sum _ _ _ fun ν _ => isSectorPreservingS_star_cpairHat ν _ _

/-- **Proposition 4.4(ii)**: "`and for every $k$`" "`\norm{\iota(h_R)-h_{R,r}}\le C^H_k(1+r)^{-k},`"
"`with $C^H_k$ depending only on $k$, $\eta$ and $\delta_0$.`" — the constant quantified before the torus, `R` and `r`. -/
theorem exists_norm_iota_hR_sub_hRr_le {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {k : ℝ}
    (hk : 0 ≤ k) :
    ∃ C : ℝ, ∀ T : Torus, T.Admissible δ₀ → ∀ (R : ℝ × ℝ) (r : ℝ), 0 ≤ r →
      ‖opCLM (iota η δ₀ T (hR T R) - hRr η δ₀ T R r)‖ ≤ C * (1 + r) ^ (-k) := by
  obtain ⟨Cl, hCl⟩ := localization_iii_analysis hη hδ₀ hk
  refine ⟨8 * π * 3 * (2 * (Real.sqrt 2 * Real.sqrt 2 * 2 * Cl)), fun T hT R r hr => ?_⟩
  obtain ⟨hl1, hl2⟩ := hCl T hT R r hr
  have hCl0 : 0 ≤ Cl := by
    have hpos : 0 < (1 + r) ^ (-k) := Real.rpow_pos_of_pos (by linarith) _
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hpos
    linarith [norm_nonneg (slotProj δ₀ T (ballCompl δ₀ T R r) (analysis η δ₀ T (ev T R)))]
  set f := analysis η δ₀ T (ev T R) with hf
  set g := analysis η δ₀ T (evD T R) with hg
  set fr := slotProj δ₀ T (slotBall δ₀ T R r) f
  set gr := slotProj δ₀ T (slotBall δ₀ T R r) g
  have hfn : ‖f‖ ≤ 1 := by rw [hf, norm_analysis hη hδ₀ hT]; exact norm_ev_le_one hδ₀ hT R
  have hgn : ‖g‖ ≤ 1 := by rw [hg, norm_analysis hη hδ₀ hT]; exact norm_evD_le_one hδ₀ hT R
  have hfrn : ‖fr‖ ≤ 1 := (norm_slotProj_le δ₀ T _ f).trans hfn
  have hgrn : ‖gr‖ ≤ 1 := (norm_slotProj_le δ₀ T _ g).trans hgn
  have hdf : ‖f - fr‖ ≤ Cl * (1 + r) ^ (-k) := by rw [slotProj_add_compl]; exact hl1
  have hdg : ‖g - gr‖ ≤ Cl * (1 + r) ^ (-k) := by rw [slotProj_add_compl]; exact hl2
  set ε := Cl * (1 + r) ^ (-k) with hε
  have hε0 : 0 ≤ ε := mul_nonneg hCl0 (Real.rpow_nonneg (by linarith) _)
  have hιh : iota η δ₀ T (hR T R) = ((8 * π : ℝ) : ℂ) • ∑ ν : Triplet,
      (cpairHat ν f g)ᴴ * cpairHat ν f g := by
    rw [hR, ← iotaHom_apply hη hδ₀ hT, map_smul, map_sum]
    refine congrArg (((8 * π : ℝ) : ℂ) • ·) (Finset.sum_congr rfl fun ν _ => ?_)
    rw [map_mul, ← Matrix.star_eq_conjTranspose, map_star, iotaHom_apply hη hδ₀ hT, Bν, iota_cpair hη hδ₀ hT,
      Matrix.star_eq_conjTranspose]
  have hterm : ∀ ν : Triplet, ‖opCLM ((cpairHat ν f g)ᴴ * cpairHat ν f g - (BνR η δ₀ T ν R r)ᴴ * BνR η δ₀ T ν R r)‖ ≤
      2 * (Real.sqrt 2 * Real.sqrt 2 * 2 * ε) := by
    intro ν
    have hX : ‖opCLM (cpairHat ν f g)‖ ≤ Real.sqrt 2 := by
      have := norm_cpairHat_le_sqrt ν f g
      have h1 : Real.sqrt 2 * ‖f‖ * ‖g‖ ≤ Real.sqrt 2 * 1 * 1 := by gcongr
      linarith
    have hY : ‖opCLM (BνR η δ₀ T ν R r)‖ ≤ Real.sqrt 2 := by
      have := norm_cpairHat_le_sqrt ν fr gr
      have h1 : Real.sqrt 2 * ‖fr‖ * ‖gr‖ ≤ Real.sqrt 2 * 1 * 1 := by gcongr
      simp only [BνR] at *
      linarith
    have hXY : ‖opCLM (cpairHat ν f g - BνR η δ₀ T ν R r)‖ ≤ Real.sqrt 2 * 2 * ε := by
      rw [BνR, cpairHat_sub_sub, opCLM_add]
      have h1 := norm_cpairHat_le_sqrt ν (f - fr) g
      have h2 := norm_cpairHat_le_sqrt ν fr (g - gr)
      have h3 : Real.sqrt 2 * ‖f - fr‖ * ‖g‖ ≤ Real.sqrt 2 * ε * 1 := by gcongr
      have h4 : Real.sqrt 2 * ‖fr‖ * ‖g - gr‖ ≤ Real.sqrt 2 * 1 * ε := by gcongr
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ Real.sqrt 2 * ε * 1 + Real.sqrt 2 * 1 * ε := add_le_add (h1.trans h3) (h2.trans h4)
        _ = Real.sqrt 2 * 2 * ε := by ring
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    calc _ ≤ ‖opCLM (cpairHat ν f g)‖ * ‖opCLM (cpairHat ν f g - BνR η δ₀ T ν R r)‖ +
          ‖opCLM (cpairHat ν f g - BνR η δ₀ T ν R r)‖ * ‖opCLM (BνR η δ₀ T ν R r)‖ := norm_star_mul_sub_le _ _
      _ ≤ Real.sqrt 2 * (Real.sqrt 2 * 2 * ε) + (Real.sqrt 2 * 2 * ε) * Real.sqrt 2 := by
          gcongr
      _ = 2 * (Real.sqrt 2 * Real.sqrt 2 * 2 * ε) := by ring
  have hpi : (0 : ℝ) ≤ 8 * π := by positivity
  rw [hιh, hRr, ← smul_sub, ← Finset.sum_sub_distrib, opCLM_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpi, opCLM_sum]
  calc 8 * π * ‖∑ ν : Triplet, opCLM ((cpairHat ν f g)ᴴ * cpairHat ν f g - (BνR η δ₀ T ν R r)ᴴ * BνR η δ₀ T ν R r)‖
      ≤ 8 * π * ∑ ν : Triplet, ‖opCLM ((cpairHat ν f g)ᴴ * cpairHat ν f g -
          (BνR η δ₀ T ν R r)ᴴ * BνR η δ₀ T ν R r)‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hpi
    _ ≤ 8 * π * ∑ _ν : Triplet, 2 * (Real.sqrt 2 * Real.sqrt 2 * 2 * ε) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ν _ => hterm ν) hpi
    _ = 8 * π * 3 * (2 * (Real.sqrt 2 * Real.sqrt 2 * 2 * Cl)) * (1 + r) ^ (-k) := by
        rw [Finset.sum_const, Finset.card_univ, show Fintype.card Triplet = 3 from rfl, hε]
        simp only [nsmul_eq_mul]
        push_cast
        ring

/-- **Proposition 4.4(iii)**: "`For each $r\ge0$ the map $R\mapsto h_{R,r}$ is Borel measurable.`" (entrywise). -/
theorem hRr_measurable (η : ℝ → ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) {r : ℝ}
    (hr : 0 ≤ r) (m m' : Conf (Slot δ₀ T)) : Measurable fun R : ℝ × ℝ => hRr η δ₀ T R r m m' := by
  have hf : ∀ s, Measurable fun R : ℝ × ℝ => analysis η δ₀ T (ev T R) s := fun s => by
    simp only [analysis_ev]
    exact (continuous_star.comp (continuous_frame η δ₀ T s)).measurable
  have hg : ∀ s, Measurable fun R : ℝ × ℝ => analysis η δ₀ T (evD T R) s := fun s => by
    simp only [analysis_evD]
    exact (continuous_star.comp (contDiff_Dcov (contDiff_frame η δ₀ T s)).continuous).measurable
  have hB : ∀ ν, MEnt fun R => BνR η δ₀ T ν R r := fun ν =>
    MEnt_cpairHat ν (measurable_slotProj_ball_apply δ₀ T r hf) (measurable_slotProj_ball_apply δ₀ T r hg)
  have h := MEnt.smul_const ((8 * π : ℝ) : ℂ) (MEnt.sum (Finset.univ : Finset Triplet)
    (fun ν _ => MEnt.mul (MEnt.conjTranspose (hB ν)) (hB ν)))
  exact h m m'

/-- The proof of **Proposition 4.4(iii)**: "`and $h_{R,r}$ is a function of $R\in\Tor_N$`" — periodic in `R_x`. -/
theorem hRr_add_Lx (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (R : ℝ × ℝ) (r : ℝ) :
    hRr η δ₀ T (R + (T.Lx, 0)) r = hRr η δ₀ T R r := by
  have hB : ∀ ν, BνR η δ₀ T ν (R + (T.Lx, 0)) r =
      Complex.exp (starRingEnd ℂ (-(I * (T.Lx : ℂ) * (R.2 : ℂ))) + starRingEnd ℂ (-(I * (T.Lx : ℂ) * (R.2 : ℂ)))) •
        BνR η δ₀ T ν R r := by
    intro ν
    rw [BνR, BνR, slotBall_add_Lx, ev_add_Lx, evD_add_Lx]
    simp only [map_smul]
    rw [cpairHat_smul_smul, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp only [hRr, hB, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  refine congrArg (((8 * π : ℝ) : ℂ) • ·) (Finset.sum_congr rfl fun ν _ => ?_)
  rw [mul_comm, phase_star_mul_self (by simp), one_smul]

/-- The same — periodic in `R_y`. -/
theorem hRr_add_Ly (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus) (R : ℝ × ℝ) (r : ℝ) :
    hRr η δ₀ T (R + (0, T.Ly)) r = hRr η δ₀ T R r := by
  simp only [hRr, BνR, slotBall_add_Ly, ev_add_Ly, evD_add_Ly]

/-- After **Proposition 4.4**: "`In the language of lattice systems, $\Hhat_N=\int\iota(h_R)\,\dd R$ is a rapidly decaying interaction of uniform size.`"
— the identity `ι(H_N) = ∫_{𝕋_N} ι(h_R) dR`. -/
theorem iota_HN_eq_opIntegral {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) :
    iota η δ₀ T (HN T) = opIntegral (fundDom T) fun R => iota η δ₀ T (hR T R) := by
  rw [(localForm_a T).2]
  refine iota_opIntegral hη hδ₀ hT _ _ fun m m' => ?_
  simpa using integrableOn_inter_fundDom (hR_contDiff T m m').continuous T Set.univ

/-! ## Definition 4.6: the class -/

/-- **Definition 4.6** "`Let $\mathcal N\subset\N$ be infinite and let $(\Tor_N)_{N\in\mathcal N}$ be admissible tori. A sequence $H=(H_N)_{N\in\mathcal N}$ of self-adjoint operators on $\Fock$ satisfies:`"
"`(\emph{slot locality of uniform size}) if $H_N=\int_{\Tor_N}h_R\,\dd R$, where $R\mapsto h_R=h_{N,R}$ is a Borel measurable map from $\Tor_N$ to the self-adjoint, sector-preserving operators on $\Fock$ with $\sup_R\norm{h_R}\le C_h$, and for every $k$ there is $C^H_k$ such that for all $N\in\mathcal N$, $R\in\Tor_N$ and $r\ge0$ some $h_{R,r}\in\Alg(\Ball rR)$ satisfies $\norm{\iota(h_R)-h_{R,r}}\le C^H_k(1+r)^{-k}$; the constants $C_h$ and $C^H_k$ do not depend on $N$;`"
— (H1) with its data explicit (the module docstring): the local terms `h`, the bound `Ch` and the constants `CH`, and the
properties. -/
structure H1Data (η : ℝ → ℝ) (δ₀ : ℝ) (Ts : TorusSeq δ₀) (H : (N : ℕ) → FockOp (Ts.T N)) where
  /-- the local terms `h_R = h_{N,R}`, for `R ∈ ℝ²` -/
  h : (N : ℕ) → ℝ × ℝ → FockOp (Ts.T N)
  /-- the bound `C_h` -/
  Ch : ℝ
  /-- the constants `C^H_k`, `k ∈ ℕ` -/
  CH : ℕ → ℝ
  /-- the setting: "`of self-adjoint operators on $\Fock$`" -/
  H_isSelfAdjoint : ∀ N ∈ Ts.idx, IsSelfAdjoint (H N)
  /-- `H_N = ∫_{𝕋_N} h_R dR` -/
  eq_opIntegral : ∀ N ∈ Ts.idx, H N = opIntegral (fundDom (Ts.T N)) (h N)
  /-- `R ↦ h_R` is a map from `𝕋_N`: periodic in `R_x` -/
  h_add_Lx : ∀ N ∈ Ts.idx, ∀ R : ℝ × ℝ, h N (R + ((Ts.T N).Lx, 0)) = h N R
  /-- the same, periodic in `R_y` -/
  h_add_Ly : ∀ N ∈ Ts.idx, ∀ R : ℝ × ℝ, h N (R + (0, (Ts.T N).Ly)) = h N R
  /-- Borel measurable (entrywise) -/
  h_measurable : ∀ N ∈ Ts.idx, ∀ m m' : Conf (ZMod (Ts.T N).Nφ), Measurable fun R : ℝ × ℝ => h N R m m'
  /-- into the self-adjoint operators -/
  h_isSelfAdjoint : ∀ N ∈ Ts.idx, ∀ R : ℝ × ℝ, IsSelfAdjoint (h N R)
  /-- into the sector-preserving operators -/
  h_isSectorPreserving : ∀ N ∈ Ts.idx, ∀ R : ℝ × ℝ, IsSectorPreserving (Ts.T N) (h N R)
  /-- `sup_R ‖h_R‖ ≤ C_h` -/
  norm_h_le : ∀ N ∈ Ts.idx, ∀ R : ℝ × ℝ, ‖toCLM (Ts.T N) (h N R)‖ ≤ Ch
  /-- the approximants `h_{R,r} ∈ Alg(Ball(r, R))` with `‖ι(h_R) − h_{R,r}‖ ≤ C^H_k (1 + r)^{−k}` -/
  approx : ∀ k : ℕ, ∀ N ∈ Ts.idx, ∀ (R : ℝ × ℝ) (r : ℝ), 0 ≤ r →
    ∃ A ∈ Alg (slotBall δ₀ (Ts.T N) R r),
      ‖opCLM (iota η δ₀ (Ts.T N) (h N R) - A)‖ ≤ CH k * (1 + r) ^ (-(k : ℝ))

/-- **Definition 4.6 (H2)**: "`(\emph{covariance}) if, in addition, $\Theta^*h_R\Theta=h_{R+\kappa\ex}$ for all $N\in\mathcal N$ and $R\in\Tor_N$.`"
— a property of the local terms of (H1) data. -/
def H1Data.H2 {η : ℝ → ℝ} {δ₀ : ℝ} {Ts : TorusSeq δ₀} {H : (N : ℕ) → FockOp (Ts.T N)} (d : H1Data η δ₀ Ts H) :
    Prop :=
  ∀ N ∈ Ts.idx, ∀ R : ℝ × ℝ, (Θ (Ts.T N))ᴴ * d.h N R * Θ (Ts.T N) = d.h N (R + ((Ts.T N).κ, 0))

/-- **Definition 4.6**: `H` satisfies (H1) — (H1) data exist. -/
def SatisfiesH1 (η : ℝ → ℝ) (δ₀ : ℝ) (Ts : TorusSeq δ₀) (H : (N : ℕ) → FockOp (Ts.T N)) : Prop :=
  Nonempty (H1Data η δ₀ Ts H)

/-- **Definition 4.6**: `H` satisfies (H1) and (H2) — (H1) data exist whose local terms satisfy (H2). -/
def SatisfiesH1H2 (η : ℝ → ℝ) (δ₀ : ℝ) (Ts : TorusSeq δ₀) (H : (N : ℕ) → FockOp (Ts.T N)) : Prop :=
  ∃ d : H1Data η δ₀ Ts H, d.H2

/-! ### Statements: the paragraph after Definition 4.6 -/

/-- After **Definition 4.6**: "`Under (H1) the operators $h_R$ are even (Lemma~\ref{lem:sectors}(ii)), and under (H2) $[\Theta,H_N]=0$, by the translation invariance of Lebesgue measure.`"
— the first. -/
theorem H1Data.h_isEven {η : ℝ → ℝ} {δ₀ : ℝ} {Ts : TorusSeq δ₀} {H : (N : ℕ) → FockOp (Ts.T N)}
    (d : H1Data η δ₀ Ts H) : ∀ N ∈ Ts.idx, ∀ R : ℝ × ℝ, IsEven (d.h N R) := by
  intro N hN R
  exact IsSectorPreserving.isEven (Ts.T N) (d.h_isSectorPreserving N hN R)

/-- The same, the second: under (H2), `[Θ, H_N] = 0`. -/
theorem H1Data.commute_Θ_of_H2 {η : ℝ → ℝ} {δ₀ : ℝ} {Ts : TorusSeq δ₀} {H : (N : ℕ) → FockOp (Ts.T N)}
    (d : H1Data η δ₀ Ts H) (hd : d.H2) : ∀ N ∈ Ts.idx, Commute (Θ (Ts.T N)) (H N) := by
  intro N hN
  have hd' : ∀ R : ℝ × ℝ, (Θ (Ts.T N))ᴴ * d.h N R * Θ (Ts.T N) = d.h N (R + ((Ts.T N).κ, 0)) := hd N hN
  have hint : ∀ m m' : Conf (ZMod (Ts.T N).Nφ),
      IntegrableOn (fun R => d.h N R m m') (Set.univ ∩ fundDom (Ts.T N)) := by
    intro m m'
    rw [Set.univ_inter]
    refine MeasureTheory.Measure.integrableOn_of_bounded (volume_fundDom_ne_top (Ts.T N))
      (d.h_measurable N hN m m').aestronglyMeasurable (M := d.Ch) ?_
    exact Filter.Eventually.of_forall fun R => (norm_entry_le _ m m').trans (d.norm_h_le N hN R)
  let Φ : FockOp (Ts.T N) →ₗ[ℂ] FockOp (Ts.T N) :=
    (LinearMap.mulLeft ℂ (Θ (Ts.T N))ᴴ).comp (LinearMap.mulRight ℂ (Θ (Ts.T N)))
  have hΦ : ∀ A : FockOp (Ts.T N), Φ A = (Θ (Ts.T N))ᴴ * A * Θ (Ts.T N) := fun A => by
    simp only [Φ, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.mul_assoc]
  have hconj : (Θ (Ts.T N))ᴴ * H N * Θ (Ts.T N) = H N := by
    rw [d.eq_opIntegral N hN, ← hΦ, show fundDom (Ts.T N) = Set.univ ∩ fundDom (Ts.T N) by rw [Set.univ_inter],
      opIntegral_map Φ _ _ hint]
    simp only [hΦ, hd']
    ext m m'
    simp only [opIntegral, Matrix.of_apply]
    have hD : IsTorusSet (Ts.T N) Set.univ := ⟨MeasurableSet.univ, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    have := setIntegral_inter_fundDom_shift (Ts.T N) hD (fun R => d.h N R m m')
      (fun R => by rw [d.h_add_Lx N hN R])
    rw [this, Set.vadd_set_univ]
  have hu : Θ (Ts.T N) * (Θ (Ts.T N))ᴴ = 1 := mul_conjTranspose_self_of_mem_unitary (Θ_mem_unitary (Ts.T N))
  show Θ (Ts.T N) * H N = H N * Θ (Ts.T N)
  calc Θ (Ts.T N) * H N = Θ (Ts.T N) * ((Θ (Ts.T N))ᴴ * H N * Θ (Ts.T N)) := by rw [hconj]
    _ = H N * Θ (Ts.T N) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.one_mul]

/-! ## Corollary 4.8 -/

/-- **Corollary 4.8**: "`For every infinite $\mathcal N\subset\N$ and admissible tori $(\Tor_N)_{N\in\mathcal N}$, the hollow-core Hamiltonians $(H_N)_{N\in\mathcal N}$ satisfy (H1), with the local terms $h_R$ of Definition~\ref{def:pairs}, $C_h=7/\pi$ and the constants $C^H_k$ of Proposition~\ref{prop:slotH}, and they satisfy (H2).`"
— there are constants `C^H_k` (`k ∈ ℕ`) for which Proposition 4.4(ii)'s estimate holds on every admissible torus (so
depending only on `k`, `η`, `δ₀`), and for every `TorusSeq` (H1) data for `H_N` with `h_R` of Definition 4.1,
`C_h = 7/π` and these `C^H_k`, satisfying (H2). -/
theorem hollowCore_mem_class {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ CH : ℕ → ℝ,
      (∀ k : ℕ, ∀ T : Torus, T.Admissible δ₀ → ∀ (R : ℝ × ℝ) (r : ℝ), 0 ≤ r →
        ‖opCLM (iota η δ₀ T (hR T R) - hRr η δ₀ T R r)‖ ≤ CH k * (1 + r) ^ (-(k : ℝ))) ∧
      ∀ Ts : TorusSeq δ₀, ∃ d : H1Data η δ₀ Ts (fun N => HN (Ts.T N)),
        d.h = (fun N => hR (Ts.T N)) ∧ d.Ch = ChHC ∧ d.CH = CH ∧ d.H2 := by
  choose CH hCH using fun k : ℕ => exists_norm_iota_hR_sub_hRr_le hη hδ₀ (k := (k : ℝ)) (Nat.cast_nonneg k)
  refine ⟨CH, fun k T hT R r hr => hCH k T hT R r hr, fun Ts => ?_⟩
  let d : H1Data η δ₀ Ts (fun N => HN (Ts.T N)) :=
    ⟨fun N => hR (Ts.T N), ChHC, CH,
      fun N _ => HN_isSelfAdjoint (Ts.T N),
      fun N _ => (localForm_a (Ts.T N)).2,
      fun N _ R => hR_add_Lx (Ts.T N) R,
      fun N _ R => hR_add_Ly (Ts.T N) R,
      fun N _ m m' => hR_measurable (Ts.T N) m m',
      fun N _ R => hR_isSelfAdjoint (Ts.T N) R,
      fun N _ R => hR_isSectorPreserving (Ts.T N) R,
      fun N hN R => (norm_hR_le hδ₀ (Ts.admissible N hN) R).1.trans (norm_hR_le hδ₀ (Ts.admissible N hN) R).2,
      fun k N hN R r hr => ⟨hRr η δ₀ (Ts.T N) R r, hRr_mem_Alg η hδ₀ (Ts.admissible N hN) R hr,
        hCH k (Ts.T N) (Ts.admissible N hN) R r hr⟩⟩
  refine ⟨d, rfl, rfl, rfl, ?_⟩
  intro N _ R
  exact Θ_conj_hR (Ts.T N) R

end HRTorus.Hamiltonian
