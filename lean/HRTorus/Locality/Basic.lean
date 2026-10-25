import HRTorus.Fock.Embedding
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The slot lattice's geometry and the locality vocabulary (T-0056 block B, `Locality.Basic`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **The definitions and statements were written
first and reviewed against the paper (phase (a)) and are unchanged; phase (b) added the proofs and the proof
devices, each marked as such (in its section's header or its docstring). Every theorem is proved; there is no
`sorry`.** The paper: the HR paper, `papers/hr/sections/03-slot-frame.tex` —
Lemma 3.2(iii) `lem:frame-consistency` (the clause Lemma 3.6 uses), Proposition 3.4 `prop:geometry`, Lemma 3.6
`lem:columns`, and §3.3 whole: Definition 3.9 `def:strips`, Lemma 3.10 `lem:strips`, Definition 3.11
`def:almostsupported` with the sentence after it (Remark 3.12 `rem:bbdf-almost` compares with another paper's
definition and is not stated).

## The model

* Points of `𝕋_N` are their lifts `R ∈ ℝ × ℝ` and distances are `SlotFrame.flatDist`, as in `SlotFrame`; the slot
  distance and the fattening are `Fock.slotDist` and `Fock.fat`; the transverse coordinate `x_s := x_a` is `xs`.
* **Subsets of the circle `ℝ/L_xℤ` are `L_x`-periodic subsets of `ℝ`** (their preimages): an interval `I ⊂ ℝ/L_xℤ` is
  the image `circImage L_x J = {x : ∃ m ∈ ℤ, x + mL_x ∈ J}` of an interval `J` of `ℝ` (the paper's proof of
  Proposition 3.4(iii): "`Let $I$ be the image of an interval $\tilde I\subset\R$ of length $\abs I$.`"); `x_s ∈ I` is
  membership of the representative `x_a`, `a ∈ {0, …, n_x − 1}`, in the periodic set. **"Open" and "length" are carried
  by the real interval**: an open interval of length `ℓ` is `J = Ioo a b` with `b − a = ℓ`; "an interval of length
  `ℓ`" in Proposition 3.4(iii) is any `J ⊆ Icc a b` with `b − a = ℓ` (this covers the four kinds of interval of that
  length, and subsets of them, for which the bound follows by monotonicity). The **closed `ρ`-neighbourhood** `I_ρ` is
  Mathlib's `Metric.cthickening ρ I` of the periodic set (the real distance to the periodic preimage is the circle
  distance to `I`); for an open interval it is the widened closed interval (`cthickening_circImage_Ioo`).
* **Definition 3.11's sequences** are carried as functions of `N` from the start: a `TorusSeq δ₀` bundles the infinite
  index set `𝒩 ⊆ ℕ` and tori `T N` with `N` electrons, admissible for `N ∈ 𝒩`; `Z N` and `A N` are a `Finset` of
  slots and an operator on `𝓗_N` of the `N`-th torus, for every `N` (values off `𝒩` are never used). The prefactor
  exponent `m` and the constants `C_k` are **explicit data**: `ASBound … m C` is the estimate for given `m` and
  `C : ℕ → ℝ`, a `ASWitness` bundles `m`, `C` and the estimate, `AlmostSupported` is the existence of a witness
  (`almostSupported_iff` restates it with the paper's quantifiers), and "uniformly in a parameter" is one `m` and
  one `C` for every value of a parameter in an arbitrary type.
* **The set norm** `‖A‖_{X;k}` lives in `ℝ≥0∞`: it is `+∞` for an operator that is not even and `k > 0`
  (`setNorm_eq_top`), and also, for `k > 0`, for a non-scalar operator and `X = ∅` (§5 states Lemmas 5.5–5.6 for
  "`$\norm A_{X;\max\{k,3\}}<\infty$`" and uses both conventions). The order `k` is real (`(1 + r)^k` is `Real.rpow`), so that §5's `\max\{k,3\}`
  and real orders are covered.
-/

open scoped InnerProductSpace Matrix ENNReal Real
open Complex (I)

noncomputable section

namespace HRTorus.Locality

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op IsEven CAR Alg)

/-! ## Definitions: coordinates, balls, strips, columns, the constants -/

section Defs

variable (δ₀ : ℝ) (T : Torus)

/-- **Definition 3.1**: "`centres $\cen s:=(x_a,y_\ell)\in\Tor_N$ and transverse coordinates $x_s:=x_a$`" — `x_s`. -/
def xs (s : Slot δ₀ T) : ℝ :=
  (centre δ₀ T s).1

/-- **Proposition 3.4(ii)**: "`where $\Ball rR:=\{s\in\Slots:d(s,R)\le r\}$`", with "`$d(s,R):=d(\cen s,R)$`"
(Definition 3.1) the flat distance; the complement of `SlotFrame.ballCompl`. -/
def slotBall (R : ℝ × ℝ) (r : ℝ) : Finset (Slot δ₀ T) :=
  Finset.univ.filter fun s => flatDist T (centre δ₀ T s) R ≤ r

/-- The image `I ⊂ ℝ/Lℤ` of a set `J ⊆ ℝ`, as the `L`-periodic subset `{x : ∃ m ∈ ℤ, x + mL ∈ J}` of `ℝ`. -/
def circImage (L : ℝ) (J : Set ℝ) : Set ℝ :=
  {x | ∃ m : ℤ, x + m * L ∈ J}

open Classical in
/-- **Proposition 3.4(iii)** / **Definition 3.9**: "`the strip $\Str(I):=\{s\in\Slots:x_s\in I\}$`", for a subset `I`
of `ℝ/L_xℤ` given as an `L_x`-periodic subset of `ℝ`. -/
def strip (I : Set ℝ) : Finset (Slot δ₀ T) :=
  Finset.univ.filter fun s => xs δ₀ T s ∈ I

/-- **Lemma 3.6**: "`\Col(j):=\{s\in\Slots:\abs{x_s-\kappa j}_{L_x}<\delta_x\}`", the column of `j ∈ ℤ`
(`|u|_{L_x}` is `SlotFrame.pdist`). -/
def col (j : ℤ) : Finset (Slot δ₀ T) :=
  Finset.univ.filter fun s => pdist T.Lx (xs δ₀ T s - T.κ * j) < δx δ₀ T

/-- **Definition 3.9**: "`For a set $\mathcal B\subset\Z_{\Nphi}$ of orbitals (a \emph{band}), $\Col(\mathcal B):=\bigcup_{j\in\mathcal B}\Col(j)$`"
(with the representative `j.val`; `col_intCast_val`: any representative gives the same column). -/
def colBand (B : Finset (ZMod T.Nφ)) : Finset (Slot δ₀ T) :=
  B.biUnion fun j => col δ₀ T (j.val : ℤ)

/-- **Proposition 3.4(ii)**: "`we take $\Cvol:=\max\{1,3/\delta_0\}\max\{1,6\delta_0/\pi\}$`". -/
def Cvol (δ₀ : ℝ) : ℝ :=
  max 1 (3 / δ₀) * max 1 (6 * δ₀ / π)

/-- **Proposition 3.4(iii)**: "`$C_{\rm str}:=(2\delta_0/\pi+\frac14)\max\{1,3/(2\delta_0)\}$ will do`". -/
def Cstr (δ₀ : ℝ) : ℝ :=
  (2 * δ₀ / π + 1 / 4) * max 1 (3 / (2 * δ₀))

end Defs

/-! ## Proof devices for the geometry (phase (b); not statements of the paper)

`|u|_P` is `P`-periodic and below `ε` exactly when some translate `u + mP` is; `δ_x > 0`; the two sides of
`n_y = ⌈2δ_x/κ⌉`; `κN_φ = n_xδ_x`; `κ ≤ 2δ₀/3`. -/

section GeometryDevices

variable {δ₀ : ℝ} {T : Torus}

theorem pdist_add_int_mul (P u : ℝ) (k : ℤ) : pdist P (u + k * P) = pdist P u := by
  unfold pdist
  rw [← QuotientAddGroup.norm_mk, ← QuotientAddGroup.norm_mk]
  congr 1
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  exact ⟨-k, by rw [zsmul_eq_mul]; push_cast; ring⟩

theorem pdist_lt_iff (P u ε : ℝ) : pdist P u < ε ↔ ∃ m : ℤ, |u + m * P| < ε := by
  unfold pdist
  rw [Metric.infDist_lt_iff ⟨0, AddSubgroup.zero_mem _⟩]
  constructor
  · rintro ⟨y, hy, hd⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff] at hy
    obtain ⟨k, rfl⟩ := hy
    refine ⟨-k, ?_⟩
    rw [Real.dist_eq, zsmul_eq_mul] at hd
    have e : u + ((-k : ℤ) : ℝ) * P = u - (k : ℝ) * P := by push_cast; ring
    rw [e]
    exact hd
  · rintro ⟨m, hm⟩
    refine ⟨-(m : ℝ) * P, ?_, ?_⟩
    · rw [SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff]
      exact ⟨-m, by rw [zsmul_eq_mul]; push_cast; ring⟩
    · have e : u - -(m : ℝ) * P = u + (m : ℝ) * P := by ring
      rw [Real.dist_eq, e]
      exact hm

open Classical in
theorem mem_strip {I : Set ℝ} {s : Slot δ₀ T} : s ∈ strip δ₀ T I ↔ xs δ₀ T s ∈ I :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))

theorem mem_col {j : ℤ} {s : Slot δ₀ T} : s ∈ col δ₀ T j ↔ pdist T.Lx (xs δ₀ T s - T.κ * j) < δx δ₀ T :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))

theorem mem_circImage {L : ℝ} {J : Set ℝ} {x : ℝ} : x ∈ circImage L J ↔ ∃ m : ℤ, x + m * L ∈ J :=
  Iff.rfl

theorem pdist_le_abs (P v : ℝ) (k : ℤ) : pdist P v ≤ |v + k * P| := by
  unfold pdist
  have hmem : (-(k : ℝ) * P) ∈ (AddSubgroup.zmultiples P : Set ℝ) := by
    rw [SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff]
    exact ⟨-k, by rw [zsmul_eq_mul]; push_cast; ring⟩
  calc Metric.infDist v (AddSubgroup.zmultiples P : Set ℝ) ≤ dist v (-(k : ℝ) * P) :=
        Metric.infDist_le_dist_of_mem hmem
    _ = |v + k * P| := by
        rw [Real.dist_eq]
        congr 1
        ring

theorem pdist_le_slotDist (s s' : Slot δ₀ T) :
    pdist T.Lx (xs δ₀ T s - xs δ₀ T s') ≤ slotDist δ₀ T s s' := by
  unfold slotDist flatDist xs
  have h0 := pdist_nonneg T.Lx ((centre δ₀ T s).1 - (centre δ₀ T s').1)
  calc pdist T.Lx ((centre δ₀ T s).1 - (centre δ₀ T s').1)
      = Real.sqrt (pdist T.Lx ((centre δ₀ T s).1 - (centre δ₀ T s').1) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (pdist T.Lx ((centre δ₀ T s).1 - (centre δ₀ T s').1) ^ 2 +
          pdist T.Ly ((centre δ₀ T s).2 - (centre δ₀ T s').2) ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

theorem slotDist_same_row (s s' : Slot δ₀ T) (h : s.2 = s'.2) :
    slotDist δ₀ T s s' = pdist T.Lx (xs δ₀ T s - xs δ₀ T s') := by
  unfold slotDist flatDist xs
  have e : (centre δ₀ T s).2 = (centre δ₀ T s').2 := by simp only [centre, h]
  rw [e, sub_self, pdist_zero, zero_pow two_ne_zero, add_zero, Real.sqrt_sq (pdist_nonneg _ _)]

theorem exists_abs_le_of_pdist_le (P u r : ℝ) (h : pdist P u ≤ r) : ∃ m : ℤ, |u + m * P| ≤ r := by
  refine ⟨-round (P⁻¹ * u), ?_⟩
  unfold pdist at h
  rw [HRTorus.SlotFrame.Analysis.infDist_zmultiples_eq] at h
  have e : u + ((-round (P⁻¹ * u) : ℤ) : ℝ) * P = u - (round (P⁻¹ * u) : ℝ) * P := by
    push_cast
    ring
  rw [e]
  exact h

theorem pdist_le_flatDist_fst (T : Torus) (p q : ℝ × ℝ) : pdist T.Lx (p.1 - q.1) ≤ flatDist T p q := by
  unfold flatDist
  calc pdist T.Lx (p.1 - q.1) = Real.sqrt (pdist T.Lx (p.1 - q.1) ^ 2) := (Real.sqrt_sq (pdist_nonneg _ _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

theorem pdist_le_flatDist_snd (T : Torus) (p q : ℝ × ℝ) : pdist T.Ly (p.2 - q.2) ≤ flatDist T p q := by
  unfold flatDist
  calc pdist T.Ly (p.2 - q.2) = Real.sqrt (pdist T.Ly (p.2 - q.2) ^ 2) := (Real.sqrt_sq (pdist_nonneg _ _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))

open Classical in
/-- The lifting count: of the `n` points `iδ` (`i < n`) on the circle of length `P = nδ`, at most `(β − α)/δ + 1`
have a translate `iδ + mP` in `[α, β]` (the lifts `i + mn` are distinct integers in `[α/δ, β/δ]`). -/
theorem card_lift_le {n : ℕ} (_hn : 0 < n) {δ P : ℝ} (hδ : 0 < δ) (hP : P = n * δ) (α β : ℝ) (hαβ : α ≤ β) :
    (((Finset.univ : Finset (Fin n)).filter fun i : Fin n =>
        ∃ m : ℤ, (((i : ℕ) : ℤ) : ℝ) * δ + m * P ∈ Set.Icc α β).card : ℝ) ≤ (β - α) / δ + 1 := by
  set A := (Finset.univ : Finset (Fin n)).filter fun i : Fin n =>
    ∃ m : ℤ, (((i : ℕ) : ℤ) : ℝ) * δ + m * P ∈ Set.Icc α β with hA
  have hex : ∀ i ∈ A, ∃ m : ℤ, (((i : ℕ) : ℤ) : ℝ) * δ + m * P ∈ Set.Icc α β := by
    intro i hi
    rw [hA, Finset.mem_filter] at hi
    exact hi.2
  choose! m hm using hex
  let g : Fin n → ℤ := fun i => ((i : ℕ) : ℤ) + m i * (n : ℤ)
  have hmaps : ∀ i ∈ A, g i ∈ Finset.Icc ⌈α / δ⌉ ⌊β / δ⌋ := by
    intro i hi
    have h1 := hm i hi
    have e : (((i : ℕ) : ℤ) : ℝ) * δ + (m i : ℝ) * P = (g i : ℝ) * δ := by
      simp only [g]
      rw [hP]
      push_cast
      ring
    rw [e, Set.mem_Icc] at h1
    rw [Finset.mem_Icc]
    constructor
    · apply Int.ceil_le.mpr
      rw [div_le_iff₀ hδ]
      exact h1.1
    · apply Int.le_floor.mpr
      rw [le_div_iff₀ hδ]
      exact h1.2
  have hinj : Set.InjOn g A := by
    intro i _ i' _ hgi
    simp only [g] at hgi
    have hdvd : (n : ℤ) ∣ ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) := ⟨m i' - m i, by linear_combination hgi⟩
    have h1 := i.isLt
    have h2 := i'.isLt
    have habs : |((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ)| < (n : ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
    exact Fin.ext (by omega)
  have hcard := Finset.card_le_card_of_injOn g hmaps hinj
  rw [Int.card_Icc] at hcard
  have hc1 : α / δ ≤ (⌈α / δ⌉ : ℝ) := Int.le_ceil _
  have hf1 : (⌊β / δ⌋ : ℝ) ≤ β / δ := Int.floor_le _
  have e : β / δ - α / δ = (β - α) / δ := by ring
  have hpos : 0 ≤ (β - α) / δ := div_nonneg (by linarith) hδ.le
  have key : (((⌊β / δ⌋ + 1 - ⌈α / δ⌉).toNat : ℕ) : ℝ) ≤ (β - α) / δ + 1 := by
    rcases le_or_gt 0 (⌊β / δ⌋ + 1 - ⌈α / δ⌉) with h | h
    · have e2 : (((⌊β / δ⌋ + 1 - ⌈α / δ⌉).toNat : ℕ) : ℝ) = ((⌊β / δ⌋ + 1 - ⌈α / δ⌉ : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg h
      rw [e2]
      push_cast
      linarith
    · rw [Int.toNat_of_nonpos h.le]
      push_cast
      linarith
  calc (A.card : ℝ) ≤ (((⌊β / δ⌋ + 1 - ⌈α / δ⌉).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (β - α) / δ + 1 := key

theorem δx_pos (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) : 0 < δx δ₀ T :=
  lt_of_lt_of_le (by unfold δminus; positivity) (consistency_ii hδ₀ hT).2.1

theorem ny_ge (δ₀ : ℝ) (T : Torus) : 2 * δx δ₀ T / T.κ ≤ (ny δ₀ T : ℝ) := by
  have h3 : ((ny δ₀ T : ℕ) : ℝ) = ((⌈2 * δx δ₀ T / T.κ⌉ : ℤ) : ℝ) := by exact_mod_cast ny_spec δ₀ T
  rw [h3]
  exact Int.le_ceil _

theorem ny_lt (δ₀ : ℝ) (T : Torus) : (ny δ₀ T : ℝ) < 2 * δx δ₀ T / T.κ + 1 := by
  have h3 : ((ny δ₀ T : ℕ) : ℝ) = ((⌈2 * δx δ₀ T / T.κ⌉ : ℤ) : ℝ) := by exact_mod_cast ny_spec δ₀ T
  rw [h3]
  exact Int.ceil_lt_add_one _

theorem κ_mul_Nφ (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) :
    T.κ * (T.Nφ : ℝ) = (nx δ₀ T : ℝ) * δx δ₀ T := by
  rw [← T.Lx_eq]
  exact Lx_eq_nx hδ₀ hT

theorem κ_le (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) : T.κ ≤ 2 / 3 * δ₀ := by
  have hLy3 : 3 * π / δ₀ ≤ T.Ly := le_trans (le_max_right _ _) hT.1
  rw [div_le_iff₀ hδ₀] at hLy3
  unfold Torus.κ
  rw [div_le_iff₀ T.Ly_pos]
  nlinarith [Real.pi_pos]

end GeometryDevices

/-! ## Lemma 3.2(iii), the clauses Lemma 3.6 uses (statements) -/

section Consistency

variable {δ₀ : ℝ} {T : Torus}

/-- **Lemma 3.2(iii)**: "`$I_a$ contains fewer than $2\delta_x/\kappa+1$ integers`". -/
theorem card_Ia_lt (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (a : ℤ) :
    ((Ia δ₀ T a).card : ℝ) < 2 * δx δ₀ T / T.κ + 1 := by
  have hκ := T.κ_pos
  have hδ := δx_pos hδ₀ hT
  set c := (xa δ₀ T a - δx δ₀ T) / T.κ with hc
  set ℓ := 2 * δx δ₀ T / T.κ with hℓ
  have hsub : Ia δ₀ T a ⊆ Finset.Icc (⌊c⌋ + 1) (⌈c + ℓ⌉ - 1) := by
    intro j hj
    rw [mem_Ia, abs_lt] at hj
    rw [Finset.mem_Icc]
    have h1 : c < (j : ℝ) := by
      rw [hc, div_lt_iff₀ hκ]
      linarith [hj.1]
    have h2 : (j : ℝ) < c + ℓ := by
      rw [hc, hℓ, ← add_div, lt_div_iff₀ hκ]
      linarith [hj.2]
    have h1' := Int.floor_lt.mpr h1
    have h2' := Int.lt_ceil.mpr h2
    constructor <;> omega
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hceil : (⌈c + ℓ⌉ : ℝ) < c + ℓ + 1 := Int.ceil_lt_add_one _
  have hfloor : c - 1 < (⌊c⌋ : ℝ) := Int.sub_one_lt_floor _
  have hℓ0 : 0 < ℓ := div_pos (by linarith) hκ
  have key : (((⌈c + ℓ⌉ - 1 + 1 - (⌊c⌋ + 1)).toNat : ℕ) : ℝ) < ℓ + 1 := by
    rcases le_or_gt 0 (⌈c + ℓ⌉ - 1 + 1 - (⌊c⌋ + 1)) with h | h
    · have e : (((⌈c + ℓ⌉ - 1 + 1 - (⌊c⌋ + 1)).toNat : ℕ) : ℝ) = ((⌈c + ℓ⌉ - 1 + 1 - (⌊c⌋ + 1) : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg h
      rw [e]
      push_cast
      linarith
    · rw [Int.toNat_of_nonpos h.le]
      push_cast
      linarith
  calc ((Ia δ₀ T a).card : ℝ) ≤ (((⌈c + ℓ⌉ - 1 + 1 - (⌊c⌋ + 1)).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
    _ < ℓ + 1 := key

/-- **Lemma 3.2(iii)**: "`and these lie in distinct classes of $\Z_{\Nphi}$`". -/
theorem eq_of_mem_Ia_of_intCast_eq (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (a : ℤ) {j j' : ℤ}
    (hj : j ∈ Ia δ₀ T a) (hj' : j' ∈ Ia δ₀ T a) (h : (j : ZMod T.Nφ) = (j' : ZMod T.Nφ)) : j = j' := by
  have hκ := T.κ_pos
  have hδ := δx_pos hδ₀ hT
  have h4 := (consistency_ii hδ₀ hT).1
  rw [mem_Ia, abs_lt] at hj hj'
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨q, hq⟩ := h
  have hLx := κ_mul_Nφ hδ₀ hT
  have h4R : (4 : ℝ) ≤ nx δ₀ T := by exact_mod_cast h4
  have hdiff : |T.κ * ((j' - j : ℤ) : ℝ)| < 2 * δx δ₀ T := by
    push_cast
    rw [abs_lt]
    constructor <;> linarith [hj.1, hj.2, hj'.1, hj'.2]
  rw [hq] at hdiff
  push_cast at hdiff
  by_contra hne
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hne
    omega
  have hq1 : (1 : ℝ) ≤ |(q : ℝ)| := by
    have : 1 ≤ |q| := Int.one_le_abs hq0
    exact_mod_cast this
  have hNφ : (0 : ℝ) < (T.Nφ : ℝ) := by exact_mod_cast T.Nφ_pos
  rw [show T.κ * ((T.Nφ : ℝ) * (q : ℝ)) = (T.κ * T.Nφ) * q by ring, abs_mul,
    abs_of_pos (mul_pos hκ hNφ), hLx] at hdiff
  have hP : (4 : ℝ) ≤ (nx δ₀ T : ℝ) * |(q : ℝ)| := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hP hδ.le]

/-- **Lemma 3.2(iii)**: "`Moreover $w_{a+\nx}(j+\Nphi)=w_a(j)$`". -/
theorem wa_add_nx_add_Nφ (η : ℝ → ℝ) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (a j : ℤ) :
    wa η δ₀ T (a + (nx δ₀ T : ℤ)) (j + (T.Nφ : ℤ)) = wa η δ₀ T a j := by
  unfold wa
  congr 1
  have hδ := δx_pos hδ₀ hT
  have e : T.κ * (T.Nφ : ℝ) / δx δ₀ T = (nx δ₀ T : ℝ) := by
    rw [κ_mul_Nφ hδ₀ hT, mul_div_cancel_right₀ _ hδ.ne']
  push_cast
  rw [mul_add, add_div, e]
  ring

end Consistency

/-! ## Proposition 3.4 (statements) -/

section Geometry

variable {δ₀ : ℝ} {T : Torus}

/-- **Proposition 3.4(i)**: "`$\pi/(\delta_x+\kappa/2)<\delta_y\le\pi/\delta_x$`". -/
theorem geometry_i_δy (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) :
    π / (δx δ₀ T + T.κ / 2) < δy δ₀ T ∧ δy δ₀ T ≤ π / δx δ₀ T := by
  have hκ := T.κ_pos
  have hδ := δx_pos hδ₀ hT
  have hny := two_le_ny hδ₀ hT
  have hnyR : (0 : ℝ) < (ny δ₀ T : ℝ) := by exact_mod_cast (by omega : 0 < ny δ₀ T)
  have hc1 := ny_ge δ₀ T
  rw [div_le_iff₀ hκ] at hc1
  have hc2 : (ny δ₀ T : ℝ) * T.κ < 2 * δx δ₀ T + T.κ := by
    have := (lt_div_iff₀ hκ).mp (show (ny δ₀ T : ℝ) - 1 < 2 * δx δ₀ T / T.κ by linarith [ny_lt δ₀ T])
    linarith
  have hLy := Torus.κ_mul_Ly T
  have e : π * (ny δ₀ T : ℝ) = T.Ly * ((ny δ₀ T : ℝ) * T.κ) / 2 := by
    linear_combination (-(ny δ₀ T : ℝ) / 2) * hLy
  unfold δy
  constructor
  · rw [div_lt_div_iff₀ (by positivity) hnyR, e]
    nlinarith [mul_lt_mul_of_pos_left hc2 T.Ly_pos]
  · rw [div_le_div_iff₀ hnyR hδ, e]
    nlinarith [mul_le_mul_of_nonneg_left hc1 T.Ly_pos.le]

/-- **Proposition 3.4(i)**: "`in particular $\delta_y>\pi/(3\delta_0)$`". -/
theorem geometry_i_δy_gt (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) : π / (3 * δ₀) < δy δ₀ T := by
  have hκ := T.κ_pos
  have hδ := δx_pos hδ₀ hT
  have hδp := (consistency_ii hδ₀ hT).2.2.1
  unfold δplus at hδp
  have hκle := κ_le hδ₀ hT
  refine lt_of_le_of_lt ?_ (geometry_i_δy hδ₀ hT).1
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)

/-- **Proposition 3.4(i)**: "`\abs{\Slots}=\nx\ny`". -/
theorem card_slot (δ₀ : ℝ) (T : Torus) : Fintype.card (Slot δ₀ T) = nx δ₀ T * ny δ₀ T := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- **Proposition 3.4(i)**: "`The number of slots satisfies $2\Nphi\le\abs{\Slots}=\nx\ny\le(2+\kappa/\delta_x)\Nphi$.`" -/
theorem geometry_i_card (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) :
    2 * T.Nφ ≤ nx δ₀ T * ny δ₀ T ∧
      ((nx δ₀ T * ny δ₀ T : ℕ) : ℝ) ≤ (2 + T.κ / δx δ₀ T) * (T.Nφ : ℝ) := by
  have hκ := T.κ_pos
  have hδ := δx_pos hδ₀ hT
  have h4 := (consistency_ii hδ₀ hT).1
  have hnxpos : (0 : ℝ) < (nx δ₀ T : ℝ) := by exact_mod_cast (by omega : 0 < nx δ₀ T)
  have hLx := κ_mul_Nφ hδ₀ hT
  have hc1 := ny_ge δ₀ T
  rw [div_le_iff₀ hκ] at hc1
  have hc2 : (ny δ₀ T : ℝ) * T.κ < 2 * δx δ₀ T + T.κ := by
    have := (lt_div_iff₀ hκ).mp (show (ny δ₀ T : ℝ) - 1 < 2 * δx δ₀ T / T.κ by linarith [ny_lt δ₀ T])
    linarith
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hc1 hnxpos.le
    have : ((2 * T.Nφ : ℕ) : ℝ) ≤ ((nx δ₀ T * ny δ₀ T : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  · have e3 : (2 + T.κ / δx δ₀ T) * (T.Nφ : ℝ) = 2 * T.Nφ + nx δ₀ T := by
      rw [add_mul, div_mul_eq_mul_div, hLx, mul_div_cancel_right₀ _ hδ.ne']
    rw [e3]
    push_cast
    have h2 := mul_lt_mul_of_pos_left hc2 hnxpos
    nlinarith

/-- **Proposition 3.4(ii)** (ball count): "`For all $R\in\Tor_N$ and $r\ge0$, $\#\Ball rR\le(1+2r/\delta_x)(1+2r/\delta_y)\le\Cvol(1+r)^2$`". -/
theorem card_slotBall_le (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (R : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ((slotBall δ₀ T R r).card : ℝ) ≤ (1 + 2 * r / δx δ₀ T) * (1 + 2 * r / δy δ₀ T) ∧
      (1 + 2 * r / δx δ₀ T) * (1 + 2 * r / δy δ₀ T) ≤ Cvol δ₀ * (1 + r) ^ 2 := by
  classical
  have hδ := δx_pos hδ₀ hT
  have hδy : 0 < δy δ₀ T := lt_trans (by positivity) (geometry_i_δy_gt hδ₀ hT)
  have h4 := (consistency_ii hδ₀ hT).1
  have hny2 := two_le_ny hδ₀ hT
  set Ax := (Finset.univ : Finset (Fin (nx δ₀ T))).filter fun i : Fin (nx δ₀ T) =>
    ∃ m : ℤ, (((i : ℕ) : ℤ) : ℝ) * δx δ₀ T + m * T.Lx ∈ Set.Icc (R.1 - r) (R.1 + r) with hAx
  set Ay := (Finset.univ : Finset (Fin (ny δ₀ T))).filter fun i : Fin (ny δ₀ T) =>
    ∃ m : ℤ, (((i : ℕ) : ℤ) : ℝ) * δy δ₀ T + m * T.Ly ∈ Set.Icc (R.2 - r) (R.2 + r) with hAy
  have hsub : slotBall δ₀ T R r ⊆ Ax ×ˢ Ay := by
    intro s hs
    simp only [slotBall, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [Finset.mem_product, hAx, hAy, Finset.mem_filter, Finset.mem_filter]
    obtain ⟨m1, hm1⟩ := exists_abs_le_of_pdist_le _ _ _ ((pdist_le_flatDist_fst T _ _).trans hs)
    obtain ⟨m2, hm2⟩ := exists_abs_le_of_pdist_le _ _ _ ((pdist_le_flatDist_snd T _ _).trans hs)
    rw [abs_le] at hm1 hm2
    simp only [centre, xa, yl] at hm1 hm2
    exact ⟨⟨Finset.mem_univ _, m1, by linarith [hm1.1], by linarith [hm1.2]⟩,
      ⟨Finset.mem_univ _, m2, by linarith [hm2.1], by linarith [hm2.2]⟩⟩
  have hAxc := card_lift_le (by omega : 0 < nx δ₀ T) hδ (Lx_eq_nx hδ₀ hT) (R.1 - r) (R.1 + r) (by linarith)
  have hAyc := card_lift_le (by omega : 0 < ny δ₀ T) hδy (Ly_eq_ny hδ₀ hT) (R.2 - r) (R.2 + r) (by linarith)
  have e1 : (R.1 + r - (R.1 - r)) / δx δ₀ T + 1 = 1 + 2 * r / δx δ₀ T := by ring
  have e2 : (R.2 + r - (R.2 - r)) / δy δ₀ T + 1 = 1 + 2 * r / δy δ₀ T := by ring
  rw [e1] at hAxc
  rw [e2] at hAyc
  have hcardB : ((slotBall δ₀ T R r).card : ℝ) ≤ (Ax.card : ℝ) * (Ay.card : ℝ) := by
    have := Finset.card_le_card hsub
    rw [Finset.card_product] at this
    exact_mod_cast this
  have hnnx : 0 ≤ 1 + 2 * r / δx δ₀ T := by
    have := div_nonneg (mul_nonneg two_pos.le hr) hδ.le
    linarith
  have hnny : 0 ≤ 1 + 2 * r / δy δ₀ T := by
    have := div_nonneg (mul_nonneg two_pos.le hr) hδy.le
    linarith
  constructor
  · calc ((slotBall δ₀ T R r).card : ℝ) ≤ (Ax.card : ℝ) * (Ay.card : ℝ) := hcardB
      _ ≤ (1 + 2 * r / δx δ₀ T) * (1 + 2 * r / δy δ₀ T) := mul_le_mul hAxc hAyc (Nat.cast_nonneg _) hnnx
  · have hδm := (consistency_ii hδ₀ hT).2.1
    unfold δminus at hδm
    have hπ := Real.pi_pos
    have hδy3 := geometry_i_δy_gt hδ₀ hT
    rw [div_lt_iff₀ (by positivity)] at hδy3
    have hx1 : 1 + 2 * r / δx δ₀ T ≤ max 1 (3 / δ₀) * (1 + r) := by
      have h1 : 2 / δx δ₀ T ≤ 3 / δ₀ := by
        rw [div_le_div_iff₀ hδ hδ₀]
        linarith
      have h2 : 2 * r / δx δ₀ T = 2 / δx δ₀ T * r := by ring
      rw [h2]
      nlinarith [mul_le_mul_of_nonneg_right h1 hr, mul_le_mul_of_nonneg_right (le_max_right 1 (3 / δ₀)) hr,
        le_max_left 1 (3 / δ₀)]
    have hy1 : 1 + 2 * r / δy δ₀ T ≤ max 1 (6 * δ₀ / π) * (1 + r) := by
      have h1 : 2 / δy δ₀ T ≤ 6 * δ₀ / π := by
        rw [div_le_div_iff₀ hδy hπ]
        linarith
      have h2 : 2 * r / δy δ₀ T = 2 / δy δ₀ T * r := by ring
      rw [h2]
      nlinarith [mul_le_mul_of_nonneg_right h1 hr, mul_le_mul_of_nonneg_right (le_max_right 1 (6 * δ₀ / π)) hr,
        le_max_left 1 (6 * δ₀ / π)]
    calc (1 + 2 * r / δx δ₀ T) * (1 + 2 * r / δy δ₀ T)
        ≤ (max 1 (3 / δ₀) * (1 + r)) * (max 1 (6 * δ₀ / π) * (1 + r)) :=
          mul_le_mul hx1 hy1 hnny (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (by linarith))
      _ = Cvol δ₀ * (1 + r) ^ 2 := by
          unfold Cvol
          ring

/-- **Proposition 3.4(iii)** (strip count): "`For every interval $I\subset\R/L_x\Z$ of length $\abs I$, the strip $\Str(I):=\{s\in\Slots:x_s\in I\}$ has at most $\ny(\abs I/\delta_x+1)\le C_{\rm str}L_y(1+\abs I)$ slots`"
— `I` the image of an interval `J ⊆ [a, b]` of `ℝ`, `|I| = b − a`. -/
theorem card_strip_le (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) {a b : ℝ} (hab : a ≤ b) {J : Set ℝ}
    (hJ : J ⊆ Set.Icc a b) :
    ((strip δ₀ T (circImage T.Lx J)).card : ℝ) ≤ (ny δ₀ T : ℝ) * ((b - a) / δx δ₀ T + 1) ∧
      (ny δ₀ T : ℝ) * ((b - a) / δx δ₀ T + 1) ≤ Cstr δ₀ * T.Ly * (1 + (b - a)) := by
  classical
  have hδ := δx_pos hδ₀ hT
  have h4 := (consistency_ii hδ₀ hT).1
  set A := (Finset.univ : Finset (Fin (nx δ₀ T))).filter fun i : Fin (nx δ₀ T) =>
    ∃ m : ℤ, (((i : ℕ) : ℤ) : ℝ) * δx δ₀ T + m * T.Lx ∈ Set.Icc a b with hA
  have hsub : strip δ₀ T (circImage T.Lx J) ⊆ A ×ˢ Finset.univ := by
    intro s hs
    rw [mem_strip, mem_circImage] at hs
    obtain ⟨m, hm⟩ := hs
    rw [Finset.mem_product, hA, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, m, hJ hm⟩, Finset.mem_univ _⟩
  have hAc := card_lift_le (by omega : 0 < nx δ₀ T) hδ (Lx_eq_nx hδ₀ hT) a b hab
  have hℓ : 0 ≤ b - a := by linarith
  have hnn2 : 0 ≤ (b - a) / δx δ₀ T + 1 := by
    have := div_nonneg hℓ hδ.le
    linarith
  constructor
  · calc ((strip δ₀ T (circImage T.Lx J)).card : ℝ)
        ≤ ((A ×ˢ (Finset.univ : Finset (Fin (ny δ₀ T)))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = (A.card : ℝ) * (ny δ₀ T : ℝ) := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
          push_cast
          ring
      _ ≤ ((b - a) / δx δ₀ T + 1) * (ny δ₀ T : ℝ) := mul_le_mul_of_nonneg_right hAc (Nat.cast_nonneg _)
      _ = (ny δ₀ T : ℝ) * ((b - a) / δx δ₀ T + 1) := by ring
  · have hκ := T.κ_pos
    have hπ := Real.pi_pos
    have hLy := T.Ly_pos
    have hLy0 : T.Ly ≠ 0 := hLy.ne'
    have hπ0 : π ≠ 0 := hπ.ne'
    have hLy4 : 4 ≤ T.Ly := le_trans (le_max_left _ _) hT.1
    have hδp := (consistency_ii hδ₀ hT).2.2.1
    have hδm := (consistency_ii hδ₀ hT).2.1
    unfold δplus at hδp
    unfold δminus at hδm
    have e : 2 * δx δ₀ T / T.κ = δx δ₀ T * T.Ly / π := by
      unfold Torus.κ
      field_simp
    have hny1 : (ny δ₀ T : ℝ) ≤ (2 * δ₀ / π + 1 / 4) * T.Ly := by
      have h1 := (ny_lt δ₀ T).le
      rw [e] at h1
      have h2 : δx δ₀ T * T.Ly / π ≤ 2 * δ₀ * T.Ly / π :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hδp hLy.le) hπ.le
      have h3 : 2 * δ₀ * T.Ly / π = 2 * δ₀ / π * T.Ly := by ring
      linarith
    have hinv : 1 / δx δ₀ T ≤ 3 / (2 * δ₀) := by
      rw [div_le_div_iff₀ hδ (by positivity)]
      linarith
    have hfac2 : (b - a) / δx δ₀ T + 1 ≤ max 1 (3 / (2 * δ₀)) * (1 + (b - a)) := by
      have e2 : (b - a) / δx δ₀ T = 1 / δx δ₀ T * (b - a) := by ring
      rw [e2]
      nlinarith [mul_le_mul_of_nonneg_right hinv hℓ, mul_le_mul_of_nonneg_right (le_max_right 1 (3 / (2 * δ₀))) hℓ,
        le_max_left 1 (3 / (2 * δ₀))]
    calc (ny δ₀ T : ℝ) * ((b - a) / δx δ₀ T + 1)
        ≤ ((2 * δ₀ / π + 1 / 4) * T.Ly) * (max 1 (3 / (2 * δ₀)) * (1 + (b - a))) :=
          mul_le_mul hny1 hfac2 hnn2 (mul_nonneg (by positivity) hLy.le)
      _ = Cstr δ₀ * T.Ly * (1 + (b - a)) := by
          unfold Cstr
          ring

/-- The slot ball is the complement of `SlotFrame.ballCompl` (Lemma 3.5(iii)'s `𝒮 ∖ Ball(r, R)`). -/
theorem slotBall_eq_compl (δ₀ : ℝ) (T : Torus) (R : ℝ × ℝ) (r : ℝ) :
    slotBall δ₀ T R r = (ballCompl δ₀ T R r)ᶜ := by
  ext s
  simp only [slotBall, ballCompl, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]

end Geometry

/-! ## Intervals of `ℝ/L_xℤ` and strips (statements) -/

section Intervals

variable {δ₀ : ℝ} {T : Torus}

/-- `circImage L J` is `L`-periodic: it is a subset of `ℝ/Lℤ`. -/
theorem add_mem_circImage_iff (L : ℝ) (J : Set ℝ) (x : ℝ) : x + L ∈ circImage L J ↔ x ∈ circImage L J := by
  rw [mem_circImage, mem_circImage]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    have e : x + ((m + 1 : ℤ) : ℝ) * L = x + L + (m : ℝ) * L := by push_cast; ring
    rw [e]
    exact hm
  · rintro ⟨m, hm⟩
    refine ⟨m - 1, ?_⟩
    have e : x + L + ((m - 1 : ℤ) : ℝ) * L = x + (m : ℝ) * L := by push_cast; ring
    rw [e]
    exact hm

/-- **Definition 3.9**: "`and $I_\rho$ denotes the closed $\rho$-neighbourhood of $I$`" — for the image of an open
interval `(a, b)`, `I_ρ` is the image of the widened closed interval `[a − ρ, b + ρ]`. -/
theorem cthickening_circImage_Ioo {L : ℝ} (hL : 0 < L) {a b : ℝ} (hab : a < b) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Metric.cthickening ρ (circImage L (Set.Ioo a b)) = circImage L (Set.Icc (a - ρ) (b + ρ)) := by
  ext x
  rw [Metric.cthickening_eq_iInter_thickening hρ, Set.mem_iInter₂, mem_circImage]
  simp only [Metric.mem_thickening_iff, Set.mem_Icc]
  constructor
  · intro hx
    set c := (a + b) / 2 with hc
    set m₀ : ℤ := -round ((x - c) / L) with hm₀
    have hmin : ∀ m : ℤ, |x + m₀ * L - c| ≤ |x + m * L - c| := by
      intro m
      have h1 := round_le ((x - c) / L) (-m)
      have e1 : x + (m₀ : ℝ) * L - c = L * ((x - c) / L - (round ((x - c) / L) : ℝ)) := by
        rw [hm₀]
        push_cast
        field_simp
        ring
      have e2 : x + (m : ℝ) * L - c = L * ((x - c) / L - ((-m : ℤ) : ℝ)) := by
        push_cast
        field_simp
        ring
      rw [e1, e2, abs_mul, abs_mul, abs_of_pos hL]
      exact mul_le_mul_of_nonneg_left h1 hL.le
    have hle : |x + m₀ * L - c| ≤ (b - a) / 2 + ρ := by
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨y, hy, hxy⟩ := hx (ρ + ε) (by linarith)
      rw [mem_circImage] at hy
      obtain ⟨m, hm⟩ := hy
      have h2 : |x + m * L - c| < (b - a) / 2 + (ρ + ε) := by
        rw [Real.dist_eq] at hxy
        rw [abs_lt] at hxy ⊢
        rw [Set.mem_Ioo] at hm
        constructor <;> linarith [hm.1, hm.2, hxy.1, hxy.2]
      linarith [hmin m]
    rw [abs_le] at hle
    exact ⟨m₀, by linarith [hle.1], by linarith [hle.2]⟩
  · rintro ⟨m, hm1, hm2⟩ ε hε
    have hη0 : 0 < min (ε - ρ) (b - a) := lt_min (by linarith) (by linarith)
    have hη1 := min_le_left (ε - ρ) (b - a)
    have hη2 := min_le_right (ε - ρ) (b - a)
    obtain ⟨y', hy', hty'⟩ : ∃ y' ∈ Set.Ioo a b, |x + m * L - y'| < ε := by
      rcases le_or_gt (x + m * L) a with h1 | h1
      · refine ⟨a + min (ε - ρ) (b - a) / 2, ⟨by linarith, by linarith⟩, ?_⟩
        rw [abs_lt]
        constructor <;> linarith
      · rcases lt_or_ge (x + m * L) b with h2 | h2
        · exact ⟨x + m * L, ⟨h1, h2⟩, by rw [sub_self, abs_zero]; linarith⟩
        · refine ⟨b - min (ε - ρ) (b - a) / 2, ⟨by linarith, by linarith⟩, ?_⟩
          rw [abs_lt]
          constructor <;> linarith
    refine ⟨y' - m * L, ?_, ?_⟩
    · rw [mem_circImage]
      refine ⟨m, ?_⟩
      rw [sub_add_cancel]
      exact hy'
    · rw [Real.dist_eq]
      have e : x - (y' - m * L) = x + m * L - y' := by ring
      rw [e]
      exact hty'

/-- Strips are monotone in the set. -/
theorem strip_mono {I I' : Set ℝ} (h : I ⊆ I') : strip δ₀ T I ⊆ strip δ₀ T I' := by
  intro s hs
  simp only [strip, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact h hs

end Intervals

/-! ## Lemma 3.6 (statements) -/

section Columns

variable {η : ℝ → ℝ} {δ₀ : ℝ} {T : Torus}

/-- **Lemma 3.6**: "`For every admissible torus, $j\in\Z$ and $s=(a,\ell)$: $\ip{\psi_{[j]}}{z_s}=\ny^{-1/2}w_a(j')e^{-2\pi\iu j'\ell/\ny}$ if some $j'\in I_a$ lies in the class of $j$ (it is then unique)`"
(uniqueness: `eq_of_mem_Ia_of_intCast_eq`; `a`, `ℓ` the representatives of `s`). -/
theorem inner_orb_frameVec (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (j : ℤ) (s : Slot δ₀ T) {j' : ℤ}
    (hj' : j' ∈ Ia δ₀ T ((s.1 : ℕ) : ℤ)) (hcl : (j' : ZMod T.Nφ) = (j : ZMod T.Nφ)) :
    ⟪orb T (j : ZMod T.Nφ), frameVec η δ₀ T s⟫_ℂ =
      (((ny δ₀ T : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((wa η δ₀ T ((s.1 : ℕ) : ℤ) j' : ℝ) : ℂ) *
        Complex.exp (-(2 * (π : ℂ) * I * (j' : ℂ) * (((s.2 : ℕ) : ℤ) : ℂ) / ((ny δ₀ T : ℕ) : ℂ))) := by
  rw [orb, EuclideanSpace.inner_single_left, map_one, one_mul, frameVec_apply]
  have hfilt : (Ia δ₀ T ((s.1 : ℕ) : ℤ)).filter (fun j'' : ℤ => (j'' : ZMod T.Nφ) = (j : ZMod T.Nφ)) = {j'} := by
    ext j''
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact eq_of_mem_Ia_of_intCast_eq hδ₀ hT _ h1 hj' (h2.trans hcl.symm)
    · rintro rfl
      exact ⟨hj', hcl⟩
  rw [hfilt, Finset.sum_singleton]
  ring

/-- **Lemma 3.6**: "`and $\ip{\psi_{[j]}}{z_s}=0$ otherwise`". -/
theorem inner_orb_frameVec_eq_zero (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (j : ℤ) (s : Slot δ₀ T)
    (h : ∀ j' ∈ Ia δ₀ T ((s.1 : ℕ) : ℤ), (j' : ZMod T.Nφ) ≠ (j : ZMod T.Nφ)) :
    ⟪orb T (j : ZMod T.Nφ), frameVec η δ₀ T s⟫_ℂ = 0 := by
  rw [orb, EuclideanSpace.inner_single_left, map_one, one_mul, frameVec_apply]
  have hfilt : (Ia δ₀ T ((s.1 : ℕ) : ℤ)).filter (fun j'' : ℤ => (j'' : ZMod T.Nφ) = (j : ZMod T.Nφ)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j'' hj''
    exact h j'' hj''
  rw [hfilt, Finset.sum_empty, mul_zero]

/-- **Lemma 3.6**: "`Consequently $\Sa\psi_{[j]}$ is supported in the \emph{column}`" `Col(j)`. -/
theorem analysis_orb_mem_col (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (j : ℤ) (s : Slot δ₀ T)
    (h : analysis η δ₀ T (orb T (j : ZMod T.Nφ)) s ≠ 0) : s ∈ col δ₀ T j := by
  rw [analysis_apply] at h
  have h' : ⟪orb T (j : ZMod T.Nφ), frameVec η δ₀ T s⟫_ℂ ≠ 0 := by
    intro h0
    apply h
    rw [← inner_conj_symm, h0, map_zero]
  by_contra hns
  apply h'
  apply inner_orb_frameVec_eq_zero hδ₀ hT j s
  intro j' hj' hcl
  apply hns
  rw [mem_Ia, abs_lt] at hj'
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcl
  obtain ⟨q, hq⟩ := hcl
  rw [mem_col, pdist_lt_iff]
  refine ⟨q, ?_⟩
  have hj : (j : ℝ) = j' + (T.Nφ : ℝ) * q := by
    have : ((j - j' : ℤ) : ℝ) = (((T.Nφ : ℤ) * q : ℤ) : ℝ) := by rw [hq]
    push_cast at this
    linarith
  have e : xs δ₀ T s - T.κ * j + (q : ℝ) * T.Lx = -(T.κ * j' - xa δ₀ T ((s.1 : ℕ) : ℤ)) := by
    rw [hj, T.Lx_eq]
    simp only [xs, centre]
    ring
  rw [e, abs_neg, abs_lt]
  exact hj'

/-- **Lemma 3.6**: "`\Col(j):=\{s\in\Slots:\abs{x_s-\kappa j}_{L_x}<\delta_x\}=\Str\bigl((\kappa j-\delta_x,\kappa j+\delta_x)\bigr),`"
— the second description, a strip of width `2δ_x`. -/
theorem col_eq_strip (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (j : ℤ) :
    col δ₀ T j = strip δ₀ T (circImage T.Lx (Set.Ioo (T.κ * j - δx δ₀ T) (T.κ * j + δx δ₀ T))) := by
  ext s
  rw [mem_col, mem_strip, mem_circImage, pdist_lt_iff]
  simp only [Set.mem_Ioo]
  apply exists_congr
  intro m
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- **Lemma 3.6**: "`a strip of width $2\delta_x$ containing the slots of at most two windows`". -/
theorem col_windows (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (j : ℤ) :
    ∃ W : Finset (Fin (nx δ₀ T)), W.card ≤ 2 ∧ col δ₀ T j = W ×ˢ Finset.univ := by
  have hδ := δx_pos hδ₀ hT
  have hLx := Lx_eq_nx hδ₀ hT
  set W : Finset (Fin (nx δ₀ T)) := Finset.univ.filter
    (fun a => pdist T.Lx (xa δ₀ T ((a : ℕ) : ℤ) - T.κ * j) < δx δ₀ T) with hW
  refine ⟨W, ?_, ?_⟩
  · set c := T.κ * j / δx δ₀ T with hc
    have hex : ∀ a ∈ W, ∃ m : ℤ, |xa δ₀ T ((a : ℕ) : ℤ) - T.κ * j + m * T.Lx| < δx δ₀ T := by
      intro a ha
      rw [hW, Finset.mem_filter] at ha
      exact (pdist_lt_iff _ _ _).mp ha.2
    choose! m hm using hex
    let g : Fin (nx δ₀ T) → ℤ := fun a => ((a : ℕ) : ℤ) + m a * (nx δ₀ T : ℤ)
    have hg : ∀ a ∈ W, |(g a : ℝ) * δx δ₀ T - T.κ * j| < δx δ₀ T := by
      intro a ha
      have e : (g a : ℝ) * δx δ₀ T - T.κ * j = xa δ₀ T ((a : ℕ) : ℤ) - T.κ * j + m a * T.Lx := by
        simp only [g, xa]
        rw [hLx]
        push_cast
        ring
      rw [e]
      exact hm a ha
    have hmaps : ∀ a ∈ W, g a ∈ Finset.Icc ⌊c⌋ (⌊c⌋ + 1) := by
      intro a ha
      have h1 := hg a ha
      rw [abs_lt] at h1
      have hlo : c - 1 < (g a : ℝ) := by
        rw [hc, sub_lt_iff_lt_add, div_lt_iff₀ hδ]
        nlinarith [h1.1]
      have hhi : (g a : ℝ) < c + 1 := by
        rw [hc, ← sub_lt_iff_lt_add, lt_div_iff₀ hδ]
        nlinarith [h1.2]
      have hf1 := Int.floor_le c
      have hf2 := Int.lt_floor_add_one c
      rw [Finset.mem_Icc]
      constructor
      · have h3 : (⌊c⌋ : ℝ) - 1 < (g a : ℝ) := by linarith
        have h4 : ⌊c⌋ - 1 < g a := by exact_mod_cast h3
        omega
      · have h3 : (g a : ℝ) < (⌊c⌋ : ℝ) + 2 := by linarith
        have h4 : g a < ⌊c⌋ + 2 := by exact_mod_cast h3
        omega
    have hinj : Set.InjOn g W := by
      intro a _ a' _ hga
      simp only [g] at hga
      have hdvd : (nx δ₀ T : ℤ) ∣ ((a : ℕ) : ℤ) - ((a' : ℕ) : ℤ) :=
        ⟨m a' - m a, by linear_combination hga⟩
      have ha1 := a.isLt
      have ha2 := a'.isLt
      have habs : |((a : ℕ) : ℤ) - ((a' : ℕ) : ℤ)| < (nx δ₀ T : ℤ) := by
        rw [abs_lt]
        constructor <;> omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
      exact Fin.ext (by omega)
    calc W.card ≤ (Finset.Icc ⌊c⌋ (⌊c⌋ + 1)).card := Finset.card_le_card_of_injOn g hmaps hinj
      _ = 2 := by
        rw [Int.card_Icc, show ⌊c⌋ + 1 + 1 - ⌊c⌋ = (2 : ℤ) by ring]
        rfl
  · ext ⟨a, l⟩
    rw [mem_col, Finset.mem_product, hW, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, and_true]
    rfl

/-- The column does not depend on the representative of the class of `j` in `ℤ_{N_φ}` (`κN_φ = L_x`). -/
theorem col_intCast_val (j : ℤ) : col δ₀ T (((j : ZMod T.Nφ).val : ℕ) : ℤ) = col δ₀ T j := by
  have : NeZero T.Nφ := ⟨T.Nφ_pos.ne'⟩
  have hv : (((j : ZMod T.Nφ).val : ℕ) : ℤ) = j - (T.Nφ : ℤ) * (j / (T.Nφ : ℤ)) := by
    rw [ZMod.val_intCast, Int.emod_def]
  ext s
  simp only [col, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hv]
  have e : xs δ₀ T s - T.κ * (((j - (T.Nφ : ℤ) * (j / (T.Nφ : ℤ)) : ℤ) : ℝ)) =
      xs δ₀ T s - T.κ * j + ((j / (T.Nφ : ℤ) : ℤ) : ℝ) * T.Lx := by
    rw [T.Lx_eq]
    push_cast
    ring
  rw [e, pdist_add_int_mul]

end Columns

/-! ## Lemma 3.10 (statements) -/

section StripsFattenings

variable {δ₀ : ℝ} {T : Torus}

/-- **Lemma 3.10**: "`Let the torus be admissible and let $I\subset\R/L_x\Z$ be an open interval of length at least $2\delta_x$. Then for every $\rho\ge0$,`"
"`\fat{\Str(I)}\rho\subset\Str(I_\rho)\subset\fat{\Str(I)}{\rho+\delta_x}.`" — the first inclusion
(`I` the image of `(a, b)`, `b − a ≥ 2δ_x`). -/
theorem fat_strip_subset (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) {a b : ℝ} (hab : 2 * δx δ₀ T ≤ b - a) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    fat (strip δ₀ T (circImage T.Lx (Set.Ioo a b))) ρ ⊆
      strip δ₀ T (Metric.cthickening ρ (circImage T.Lx (Set.Ioo a b))) := by
  intro s hs
  rw [mem_fat] at hs
  obtain ⟨s', hs', hd⟩ := hs
  rw [mem_strip, mem_circImage] at hs'
  obtain ⟨m, hm⟩ := hs'
  rw [mem_strip]
  set u := xs δ₀ T s - xs δ₀ T s' with hu
  set k : ℤ := round (T.Lx⁻¹ * u) with hk
  have hp : |u - (k : ℝ) * T.Lx| ≤ ρ := by
    have h1 := le_trans (pdist_le_slotDist s s') hd
    unfold pdist at h1
    rwa [HRTorus.SlotFrame.Analysis.infDist_zmultiples_eq] at h1
  refine Metric.mem_cthickening_of_dist_le _ (xs δ₀ T s' + (k : ℝ) * T.Lx) ρ _ ?_ ?_
  · rw [mem_circImage]
    refine ⟨m - k, ?_⟩
    have e : xs δ₀ T s' + (k : ℝ) * T.Lx + ((m - k : ℤ) : ℝ) * T.Lx = xs δ₀ T s' + (m : ℝ) * T.Lx := by
      push_cast
      ring
    rw [e]
    exact hm
  · rw [Real.dist_eq]
    have e : xs δ₀ T s - (xs δ₀ T s' + (k : ℝ) * T.Lx) = u - (k : ℝ) * T.Lx := by
      rw [hu]
      ring
    rw [e]
    exact hp

/-- **Lemma 3.10**, the second inclusion. -/
theorem strip_cthickening_subset (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) {a b : ℝ} (hab : 2 * δx δ₀ T ≤ b - a)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    strip δ₀ T (Metric.cthickening ρ (circImage T.Lx (Set.Ioo a b))) ⊆
      fat (strip δ₀ T (circImage T.Lx (Set.Ioo a b))) (ρ + δx δ₀ T) := by
  have hδ := δx_pos hδ₀ hT
  have hLx := Lx_eq_nx hδ₀ hT
  have h4 := (consistency_ii hδ₀ hT).1
  have hab' : a < b := by linarith
  intro s hs
  rw [mem_strip, cthickening_circImage_Ioo T.Lx_pos hab' hρ, mem_circImage] at hs
  obtain ⟨m, hm⟩ := hs
  rw [Set.mem_Icc] at hm
  obtain ⟨z, hz, hyz⟩ : ∃ z ∈ Set.Icc a b, |xs δ₀ T s + m * T.Lx - z| ≤ ρ := by
    rcases le_or_gt (xs δ₀ T s + m * T.Lx) a with h1 | h1
    · refine ⟨a, ⟨le_rfl, hab'.le⟩, ?_⟩
      rw [abs_le]
      constructor <;> linarith [hm.1]
    · rcases le_or_gt (xs δ₀ T s + m * T.Lx) b with h2 | h2
      · exact ⟨xs δ₀ T s + m * T.Lx, ⟨h1.le, h2⟩, by rw [sub_self, abs_zero]; exact hρ⟩
      · refine ⟨b, ⟨hab'.le, le_rfl⟩, ?_⟩
        rw [abs_le]
        constructor <;> linarith [hm.2]
  obtain ⟨n, hn, hnz⟩ : ∃ n : ℤ, (n : ℝ) * δx δ₀ T ∈ Set.Ioo a b ∧ |z - n * δx δ₀ T| ≤ δx δ₀ T := by
    have hf1 : (⌊z / δx δ₀ T⌋ : ℝ) * δx δ₀ T ≤ z := by
      have := Int.floor_le (z / δx δ₀ T)
      rwa [le_div_iff₀ hδ] at this
    have hf2 : z < ((⌊z / δx δ₀ T⌋ : ℝ) + 1) * δx δ₀ T := by
      have := Int.lt_floor_add_one (z / δx δ₀ T)
      rwa [div_lt_iff₀ hδ] at this
    rcases le_or_gt ((⌊z / δx δ₀ T⌋ : ℝ) * δx δ₀ T) a with h1 | h1
    · refine ⟨⌊z / δx δ₀ T⌋ + 1, ⟨?_, ?_⟩, ?_⟩
      · push_cast
        linarith [hz.1]
      · push_cast
        linarith
      · push_cast
        rw [abs_le]
        constructor <;> linarith
    · rcases lt_or_eq_of_le (show (⌊z / δx δ₀ T⌋ : ℝ) * δx δ₀ T ≤ b by linarith [hz.2]) with h2 | h2
      · refine ⟨⌊z / δx δ₀ T⌋, ⟨h1, h2⟩, ?_⟩
        rw [abs_le]
        constructor <;> linarith
      · refine ⟨⌊z / δx δ₀ T⌋ - 1, ⟨?_, ?_⟩, ?_⟩
        · push_cast
          linarith
        · push_cast
          linarith
        · push_cast
          rw [abs_le]
          constructor <;> linarith [hz.2]
  have hnx0 : (0 : ℤ) < (nx δ₀ T : ℤ) := by exact_mod_cast (by omega : 0 < nx δ₀ T)
  set r := n % (nx δ₀ T : ℤ) with hr
  set q := n / (nx δ₀ T : ℤ) with hq
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hnx0.ne'
  have hr1 : r < (nx δ₀ T : ℤ) := Int.emod_lt_of_pos _ hnx0
  have hnrq : n = r + (nx δ₀ T : ℤ) * q := (Int.emod_add_mul_ediv n (nx δ₀ T : ℤ)).symm
  obtain ⟨r', hr'⟩ := Int.eq_ofNat_of_zero_le hr0
  let a' : Fin (nx δ₀ T) := ⟨r', by omega⟩
  have ha' : (((a' : ℕ) : ℤ)) = r := hr'.symm
  have hxa' : xs δ₀ T (a', s.2) = (r : ℝ) * δx δ₀ T := by
    show xa δ₀ T ((a' : ℕ) : ℤ) = _
    rw [ha']
    rfl
  rw [mem_fat]
  refine ⟨(a', s.2), ?_, ?_⟩
  · rw [mem_strip, mem_circImage, hxa']
    refine ⟨q, ?_⟩
    have e : (r : ℝ) * δx δ₀ T + (q : ℝ) * T.Lx = (n : ℝ) * δx δ₀ T := by
      rw [hLx, hnrq]
      push_cast
      ring
    rw [e]
    exact hn
  · rw [slotDist_same_row s (a', s.2) rfl, hxa']
    calc pdist T.Lx (xs δ₀ T s - (r : ℝ) * δx δ₀ T)
        ≤ |xs δ₀ T s - (r : ℝ) * δx δ₀ T + ((m - q : ℤ) : ℝ) * T.Lx| := pdist_le_abs _ _ _
      _ = |(xs δ₀ T s + m * T.Lx - z) + (z - n * δx δ₀ T)| := by
          congr 1
          rw [hLx, hnrq]
          push_cast
          ring
      _ ≤ |xs δ₀ T s + m * T.Lx - z| + |z - n * δx δ₀ T| := abs_add_le _ _
      _ ≤ ρ + δx δ₀ T := add_le_add hyz hnz

end StripsFattenings

/-! ## Definition 3.11: almost-supported sequences and the set norm -/

section AlmostSupported

/-- **Definition 3.11**: "`Let $\mathcal N\subset\N$ be infinite, let $(\Tor_N)_{N\in\mathcal N}$ be admissible tori`" —
the index set `𝒩` and the tori `𝕋_N` (with `N` electrons, Definition 2.1's `N`), as a function of `N`. -/
structure TorusSeq (δ₀ : ℝ) where
  /-- the infinite index set `𝒩 ⊆ ℕ` -/
  idx : Set ℕ
  idx_infinite : idx.Infinite
  /-- the torus `𝕋_N` (its values off `𝒩` are never used) -/
  T : ℕ → Torus
  T_N : ∀ N ∈ idx, (T N).N = N
  admissible : ∀ N ∈ idx, (T N).Admissible δ₀

/-- Definition 3.11's setting is not empty: for every `δ₀ > 0` there are admissible tori with `N` electrons for all
large `N` (not a statement of the paper; a non-vacuity check of the encoding). -/
theorem nonempty_torusSeq {δ₀ : ℝ} (hδ₀ : 0 < δ₀) : Nonempty (TorusSeq δ₀) := by
  have hπ := Real.pi_pos
  have hLx0 : (0 : ℝ) < 4 * δ₀ + 4 := by positivity
  set N₀ : ℕ := ⌈L0 δ₀ * (4 * δ₀ + 4) / (4 * π)⌉₊ + 1 with hN₀
  let mk : ℕ → Torus := fun N =>
    { N := max N 1
      Lx := 4 * δ₀ + 4
      Ly := 2 * π * ((2 * max N 1 : ℕ) : ℝ) / (4 * δ₀ + 4)
      Lx_pos := hLx0
      Ly_pos := by
        have : (0 : ℝ) < ((2 * max N 1 : ℕ) : ℝ) := by
          have : 0 < 2 * max N 1 := by have := le_max_right N 1; omega
          exact_mod_cast this
        positivity
      area := by field_simp }
  refine ⟨{ idx := Set.Ici N₀, idx_infinite := Set.Ici_infinite N₀, T := mk, T_N := ?_, admissible := ?_ }⟩
  · intro N hN
    have h1 : 1 ≤ N := le_trans (by omega) (Set.mem_Ici.mp hN)
    exact max_eq_left h1
  · intro N hN
    have h1 : 1 ≤ N := le_trans (by omega) (Set.mem_Ici.mp hN)
    refine ⟨?_, le_refl _⟩
    show L0 δ₀ ≤ 2 * π * ((2 * max N 1 : ℕ) : ℝ) / (4 * δ₀ + 4)
    rw [max_eq_left h1, le_div_iff₀ hLx0]
    have hceil := Nat.le_ceil (L0 δ₀ * (4 * δ₀ + 4) / (4 * π))
    have hN : (N₀ : ℝ) ≤ N := by exact_mod_cast Set.mem_Ici.mp hN
    have hlt : L0 δ₀ * (4 * δ₀ + 4) / (4 * π) ≤ N := by
      have : ((⌈L0 δ₀ * (4 * δ₀ + 4) / (4 * π)⌉₊ : ℕ) : ℝ) + 1 = (N₀ : ℝ) := by rw [hN₀]; push_cast; ring
      linarith
    rw [div_le_iff₀ (by positivity)] at hlt
    push_cast
    linarith

/-- **Definition 3.11**: "`For an operator $A$ on $\FockS$ and $X\subset\Slots$, the \emph{set norm} of order $k$ is $\norm A_{X;k}:=\sup_{r\ge0}(1+r)^k\inf\{\norm{A-A'}:A'\in\Alg(\fat Xr)\}$.`"
— in `ℝ≥0∞` (the module docstring), the infimum a real infimum over the nonempty set `Alg(X^{(r)}) ∋ 0`. -/
def setNorm {δ₀ : ℝ} {T : Torus} (A : Op (Slot δ₀ T)) (X : Finset (Slot δ₀ T)) (k : ℝ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 ≤ r),
    ENNReal.ofReal ((1 + r) ^ k * ⨅ A' : Alg (fat X r), ‖opCLM (A - (A' : Op (Slot δ₀ T)))‖)

variable (η : ℝ → ℝ) (δ₀ : ℝ) (Ts : TorusSeq δ₀)

/-- **Definition 3.11**, the estimate for a given prefactor exponent `m` and constants `C = (C_k)_{k∈ℕ}`:
"`there are $m\ge0$ and, for every $k\in\N$, a constant $C_k$ such that for all $N\in\mathcal N$ and $r\ge0$ there is $A_{N,r}\in\Alg(\fat{(Z_N)}r)$ with`"
"`\norm{\iota(A_N)-A_{N,r}}\le C_kN^m(1+r)^{-k}.`" (`A_{N,r}` read inside the scope of `k`, as the sentence is
built; `ASBound.exists_approx_forall_k`: one `A_{N,r}` serves every `k`.) -/
def ASBound (Z : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))) (A : (N : ℕ) → FockOp (Ts.T N)) (m : ℝ) (C : ℕ → ℝ) :
    Prop :=
  0 ≤ m ∧ ∀ k : ℕ, ∀ N ∈ Ts.idx, ∀ r : ℝ, 0 ≤ r →
    ∃ A' ∈ Alg (fat (Z N) r),
      ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A')‖ ≤ C k * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ))

/-- **Definition 3.11**: the data of `A ∈ 𝒜𝒮_Z` made explicit — a prefactor exponent `m`, the constants `C_k`, and
the estimate. -/
structure ASWitness (Z : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))) (A : (N : ℕ) → FockOp (Ts.T N)) where
  /-- the prefactor exponent `m ≥ 0` -/
  m : ℝ
  /-- the constants `C_k`, `k ∈ ℕ` -/
  C : ℕ → ℝ
  bound : ASBound η δ₀ Ts Z A m C

/-- **Definition 3.11**: "`A sequence $A=(A_N)_{N\in\mathcal N}$ of operators $A_N$ on $\Fock$ is \emph{almost supported in $Z$}, written $A\in\AS_Z$`",
for "`$Z=(Z_N)_{N\in\mathcal N}$ with $Z_N\subset\Slots$`": a witness exists. -/
def AlmostSupported (Z : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))) (A : (N : ℕ) → FockOp (Ts.T N)) : Prop :=
  Nonempty (ASWitness η δ₀ Ts Z A)

/-- **Definition 3.11**: "`Such an $m$ is a \emph{prefactor exponent} of $A$.`" -/
def IsPrefactorExponent (Z : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))) (A : (N : ℕ) → FockOp (Ts.T N)) (m : ℝ) :
    Prop :=
  ∃ C : ℕ → ℝ, ASBound η δ₀ Ts Z A m C

/-- **Definition 3.11**: "`A family of such sequences depending on a parameter is almost supported \emph{uniformly} in the parameter if one $m$ and one set of constants $C_k$ serve for all values of the parameter.`"
— the parameter in any type `P`; the sets `Z` may depend on it too. -/
def AlmostSupportedUniformly {P : Type*} (Z : P → (N : ℕ) → Finset (Slot δ₀ (Ts.T N)))
    (A : P → (N : ℕ) → FockOp (Ts.T N)) : Prop :=
  ∃ (m : ℝ) (C : ℕ → ℝ), ∀ p : P, ASBound η δ₀ Ts (Z p) (A p) m C

/-! ### Statements -/

variable {η δ₀ Ts}

/-! ### Proof devices for Definition 3.11 (phase (b); not statements of the paper)

The commutator with the parity is bounded by twice the norm (the parity is unitary); an operator that even operators
approximate arbitrarily well is even. -/

section Def311Devices

theorem norm_comm_parity_le {T : Torus} (Y : Op (Slot δ₀ T)) :
    ‖opCLM (Y * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * Y)‖ ≤ 2 * ‖opCLM Y‖ := by
  open scoped Matrix.Norms.L2Operator in
  have hP : ‖(Fermion.Pilot.JW.parityOp (S := Slot δ₀ T))‖ = 1 := CStarRing.norm_of_mem_unitary parityOp_mem_unitary
  open scoped Matrix.Norms.L2Operator in
  show ‖Y * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * Y‖ ≤ 2 * ‖Y‖
  open scoped Matrix.Norms.L2Operator in
  calc ‖Y * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * Y‖ ≤ ‖Y * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T))‖ + ‖(Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖ * ‖(Fermion.Pilot.JW.parityOp (S := Slot δ₀ T))‖ + ‖(Fermion.Pilot.JW.parityOp (S := Slot δ₀ T))‖ * ‖Y‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖Y‖ := by rw [hP]; ring

theorem isEven_of_bound {T : Torus} {B : Op (Slot δ₀ T)} {K : ℝ}
    (hB : ∀ r : ℝ, 0 ≤ r → ∃ A' : Op (Slot δ₀ T), IsEven A' ∧ ‖opCLM (B - A')‖ ≤ K * (1 + r) ^ (-(1 : ℝ))) :
    IsEven B := by
  by_contra hne
  have hΦ : B * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * B ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hx : 0 < ‖opCLM (B * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * B)‖ := by
    rw [norm_pos_iff]
    intro h0
    exact hΦ ((Matrix.toEuclideanCLM (n := Conf (Slot δ₀ T)) (𝕜 := ℂ)).injective (h0.trans (map_zero _).symm))
  set x := ‖opCLM (B * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * B)‖ with hxdef
  have key : ∀ r : ℝ, 0 ≤ r → x ≤ 2 * K * (1 + r)⁻¹ := by
    intro r hr
    obtain ⟨A', hA', hb⟩ := hB r hr
    have e : B * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * B = (B - A') * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * (B - A') := by
      rw [Matrix.sub_mul, Matrix.mul_sub, hA'.eq]
      abel
    calc x = ‖opCLM ((B - A') * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * (B - A'))‖ := by rw [hxdef, e]
      _ ≤ 2 * ‖opCLM (B - A')‖ := norm_comm_parity_le _
      _ ≤ 2 * (K * (1 + r) ^ (-(1 : ℝ))) := by linarith
      _ = 2 * K * (1 + r)⁻¹ := by rw [Real.rpow_neg_one]; ring
  have hK : 0 < K := by
    have := key 0 le_rfl
    norm_num at this
    linarith
  have hx0 : x ≠ 0 := hx.ne'
  have hxK : x + 2 * K ≠ 0 := (by linarith : 0 < x + 2 * K).ne'
  have h1 := key (2 * K / x) (by positivity)
  have h2 : 2 * K * (1 + 2 * K / x)⁻¹ = 2 * K * x / (x + 2 * K) := by
    rw [show 1 + 2 * K / x = (x + 2 * K) / x by field_simp, inv_div]
    ring
  rw [h2, le_div_iff₀ (by linarith)] at h1
  nlinarith

/-- A closed nonempty set of operators has a nearest point to any operator in the operator norm (the operators as
continuous linear maps form a finite-dimensional, hence proper, normed space). -/
theorem exists_nearest_opCLM {S : Type*} [Fintype S] [DecidableEq S] (s : Set (Op S)) (hs : IsClosed s)
    (hne : s.Nonempty) (x : Op S) : ∃ B ∈ s, ∀ A' ∈ s, ‖opCLM (x - B)‖ ≤ ‖opCLM (x - A')‖ := by
  let e : Op S ≃L[ℂ] (EuclideanSpace ℂ (Conf S) →L[ℂ] EuclideanSpace ℂ (Conf S)) :=
    LinearEquiv.toContinuousLinearEquiv (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv
  have : ProperSpace (EuclideanSpace ℂ (Conf S) →L[ℂ] EuclideanSpace ℂ (Conf S)) := FiniteDimensional.proper ℂ _
  have hs' : IsClosed (e '' s) := e.toHomeomorph.isClosedMap _ hs
  obtain ⟨y, ⟨B, hB, rfl⟩, h⟩ := hs'.exists_infDist_eq_dist (hne.image e) (e x)
  refine ⟨B, hB, fun A' hA' => ?_⟩
  have h1 := Metric.infDist_le_dist_of_mem (x := e x) (Set.mem_image_of_mem e hA')
  rw [h, dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub] at h1
  exact h1

/-- `Alg(Y)` is closed (the intersection of the closed `CAR(Y)` with the closed commutant of the parity). -/
theorem isClosed_Alg {S : Type*} [Fintype S] [DecidableEq S] (Y : Finset S) :
    IsClosed (Alg Y : Set (Op S)) := by
  have h1 := Fermion.Pilot.JW.isClosed_CAR Y
  have h2 : IsClosed {B : Op S | B * Fermion.Pilot.JW.parityOp = Fermion.Pilot.JW.parityOp * B} :=
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  exact h1.inter h2

end Def311Devices

/-- **Definition 3.11** with the paper's quantifiers: `A ∈ 𝒜𝒮_Z` if and only if there are `m ≥ 0` and, for every
`k ∈ ℕ`, a constant `C_k` such that for all `N ∈ 𝒩` and `r ≥ 0` there is `A_{N,r} ∈ Alg(Z_N^{(r)})` with
`‖ι(A_N) − A_{N,r}‖ ≤ C_k N^m (1 + r)^{−k}`. -/
theorem almostSupported_iff (Z : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))) (A : (N : ℕ) → FockOp (Ts.T N)) :
    AlmostSupported η δ₀ Ts Z A ↔
      ∃ m : ℝ, 0 ≤ m ∧ ∀ k : ℕ, ∃ Ck : ℝ, ∀ N ∈ Ts.idx, ∀ r : ℝ, 0 ≤ r →
        ∃ A' ∈ Alg (fat (Z N) r),
          ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A')‖ ≤ Ck * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ)) := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.m, w.bound.1, fun k => ⟨w.C k, w.bound.2 k⟩⟩
  · rintro ⟨m, hm, hC⟩
    choose C hC' using hC
    exact ⟨⟨m, C, hm, hC'⟩⟩

/-- The approximant `A_{N,r}` can be chosen independently of `k` (a best approximant in the finite-dimensional
`Alg(Z_N^{(r)})` serves every `k`), so the reading of the quantifiers does not matter. -/
theorem ASBound.exists_approx_forall_k {Z : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))} {A : (N : ℕ) → FockOp (Ts.T N)}
    {m : ℝ} {C : ℕ → ℝ} (h : ASBound η δ₀ Ts Z A m C) :
    ∀ N ∈ Ts.idx, ∀ r : ℝ, 0 ≤ r → ∃ A' ∈ Alg (fat (Z N) r), ∀ k : ℕ,
      ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A')‖ ≤ C k * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ)) := by
  intro N hN r hr
  obtain ⟨B, hB, hmin⟩ := exists_nearest_opCLM (Alg (fat (Z N) r)) (isClosed_Alg _)
    ⟨0, zero_mem _, Commute.zero_left _⟩ (iota η δ₀ (Ts.T N) (A N))
  refine ⟨B, hB, fun k => ?_⟩
  obtain ⟨A', hA', hk⟩ := h.2 k N hN r hr
  exact (hmin A' hA').trans hk

/-- The sentence after **Definition 3.11**: "`Since $\Alg(\fat Xr)$ consists of even operators, only even operators can be almost supported in this sense`"
— an almost-supported sequence consists of even operators. -/
theorem AlmostSupported.isEven (hη : IsProfile η) (hδ₀ : 0 < δ₀) {Z : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))}
    {A : (N : ℕ) → FockOp (Ts.T N)} (h : AlmostSupported η δ₀ Ts Z A) : ∀ N ∈ Ts.idx, IsEven (A N) := by
  intro N hN
  obtain ⟨w⟩ := h
  have hT := Ts.admissible N hN
  have hιev : IsEven (iota η δ₀ (Ts.T N) (A N)) :=
    isEven_of_bound (K := w.C 1 * (N : ℝ) ^ w.m) fun r hr => by
      obtain ⟨A', hA', hb⟩ := w.bound.2 1 N hN r hr
      exact ⟨A', hA'.2, by simpa using hb⟩
  have hpar := iota_parity hη hδ₀ hT (A N)
  have hPι : Fermion.Pilot.JW.parityOp * iota η δ₀ (Ts.T N) (A N) * Fermion.Pilot.JW.parityOp = iota η δ₀ (Ts.T N) (A N) := by
    rw [Matrix.mul_assoc, hιev.eq, ← Matrix.mul_assoc, Fermion.Pilot.JW.parityOp_mul_parityOp, Matrix.one_mul]
  rw [hPι] at hpar
  have hPA : Fermion.Pilot.JW.parityOp * A N * Fermion.Pilot.JW.parityOp = A N := (iota_injective hη hδ₀ hT hpar).symm
  show A N * Fermion.Pilot.JW.parityOp = Fermion.Pilot.JW.parityOp * A N
  calc A N * Fermion.Pilot.JW.parityOp = Fermion.Pilot.JW.parityOp * A N * Fermion.Pilot.JW.parityOp * Fermion.Pilot.JW.parityOp := by rw [hPA]
    _ = Fermion.Pilot.JW.parityOp * A N := by rw [Matrix.mul_assoc, Fermion.Pilot.JW.parityOp_mul_parityOp, Matrix.mul_one]

/-- The same for the slot-side operators `ι(A_N)`. -/
theorem AlmostSupported.isEven_iota (hη : IsProfile η) (hδ₀ : 0 < δ₀) {Z : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))}
    {A : (N : ℕ) → FockOp (Ts.T N)} (h : AlmostSupported η δ₀ Ts Z A) :
    ∀ N ∈ Ts.idx, IsEven (iota η δ₀ (Ts.T N) (A N)) := by
  intro N hN
  obtain ⟨w⟩ := h
  exact isEven_of_bound (K := w.C 1 * (N : ℝ) ^ w.m) fun r hr => by
    obtain ⟨A', hA', hb⟩ := w.bound.2 1 N hN r hr
    exact ⟨A', hA'.2, by simpa using hb⟩

/-- The set norm of an operator that is not even is `+∞` for every order `k > 0` (whence `ℝ≥0∞`). -/
theorem setNorm_eq_top {T : Torus} (A : Op (Slot δ₀ T)) (X : Finset (Slot δ₀ T)) {k : ℝ} (hk : 0 < k)
    (hA : ¬ IsEven A) : setNorm A X k = ⊤ := by
  have hΦ : A * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * A ≠ 0 := fun h0 => hA (sub_eq_zero.mp h0)
  have hx : 0 < ‖opCLM (A * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * A)‖ := by
    rw [norm_pos_iff]
    intro h0
    exact hΦ ((Matrix.toEuclideanCLM (n := Conf (Slot δ₀ T)) (𝕜 := ℂ)).injective (h0.trans (map_zero _).symm))
  set x := ‖opCLM (A * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * A)‖ with hxdef
  have hlow : ∀ r : ℝ, 0 ≤ r → x / 2 ≤ ⨅ A' : Alg (fat X r), ‖opCLM (A - (A' : Op (Slot δ₀ T)))‖ := by
    intro r _
    have : Nonempty (Alg (fat X r)) := ⟨⟨0, zero_mem _, Commute.zero_left _⟩⟩
    refine le_ciInf fun A' => ?_
    have e : A * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * A =
        (A - (A' : Op (Slot δ₀ T))) * (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) - (Fermion.Pilot.JW.parityOp (S := Slot δ₀ T)) * (A - (A' : Op (Slot δ₀ T))) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, A'.2.2.eq]
      abel
    have := norm_comm_parity_le (A - (A' : Op (Slot δ₀ T)))
    rw [← e, ← hxdef] at this
    linarith
  rw [setNorm, iSup_eq_top]
  intro b hb
  set b' := b.toReal with hb'
  have hb'0 : 0 ≤ b' := ENNReal.toReal_nonneg
  set r : ℝ := (2 * b' / x + 1) ^ (1 / k) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  refine ⟨r, ?_⟩
  rw [iSup_pos hr0]
  have hrk : r ^ k = 2 * b' / x + 1 := by
    rw [hr, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hk.ne', Real.rpow_one]
  have h1 : 2 * b' / x + 1 ≤ (1 + r) ^ k := by
    rw [← hrk]
    exact Real.rpow_le_rpow hr0 (by linarith) hk.le
  have h2 : b' < (1 + r) ^ k * (x / 2) := by
    have hx0 : x ≠ 0 := hx.ne'
    have : b' < (2 * b' / x + 1) * (x / 2) := by
      have e : (2 * b' / x + 1) * (x / 2) = b' + x / 2 := by
        field_simp
      rw [e]
      linarith
    calc b' < (2 * b' / x + 1) * (x / 2) := this
      _ ≤ (1 + r) ^ k * (x / 2) := by gcongr
  calc b = ENNReal.ofReal b' := (ENNReal.ofReal_toReal hb.ne).symm
    _ < ENNReal.ofReal ((1 + r) ^ k * (x / 2)) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr h2
    _ ≤ ENNReal.ofReal ((1 + r) ^ k * ⨅ A' : Alg (fat X r), ‖opCLM (A - (A' : Op (Slot δ₀ T)))‖) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hlow r hr0) (Real.rpow_nonneg (by linarith) _))

/-- For `A ∈ 𝒜𝒮_Z` with witness `(m, C)`: `‖ι(A_N)‖_{Z_N;k} ≤ C_k N^m` for every `k ∈ ℕ` and `N ∈ 𝒩`. -/
theorem ASBound.setNorm_le {Z : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))} {A : (N : ℕ) → FockOp (Ts.T N)}
    {m : ℝ} {C : ℕ → ℝ} (h : ASBound η δ₀ Ts Z A m C) (k : ℕ) :
    ∀ N ∈ Ts.idx, setNorm (iota η δ₀ (Ts.T N) (A N)) (Z N) k ≤ ENNReal.ofReal (C k * (N : ℝ) ^ m) := by
  intro N hN
  unfold setNorm
  refine iSup₂_le fun r hr => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨A', hA', hb⟩ := h.2 k N hN r hr
  have hbdd : BddBelow (Set.range fun B : Alg (fat (Z N) r) =>
      ‖opCLM (iota η δ₀ (Ts.T N) (A N) - (B : Op (Slot δ₀ (Ts.T N))))‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨B, rfl⟩
    exact norm_nonneg _
  have hinf : (⨅ B : Alg (fat (Z N) r), ‖opCLM (iota η δ₀ (Ts.T N) (A N) - (B : Op (Slot δ₀ (Ts.T N))))‖) ≤
      ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A')‖ := ciInf_le hbdd ⟨A', hA'⟩
  have hpos : 0 < (1 + r) ^ (k : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  calc (1 + r) ^ (k : ℝ) * ⨅ B : Alg (fat (Z N) r), ‖opCLM (iota η δ₀ (Ts.T N) (A N) - (B : Op (Slot δ₀ (Ts.T N))))‖
      ≤ (1 + r) ^ (k : ℝ) * (C k * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left (hinf.trans hb) hpos.le
    _ = C k * (N : ℝ) ^ m := by
        rw [Real.rpow_neg (by linarith), mul_left_comm, mul_inv_cancel₀ hpos.ne', mul_one]

end AlmostSupported

end HRTorus.Locality
