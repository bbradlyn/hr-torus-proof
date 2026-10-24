import HRTorus.Fock.Physical

/-!
# The slot Fock space, its local algebras and the fattenings (T-0056 block B, `Fock.Slot`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **The definitions and statements were written
first and reviewed against the paper (phase (a)) and are unchanged; phase (b) added the proofs and the proof
devices, each marked as such (in its section's header or its docstring). Every theorem is proved; there is no
`sorry`.** The paper: the HR paper, `papers/hr/sections/03-slot-frame.tex` —
Definition 3.1 `def:frame` (the slot distances), the first half of Definition 3.7 `def:slotfock` (the slot Fock
space, `ĉ(g)`, `ĉ_{sσ}`, `N̂_σ`, `CAR(X)`, `Alg(X)`, the `r`-fattening) and the paragraph after it, and the middle
sentence of Lemma 3.8(iii) `lem:embedding` (the gauge transformations map `CAR(X)` and `Alg(X)` onto themselves).

## The model (R-0021: the concrete Jordan–Wigner Fock space)

* `𝔉_𝒮` is the pilot's Jordan–Wigner space (`HRTorus.Fermion.Pilot.JW`) at the slot type `S := Slot δ₀ T`:
  modes `(s, σ)`, configurations `Conf = (modes → Bool)`, operators `Op` = matrices on configurations
  (`SlotFock δ₀ T`, `SlotOp δ₀ T`). Its `ĉ_{sσ}` (`chat`), `N̂_σ` (`numberOp`), parity, gauge unitaries and
  conjugations (`parityOp`, `gaugeOp`, `gauge`), `CAR(X)`, `Alg(X)` and `IsEven` are the pilot's, unchanged: the pilot
  states them for any finite `S`. The annihilator `ĉ(g)` of `g ∈ ℓ²(𝒮) ⊗ ℂ²` is block A's `cVec` on the vector's
  coordinates (`chatVec`, the generic form of block A's `cf`).
* The statements about operators are generic in the finite type `S` (the physical side is `S := ZMod N_φ`, the slot
  side `S := Slot δ₀ T`): the operator norm (`opCLM`, block A's `toCLM` for any `S`; norms of operators are always
  `‖opCLM A‖`), `ĉ(g)` and its CAR, the commutation of the local algebras, the gauge invariance of `CAR(X)` and
  `Alg(X)`, and the sector vocabulary on any Jordan–Wigner space (`IsSectorPreservingS`: commuting with `N̂_↑` and
  `N̂_↓`; `sectorS`, `PsecS` are block A's `sector`, `Psec` for any `S`, stated here rather than edited in block A's
  files).
* The slot distance `d(s, s') := d(r_s, r_{s'})` is `SlotFrame.flatDist` of the centres (`slotDist`); the
  fattening `X^{(r)} = {s : d(s, X) ≤ r}` is a `Finset` (`fat`), with `d(s, X) ≤ r` written as
  `∃ s' ∈ X, d(s, s') ≤ r` — for nonempty `X` the minimum `d(s, X)` over the finite set is attained and
  `mem_fat_iff_inf'` states that this is the same; for `X = ∅` both readings give `∅` (the minimum over the empty set
  read as `+∞`). Real comparisons are decided classically (Mathlib's instances).
-/

open scoped InnerProductSpace Matrix
open Complex (I)

noncomputable section

namespace HRTorus.Fock

open HRTorus.SlotFrame HRTorus.LLL
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op num c chat numberOp parityOp gaugeOp IsEven CAR Alg)

/-! ## Any finite slot type `S`: the operator norm, `ĉ(g)`, the local algebras, the sectors -/

section Generic

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- An operator on `ℂ^{Conf S}` as a continuous linear map (`Matrix.toEuclideanCLM`): block A's `toCLM`, for any
`S`. Operator norms are `‖opCLM A‖` throughout (block A's convention), so that `‖ι(A)‖ = ‖A‖` compares the same
norms on both sides. -/
abbrev opCLM (A : Op S) : EuclideanSpace ℂ (Conf S) →L[ℂ] EuclideanSpace ℂ (Conf S) :=
  Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) A

/-- **Definition 3.7**: "`with annihilation operators $\chat(g)$, $g\in\ell^2(\Slots)\otimes\C^2$`" — the
annihilator `ĉ(g) = Σ_μ \overline{g_μ} ĉ_μ` of a one-body vector `g ∈ ℓ²(S) ⊗ ℂ² = ℓ²(S × {↑,↓})`, conjugate-linear in
`g`: block A's `cVec` on the coordinates of `g` (block A's `cf` is the case `S = ZMod N_φ`, `cf_eq_chatVec`). -/
def chatVec (g : EuclideanSpace ℂ (Mode S)) : Op S :=
  cVec fun μ => g μ

/-- The sector labels `𝐧 = (n_↑, n_↓) ∈ {0, …, |S|}²` (block A's `SectorLabel`, for any `S`). -/
abbrev SectorLabelS (S : Type*) [Fintype S] : Type :=
  Fin (Fintype.card S + 1) × Fin (Fintype.card S + 1)

/-- The sector `𝐧` of `ℂ^{Conf S}`: the joint eigenspace `{Ψ : N̂_↑Ψ = n_↑Ψ, N̂_↓Ψ = n_↓Ψ}` (block A's `sector`, for
any `S`). -/
def sectorS (nn : SectorLabelS S) : Submodule ℂ (EuclideanSpace ℂ (Conf S)) :=
  Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S) (n := Conf S) (numberOp .up))
      (((nn.1 : ℕ) : ℝ) : ℂ) ⊓
    Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S) (n := Conf S) (numberOp .dn))
      (((nn.2 : ℕ) : ℝ) : ℂ)

/-- The orthogonal projection `P̂_𝐧` onto the sector `𝐧`, as a matrix (block A's `Psec`, for any `S`). -/
def PsecS (nn : SectorLabelS S) : Op S :=
  (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)).symm (sectorS nn).starProjection

/-- Commuting with `N̂_↑` and `N̂_↓` (**Lemma 3.8(iii)**: "`that commutes with $\Nhat\up$ and $\Nhat\dn$`"); block A's
`IsSectorPreserving` for any `S` (`isSectorPreserving_iff_S`). -/
def IsSectorPreservingS (A : Op S) : Prop :=
  Commute A (numberOp .up) ∧ Commute A (numberOp .dn)

/-! ### Proof devices for the generic statements (phase (b); not statements of the paper)

The parity and the gauge unitaries are diagonal in the occupation basis (the pilot's `parityOp_eq_diagonal`,
`gauge_eq_conj`); conjugating an annihilator by a diagonal unitary multiplies it by a phase (the pilot's
`diagonal_mul_c_mul_conjTranspose`), here with the phase written out (`−1` for the parity, `e^{−iφ_σ}` for the
gauge). The commutation of the local algebras is by induction over the generators: every `A ∈ CAR(X)` satisfies
`A ĉ_ν = ĉ_ν (P A P)` for a mode `ν` outside `X` (`P` the parity), and `P A P = A` when `A` is even. The sector
devices are block A's (`ctσ`, `secOf`, `secInd`, …) for any `S`. -/

section GenericDevices

open HRTorus.Fermion.Pilot.JW (diagonal_mul_c_mul_conjTranspose diagonal_conj_mem_CAR occ occ_update
  parityOp_eq_diagonal gaugePhase gaugePhase_update star_gaugePhase gauge_eq_conj gauge_unit gauge_phase
  parityOp_mul_parityOp c_anticomm c_anticomm_star card_occ_split sum_spin)

theorem parity_phase_eq (μ : Mode S) (m : Conf S) (hm : m μ = true) :
    (-1 : ℂ) ^ occ (Function.update m μ false) * star ((-1 : ℂ) ^ occ m) = -1 := by
  rw [occ_update hm, star_pow, star_neg, star_one, pow_succ, mul_neg_one, mul_neg, ← mul_pow,
    neg_one_mul, neg_neg, one_pow]

theorem parityOp_conjTranspose : (parityOp : Op S)ᴴ = parityOp := by
  rw [parityOp_eq_diagonal, Matrix.diagonal_conjTranspose]
  congr 1
  funext m
  rw [Pi.star_apply, star_pow, star_neg, star_one]

theorem parityOp_mul_c_mul_parityOp (μ : Mode S) : parityOp * c μ * parityOp = -c μ := by
  have hPh : (parityOp : Op S) = (Matrix.diagonal fun m : Conf S => (-1 : ℂ) ^ occ m)ᴴ := by
    rw [← parityOp_eq_diagonal, parityOp_conjTranspose]
  calc (parityOp : Op S) * c μ * parityOp
      = (Matrix.diagonal fun m : Conf S => (-1 : ℂ) ^ occ m) * c μ *
          (Matrix.diagonal fun m : Conf S => (-1 : ℂ) ^ occ m)ᴴ := by
        rw [← hPh]; rfl
    _ = -c μ := by
        rw [diagonal_mul_c_mul_conjTranspose (fun m hm => parity_phase_eq μ m hm), neg_one_smul]

theorem parityOp_mul_c_conjTranspose_mul_parityOp (μ : Mode S) :
    parityOp * (c μ)ᴴ * parityOp = -(c μ)ᴴ := by
  have h := congrArg Matrix.conjTranspose (parityOp_mul_c_mul_parityOp (S := S) μ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, parityOp_conjTranspose, Matrix.conjTranspose_neg] at h
  rw [Matrix.mul_assoc]
  exact h

theorem parityOp_conj_parityOp_conj (A : Op S) : parityOp * (parityOp * A * parityOp) * parityOp = A := by
  simp only [← Matrix.mul_assoc, parityOp_mul_parityOp, Matrix.one_mul]
  rw [Matrix.mul_assoc, parityOp_mul_parityOp, Matrix.mul_one]

theorem c_conjTranspose_anticomm (μ ν : Mode S) :
    (c μ)ᴴ * (c ν)ᴴ + (c ν)ᴴ * (c μ)ᴴ = 0 := by
  have h := congrArg Matrix.conjTranspose (c_anticomm ν μ)
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_zero] at h
  exact h

/-- Every element of `CAR(X)` moves past the annihilator and the creator of a mode outside `X` with the parity. -/
theorem mul_c_eq_of_mem_CAR {X : Finset S} {ν : Mode S} (hν : ν.1 ∉ X) {A : Op S} (hA : A ∈ CAR X) :
    A * c ν = c ν * (parityOp * A * parityOp) ∧ A * (c ν)ᴴ = (c ν)ᴴ * (parityOp * A * parityOp) := by
  have hA' : A ∈ Algebra.adjoin ℂ ({B | ∃ s ∈ X, ∃ σ : Spin, B = chat s σ} ∪
      star {B | ∃ s ∈ X, ∃ σ : Spin, B = chat s σ}) := hA
  refine Algebra.adjoin_induction (p := fun A _ => A * c ν = c ν * (parityOp * A * parityOp) ∧
    A * (c ν)ᴴ = (c ν)ᴴ * (parityOp * A * parityOp)) ?_ ?_ ?_ ?_ hA'
  · intro x hx
    rcases hx with ⟨s, hs, σ, rfl⟩ | hx
    · have hne : ((s, σ) : Mode S) ≠ ν := fun h => hν (h ▸ hs)
      have hP : parityOp * chat s σ * parityOp = -chat s σ := parityOp_mul_c_mul_parityOp (s, σ)
      rw [hP, Matrix.mul_neg, Matrix.mul_neg]
      refine ⟨eq_neg_of_add_eq_zero_left (c_anticomm (s, σ) ν), ?_⟩
      have h2 := c_anticomm_star (s, σ) ν
      rw [if_neg hne] at h2
      exact eq_neg_of_add_eq_zero_left h2
    · obtain ⟨s, hs, σ, h⟩ := hx
      have hx : x = (chat s σ)ᴴ := by
        rw [← Matrix.star_eq_conjTranspose, ← h, star_star]
      have hne : ((s, σ) : Mode S) ≠ ν := fun h => hν (h ▸ hs)
      have hP : parityOp * (chat s σ)ᴴ * parityOp = -(chat s σ)ᴴ :=
        parityOp_mul_c_conjTranspose_mul_parityOp (s, σ)
      rw [hx, hP, Matrix.mul_neg, Matrix.mul_neg]
      constructor
      · have h2 := c_anticomm_star ν (s, σ)
        rw [if_neg (Ne.symm hne)] at h2
        exact eq_neg_of_add_eq_zero_right h2
      · exact eq_neg_of_add_eq_zero_left (c_conjTranspose_anticomm (s, σ) ν)
  · intro r
    have hr : parityOp * algebraMap ℂ (Op S) r * parityOp = algebraMap ℂ (Op S) r := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        parityOp_mul_parityOp]
    rw [hr]
    exact ⟨Algebra.commutes r (c ν), Algebra.commutes r (c ν)ᴴ⟩
  · intro x y _ _ hx hy
    have e : parityOp * (x + y) * parityOp = parityOp * x * parityOp + parityOp * y * parityOp := by
      rw [Matrix.mul_add, Matrix.add_mul]
    rw [e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hx.1, hy.1, hx.2, hy.2]
    exact ⟨rfl, rfl⟩
  · intro x y _ _ hx hy
    have e : parityOp * (x * y) * parityOp = (parityOp * x * parityOp) * (parityOp * y * parityOp) := by
      calc parityOp * (x * y) * parityOp = parityOp * x * (parityOp * parityOp) * y * parityOp := by
            rw [parityOp_mul_parityOp, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e]
    constructor
    · rw [Matrix.mul_assoc, hy.1, ← Matrix.mul_assoc, hx.1, Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, hy.2, ← Matrix.mul_assoc, hx.2, Matrix.mul_assoc]

/-- An even element of `CAR(X)` commutes with the annihilator and the creator of every mode outside `X`. -/
theorem commute_c_of_mem_Alg {X : Finset S} {ν : Mode S} (hν : ν.1 ∉ X) {A : Op S} (hA : A ∈ Alg X) :
    Commute A (c ν) ∧ Commute A (c ν)ᴴ := by
  have hPA : parityOp * A * parityOp = A := by
    rw [Matrix.mul_assoc, hA.2.eq, ← Matrix.mul_assoc, parityOp_mul_parityOp, Matrix.one_mul]
  obtain ⟨h1, h2⟩ := mul_c_eq_of_mem_CAR hν hA.1
  rw [hPA] at h1 h2
  exact ⟨h1, h2⟩

/-- The gauge conjugation of an annihilator, with the phase written out. -/
theorem gauge_c (φ : Spin → ℝ) (μ : Mode S) :
    Fermion.Pilot.JW.gauge φ (c μ) = Complex.exp (-(I * (φ μ.2 : ℂ))) • c μ := by
  rw [gauge_eq_conj]
  apply diagonal_mul_c_mul_conjTranspose
  intro m hm
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, ← Complex.star_def,
    star_gaugePhase, gaugePhase_update φ hm, ← Complex.exp_add]
  congr 1
  ring

theorem gaugeOp_mul_gaugeOp_neg (φ : Spin → ℝ) : (gaugeOp φ : Op S) * gaugeOp (-φ) = 1 := by
  rw [gaugeOp, gaugeOp, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext m
  have e : ∀ μ : Mode S, (if m μ = true then (((-φ) μ.2 : ℝ) : ℂ) else 0) =
      -(if m μ = true then ((φ μ.2 : ℝ) : ℂ) else 0) := by
    intro μ
    split_ifs <;> simp
  rw [← Complex.exp_add]
  simp_rw [e, Finset.sum_neg_distrib, mul_neg, add_neg_cancel, Complex.exp_zero]

theorem gauge_gauge_neg (φ : Spin → ℝ) (A : Op S) :
    Fermion.Pilot.JW.gauge φ (Fermion.Pilot.JW.gauge (-φ) A) = A := by
  simp only [Fermion.Pilot.JW.gauge, neg_neg, Matrix.mul_assoc]
  rw [gaugeOp_mul_gaugeOp_neg, Matrix.mul_one, ← Matrix.mul_assoc, gaugeOp_mul_gaugeOp_neg, Matrix.one_mul]

theorem gauge_mem_CAR (φ : Spin → ℝ) {X : Finset S} {A : Op S} (hA : A ∈ CAR X) :
    Fermion.Pilot.JW.gauge φ A ∈ CAR X := by
  rw [gauge_eq_conj]
  exact diagonal_conj_mem_CAR (gauge_unit φ) (gauge_phase φ) hA

theorem commute_gaugeOp_parityOp (φ : Spin → ℝ) : Commute (gaugeOp φ : Op S) parityOp := by
  rw [parityOp_eq_diagonal]
  exact commute_diagonal_diagonal _ _

theorem isEven_gauge (φ : Spin → ℝ) {A : Op S} (hA : IsEven A) : IsEven (Fermion.Pilot.JW.gauge φ A) :=
  ((commute_gaugeOp_parityOp φ).mul_left hA).mul_left (commute_gaugeOp_parityOp (-φ))

/-- The number of occupied modes of spin `σ` in `m` (block A's `ctσ`, for any `S`). -/
def ctS (σ : Spin) (m : Conf S) : ℕ :=
  (Finset.univ.filter fun s : S => m (s, σ) = true).card

theorem ctS_le (σ : Spin) (m : Conf S) : ctS σ m ≤ Fintype.card S := by
  rw [ctS]
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ])

/-- The sector label of a configuration (block A's `secOf`, for any `S`). -/
def secOfS (m : Conf S) : SectorLabelS S :=
  (⟨ctS .up m, Nat.lt_succ_of_le (ctS_le .up m)⟩, ⟨ctS .dn m, Nat.lt_succ_of_le (ctS_le .dn m)⟩)

theorem secOfS_eq_iff (m : Conf S) (nn : SectorLabelS S) :
    secOfS m = nn ↔ ctS .up m = nn.1 ∧ ctS .dn m = nn.2 := by
  rw [secOfS, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]

theorem numberOp_eq_diag (σ : Spin) : (numberOp σ : Op S) = Matrix.diagonal fun m => (ctS σ m : ℂ) := by
  rw [Fermion.Pilot.JW.numberOp_eq]
  rfl

theorem isSectorPreservingS_iff_entries (A : Op S) :
    IsSectorPreservingS A ↔ ∀ i j, A i j ≠ 0 → secOfS i = secOfS j := by
  rw [IsSectorPreservingS, numberOp_eq_diag, numberOp_eq_diag, commute_diagonal_iff, commute_diagonal_iff]
  constructor
  · rintro ⟨h1, h2⟩ i j hA
    have e1 := h1 i j; have e2 := h2 i j
    rw [mul_comm] at e1 e2
    have u := mul_right_cancel₀ hA e1
    have d := mul_right_cancel₀ hA e2
    rw [secOfS_eq_iff]
    exact ⟨(Nat.cast_injective u).symm, (Nat.cast_injective d).symm⟩
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
    · by_cases hA : A i j = 0
      · simp [hA]
      · have := (secOfS_eq_iff i (secOfS j)).mp (h i j hA)
        rw [mul_comm]
        congr 2
        first | exact this.1.symm | exact this.2.symm

theorem mem_sectorS_iff (nn : SectorLabelS S) (v : EuclideanSpace ℂ (Conf S)) :
    v ∈ sectorS nn ↔ ∀ m, v m ≠ 0 → secOfS m = nn := by
  rw [sectorS, Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff,
    numberOp_eq_diag, numberOp_eq_diag]
  have key : ∀ (d : Conf S → ℂ) (μ : ℂ),
      Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S) (n := Conf S) (Matrix.diagonal d) v = μ • v ↔
        ∀ m, v m ≠ 0 → d m = μ := by
    intro d μ
    constructor
    · intro h m hm
      have := congrArg (fun w : EuclideanSpace ℂ (Conf S) => w m) h
      simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec_diagonal, PiLp.smul_apply,
        smul_eq_mul] at this
      exact mul_right_cancel₀ hm this
    · intro h
      refine PiLp.ext fun m => ?_
      simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec_diagonal, PiLp.smul_apply,
        smul_eq_mul]
      by_cases hm : v m = 0
      · simp [hm]
      · rw [h m hm]
  rw [key, key]
  constructor
  · rintro ⟨h1, h2⟩ m hm
    rw [secOfS_eq_iff]
    exact ⟨by exact_mod_cast h1 m hm, by exact_mod_cast h2 m hm⟩
  · intro h
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have := (secOfS_eq_iff m nn).mp (h m hm); simp [this.1]
    · have := (secOfS_eq_iff m nn).mp (h m hm); simp [this.2]

/-- The indicator of the configurations of a sector (block A's `secInd`, for any `S`). -/
def secIndS (nn : SectorLabelS S) (m : Conf S) : ℂ := if secOfS m = nn then 1 else 0

theorem opCLM_diag_secIndS (nn : SectorLabelS S) :
    opCLM (Matrix.diagonal (secIndS nn)) = (sectorS nn).starProjection := by
  ext v : 1
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [mem_sectorS_iff]
    intro m hm
    by_contra hne
    apply hm
    simp [opCLM, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal, secIndS, hne]
  · intro w hw
    rw [mem_sectorS_iff] at hw
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hwm : w m = 0
    · simp [hwm]
    · have := hw m hwm
      simp [opCLM, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal, secIndS, this]

theorem PsecS_eq_diag (nn : SectorLabelS S) : PsecS nn = Matrix.diagonal (secIndS nn) := by
  rw [PsecS, ← opCLM_diag_secIndS]
  exact (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)).symm_apply_apply _

/-- The gauge phase is `φ_↑ n_↑ + φ_↓ n_↓`. -/
theorem gaugePhase_eq (φ : Spin → ℝ) (m : Conf S) :
    gaugePhase φ m = (φ .up : ℂ) * (ctS .up m : ℂ) + (φ .dn : ℂ) * (ctS .dn m : ℂ) := by
  unfold gaugePhase ctS
  rw [Fintype.sum_prod_type]
  simp_rw [sum_spin]
  rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const_zero,
    add_zero, add_zero, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- The entries of a gauge conjugation. -/
theorem gauge_apply (φ : Spin → ℝ) (A : Op S) (i j : Conf S) :
    Fermion.Pilot.JW.gauge φ A i j = Complex.exp (I * (gaugePhase φ i - gaugePhase φ j)) * A i j := by
  rw [gauge_eq_conj, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Pi.star_apply, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, ← Complex.star_def,
    star_gaugePhase, show I * (gaugePhase φ i - gaugePhase φ j) = I * gaugePhase φ i + -I * gaugePhase φ j by ring,
    Complex.exp_add]
  ring

/-- A difference of natural numbers that every phase `e^{iθ(a − b)}` sees as `1` is `0`. -/
theorem eq_of_forall_exp_eq_one {a b : ℕ}
    (h : ∀ θ : ℝ, Complex.exp (I * ((θ : ℂ) * ((a : ℂ) - (b : ℂ)))) = 1) : a = b := by
  by_contra hne
  have hk : ((a : ℝ) - (b : ℝ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have hk' : ((a : ℂ) - (b : ℂ)) ≠ 0 := by exact_mod_cast hk
  have e1 := h (Real.pi / ((a : ℝ) - (b : ℝ)))
  have e2 : I * ((((Real.pi / ((a : ℝ) - (b : ℝ)) : ℝ) : ℂ) * ((a : ℂ) - (b : ℂ)))) = (Real.pi : ℂ) * I := by
    push_cast
    field_simp
  rw [e2, Complex.exp_pi_mul_I] at e1
  norm_num at e1

end GenericDevices

/-! ### Statements: the norm, `ĉ(g)` -/

open scoped Matrix.Norms.L2Operator in
/-- The operator norm `‖opCLM A‖` is the pilot's norm (Mathlib's `L²` operator norm on matrices, scope
`Matrix.Norms.L2Operator`, in which Lemma 5.1's norm statements are written). -/
theorem norm_opCLM_eq_l2 (A : Op S) : ‖opCLM A‖ = ‖A‖ :=
  rfl

/-- `𝔉_𝒮` has dimension `2^{2|𝒮|} = 4^{|𝒮|}` (the slot-side analogue of block A's `card_conf`). -/
theorem card_conf_S : Fintype.card (Conf S) = 4 ^ Fintype.card S := by
  have hs : Fintype.card Spin = 2 := rfl
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod, hs, pow_mul']
  norm_num

/-- `ĉ(g)` is additive in `g`. -/
theorem chatVec_add (g h : EuclideanSpace ℂ (Mode S)) : chatVec (g + h) = chatVec g + chatVec h := by
  simp only [chatVec, cVec, PiLp.add_apply, star_add, add_smul, Finset.sum_add_distrib]

/-- `ĉ(g)` is conjugate-linear in `g`: `ĉ(ag) = \bar a ĉ(g)`. -/
theorem chatVec_smul (a : ℂ) (g : EuclideanSpace ℂ (Mode S)) : chatVec (a • g) = star a • chatVec g := by
  simp only [chatVec, cVec, PiLp.smul_apply, smul_eq_mul, star_mul', Finset.smul_sum, smul_smul]

/-- The CAR for `ĉ(g)` (Definition 2.5's conventions on `𝔉_𝒮`): `{ĉ(g), ĉ(h)^*} = ⟨g, h⟩`. -/
theorem chatVec_anticomm_star (g h : EuclideanSpace ℂ (Mode S)) :
    chatVec g * (chatVec h)ᴴ + (chatVec h)ᴴ * chatVec g = ⟪g, h⟫_ℂ • (1 : Op S) := by
  rw [chatVec, chatVec, cVec_anticomm_star_dev]
  congr 1
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- The CAR for `ĉ(g)`: `{ĉ(g), ĉ(h)} = 0`. -/
theorem chatVec_anticomm (g h : EuclideanSpace ℂ (Mode S)) :
    chatVec g * chatVec h + chatVec h * chatVec g = 0 :=
  cVec_anticomm_dev _ _

/-- **Definition 3.7**: "`$\chat_{s\sigma}:=\chat(\delta_s\otimes\sigma)$, where $\delta_s$ is the indicator of the slot $s$`"
(with block A's `spinTensor` for `δ_s ⊗ σ`). -/
theorem chatVec_spinTensor_single (s : S) (σ : Spin) :
    chatVec (spinTensor (EuclideanSpace.single s 1) σ) = chat s σ := by
  rw [chatVec, Fermion.Pilot.JW.chat, ← cVec_single]
  congr 1
  funext μ
  simp only [spinTensor, PiLp.toLp_apply, PiLp.single_apply]
  by_cases h1 : μ.1 = s <;> by_cases h2 : μ.2 = σ <;> simp [h1, h2, Prod.ext_iff]

/-- `ĉ(g) ∈ CAR(X)` when `g` is supported in `X` (each `ĉ(g)` is a linear combination of the `ĉ_{sσ}` with `g_{sσ} ≠ 0`). -/
theorem chatVec_mem_CAR (X : Finset S) (g : EuclideanSpace ℂ (Mode S)) (hg : ∀ μ : Mode S, μ.1 ∉ X → g μ = 0) :
    chatVec g ∈ CAR X := by
  rw [chatVec, cVec]
  refine sum_mem fun μ _ => ?_
  by_cases h : μ.1 ∈ X
  · exact Subalgebra.smul_mem (CAR X).toSubalgebra (StarAlgebra.subset_adjoin ℂ _ ⟨μ.1, h, μ.2, rfl⟩) _
  · rw [hg μ h, star_zero, zero_smul]
    exact zero_mem _

/-! ### Statements: the paragraph after Definition 3.7 -/

/-- The paragraph after **Definition 3.7**: "`Indeed, conjugation by $(-1)^{\Nhat\up+\Nhat\dn}$ changes the sign of every $\chat_{s\sigma}$ and of every $\chat_{s\sigma}^*$`" — for `ĉ_{sσ}`. -/
theorem parityOp_mul_chat_mul_parityOp (s : S) (σ : Spin) :
    parityOp * chat s σ * parityOp = -chat s σ :=
  parityOp_mul_c_mul_parityOp (s, σ)

/-- The same for `ĉ_{sσ}^*`. -/
theorem parityOp_mul_chat_conjTranspose_mul_parityOp (s : S) (σ : Spin) :
    parityOp * (chat s σ)ᴴ * parityOp = -(chat s σ)ᴴ :=
  parityOp_mul_c_conjTranspose_mul_parityOp (s, σ)

/-- The paragraph after **Definition 3.7**: "`and an element of $\Alg(X)$ commutes with every element of $\CAR(Y)$ in that case`". -/
theorem commute_of_mem_Alg_of_mem_CAR {X Y : Finset S} (hXY : Disjoint X Y) {A B : Op S} (hA : A ∈ Alg X)
    (hB : B ∈ CAR Y) : Commute A B := by
  have hle : (CAR Y).toSubalgebra ≤ Subalgebra.centralizer ℂ {A} := by
    rw [CAR, StarAlgebra.adjoin_toSubalgebra]
    apply Algebra.adjoin_le
    rintro C (⟨s, hs, σ, rfl⟩ | hC)
    · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact (commute_c_of_mem_Alg (ν := (s, σ)) (Finset.disjoint_right.mp hXY hs) hA).1.eq
    · obtain ⟨s, hs, σ, h⟩ := Set.mem_star.mp hC
      have hC' : C = (c (s, σ))ᴴ := by rw [← star_star C, h]; rfl
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      rw [hC']
      exact (commute_c_of_mem_Alg (ν := (s, σ)) (Finset.disjoint_right.mp hXY hs) hA).2.eq
  have hB' : B ∈ (CAR Y).toSubalgebra := hB
  exact (Subalgebra.mem_centralizer_iff ℂ).mp (hle hB') A rfl

/-- The paragraph after **Definition 3.7**: "`Elements of $\Alg(X)$ and of $\Alg(Y)$ commute when $X\cap Y=\emptyset$`". -/
theorem commute_of_mem_Alg_of_mem_Alg {X Y : Finset S} (hXY : Disjoint X Y) {A B : Op S} (hA : A ∈ Alg X)
    (hB : B ∈ Alg Y) : Commute A B :=
  commute_of_mem_Alg_of_mem_CAR hXY hA hB.1

/-! ### Statements: the gauge transformations (Lemma 3.8(iii) and its proof) -/

/-- The proof of **Lemma 3.8(iii)**: "`$e^{\iu\varphi\cdot\widehat{\mathbf N}}\chat(g\otimes\sigma')e^{-\iu\varphi\cdot\widehat{\mathbf N}}=e^{-\iu\varphi_{\sigma'}}\chat(g\otimes\sigma')$`"
(the pilot's `gauge φ X = e^{i(φ_↑N̂_↑+φ_↓N̂_↓)} X e^{−i(φ_↑N̂_↑+φ_↓N̂_↓)}`, `gaugeOp_eq_exp`). -/
theorem gauge_chatVec_spinTensor (φ : Spin → ℝ) (g : EuclideanSpace ℂ S) (σ : Spin) :
    Fermion.Pilot.JW.gauge φ (chatVec (spinTensor g σ)) =
      Complex.exp (-(I * (φ σ : ℂ))) • chatVec (spinTensor g σ) := by
  rw [chatVec, cVec, Fermion.Pilot.JW.gauge, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul,
    show gaugeOp φ * c μ * gaugeOp (-φ) = Fermion.Pilot.JW.gauge φ (c μ) from rfl, gauge_c, smul_comm]
  by_cases h : μ.2 = σ
  · rw [h]
  · have hz : (spinTensor g σ) μ = 0 := by simp [spinTensor, h]
    simp [hz]

/-- **Lemma 3.8(iii)**: "`and these gauge transformations map every $\CAR(X)$ and $\Alg(X)$ onto itself`" — `CAR(X)`. -/
theorem gauge_image_CAR (φ : Spin → ℝ) (X : Finset S) :
    Fermion.Pilot.JW.gauge φ '' (CAR X : Set (Op S)) = CAR X := by
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact gauge_mem_CAR φ hA
  · intro hB
    exact ⟨Fermion.Pilot.JW.gauge (-φ) B, gauge_mem_CAR (-φ) hB, gauge_gauge_neg φ B⟩

/-- **Lemma 3.8(iii)**: "`and these gauge transformations map every $\CAR(X)$ and $\Alg(X)$ onto itself`" — `Alg(X)`. -/
theorem gauge_image_Alg (φ : Spin → ℝ) (X : Finset S) :
    Fermion.Pilot.JW.gauge φ '' Alg X = Alg X := by
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨gauge_mem_CAR φ hA.1, isEven_gauge φ hA.2⟩
  · intro hB
    exact ⟨Fermion.Pilot.JW.gauge (-φ) B, ⟨gauge_mem_CAR (-φ) hB.1, isEven_gauge (-φ) hB.2⟩,
      gauge_gauge_neg φ B⟩

/-! ### Statements: the sector vocabulary on any Jordan–Wigner space (block A's Lemma 2.6(ii), generalized) -/

/-- Block A's `isSectorPreserving_iff_commute`, for any `S`: commuting with `N̂_↑`, `N̂_↓` if and only if commuting with
every `P̂_𝐧`. -/
theorem isSectorPreservingS_iff_commute (A : Op S) :
    IsSectorPreservingS A ↔ ∀ nn : SectorLabelS S, Commute A (PsecS nn) := by
  rw [isSectorPreservingS_iff_entries]
  simp_rw [PsecS_eq_diag, commute_diagonal_iff, secIndS]
  constructor
  · intro h nn i j
    by_cases hA : A i j = 0
    · simp [hA]
    · rw [h i j hA]; ring
  · intro h i j hA
    have := h (secOfS j) i j
    simp only [if_true] at this
    by_contra hne
    rw [if_neg hne, mul_one, zero_mul] at this
    exact hA this

/-- Block A's `isSectorPreserving_iff_sum`, for any `S`: `A = Σ_𝐧 P̂_𝐧 A P̂_𝐧`. -/
theorem isSectorPreservingS_iff_sum (A : Op S) :
    IsSectorPreservingS A ↔ A = ∑ nn : SectorLabelS S, PsecS nn * A * PsecS nn := by
  rw [isSectorPreservingS_iff_entries]
  have hsum : ∀ i j, (∑ nn : SectorLabelS S, PsecS nn * A * PsecS nn) i j =
      if secOfS i = secOfS j then A i j else 0 := by
    intro i j
    rw [Matrix.sum_apply]
    have hterm : ∀ nn : SectorLabelS S, (PsecS nn * A * PsecS nn) i j =
        if secOfS i = nn ∧ secOfS j = nn then A i j else 0 := by
      intro nn
      rw [PsecS_eq_diag, Matrix.mul_diagonal, Matrix.diagonal_mul, secIndS, secIndS]
      by_cases h1 : secOfS i = nn <;> by_cases h2 : secOfS j = nn <;> simp [h1, h2]
    simp_rw [hterm]
    rw [Finset.sum_eq_single (secOfS i)]
    · by_cases h : secOfS i = secOfS j
      · simp [h]
      · simp [h, Ne.symm h]
    · intro b _ hb; rw [ite_eq_right (fun h => hb h.1.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  constructor
  · intro h
    ext i j
    rw [hsum]
    by_cases hA : A i j = 0
    · simp [hA]
    · rw [if_pos (h i j hA)]
  · intro h i j hA
    have := congrFun (congrFun h i) j
    rw [hsum] at this
    by_contra hne
    rw [if_neg hne] at this
    exact hA this

/-- Block A's `IsSectorPreserving.isEven`, for any `S`. -/
theorem IsSectorPreservingS.isEven {A : Op S} (hA : IsSectorPreservingS A) : IsEven A := by
  rw [isSectorPreservingS_iff_entries] at hA
  rw [IsEven, Fermion.Pilot.JW.parityOp_eq_diagonal, commute_diagonal_iff]
  intro i j
  by_cases h : A i j = 0
  · simp [h]
  · have hs := (secOfS_eq_iff i (secOfS j)).mp (hA i j h)
    have occ_eq : ∀ m : Conf S, Fermion.Pilot.JW.occ m = ctS .up m + ctS .dn m := by
      intro m
      have := Fermion.Pilot.JW.card_occ_split m
      exact_mod_cast this
    rw [occ_eq, occ_eq, hs.1, hs.2, mul_comm]
    rfl

/-- The proof of **Lemma 3.8(iii)**: commuting with `N̂_↑` and `N̂_↓` is invariance under every gauge transformation
("`If $A$ is sector-preserving, then $A$ commutes with $e^{\iu\varphi\cdot\mathbf N}$`", and the converse: "`(differentiate at $\varphi'=0$)`"). -/
theorem isSectorPreservingS_iff_gauge (A : Op S) :
    IsSectorPreservingS A ↔ ∀ φ : Spin → ℝ, Fermion.Pilot.JW.gauge φ A = A := by
  rw [isSectorPreservingS_iff_entries]
  constructor
  · intro h φ
    ext i j
    rw [gauge_apply]
    by_cases hA : A i j = 0
    · simp [hA]
    · have hs := (secOfS_eq_iff i (secOfS j)).mp (h i j hA)
      have hup : ctS .up i = ctS .up j := hs.1
      have hdn : ctS .dn i = ctS .dn j := hs.2
      rw [gaugePhase_eq, gaugePhase_eq, hup, hdn]
      simp
  · intro h i j hA
    have key : ∀ σ : Spin, ctS σ i = ctS σ j := by
      intro σ
      refine eq_of_forall_exp_eq_one fun θ => ?_
      have e := congrFun (congrFun (h fun τ => if τ = σ then θ else 0) i) j
      rw [gauge_apply, gaugePhase_eq, gaugePhase_eq] at e
      have e1 := mul_right_cancel₀ hA (e.trans (one_mul (A i j)).symm)
      refine Eq.trans ?_ e1
      congr 1
      cases σ <;> simp <;> ring
    rw [secOfS_eq_iff]
    exact ⟨key .up, key .dn⟩

end Generic

/-! ## The physical side as an instance (bridges to block A) -/

section PhysicalBridges

variable (T : Torus)

/-- Block A's `toCLM` is `opCLM` at `S = ZMod N_φ`. -/
theorem toCLM_eq_opCLM (A : FockOp T) : toCLM T A = opCLM A :=
  rfl

/-- Block A's `c(f)` is `chatVec` at `S = ZMod N_φ`. -/
theorem cf_eq_chatVec (f : Space2 T) : cf T f = chatVec f :=
  rfl

/-- Block A's sector-preserving (`[A, N_↑] = [A, N_↓] = 0` with `N_σ = Σ_j n_{jσ}`) is `IsSectorPreservingS` at
`S = ZMod N_φ`. -/
theorem isSectorPreserving_iff_S (A : FockOp T) : IsSectorPreserving T A ↔ IsSectorPreservingS A := by
  rw [IsSectorPreserving, IsSectorPreservingS, Nsig_eq_numberOp, Nsig_eq_numberOp]

end PhysicalBridges

/-! ## The slot side: the space, the slot distance and the fattenings -/

section Slots

/-- **Definition 3.7**: "`The \emph{slot Fock space} is $\FockS:=\Ff(\ell^2(\Slots)\otimes\C^2)$`" — as `ℂ^{Conf 𝒮}`
with the occupation basis (the pilot's space at `S := Slot δ₀ T`). -/
abbrev SlotFock (δ₀ : ℝ) (T : Torus) : Type := EuclideanSpace ℂ (Conf (Slot δ₀ T))

/-- Operators on `𝔉_𝒮`, as matrices in the occupation basis. -/
abbrev SlotOp (δ₀ : ℝ) (T : Torus) : Type := Op (Slot δ₀ T)

/-- **Definition 3.1**: "`$d(s,s'):=d(\cen s,\cen{s'})$`", the flat distance of the centres. -/
def slotDist (δ₀ : ℝ) (T : Torus) (s s' : Slot δ₀ T) : ℝ :=
  flatDist T (centre δ₀ T s) (centre δ₀ T s')

/-- **Definition 3.7**: "`For $r\ge0$ the \emph{$r$-fattening} of $X$ is $\fat Xr:=\{s\in\Slots:d(s,X)\le r\}$`", with
`d(s, X) ≤ r` written as `∃ s' ∈ X, d(s, s') ≤ r` (`mem_fat_iff_inf'`: the same as `min_{s'∈X} d(s, s') ≤ r` for
nonempty `X`, Definition 3.1's "`$d(X,Y):=\min\{d(s,s'):s\in X,\ s'\in Y\}$`"). Defined for every real `r`. -/
def fat {δ₀ : ℝ} {T : Torus} (X : Finset (Slot δ₀ T)) (r : ℝ) : Finset (Slot δ₀ T) :=
  Finset.univ.filter fun s => ∃ s' ∈ X, slotDist δ₀ T s s' ≤ r

variable {δ₀ : ℝ} {T : Torus}

/-! ### Proof devices for the fattenings (phase (b); not statements of the paper)

The periodic distance is the quotient norm of `ℝ/Pℤ` (`QuotientAddGroup.norm_mk`), hence subadditive, and has the
explicit form `|u − round(u/P)P|` (`SlotFrame.Analysis.infDist_zmultiples_eq`); the flat distance satisfies the
triangle inequality (Minkowski in the plane); distinct slots have distinct centres on the torus. -/

theorem pdist_add_le (P u v : ℝ) : pdist P (u + v) ≤ pdist P u + pdist P v := by
  unfold pdist
  rw [← QuotientAddGroup.norm_mk, ← QuotientAddGroup.norm_mk, ← QuotientAddGroup.norm_mk, QuotientAddGroup.mk_add]
  exact norm_add_le _ _

theorem pdist_nonneg (P u : ℝ) : 0 ≤ pdist P u :=
  Metric.infDist_nonneg

theorem pdist_zero (P : ℝ) : pdist P 0 = 0 :=
  Metric.infDist_zero_of_mem (AddSubgroup.zero_mem _)

theorem flatDist_self (r : ℝ × ℝ) : flatDist T r r = 0 := by
  simp [flatDist, pdist_zero]

theorem flatDist_triangle (r r' r'' : ℝ × ℝ) :
    flatDist T r r'' ≤ flatDist T r r' + flatDist T r' r'' := by
  unfold flatDist
  set a := pdist T.Lx (r.1 - r'.1)
  set b := pdist T.Ly (r.2 - r'.2)
  set a' := pdist T.Lx (r'.1 - r''.1)
  set b' := pdist T.Ly (r'.2 - r''.2)
  have ha : 0 ≤ a := pdist_nonneg _ _
  have hb : 0 ≤ b := pdist_nonneg _ _
  have ha' : 0 ≤ a' := pdist_nonneg _ _
  have hb' : 0 ≤ b' := pdist_nonneg _ _
  have hx : pdist T.Lx (r.1 - r''.1) ≤ a + a' := by
    have := pdist_add_le T.Lx (r.1 - r'.1) (r'.1 - r''.1)
    rwa [sub_add_sub_cancel] at this
  have hy : pdist T.Ly (r.2 - r''.2) ≤ b + b' := by
    have := pdist_add_le T.Ly (r.2 - r'.2) (r'.2 - r''.2)
    rwa [sub_add_sub_cancel] at this
  set s1 := Real.sqrt (a ^ 2 + b ^ 2)
  set s2 := Real.sqrt (a' ^ 2 + b' ^ 2)
  have hs1 : 0 ≤ s1 := Real.sqrt_nonneg _
  have hs2 : 0 ≤ s2 := Real.sqrt_nonneg _
  have hs1sq : s1 ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hs2sq : s2 ^ 2 = a' ^ 2 + b' ^ 2 := Real.sq_sqrt (by positivity)
  have hCS : a * a' + b * b' ≤ s1 * s2 := by
    have h1 : (a * a' + b * b') ^ 2 ≤ (s1 * s2) ^ 2 := by
      rw [mul_pow, hs1sq, hs2sq]
      nlinarith [sq_nonneg (a * b' - a' * b)]
    exact (abs_le_of_sq_le_sq' h1 (mul_nonneg hs1 hs2)).2
  calc Real.sqrt (pdist T.Lx (r.1 - r''.1) ^ 2 + pdist T.Ly (r.2 - r''.2) ^ 2)
      ≤ Real.sqrt ((a + a') ^ 2 + (b + b') ^ 2) := by
        apply Real.sqrt_le_sqrt
        have h1 := pow_le_pow_left₀ (pdist_nonneg _ _) hx 2
        have h2 := pow_le_pow_left₀ (pdist_nonneg _ _) hy 2
        linarith
    _ ≤ Real.sqrt ((s1 + s2) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
    _ = s1 + s2 := Real.sqrt_sq (add_nonneg hs1 hs2)

theorem slotDist_self (s : Slot δ₀ T) : slotDist δ₀ T s s = 0 :=
  flatDist_self _

theorem slotDist_triangle (s t u : Slot δ₀ T) :
    slotDist δ₀ T s u ≤ slotDist δ₀ T s t + slotDist δ₀ T t u :=
  flatDist_triangle _ _ _

/-- A periodic distance `|(a − a')L/n|_L` with `a, a' < n` vanishes only for `a = a'`. -/
theorem eq_of_pdist_mul_eq_zero {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) {a a' : ℕ} (ha : a < n)
    (ha' : a' < n) (h : pdist L ((a : ℝ) * (L / n) - (a' : ℝ) * (L / n)) = 0) : a = a' := by
  unfold pdist at h
  rw [HRTorus.SlotFrame.Analysis.infDist_zmultiples_eq, abs_eq_zero, sub_eq_zero] at h
  set k : ℤ := round (L⁻¹ * ((a : ℝ) * (L / n) - (a' : ℝ) * (L / n)))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ((a : ℝ) - (a' : ℝ)) = (k : ℝ) * n := by
    have h' : ((a : ℝ) - (a' : ℝ)) * (L / n) = (k : ℝ) * L := by rw [← h]; ring
    field_simp at h'
    linarith [h']
  have e' : ((a : ℤ) - (a' : ℤ)) = k * n := by exact_mod_cast e
  have hdvd : (n : ℤ) ∣ ((a : ℤ) - (a' : ℤ)) := ⟨k, by rw [e', mul_comm]⟩
  have hlt : |((a : ℤ) - (a' : ℤ))| < n := by
    rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  omega

theorem eq_of_slotDist_le_zero {s s' : Slot δ₀ T} (h : slotDist δ₀ T s s' ≤ 0) : s = s' := by
  unfold slotDist flatDist at h
  have hsum : pdist T.Lx ((centre δ₀ T s).1 - (centre δ₀ T s').1) ^ 2 +
      pdist T.Ly ((centre δ₀ T s).2 - (centre δ₀ T s').2) ^ 2 ≤ 0 :=
    Real.sqrt_eq_zero'.mp (le_antisymm h (Real.sqrt_nonneg _))
  have h1 := sq_nonneg (pdist T.Lx ((centre δ₀ T s).1 - (centre δ₀ T s').1))
  have h2 := sq_nonneg (pdist T.Ly ((centre δ₀ T s).2 - (centre δ₀ T s').2))
  have hx0 : pdist T.Lx ((centre δ₀ T s).1 - (centre δ₀ T s').1) = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm (by linarith) h1)
  have hy0 : pdist T.Ly ((centre δ₀ T s).2 - (centre δ₀ T s').2) = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm (by linarith) h2)
  have hnx : 0 < nx δ₀ T := Fin.pos s.1
  have hny : 0 < ny δ₀ T := Fin.pos s.2
  have e1 : (s.1 : ℕ) = (s'.1 : ℕ) := by
    refine eq_of_pdist_mul_eq_zero T.Lx_pos hnx s.1.isLt s'.1.isLt ?_
    simpa [centre, xa, δx] using hx0
  have e2 : (s.2 : ℕ) = (s'.2 : ℕ) := by
    refine eq_of_pdist_mul_eq_zero T.Ly_pos hny s.2.isLt s'.2.isLt ?_
    simpa [centre, yl, δy] using hy0
  exact Prod.ext (Fin.ext e1) (Fin.ext e2)

/-- Membership in the fattening. -/
theorem mem_fat {X : Finset (Slot δ₀ T)} {r : ℝ} {s : Slot δ₀ T} :
    s ∈ fat X r ↔ ∃ s' ∈ X, slotDist δ₀ T s s' ≤ r := by
  simp [fat]

/-- For nonempty `X`, `s ∈ X^{(r)}` if and only if `d(s, X) = min_{s' ∈ X} d(s, s') ≤ r`. -/
theorem mem_fat_iff_inf' {X : Finset (Slot δ₀ T)} (hX : X.Nonempty) (r : ℝ) (s : Slot δ₀ T) :
    s ∈ fat X r ↔ X.inf' hX (slotDist δ₀ T s) ≤ r := by
  rw [mem_fat, Finset.inf'_le_iff]

/-- `X ⊆ X^{(r)}` for `r ≥ 0`. -/
theorem subset_fat (X : Finset (Slot δ₀ T)) {r : ℝ} (hr : 0 ≤ r) : X ⊆ fat X r := by
  intro s hs
  rw [mem_fat]
  exact ⟨s, hs, by rw [slotDist_self]; exact hr⟩

/-- The fattening is monotone in `X`. -/
theorem fat_mono_left {X Y : Finset (Slot δ₀ T)} (hXY : X ⊆ Y) (r : ℝ) : fat X r ⊆ fat Y r := by
  intro s hs
  rw [mem_fat] at hs ⊢
  obtain ⟨s', hs', hd⟩ := hs
  exact ⟨s', hXY hs', hd⟩

/-- The fattening is monotone in `r`. -/
theorem fat_mono_right (X : Finset (Slot δ₀ T)) {r r' : ℝ} (hrr : r ≤ r') : fat X r ⊆ fat X r' := by
  intro s hs
  rw [mem_fat] at hs ⊢
  obtain ⟨s', hs', hd⟩ := hs
  exact ⟨s', hs', hd.trans hrr⟩

/-- `(X^{(r)})^{(r')} ⊆ X^{(r+r')}` (the triangle inequality of the flat distance). -/
theorem fat_fat_subset (X : Finset (Slot δ₀ T)) (r r' : ℝ) : fat (fat X r) r' ⊆ fat X (r + r') := by
  intro s hs
  rw [mem_fat] at hs ⊢
  obtain ⟨t, ht, hst⟩ := hs
  rw [mem_fat] at ht
  obtain ⟨u, hu, htu⟩ := ht
  exact ⟨u, hu, (slotDist_triangle s t u).trans (by linarith)⟩

/-- `X^{(0)} = X` (distinct slots have distinct centres on the torus). -/
theorem fat_zero (X : Finset (Slot δ₀ T)) : fat X 0 = X := by
  apply Finset.Subset.antisymm
  · intro s hs
    rw [mem_fat] at hs
    obtain ⟨s', hs', hd⟩ := hs
    rwa [eq_of_slotDist_le_zero hd]
  · exact subset_fat X le_rfl

end Slots

end HRTorus.Fock
