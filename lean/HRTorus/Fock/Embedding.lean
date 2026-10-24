import HRTorus.Fock.Slot
import HRTorus.LLL.Frame
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# The embedding `ι` of the physical Fock space into the slot Fock space (T-0056 block B, `Fock.Embedding`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **The definitions and statements were written
first and reviewed against the paper (phase (a)) and are unchanged; phase (b) added the proofs and the proof
devices, each marked as such (in its section's header or its docstring). Every theorem is proved; there is no
`sorry`. One route departure, ruled at review: Lemma 3.8(iii)'s approximant in the sector-preserving case is the
average of the gauge conjugations over a finite grid of phases (the pinching), not the paper's integral over the
torus of phases (`ApproxDevices`).** The paper: the HR paper, `papers/hr/sections/03-slot-frame.tex` — the
second half of Definition 3.7 `def:slotfock` (the embedding `ι`) and Lemma 3.8 `lem:embedding` with its proof.

## The model (R-0021: the concrete Jordan–Wigner Fock spaces on both sides)

* `𝔉(𝒮) : 𝓗_N → 𝔉_𝒮` (`FfA`) is block A's `secondQuant` of the matrix of `𝒮 ⊗ 1` (`anaMat`, the matrix of
  `LLL.analysis2` in the bases `ψ_j ⊗ σ` and `δ_s ⊗ σ`): the formula of the proof of Lemma 3.8(i) on the occupation
  basis, already rectangular in block A.
* **`ι` is a definition** (`iota`). The paper's route builds a unitary `𝒱 : 𝔉_𝒮 → 𝓗_N ⊗ 𝔉(𝔯^⊥)` from an orthonormal
  basis `g_1, …, g_{n₂}` of `ℓ²(𝒮) ⊗ ℂ²` whose first `n₁ = 2N_φ` vectors are the `𝒮f_i`, and puts
  `ι(A) := 𝒱^*(A ⊗ 1)𝒱`. Here the same idea in the Jordan–Wigner matrices:
  - the physical modes are sent onto the **initial segment of the slot modes in the Jordan–Wigner order** (`segEmb`:
    the slot mode whose number under the pilot's `num` is the physical mode's number), so that the Jordan–Wigner sign
    of a segment mode, which counts only modes numbered before it, is the physical sign (`ampl_c`) — the paper's
    "`$c(f_i)$ acts on the $e_{\mathbf m'}$ by the same formula, with the same sign, which involves only $m_1,\dots,m_{i-1}$`";
  - `A ⊠ 1` (`ampl`) acts as `A` on the occupations of the segment and as the identity on the other occupations,
    written entrywise in the configuration basis;
  - `U` (`embedU`) is a unitary on `ℓ²(𝒮) ⊗ ℂ²` whose column at the segment mode of `μ` is `𝒮δ_μ` (the rest of its
    columns an orthonormal basis of `(ran 𝒮)^⊥`), chosen noncomputably among the unitaries with that property
    (`embedU_spec`: one exists for every admissible torus, by Parseval);
  - `ι(A) := 𝔉(U) (A ⊠ 1) 𝔉(U)^*` (`iota`), with `𝔉(U)` block A's `secondQuant`.
  The definition makes no use of the hypotheses: when `2N_φ > 2|𝒮|` it is `0`, and when no unitary with the required
  columns exists `U := 1`; every statement assumes an admissible torus, `0 < δ₀` and a profile `η`, where neither
  happens. **Uniqueness** (`iota_unique`) makes `ι` canonical: it does not depend on `num`, on `U`, or on the segment.
* Operator norms are `‖opCLM ·‖` on both sides (block A's convention; `toCLM T A = opCLM A`).
* Lemma 3.8(ii)'s functional calculus is Mathlib's `cfc` over `ℝ` for self-adjoint matrices (the instance block A's
  `Psec_eq_cfc` and `specProj_sector` use); `e^{±itH}` is `NormedSpace.exp` of `(±it)H`, as the pilot's `gaugeOp_eq_exp`.
-/

open scoped InnerProductSpace Matrix
open Complex (I)

noncomputable section

namespace HRTorus.Fock

open HRTorus.SlotFrame HRTorus.LLL
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op num c chat numberOp parityOp gaugeOp IsEven CAR Alg)

/-! ## The Jordan–Wigner initial segment and `A ⊠ 1` (any finite `S`, `S'`) -/

section Segment

variable {S S' : Type*} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']

/-- The initial segment of the modes of `S'` in the Jordan–Wigner order: for `#modes(S) ≤ #modes(S')`, the mode `ν`
of `S'` with `num ν = num μ` (the pilot's fixed numberings on both sides). -/
def segEmb (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (μ : Mode S) : Mode S' :=
  num.symm (Fin.castLE h (num μ))

/-- The occupations of the segment, as a configuration of `S`. -/
def segRestr (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (m : Conf S') : Conf S :=
  fun μ => m (segEmb h μ)

/-- `A ⊠ 1`: the operator on `ℂ^{Conf S'}` acting as `A` on the occupations of the segment and as the identity on
the occupations of the other modes (those numbered `≥ #modes(S)`): its entry at `(m', m)` is
`A (m'|_seg) (m|_seg)` if `m'` and `m` agree off the segment, `0` otherwise. -/
def ampl (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (A : Op S) : Op S' :=
  Matrix.of fun m' m =>
    if ∀ ν : Mode S', Fintype.card (Mode S) ≤ ((num ν : Fin (Fintype.card (Mode S'))) : ℕ) → m' ν = m ν then
      A (segRestr h m') (segRestr h m)
    else 0

/-! ### Proof devices for the construction (phase (b); not statements of the paper)

`OffEq h m' m`: the two configurations agree off the segment (the condition in `ampl`); `segPre` the physical mode of a
segment mode; `glue h κ m` the configuration that is `κ` on the segment and `m` off it. A sum over the configurations
that agree with a given one off the segment is a sum over the physical configurations (`sum_offEq`); the Jordan–Wigner
count of a segment mode is the physical count (`cnt_segEmb`). -/

section SegmentDevices

/-- The two configurations agree off the segment. -/
abbrev OffEq (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (m' m : Conf S') : Prop :=
  ∀ ν : Mode S', Fintype.card (Mode S) ≤ ((num ν : Fin (Fintype.card (Mode S'))) : ℕ) → m' ν = m ν

theorem ampl_apply (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (A : Op S) (m' m : Conf S') :
    ampl h A m' m = if OffEq h m' m then A (segRestr h m') (segRestr h m) else 0 :=
  rfl

theorem segEmb_num (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (μ : Mode S) :
    ((num (segEmb h μ) : Fin (Fintype.card (Mode S'))) : ℕ) = ((num μ : Fin (Fintype.card (Mode S))) : ℕ) := by
  simp [segEmb]

theorem segEmb_num_lt (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (μ : Mode S) :
    ((num (segEmb h μ) : Fin (Fintype.card (Mode S'))) : ℕ) < Fintype.card (Mode S) := by
  rw [segEmb_num]
  exact (num μ).isLt

/-- The physical mode of a segment mode. -/
def segPre (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (ν : Mode S')
    (hν : ((num ν : Fin (Fintype.card (Mode S'))) : ℕ) < Fintype.card (Mode S)) : Mode S :=
  num.symm ⟨num ν, hν⟩

theorem segEmb_segPre (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (ν : Mode S')
    (hν : ((num ν : Fin (Fintype.card (Mode S'))) : ℕ) < Fintype.card (Mode S)) : segEmb h (segPre h ν hν) = ν := by
  apply num.injective
  apply Fin.ext
  simp [segEmb, segPre]

theorem segPre_segEmb (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (μ : Mode S) :
    segPre h (segEmb h μ) (segEmb_num_lt h μ) = μ := by
  apply num.injective
  apply Fin.ext
  simp [segEmb, segPre]

theorem segEmb_inj (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) {μ μ' : Mode S}
    (e : segEmb h μ = segEmb h μ') : μ = μ' := by
  have := congrArg (fun ν => ((num ν : Fin (Fintype.card (Mode S'))) : ℕ)) e
  simp only [segEmb_num] at this
  exact num.injective (Fin.ext this)

theorem ne_segEmb_of_le (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) {ν : Mode S'}
    (hν : Fintype.card (Mode S) ≤ ((num ν : Fin (Fintype.card (Mode S'))) : ℕ)) (μ : Mode S) : ν ≠ segEmb h μ := by
  rintro rfl
  exact absurd (segEmb_num_lt h μ) (not_lt.mpr hν)

/-- The configuration that is `κ` on the segment and `m` off it. -/
def glue (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (κ : Conf S) (m : Conf S') : Conf S' :=
  fun ν => if hν : ((num ν : Fin (Fintype.card (Mode S'))) : ℕ) < Fintype.card (Mode S) then κ (segPre h ν hν)
    else m ν

theorem glue_segEmb (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (κ : Conf S) (m : Conf S') (μ : Mode S) :
    glue h κ m (segEmb h μ) = κ μ := by
  rw [glue, dif_pos (segEmb_num_lt h μ), segPre_segEmb]

theorem segRestr_glue (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (κ : Conf S) (m : Conf S') :
    segRestr h (glue h κ m) = κ :=
  funext fun μ => glue_segEmb h κ m μ

theorem offEq_glue (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (κ : Conf S) (m : Conf S') :
    OffEq h (glue h κ m) m := by
  intro ν hν
  rw [glue, dif_neg (not_lt.mpr hν)]

theorem offEq_symm (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) {m' m : Conf S'} (hm : OffEq h m' m) :
    OffEq h m m' :=
  fun ν hν => (hm ν hν).symm

theorem offEq_trans (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) {m₁ m₂ m₃ : Conf S'}
    (h₁ : OffEq h m₁ m₂) (h₂ : OffEq h m₂ m₃) : OffEq h m₁ m₃ :=
  fun ν hν => (h₁ ν hν).trans (h₂ ν hν)

theorem eq_of_segRestr_eq (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) {m' m : Conf S'}
    (h1 : segRestr h m' = segRestr h m) (h2 : OffEq h m' m) : m' = m := by
  funext ν
  by_cases hν : ((num ν : Fin (Fintype.card (Mode S'))) : ℕ) < Fintype.card (Mode S)
  · have := congrFun h1 (segPre h ν hν)
    simpa only [segRestr, segEmb_segPre] using this
  · exact h2 ν (not_lt.mp hν)

theorem glue_segRestr (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) {m' m : Conf S'} (hm : OffEq h m' m) :
    glue h (segRestr h m') m = m' :=
  eq_of_segRestr_eq h (segRestr_glue h _ m) (offEq_trans h (offEq_glue h _ m) (offEq_symm h hm))

theorem glue_injective (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (m : Conf S') :
    Function.Injective fun κ : Conf S => glue h κ m := by
  intro κ κ' e
  have := congrArg (segRestr h) e
  simpa only [segRestr_glue] using this

theorem segRestr_update_segEmb (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (m : Conf S') (μ : Mode S)
    (b : Bool) : segRestr h (Function.update m (segEmb h μ) b) = Function.update (segRestr h m) μ b := by
  funext μ'
  by_cases e : μ' = μ
  · subst e
    simp [segRestr]
  · simp only [segRestr]
    rw [Function.update_of_ne (fun h' => e (segEmb_inj h h')), Function.update_of_ne e]
    rfl

theorem offEq_update_segEmb (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (m : Conf S') (μ : Mode S)
    (b : Bool) : OffEq h (Function.update m (segEmb h μ) b) m := by
  intro ν hν
  rw [Function.update_of_ne (ne_segEmb_of_le h hν μ)]

/-- A sum over the configurations of `S'` of a function that vanishes unless the configuration agrees with `m'` off the
segment is a sum over the configurations of `S`. -/
theorem sum_offEq (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (m' : Conf S') (F : Conf S' → ℂ)
    (hF : ∀ k, ¬ OffEq h m' k → F k = 0) : ∑ k, F k = ∑ κ : Conf S, F (glue h κ m') := by
  rw [← Finset.sum_image (s := Finset.univ) (g := fun κ : Conf S => glue h κ m') (f := F)
    (fun κ _ κ' _ e => glue_injective h m' e)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  apply hF k
  intro hoff
  apply hk
  rw [Finset.mem_image]
  exact ⟨segRestr h k, Finset.mem_univ _, glue_segRestr h (offEq_symm h hoff)⟩

/-- The Jordan–Wigner count of a segment mode is the physical one. -/
theorem cnt_segEmb (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (μ : Mode S) (m : Conf S') :
    Fermion.Pilot.JW.cnt (segEmb h μ) m = Fermion.Pilot.JW.cnt μ (segRestr h m) := by
  unfold Fermion.Pilot.JW.cnt
  rw [← Finset.card_image_of_injective _ (fun μ₁ μ₂ e => segEmb_inj h e)]
  congr 1
  ext ν
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hlt, hm⟩
    have hlt' : ((num ν : Fin (Fintype.card (Mode S'))) : ℕ) < ((num μ : Fin (Fintype.card (Mode S))) : ℕ) := by
      rw [← segEmb_num h μ]
      exact hlt
    have hν : ((num ν : Fin (Fintype.card (Mode S'))) : ℕ) < Fintype.card (Mode S) := hlt'.trans (num μ).isLt
    refine ⟨segPre h ν hν, ⟨?_, ?_⟩, segEmb_segPre h ν hν⟩
    · rw [Fin.lt_def, ← segEmb_num h (segPre h ν hν), segEmb_segPre]
      exact hlt'
    · show m (segEmb h (segPre h ν hν)) = true
      rw [segEmb_segPre]
      exact hm
  · rintro ⟨μ', ⟨hlt, hm⟩, rfl⟩
    refine ⟨?_, hm⟩
    rw [Fin.lt_def, segEmb_num, segEmb_num]
    exact hlt

end SegmentDevices

/-! ### Statements: the construction (model statements, not the paper's; the route to Lemma 3.8) -/

/-- The segment map is injective. -/
theorem segEmb_injective (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) :
    Function.Injective (segEmb (S := S) (S' := S') h) :=
  fun _ _ e => segEmb_inj h e

/-- The segment map preserves the Jordan–Wigner numbers. -/
theorem num_segEmb (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (μ : Mode S) :
    ((num (segEmb h μ) : Fin (Fintype.card (Mode S'))) : ℕ) = ((num μ : Fin (Fintype.card (Mode S))) : ℕ) :=
  segEmb_num h μ

/-- The segment is the initial segment: `ν` is in the image if and only if `num ν < #modes(S)`. -/
theorem exists_segEmb_eq_iff (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (ν : Mode S') :
    (∃ μ : Mode S, segEmb h μ = ν) ↔ ((num ν : Fin (Fintype.card (Mode S'))) : ℕ) < Fintype.card (Mode S) := by
  constructor
  · rintro ⟨μ, rfl⟩
    exact segEmb_num_lt h μ
  · intro hν
    exact ⟨segPre h ν hν, segEmb_segPre h ν hν⟩

/-- `A ⊠ 1` is unital. -/
theorem ampl_one (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) : ampl h (1 : Op S) = (1 : Op S') := by
  ext m' m
  rw [ampl_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases e : m' = m
  · subst e
    rw [if_pos (show OffEq h m' m' from fun _ _ => rfl), if_pos rfl, if_pos rfl]
  · rw [if_neg e]
    split_ifs with hoff hr
    · exact absurd (eq_of_segRestr_eq h hr hoff) e
    · rfl
    · rfl

/-- `A ⊠ 1` is multiplicative. -/
theorem ampl_mul (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (A B : Op S) :
    ampl h (A * B) = ampl h A * ampl h B := by
  ext m' m
  rw [Matrix.mul_apply, ampl_apply]
  simp only [ampl_apply]
  by_cases hm : OffEq h m' m
  · rw [if_pos hm, Matrix.mul_apply, sum_offEq h m' _ ?hF]
    · refine Finset.sum_congr rfl fun κ _ => ?_
      rw [if_pos (offEq_symm h (offEq_glue h κ m')), if_pos (offEq_trans h (offEq_glue h κ m') hm),
        segRestr_glue]
    · intro k hk
      rw [if_neg hk, zero_mul]
  · rw [if_neg hm]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : OffEq h m' k
    · rw [if_neg (fun h2 => hm (offEq_trans h h1 h2)), mul_zero]
    · rw [if_neg h1, zero_mul]

/-- `A ⊠ 1` is additive. -/
theorem ampl_add (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (A B : Op S) :
    ampl h (A + B) = ampl h A + ampl h B := by
  ext m' m
  simp only [ampl_apply, Matrix.add_apply]
  split_ifs <;> simp

/-- `A ⊠ 1` is linear. -/
theorem ampl_smul (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (a : ℂ) (A : Op S) :
    ampl h (a • A) = a • ampl h A := by
  ext m' m
  simp only [ampl_apply, Matrix.smul_apply]
  split_ifs <;> simp

/-- `A ⊠ 1` is star-preserving. -/
theorem ampl_conjTranspose (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (A : Op S) :
    ampl h Aᴴ = (ampl h A)ᴴ := by
  ext m' m
  rw [Matrix.conjTranspose_apply, ampl_apply, ampl_apply, Matrix.conjTranspose_apply]
  by_cases hoff : OffEq h m' m
  · rw [if_pos hoff, if_pos (offEq_symm h hoff)]
  · rw [if_neg hoff, if_neg (fun h' => hoff (offEq_symm h h')), star_zero]

/-- **The signs come out exactly**: `c_μ ⊠ 1` is the Jordan–Wigner annihilator of the segment mode of `μ` — the proof
of Lemma 3.8: "`$c(f_i)$ acts on the $e_{\mathbf m'}$ by the same formula, with the same sign, which involves only $m_1,\dots,m_{i-1}$`". -/
theorem ampl_c (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (μ : Mode S) :
    ampl h (c μ) = c (segEmb h μ) := by
  ext m' m
  rw [ampl_apply, Fermion.Pilot.JW.c_apply, Fermion.Pilot.JW.c_apply]
  have key : (OffEq h m' m ∧ (segRestr h m μ = true ∧ segRestr h m' = Function.update (segRestr h m) μ false)) ↔
      (m (segEmb h μ) = true ∧ m' = Function.update m (segEmb h μ) false) := by
    constructor
    · rintro ⟨hoff, h1, h2⟩
      refine ⟨h1, eq_of_segRestr_eq h ?_ ?_⟩
      · rw [h2, segRestr_update_segEmb]
      · intro ν hν
        rw [hoff ν hν, Function.update_of_ne (ne_segEmb_of_le h hν μ)]
    · rintro ⟨h1, rfl⟩
      exact ⟨offEq_update_segEmb h m μ false, h1, segRestr_update_segEmb h m μ false⟩
  by_cases hc : m (segEmb h μ) = true ∧ m' = Function.update m (segEmb h μ) false
  · obtain ⟨hoff, hin⟩ := key.mpr hc
    rw [if_pos hoff, if_pos hin, if_pos hc, Fermion.Pilot.JW.jwSign_eq, Fermion.Pilot.JW.jwSign_eq, cnt_segEmb]
  · rw [if_neg hc]
    split_ifs with hoff hin
    · exact absurd (key.mp ⟨hoff, hin⟩) hc
    · rfl
    · rfl

/-! ### Proof devices after the construction's statements (phase (b); not statements of the paper) -/

section SegmentDevices2

/-- `A ⊠ 1` as a star-algebra homomorphism. -/
def amplHom (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) : Op S →⋆ₐ[ℂ] Op S' where
  toFun := ampl h
  map_one' := ampl_one h
  map_mul' := ampl_mul h
  map_zero' := by
    have := ampl_smul h 0 (0 : Op S)
    simpa using this
  map_add' := ampl_add h
  commutes' := fun r => by
    show ampl h (algebraMap ℂ (Op S) r) = algebraMap ℂ (Op S') r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ampl_smul, ampl_one]
  map_star' := fun A => by
    show ampl h (star A) = star (ampl h A)
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
    exact ampl_conjTranspose h A

theorem amplHom_apply (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (A : Op S) :
    amplHom h A = ampl h A :=
  rfl

theorem ampl_injective (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) :
    Function.Injective (ampl (S := S) (S' := S') h) := by
  intro A B e
  ext κ' κ
  have hoff : OffEq h (glue h κ' vac) (glue h κ vac) :=
    offEq_trans h (offEq_glue h κ' vac) (offEq_symm h (offEq_glue h κ vac))
  have := congrFun (congrFun e (glue h κ' vac)) (glue h κ vac)
  rwa [ampl_apply, ampl_apply, if_pos hoff, if_pos hoff, segRestr_glue, segRestr_glue] at this

/-- `cVec` of a matrix image (block A's computation inside `secondQuant_mul_cVec`). -/
theorem cVec_mulVec (U : Matrix (Mode S') (Mode S) ℂ) (g : Mode S → ℂ) :
    cVec (U *ᵥ g) = ∑ ν, star (g ν) • cVec (fun ρ => U ρ ν) := by
  simp only [cVec, Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => by rw [mul_comm]

/-- The rectangular version of block A's `secondQuant_conjTranspose_mul_self` (block A's proof, for
`U : Matrix (Mode S') (Mode S) ℂ`): the second quantization of an isometry is an isometry. -/
theorem secondQuant_conjTranspose_mul_self_rect {U : Matrix (Mode S') (Mode S) ℂ} (hU : Uᴴ * U = 1) :
    (secondQuant U)ᴴ * secondQuant U = 1 := by
  set W := secondQuant U with hW
  have hcd : ∀ ν, W * (c ν)ᴴ = (cVec fun ρ => U ρ ν)ᴴ * W := secondQuant_mul_cdag U
  have hc : ∀ ν, W * c ν = cVec (fun ρ => U ρ ν) * W := secondQuant_mul_c hU
  have h1 : ∀ ν, Commute (Wᴴ * W) (c ν) := by
    intro ν
    have e : Wᴴ * cVec (fun ρ => U ρ ν) = c ν * Wᴴ := by
      have := congrArg Matrix.conjTranspose (hcd ν)
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_conjTranspose] at this
      exact this.symm
    show Wᴴ * W * c ν = c ν * (Wᴴ * W)
    rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, e, Matrix.mul_assoc]
  have h2 : ∀ ν, Commute (Wᴴ * W) (c ν)ᴴ := by
    intro ν
    have e : Wᴴ * (cVec fun ρ => U ρ ν)ᴴ = (c ν)ᴴ * Wᴴ := by
      have := congrArg Matrix.conjTranspose (hc ν)
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at this
      exact this.symm
    show Wᴴ * W * (c ν)ᴴ = (c ν)ᴴ * (Wᴴ * W)
    rw [Matrix.mul_assoc, hcd, ← Matrix.mul_assoc, e, Matrix.mul_assoc]
  obtain ⟨a, ha⟩ := exists_smul_one_of_commute_c h1 h2
  have hvv : (Wᴴ * W) vac vac = 1 := by
    rw [Matrix.mul_apply]
    simp [Matrix.conjTranspose_apply, hW, secondQuant_apply_vac]
  rw [ha] at hvv ⊢
  have ha1 : a = 1 := by simpa using hvv
  rw [ha1, one_smul]

end SegmentDevices2

end Segment

/-! ## The second quantization of `𝒮`, the one-body unitary, and `ι` -/

section Embedding

variable (η : ℝ → ℝ) (δ₀ : ℝ) (T : Torus)

/-- The matrix of `𝒮 ⊗ 1 : 𝔨_N → ℓ²(𝒮) ⊗ ℂ²` (`LLL.analysis2`) in the bases `ψ_j ⊗ σ` and `δ_s ⊗ σ`. -/
def anaMat : Matrix (Mode (Slot δ₀ T)) (Modes T) ℂ :=
  Matrix.of fun ρ μ => analysis2 η δ₀ T (EuclideanSpace.single μ 1) ρ

/-- **Lemma 3.8(i)**: "`With $\Ff(\Sa):\Fock\to\FockS$ the second quantization of the isometry $\Sa$`" — block A's
`secondQuant` of the matrix of `𝒮 ⊗ 1`, i.e. "`$\Ff(\Sa)c(h_1)^*\cdots c(h_p)^*\Omega_0=\chat(\Sa h_1)^*\cdots\chat(\Sa h_p)^*\widehat\Omega_0$`"
on the occupation basis. -/
def FfA : Matrix (Conf (Slot δ₀ T)) (Conf (ZMod T.Nφ)) ℂ :=
  secondQuant (anaMat η δ₀ T)

open Classical in
/-- The one-body unitary `U` of the construction: a unitary on `ℓ²(𝒮) ⊗ ℂ²` whose column at the segment mode of
each physical mode `μ` is `𝒮δ_μ` (the paper's orthonormal basis `g_i`, with `g_i := 𝒮f_i` for `i ≤ n₁`, in the
Jordan–Wigner order), chosen among those that exist; `1` if none does (never on an admissible torus,
`embedU_spec`). -/
def embedU (h : Fintype.card (Modes T) ≤ Fintype.card (Mode (Slot δ₀ T))) :
    Matrix (Mode (Slot δ₀ T)) (Mode (Slot δ₀ T)) ℂ :=
  if hU : ∃ U : Matrix (Mode (Slot δ₀ T)) (Mode (Slot δ₀ T)) ℂ,
      U ∈ unitary (Matrix (Mode (Slot δ₀ T)) (Mode (Slot δ₀ T)) ℂ) ∧
        ∀ (μ : Modes T) (ρ : Mode (Slot δ₀ T)), U ρ (segEmb h μ) = anaMat η δ₀ T ρ μ
  then hU.choose
  else 1

/-- **Definition 3.7**, the embedding: "`The \emph{embedding} $\iota$ is the unital $*$-homomorphism from the operators on $\Fock$ to the operators on $\FockS$ determined by`"
"`\iota\bigl(c(f)\bigr)=\chat(\Sa f),\qquad f\in\kN`" — **defined** as `ι(A) := 𝔉(U) (A ⊠ 1) 𝔉(U)^*` (the module
docstring; the paper's `𝒱^*(A ⊗ 1)𝒱`, "`Define $\iota(A):=\mathcal V^*(A\otimes\one)\mathcal V$`"); `iota_cf`,
`exists_starAlgHom_iota` and `iota_unique` are the paper's characterization. "`For an operator $H$ on $\Fock$ we write $\Hhat:=\iota(H)$`". -/
def iota (A : FockOp T) : Op (Slot δ₀ T) :=
  if h : Fintype.card (Modes T) ≤ Fintype.card (Mode (Slot δ₀ T)) then
    secondQuant (embedU η δ₀ T h) * ampl h A * (secondQuant (embedU η δ₀ T h))ᴴ
  else 0

end Embedding

/-! ## Statements -/

section Statements

variable {η : ℝ → ℝ} {δ₀ : ℝ} {T : Torus}

/-! ### The construction (model statements, not the paper's) -/

/-- `anaMat` is the matrix of `𝒮 ⊗ 1`. -/
theorem toEuclideanLin_anaMat : Matrix.toEuclideanLin (𝕜 := ℂ) (anaMat η δ₀ T) = analysis2 η δ₀ T := by
  apply LinearMap.ext
  intro f
  conv_rhs => rw [← (EuclideanSpace.basisFun (Modes T) ℂ).sum_repr f]
  rw [map_sum]
  simp only [map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  apply PiLp.ext
  intro ρ
  rw [Matrix.toLpLin_apply]
  simp only [WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, anaMat, Matrix.of_apply]
  exact Finset.sum_congr rfl fun μ _ => mul_comm _ _

/-- On an admissible torus there are at least as many slot modes as physical modes (`2N_φ ≤ 2|𝒮|`, Proposition
3.4(i)), so the segment exists. -/
theorem card_modes_le (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) :
    Fintype.card (Modes T) ≤ Fintype.card (Mode (Slot δ₀ T)) := by
  have h1 := finrank_range_analysis2 isProfile_etaStd hδ₀ hT
  have h2 := Submodule.finrank_le (LinearMap.range (analysis2 etaStd δ₀ T))
  rw [h1, finrank_euclideanSpace] at h2
  have hs : Fintype.card Spin = 2 := rfl
  rw [Fintype.card_prod, ZMod.card, hs]
  omega

/-- On an admissible torus the one-body unitary of the construction exists: `embedU` is unitary with the
columns `𝒮δ_μ` at the segment modes (the orthonormal family `𝒮δ_μ` of Proposition 3.3 completed to a basis). -/
theorem embedU_spec (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀)
    (h : Fintype.card (Modes T) ≤ Fintype.card (Mode (Slot δ₀ T))) :
    embedU η δ₀ T h ∈ unitary (Matrix (Mode (Slot δ₀ T)) (Mode (Slot δ₀ T)) ℂ) ∧
      ∀ (μ : Modes T) (ρ : Mode (Slot δ₀ T)), embedU η δ₀ T h ρ (segEmb h μ) = anaMat η δ₀ T ρ μ := by
  classical
  have hinner : ∀ f g : Space2 T, ⟪analysis2 η δ₀ T f, analysis2 η δ₀ T g⟫_ℂ = ⟪f, g⟫_ℂ := by
    intro f g
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, adjoint_analysis2_comp_analysis2 hη hδ₀ hT,
      LinearMap.id_apply]
  have hex : ∃ U : Matrix (Mode (Slot δ₀ T)) (Mode (Slot δ₀ T)) ℂ,
      U ∈ unitary (Matrix (Mode (Slot δ₀ T)) (Mode (Slot δ₀ T)) ℂ) ∧
        ∀ (μ : Modes T) (ρ : Mode (Slot δ₀ T)), U ρ (segEmb h μ) = anaMat η δ₀ T ρ μ := by
    let v : Mode (Slot δ₀ T) → EuclideanSpace ℂ (Mode (Slot δ₀ T)) := fun ν =>
      if hν : ((num ν : Fin (Fintype.card (Mode (Slot δ₀ T)))) : ℕ) < Fintype.card (Modes T) then
        analysis2 η δ₀ T (EuclideanSpace.single (segPre h ν hν) 1) else 0
    have hv_seg : ∀ μ : Modes T, v (segEmb h μ) = analysis2 η δ₀ T (EuclideanSpace.single μ 1) := by
      intro μ
      simp only [v]
      rw [dif_pos (segEmb_num_lt h μ), segPre_segEmb]
    have hon : Orthonormal ℂ ((Set.range (segEmb h)).domRestrict v) := by
      rw [orthonormal_iff_ite]
      rintro ⟨_, μ, rfl⟩ ⟨_, μ', rfl⟩
      simp only [Set.domRestrict_apply, hv_seg, hinner, EuclideanSpace.inner_single_left, map_one, one_mul,
        PiLp.single_apply]
      by_cases e : μ = μ'
      · subst e; simp
      · rw [if_neg e, if_neg (fun h' => e (segEmb_inj h (congrArg Subtype.val h')))]
    obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (by rw [finrank_euclideanSpace]) hon
    refine ⟨(EuclideanSpace.basisFun (Mode (Slot δ₀ T)) ℂ).toBasis.toMatrix b,
      OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _, fun μ ρ => ?_⟩
    rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      hb _ ⟨μ, rfl⟩, hv_seg]
    rfl
  unfold embedU
  rw [dif_pos hex]
  exact hex.choose_spec

/-- `ι` unfolded. -/
theorem iota_eq (h : Fintype.card (Modes T) ≤ Fintype.card (Mode (Slot δ₀ T))) (A : FockOp T) :
    iota η δ₀ T A = secondQuant (embedU η δ₀ T h) * ampl h A * (secondQuant (embedU η δ₀ T h))ᴴ := by
  rw [iota, dif_pos h]

/-! ### Proof devices for `ι` (phase (b); not statements of the paper)

`ι` bundled as a star-algebra homomorphism (`iotaHom`: the conjugation by the unitary `𝔉(U)`, Mathlib's
`Unitary.conjStarAlgAut`, after `amplHom`), the parity and the gauge conjugations as star-algebra automorphisms, and
the spectral projection of a self-adjoint matrix as the orthogonal projection onto the span of its eigenvectors (block
A's `specProj_sector` without the sector). -/

section IotaDevices

theorem secondQuant_embedU_mem_unitary (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀)
    (h : Fintype.card (Modes T) ≤ Fintype.card (Mode (Slot δ₀ T))) :
    secondQuant (embedU η δ₀ T h) ∈ unitary (Op (Slot δ₀ T)) := by
  have h1 := secondQuant_conjTranspose_mul_self (conjTranspose_mul_self_of_mem_unitary (embedU_spec hη hδ₀ hT h).1)
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
  exact ⟨h1, mul_eq_one_comm.mp h1⟩

/-- `ι` as a star-algebra homomorphism. -/
def iotaHom (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) : FockOp T →⋆ₐ[ℂ] Op (Slot δ₀ T) :=
  (StarAlgHom.ofClass (Unitary.conjStarAlgAut ℂ (Op (Slot δ₀ T))
    ⟨secondQuant (embedU η δ₀ T (card_modes_le hδ₀ hT)),
      secondQuant_embedU_mem_unitary hη hδ₀ hT (card_modes_le hδ₀ hT)⟩)).comp (amplHom (card_modes_le hδ₀ hT))

theorem iotaHom_apply (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (A : FockOp T) :
    iotaHom hη hδ₀ hT A = iota η δ₀ T A := by
  rw [iota_eq (card_modes_le hδ₀ hT)]
  rfl

theorem iotaHom_injective (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) :
    Function.Injective (iotaHom hη hδ₀ hT) := by
  intro A B e
  apply ampl_injective (card_modes_le hδ₀ hT)
  exact (Unitary.conjStarAlgAut ℂ (Op (Slot δ₀ T)) _).injective e

theorem iotaHom_continuous (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) :
    Continuous (iotaHom hη hδ₀ hT) :=
  LinearMap.continuous_of_finiteDimensional (iotaHom hη hδ₀ hT).toAlgHom.toLinearMap

/-- The coordinates of `(𝒮 ⊗ 1)f` are those of `anaMat · f`. -/
theorem analysis2_coord (f : Space2 T) :
    (fun ρ => analysis2 η δ₀ T f ρ) = anaMat η δ₀ T *ᵥ (fun μ => f μ) := by
  funext ρ
  rw [← toEuclideanLin_anaMat (η := η) (δ₀ := δ₀) (T := T), Matrix.toLpLin_apply]

theorem anaMat_conjTranspose_mul_self (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) :
    (anaMat η δ₀ T)ᴴ * anaMat η δ₀ T = 1 := by
  have hinner : ∀ f g : Space2 T, ⟪analysis2 η δ₀ T f, analysis2 η δ₀ T g⟫_ℂ = ⟪f, g⟫_ℂ := by
    intro f g
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, adjoint_analysis2_comp_analysis2 hη hδ₀ hT,
      LinearMap.id_apply]
  ext μ μ'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h1 := hinner (EuclideanSpace.single μ 1) (EuclideanSpace.single μ' 1)
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, EuclideanSpace.single_apply] at h1
  rw [← h1, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Matrix.conjTranspose_apply, anaMat, Matrix.of_apply, RCLike.inner_apply, Complex.star_def]
  ring

theorem parityOp_mem_unitary {S : Type*} [Fintype S] [DecidableEq S] : (parityOp : Op S) ∈ unitary (Op S) := by
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, parityOp_conjTranspose,
    Fermion.Pilot.JW.parityOp_mul_parityOp]
  exact ⟨rfl, rfl⟩

theorem parityOp_mul_cVec_mul_parityOp {S : Type*} [Fintype S] [DecidableEq S] (g : Mode S → ℂ) :
    parityOp * cVec g * parityOp = -cVec g := by
  rw [cVec, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, parityOp_mul_c_mul_parityOp, smul_neg]

theorem gaugeOp_mem_unitary {S : Type*} [Fintype S] [DecidableEq S] (φ : Spin → ℝ) :
    (gaugeOp φ : Op S) ∈ unitary (Op S) := by
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
  exact ⟨Fermion.Pilot.JW.diagonal_conjTranspose_mul_diagonal (Fermion.Pilot.JW.gauge_unit φ),
    Fermion.Pilot.JW.diagonal_mul_diagonal_conjTranspose (Fermion.Pilot.JW.gauge_unit φ)⟩

theorem gauge_eq_conjAut {S : Type*} [Fintype S] [DecidableEq S] (φ : Spin → ℝ) (A : Op S) :
    Fermion.Pilot.JW.gauge φ A = Unitary.conjStarAlgAut ℂ (Op S) ⟨gaugeOp φ, gaugeOp_mem_unitary φ⟩ A := by
  rw [Unitary.conjStarAlgAut_apply, Fermion.Pilot.JW.gauge_eq_conj]
  rfl

theorem parity_eq_conjAut {S : Type*} [Fintype S] [DecidableEq S] (A : Op S) :
    parityOp * A * parityOp = Unitary.conjStarAlgAut ℂ (Op S) ⟨parityOp, parityOp_mem_unitary⟩ A := by
  rw [Unitary.conjStarAlgAut_apply]
  show parityOp * A * parityOp = parityOp * A * parityOpᴴ
  rw [parityOp_conjTranspose]

/-- A real polynomial of `H` acts on an eigenvector of `H` by its value at the eigenvalue (block A's
`toCLM_aeval_eigen`, for any `S`). -/
theorem opCLM_aeval_eigen {S : Type*} [Fintype S] [DecidableEq S] (H : Op S) (μ : ℂ)
    (w : EuclideanSpace ℂ (Conf S)) (hw : Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) H w = μ • w)
    (p : Polynomial ℝ) :
    Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) (Polynomial.aeval H p) w = Polynomial.aeval μ p • w := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.aeval_C, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one (A := Op S) a,
      ← Complex.coe_smul, map_smul, map_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      Complex.coe_algebraMap]
  | add p p' hp hp' => simp only [map_add, ContinuousLinearMap.add_apply, hp, hp', add_smul]
  | monomial n a h =>
    have e1 : Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ (n + 1)) =
        Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n) * H := by
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    have e2 : Polynomial.aeval μ (Polynomial.C a * Polynomial.X ^ (n + 1)) =
        Polynomial.aeval μ (Polynomial.C a * Polynomial.X ^ n) * μ := by
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    rw [e1, e2, map_mul, ContinuousLinearMap.mul_apply, hw, map_smul, h, smul_smul, mul_comm μ]

/-- The spectral projection `1_B(H)` of a self-adjoint matrix is the orthogonal projection onto the span of the
eigenvectors with eigenvalues in `B` (block A's `specProj_sector` without the sector, block A's proof). -/
theorem specProj_eq {S : Type*} [Fintype S] [DecidableEq S] {H : Op S} (hH : IsSelfAdjoint H) (B : Set ℝ) :
    Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H) =
      (⨆ μ ∈ B, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S) (n := Conf S) H)
        (μ : ℂ)).starProjection := by
  have hHerm : H.IsHermitian := hH
  have hsym : (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S) (n := Conf S) H).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp hHerm
  have hlin : ∀ (M : Op S) (w : EuclideanSpace ℂ (Conf S)),
      Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S) (n := Conf S) M w =
        Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) M w := by
    intro M w
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    rfl
  have hreal : ∀ (μ : ℂ) (w : EuclideanSpace ℂ (Conf S)),
      Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) H w = μ • w → w ≠ 0 → μ = ((μ.re : ℝ) : ℂ) := by
    intro μ w hw hw0
    have hev : Module.End.HasEigenvalue (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S) (n := Conf S) H) μ :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (by rw [hlin]; exact hw), hw0⟩
    exact (Complex.conj_eq_iff_re.mp (hsym.conj_eigenvalue_eq_self hev)).symm
  have hspec : ∀ (r : ℝ) (w : EuclideanSpace ℂ (Conf S)),
      Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) H w = (r : ℂ) • w → w ≠ 0 → r ∈ spectrum ℝ H := by
    intro r w hw hw0
    rw [spectrum.mem_iff]
    intro hu
    apply hw0
    obtain ⟨M, hM⟩ := hu.exists_left_inv
    have h0 : Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) (algebraMap ℝ (Op S) r - H) w = 0 := by
      rw [map_sub, ContinuousLinearMap.sub_apply, hw, Algebra.algebraMap_eq_smul_one (A := Op S) r,
        ← Complex.coe_smul, map_smul, map_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        sub_self]
    calc w = Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) (M * (algebraMap ℝ (Op S) r - H)) w := by
          rw [hM, map_one]; rfl
      _ = 0 := by rw [map_mul, ContinuousLinearMap.mul_apply, h0, map_zero]
  obtain ⟨q, hq⟩ := exists_poly_interp (Matrix.finite_real_spectrum (A := H)).toFinset (B.indicator (1 : ℝ → ℝ))
  have hPq : cfc (B.indicator (1 : ℝ → ℝ)) H = Polynomial.aeval H q := by
    rw [cfc_congr (g := fun x => q.eval x) ?_, cfc_polynomial q H hH]
    intro x hx
    exact (hq x ((Set.Finite.mem_toFinset _).mpr hx)).symm
  have heig : ∀ (μ : ℂ) (w : EuclideanSpace ℂ (Conf S)), Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) H w = μ • w →
      Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H) w =
        ((B.indicator (1 : ℝ → ℝ) μ.re : ℝ) : ℂ) • w := by
    intro μ w hw
    by_cases hw0 : w = 0
    · subst hw0
      simp
    have hμ := hreal μ w hw hw0
    have hr : μ.re ∈ spectrum ℝ H := hspec μ.re w (by rw [← hμ]; exact hw) hw0
    rw [hPq, opCLM_aeval_eigen H μ w hw q]
    congr 1
    rw [← hq μ.re ((Set.Finite.mem_toFinset _).mpr hr)]
    conv_lhs => rw [hμ]
    rw [show ((μ.re : ℝ) : ℂ) = algebraMap ℝ ℂ μ.re from rfl, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
    rfl
  have hPsa : (cfc (B.indicator (1 : ℝ → ℝ)) H)ᴴ = cfc (B.indicator (1 : ℝ → ℝ)) H :=
    cfc_predicate (B.indicator (1 : ℝ → ℝ)) H
  have hXsa : IsSelfAdjoint (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H)) := by
    have hmat : IsSelfAdjoint (cfc (B.indicator (1 : ℝ → ℝ)) H) := by
      rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hPsa]
    exact hmat.map _
  have hS2 : ∀ w ∈ (⨆ μ ∈ B, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S)
        (n := Conf S) H) (μ : ℂ)),
      Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H) w = w := by
    intro w hw
    have hle : (⨆ μ ∈ B, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S)
        (n := Conf S) H) (μ : ℂ)) ≤
        LinearMap.ker ((Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H) :
          EuclideanSpace ℂ (Conf S) →ₗ[ℂ] EuclideanSpace ℂ (Conf S)) - LinearMap.id) := by
      refine iSup₂_le fun μ hμB => ?_
      intro v hv
      rw [Module.End.mem_eigenspace_iff, hlin] at hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, LinearMap.id_apply, sub_eq_zero,
        heig _ v hv, Complex.ofReal_re, Set.indicator_of_mem hμB, Pi.one_apply, Complex.ofReal_one, one_smul]
    have := hle hw
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, LinearMap.id_apply, sub_eq_zero]
      at this
  have htop : (⨆ μ : ℂ, Module.End.eigenspace
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S) (n := Conf S) H) μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hsym.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hS3 : ∀ u, Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H) u ∈
      (⨆ μ ∈ B, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S)
        (n := Conf S) H) (μ : ℂ)) := by
    intro u
    have hu : u ∈ ⨆ μ : ℂ, Module.End.eigenspace
        (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S) (n := Conf S) H) μ := by
      rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun u =>
      Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H) u ∈
        (⨆ μ ∈ B, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf S)
          (n := Conf S) H) (μ : ℂ))) hu ?_ ?_ ?_
    · intro μ v hv
      rw [Module.End.mem_eigenspace_iff, hlin] at hv
      rw [heig μ v hv]
      by_cases hv0 : v = 0
      · rw [hv0, smul_zero]; exact Submodule.zero_mem _
      by_cases hB : μ.re ∈ B
      · rw [Set.indicator_of_mem hB, Pi.one_apply, Complex.ofReal_one, one_smul]
        have hμ := hreal μ v hv hv0
        refine (le_iSup₂ (f := fun (r : ℝ) (_ : r ∈ B) => Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ)
          (m := Conf S) (n := Conf S) H) (r : ℂ)) μ.re hB) ?_
        rw [Module.End.mem_eigenspace_iff, hlin, ← hμ]
        exact hv
      · rw [Set.indicator_of_notMem hB, Complex.ofReal_zero, zero_smul]
        exact Submodule.zero_mem _
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  ext u : 1
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS3 u) fun w hw => ?_
  have hsymX := hXsa.isSymmetric u w
  simp only [ContinuousLinearMap.coe_coe] at hsymX
  rw [inner_sub_left, hsymX, hS2 w hw, sub_self]

end IotaDevices

/-! ### Lemma 3.8(i): `𝔉(𝒮)` -/

/-- **Lemma 3.8(i)**: `𝔉(𝒮)` is "`an isometry`": `𝔉(𝒮)^*𝔉(𝒮) = 1`. -/
theorem FfA_conjTranspose_mul_self (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) :
    (FfA η δ₀ T)ᴴ * FfA η δ₀ T = 1 :=
  secondQuant_conjTranspose_mul_self_rect (anaMat_conjTranspose_mul_self hη hδ₀ hT)

/-- **Lemma 3.8(i)**: `𝔉(𝒮)` is an isometry, `‖𝔉(𝒮)Ψ‖ = ‖Ψ‖`. -/
theorem norm_FfA_apply (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (Ψ : FockSpace T) :
    ‖Matrix.toEuclideanLin (𝕜 := ℂ) (FfA η δ₀ T) Ψ‖ = ‖Ψ‖ := by
  have h1 := FfA_conjTranspose_mul_self hη hδ₀ hT
  have key : Matrix.toEuclideanLin (𝕜 := ℂ) (FfA η δ₀ T)ᴴ (Matrix.toEuclideanLin (𝕜 := ℂ) (FfA η δ₀ T) Ψ) = Ψ := by
    rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) Ψ]
  congr 2
  rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, key]

/-! ### Proof devices for `range_FfA` (phase (b); not statements of the paper)

`segIncl` is the inclusion `e_κ ↦ e_{glue κ vac}` of the physical configurations as the segment configurations with
every other mode empty; it intertwines `A` with `A ⊠ 1`, hence the creators `c_μ^*` with `c_{segEmb μ}^*`. Then
`𝔉(𝒮) = 𝔉(U) segIncl`, because both sides intertwine the creators in the same way and agree on the vacuum, and an
operator out of `𝓗_N` that intertwines the creators and kills the vacuum is `0` (the occupation basis is generated from
the vacuum by creators: block A's `Ff_unique` gives `𝔉(1) = 1`). The range of `𝔉(U) segIncl` and the joint kernel of
the `ĉ(e)`, `e ⊥ ran 𝒮`, are both characterized by: `𝔉(U)^*Ψ` vanishes on every configuration with an occupied mode
off the segment. -/

section RangeDevices

section RangeGeneric

variable {S S' : Type*} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']

theorem glue_vac (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) : glue h (vac : Conf S) (vac : Conf S') = vac := by
  funext ν
  simp only [glue, vac]
  split_ifs <;> rfl

theorem eq_glue_vac_iff (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (k : Conf S') (κ : Conf S) :
    k = glue h κ vac ↔ OffEq h k vac ∧ segRestr h k = κ := by
  constructor
  · rintro rfl
    exact ⟨offEq_glue h κ vac, segRestr_glue h κ vac⟩
  · rintro ⟨h1, h2⟩
    exact eq_of_segRestr_eq h (by rw [h2, segRestr_glue]) (offEq_trans h h1 (offEq_symm h (offEq_glue h κ vac)))

/-- The inclusion of the physical configurations as segment configurations with the other modes empty. -/
def segIncl (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) : Matrix (Conf S') (Conf S) ℂ :=
  Matrix.of fun k κ => if k = glue h κ vac then 1 else 0

theorem segIncl_mul (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (A : Op S) :
    segIncl h * A = ampl h A * segIncl h := by
  ext m' κ
  have hL : (segIncl h * A) m' κ = if OffEq h m' vac then A (segRestr h m') κ else 0 := by
    rw [Matrix.mul_apply]
    simp only [segIncl, Matrix.of_apply, eq_glue_vac_iff]
    simp only [ite_mul, one_mul, zero_mul]
    by_cases hm : OffEq h m' vac
    · rw [if_pos hm, Finset.sum_eq_single (segRestr h m')]
      · rw [if_pos (show OffEq h m' vac ∧ segRestr h m' = segRestr h m' from ⟨hm, rfl⟩)]
      · intro b _ hb
        rw [if_neg (fun h' => hb h'.2.symm)]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [if_neg hm]
      exact Finset.sum_eq_zero fun x _ => if_neg (fun h' => hm h'.1)
  have hR : (ampl h A * segIncl h) m' κ = ampl h A m' (glue h κ vac) := by
    rw [Matrix.mul_apply]
    simp only [segIncl, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hL, hR, ampl_apply, segRestr_glue]
  by_cases hm : OffEq h m' vac
  · rw [if_pos hm, if_pos (offEq_trans h hm (offEq_symm h (offEq_glue h κ vac)))]
  · rw [if_neg hm, if_neg (fun h' => hm (offEq_trans h h' (offEq_glue h κ vac)))]

theorem exists_segIncl_mulVec_iff (h : Fintype.card (Mode S) ≤ Fintype.card (Mode S')) (v : Conf S' → ℂ) :
    (∃ φ : Conf S → ℂ, v = segIncl h *ᵥ φ) ↔ ∀ m, ¬OffEq h m vac → v m = 0 := by
  have happ : ∀ (φ : Conf S → ℂ) m, (segIncl h *ᵥ φ) m = if OffEq h m vac then φ (segRestr h m) else 0 := by
    intro φ m
    simp only [Matrix.mulVec, dotProduct, segIncl, Matrix.of_apply, eq_glue_vac_iff]
    simp only [ite_mul, one_mul, zero_mul]
    by_cases hm : OffEq h m vac
    · rw [if_pos hm, Finset.sum_eq_single (segRestr h m)]
      · rw [if_pos (show OffEq h m vac ∧ segRestr h m = segRestr h m from ⟨hm, rfl⟩)]
      · intro b _ hb
        rw [if_neg (fun h' => hb h'.2.symm)]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [if_neg hm]
      exact Finset.sum_eq_zero fun x _ => if_neg (fun h' => hm h'.1)
  constructor
  · rintro ⟨φ, rfl⟩ m hm
    rw [happ, if_neg hm]
  · intro hv
    refine ⟨fun κ => v (glue h κ vac), funext fun m => ?_⟩
    rw [happ]
    by_cases hm : OffEq h m vac
    · rw [if_pos hm, glue_segRestr h hm]
    · rw [if_neg hm, hv m hm]

theorem mul_prod_eq_prod_mul_rect {ι : Type*} (X : Matrix (Conf S') (Conf S) ℂ) (Y : ι → Op S) (Z : ι → Op S')
    (hXY : ∀ i, X * Y i = Z i * X) (l : List ι) : X * (l.map Y).prod = (l.map Z).prod * X := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← Matrix.mul_assoc, hXY, Matrix.mul_assoc, ih,
      ← Matrix.mul_assoc]

theorem c_mulVec_eq_zero_iff (ν : Mode S') (v : Conf S' → ℂ) : c ν *ᵥ v = 0 ↔ ∀ m, m ν = true → v m = 0 := by
  constructor
  · intro h0 m hm
    have := congrFun h0 (Function.update m ν false)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    rw [Fermion.Pilot.JW.sum_c_mul ν v (Function.update m ν false), Function.update_self, if_pos rfl,
      Function.update_idem, Function.update_eq_self_iff.mpr hm.symm] at this
    have hs := Fermion.Pilot.JW.jwSign_mul_self ν m
    rcases mul_eq_zero.mp this with h1 | h1
    · rw [h1, zero_mul] at hs
      exact absurd hs zero_ne_one
    · exact h1
  · intro hv
    funext m'
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Fermion.Pilot.JW.sum_c_mul ν v m']
    split_ifs
    · rw [hv _ (by simp), mul_zero]
    · rfl

theorem cVec_col_eq {U : Matrix (Mode S') (Mode S') ℂ} (hUU : Uᴴ * U = 1) (ν : Mode S') :
    cVec (fun ρ => U ρ ν) = secondQuant U * c ν * (secondQuant U)ᴴ := by
  have hWW' : secondQuant U * (secondQuant U)ᴴ = 1 := mul_eq_one_comm.mp (secondQuant_conjTranspose_mul_self hUU)
  rw [secondQuant_mul_c hUU, Matrix.mul_assoc, hWW', Matrix.mul_one]

theorem cVec_eq_conj {U : Matrix (Mode S') (Mode S') ℂ} (hUU : Uᴴ * U = 1) (hUU' : U * Uᴴ = 1) (e : Mode S' → ℂ) :
    cVec e = secondQuant U * cVec (Uᴴ *ᵥ e) * (secondQuant U)ᴴ := by
  have hWW' : secondQuant U * (secondQuant U)ᴴ = 1 := mul_eq_one_comm.mp (secondQuant_conjTranspose_mul_self hUU)
  rw [secondQuant_mul_cVec hUU, Matrix.mulVec_mulVec, hUU', Matrix.one_mulVec, Matrix.mul_assoc, hWW',
    Matrix.mul_one]

end RangeGeneric

theorem secondQuant_one_phys (T : Torus) : secondQuant (1 : Matrix (Modes T) (Modes T) ℂ) = 1 := by
  have h1 : (1 : Matrix (Modes T) (Modes T) ℂ) ∈ unitary (Matrix (Modes T) (Modes T) ℂ) := one_mem _
  have := Ff_unique T h1 (W := 1) (one_mem _) (fun f => by simp) (Matrix.one_mulVec _)
  exact this.symm

theorem eq_zero_of_intertwines_cdag {S' : Type*} [Fintype S'] [DecidableEq S'] (T : Torus)
    (X : Matrix (Conf S') (Conf (ZMod T.Nφ)) ℂ) (Z : Modes T → Op S')
    (hX : ∀ μ, X * (c μ)ᴴ = Z μ * X) (hvac : ∀ k, X k vac = 0) : X = 0 := by
  have hc : (fun μ : Modes T => (cVec fun ν => (1 : Matrix (Modes T) (Modes T) ℂ) ν μ)ᴴ) = fun μ => (c μ)ᴴ := by
    funext μ
    rw [← cVec_single]
    congr 2
  ext m' κ
  have e1 : X m' κ = (X * secondQuant (1 : Matrix (Modes T) (Modes T) ℂ)) m' κ := by
    rw [secondQuant_one_phys, Matrix.mul_one]
  rw [e1, Matrix.mul_apply]
  simp only [secondQuant_apply, hc]
  rw [← Matrix.mul_apply (M := X), mul_prod_eq_prod_mul_rect X _ Z hX, Matrix.mul_apply]
  simp [hvac]

theorem mem_orthogonal_range_analysis2_iff (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀)
    (h : Fintype.card (Modes T) ≤ Fintype.card (Mode (Slot δ₀ T))) (e : EuclideanSpace ℂ (Mode (Slot δ₀ T))) :
    e ∈ (LinearMap.range (analysis2 η δ₀ T))ᗮ ↔
      ∀ μ : Modes T, ((embedU η δ₀ T h)ᴴ *ᵥ (fun ρ => e ρ)) (segEmb h μ) = 0 := by
  have hU := embedU_spec hη hδ₀ hT h
  have hcolμ : ∀ μ : Modes T, ((embedU η δ₀ T h)ᴴ *ᵥ (fun ρ => e ρ)) (segEmb h μ) =
      ∑ ρ, star (anaMat η δ₀ T ρ μ) * e ρ := by
    intro μ
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, hU.2 μ]
  simp_rw [hcolμ]
  rw [Submodule.mem_orthogonal]
  constructor
  · intro he μ
    have := he (analysis2 η δ₀ T (EuclideanSpace.single μ 1)) (LinearMap.mem_range_self _ _)
    rw [PiLp.inner_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [RCLike.inner_apply, anaMat, Matrix.of_apply, Complex.star_def]
    ring
  · intro he u hu
    obtain ⟨f, rfl⟩ := hu
    rw [PiLp.inner_apply]
    have hcoord := congrFun (analysis2_coord (η := η) (δ₀ := δ₀) (T := T) f)
    simp only [RCLike.inner_apply]
    simp_rw [show ∀ ρ, analysis2 η δ₀ T f ρ = (anaMat η δ₀ T *ᵥ fun μ => f μ) ρ from hcoord]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun μ _ => ?_
    have := he μ
    calc ∑ ρ, e ρ * ((starRingEnd ℂ) (anaMat η δ₀ T ρ μ) * (starRingEnd ℂ) (f μ))
        = (starRingEnd ℂ) (f μ) * ∑ ρ, star (anaMat η δ₀ T ρ μ) * e ρ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          rw [Complex.star_def]
          ring
      _ = 0 := by rw [this, mul_zero]

end RangeDevices

/-- **Lemma 3.8(i)**: "`an isometry onto the subspace of $\FockS$ in which the modes orthogonal to $\ran\Sa$ are empty`" —
in the proof's words, "`the subspace on which every $\chat(e)$, $e\in\mathfrak r^\perp$, vanishes`". -/
theorem range_FfA (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) :
    LinearMap.range (Matrix.toEuclideanLin (𝕜 := ℂ) (FfA η δ₀ T)) =
      ⨅ e ∈ (LinearMap.range (analysis2 η δ₀ T))ᗮ, LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (chatVec e)) := by
  have h := card_modes_le hδ₀ hT
  have hU := embedU_spec hη hδ₀ hT h
  have hUU : (embedU η δ₀ T h)ᴴ * embedU η δ₀ T h = 1 := conjTranspose_mul_self_of_mem_unitary hU.1
  have hUU' : embedU η δ₀ T h * (embedU η δ₀ T h)ᴴ = 1 := mul_conjTranspose_self_of_mem_unitary hU.1
  have hWW : (secondQuant (embedU η δ₀ T h))ᴴ * secondQuant (embedU η δ₀ T h) = 1 :=
    secondQuant_conjTranspose_mul_self hUU
  have hWW' : secondQuant (embedU η δ₀ T h) * (secondQuant (embedU η δ₀ T h))ᴴ = 1 := mul_eq_one_comm.mp hWW
  have hcol : ∀ μ, (fun ρ => embedU η δ₀ T h ρ (segEmb h μ)) = fun ρ => anaMat η δ₀ T ρ μ :=
    fun μ => funext (hU.2 μ)
  -- `𝔉(𝒮) = 𝔉(U) segIncl`
  have hF : FfA η δ₀ T = secondQuant (embedU η δ₀ T h) * segIncl h := by
    refine sub_eq_zero.mp (eq_zero_of_intertwines_cdag T _ (fun μ => (cVec fun ρ => anaMat η δ₀ T ρ μ)ᴴ) ?_ ?_)
    · intro μ
      rw [Matrix.sub_mul, Matrix.mul_sub, FfA, secondQuant_mul_cdag, Matrix.mul_assoc, segIncl_mul,
        ampl_conjTranspose, ampl_c, ← Matrix.mul_assoc, secondQuant_mul_cdag, hcol, Matrix.mul_assoc]
    · intro k
      rw [Matrix.sub_apply, FfA, secondQuant_apply_vac, Matrix.mul_apply]
      simp only [segIncl, Matrix.of_apply, glue_vac, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, secondQuant_apply_vac, sub_self]
  ext Ψ
  rw [LinearMap.mem_range, Submodule.mem_iInf]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  have key_l : (∃ φ, Matrix.toEuclideanLin (𝕜 := ℂ) (FfA η δ₀ T) φ = Ψ) ↔
      ∀ m, ¬OffEq h m vac → ((secondQuant (embedU η δ₀ T h))ᴴ *ᵥ (fun m => Ψ m)) m = 0 := by
    rw [← exists_segIncl_mulVec_iff h]
    constructor
    · rintro ⟨φ, rfl⟩
      refine ⟨fun κ => φ κ, ?_⟩
      rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp, hF, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hWW,
        Matrix.one_mulVec]
    · rintro ⟨φ, hφ⟩
      refine ⟨WithLp.toLp 2 φ, ?_⟩
      rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp, hF, ← Matrix.mulVec_mulVec, ← hφ, Matrix.mulVec_mulVec, hWW',
        Matrix.one_mulVec]
  have key_r : (∀ e, e ∈ (LinearMap.range (analysis2 η δ₀ T))ᗮ →
      Matrix.toEuclideanLin (𝕜 := ℂ) (chatVec e) Ψ = 0) ↔
      ∀ m, ¬OffEq h m vac → ((secondQuant (embedU η δ₀ T h))ᴴ *ᵥ (fun m => Ψ m)) m = 0 := by
    constructor
    · intro hker m hm
      have hm' : ∃ ν : Mode (Slot δ₀ T), Fintype.card (Modes T) ≤ ((num ν : Fin _) : ℕ) ∧ m ν = true := by
        by_contra hno
        push_neg at hno
        apply hm
        intro ν hν
        have := hno ν hν
        simpa [vac] using this
      obtain ⟨ν, hν, hmν⟩ := hm'
      have he : (WithLp.toLp 2 fun ρ => embedU η δ₀ T h ρ ν : EuclideanSpace ℂ (Mode (Slot δ₀ T))) ∈
          (LinearMap.range (analysis2 η δ₀ T))ᗮ := by
        rw [mem_orthogonal_range_analysis2_iff hη hδ₀ hT h]
        intro μ
        have := congrFun (congrFun hUU (segEmb h μ)) ν
        rw [Matrix.mul_apply, Matrix.one_apply, if_neg (Ne.symm (ne_segEmb_of_le h hν μ))] at this
        rw [← this]
        rfl
      have h0 := hker _ he
      rw [Matrix.toLpLin_apply, chatVec] at h0
      have h0' : (secondQuant (embedU η δ₀ T h) * c ν * (secondQuant (embedU η δ₀ T h))ᴴ) *ᵥ (fun m => Ψ m) = 0 := by
        rw [← cVec_col_eq hUU]
        have := congrArg WithLp.ofLp h0
        exact this
      have h1 : c ν *ᵥ ((secondQuant (embedU η δ₀ T h))ᴴ *ᵥ (fun m => Ψ m)) = 0 := by
        have := congrArg (fun w => (secondQuant (embedU η δ₀ T h))ᴴ *ᵥ w) h0'
        simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hWW, Matrix.one_mul] at this
        rw [Matrix.mulVec_mulVec]
        exact this
      exact (c_mulVec_eq_zero_iff ν _).mp h1 m hmν
    · intro hv e he
      rw [mem_orthogonal_range_analysis2_iff hη hδ₀ hT h] at he
      rw [Matrix.toLpLin_apply, chatVec, cVec_eq_conj hUU hUU']
      have hterm : cVec ((embedU η δ₀ T h)ᴴ *ᵥ fun ρ => e ρ) *ᵥ ((secondQuant (embedU η δ₀ T h))ᴴ *ᵥ (fun m => Ψ m)) = 0 := by
        rw [cVec, Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun ν _ => ?_
        rw [Matrix.smul_mulVec]
        by_cases hν : ((num ν : Fin _) : ℕ) < Fintype.card (Modes T)
        · obtain ⟨μ, rfl⟩ := (exists_segEmb_eq_iff h ν).mpr hν
          rw [he μ, star_zero, zero_smul]
        · rw [(c_mulVec_eq_zero_iff ν _).mpr, smul_zero]
          intro m hm
          apply hv m
          intro hoff
          have := hoff ν (not_lt.mp hν)
          simp [vac, hm] at this
      have : (secondQuant (embedU η δ₀ T h) * cVec ((embedU η δ₀ T h)ᴴ *ᵥ fun ρ => e ρ) *
          (secondQuant (embedU η δ₀ T h))ᴴ) *ᵥ (fun m => Ψ m) = 0 := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hterm, Matrix.mulVec_zero]
      rw [show (fun m => Ψ m) = WithLp.ofLp Ψ from rfl] at this
      rw [this]
      rfl
  rw [key_l, key_r]

/-- The proof of **Lemma 3.8(i)**, the defining formula of `𝔉(𝒮)`: the vacuum goes to the vacuum ... -/
theorem FfA_mulVec_vac :
    (FfA η δ₀ T).mulVec (Pi.single (vac : Conf (ZMod T.Nφ)) (1 : ℂ)) =
      Pi.single (vac : Conf (Slot δ₀ T)) (1 : ℂ) := by
  rw [Matrix.mulVec_single_one]
  funext m'
  rw [Matrix.col_apply, FfA, secondQuant_apply_vac]
  simp [Pi.single_apply]

/-- ... and the creators are intertwined, `𝔉(𝒮)c(f)^* = ĉ(𝒮f)^*𝔉(𝒮)`: together,
"`$\Ff(\Sa)c(h_1)^*\cdots c(h_p)^*\Omega_0=\chat(\Sa h_1)^*\cdots\chat(\Sa h_p)^*\widehat\Omega_0$`". -/
theorem FfA_mul_cf_conjTranspose (f : Space2 T) :
    FfA η δ₀ T * (cf T f)ᴴ = (chatVec (analysis2 η δ₀ T f))ᴴ * FfA η δ₀ T := by
  rw [chatVec, analysis2_coord, cVec_mulVec, cf, conjTranspose_cVec, Matrix.mul_sum, Matrix.conjTranspose_sum,
    Matrix.sum_mul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Matrix.mul_smul, FfA, secondQuant_mul_cdag, Matrix.conjTranspose_smul, star_star, Matrix.smul_mul]

/-- The annihilators are intertwined too, `𝔉(𝒮)c(f) = ĉ(𝒮f)𝔉(𝒮)` (`𝒮` an isometry). -/
theorem FfA_mul_cf (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (f : Space2 T) :
    FfA η δ₀ T * cf T f = chatVec (analysis2 η δ₀ T f) * FfA η δ₀ T := by
  rw [chatVec, analysis2_coord, cf, FfA]
  exact secondQuant_mul_cVec (anaMat_conjTranspose_mul_self hη hδ₀ hT) _

/-! ### Definition 3.7 and Lemma 3.8(i): `ι` -/

/-- **Definition 3.7**: "`\iota\bigl(c(f)\bigr)=\chat(\Sa f),\qquad f\in\kN`". -/
theorem iota_cf (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (f : Space2 T) :
    iota η δ₀ T (cf T f) = chatVec (analysis2 η δ₀ T f) := by
  have h := card_modes_le hδ₀ hT
  have hU := embedU_spec hη hδ₀ hT h
  have hUU : (embedU η δ₀ T h)ᴴ * embedU η δ₀ T h = 1 := conjTranspose_mul_self_of_mem_unitary hU.1
  have hWW : secondQuant (embedU η δ₀ T h) * (secondQuant (embedU η δ₀ T h))ᴴ = 1 :=
    mul_eq_one_comm.mp (secondQuant_conjTranspose_mul_self hUU)
  rw [iota_eq h]
  have hampl : ampl h (cf T f) = ∑ μ, star (f μ) • c (segEmb h μ) := by
    rw [← amplHom_apply, cf, cVec, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_smul, amplHom_apply, ampl_c]
  rw [hampl, Finset.mul_sum, Finset.sum_mul, chatVec, analysis2_coord, cVec_mulVec]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, secondQuant_mul_c hUU, Matrix.mul_assoc, hWW, Matrix.mul_one]
  congr 2
  funext ρ
  exact hU.2 μ ρ

/-- **Definition 3.7**: `ι` is "`the unital $*$-homomorphism from the operators on $\Fock$ to the operators on $\FockS$`"
— a `StarAlgHom` (linear, unital, multiplicative, star-preserving at once). -/
theorem exists_starAlgHom_iota (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) :
    ∃ φ : FockOp T →⋆ₐ[ℂ] Op (Slot δ₀ T), ⇑φ = iota η δ₀ T :=
  ⟨iotaHom hη hδ₀ hT, funext (iotaHom_apply hη hδ₀ hT)⟩

/-- `ι` is additive. -/
theorem iota_add (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (A B : FockOp T) :
    iota η δ₀ T (A + B) = iota η δ₀ T A + iota η δ₀ T B := by
  simp only [← iotaHom_apply hη hδ₀ hT, map_add]

/-- `ι` is linear. -/
theorem iota_smul (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (a : ℂ) (A : FockOp T) :
    iota η δ₀ T (a • A) = a • iota η δ₀ T A := by
  simp only [← iotaHom_apply hη hδ₀ hT, map_smul]

/-- **Lemma 3.8(i)**: `ι` is "`unital`". -/
theorem iota_one (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) : iota η δ₀ T 1 = 1 := by
  rw [← iotaHom_apply hη hδ₀ hT, map_one]

/-- `ι` is multiplicative. -/
theorem iota_mul (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (A B : FockOp T) :
    iota η δ₀ T (A * B) = iota η δ₀ T A * iota η δ₀ T B := by
  simp only [← iotaHom_apply hη hδ₀ hT, map_mul]

/-- `ι` is star-preserving. -/
theorem iota_conjTranspose (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (A : FockOp T) :
    iota η δ₀ T Aᴴ = (iota η δ₀ T A)ᴴ := by
  rw [← iotaHom_apply hη hδ₀ hT, ← iotaHom_apply hη hδ₀ hT, ← Matrix.star_eq_conjTranspose,
    ← Matrix.star_eq_conjTranspose, map_star]

/-- **Lemma 3.8(i)**: `ι` is "`injective`". -/
theorem iota_injective (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) :
    Function.Injective (iota η δ₀ T) := by
  intro A B e
  rw [← iotaHom_apply hη hδ₀ hT, ← iotaHom_apply hη hδ₀ hT] at e
  exact iotaHom_injective hη hδ₀ hT e

/-- **Lemma 3.8(i)**: `ι` is "`isometric`" (operator norms). -/
theorem norm_iota (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (A : FockOp T) :
    ‖opCLM (iota η δ₀ T A)‖ = ‖toCLM T A‖ := by
  rw [← iotaHom_apply hη hδ₀ hT]
  open scoped Matrix.Norms.L2Operator in
  exact NonUnitalStarAlgHom.norm_map (iotaHom hη hδ₀ hT) (iotaHom_injective hη hδ₀ hT) A

/-- The proof of **Lemma 3.8(i)**: "`the operators $c(f)$ generate all operators on $\Fock$ as a unital $*$-algebra`". -/
theorem adjoin_range_cf (T : Torus) : StarAlgebra.adjoin ℂ (Set.range (cf T)) = ⊤ := by
  rw [eq_top_iff, ← Fermion.Pilot.JW.CAR_univ, Fermion.Pilot.JW.CAR]
  apply StarAlgebra.adjoin_le
  rintro A ⟨s, -, σ, rfl⟩
  exact StarAlgebra.subset_adjoin ℂ _ ⟨EuclideanSpace.single (s, σ) 1, cf_single T (s, σ)⟩

/-- The proof of **Lemma 3.8(i)**: "`It is the only unital $*$-homomorphism with this property`". -/
theorem iota_unique (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀)
    (φ : FockOp T →⋆ₐ[ℂ] Op (Slot δ₀ T)) (hφ : ∀ f : Space2 T, φ (cf T f) = chatVec (analysis2 η δ₀ T f)) :
    ⇑φ = iota η δ₀ T := by
  have := StarAlgHom.ext_of_adjoin_eq_top (adjoin_range_cf T) (f := φ) (g := iotaHom hη hδ₀ hT) (by
    rintro _ ⟨f, rfl⟩
    rw [hφ, iotaHom_apply, iota_cf hη hδ₀ hT])
  rw [this]
  exact funext (iotaHom_apply hη hδ₀ hT)

/-- **Lemma 3.8(i)**: "`it maps even operators to even operators`". -/
theorem iota_isEven (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) {A : FockOp T} (hA : IsEven A) :
    IsEven (iota η δ₀ T A) := by
  have key : (StarAlgHom.ofClass (Unitary.conjStarAlgAut ℂ (Op (Slot δ₀ T)) ⟨parityOp, parityOp_mem_unitary⟩)).comp
        (iotaHom hη hδ₀ hT) =
      (iotaHom hη hδ₀ hT).comp
        (StarAlgHom.ofClass (Unitary.conjStarAlgAut ℂ (FockOp T) ⟨parityOp, parityOp_mem_unitary⟩)) := by
    apply StarAlgHom.ext_of_adjoin_eq_top (adjoin_range_cf T)
    rintro _ ⟨f, rfl⟩
    show Unitary.conjStarAlgAut ℂ (Op (Slot δ₀ T)) ⟨parityOp, parityOp_mem_unitary⟩ (iotaHom hη hδ₀ hT (cf T f)) =
      iotaHom hη hδ₀ hT (Unitary.conjStarAlgAut ℂ (FockOp T) ⟨parityOp, parityOp_mem_unitary⟩ (cf T f))
    rw [← parity_eq_conjAut, ← parity_eq_conjAut, iotaHom_apply, iotaHom_apply, iota_cf hη hδ₀ hT, cf,
      parityOp_mul_cVec_mul_parityOp, ← cf, ← neg_one_smul ℂ (cf T f), iota_smul hη hδ₀ hT, iota_cf hη hδ₀ hT,
      chatVec, parityOp_mul_cVec_mul_parityOp, neg_one_smul]
  have hPA : parityOp * A * parityOp = A := by
    rw [Matrix.mul_assoc, hA.eq, ← Matrix.mul_assoc, Fermion.Pilot.JW.parityOp_mul_parityOp, Matrix.one_mul]
  have e := congrArg (fun φ => φ A) key
  simp only [StarAlgHom.comp_apply] at e
  change Unitary.conjStarAlgAut ℂ (Op (Slot δ₀ T)) ⟨parityOp, parityOp_mem_unitary⟩ (iotaHom hη hδ₀ hT A) =
    iotaHom hη hδ₀ hT (Unitary.conjStarAlgAut ℂ (FockOp T) ⟨parityOp, parityOp_mem_unitary⟩ A) at e
  rw [← parity_eq_conjAut, ← parity_eq_conjAut, hPA, iotaHom_apply] at e
  show iota η δ₀ T A * parityOp = parityOp * iota η δ₀ T A
  calc iota η δ₀ T A * parityOp = parityOp * (parityOp * iota η δ₀ T A * parityOp) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Fermion.Pilot.JW.parityOp_mul_parityOp, Matrix.one_mul]
    _ = parityOp * iota η δ₀ T A := by rw [e]

/-- (A proof device, not a statement of the paper.) `ι` commutes with the parity conjugations:
`P̂ ι(A) P̂ = ι(P A P)` (the uniqueness argument of `iota_isEven`, for every `A`). -/
theorem iota_parity (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (A : FockOp T) :
    parityOp * iota η δ₀ T A * parityOp = iota η δ₀ T (parityOp * A * parityOp) := by
  have key : (StarAlgHom.ofClass (Unitary.conjStarAlgAut ℂ (Op (Slot δ₀ T)) ⟨parityOp, parityOp_mem_unitary⟩)).comp
        (iotaHom hη hδ₀ hT) =
      (iotaHom hη hδ₀ hT).comp
        (StarAlgHom.ofClass (Unitary.conjStarAlgAut ℂ (FockOp T) ⟨parityOp, parityOp_mem_unitary⟩)) := by
    apply StarAlgHom.ext_of_adjoin_eq_top (adjoin_range_cf T)
    rintro _ ⟨f, rfl⟩
    show Unitary.conjStarAlgAut ℂ (Op (Slot δ₀ T)) ⟨parityOp, parityOp_mem_unitary⟩ (iotaHom hη hδ₀ hT (cf T f)) =
      iotaHom hη hδ₀ hT (Unitary.conjStarAlgAut ℂ (FockOp T) ⟨parityOp, parityOp_mem_unitary⟩ (cf T f))
    rw [← parity_eq_conjAut, ← parity_eq_conjAut, iotaHom_apply, iotaHom_apply, iota_cf hη hδ₀ hT, cf,
      parityOp_mul_cVec_mul_parityOp, ← cf, ← neg_one_smul ℂ (cf T f), iota_smul hη hδ₀ hT, iota_cf hη hδ₀ hT,
      chatVec, parityOp_mul_cVec_mul_parityOp, neg_one_smul]
  have e := congrArg (fun φ => φ A) key
  simp only [StarAlgHom.comp_apply] at e
  change Unitary.conjStarAlgAut ℂ (Op (Slot δ₀ T)) ⟨parityOp, parityOp_mem_unitary⟩ (iotaHom hη hδ₀ hT A) =
    iotaHom hη hδ₀ hT (Unitary.conjStarAlgAut ℂ (FockOp T) ⟨parityOp, parityOp_mem_unitary⟩ A) at e
  rw [← parity_eq_conjAut, ← parity_eq_conjAut, iotaHom_apply, iotaHom_apply] at e
  exact e

/-- **Lemma 3.8(i)**: "`$\iota(A)\Ff(\Sa)=\Ff(\Sa)A$ for every operator $A$ on $\Fock$`". -/
theorem iota_mul_FfA (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (A : FockOp T) :
    iota η δ₀ T A * FfA η δ₀ T = FfA η δ₀ T * A := by
  have hA : A ∈ CAR (Finset.univ : Finset (ZMod T.Nφ)) := by
    rw [Fermion.Pilot.JW.CAR_univ]; trivial
  have hA' : A ∈ Algebra.adjoin ℂ ({B | ∃ s ∈ (Finset.univ : Finset (ZMod T.Nφ)), ∃ σ : Spin, B = chat s σ} ∪
      star {B | ∃ s ∈ (Finset.univ : Finset (ZMod T.Nφ)), ∃ σ : Spin, B = chat s σ}) := hA
  refine Algebra.adjoin_induction (p := fun A _ => iota η δ₀ T A * FfA η δ₀ T = FfA η δ₀ T * A) ?_ ?_ ?_ ?_ hA'
  · intro x hx
    rcases hx with ⟨s, -, σ, rfl⟩ | hx
    · rw [show chat s σ = cf T (EuclideanSpace.single (s, σ) 1) from (cf_single T (s, σ)).symm,
        iota_cf hη hδ₀ hT, FfA_mul_cf hη hδ₀ hT]
    · obtain ⟨s, -, σ, h⟩ := hx
      have hx : x = (cf T (EuclideanSpace.single (s, σ) 1))ᴴ := by
        rw [cf_single, ← Matrix.star_eq_conjTranspose, show c (s, σ) = chat s σ from rfl, ← h, star_star]
      rw [hx, iota_conjTranspose hη hδ₀ hT, iota_cf hη hδ₀ hT, FfA_mul_cf_conjTranspose]
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, iota_smul hη hδ₀ hT, iota_one hη hδ₀ hT, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · intro x y _ _ hx hy
    rw [iota_add hη hδ₀ hT, Matrix.add_mul, Matrix.mul_add, hx, hy]
  · intro x y _ _ hx hy
    rw [iota_mul hη hδ₀ hT, Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx, Matrix.mul_assoc]

/-! ### Lemma 3.8(ii): spectra and the functional calculus -/

/-- **Lemma 3.8(ii)**: "`$\iota(A)$ has the same spectrum as $A$`" — stated for every `A` (the paper states it for
self-adjoint `A`; its proof, "`$\iota(A)$ is unitarily equivalent to $A\otimes\one$, which has the spectrum of $A$`",
does not use self-adjointness). -/
theorem spectrum_iota (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (A : FockOp T) :
    spectrum ℂ (iota η δ₀ T A) = spectrum ℂ A := by
  rw [← iotaHom_apply hη hδ₀ hT]
  refine Set.Subset.antisymm (AlgHom.spectrum_apply_subset (iotaHom hη hδ₀ hT) A) ?_
  intro z hz
  rw [spectrum.mem_iff] at hz ⊢
  intro hu
  apply hz
  have hdet : (algebraMap ℂ (FockOp T) z - A).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    set M : FockOp T := Matrix.of fun i _ => v i with hM
    have hM0 : M ≠ 0 := by
      intro h'
      apply hv0
      funext i
      have := congrFun (congrFun h' i) i
      simpa [hM] using this
    have hMz : (algebraMap ℂ (FockOp T) z - A) * M = 0 := by
      ext i j
      have := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      simp only [Matrix.mul_apply, hM, Matrix.of_apply, Matrix.zero_apply]
      exact this
    have himg : (algebraMap ℂ (Op (Slot δ₀ T)) z - iotaHom hη hδ₀ hT A) * iotaHom hη hδ₀ hT M = 0 := by
      rw [← AlgHomClass.commutes (iotaHom hη hδ₀ hT) z, ← map_sub, ← map_mul, hMz, map_zero]
    obtain ⟨Y, hY⟩ := hu.exists_left_inv
    apply hM0
    apply iotaHom_injective hη hδ₀ hT
    rw [map_zero]
    calc iotaHom hη hδ₀ hT M = Y * (algebraMap ℂ (Op (Slot δ₀ T)) z - iotaHom hη hδ₀ hT A) * iotaHom hη hδ₀ hT M := by
          rw [hY, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, himg, Matrix.mul_zero]
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr hdet

/-- **Lemma 3.8(ii)**, the real spectrum (the one the functional calculus over `ℝ` uses), for every `A`. -/
theorem spectrum_real_iota (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (A : FockOp T) :
    spectrum ℝ (iota η δ₀ T A) = spectrum ℝ A := by
  have e1 := spectrum.preimage_algebraMap (R := ℝ) ℂ (a := iota η δ₀ T A)
  have e2 := spectrum.preimage_algebraMap (R := ℝ) ℂ (a := A)
  rw [← e1, ← e2, spectrum_iota hη hδ₀ hT]

/-- **Lemma 3.8(ii)**: "`For every self-adjoint $A$ on $\Fock$, $\iota(A)$ has the same spectrum as $A$ and $\iota(f(A))=f(\iota(A))$ for every function $f$ on that spectrum.`" -/
theorem cfc_iota (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) {A : FockOp T} (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) : cfc f (iota η δ₀ T A) = iota η δ₀ T (cfc f A) := by
  rw [← iotaHom_apply hη hδ₀ hT, ← iotaHom_apply hη hδ₀ hT]
  exact (StarAlgHomClass.map_cfc (iotaHom hη hδ₀ hT) f A ((Matrix.finite_real_spectrum (A := A)).continuousOn f)
    (iotaHom_continuous hη hδ₀ hT) hA (hA.map _)).symm

/-- **Lemma 3.8(ii)**: "`In particular $\iota(e^{\iu tH}Ae^{-\iu tH})=e^{\iu t\Hhat}\iota(A)e^{-\iu t\Hhat}$`" (for
self-adjoint `H`, the paper's setting: "`The two particular statements are the cases $f(x)=e^{\pm\iu tx}$, together with the multiplicativity of $\iota$`"). -/
theorem iota_conj_exp (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) {H : FockOp T}
    (_hH : IsSelfAdjoint H) (A : FockOp T) (t : ℝ) :
    iota η δ₀ T (NormedSpace.exp ((I * (t : ℂ)) • H) * A * NormedSpace.exp ((-(I * (t : ℂ))) • H)) =
      NormedSpace.exp ((I * (t : ℂ)) • iota η δ₀ T H) * iota η δ₀ T A *
        NormedSpace.exp ((-(I * (t : ℂ))) • iota η δ₀ T H) := by
  have hexp : ∀ X : FockOp T, iotaHom hη hδ₀ hT (NormedSpace.exp X) = NormedSpace.exp (iotaHom hη hδ₀ hT X) := by
    intro X
    open scoped Matrix.Norms.L2Operator in
    exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (iotaHom hη hδ₀ hT) (iotaHom_continuous hη hδ₀ hT) X
      ((NormedSpace.expSeries_radius_eq_top ℂ (FockOp T)).symm ▸ edist_lt_top _ _)
  simp only [← iotaHom_apply hη hδ₀ hT, map_mul, hexp, map_smul]

/-- **Lemma 3.8(ii)**: "`and $\iota$ maps the spectral projections of $H$ to those of $\Hhat$`" ("`and $f=\one_B$ for Borel sets $B$`"),
in the form of block A's `specProj_sector`: `ι(1_B(H))` is the orthogonal projection of `𝔉_𝒮` onto the span of the
eigenvectors of `Ĥ` with eigenvalues in `B` (the Borel hypothesis kept literally, unused). -/
theorem specProj_iota (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) {H : FockOp T}
    (hH : IsSelfAdjoint H) (B : Set ℝ) (_hB : MeasurableSet B) :
    opCLM (iota η δ₀ T (cfc (B.indicator (1 : ℝ → ℝ)) H)) =
      (⨆ μ ∈ B, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (Slot δ₀ T))
        (n := Conf (Slot δ₀ T)) (iota η δ₀ T H)) (μ : ℂ)).starProjection := by
  have hH' : IsSelfAdjoint (iota η δ₀ T H) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ← iota_conjTranspose hη hδ₀ hT, ← Matrix.star_eq_conjTranspose,
      hH.star_eq]
  rw [← cfc_iota hη hδ₀ hT hH]
  exact specProj_eq hH' B

/-! ### Lemma 3.8(iii): the gauge transformations and the approximants -/

/-- **Lemma 3.8(iii)**: "`$\iota\bigl(e^{\iu(\varphi_\up\Nup+\varphi_\dn\Ndn)}Ae^{-\iu(\varphi_\up\Nup+\varphi_\dn\Ndn)}\bigr) =e^{\iu(\varphi_\up\Nhat\up+\varphi_\dn\Nhat\dn)}\iota(A)e^{-\iu(\varphi_\up\Nhat\up+\varphi_\dn\Nhat\dn)}$`"
— the pilot's `gauge` on both sides (`N_σ = numberOp σ` on the physical side: block A's `Nsig_eq_numberOp`). -/
theorem iota_gauge (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) (φ : Spin → ℝ) (A : FockOp T) :
    iota η δ₀ T (Fermion.Pilot.JW.gauge φ A) = Fermion.Pilot.JW.gauge φ (iota η δ₀ T A) := by
  have key : (StarAlgHom.ofClass (Unitary.conjStarAlgAut ℂ (Op (Slot δ₀ T)) ⟨gaugeOp φ, gaugeOp_mem_unitary φ⟩)).comp
        (iotaHom hη hδ₀ hT) =
      (iotaHom hη hδ₀ hT).comp
        (StarAlgHom.ofClass (Unitary.conjStarAlgAut ℂ (FockOp T) ⟨gaugeOp φ, gaugeOp_mem_unitary φ⟩)) := by
    apply StarAlgHom.ext_of_adjoin_eq_top (s := {B | ∃ s ∈ (Finset.univ : Finset (ZMod T.Nφ)), ∃ σ : Spin,
      B = chat s σ}) Fermion.Pilot.JW.CAR_univ
    rintro _ ⟨j, -, σ, rfl⟩
    show Unitary.conjStarAlgAut ℂ (Op (Slot δ₀ T)) ⟨gaugeOp φ, gaugeOp_mem_unitary φ⟩ (iotaHom hη hδ₀ hT (chat j σ)) =
      iotaHom hη hδ₀ hT (Unitary.conjStarAlgAut ℂ (FockOp T) ⟨gaugeOp φ, gaugeOp_mem_unitary φ⟩ (chat j σ))
    have hc : chat j σ = cf T (spinTensor (orb T j) σ) := by
      rw [spinTensor_orb, cf_single]; rfl
    rw [← gauge_eq_conjAut, ← gauge_eq_conjAut, iotaHom_apply, iotaHom_apply,
      show Fermion.Pilot.JW.gauge φ (chat j σ) = Complex.exp (-(I * (φ σ : ℂ))) • chat j σ from gauge_c φ (j, σ),
      iota_smul hη hδ₀ hT, hc, iota_cf hη hδ₀ hT, analysis2_spinTensor, gauge_chatVec_spinTensor]
  have e := congrArg (fun ψ => ψ A) key
  change Unitary.conjStarAlgAut ℂ (Op (Slot δ₀ T)) ⟨gaugeOp φ, gaugeOp_mem_unitary φ⟩ (iotaHom hη hδ₀ hT A) =
    iotaHom hη hδ₀ hT (Unitary.conjStarAlgAut ℂ (FockOp T) ⟨gaugeOp φ, gaugeOp_mem_unitary φ⟩ A) at e
  rw [← gauge_eq_conjAut, ← gauge_eq_conjAut, iotaHom_apply, iotaHom_apply] at e
  exact e.symm

/-- The proof of **Lemma 3.8(iii)**: "`If $A$ is sector-preserving, then $A$ commutes with $e^{\iu\varphi\cdot\mathbf N}$, hence $\iota(A)$ commutes with $e^{\iu\varphi\cdot\widehat{\mathbf N}}$ for all $\varphi$`" —
so `ι(A)` commutes with `N̂_↑` and `N̂_↓`. -/
theorem iota_isSectorPreservingS (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀) {A : FockOp T}
    (hA : IsSectorPreserving T A) : IsSectorPreservingS (iota η δ₀ T A) := by
  have hS : IsSectorPreservingS A := (isSectorPreserving_iff_S T A).mp hA
  rw [isSectorPreservingS_iff_gauge] at hS ⊢
  intro φ
  rw [← iota_gauge hη hδ₀ hT, hS φ]

/-! ### Proof devices for the approximants (phase (b); not statements of the paper)

The self-adjoint part `½(A' + A'^*)` of an element of `Alg(X)` stays in `Alg(X)` and is no farther from a self-adjoint
operator than `A'`. The sector-preserving case by the finite route (a route departure, ruled at review): the average of
the gauge conjugations over the grid `φ = (2πk/M, 2πl/M)`, `k, l < M`, `M = |𝒮| + 1`, has the entries of `A'` between
configurations of the same sector and `0` otherwise (it is the pinching `Σ_𝐧 P̂_𝐧 A' P̂_𝐧`), stays in `Alg(X)`, commutes
with `N̂_↑` and `N̂_↓`, and is no farther from a gauge-invariant operator than `A'`. -/

section ApproxDevices

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem saPart_mem_Alg {X : Finset S} {A' : Op S} (hA' : A' ∈ Alg X) : (1 / 2 : ℂ) • (A' + A'ᴴ) ∈ Alg X := by
  refine ⟨Subalgebra.smul_mem (CAR X).toSubalgebra
    (add_mem hA'.1 (Fermion.Pilot.JW.conjTranspose_mem_CAR hA'.1)) _, ?_⟩
  have h1 : Commute A'ᴴ parityOp := by
    have := congrArg Matrix.conjTranspose hA'.2.eq
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, parityOp_conjTranspose] at this
    exact this.symm
  exact (hA'.2.add_left h1).smul_left _

theorem saPart_isSelfAdjoint (A' : Op S) : IsSelfAdjoint ((1 / 2 : ℂ) • (A' + A'ᴴ)) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

theorem saPart_isSectorPreservingS {A' : Op S} (h : IsSectorPreservingS A') :
    IsSectorPreservingS ((1 / 2 : ℂ) • (A' + A'ᴴ)) := by
  have hN : ∀ σ, (numberOp σ : Op S)ᴴ = numberOp σ := by
    intro σ
    rw [numberOp_eq_diag, Matrix.diagonal_conjTranspose]
    congr 1
    funext m
    simp
  have hc : ∀ σ, Commute A' (numberOp σ) → Commute A'ᴴ (numberOp σ) := by
    intro σ hσ
    have := congrArg Matrix.conjTranspose hσ.eq
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hN] at this
    exact this.symm
  exact ⟨(h.1.add_left (hc _ h.1)).smul_left _, (h.2.add_left (hc _ h.2)).smul_left _⟩

open scoped Matrix.Norms.L2Operator in
theorem norm_sub_saPart_le {B A' : Op S} (hB : Bᴴ = B) :
    ‖B - (1 / 2 : ℂ) • (A' + A'ᴴ)‖ ≤ ‖B - A'‖ := by
  have e : B - (1 / 2 : ℂ) • (A' + A'ᴴ) = (1 / 2 : ℂ) • (B - A') + (1 / 2 : ℂ) • (B - A')ᴴ := by
    rw [Matrix.conjTranspose_sub, hB]
    module
  rw [e]
  calc ‖(1 / 2 : ℂ) • (B - A') + (1 / 2 : ℂ) • (B - A')ᴴ‖
      ≤ ‖(1 / 2 : ℂ) • (B - A')‖ + ‖(1 / 2 : ℂ) • (B - A')ᴴ‖ := norm_add_le _ _
    _ = ‖B - A'‖ := by
      rw [norm_smul, norm_smul, Matrix.l2_opNorm_conjTranspose]
      norm_num
      ring

/-- The phases of the grid. -/
def gridPhase (M : ℕ) (k l : Fin M) : Spin → ℝ := fun σ =>
  match σ with
  | .up => 2 * Real.pi * ((k : ℕ) : ℝ) / M
  | .dn => 2 * Real.pi * ((l : ℕ) : ℝ) / M

/-- The average of the gauge conjugations over the grid. -/
def gaugeAvg (M : ℕ) (A : Op S) : Op S :=
  ((M : ℂ) ^ 2)⁻¹ • ∑ k : Fin M, ∑ l : Fin M, Fermion.Pilot.JW.gauge (gridPhase M k l) A

theorem sum_exp_grid {M : ℕ} (hM : 0 < M) (d : ℤ) (hd : |d| < M) :
    ∑ k : Fin M, Complex.exp (I * (((2 * Real.pi * ((k : ℕ) : ℝ) / M : ℝ) : ℂ) * (d : ℂ))) =
      if d = 0 then (M : ℂ) else 0 := by
  have h := HRTorus.LLL.sum_exp_neg_two_pi M hM (-d) (by rwa [abs_neg])
  have e : ∀ k : Fin M, Complex.exp (I * (((2 * Real.pi * ((k : ℕ) : ℝ) / M : ℝ) : ℂ) * (d : ℂ))) =
      Complex.exp (-(2 * (Real.pi : ℂ) * I * (((-d : ℤ)) : ℂ) * (((k : ℕ) : ℤ) : ℂ) / ((M : ℕ) : ℂ))) := by
    intro k
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun k _ => e k, h]
  simp [neg_eq_zero]

theorem gaugeAvg_apply (A : Op S) (i j : Conf S) :
    gaugeAvg (Fintype.card S + 1) A i j = if secOfS i = secOfS j then A i j else 0 := by
  have hM0 : 0 < Fintype.card S + 1 := Nat.succ_pos _
  have hlt : ∀ (σ : Spin) (m m' : Conf S), |((ctS σ m : ℤ) - (ctS σ m' : ℤ))| < ((Fintype.card S + 1 : ℕ) : ℤ) := by
    intro σ m m'
    have h1 := ctS_le σ m
    have h2 := ctS_le σ m'
    rw [abs_lt]
    constructor <;> push_cast <;> omega
  have hentry : ∀ k l : Fin (Fintype.card S + 1),
      Fermion.Pilot.JW.gauge (gridPhase (Fintype.card S + 1) k l) A i j =
        Complex.exp (I * (((2 * Real.pi * ((k : ℕ) : ℝ) / ((Fintype.card S + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
            (((ctS .up i : ℤ) - (ctS .up j : ℤ) : ℤ) : ℂ))) *
          Complex.exp (I * (((2 * Real.pi * ((l : ℕ) : ℝ) / ((Fintype.card S + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
            (((ctS .dn i : ℤ) - (ctS .dn j : ℤ) : ℤ) : ℂ))) * A i j := by
    intro k l
    rw [gauge_apply, gaugePhase_eq, gaugePhase_eq, ← Complex.exp_add]
    congr 2
    simp only [gridPhase]
    push_cast
    ring
  rw [gaugeAvg, Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [Matrix.sum_apply, hentry]
  rw [show (∑ k : Fin (Fintype.card S + 1), ∑ l : Fin (Fintype.card S + 1),
      Complex.exp (I * (((2 * Real.pi * ((k : ℕ) : ℝ) / ((Fintype.card S + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
            (((ctS .up i : ℤ) - (ctS .up j : ℤ) : ℤ) : ℂ))) *
          Complex.exp (I * (((2 * Real.pi * ((l : ℕ) : ℝ) / ((Fintype.card S + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
            (((ctS .dn i : ℤ) - (ctS .dn j : ℤ) : ℤ) : ℂ))) * A i j) =
      (∑ k : Fin (Fintype.card S + 1),
        Complex.exp (I * (((2 * Real.pi * ((k : ℕ) : ℝ) / ((Fintype.card S + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
            (((ctS .up i : ℤ) - (ctS .up j : ℤ) : ℤ) : ℂ)))) *
      (∑ l : Fin (Fintype.card S + 1),
        Complex.exp (I * (((2 * Real.pi * ((l : ℕ) : ℝ) / ((Fintype.card S + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
            (((ctS .dn i : ℤ) - (ctS .dn j : ℤ) : ℤ) : ℂ)))) * A i j by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]]
  rw [sum_exp_grid hM0 _ (hlt .up i j), sum_exp_grid hM0 _ (hlt .dn i j)]
  have hMc : ((Fintype.card S + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  by_cases hs : secOfS i = secOfS j
  · have hs' := (secOfS_eq_iff i (secOfS j)).mp hs
    have hu : (ctS .up i : ℤ) - (ctS .up j : ℤ) = 0 := by
      have : ctS .up i = ctS .up j := hs'.1
      omega
    have hd : (ctS .dn i : ℤ) - (ctS .dn j : ℤ) = 0 := by
      have : ctS .dn i = ctS .dn j := hs'.2
      omega
    rw [if_pos hu, if_pos hd, if_pos hs, smul_eq_mul]
    field_simp
  · rw [if_neg hs]
    have hne : ¬((ctS .up i : ℤ) - (ctS .up j : ℤ) = 0 ∧ (ctS .dn i : ℤ) - (ctS .dn j : ℤ) = 0) := by
      rintro ⟨hu, hd⟩
      apply hs
      rw [secOfS_eq_iff]
      exact ⟨show ctS .up i = ctS .up j by omega, show ctS .dn i = ctS .dn j by omega⟩
    by_cases hu : (ctS .up i : ℤ) - (ctS .up j : ℤ) = 0
    · rw [if_neg (fun hd => hne ⟨hu, hd⟩), smul_eq_mul]
      simp
    · rw [if_neg hu, smul_eq_mul]
      simp

theorem gaugeAvg_mem_Alg {X : Finset S} {A : Op S} (hA : A ∈ Alg X) (M : ℕ) : gaugeAvg M A ∈ Alg X := by
  refine ⟨Subalgebra.smul_mem (CAR X).toSubalgebra
    (sum_mem fun k _ => sum_mem fun l _ => gauge_mem_CAR _ hA.1) _, ?_⟩
  have h : ∀ k l : Fin M, IsEven (Fermion.Pilot.JW.gauge (gridPhase M k l) A) := fun k l => isEven_gauge _ hA.2
  exact (Commute.sum_left _ _ _ fun k _ => Commute.sum_left _ _ _ fun l _ => h k l).smul_left _

theorem gaugeAvg_isSectorPreservingS (A : Op S) : IsSectorPreservingS (gaugeAvg (Fintype.card S + 1) A) := by
  rw [isSectorPreservingS_iff_entries]
  intro i j h
  rw [gaugeAvg_apply] at h
  by_contra hne
  exact h (if_neg hne)

open scoped Matrix.Norms.L2Operator in
theorem norm_sub_gaugeAvg_le {B A' : Op S} (hB : ∀ φ, Fermion.Pilot.JW.gauge φ B = B) (M : ℕ) (hM : 0 < M) :
    ‖B - gaugeAvg M A'‖ ≤ ‖B - A'‖ := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hg : ∀ φ, Fermion.Pilot.JW.gauge φ (B - A') = B - Fermion.Pilot.JW.gauge φ A' := by
    intro φ
    have := hB φ
    simp only [Fermion.Pilot.JW.gauge, Matrix.mul_sub, Matrix.sub_mul] at this ⊢
    rw [this]
  have hsplit : B - gaugeAvg M A' =
      ((M : ℂ) ^ 2)⁻¹ • ∑ k : Fin M, ∑ l : Fin M, Fermion.Pilot.JW.gauge (gridPhase M k l) (B - A') := by
    simp_rw [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub, gaugeAvg]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    rw [show ((M : ℂ) ^ 2)⁻¹ * (M : ℂ) * (M : ℂ) = 1 by field_simp, one_smul]
  have hiso : ∀ φ (Z : Op S), ‖Fermion.Pilot.JW.gauge φ Z‖ = ‖Z‖ := by
    intro φ Z
    rw [gauge_eq_conjAut]
    exact NonUnitalStarAlgHom.norm_map (Unitary.conjStarAlgAut ℂ (Op S) ⟨gaugeOp φ, gaugeOp_mem_unitary φ⟩)
      (Unitary.conjStarAlgAut ℂ (Op S) ⟨gaugeOp φ, gaugeOp_mem_unitary φ⟩).injective Z
  have hsum : ‖∑ k : Fin M, ∑ l : Fin M, Fermion.Pilot.JW.gauge (gridPhase M k l) (B - A')‖ ≤
      (M : ℝ) * (M : ℝ) * ‖B - A'‖ := by
    calc _ ≤ ∑ k : Fin M, ‖∑ l : Fin M, Fermion.Pilot.JW.gauge (gridPhase M k l) (B - A')‖ := norm_sum_le _ _
      _ ≤ ∑ k : Fin M, ∑ l : Fin M, ‖Fermion.Pilot.JW.gauge (gridPhase M k l) (B - A')‖ :=
          Finset.sum_le_sum fun k _ => norm_sum_le _ _
      _ = (M : ℝ) * (M : ℝ) * ‖B - A'‖ := by
          simp only [hiso, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hsplit, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  calc ((M : ℝ) ^ 2)⁻¹ * ‖∑ k : Fin M, ∑ l : Fin M, Fermion.Pilot.JW.gauge (gridPhase M k l) (B - A')‖
      ≤ ((M : ℝ) ^ 2)⁻¹ * ((M : ℝ) * (M : ℝ) * ‖B - A'‖) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖B - A'‖ := by field_simp

end ApproxDevices

/-- **Lemma 3.8(iii)**: "`Consequently, if $A$ is sector-preserving (respectively self-adjoint), then for every $X\subset\Slots$ and every $A'\in\Alg(X)$ there is $A''\in\Alg(X)$ that commutes with $\Nhat\up$ and $\Nhat\dn$ (respectively is self-adjoint, respectively both, if $A$ is both) and satisfies $\norm{\iota(A)-A''}\le\norm{\iota(A)-A'}$.`"
— the sector-preserving case. -/
theorem exists_approx_of_isSectorPreserving (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀)
    {A : FockOp T} (hA : IsSectorPreserving T A) (X : Finset (Slot δ₀ T)) {A' : Op (Slot δ₀ T)} (hA' : A' ∈ Alg X) :
    ∃ A'' ∈ Alg X, IsSectorPreservingS A'' ∧
      ‖opCLM (iota η δ₀ T A - A'')‖ ≤ ‖opCLM (iota η δ₀ T A - A')‖ := by
  refine ⟨gaugeAvg (Fintype.card (Slot δ₀ T) + 1) A', gaugeAvg_mem_Alg hA' _, gaugeAvg_isSectorPreservingS A', ?_⟩
  have hB := (isSectorPreservingS_iff_gauge _).mp (iota_isSectorPreservingS hη hδ₀ hT hA)
  open scoped Matrix.Norms.L2Operator in
  exact norm_sub_gaugeAvg_le hB _ (Nat.succ_pos _)

/-- **Lemma 3.8(iii)**, the self-adjoint case. -/
theorem exists_approx_of_isSelfAdjoint (hη : IsProfile η) (hδ₀ : 0 < δ₀) (hT : T.Admissible δ₀)
    {A : FockOp T} (hA : IsSelfAdjoint A) (X : Finset (Slot δ₀ T)) {A' : Op (Slot δ₀ T)} (hA' : A' ∈ Alg X) :
    ∃ A'' ∈ Alg X, IsSelfAdjoint A'' ∧
      ‖opCLM (iota η δ₀ T A - A'')‖ ≤ ‖opCLM (iota η δ₀ T A - A')‖ := by
  have hsa : (iota η δ₀ T A)ᴴ = iota η δ₀ T A := by
    rw [← iota_conjTranspose hη hδ₀ hT, ← Matrix.star_eq_conjTranspose, hA.star_eq]
  refine ⟨(1 / 2 : ℂ) • (A' + A'ᴴ), saPart_mem_Alg hA', saPart_isSelfAdjoint A', ?_⟩
  open scoped Matrix.Norms.L2Operator in
  exact norm_sub_saPart_le hsa

/-- **Lemma 3.8(iii)**, the case "`respectively both, if $A$ is both`". -/
theorem exists_approx_of_isSectorPreserving_of_isSelfAdjoint (hη : IsProfile η) (hδ₀ : 0 < δ₀)
    (hT : T.Admissible δ₀) {A : FockOp T} (hA : IsSectorPreserving T A) (hA2 : IsSelfAdjoint A)
    (X : Finset (Slot δ₀ T)) {A' : Op (Slot δ₀ T)} (hA' : A' ∈ Alg X) :
    ∃ A'' ∈ Alg X, IsSectorPreservingS A'' ∧ IsSelfAdjoint A'' ∧
      ‖opCLM (iota η δ₀ T A - A'')‖ ≤ ‖opCLM (iota η δ₀ T A - A')‖ := by
  obtain ⟨A₁, hA₁, hS₁, hn₁⟩ := exists_approx_of_isSectorPreserving hη hδ₀ hT hA X hA'
  have hsa : (iota η δ₀ T A)ᴴ = iota η δ₀ T A := by
    rw [← iota_conjTranspose hη hδ₀ hT, ← Matrix.star_eq_conjTranspose, hA2.star_eq]
  refine ⟨(1 / 2 : ℂ) • (A₁ + A₁ᴴ), saPart_mem_Alg hA₁, saPart_isSectorPreservingS hS₁, saPart_isSelfAdjoint A₁, ?_⟩
  have h2 : ‖opCLM (iota η δ₀ T A - (1 / 2 : ℂ) • (A₁ + A₁ᴴ))‖ ≤ ‖opCLM (iota η δ₀ T A - A₁)‖ := by
    open scoped Matrix.Norms.L2Operator in
    exact norm_sub_saPart_le hsa
  exact h2.trans hn₁

end Statements

end HRTorus.Fock
