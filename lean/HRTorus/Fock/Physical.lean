import HRTorus.LLL.Space
import HRTorus.Fermion.Pilot.JW
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Normed.Algebra.Exponential
import HRTorus.IndexCore.Sanity
import HRTorus.IndexCore.Translation

/-!
# The physical Fock space, its sectors and the many-body magnetic translation (`Fock.Physical`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **The definitions and statements were written
first and reviewed against the paper (phase (a)) and are unchanged; phase (b) added the proofs and the proof
devices, each section of which is marked as such. Every theorem is proved; there is no `sorry`.** The paper: the HR paper, `papers/hr/sections/02-setting.tex` —
Definition 2.5 `def:fock` and Lemma 2.6 `lem:sectors`; for the fit to `HRTorus.IndexCore.Orbital`, the property
list of Remark 8.7 `rem:loophole` (`sections/08-hollow-core.tex`).

## The model (the concrete Jordan–Wigner Fock space)

* `𝓗_N = 𝔉(𝔨_N)` is the Jordan–Wigner space of `HRTorus.Fermion.Pilot.JW` at the slot type `S := ZMod N_φ`:
  modes `(j, σ) ∈ ℤ_{N_φ} × {↑,↓}`, configurations `Conf = (modes → Bool)`, operators the matrices
  `FockOp T = Matrix Conf Conf ℂ`, the Hilbert space `FockSpace T = EuclideanSpace ℂ Conf` (operators act on it through
  `Matrix.toEuclideanCLM`, abbreviated `toCLM`). **The Jordan–Wigner numbering is the pilot's `num`**, i.e.
  `Fintype.equivFin (ZMod N_φ × Spin)`: one fixed, unspecified numbering; nothing stated below depends on it.
* `c(f)` for `f ∈ 𝔨_N` is `Σ_μ \overline{f_μ} c_μ` with the pilot's Jordan–Wigner `c_μ` (`cf`); the CAR are stated.
* The second quantization `𝔉(u)` is **defined** by its action on the occupation basis,
  `𝔉(u) c_{μ₁}^* ⋯ c_{μ_k}^* Ω = c(uδ_{μ₁})^* ⋯ c(uδ_{μ_k})^* Ω` (`secondQuant`, for any one-body matrix, square or
  rectangular, so that block B's `𝔉(𝒮)` is the same construction); the paper's characterization ("the unitary with
  `𝔉(u)c(f)𝔉(u)^* = c(uf)` that fixes the vacuum") is stated as theorems, uniqueness included. `Θ := 𝔉(θ_x ⊗ 1)^*`.
* The sectors are the joint eigenspaces of `N_↑`, `N_↓` (submodules of `FockSpace T`), `Π^𝐧` the orthogonal projection
  onto them (Mathlib's `starProjection`, carried back to a matrix); sector labels are `Fin (N_φ+1) × Fin (N_φ+1)`.
-/

open MeasureTheory
open scoped InnerProductSpace Real Matrix
open Complex (I)

noncomputable section

namespace HRTorus.Fock

open HRTorus.SlotFrame HRTorus.LLL
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op num numberOp parityOp IsEven)

/-! ## Annihilators of vectors and second quantization, for any finite slot type -/

section Generic

variable {S S' : Type*} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']

/-- The annihilator of a one-body vector `g = Σ_μ g_μ δ_μ` of `ℓ²(S) ⊗ ℂ²`, conjugate-linear in `g`:
`c(g) := Σ_μ \overline{g_μ} c_μ`, with the pilot's Jordan–Wigner annihilators `c_μ`. -/
def cVec (g : Mode S → ℂ) : Op S :=
  ∑ μ, star (g μ) • Fermion.Pilot.JW.c μ

/-- The vacuum configuration: every mode empty. -/
def vac : Conf S := fun _ => false

/-- The occupied modes of `m`, listed in the Jordan–Wigner order `num`. -/
def occList (m : Conf S) : List (Mode S) :=
  ((List.finRange (Fintype.card (Mode S))).filter fun i => m (num.symm i)).map num.symm

/-- **Second quantization** `𝔉(U)` of a one-body matrix `U` (the matrix of a linear map
`ℓ²(S) ⊗ ℂ² → ℓ²(S') ⊗ ℂ²` in the bases `δ_μ`): the matrix whose column `m` is
`c(Uδ_{μ₁})^* ⋯ c(Uδ_{μ_k})^* Ω`, where `μ₁, …, μ_k` are the occupied modes of `m` in Jordan–Wigner order (so that
the occupation basis vector is `c_{μ₁}^* ⋯ c_{μ_k}^* Ω`). For a unitary `u` on `𝔨_N` this is the paper's `𝔉(u)`
(`Ff_conj_cf`, `Ff_mulVec_vac`, `Ff_unique`); it is the formula of the proof of Lemma 3.8(i),
"`$\Ff(\Sa)c(h_1)^*\cdots c(h_p)^*\Omega_0=\chat(\Sa h_1)^*\cdots\chat(\Sa h_p)^*\widehat\Omega_0$`", on basis vectors. -/
def secondQuant (U : Matrix (Mode S') (Mode S) ℂ) : Matrix (Conf S') (Conf S) ℂ :=
  Matrix.of fun m' m => ((occList m).map fun μ => (cVec fun ν => U ν μ)ᴴ).prod m' vac

end Generic

/-! ## Proof devices for the generic constructions (phase (b); not statements of the paper)

The annihilators `cVec g` satisfy the CAR; products of anticommuting creators over a list sorted by the
Jordan–Wigner order move one creator into place with the sign of the modes passed (`mul_prod_orderedInsert`) or
vanish (`mul_prod_eq_zero_of_mem`); an annihilator moved through such a product onto the vacuum removes its mode
with the same sign (`mul_prod_mul_vac`). With `occList` these give the intertwining of `secondQuant U` with the
creators (any `U`) and with the annihilators (`Uᴴ U = 1`); and an operator commuting with every `c_μ` and `c_μ^*` is
a scalar, because the `c_μ` generate all operators (the pilot's `CAR_univ`). -/

section GenericProofs

open HRTorus.Fermion.Pilot.JW (c jwSign cnt chat CAR c_anticomm c_anticomm_star sum_mul_c sum_c_mul
  star_jwSign jwSign_eq CAR_univ c_apply)

variable {S S' : Type*} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']

theorem cVec_add_dev (g h : Mode S → ℂ) : cVec (g + h) = cVec g + cVec h := by
  simp only [cVec, Pi.add_apply, star_add, add_smul, Finset.sum_add_distrib]

theorem cVec_smul_dev (a : ℂ) (g : Mode S → ℂ) : cVec (a • g) = star a • cVec g := by
  simp only [cVec, Pi.smul_apply, smul_eq_mul, star_mul', Finset.smul_sum, smul_smul]

theorem conjTranspose_cVec (g : Mode S → ℂ) : (cVec g)ᴴ = ∑ μ, g μ • (c μ)ᴴ := by
  simp only [cVec, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_star]

theorem cVec_anticomm_star_dev (g h : Mode S → ℂ) :
    cVec g * (cVec h)ᴴ + (cVec h)ᴴ * cVec g = (∑ μ, star (g μ) * h μ) • (1 : Op S) := by
  have e1 : cVec g * (cVec h)ᴴ = ∑ μ, ∑ ν, (star (g μ) * h ν) • (c μ * (c ν)ᴴ) := by
    rw [conjTranspose_cVec, cVec, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => smul_mul_smul_comm _ _ _ _
  have e2 : (cVec h)ᴴ * cVec g = ∑ μ, ∑ ν, (star (g μ) * h ν) • ((c ν)ᴴ * c μ) := by
    rw [conjTranspose_cVec, cVec, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [smul_mul_smul_comm, mul_comm (h ν)]
  rw [e1, e2, ← Finset.sum_add_distrib, Finset.sum_smul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  simp_rw [← smul_add, c_anticomm_star, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem cVec_anticomm_dev (g h : Mode S → ℂ) : cVec g * cVec h + cVec h * cVec g = 0 := by
  have e1 : cVec g * cVec h = ∑ μ, ∑ ν, (star (g μ) * star (h ν)) • (c μ * c ν) := by
    rw [cVec, cVec, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => smul_mul_smul_comm _ _ _ _
  have e2 : cVec h * cVec g = ∑ μ, ∑ ν, (star (g μ) * star (h ν)) • (c ν * c μ) := by
    rw [cVec, cVec, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [smul_mul_smul_comm, mul_comm (star (h ν))]
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun ν _ => ?_
  rw [← smul_add, c_anticomm, smul_zero]

/-- The creators `c(g)^*` anticommute. -/
theorem cdag_anticomm (g h : Mode S → ℂ) :
    (cVec g)ᴴ * (cVec h)ᴴ + (cVec h)ᴴ * (cVec g)ᴴ = 0 := by
  rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_add, add_comm,
    cVec_anticomm_dev, Matrix.conjTranspose_zero]

/-- A creator squares to zero. -/
theorem cdag_mul_self (g : Mode S → ℂ) : (cVec g)ᴴ * (cVec g)ᴴ = 0 := by
  have h := cdag_anticomm g g
  rw [← two_smul ℂ] at h
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

/-- `c(g)` for the indicator of a mode is `c_μ`. -/
theorem cVec_single (μ : Mode S) : cVec (fun ν => if ν = μ then (1 : ℂ) else 0) = c μ := by
  simp [cVec]

/-! ### Products over lists of anticommuting operators -/

theorem mul_prod_eq_zero_of_mem {ι : Type*} [DecidableEq ι] (A : ι → Op S')
    (hanti : ∀ μ ν, A μ * A ν + A ν * A μ = 0) (hsq : ∀ μ, A μ * A μ = 0) {ν : ι} :
    ∀ {L : List ι}, ν ∈ L → A ν * (L.map A).prod = 0
  | [], h => by simp at h
  | μ :: L, h => by
    rw [List.map_cons, List.prod_cons]
    by_cases hμ : ν = μ
    · subst hμ; rw [← mul_assoc, hsq, zero_mul]
    · have hL : ν ∈ L := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h hμ
        · exact h
      have e : A ν * A μ = -(A μ * A ν) := eq_neg_of_add_eq_zero_left (hanti ν μ)
      rw [← mul_assoc, e, neg_mul, mul_assoc, mul_prod_eq_zero_of_mem A hanti hsq hL, mul_zero, neg_zero]

theorem mul_prod_orderedInsert {ι : Type*} [DecidableEq ι] (A : ι → Op S') (key : ι → ℕ)
    (hanti : ∀ μ ν, A μ * A ν + A ν * A μ = 0) (ν : ι) :
    ∀ (L : List ι), L.Pairwise (fun a b => key a < key b) → ν ∉ L →
      A ν * (L.map A).prod = ((-1 : ℂ) ^ (L.filter fun μ => key μ < key ν).length) •
        ((L.orderedInsert (fun a b => key a ≤ key b) ν).map A).prod
  | [], _, _ => by simp
  | μ :: L, hp, hν => by
    rw [List.pairwise_cons] at hp
    have hνL : ν ∉ L := fun h => hν (List.mem_cons_of_mem _ h)
    by_cases hle : key ν ≤ key μ
    · have hf : ((μ :: L).filter fun b => key b < key ν) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simpa using hle
        · have := hp.1 b hb; simp; omega
      rw [hf, List.orderedInsert_cons, ite_eq_left hle]
      simp
    · have hlt : key μ < key ν := by omega
      have hf : ((μ :: L).filter fun b => key b < key ν) = μ :: (L.filter fun b => key b < key ν) := by
        rw [List.filter_cons_of_pos (by simpa using hlt)]
      rw [hf, List.orderedInsert_cons, ite_eq_right hle, List.length_cons, List.map_cons, List.prod_cons,
        List.map_cons, List.prod_cons]
      have e : A ν * A μ = -(A μ * A ν) := eq_neg_of_add_eq_zero_left (hanti ν μ)
      rw [← mul_assoc, e, neg_mul, mul_assoc, mul_prod_orderedInsert A key hanti ν L hp.2 hνL,
        mul_smul_comm, pow_succ, mul_neg_one, neg_smul]

theorem mul_prod_mul_vac {ι : Type*} [DecidableEq ι] (A : ι → Op S') (B P0 : Op S') (key : ι → ℕ) (ν : ι)
    (hBA : ∀ μ, B * A μ + A μ * B = if μ = ν then 1 else 0) (hB0 : B * P0 = 0) :
    ∀ (L : List ι), L.Pairwise (fun a b => key a < key b) →
      B * (L.map A).prod * P0 = if ν ∈ L then ((-1 : ℂ) ^ (L.filter fun μ => key μ < key ν).length) •
        ((L.erase ν).map A).prod * P0 else 0
  | [], _ => by simp [hB0]
  | μ :: L, hp => by
    rw [List.pairwise_cons] at hp
    have ih := mul_prod_mul_vac A B P0 key ν hBA hB0 L hp.2
    have e : B * A μ = (if μ = ν then 1 else 0) - A μ * B := eq_sub_of_add_eq (hBA μ)
    rw [List.map_cons, List.prod_cons, ← mul_assoc, e, sub_mul, sub_mul, mul_assoc (A μ), mul_assoc (A μ), ih]
    by_cases hμ : μ = ν
    · subst hμ
      have hνL : μ ∉ L := fun h => lt_irrefl _ (hp.1 μ h)
      have hf : ((μ :: L).filter fun b => key b < key μ) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simp
        · have := hp.1 b hb; simp; omega
      simp [hνL, hf, List.erase_cons_head]
    · simp only [ite_eq_right hμ, zero_mul, zero_sub]
      by_cases hνL : ν ∈ L
      · have hlt : key μ < key ν := hp.1 ν hνL
        have hf : ((μ :: L).filter fun b => key b < key ν) = μ :: (L.filter fun b => key b < key ν) := by
          rw [List.filter_cons_of_pos (by simpa using hlt)]
        rw [ite_eq_left hνL, ite_eq_left (List.mem_cons_of_mem _ hνL), hf, List.length_cons,
          List.erase_cons_tail (by simpa using hμ), List.map_cons, List.prod_cons]
        simp only [smul_mul_assoc, mul_smul_comm, pow_succ, mul_neg_one, neg_smul, neg_mul, mul_assoc]
      · have : ν ∉ μ :: L := by
          intro h; rcases List.mem_cons.mp h with h | h
          · exact hμ h.symm
          · exact hνL h
        rw [ite_eq_right hνL, ite_eq_right this, mul_zero, neg_zero]

end GenericProofs

/-! ### The occupation lists, and second quantization through creators and annihilators (proof devices) -/

section GenericProofs2

open HRTorus.Fermion.Pilot.JW (c jwSign cnt chat CAR c_anticomm c_anticomm_star sum_mul_c sum_c_mul
  star_jwSign jwSign_eq jwSign_update_self CAR_univ c_apply)

variable {S S' : Type*} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']

theorem mem_occList (m : Conf S) (μ : Mode S) : μ ∈ occList m ↔ m μ = true := by
  simp only [occList, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro h; exact ⟨num μ, by simpa using h, by simp⟩

theorem occList_pairwise (m : Conf S) :
    (occList m).Pairwise (fun a b => (num a : ℕ) < (num b : ℕ)) := by
  rw [occList, List.pairwise_map]
  refine ((List.pairwise_lt_finRange _).filter _).imp ?_
  intro a b hab
  simpa using hab

theorem occList_nodup (m : Conf S) : (occList m).Nodup :=
  (occList_pairwise m).imp fun {a b} h hab => by subst hab; exact lt_irrefl _ h

theorem occList_update_true {m : Conf S} {ν : Mode S} (hm : m ν = false) :
    occList (Function.update m ν true) =
      (occList m).orderedInsert (fun a b => (num a : ℕ) ≤ (num b : ℕ)) ν := by
  have : Std.Total (fun a b : Mode S => (num a : ℕ) ≤ (num b : ℕ)) := ⟨fun a b => le_total _ _⟩
  have : IsTrans (Mode S) (fun a b : Mode S => (num a : ℕ) ≤ (num b : ℕ)) := ⟨fun a b c => le_trans⟩
  have hnd : (ν :: occList m).Nodup :=
    List.nodup_cons.mpr ⟨by rw [mem_occList, hm]; simp, occList_nodup m⟩
  refine List.Perm.eq_of_pairwise (le := fun a b : Mode S => (num a : ℕ) ≤ (num b : ℕ)) ?_ ?_ ?_ ?_
  · intro a b _ _ h1 h2; exact num.injective (Fin.ext (le_antisymm h1 h2))
  · exact (occList_pairwise _).imp le_of_lt
  · exact List.Pairwise.orderedInsert ν _ ((occList_pairwise m).imp le_of_lt)
  · refine List.Perm.trans ?_ (List.perm_orderedInsert _ ν _).symm
    rw [List.perm_ext_iff_of_nodup (occList_nodup _) hnd]
    intro a
    rw [List.mem_cons, mem_occList, mem_occList]
    by_cases h : a = ν
    · subst h; simp
    · simp [h]

theorem occList_update_false {m : Conf S} {ν : Mode S} (hm : m ν = true) :
    occList (Function.update m ν false) = @List.erase (Mode S) instBEqOfDecidableEq (occList m) ν := by
  let : BEq (Mode S) := instBEqOfDecidableEq
  refine List.Perm.eq_of_pairwise (le := fun a b : Mode S => (num a : ℕ) ≤ (num b : ℕ)) ?_ ?_ ?_ ?_
  · intro a b _ _ h1 h2; exact num.injective (Fin.ext (le_antisymm h1 h2))
  · exact (occList_pairwise _).imp le_of_lt
  · exact ((occList_pairwise m).sublist (List.erase_sublist ..)).imp le_of_lt
  · rw [List.perm_ext_iff_of_nodup (occList_nodup _) ((occList_nodup m).erase ν)]
    intro a
    rw [(occList_nodup m).mem_erase_iff, mem_occList, mem_occList]
    by_cases h : a = ν
    · subst h; simp
    · simp [h]

theorem length_filter_occList (m : Conf S) (ν : Mode S) :
    ((occList m).filter fun μ => (num μ : ℕ) < (num ν : ℕ)).length = cnt ν m := by
  rw [← List.toFinset_card_of_nodup ((occList_nodup m).filter _), cnt]
  congr 1
  ext μ
  simp only [List.mem_toFinset, List.mem_filter, mem_occList, decide_eq_true_eq, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.lt_def]
  exact and_comm

theorem occList_vac : occList (vac : Conf S) = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro μ
  rw [mem_occList]
  simp [vac]

theorem secondQuant_apply (U : Matrix (Mode S') (Mode S) ℂ) (m' : Conf S') (m : Conf S) :
    secondQuant U m' m = ((occList m).map fun μ => (cVec fun ν => U ν μ)ᴴ).prod m' vac := rfl

theorem secondQuant_apply_vac (U : Matrix (Mode S') (Mode S) ℂ) (m' : Conf S') :
    secondQuant U m' vac = if m' = vac then 1 else 0 := by
  rw [secondQuant_apply, occList_vac]
  simp [Matrix.one_apply]

/-- Second quantization intertwines the creators, for every one-body matrix `U`:
`𝔉(U) c_ν^* = c(Uδ_ν)^* 𝔉(U)`. -/
theorem secondQuant_mul_cdag (U : Matrix (Mode S') (Mode S) ℂ) (ν : Mode S) :
    secondQuant U * (c ν)ᴴ = (cVec fun ρ => U ρ ν)ᴴ * secondQuant U := by
  set B : Mode S → Op S' := fun μ => (cVec fun ρ => U ρ μ)ᴴ with hB
  have hanti : ∀ μ μ', B μ * B μ' + B μ' * B μ = 0 := fun μ μ' => cdag_anticomm _ _
  have hsq : ∀ μ, B μ * B μ = 0 := fun μ => cdag_mul_self _
  ext m' m
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ k, secondQuant U m' k * (c ν)ᴴ k m = if m ν = false then
      jwSign ν (Function.update m ν true) * secondQuant U m' (Function.update m ν true) else 0 := by
    have h2 : ∑ k, secondQuant U m' k * (c ν)ᴴ k m =
        star (∑ k, c ν m k * star (secondQuant U m' k)) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply, star_mul', star_star, mul_comm]
    rw [h2, sum_c_mul ν (fun k => star (secondQuant U m' k)) m]
    split_ifs <;> simp [star_jwSign]
  have hR : ∑ k, (cVec fun ρ => U ρ ν)ᴴ m' k * secondQuant U k m =
      (B ν * ((occList m).map B).prod) m' vac := by
    rw [Matrix.mul_apply]
    rfl
  rw [hL, hR]
  by_cases hm : m ν = true
  · rw [ite_eq_right (by simp [hm]), mul_prod_eq_zero_of_mem B hanti hsq ((mem_occList m ν).mpr hm)]
    rfl
  · have hm' : m ν = false := by simpa using hm
    have hνL : ν ∉ occList m := by rw [mem_occList]; simp [hm']
    have key := mul_prod_orderedInsert B (fun μ => (num μ : ℕ)) hanti ν (occList m) (occList_pairwise m) hνL
    beta_reduce at key
    rw [ite_eq_left hm', key, ← occList_update_true hm', length_filter_occList, Matrix.smul_apply, smul_eq_mul,
      jwSign_update_self, jwSign_eq, secondQuant_apply]

/-- `c_ρ` annihilates the vacuum. -/
theorem c_mul_single_vac (ρ : Mode S') :
    c ρ * Matrix.single (vac : Conf S') (vac : Conf S') (1 : ℂ) = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.single_apply, c_apply]
  by_cases hj : j = vac
  · subst hj; simp [vac]
  · simp [Ne.symm hj]

theorem mul_single_vac_apply (X : Op S') (m' : Conf S') :
    (X * Matrix.single (vac : Conf S') (vac : Conf S') (1 : ℂ)) m' vac = X m' vac := by
  rw [Matrix.mul_apply]
  simp [Matrix.single_apply]

/-- Second quantization of an isometry intertwines the annihilators: `𝔉(U) c_ν = c(Uδ_ν) 𝔉(U)` if `Uᴴ U = 1`. -/
theorem secondQuant_mul_c {U : Matrix (Mode S') (Mode S) ℂ} (hU : Uᴴ * U = 1) (ν : Mode S) :
    secondQuant U * c ν = cVec (fun ρ => U ρ ν) * secondQuant U := by
  set B : Mode S → Op S' := fun μ => (cVec fun ρ => U ρ μ)ᴴ with hB
  set P0 : Op S' := Matrix.single (vac : Conf S') (vac : Conf S') (1 : ℂ) with hP0
  have hBA : ∀ μ, cVec (fun ρ => U ρ ν) * B μ + B μ * cVec (fun ρ => U ρ ν) = if μ = ν then 1 else 0 := by
    intro μ
    rw [hB]
    simp only []
    rw [cVec_anticomm_star_dev]
    have e : (∑ ρ, star (U ρ ν) * U ρ μ) = (Uᴴ * U) ν μ := by
      rw [Matrix.mul_apply]
      simp [Matrix.conjTranspose_apply]
    rw [e, hU, Matrix.one_apply]
    by_cases h : μ = ν
    · subst h; simp
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h, zero_smul]
  have hB0 : cVec (fun ρ => U ρ ν) * P0 = 0 := by
    rw [cVec, Finset.sum_mul]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [smul_mul_assoc, hP0, c_mul_single_vac, smul_zero]
  ext m' m
  rw [Matrix.mul_apply, Matrix.mul_apply, sum_mul_c ν (fun k => secondQuant U m' k) m]
  have hR : ∑ k, cVec (fun ρ => U ρ ν) m' k * secondQuant U k m =
      (cVec (fun ρ => U ρ ν) * ((occList m).map B).prod * P0) m' vac := by
    rw [hP0, mul_single_vac_apply, Matrix.mul_apply]
    rfl
  rw [hR, mul_prod_mul_vac B (cVec fun ρ => U ρ ν) P0 (fun μ => (num μ : ℕ)) ν hBA hB0 (occList m)
    (occList_pairwise m)]
  by_cases hm : m ν = true
  · rw [ite_eq_left hm, ite_eq_left ((mem_occList m ν).mpr hm),
      secondQuant_apply U m' (Function.update m ν false), occList_update_false hm]
    rw [length_filter_occList, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul, hP0, mul_single_vac_apply,
      jwSign_eq, mul_comm]
  · rw [ite_eq_right hm, ite_eq_right (by rw [mem_occList]; exact hm), Matrix.zero_apply]

/-- An operator commuting with every `c_μ` and every `c_μ^*` is a multiple of the identity (the `c_μ` generate
all operators: the pilot's `CAR_univ`). -/
theorem exists_smul_one_of_commute_c {X : Op S} (h1 : ∀ μ, Commute X (c μ))
    (h2 : ∀ μ, Commute X (c μ)ᴴ) : ∃ a : ℂ, X = a • (1 : Op S) := by
  have hle : (CAR (Finset.univ : Finset S)).toSubalgebra ≤ Subalgebra.centralizer ℂ {X} := by
    rw [CAR, StarAlgebra.adjoin_toSubalgebra]
    apply Algebra.adjoin_le
    rintro A (⟨s, -, σ, rfl⟩ | hA)
    · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact (h1 (s, σ)).eq
    · obtain ⟨s, -, σ, hs⟩ := Set.mem_star.mp hA
      have hA' : A = (c (s, σ))ᴴ := by rw [← star_star A, hs]; rfl
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      rw [hA']
      exact (h2 (s, σ)).eq
  have hall : ∀ M : Op S, Commute M X := by
    intro M
    have hM : M ∈ (CAR (Finset.univ : Finset S)).toSubalgebra := by
      rw [StarSubalgebra.mem_toSubalgebra, CAR_univ]; trivial
    exact ((Subalgebra.mem_centralizer_iff ℂ).mp (hle hM) X rfl).symm
  obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_of_commute_single (M := X) (fun i j _ => hall _)
  exact ⟨a, by rw [← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

/-- Second quantization of a square isometry is an isometry: `𝔉(U)^* 𝔉(U) = 1` if `Uᴴ U = 1`. -/
theorem secondQuant_conjTranspose_mul_self {U : Matrix (Mode S) (Mode S) ℂ} (hU : Uᴴ * U = 1) :
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
    rw [mul_assoc, hc, ← mul_assoc, e, mul_assoc]
  have h2 : ∀ ν, Commute (Wᴴ * W) (c ν)ᴴ := by
    intro ν
    have e : Wᴴ * (cVec fun ρ => U ρ ν)ᴴ = (c ν)ᴴ * Wᴴ := by
      have := congrArg Matrix.conjTranspose (hc ν)
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at this
      exact this.symm
    show Wᴴ * W * (c ν)ᴴ = (c ν)ᴴ * (Wᴴ * W)
    rw [mul_assoc, hcd, ← mul_assoc, e, mul_assoc]
  obtain ⟨a, ha⟩ := exists_smul_one_of_commute_c h1 h2
  have hvv : (Wᴴ * W) vac vac = 1 := by
    rw [Matrix.mul_apply]
    simp [Matrix.conjTranspose_apply, hW, secondQuant_apply_vac]
  rw [ha] at hvv ⊢
  have ha1 : a = 1 := by simpa using hvv
  rw [ha1, one_smul]

end GenericProofs2

/-! ## Definition 2.5: the Fock space, the operators `c(f)`, `n_{jσ}`, `N_σ`, the sectors, `Θ` -/

section Physical

variable (T : Torus)

/-- The modes `(j, σ)` of `𝔨_N`. -/
abbrev Modes : Type := Mode (ZMod T.Nφ)

/-- **Definition 2.5**: "`Let $\Fock:=\Ff(\kN)$ be the fermionic Fock space over $\kN$ (of dimension $4^{\Nphi}$),
with annihilation operators $c(f)$, $f\in\kN$, conjugate-linear in $f$ and satisfying the canonical anticommutation
relations $\{c(f),c(g)^*\}=\ip fg$, $\{c(f),c(g)\}=0$`" — the space, `ℂ^{Conf}` with the occupation basis. -/
abbrev FockSpace : Type := EuclideanSpace ℂ (Conf (ZMod T.Nφ))

/-- Operators on `𝓗_N`, as matrices in the occupation basis. -/
abbrev FockOp : Type := Op (ZMod T.Nφ)

/-- An operator on `𝓗_N` as a continuous linear map (`Matrix.toEuclideanCLM`, a star-algebra isomorphism). -/
abbrev toCLM (A : FockOp T) : FockSpace T →L[ℂ] FockSpace T :=
  Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) A

/-- **Definition 2.5**: `c(f)` for `f ∈ 𝔨_N` ("`with annihilation operators $c(f)$, $f\in\kN$, conjugate-linear in $f$`"). -/
def cf (f : Space2 T) : FockOp T :=
  cVec fun μ => f μ

/-- **Definition 2.5**: "`c_{j\sigma}:=c(\psi_j\otimes\sigma),\qquad n_{j\sigma}:=c_{j\sigma}^*c_{j\sigma},\qquad
N_\sigma:=\sum_{j\in\Z_{\Nphi}}n_{j\sigma},\qquad S_z:=\tfrac12(\Nup-\Ndn)`" — `c_{jσ}`. -/
def cjs (j : ZMod T.Nφ) (σ : Spin) : FockOp T :=
  cf T (spinTensor (orb T j) σ)

/-- **Definition 2.5**: "`n_{j\sigma}:=c_{j\sigma}^*c_{j\sigma}`". -/
def njs (j : ZMod T.Nφ) (σ : Spin) : FockOp T :=
  (cjs T j σ)ᴴ * cjs T j σ

/-- **Definition 2.5**: "`N_\sigma:=\sum_{j\in\Z_{\Nphi}}n_{j\sigma}`". -/
def Nsig (σ : Spin) : FockOp T :=
  ∑ j, njs T j σ

/-- **Definition 2.5**: "`S_z:=\tfrac12(\Nup-\Ndn)`". -/
def Sz : FockOp T :=
  (1 / 2 : ℂ) • (Nsig T .up - Nsig T .dn)

/-- The sector labels `𝐧 = (n_↑, n_↓) ∈ {0, …, N_φ}²`. -/
abbrev SectorLabel : Type := Fin (T.Nφ + 1) × Fin (T.Nφ + 1)

/-- **Definition 2.5**: "`For $\nn=(n_\up,n_\dn)\in\{0,\dots,\Nphi\}^2$ the \emph{sector} $\sect\nn$ is the joint
eigenspace $\{\Psi:\Nup\Psi=n_\up\Psi,\ \Ndn\Psi=n_\dn\Psi\}$, and $\Psec\nn$ is the orthogonal projection onto
it`" — the sector. -/
def sector (nn : SectorLabel T) : Submodule ℂ (FockSpace T) :=
  Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ))
      (Nsig T .up)) (((nn.1 : ℕ) : ℝ) : ℂ) ⊓
    Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ))
      (Nsig T .dn)) (((nn.2 : ℕ) : ℝ) : ℂ)

/-- **Definition 2.5**: "`and $\Psec\nn$ is the orthogonal projection onto it`", as a matrix. -/
def Psec (nn : SectorLabel T) : FockOp T :=
  (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)).symm (sector T nn).starProjection

/-- **Definition 2.5**: "`An operator $A$ on $\Fock$ is \emph{sector-preserving} if $[A,\Nup]=[A,\Ndn]=0$, and
\emph{even} if it commutes with the parity $(-1)^{\Nup+\Ndn}$`" — sector-preserving (even is the pilot's `IsEven`). -/
def IsSectorPreserving (A : FockOp T) : Prop :=
  Commute A (Nsig T .up) ∧ Commute A (Nsig T .dn)

/-- `θ_x ⊗ 1` on `𝔨_N`: its matrix in the basis `ψ_j ⊗ σ` (Kronecker product with `1_{ℂ²}`). -/
def thx2 : Matrix (Modes T) (Modes T) ℂ :=
  Matrix.kronecker (thxMat T) (1 : Matrix Spin Spin ℂ)

/-- **Definition 2.5**: "`For a unitary $u$ on $\kN$, $\Ff(u)$ denotes its second quantization, the unitary on
$\Fock$ with $\Ff(u)c(f)\Ff(u)^*=c(uf)$ that fixes the vacuum`" — `𝔉(u)` for a one-body matrix `u` on `𝔨_N`. -/
def Ff (u : Matrix (Modes T) (Modes T) ℂ) : FockOp T :=
  secondQuant u

/-- **Definition 2.5**: "`The \emph{many-body magnetic translation} is $\Theta:=\Ff(\thx\otimes\one)^*$`". -/
def Θ : FockOp T :=
  (Ff T (thx2 T))ᴴ

/-! ### Statements of Definition 2.5 -/

/-! ### Proof devices for the statements of Definition 2.5 (phase (b); not statements of the paper) -/

section PhysDevices1

open HRTorus.Fermion.Pilot.JW (c chat)

/-- `c(g)` through `𝔉(U)` for an isometry `U`: `𝔉(U) c(g) = c(Ug) 𝔉(U)`. -/
theorem secondQuant_mul_cVec {S S' : Type*} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']
    {U : Matrix (Mode S') (Mode S) ℂ} (hU : Uᴴ * U = 1) (g : Mode S → ℂ) :
    secondQuant U * cVec g = cVec (U *ᵥ g) * secondQuant U := by
  have e : cVec (U *ᵥ g) = ∑ ν, star (g ν) • cVec (fun ρ => U ρ ν) := by
    simp only [cVec, Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_smul, Finset.smul_sum,
      smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun ρ _ => by rw [mul_comm]
  rw [e, Matrix.sum_mul, cVec, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Matrix.mul_smul, secondQuant_mul_c hU, Matrix.smul_mul]

theorem conjTranspose_mul_self_of_mem_unitary {n : Type*} [Fintype n] [DecidableEq n]
    {u : Matrix n n ℂ} (hu : u ∈ unitary (Matrix n n ℂ)) : uᴴ * u = 1 := by
  have := Unitary.star_mul_self_of_mem hu
  rwa [Matrix.star_eq_conjTranspose] at this

theorem mul_conjTranspose_self_of_mem_unitary {n : Type*} [Fintype n] [DecidableEq n]
    {u : Matrix n n ℂ} (hu : u ∈ unitary (Matrix n n ℂ)) : u * uᴴ = 1 := by
  have := Unitary.mul_star_self_of_mem hu
  rwa [Matrix.star_eq_conjTranspose] at this

theorem cf_single (T : Torus) (μ : Modes T) :
    cf T (EuclideanSpace.single μ 1) = c μ := by
  rw [cf, ← cVec_single]
  congr 1
  funext ν
  simp [PiLp.single_apply]

end PhysDevices1

/-- **Definition 2.5**: `𝓗_N` has dimension `4^{N_φ}` ("`(of dimension $4^{\Nphi}$)`"). -/
theorem card_conf : Fintype.card (Conf (ZMod T.Nφ)) = 4 ^ T.Nφ := by
  have hs : Fintype.card Spin = 2 := rfl
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod, ZMod.card, hs, pow_mul']
  norm_num

/-- **Definition 2.5**: "`conjugate-linear in $f$`" — additivity. -/
theorem cf_add (f g : Space2 T) : cf T (f + g) = cf T f + cf T g := by
  simp only [cf, cVec, PiLp.add_apply, star_add, add_smul, Finset.sum_add_distrib]

/-- **Definition 2.5**: "`conjugate-linear in $f$`" — `c(af) = \bar a c(f)`. -/
theorem cf_smul (a : ℂ) (f : Space2 T) : cf T (a • f) = star a • cf T f := by
  simp only [cf, cVec, PiLp.smul_apply, smul_eq_mul, star_mul', Finset.smul_sum, smul_smul]

/-- **Definition 2.5**, the CAR: "`$\{c(f),c(g)^*\}=\ip fg$`". -/
theorem cf_anticomm_star (f g : Space2 T) :
    cf T f * (cf T g)ᴴ + (cf T g)ᴴ * cf T f = ⟪f, g⟫_ℂ • (1 : FockOp T) := by
  rw [cf, cf, cVec_anticomm_star_dev]
  congr 1
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- **Definition 2.5**, the CAR: "`$\{c(f),c(g)\}=0$`". -/
theorem cf_anticomm (f g : Space2 T) : cf T f * cf T g + cf T g * cf T f = 0 := by
  exact cVec_anticomm_dev _ _

/-- `c_{jσ}` is the Jordan–Wigner annihilator of the mode `(j, σ)`. -/
theorem cjs_eq (j : ZMod T.Nφ) (σ : Spin) : cjs T j σ = Fermion.Pilot.JW.c (j, σ) := by
  rw [cjs, cf, ← cVec_single]
  congr 1
  funext μ
  simp only [spinTensor, orb, PiLp.toLp_apply, PiLp.single_apply]
  by_cases h1 : μ.1 = j <;> by_cases h2 : μ.2 = σ <;> simp [h1, h2, Prod.ext_iff]

/-- `N_σ` is the pilot's number operator (diagonal: the number of occupied modes of spin `σ`). -/
theorem Nsig_eq_numberOp (σ : Spin) : Nsig T σ = numberOp σ := by
  simp only [Nsig, njs, cjs_eq, numberOp]
  rfl

/-- `θ_x ⊗ 1` is the paper's: on `f ⊗ σ` it gives `(θ_x f) ⊗ σ`. -/
theorem thx2_spinTensor (f : Space T) (σ : Spin) :
    Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) (thx2 T) (spinTensor f σ) = spinTensor (thx T f) σ := by
  refine PiLp.ext fun μ => ?_
  rcases μ with ⟨i, τ⟩
  show (Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) (thx2 T) (spinTensor f σ)).ofLp (i, τ) =
    (spinTensor (thx T f) σ).ofLp (i, τ)
  rw [Matrix.ofLp_toEuclideanCLM]
  simp only [spinTensor, thx, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, thx2,
    WithLp.ofLp_toLp, Matrix.ofLp_toEuclideanCLM]
  by_cases h : τ = σ
  · subst h; simp
  · simp [h]

/-- **Definition 2.5**, `𝔉(u)` is unitary for unitary `u` ("`the unitary on $\Fock$`"). -/
theorem Ff_mem_unitary {u : Matrix (Modes T) (Modes T) ℂ} (hu : u ∈ unitary (Matrix (Modes T) (Modes T) ℂ)) :
    Ff T u ∈ unitary (FockOp T) := by
  have h := secondQuant_conjTranspose_mul_self (conjTranspose_mul_self_of_mem_unitary hu)
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
  exact ⟨h, mul_eq_one_comm.mp h⟩

/-- **Definition 2.5**, "`$\Ff(u)c(f)\Ff(u)^*=c(uf)$`" for unitary `u`. -/
theorem Ff_conj_cf {u : Matrix (Modes T) (Modes T) ℂ} (hu : u ∈ unitary (Matrix (Modes T) (Modes T) ℂ))
    (f : Space2 T) :
    Ff T u * cf T f * (Ff T u)ᴴ = cf T (Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) u f) := by
  have hU := conjTranspose_mul_self_of_mem_unitary hu
  have hsq : secondQuant u * (secondQuant u)ᴴ = 1 :=
    mul_eq_one_comm.mp (secondQuant_conjTranspose_mul_self hU)
  rw [Ff, cf, cf, secondQuant_mul_cVec hU, mul_assoc, hsq, mul_one]
  rfl

/-- **Definition 2.5**, `𝔉(u)` fixes the vacuum `Ω` (the basis vector of the empty configuration): "`that fixes the
vacuum`". -/
theorem Ff_mulVec_vac (u : Matrix (Modes T) (Modes T) ℂ) :
    (Ff T u).mulVec (Pi.single (vac : Conf (ZMod T.Nφ)) (1 : ℂ)) =
      Pi.single (vac : Conf (ZMod T.Nφ)) (1 : ℂ) := by
  rw [Matrix.mulVec_single_one]
  funext m'
  rw [Matrix.col_apply, Ff, secondQuant_apply_vac]
  simp [Pi.single_apply]

/-- **Definition 2.5**, uniqueness: a unitary `W` with `W c(f) W^* = c(uf)` for all `f` that fixes the vacuum
is `𝔉(u)` ("`the unitary on $\Fock$ with $\Ff(u)c(f)\Ff(u)^*=c(uf)$ that fixes the vacuum`"). -/
theorem Ff_unique {u : Matrix (Modes T) (Modes T) ℂ} (hu : u ∈ unitary (Matrix (Modes T) (Modes T) ℂ))
    {W : FockOp T} (hW : W ∈ unitary (FockOp T))
    (hWc : ∀ f : Space2 T, W * cf T f * Wᴴ = cf T (Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) u f))
    (hWv : W.mulVec (Pi.single (vac : Conf (ZMod T.Nφ)) (1 : ℂ)) =
      Pi.single (vac : Conf (ZMod T.Nφ)) (1 : ℂ)) :
    W = Ff T u := by
  have hU := conjTranspose_mul_self_of_mem_unitary hu
  set F := Ff T u with hFdef
  have hF1 : Fᴴ * F = 1 := secondQuant_conjTranspose_mul_self hU
  have hF2 : F * Fᴴ = 1 := mul_eq_one_comm.mp hF1
  have hW1 : Wᴴ * W = 1 := conjTranspose_mul_self_of_mem_unitary hW
  have hW2 : W * Wᴴ = 1 := mul_conjTranspose_self_of_mem_unitary hW
  have hFc : ∀ f : Space2 T, F * cf T f =
      cf T (Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) u f) * F := by
    intro f
    rw [hFdef, Ff, cf, cf, secondQuant_mul_cVec hU]
    rfl
  have hWc' : ∀ f : Space2 T, W * cf T f =
      cf T (Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) u f) * W := by
    intro f
    calc W * cf T f = W * cf T f * (Wᴴ * W) := by rw [hW1, mul_one]
      _ = W * cf T f * Wᴴ * W := by simp only [mul_assoc]
      _ = _ := by rw [hWc f]
  -- the adjoint relations
  have adj : ∀ (V : FockOp T), Vᴴ * V = 1 → V * Vᴴ = 1 → ∀ f : Space2 T,
      V * cf T f = cf T (Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) u f) * V →
      V * (cf T f)ᴴ = (cf T (Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) u f))ᴴ * V := by
    intro V hV1 hV2 f hVf
    have h := congrArg Matrix.conjTranspose hVf
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul] at h
    calc V * (cf T f)ᴴ = V * (cf T f)ᴴ * (Vᴴ * V) := by rw [hV1, mul_one]
      _ = V * ((cf T f)ᴴ * Vᴴ) * V := by simp only [mul_assoc]
      _ = V * (Vᴴ * (cf T (Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) u f))ᴴ) * V := by rw [h]
      _ = (V * Vᴴ) * (cf T (Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) u f))ᴴ * V := by
          simp only [mul_assoc]
      _ = _ := by rw [hV2, one_mul]
  -- moving `Fᴴ` through: `Fᴴ X' = X Fᴴ` whenever `F X = X' F`
  have back : ∀ (A A' : FockOp T), F * A = A' * F → Fᴴ * A' = A * Fᴴ := by
    intro A A' h
    calc Fᴴ * A' = Fᴴ * A' * (F * Fᴴ) := by rw [hF2, mul_one]
      _ = Fᴴ * (A' * F) * Fᴴ := by simp only [mul_assoc]
      _ = Fᴴ * (F * A) * Fᴴ := by rw [h]
      _ = (Fᴴ * F) * A * Fᴴ := by simp only [mul_assoc]
      _ = A * Fᴴ := by rw [hF1, one_mul]
  have hX1 : ∀ μ : Modes T, Commute (Fᴴ * W) (Fermion.Pilot.JW.c μ) := by
    intro μ
    rw [← cf_single]
    show Fᴴ * W * cf T _ = cf T _ * (Fᴴ * W)
    rw [mul_assoc, hWc', ← mul_assoc, back _ _ (hFc _), mul_assoc]
  have hX2 : ∀ μ : Modes T, Commute (Fᴴ * W) (Fermion.Pilot.JW.c μ)ᴴ := by
    intro μ
    rw [← cf_single]
    show Fᴴ * W * (cf T _)ᴴ = (cf T _)ᴴ * (Fᴴ * W)
    rw [mul_assoc, adj W hW1 hW2 _ (hWc' _), ← mul_assoc,
      back _ _ (adj F hF1 hF2 _ (hFc _)), mul_assoc]
  obtain ⟨a, ha⟩ := exists_smul_one_of_commute_c hX1 hX2
  have hWvv : W vac vac = 1 := by
    have := congrFun hWv vac
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
    simpa using this
  have hvv : (Fᴴ * W) vac vac = 1 := by
    rw [Matrix.mul_apply]
    simp [Matrix.conjTranspose_apply, hFdef, Ff, secondQuant_apply_vac, hWvv]
  rw [ha] at hvv
  have ha1 : a = 1 := by simpa using hvv
  rw [ha1, one_smul] at ha
  calc W = (F * Fᴴ) * W := by rw [hF2, one_mul]
    _ = F * (Fᴴ * W) := by rw [mul_assoc]
    _ = F := by rw [ha, mul_one]

/-! ## Lemma 2.6 (i)–(ii): sectors -/

/-! ### Proof devices for the sectors (phase (b); not statements of the paper) -/

/-- The number of occupied modes of spin `σ` in the configuration `m`. -/
def ctσ (σ : Spin) (m : Conf (ZMod T.Nφ)) : ℕ :=
  (Finset.univ.filter fun j : ZMod T.Nφ => m (j, σ) = true).card

theorem ctσ_le (σ : Spin) (m : Conf (ZMod T.Nφ)) : ctσ T σ m ≤ T.Nφ := by
  rw [ctσ]
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, ZMod.card])

/-- The sector label of a configuration. -/
def secOf (m : Conf (ZMod T.Nφ)) : SectorLabel T :=
  (⟨ctσ T .up m, Nat.lt_succ_of_le (ctσ_le T .up m)⟩, ⟨ctσ T .dn m, Nat.lt_succ_of_le (ctσ_le T .dn m)⟩)

theorem secOf_eq_iff (m : Conf (ZMod T.Nφ)) (nn : SectorLabel T) :
    secOf T m = nn ↔ ctσ T .up m = nn.1 ∧ ctσ T .dn m = nn.2 := by
  rw [secOf, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]

theorem Nsig_eq_diag (σ : Spin) : Nsig T σ = Matrix.diagonal fun m => (ctσ T σ m : ℂ) := by
  rw [Nsig_eq_numberOp, Fermion.Pilot.JW.numberOp_eq]
  rfl

theorem Nsig_conjTranspose (σ : Spin) : (Nsig T σ)ᴴ = Nsig T σ := by
  rw [Nsig_eq_diag, Matrix.diagonal_conjTranspose]
  congr 1
  funext m
  simp

theorem commute_diagonal_iff {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (d : n → ℂ) :
    Commute A (Matrix.diagonal d) ↔ ∀ i j, A i j * d j = d i * A i j := by
  constructor
  · intro h i j
    have := congrFun (congrFun h.eq i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  · intro h
    show A * Matrix.diagonal d = Matrix.diagonal d * A
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, h]

theorem isSectorPreserving_iff_entries (A : FockOp T) :
    IsSectorPreserving T A ↔ ∀ i j, A i j ≠ 0 → secOf T i = secOf T j := by
  rw [IsSectorPreserving, Nsig_eq_diag, Nsig_eq_diag, commute_diagonal_iff, commute_diagonal_iff]
  constructor
  · rintro ⟨h1, h2⟩ i j hA
    have e1 := h1 i j; have e2 := h2 i j
    rw [mul_comm] at e1 e2
    have u := mul_right_cancel₀ hA e1
    have d := mul_right_cancel₀ hA e2
    rw [secOf_eq_iff]
    exact ⟨(Nat.cast_injective u).symm, (Nat.cast_injective d).symm⟩
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
    · by_cases hA : A i j = 0
      · simp [hA]
      · have := (secOf_eq_iff T i (secOf T j)).mp (h i j hA)
        rw [mul_comm]
        congr 2
        first | exact this.1.symm | exact this.2.symm

theorem mem_sector_iff (nn : SectorLabel T) (v : FockSpace T) :
    v ∈ sector T nn ↔ ∀ m, v m ≠ 0 → secOf T m = nn := by
  rw [sector, Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff,
    Nsig_eq_diag, Nsig_eq_diag]
  have key : ∀ (d : Conf (ZMod T.Nφ) → ℂ) (μ : ℂ),
      Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (Matrix.diagonal d) v = μ • v ↔
        ∀ m, v m ≠ 0 → d m = μ := by
    intro d μ
    constructor
    · intro h m hm
      have := congrArg (fun w : FockSpace T => w m) h
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
    rw [secOf_eq_iff]
    exact ⟨by exact_mod_cast h1 m hm, by exact_mod_cast h2 m hm⟩
  · intro h
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have := (secOf_eq_iff T m nn).mp (h m hm); simp [this.1]
    · have := (secOf_eq_iff T m nn).mp (h m hm); simp [this.2]

/-- The indicator of the configurations of a sector. -/
def secInd (nn : SectorLabel T) (m : Conf (ZMod T.Nφ)) : ℂ := if secOf T m = nn then 1 else 0

theorem toCLM_diag_secInd (nn : SectorLabel T) :
    toCLM T (Matrix.diagonal (secInd T nn)) = (sector T nn).starProjection := by
  ext v : 1
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [mem_sector_iff]
    intro m hm
    by_contra hne
    apply hm
    simp [toCLM, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal, secInd, hne]
  · intro w hw
    rw [mem_sector_iff] at hw
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hwm : w m = 0
    · simp [hwm]
    · have := hw m hwm
      simp [toCLM, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal, secInd, this]

theorem Psec_eq_diag (nn : SectorLabel T) : Psec T nn = Matrix.diagonal (secInd T nn) := by
  rw [Psec, ← toCLM_diag_secInd]
  exact (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)).symm_apply_apply _


/-- **Lemma 2.6(i)**: "`$\Fock=\bigoplus_\nn\sect\nn$, an orthogonal sum, and
$\Psec\nn=\one_{\{n_\up\}}(\Nup)\,\one_{\{n_\dn\}}(\Ndn)$`" — the sectors are mutually orthogonal. -/
theorem orthogonalFamily_sector :
    OrthogonalFamily ℂ (fun nn : SectorLabel T => ↥(sector T nn)) fun nn => (sector T nn).subtypeₗᵢ := by
  intro nn nn' hne v w
  simp only [Submodule.coe_subtypeₗᵢ]
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hv : (v : FockSpace T) m = 0
  · simp [hv]
  · by_cases hw : (w : FockSpace T) m = 0
    · simp [hw]
    · exfalso
      exact hne (((mem_sector_iff T nn _).mp v.2 m hv).symm.trans ((mem_sector_iff T nn' _).mp w.2 m hw))

/-- **Lemma 2.6(i)**: "`$\Fock=\bigoplus_\nn\sect\nn$, an orthogonal sum`" — the sectors span `𝓗_N` (an internal direct sum). -/
theorem isInternal_sector : DirectSum.IsInternal fun nn : SectorLabel T => sector T nn := by
  rw [(orthogonalFamily_sector T).isInternal_iff, Submodule.eq_bot_iff]
  intro v hv
  refine PiLp.ext fun m => ?_
  have hmem : EuclideanSpace.single m (1 : ℂ) ∈ ⨆ nn, sector T nn := by
    refine Submodule.mem_iSup_of_mem (secOf T m) ?_
    rw [mem_sector_iff]
    intro m' hm'
    by_cases h : m' = m
    · rw [h]
    · exact absurd (by simp [h]) hm'
  have := (Submodule.mem_orthogonal _ _).mp hv _ hmem
  rw [EuclideanSpace.inner_single_left] at this
  simpa using this

/-- Polynomial interpolation on a finite set of reals (a proof device). -/
theorem exists_poly_interp (S : Finset ℝ) (f : ℝ → ℝ) : ∃ q : Polynomial ℝ, ∀ x ∈ S, q.eval x = f x := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | insert a S ha ih =>
    obtain ⟨q, hq⟩ := ih
    have hw : ∀ x ∈ S, (∏ y ∈ S, (Polynomial.X - Polynomial.C y)).eval x = 0 := fun x hx => by
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero hx (by simp)
    have hwa : (∏ y ∈ S, (Polynomial.X - Polynomial.C y)).eval a ≠ 0 := by
      rw [Polynomial.eval_prod]
      refine Finset.prod_ne_zero_iff.mpr fun y hy => ?_
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.mpr fun h => ha (h ▸ hy)
    refine ⟨q + Polynomial.C ((f a - q.eval a) / (∏ y ∈ S, (Polynomial.X - Polynomial.C y)).eval a) *
      ∏ y ∈ S, (Polynomial.X - Polynomial.C y), fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, div_mul_cancel₀ _ hwa]
      ring
    · rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hw x hx, mul_zero, add_zero, hq x hx]

/-- The continuous functional calculus of a real diagonal matrix: `f(diag d) = diag (f ∘ d)` (a proof device,
by interpolating `f` on the finite spectrum by a polynomial). -/
theorem cfc_diagonal_ofReal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal fun i => (d i : ℂ)) = Matrix.diagonal fun i => ((f (d i) : ℝ) : ℂ) := by
  have hspec : spectrum ℝ (Matrix.diagonal fun i => (d i : ℂ)) = Set.range d := by
    rw [← spectrum.preimage_algebraMap ℂ, spectrum_diagonal]
    ext x
    simp only [Set.mem_preimage, Set.mem_range, Complex.coe_algebraMap, Complex.ofReal_inj]
  have hsa : IsSelfAdjoint (Matrix.diagonal fun i => (d i : ℂ)) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [Complex.conj_ofReal]
  obtain ⟨q, hq⟩ := exists_poly_interp (Finset.univ.image d) f
  have hqf : ∀ i, q.eval (d i) = f (d i) := fun i =>
    hq _ (Finset.mem_image_of_mem d (Finset.mem_univ i))
  rw [cfc_congr (g := fun x => q.eval x) ?_, cfc_polynomial q _ hsa]
  · rw [show (Matrix.diagonal fun i => (d i : ℂ)) = Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) from rfl,
      Polynomial.aeval_algHom_apply]
    show Matrix.diagonal _ = _
    congr 1
    funext i
    rw [← hqf i]
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : n => ℂ) i) (fun j => (d j : ℂ)) q
    simp only [Pi.evalAlgHom_apply] at this
    rw [← this, show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl,
      Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
    rfl
  · intro x hx
    rw [hspec] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hqf i).symm


/-- **Lemma 2.6(i)**: "`$\Psec\nn=\one_{\{n_\up\}}(\Nup)\,\one_{\{n_\dn\}}(\Ndn)$`" (the continuous functional calculus of the
Hermitian matrices `N_σ`; on their finite spectra every function is continuous). -/
theorem Psec_eq_cfc (nn : SectorLabel T) :
    Psec T nn =
      cfc (Set.indicator ({((nn.1 : ℕ) : ℝ)} : Set ℝ) (1 : ℝ → ℝ)) (Nsig T .up) *
        cfc (Set.indicator ({((nn.2 : ℕ) : ℝ)} : Set ℝ) (1 : ℝ → ℝ)) (Nsig T .dn) := by
  have e : ∀ σ : Spin, Nsig T σ = Matrix.diagonal fun m => (((ctσ T σ m : ℕ) : ℝ) : ℂ) := by
    intro σ
    rw [Nsig_eq_diag]
    rfl
  rw [Psec_eq_diag, e, e, cfc_diagonal_ofReal, cfc_diagonal_ofReal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext m
  simp only [secInd, secOf_eq_iff, Set.indicator, Set.mem_singleton_iff, Pi.one_apply, Nat.cast_inj]
  by_cases h1 : ctσ T .up m = (nn.1 : ℕ) <;> by_cases h2 : ctσ T .dn m = (nn.2 : ℕ) <;> simp [h1, h2]

/-- `Π^𝐧` is diagonal in the occupation basis: the indicator of the configurations with `n_↑` up-spins and
`n_↓` down-spins. -/
theorem Psec_eq_diagonal (nn : SectorLabel T) :
    Psec T nn = Matrix.diagonal fun m : Conf (ZMod T.Nφ) =>
      if (Finset.univ.filter fun j => m (j, .up) = true).card = (nn.1 : ℕ) ∧
          (Finset.univ.filter fun j => m (j, .dn) = true).card = (nn.2 : ℕ) then 1 else 0 := by
  rw [Psec_eq_diag]
  congr 1
  funext m
  simp only [secInd, secOf_eq_iff]
  rfl

/-- **Lemma 2.6(ii)**: "`An operator $A$ is sector-preserving if and only if $A=\sum_\nn\Psec\nn A\Psec\nn$, if and
only if $[A,\Psec\nn]=0$ for every $\nn$`" — the first equivalence. -/
theorem isSectorPreserving_iff_sum (A : FockOp T) :
    IsSectorPreserving T A ↔ A = ∑ nn : SectorLabel T, Psec T nn * A * Psec T nn := by
  rw [isSectorPreserving_iff_entries]
  have hsum : ∀ i j, (∑ nn : SectorLabel T, Psec T nn * A * Psec T nn) i j =
      if secOf T i = secOf T j then A i j else 0 := by
    intro i j
    rw [Matrix.sum_apply]
    have hterm : ∀ nn : SectorLabel T, (Psec T nn * A * Psec T nn) i j =
        if secOf T i = nn ∧ secOf T j = nn then A i j else 0 := by
      intro nn
      rw [Psec_eq_diag, Matrix.mul_diagonal, Matrix.diagonal_mul, secInd, secInd]
      by_cases h1 : secOf T i = nn <;> by_cases h2 : secOf T j = nn <;> simp [h1, h2]
    simp_rw [hterm]
    rw [Finset.sum_eq_single (secOf T i)]
    · by_cases h : secOf T i = secOf T j
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
    · rw [ite_eq_left (h i j hA)]
  · intro h i j hA
    have := congrFun (congrFun h i) j
    rw [hsum] at this
    by_contra hne
    rw [ite_eq_right hne] at this
    exact hA this

/-- **Lemma 2.6(ii)**: the second equivalence, "`if and only if $[A,\Psec\nn]=0$ for every $\nn$`". -/
theorem isSectorPreserving_iff_commute (A : FockOp T) :
    IsSectorPreserving T A ↔ ∀ nn : SectorLabel T, Commute A (Psec T nn) := by
  rw [isSectorPreserving_iff_entries]
  simp_rw [Psec_eq_diag, commute_diagonal_iff, secInd]
  constructor
  · intro h nn i j
    by_cases hA : A i j = 0
    · simp [hA]
    · rw [h i j hA]; ring
  · intro h i j hA
    have := h (secOf T j) i j
    simp only [ite_true] at this
    by_contra hne
    rw [ite_eq_right hne, mul_one, zero_mul] at this
    exact hA this

/-- **Lemma 2.6(ii)**: "`Sector-preserving operators form a unital $*$-subalgebra of the operators on $\Fock$,
and they are even`" — the subalgebra. -/
theorem exists_starSubalgebra_sectorPreserving :
    ∃ B : StarSubalgebra ℂ (FockOp T), ∀ A : FockOp T, A ∈ B ↔ IsSectorPreserving T A := by
  have hstar : ∀ A : FockOp T, IsSectorPreserving T A → IsSectorPreserving T (star A) := by
    intro A hA
    refine ⟨?_, ?_⟩
    · have := hA.1.star_star
      rwa [Matrix.star_eq_conjTranspose (Nsig T .up), Nsig_conjTranspose] at this
    · have := hA.2.star_star
      rwa [Matrix.star_eq_conjTranspose (Nsig T .dn), Nsig_conjTranspose] at this
  refine ⟨{ carrier := {A | IsSectorPreserving T A}
            mul_mem' := fun ha hb => ⟨ha.1.mul_left hb.1, ha.2.mul_left hb.2⟩
            one_mem' := ⟨Commute.one_left _, Commute.one_left _⟩
            add_mem' := fun ha hb => ⟨ha.1.add_left hb.1, ha.2.add_left hb.2⟩
            zero_mem' := ⟨Commute.zero_left _, Commute.zero_left _⟩
            algebraMap_mem' := fun r => ⟨Algebra.commute_algebraMap_left r _, Algebra.commute_algebraMap_left r _⟩
            star_mem' := fun ha => hstar _ ha }, fun A => Iff.rfl⟩

/-- **Lemma 2.6(ii)**: sector-preserving operators are even ("`and they are even`"). -/
theorem IsSectorPreserving.isEven {A : FockOp T} (hA : IsSectorPreserving T A) : IsEven A := by
  rw [isSectorPreserving_iff_entries] at hA
  rw [IsEven, Fermion.Pilot.JW.parityOp_eq_diagonal, commute_diagonal_iff]
  intro i j
  by_cases h : A i j = 0
  · simp [h]
  · have hs := (secOf_eq_iff T i (secOf T j)).mp (hA i j h)
    have occ_eq : ∀ m : Conf (ZMod T.Nφ), Fermion.Pilot.JW.occ m = ctσ T .up m + ctσ T .dn m := by
      intro m
      have := Fermion.Pilot.JW.card_occ_split m
      exact_mod_cast this
    rw [occ_eq, occ_eq, hs.1, hs.2, mul_comm]
    rfl

/-- **Lemma 2.6(ii)**: "`If $H$ is self-adjoint and sector-preserving, then $f(H)$ is sector-preserving for every
function $f$ on the spectrum of $H$`". -/
theorem IsSectorPreserving.cfc {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (f : ℝ → ℝ) : IsSectorPreserving T (cfc f H) := by
  refine ⟨Commute.cfc (𝕜 := ℝ) hHs.1 (by rw [hH.star_eq]; exact hHs.1) f,
    Commute.cfc (𝕜 := ℝ) hHs.2 (by rw [hH.star_eq]; exact hHs.2) f⟩

/-! ### Proof devices for the spectral projections (phase (b); not statements of the paper) -/

/-- A real polynomial of `H` acts on an eigenvector of `H` by its value at the eigenvalue. -/
theorem toCLM_aeval_eigen (H : FockOp T) (μ : ℂ) (w : FockSpace T)
    (hw : Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) H w = μ • w) (p : Polynomial ℝ) :
    Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (Polynomial.aeval H p) w = Polynomial.aeval μ p • w := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.aeval_C, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one (A := FockOp T) a,
      ← Complex.coe_smul, map_smul, map_one, smul_apply, one_apply_eq_self,
      Complex.coe_algebraMap]
  | add p p' hp hp' => simp only [map_add, add_apply, hp, hp', add_smul]
  | monomial n a h =>
    have e1 : Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ (n + 1)) =
        Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n) * H := by
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    have e2 : Polynomial.aeval μ (Polynomial.C a * Polynomial.X ^ (n + 1)) =
        Polynomial.aeval μ (Polynomial.C a * Polynomial.X ^ n) * μ := by
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    rw [e1, e2, map_mul, mul_apply_eq_comp, hw, map_smul, h, smul_smul, mul_comm μ]


/-- **Lemma 2.6(ii)**: "`for every $\nn$ and every Borel set $B\subset\R$ the spectral projection of $H|_{\sect\nn}$
onto $B$, extended by zero to $\Fock$, equals $\one_B(H)\Psec\nn$`". The spectral projection of the restriction
onto `B`, extended by zero, is written as what it is in finite dimension: the orthogonal projection of `𝓗_N`
onto the span of the eigenvectors of `H` in the sector with eigenvalues in `B`. -/
theorem specProj_sector {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (nn : SectorLabel T) (B : Set ℝ) (_hB : MeasurableSet B) :
    toCLM T (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn) =
      (⨆ μ ∈ B, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) H) (μ : ℂ) ⊓ sector T nn).starProjection := by
  show Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn) = _
  have hHerm : H.IsHermitian := hH
  have hsym : (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) H).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.symm.mp hHerm
  have hlin : ∀ (M : FockOp T) (w : FockSpace T),
      Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) M w = Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) M w := by
    intro M w
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    rfl
  -- the eigenvalues of `H` are real and lie in its real spectrum
  have hreal : ∀ (μ : ℂ) (w : FockSpace T), Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) H w = μ • w → w ≠ 0 → μ = ((μ.re : ℝ) : ℂ) := by
    intro μ w hw hw0
    have hev : Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) H) μ :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (by rw [hlin]; exact hw), hw0⟩
    exact (Complex.conj_eq_iff_re.mp (hsym.conj_eigenvalue_eq_self hev)).symm
  have hspec : ∀ (r : ℝ) (w : FockSpace T), Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) H w = (r : ℂ) • w → w ≠ 0 → r ∈ spectrum ℝ H := by
    intro r w hw hw0
    rw [spectrum.mem_iff]
    intro hu
    apply hw0
    obtain ⟨M, hM⟩ := hu.exists_left_inv
    have h0 : Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (algebraMap ℝ (FockOp T) r - H) w = 0 := by
      rw [map_sub, sub_apply, hw, Algebra.algebraMap_eq_smul_one (A := FockOp T) r,
        ← Complex.coe_smul, map_smul, map_one, smul_apply, one_apply_eq_self,
        sub_self]
    calc w = Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (M * (algebraMap ℝ (FockOp T) r - H)) w := by rw [hM, map_one]; rfl
      _ = 0 := by rw [map_mul, mul_apply_eq_comp, h0, map_zero]
  -- `1_B(H)` is a polynomial of `H`
  obtain ⟨q, hq⟩ := exists_poly_interp (Matrix.finite_real_spectrum (A := H)).toFinset (B.indicator (1 : ℝ → ℝ))
  have hPq : cfc (B.indicator (1 : ℝ → ℝ)) H = Polynomial.aeval H q := by
    rw [cfc_congr (g := fun x => q.eval x) ?_, cfc_polynomial q H hH]
    intro x hx
    exact (hq x ((Set.Finite.mem_toFinset _).mpr hx)).symm
  have heig : ∀ (μ : ℂ) (w : FockSpace T), Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) H w = μ • w →
      Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H) w = ((B.indicator (1 : ℝ → ℝ) μ.re : ℝ) : ℂ) • w := by
    intro μ w hw
    by_cases hw0 : w = 0
    · subst hw0
      simp
    have hμ := hreal μ w hw hw0
    have hr : μ.re ∈ spectrum ℝ H := hspec μ.re w (by rw [← hμ]; exact hw) hw0
    rw [hPq, toCLM_aeval_eigen T H μ w hw q]
    congr 1
    rw [← hq μ.re ((Set.Finite.mem_toFinset _).mpr hr)]
    conv_lhs => rw [hμ]
    rw [show ((μ.re : ℝ) : ℂ) = algebraMap ℝ ℂ μ.re from rfl, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
    rfl
  -- self-adjointness and commutation
  have hPsa : (cfc (B.indicator (1 : ℝ → ℝ)) H)ᴴ = cfc (B.indicator (1 : ℝ → ℝ)) H :=
    cfc_predicate (B.indicator (1 : ℝ → ℝ)) H
  have hQsa : (Psec T nn)ᴴ = Psec T nn := by
    rw [Psec_eq_diag, Matrix.diagonal_conjTranspose]
    congr 1
    funext m
    simp only [Pi.star_apply, secInd]
    split_ifs <;> simp
  have hQproj : Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (Psec T nn) = (sector T nn).starProjection :=
    (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)).apply_symm_apply _
  have hPQ : Commute (cfc (B.indicator (1 : ℝ → ℝ)) H) (Psec T nn) :=
    (isSectorPreserving_iff_commute T _).mp (IsSectorPreserving.cfc T hH hHs _) nn
  have hHQ : Commute H (Psec T nn) := (isSectorPreserving_iff_commute T H).mp hHs nn
  have hXsa : IsSelfAdjoint (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn)) := by
    have hmat : IsSelfAdjoint (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn) := by
      rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hPsa, hQsa]
      exact hPQ.eq.symm
    exact hmat.map _
  -- `1_B(H) Π^𝐧` fixes the subspace
  have hS2 : ∀ w ∈ (⨆ μ ∈ B, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) H) (μ : ℂ) ⊓ sector T nn),
      Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn) w = w := by
    intro w hw
    have hle : (⨆ μ ∈ B, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) H) (μ : ℂ) ⊓ sector T nn) ≤
        LinearMap.ker ((Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn) : FockSpace T →ₗ[ℂ] FockSpace T) -
          LinearMap.id) := by
      refine iSup₂_le fun μ hμB => ?_
      intro v hv
      rcases Submodule.mem_inf.mp hv with ⟨hvE, hvS⟩
      rw [Module.End.mem_eigenspace_iff, hlin] at hvE
      have hQv : Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (Psec T nn) v = v := by
        rw [hQproj]
        exact Submodule.starProjection_eq_self_iff.mpr hvS
      rw [LinearMap.mem_ker, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, LinearMap.id_apply, sub_eq_zero,
        map_mul, mul_apply_eq_comp, hQv, heig _ v hvE, Complex.ofReal_re, Set.indicator_of_mem hμB,
        Pi.one_apply, Complex.ofReal_one, one_smul]
    have := hle hw
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, LinearMap.id_apply, sub_eq_zero]
      at this
  -- its range lies in the subspace
  have htop : (⨆ μ : ℂ, Module.End.eigenspace
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) H) μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hsym.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hS3 : ∀ u, Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn) u ∈
      (⨆ μ ∈ B, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) H) (μ : ℂ) ⊓ sector T nn) := by
    intro u
    have hu : u ∈ ⨆ μ : ℂ, Module.End.eigenspace
        (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) H) μ := by
      rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun u => Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn) u ∈
      (⨆ μ ∈ B, Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) H) (μ : ℂ) ⊓ sector T nn)) hu ?_ ?_ ?_
    · intro μ v hv
      rw [Module.End.mem_eigenspace_iff, hlin] at hv
      have hQvS : Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (Psec T nn) v ∈ sector T nn := by
        rw [hQproj]; exact Submodule.coe_mem _
      have hQvE : Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) H (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (Psec T nn) v) = μ • Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (Psec T nn) v := by
        rw [← mul_apply_eq_comp, ← map_mul, hHQ.eq, map_mul, mul_apply_eq_comp, hv, map_smul]
      rw [map_mul, mul_apply_eq_comp, heig μ _ hQvE]
      by_cases hQ0 : Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (Psec T nn) v = 0
      · rw [hQ0, smul_zero]; exact Submodule.zero_mem _
      by_cases hB : μ.re ∈ B
      · rw [Set.indicator_of_mem hB, Pi.one_apply, Complex.ofReal_one, one_smul]
        have hμ := hreal μ _ hQvE hQ0
        refine (le_iSup₂ (f := fun (r : ℝ) (_ : r ∈ B) => Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ)
          (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) H) (r : ℂ) ⊓ sector T nn) μ.re hB) ?_
        refine Submodule.mem_inf.mpr ⟨?_, hQvS⟩
        rw [Module.End.mem_eigenspace_iff, hlin, ← hμ]
        exact hQvE
      · rw [Set.indicator_of_notMem hB, Complex.ofReal_zero, zero_smul]
        exact Submodule.zero_mem _
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  -- conclusion: the orthogonal projection onto the subspace
  ext u : 1
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS3 u) fun w hw => ?_
  have hsymX := hXsa.isSymmetric u w
  simp only [ContinuousLinearMap.coe_coe] at hsymX
  rw [inner_sub_left, hsymX, hS2 w hw, sub_self]

/-! ## Lemma 2.6(iii): the many-body magnetic translation -/

/-! ### Proof devices for `Θ` (phase (b); not statements of the paper) -/

theorem thxMat_conjTranspose_mul_self : (thxMat T)ᴴ * thxMat T = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, thxMat, Matrix.of_apply, apply_ite star, star_one, star_zero,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

theorem thx2_conjTranspose_mul_self : (thx2 T)ᴴ * thx2 T = 1 := by
  rw [thx2, Matrix.kronecker, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    thxMat_conjTranspose_mul_self, Matrix.conjTranspose_one, Matrix.mul_one]
  exact Matrix.one_kronecker_one

theorem thx2_mem_unitary : thx2 T ∈ unitary (Matrix (Modes T) (Modes T) ℂ) := by
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
  exact ⟨thx2_conjTranspose_mul_self T, mul_eq_one_comm.mp (thx2_conjTranspose_mul_self T)⟩

theorem Θ_apply_vac (m' : Conf (ZMod T.Nφ)) : Θ T m' vac = if m' = vac then 1 else 0 := by
  have h1 : (Ff T (thx2 T))ᴴ * Ff T (thx2 T) = 1 :=
    secondQuant_conjTranspose_mul_self (thx2_conjTranspose_mul_self T)
  have := congrFun (congrFun h1 m') vac
  rw [Matrix.mul_apply] at this
  simp only [Ff, secondQuant_apply_vac, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at this
  rw [Θ, Ff, this, Matrix.one_apply]

theorem Θ_mem_unitary_dev : Θ T ∈ unitary (FockOp T) := by
  rw [Θ, ← Matrix.star_eq_conjTranspose]
  exact Unitary.star_mem (Ff_mem_unitary T (thx2_mem_unitary T))

theorem Θ_conj_cf_dev (f : Space2 T) :
    (Θ T)ᴴ * cf T f * Θ T = cf T (Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) (thx2 T) f) := by
  rw [Θ, Matrix.conjTranspose_conjTranspose]
  exact Ff_conj_cf T (thx2_mem_unitary T) f

theorem Θ_conj_cjs_dev (j : ZMod T.Nφ) (σ : Spin) : (Θ T)ᴴ * cjs T j σ * Θ T = cjs T (j + 1) σ := by
  rw [cjs, cjs, Θ_conj_cf_dev, thx2_spinTensor, thx_orb]

theorem Θ_conj_njs_dev (j : ZMod T.Nφ) (σ : Spin) : (Θ T)ᴴ * njs T j σ * Θ T = njs T (j + 1) σ := by
  have h2 := mul_conjTranspose_self_of_mem_unitary (Θ_mem_unitary_dev T)
  rw [njs, njs, ← Θ_conj_cjs_dev, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [mul_assoc]
  rw [← mul_assoc (Θ T) (Θ T)ᴴ, h2, one_mul]


/-- **Lemma 2.6(iii)**: "`$\Theta$ is unitary and sector-preserving, $\Theta^{\Nphi}=\one$`" — unitary. -/
theorem Θ_mem_unitary : Θ T ∈ unitary (FockOp T) := by
  exact Θ_mem_unitary_dev T

/-- **Lemma 2.6(iii)**: "`$\Theta$ is unitary and sector-preserving`" — sector-preserving. -/
theorem Θ_isSectorPreserving : IsSectorPreserving T (Θ T) := by
  have h2 := mul_conjTranspose_self_of_mem_unitary (Θ_mem_unitary_dev T)
  have hN : ∀ σ, (Θ T)ᴴ * Nsig T σ * Θ T = Nsig T σ := by
    intro σ
    rw [Nsig, Finset.mul_sum, Finset.sum_mul]
    simp_rw [Θ_conj_njs_dev]
    exact Equiv.sum_comp (Equiv.addRight 1) (fun j => njs T j σ)
  have key : ∀ σ, Θ T * Nsig T σ = Nsig T σ * Θ T := by
    intro σ
    calc Θ T * Nsig T σ = Θ T * ((Θ T)ᴴ * Nsig T σ * Θ T) := by rw [hN]
      _ = (Θ T * (Θ T)ᴴ) * Nsig T σ * Θ T := by simp only [mul_assoc]
      _ = Nsig T σ * Θ T := by rw [h2, one_mul]
  exact ⟨key .up, key .dn⟩

/-- **Lemma 2.6(iii)**: "`$\Theta^{\Nphi}=\one$`". -/
theorem Θ_pow : Θ T ^ T.Nφ = 1 := by
  have hu := Θ_mem_unitary_dev T
  have hc : ∀ μ : Modes T, (Θ T)ᴴ * Fermion.Pilot.JW.c μ * Θ T = Fermion.Pilot.JW.c (μ.1 + 1, μ.2) := by
    rintro ⟨j, σ⟩
    rw [← cjs_eq, ← cjs_eq]
    exact Θ_conj_cjs_dev T j σ
  have hpow : ∀ (n : ℕ) (μ : Modes T),
      ((Θ T) ^ n)ᴴ * Fermion.Pilot.JW.c μ * (Θ T) ^ n = Fermion.Pilot.JW.c (μ.1 + n, μ.2) := by
    intro n
    induction n with
    | zero => intro μ; simp
    | succ n ih =>
      intro μ
      rw [pow_succ, Matrix.conjTranspose_mul]
      calc (Θ T)ᴴ * ((Θ T) ^ n)ᴴ * Fermion.Pilot.JW.c μ * ((Θ T) ^ n * Θ T)
          = (Θ T)ᴴ * (((Θ T) ^ n)ᴴ * Fermion.Pilot.JW.c μ * (Θ T) ^ n) * Θ T := by
            simp only [mul_assoc]
        _ = (Θ T)ᴴ * Fermion.Pilot.JW.c (μ.1 + n, μ.2) * Θ T := by rw [ih]
        _ = Fermion.Pilot.JW.c (μ.1 + (n + 1 : ℕ), μ.2) := by rw [hc]; push_cast; rw [add_assoc]
  set P := (Θ T) ^ T.Nφ with hP
  have hPu : P ∈ unitary (FockOp T) := pow_mem hu _
  have hP1 := conjTranspose_mul_self_of_mem_unitary hPu
  have hP2 := mul_conjTranspose_self_of_mem_unitary hPu
  have hfix : ∀ μ : Modes T, Pᴴ * Fermion.Pilot.JW.c μ * P = Fermion.Pilot.JW.c μ := by
    intro μ
    rw [hP, hpow, ZMod.natCast_self, add_zero]
  have hcomm : ∀ (A : FockOp T), Pᴴ * A * P = A → Commute P A := by
    intro A hA
    show P * A = A * P
    calc P * A = P * (Pᴴ * A * P) := by rw [hA]
      _ = (P * Pᴴ) * A * P := by simp only [mul_assoc]
      _ = A * P := by rw [hP2, one_mul]
  have h1 : ∀ μ : Modes T, Commute P (Fermion.Pilot.JW.c μ) := fun μ => hcomm _ (hfix μ)
  have h2 : ∀ μ : Modes T, Commute P (Fermion.Pilot.JW.c μ)ᴴ := by
    intro μ
    apply hcomm
    have := congrArg Matrix.conjTranspose (hfix μ)
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← mul_assoc] at this
  obtain ⟨a, ha⟩ := exists_smul_one_of_commute_c h1 h2
  have hvac : ∀ (n : ℕ) (m' : Conf (ZMod T.Nφ)), ((Θ T) ^ n) m' vac = if m' = vac then 1 else 0 := by
    intro n
    induction n with
    | zero => intro m'; simp [Matrix.one_apply]
    | succ n ih =>
      intro m'
      rw [pow_succ, Matrix.mul_apply]
      simp only [Θ_apply_vac, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ih]
  have hvv : P vac vac = 1 := by rw [hP, hvac]; simp
  rw [ha] at hvv ⊢
  have ha1 : a = 1 := by simpa using hvv
  rw [ha1, one_smul]

/-- **Lemma 2.6(iii)**: "`\Theta^*c(f)\Theta=c\bigl((\thx\otimes\one)f\bigr),\qquad\Theta^*c_{j\sigma}\Theta=c_{j+1,\sigma},\qquad
\Theta^*n_{j\sigma}\Theta=n_{j+1,\sigma}`" — the first. -/
theorem Θ_conj_cf (f : Space2 T) :
    (Θ T)ᴴ * cf T f * Θ T = cf T (Matrix.toEuclideanCLM (n := Modes T) (𝕜 := ℂ) (thx2 T) f) := by
  exact Θ_conj_cf_dev T f

/-- **Lemma 2.6(iii)**: "`\Theta^*c_{j\sigma}\Theta=c_{j+1,\sigma}`". -/
theorem Θ_conj_cjs (j : ZMod T.Nφ) (σ : Spin) : (Θ T)ᴴ * cjs T j σ * Θ T = cjs T (j + 1) σ := by
  exact Θ_conj_cjs_dev T j σ

/-- **Lemma 2.6(iii)**: "`\Theta^*n_{j\sigma}\Theta=n_{j+1,\sigma}`". -/
theorem Θ_conj_njs (j : ZMod T.Nφ) (σ : Spin) : (Θ T)ᴴ * njs T j σ * Θ T = njs T (j + 1) σ := by
  exact Θ_conj_njs_dev T j σ

end Physical

/-! ## The fit to `HRTorus.IndexCore.Orbital` -/

/-- The orbital part of the field list of `HRTorus.IndexCore.Orbital` (the fields `Psec_proj`, `n_sa`, `n_comm`,
`exp_n`, `Psec_n`, `sum_n_Psec`, `Θ_unitary`, `Psec_Θ`, `Θ_n`, verbatim): the properties that Remark 8.7 lists
("`use only that the charge is a sum over the orbitals $j$ of the band of mutually commuting, self-adjoint,
sector-preserving operators $n_j$ with integer spectrum`", and `Θ^* n_j Θ = n_{j+1}`) together with the sector
projection's and the translation's. The fields of `Orbital` that concern `H` are `HN_orbitalFit`
(`Fock.Hamiltonian`). -/
structure OrbitalFit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [CompleteSpace E] {Nφ : ℕ} [NeZero Nφ] (n : ZMod Nφ → (E →L[ℂ] E)) (Th Pc : E →L[ℂ] E) (nup : ℕ) :
    Prop where
  Psec_proj : IsStarProjection Pc
  n_sa : ∀ j, IsSelfAdjoint (n j)
  n_comm : ∀ i j, Commute (n i) (n j)
  exp_n : ∀ j, NormedSpace.exp ((2 * π * I) • n j) = 1
  Psec_n : ∀ j, Commute Pc (n j)
  sum_n_Psec : (∑ j, n j) * Pc = (nup : ℂ) • Pc
  Θ_unitary : Th ∈ unitary (E →L[ℂ] E)
  Psec_Θ : Commute Pc Th
  Θ_n : ∀ j, star Th * n j * Th = n (j + 1)

/-! ### Proof devices for the fit (phase (b); not statements of the paper) -/

section OrbitalDevices

variable (T : Torus)

theorem njs_eq_diag (j : ZMod T.Nφ) (σ : Spin) :
    njs T j σ = Matrix.diagonal fun m => if m (j, σ) = true then (1 : ℂ) else 0 := by
  rw [njs, cjs_eq, Fermion.Pilot.JW.conjTranspose_c_mul_c_self]

theorem commute_diagonal_diagonal {n : Type*} [Fintype n] [DecidableEq n] (a b : n → ℂ) :
    Commute (Matrix.diagonal a) (Matrix.diagonal b) := by
  show Matrix.diagonal a * Matrix.diagonal b = Matrix.diagonal b * Matrix.diagonal a
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem toCLM_isSelfAdjoint {A : FockOp T} (h : Aᴴ = A) : IsSelfAdjoint (toCLM T A) := by
  show star (toCLM T A) = toCLM T A
  rw [← map_star, Matrix.star_eq_conjTranspose, h]

theorem toCLM_mem_unitary {A : FockOp T} (h : A ∈ unitary (FockOp T)) : toCLM T A ∈ unitary _ := by
  rw [Unitary.mem_iff] at h ⊢
  rw [← map_star, ← map_mul, ← map_mul, h.1, h.2, map_one]
  exact ⟨rfl, rfl⟩

theorem njs_isIdempotentElem (j : ZMod T.Nφ) (σ : Spin) : IsIdempotentElem (toCLM T (njs T j σ)) := by
  show toCLM T (njs T j σ) * toCLM T (njs T j σ) = toCLM T (njs T j σ)
  rw [← map_mul, njs_eq_diag, Matrix.diagonal_mul_diagonal]
  congr 2
  funext m
  split_ifs <;> simp

theorem Nsig_mul_Psec (σ : Spin) (nn : SectorLabel T) :
    Nsig T σ * Psec T nn = ((if σ = .up then (nn.1 : ℕ) else (nn.2 : ℕ) : ℕ) : ℂ) • Psec T nn := by
  rw [Nsig_eq_diag, Psec_eq_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext m
  simp only [secInd, Pi.smul_apply, smul_eq_mul]
  by_cases h : secOf T m = nn
  · have := (secOf_eq_iff T m nn).mp h
    cases σ <;> simp [h, this.1, this.2]
  · simp [h]

end OrbitalDevices


/-- The occupation operators `n_{jσ}` of one spin, with `Θ` and `Π^𝐧`, have the property list of
`IndexCore.Orbital`, with the sector's charge `n_σ` (Remark 8.7: the up-spin and the down-spin band charges). -/
theorem orbitalFit_spin (T : Torus) (σ : Spin) (nn : SectorLabel T) :
    OrbitalFit (Nφ := T.Nφ) (fun j => toCLM T (njs T j σ)) (toCLM T (Θ T)) (toCLM T (Psec T nn))
      (if σ = .up then (nn.1 : ℕ) else (nn.2 : ℕ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toCLM, Psec, StarAlgEquiv.apply_symm_apply]
    exact isStarProjection_starProjection
  · intro j
    exact toCLM_isSelfAdjoint T (by rw [njs, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose])
  · intro i j
    rw [njs_eq_diag, njs_eq_diag]
    exact (commute_diagonal_diagonal _ _).map _
  · intro j
    exact HRTorus.IndexCore.exp_two_pi_I_smul_of_isIdempotentElem (njs_isIdempotentElem T j σ)
  · intro j
    rw [Psec_eq_diag, njs_eq_diag]
    exact (commute_diagonal_diagonal _ _).map _
  · rw [← map_sum, ← map_mul, ← Nsig, Nsig_mul_Psec, map_smul]
  · exact toCLM_mem_unitary T (Θ_mem_unitary T)
  · exact (((isSectorPreserving_iff_commute T _).mp (Θ_isSectorPreserving T) nn).symm).map _
  · intro j
    rw [← map_star, ← map_mul, ← map_mul, Matrix.star_eq_conjTranspose, Θ_conj_njs]

/-- The total occupations `n_{j↑} + n_{j↓}`, with `Θ` and `Π^𝐧`, have the property list of `IndexCore.Orbital`,
with the charge `n_↑ + n_↓` (Remark 8.7: the total band charge). -/
theorem orbitalFit_total (T : Torus) (nn : SectorLabel T) :
    OrbitalFit (Nφ := T.Nφ) (fun j => toCLM T (njs T j .up + njs T j .dn)) (toCLM T (Θ T))
      (toCLM T (Psec T nn)) ((nn.1 : ℕ) + (nn.2 : ℕ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [toCLM, Psec, StarAlgEquiv.apply_symm_apply]
    exact isStarProjection_starProjection
  · intro j
    refine toCLM_isSelfAdjoint T ?_
    rw [Matrix.conjTranspose_add, njs, njs, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  · intro i j
    rw [njs_eq_diag, njs_eq_diag, njs_eq_diag, njs_eq_diag, Matrix.diagonal_add, Matrix.diagonal_add]
    exact (commute_diagonal_diagonal _ _).map _
  · intro j
    have hadd : toCLM T (njs T j .up + njs T j .dn) = toCLM T (njs T j .up) + toCLM T (njs T j .dn) :=
      map_add _ _ _
    rw [hadd]
    refine HRTorus.IndexCore.exp_two_pi_I_smul_add_eq_one ?_
      (HRTorus.IndexCore.exp_two_pi_I_smul_of_isIdempotentElem (njs_isIdempotentElem T j .up))
      (HRTorus.IndexCore.exp_two_pi_I_smul_of_isIdempotentElem (njs_isIdempotentElem T j .dn))
    rw [njs_eq_diag, njs_eq_diag]
    exact (commute_diagonal_diagonal _ _).map _
  · intro j
    rw [Psec_eq_diag, njs_eq_diag, njs_eq_diag, Matrix.diagonal_add]
    exact (commute_diagonal_diagonal _ _).map _
  · rw [← map_sum, ← map_mul, Finset.sum_add_distrib, ← Nsig, ← Nsig, add_mul, Nsig_mul_Psec, Nsig_mul_Psec,
      ← add_smul, map_smul]
    simp
  · exact toCLM_mem_unitary T (Θ_mem_unitary T)
  · exact (((isSectorPreserving_iff_commute T _).mp (Θ_isSectorPreserving T) nn).symm).map _
  · intro j
    rw [← map_star, ← map_mul, ← map_mul, Matrix.star_eq_conjTranspose, Matrix.mul_add, Matrix.add_mul,
      Θ_conj_njs, Θ_conj_njs]

end HRTorus.Fock
