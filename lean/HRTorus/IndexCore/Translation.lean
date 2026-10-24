import HRTorus.IndexCore.Main
import Mathlib.Data.ZMod.Basic

/-!
# The divisibility corollary of the HR paper (§7) on top of the index core

Written by Claude Opus 5.5 (an AI model), 2026-10-23.
**Phase (a): the statement**, reviewed against §7 and accepted for proofs
without change.
**Phase (b): the proofs.** Every statement of phase (a) is proved below with its text unchanged;
the helper lemmas added in phase (b) are marked as such. Nothing in the twelve index-core
modules is changed; this file only imports them.

## What is formalized

Section 7 of the HR paper (`papers/hr/sections/07-translation.tex`) applies the index
theorem (Theorem 6.18) with the magnetic translation `Θ` as the transport unitary `U`. Here:

* `Orbital E` is the *orbital structure*: the non-orbital data of `Setting` unchanged, plus
  occupation operators `n : ℤ_{N_φ} → End E` with exactly the algebraic properties that
  Remark 8.7 lists (self-adjoint, mutually commuting, integer spectrum as `e^{2πi n_j} = 1`,
  sector-preserving, `Θ^* n_j Θ = n_{j+1}`), a translation `Θ` (unitary, sector-preserving,
  commuting with `H` — what (H2) gives), the sector's charge `nup` with `(∑_j n_j) Π = nup Π`
  (Lemma 2.6(i)), and three bands partitioning `Γ = {0, …, N-1}` (Setting 6.1).
* `Orbital.toSetting` *constructs* a `Setting` from it: `Q_B = ∑_{j ∈ B} n_j` (Definition 4.9),
  `U = Θ`, `T_- = -n_0`, `T_+ = n_N` (Lemma 7.1(b)). Its proof obligations are Lemma 4.10 and
  Lemma 7.1(b), proved below as separate lemmas.
* Lemma 7.1(a)–(d) on `O.toSetting`, the finite clause of 7.1(e), and the five commutators of
  Lemma 6.13(i) that vanish for `Θ`.
* Corollary 7.2 quantitatively: from the 16 separated commutators that do not vanish for `Θ`,
  the four clustering commutators, `‖n_0‖ ≤ M` and `‖K_-‖ ≤ M`, an integer `k` with
  `|p · nup / N_φ - k| ≤ 400 p (M + 1) √ε` (by `index_core_400`).
* Corollary 7.3 quantitatively: if moreover `4 nup = N_φ` and `400 p (M + 1) √ε < 1/4`, then
  `4 ∣ p`; and Corollary 7.4's finite content (the density defect `± p/(4N)` for odd `N`).

## Conventions

As in `Statement.lean`. The orbital index set is `ZMod Nφ` (the paper's `ℤ_{N_φ}`), with
`[NeZero Nφ]` as a field so that `∑ j, n j` (the paper's `N_↑ = ∑_{j ∈ ℤ_{N_φ}} n_{j↑}`) is a
finite sum. `Γ = {0, …, N-1}` is the image of `Finset.range N` in `ZMod Nφ` (`bandΓ`).
-/

open scoped InnerProductSpace ComplexConjugate Real
open Complex (I)

noncomputable section

namespace HRTorus.IndexCore

/-! ## The bands -/

/-- `Γ = {0, 1, …, N-1} ⊂ ℤ_{N_φ}` (Setting 6.1): the classes of the first `N` orbitals. -/
def bandΓ (Nφ N : ℕ) : Finset (ZMod Nφ) :=
  (Finset.range N).image (fun k : ℕ => (k : ZMod Nφ))

/-- The paper's lower quarter `Γ_- = {0, …, ⌊N/4⌋ - 1}` (Setting 6.1; `N / 4` is `⌊N/4⌋`). -/
def quarterMinus (Nφ N : ℕ) : Finset (ZMod Nφ) :=
  (Finset.range (N / 4)).image (fun k : ℕ => (k : ZMod Nφ))

/-- The paper's upper quarter `Γ_+ = {⌈3N/4⌉, …, N - 1}` (Setting 6.1). -/
def quarterPlus (Nφ N : ℕ) : Finset (ZMod Nφ) :=
  (Finset.Ico ⌈(3 * N : ℝ) / 4⌉₊ N).image (fun k : ℕ => (k : ZMod Nφ))

/-- The paper's middle band `Γ_mid = Γ ∖ (Γ_- ∪ Γ_+)` (Setting 6.1). -/
def quarterMid (Nφ N : ℕ) : Finset (ZMod Nφ) :=
  bandΓ Nφ N \ (quarterMinus Nφ N ∪ quarterPlus Nφ N)

/-- Setting 6.1's quarters partition `Γ` (for `N ≤ N_φ`, so that `0, …, N-1` are distinct classes):
they are one instance of the bands of `Orbital`. -/
theorem quarters_partition {Nφ N : ℕ} (h : N ≤ Nφ) :
    Disjoint (quarterMinus Nφ N) (quarterMid Nφ N) ∧
    Disjoint (quarterMinus Nφ N) (quarterPlus Nφ N) ∧
    Disjoint (quarterMid Nφ N) (quarterPlus Nφ N) ∧
    quarterMinus Nφ N ∪ quarterMid Nφ N ∪ quarterPlus Nφ N = bandΓ Nφ N := by
  -- the classes of `0, …, Nφ - 1` are distinct
  have hinj : ∀ a b : ℕ, a < Nφ → b < Nφ → (a : ZMod Nφ) = (b : ZMod Nφ) → a = b := by
    intro a b ha hb hab
    have hv : ((a : ZMod Nφ)).val = ((b : ZMod Nφ)).val := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv
  -- `⌊N/4⌋ ≤ ⌈3N/4⌉`
  have hceil : N / 4 ≤ ⌈(3 * N : ℝ) / 4⌉₊ := by
    have h1 : ((N / 4 : ℕ) : ℝ) ≤ (N : ℝ) / 4 := Nat.cast_div_le
    have h2 : (N : ℝ) / 4 ≤ (3 * N : ℝ) / 4 := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    have h3 : (3 * N : ℝ) / 4 ≤ ⌈(3 * N : ℝ) / 4⌉₊ := Nat.le_ceil _
    exact_mod_cast h1.trans (h2.trans h3)
  have hsubm : quarterMinus Nφ N ⊆ bandΓ Nφ N := by
    refine Finset.image_subset_image fun k hk => ?_
    rw [Finset.mem_range] at hk ⊢
    omega
  have hsubp : quarterPlus Nφ N ⊆ bandΓ Nφ N := by
    refine Finset.image_subset_image fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    exact Finset.mem_range.2 hk.2
  have hmp : Disjoint (quarterMinus Nφ N) (quarterPlus Nφ N) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 hx'
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico] at hb
    obtain ⟨hb1, hb2⟩ := hb
    have hba := hinj b a (by omega) (by omega) hab
    omega
  have hm1 : Disjoint (quarterMinus Nφ N) (quarterMid Nφ N) := by
    rw [quarterMid]
    exact Finset.disjoint_sdiff.mono_left Finset.subset_union_left
  have hm2 : Disjoint (quarterMid Nφ N) (quarterPlus Nφ N) := by
    rw [quarterMid]
    exact Finset.sdiff_disjoint.mono_right Finset.subset_union_right
  refine ⟨hm1, hmp, hm2, ?_⟩
  rw [quarterMid, Finset.union_right_comm,
    Finset.union_sdiff_of_subset (Finset.union_subset hsubm hsubp)]

/-! ## Two exponential identities (helpers, phase (b)) -/

section ExpHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `e^{2πi(X+Y)} = 1` for commuting `X`, `Y` with `e^{2πiX} = e^{2πiY} = 1`. -/
theorem exp_two_pi_I_smul_add_eq_one {X Y : E →L[ℂ] E} (hXY : Commute X Y)
    (hX : NormedSpace.exp ((2 * π * I) • X) = 1) (hY : NormedSpace.exp ((2 * π * I) • Y) = 1) :
    NormedSpace.exp ((2 * π * I) • (X + Y)) = 1 := by
  let _ : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [smul_add, NormedSpace.exp_add_of_commute
    ((hXY.smul_left (2 * π * I : ℂ)).smul_right (2 * π * I : ℂ)), hX, hY, one_mul]

/-- `e^{2πi(-X)} = 1` if `e^{2πiX} = 1`. -/
theorem exp_two_pi_I_smul_neg_eq_one {X : E →L[ℂ] E}
    (hX : NormedSpace.exp ((2 * π * I) • X) = 1) :
    NormedSpace.exp ((2 * π * I) • (-X)) = 1 := by
  let _ : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  have h := NormedSpace.exp_add_of_commute (Commute.refl ((2 * π * I : ℂ) • X)).neg_right
  rw [add_neg_cancel, NormedSpace.exp_zero, hX, one_mul] at h
  rw [smul_neg]
  exact h.symm

end ExpHelpers

/-! ## The orbital structure -/

/-- The exact data of Section 7 on one torus: the non-orbital data of `Setting` unchanged, and
in place of the band charges, the unitary `U` and the operators `T_±`, the orbital data from
which they are constructed (`Orbital.toSetting`). The occupation operators `n j` carry exactly
the algebraic properties of Remark 8.7's list, so that the down-spin and total charges are
instances as well as the up-spin projections `n_{j↑}`. -/
structure Orbital (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E] where
  /-- The Hamiltonian `H_N` (Setting 6.1, (H1)). -/
  H : E →L[ℂ] E
  H_sa : IsSelfAdjoint H
  /-- The sector projection `Π = Π_{n_N}` (Assumption 6.3). -/
  Psec : E →L[ℂ] E
  Psec_proj : IsStarProjection Psec
  /-- `H` is sector-preserving (`[h_R, N_σ] = 0`, Lemma 2.6(ii)). -/
  Psec_H : Commute Psec H
  /-- The number of orbitals `N_φ` (`= 2N` in the paper), nonzero. -/
  Nφ : ℕ
  [Nφ_neZero : NeZero Nφ]
  /-- The band length `N`: `Γ = {0, …, N-1}`. The paper has `N_φ = 2N`; only `N ≤ N_φ` is used
  (the classes of `0, …, N-1` are distinct). -/
  N : ℕ
  N_le_Nφ : N ≤ Nφ
  /-- The occupation operators `n_j`, `j ∈ ℤ_{N_φ}` (Definition 2.5: `n_{j↑}`; Remark 8.7's
  list): self-adjoint, mutually commuting, with integer spectrum (`e^{2πi n_j} = 1`), and
  sector-preserving. -/
  n : ZMod Nφ → (E →L[ℂ] E)
  n_sa : ∀ j, IsSelfAdjoint (n j)
  n_comm : ∀ i j, Commute (n i) (n j)
  exp_n : ∀ j, NormedSpace.exp ((2 * π * I) • n j) = 1
  Psec_n : ∀ j, Commute Psec (n j)
  /-- The sector's charge `n_{↑,N}`: `N_↑ Π = n_{↑,N} Π` with `N_↑ = ∑_j n_j` (Lemma 2.6(i)). -/
  nup : ℕ
  sum_n_Psec : (∑ j, n j) * Psec = (nup : ℂ) • Psec
  /-- The bands `Γ_-`, `Γ_mid`, `Γ_+`: pairwise disjoint with union `Γ` (Setting 6.1; the
  paper's quarters are one choice, `quarters_partition`). -/
  Γminus : Finset (ZMod Nφ)
  Γmid : Finset (ZMod Nφ)
  Γplus : Finset (ZMod Nφ)
  disjoint_minus_mid : Disjoint Γminus Γmid
  disjoint_minus_plus : Disjoint Γminus Γplus
  disjoint_mid_plus : Disjoint Γmid Γplus
  bands_union : Γminus ∪ Γmid ∪ Γplus = bandΓ Nφ N
  /-- Assumption 6.3, exactly as in `Setting` (Remark 6.20's `γ > Δ`). -/
  γ : ℝ
  Δ : ℝ
  a : ℝ
  b : ℝ
  Δ_nonneg : 0 ≤ Δ
  Δ_lt_γ : Δ < γ
  width : b - a ≤ Δ
  gap : ∀ (μ : ℝ) (v : E), v ≠ 0 → Psec v = v → H v = (μ : ℂ) • v → μ ∈ Set.Icc a b ∨ b + γ ≤ μ
  /-- The magnetic translation `Θ` (Definition 2.5, Lemma 2.6(iii)): unitary, sector-preserving,
  commuting with `H` (what (H2) gives, Definition 4.6), and `Θ^* n_j Θ = n_{j+1}`. -/
  Θ : E →L[ℂ] E
  Θ_unitary : Θ ∈ unitary (E →L[ℂ] E)
  Psec_Θ : Commute Psec Θ
  Θ_H : Commute Θ H
  Θ_n : ∀ j, star Θ * n j * Θ = n (j + 1)
  /-- The currents `J_±` (Definition 6.5) through Lemma 6.6(i), as in `Setting`, with
  `Q = Q_Γ = ∑_{j ∈ Γ} n_j`. -/
  Jminus : E →L[ℂ] E
  Jplus : E →L[ℂ] E
  Jminus_sa : IsSelfAdjoint Jminus
  Jplus_sa : IsSelfAdjoint Jplus
  Psec_Jminus : Commute Psec Jminus
  Psec_Jplus : Commute Psec Jplus
  current_split : Jminus + Jplus = I • ⁅H, ∑ j ∈ bandΓ Nφ N, n j⁆
  /-- The filters, exactly as in `Setting`. -/
  W : ℝ → ℂ
  W_eq : ∀ ω : ℝ, γ ≤ |ω| → W ω = I / ω
  W_conj : ∀ ω : ℝ, W (-ω) = conj (W ω)
  g : ℝ → ℂ
  g_zero : ∀ ω : ℝ, -Δ ≤ ω → g ω = 0
  g_one : ∀ ω : ℝ, ω ≤ -γ → g ω = 1

attribute [instance] Orbital.Nφ_neZero

namespace Orbital

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E] (O : Orbital E)

/-! ## Band charges: Definition 4.9 and Lemma 4.10 -/

/-- The band charge `Q_B = ∑_{j ∈ B} n_j` (Definition 4.9). -/
def Qb (B : Finset (ZMod O.Nφ)) : E →L[ℂ] E := ∑ j ∈ B, O.n j

/-- Lemma 4.10: band charges are self-adjoint. -/
theorem isSelfAdjoint_Qb (B : Finset (ZMod O.Nφ)) : IsSelfAdjoint (O.Qb B) :=
  isSelfAdjoint_sum B fun j _ => O.n_sa j

/-- Lemma 4.10: band charges commute with one another. -/
theorem commute_Qb (B B' : Finset (ZMod O.Nφ)) : Commute (O.Qb B) (O.Qb B') :=
  Commute.sum_left B _ _ fun j _ => Commute.sum_right B' _ _ fun k _ => O.n_comm j k

/-- Lemma 4.10: `e^{2πi Q_B} = 1`. -/
theorem exp_Qb (B : Finset (ZMod O.Nφ)) : NormedSpace.exp ((2 * π * I) • O.Qb B) = 1 := by
  let _ : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  unfold Qb
  induction B using Finset.induction_on with
  | empty => rw [Finset.sum_empty, smul_zero, NormedSpace.exp_zero]
  | insert a s ha ih =>
    have hc : Commute ((2 * π * I : ℂ) • O.n a) ((2 * π * I : ℂ) • ∑ j ∈ s, O.n j) :=
      ((Commute.sum_right s _ _ fun k _ => O.n_comm a k).smul_left (2 * π * I : ℂ)).smul_right
        (2 * π * I : ℂ)
    rw [Finset.sum_insert ha, smul_add, NormedSpace.exp_add_of_commute hc, O.exp_n, ih, one_mul]

/-- Lemma 4.10: band charges commute with `N_↑`, `N_↓`; here, with `Π`. -/
theorem commute_Psec_Qb (B : Finset (ZMod O.Nφ)) : Commute O.Psec (O.Qb B) :=
  Commute.sum_right B _ _ fun j _ => O.Psec_n j

/-- Lemma 4.10: `Q_B + Q_{B'} = Q_{B ∪ B'}` for disjoint bands. -/
theorem Qb_union {B B' : Finset (ZMod O.Nφ)} (h : Disjoint B B') :
    O.Qb B + O.Qb B' = O.Qb (B ∪ B') :=
  (Finset.sum_union h).symm

/-- Each `n_j` commutes with every band charge (helper, phase (b)). -/
theorem commute_n_Qb (j : ZMod O.Nφ) (B : Finset (ZMod O.Nφ)) : Commute (O.n j) (O.Qb B) :=
  Commute.sum_right B _ _ fun k _ => O.n_comm j k

/-- Setting 6.1: `Q = Q_- + Q_m + Q_+ = Q_Γ`. -/
theorem Qb_bands : O.Qb O.Γminus + O.Qb O.Γmid + O.Qb O.Γplus = O.Qb (bandΓ O.Nφ O.N) := by
  rw [O.Qb_union O.disjoint_minus_mid,
    O.Qb_union (Finset.disjoint_union_left.2 ⟨O.disjoint_minus_plus, O.disjoint_mid_plus⟩),
    O.bands_union]

/-- **Lemma 7.1(b)**, the identity: `Θ^* Q Θ - Q = n_N - n_0` for `Q = Q_Γ`. -/
theorem transport_Γ :
    star O.Θ * O.Qb (bandΓ O.Nφ O.N) * O.Θ - O.Qb (bandΓ O.Nφ O.N) =
      O.n (O.N : ZMod O.Nφ) - O.n 0 := by
  -- `Q_Γ = ∑_{k < N} n_k`: the classes of `0, …, N - 1` are distinct (`N ≤ N_φ`)
  have hinj : Set.InjOn (fun k : ℕ => (k : ZMod O.Nφ)) ↑(Finset.range O.N) := by
    intro a ha b hb hab
    have ha' : a < O.Nφ := (Finset.mem_range.1 (Finset.mem_coe.1 ha)).trans_le O.N_le_Nφ
    have hb' : b < O.Nφ := (Finset.mem_range.1 (Finset.mem_coe.1 hb)).trans_le O.N_le_Nφ
    have hv : ((a : ZMod O.Nφ)).val = ((b : ZMod O.Nφ)).val := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at hv
  have hQ : O.Qb (bandΓ O.Nφ O.N) = ∑ k ∈ Finset.range O.N, O.n (k : ZMod O.Nφ) := by
    show ∑ j ∈ (Finset.range O.N).image (fun k : ℕ => (k : ZMod O.Nφ)), O.n j = _
    exact Finset.sum_image hinj
  -- `Θ^* Q_Γ Θ = ∑_{k < N} n_{k+1}`
  have hconj : star O.Θ * (∑ k ∈ Finset.range O.N, O.n (k : ZMod O.Nφ)) * O.Θ =
      ∑ k ∈ Finset.range O.N, O.n ((k : ZMod O.Nφ) + 1) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => O.Θ_n _
  -- the telescoping identity
  have h1 : ∑ k ∈ Finset.range (O.N + 1), O.n (k : ZMod O.Nφ) =
      ∑ k ∈ Finset.range O.N, O.n (k : ZMod O.Nφ) + O.n (O.N : ZMod O.Nφ) :=
    Finset.sum_range_succ _ _
  have h2 : ∑ k ∈ Finset.range (O.N + 1), O.n (k : ZMod O.Nφ) =
      ∑ k ∈ Finset.range O.N, O.n ((k : ZMod O.Nφ) + 1) + O.n 0 := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
  have h3 : ∑ k ∈ Finset.range O.N, O.n ((k : ZMod O.Nφ) + 1) + O.n 0 =
      ∑ k ∈ Finset.range O.N, O.n (k : ZMod O.Nφ) + O.n (O.N : ZMod O.Nφ) := h2.symm.trans h1
  rw [hQ, hconj, sub_eq_sub_iff_add_eq_add, h3]
  abel

/-! ## The setting constructed from the orbital data -/

/-- The `Setting` of Section 6 constructed from the orbital data (Section 7): the band charges
`Q_± = Q_{Γ_±}`, `Q_m = Q_{Γ_mid}` (Setting 6.1), `U = Θ` (Corollary 7.2), `T_- = -n_0`,
`T_+ = n_N` (Lemma 7.1(b)); every other field is copied. The proof obligations are the lemmas
above (Lemma 4.10, Setting 6.1, Lemma 7.1(b)). -/
def toSetting : Setting E where
  H := O.H
  H_sa := O.H_sa
  Psec := O.Psec
  Psec_proj := O.Psec_proj
  Psec_H := O.Psec_H
  Qminus := O.Qb O.Γminus
  Qmid := O.Qb O.Γmid
  Qplus := O.Qb O.Γplus
  Qminus_sa := O.isSelfAdjoint_Qb _
  Qmid_sa := O.isSelfAdjoint_Qb _
  Qplus_sa := O.isSelfAdjoint_Qb _
  comm_Qminus_Qmid := O.commute_Qb _ _
  comm_Qmid_Qplus := O.commute_Qb _ _
  comm_Qminus_Qplus := O.commute_Qb _ _
  exp_Qminus := O.exp_Qb _
  exp_Qmid := O.exp_Qb _
  exp_Qplus := O.exp_Qb _
  Psec_Qminus := O.commute_Psec_Qb _
  Psec_Qmid := O.commute_Psec_Qb _
  Psec_Qplus := O.commute_Psec_Qb _
  γ := O.γ
  Δ := O.Δ
  a := O.a
  b := O.b
  Δ_nonneg := O.Δ_nonneg
  Δ_lt_γ := O.Δ_lt_γ
  width := O.width
  gap := O.gap
  U := O.Θ
  U_unitary := O.Θ_unitary
  Psec_U := O.Psec_Θ
  Tminus := -O.n 0
  Tplus := O.n (O.N : ZMod O.Nφ)
  Tminus_sa := (O.n_sa 0).neg
  Tplus_sa := O.n_sa _
  Psec_Tminus := (O.Psec_n 0).neg_right
  Psec_Tplus := O.Psec_n _
  transport := by rw [O.Qb_bands, O.transport_Γ]; abel
  Jminus := O.Jminus
  Jplus := O.Jplus
  Jminus_sa := O.Jminus_sa
  Jplus_sa := O.Jplus_sa
  Psec_Jminus := O.Psec_Jminus
  Psec_Jplus := O.Psec_Jplus
  current_split := by rw [O.Qb_bands]; exact O.current_split
  W := O.W
  W_eq := O.W_eq
  W_conj := O.W_conj
  g := O.g
  g_zero := O.g_zero
  g_one := O.g_one

/-- `Q = Q_Γ` for the constructed setting (helper, phase (b)). -/
theorem toSetting_Q : O.toSetting.Q = O.Qb (bandΓ O.Nφ O.N) := O.Qb_bands

/-! ## Lemma 7.1 on the constructed setting -/

/-- **Lemma 7.1(a)**: `[Θ, P] = 0`. -/
theorem commute_Θ_P : Commute O.Θ O.toSetting.P := by
  rw [Setting.P_def]
  exact (commute_specProj_of_commute O.toSetting.H O.toSetting.H_sa O.Θ_H _).mul_right
    O.Psec_Θ.symm

/-- **Lemma 7.1(a)**: `[Θ, N_↑] = 0`, with `N_↑ = ∑_j n_j` (unused by the chain; the clause of
the paper's (a) that the structure can express). -/
theorem commute_Θ_sum_n : Commute O.Θ (∑ j, O.n j) := by
  have hU : O.Θ * star O.Θ = 1 := Unitary.mul_star_self_of_mem O.Θ_unitary
  have h1 : star O.Θ * (∑ j, O.n j) * O.Θ = ∑ j, O.n j := by
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [O.Θ_n]
    exact Equiv.sum_comp (Equiv.addRight 1) O.n
  show O.Θ * (∑ j, O.n j) = (∑ j, O.n j) * O.Θ
  calc O.Θ * (∑ j, O.n j) = O.Θ * (star O.Θ * (∑ j, O.n j) * O.Θ) := by rw [h1]
    _ = O.Θ * star O.Θ * (∑ j, O.n j) * O.Θ := by simp only [mul_assoc]
    _ = (∑ j, O.n j) * O.Θ := by rw [hU, one_mul]

/-- **(U2) exactly** (Corollary 7.2's proof): `‖[U, P]‖ = 0` for `U = Θ`. -/
theorem norm_lie_U_P : ‖⁅O.toSetting.U, O.toSetting.P⁆‖ = 0 := by
  have h : Commute O.toSetting.U O.toSetting.P := O.commute_Θ_P
  rw [h.lie_eq, norm_zero]

/-- **Lemma 7.1(c)**: `e^{2πi(Q + T_+)} = 1` ((U4)'s exponential exactly). -/
theorem exp_Q_add_Tplus :
    NormedSpace.exp ((2 * π * I) • (O.toSetting.Q + O.toSetting.Tplus)) = 1 := by
  rw [O.toSetting_Q]
  exact exp_two_pi_I_smul_add_eq_one (O.commute_n_Qb _ _).symm (O.exp_Qb _) (O.exp_n _)

/-- **Lemma 7.1(c)**: `e^{2πi(Q + T_-)} = 1`. -/
theorem exp_Q_add_Tminus :
    NormedSpace.exp ((2 * π * I) • (O.toSetting.Q + O.toSetting.Tminus)) = 1 := by
  rw [O.toSetting_Q]
  exact exp_two_pi_I_smul_add_eq_one (O.commute_n_Qb 0 _).symm.neg_right (O.exp_Qb _)
    (exp_two_pi_I_smul_neg_eq_one (O.exp_n 0))

/-- **Lemma 7.1(c)**: `e^{2πi(Q_+ + T_+)} = 1` (and `e^{2πi Q_m} = 1` is the field
`O.toSetting.exp_Qmid`). -/
theorem exp_Qplus_add_Tplus :
    NormedSpace.exp ((2 * π * I) • (O.toSetting.Qplus + O.toSetting.Tplus)) = 1 :=
  exp_two_pi_I_smul_add_eq_one (O.commute_n_Qb _ _).symm (O.exp_Qb _) (O.exp_n _)

/-- **Lemma 6.13(i) for `U = Θ`**: `[T_-, Q_m] = 0`. -/
theorem lie_Tminus_Qmid : ⁅O.toSetting.Tminus, O.toSetting.Qmid⁆ = 0 :=
  (O.commute_n_Qb 0 O.Γmid).neg_left.lie_eq

/-- **Lemma 6.13(i) for `U = Θ`**: `[T_+, Q_m] = 0`. -/
theorem lie_Tplus_Qmid : ⁅O.toSetting.Tplus, O.toSetting.Qmid⁆ = 0 :=
  (O.commute_n_Qb _ O.Γmid).lie_eq

/-- **Lemma 6.13(i) for `U = Θ`**: `[Q_-, T_+] = 0`. -/
theorem lie_Qminus_Tplus : ⁅O.toSetting.Qminus, O.toSetting.Tplus⁆ = 0 :=
  (O.commute_n_Qb _ O.Γminus).symm.lie_eq

/-- **Lemma 6.13(i) for `U = Θ`**: `[T_-, Q_+] = 0`. -/
theorem lie_Tminus_Qplus : ⁅O.toSetting.Tminus, O.toSetting.Qplus⁆ = 0 :=
  (O.commute_n_Qb 0 O.Γplus).neg_left.lie_eq

/-- **Lemma 6.13(i) for `U = Θ`**: `[T_-, T_+] = 0`. -/
theorem lie_Tminus_Tplus : ⁅O.toSetting.Tminus, O.toSetting.Tplus⁆ = 0 :=
  (O.n_comm 0 _).neg_left.lie_eq

/-- `Tr(P Θ^* X Θ) = Tr(P X)`, by cyclicity and `[Θ, P] = 0` (helper, phase (b)). -/
theorem trc_P_conj (X : E →L[ℂ] E) :
    trc (O.toSetting.P * (star O.Θ * X * O.Θ)) = trc (O.toSetting.P * X) := by
  have hU : O.Θ * star O.Θ = 1 := Unitary.mul_star_self_of_mem O.Θ_unitary
  have hP : O.Θ * O.toSetting.P = O.toSetting.P * O.Θ := O.commute_Θ_P.eq
  calc trc (O.toSetting.P * (star O.Θ * X * O.Θ))
      = trc ((O.toSetting.P * star O.Θ * X) * O.Θ) := by simp only [mul_assoc]
    _ = trc (O.Θ * (O.toSetting.P * star O.Θ * X)) := trc_mul_comm _ _
    _ = trc ((O.Θ * O.toSetting.P) * star O.Θ * X) := by simp only [mul_assoc]
    _ = trc (O.toSetting.P * (O.Θ * star O.Θ) * X) := by rw [hP]; simp only [mul_assoc]
    _ = trc (O.toSetting.P * X) := by rw [hU, mul_one]

/-- Translation invariance: `Tr(P n_{j+1}) = Tr(P n_j)` (helper, phase (b)). -/
theorem trc_P_n_succ (j : ZMod O.Nφ) :
    trc (O.toSetting.P * O.n (j + 1)) = trc (O.toSetting.P * O.n j) := by
  rw [← O.Θ_n j]
  exact O.trc_P_conj (O.n j)

/-- `j ↦ Tr(P n_j)` is constant on `ℤ_{N_φ}` (helper, phase (b)). -/
theorem trc_P_n_eq (j : ZMod O.Nφ) :
    trc (O.toSetting.P * O.n j) = trc (O.toSetting.P * O.n 0) := by
  have key : ∀ k : ℕ,
      trc (O.toSetting.P * O.n (k : ZMod O.Nφ)) = trc (O.toSetting.P * O.n 0) := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero]
    | succ k ih => rw [Nat.cast_add_one, O.trc_P_n_succ, ih]
  have h := key j.val
  rwa [ZMod.natCast_zmod_val] at h

/-- **Lemma 7.1(d)**: `Tr(P n_j) = p n_{↑,N} / N_φ` for every `j ∈ ℤ_{N_φ}`. -/
theorem trc_P_n (j : ZMod O.Nφ) :
    trc (O.toSetting.P * O.n j) = (O.toSetting.p : ℂ) * O.nup / O.Nφ := by
  -- `Tr P = p`
  have hid : IsIdempotentElem (O.toSetting.P : E →ₗ[ℂ] E) := by
    show (O.toSetting.P : E →ₗ[ℂ] E) * (O.toSetting.P : E →ₗ[ℂ] E) = O.toSetting.P
    rw [← ContinuousLinearMap.toLinearMap_mul, O.toSetting.P_mul_self]
  have htrP : trc O.toSetting.P = (O.toSetting.p : ℂ) :=
    (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  -- `P N_↑ = nup P`
  have hPP : O.toSetting.P * O.Psec = O.toSetting.P := O.toSetting.P_mul_Psec
  have hc : Commute O.Psec (∑ k, O.n k) := Commute.sum_right _ _ _ fun k _ => O.Psec_n k
  have hPsum : O.toSetting.P * (∑ k, O.n k) = (O.nup : ℂ) • O.toSetting.P := by
    calc O.toSetting.P * (∑ k, O.n k) = O.toSetting.P * O.Psec * (∑ k, O.n k) := by rw [hPP]
      _ = O.toSetting.P * ((∑ k, O.n k) * O.Psec) := by rw [mul_assoc, hc.eq]
      _ = O.toSetting.P * ((O.nup : ℂ) • O.Psec) := by rw [O.sum_n_Psec]
      _ = (O.nup : ℂ) • (O.toSetting.P * O.Psec) := by rw [mul_smul_comm]
      _ = (O.nup : ℂ) • O.toSetting.P := by rw [hPP]
  -- `∑_k Tr(P n_k) = Tr(P N_↑)`
  have hsum : ∑ k, trc (O.toSetting.P * O.n k) = trc (O.toSetting.P * ∑ k, O.n k) := by
    rw [Finset.mul_sum]
    unfold trc
    rw [ContinuousLinearMap.toLinearMap_sum, map_sum]
  -- `∑_k Tr(P n_k) = N_φ Tr(P n_0)`
  have hconst : ∑ k, trc (O.toSetting.P * O.n k) = (O.Nφ : ℂ) * trc (O.toSetting.P * O.n 0) := by
    rw [Finset.sum_congr rfl fun k _ => O.trc_P_n_eq k, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul]
  have hNφ : (O.Nφ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
  have key : (O.Nφ : ℂ) * trc (O.toSetting.P * O.n 0) = (O.nup : ℂ) * O.toSetting.p := by
    rw [← hconst, hsum, hPsum, trc_smul, htrP]
  rw [O.trc_P_n_eq j, eq_div_iff hNφ]
  linear_combination key

/-- **Lemma 7.1(d)**: `Tr(P T_-) = -p n_{↑,N} / N_φ`. -/
theorem trc_P_Tminus :
    trc (O.toSetting.P * O.toSetting.Tminus) = -((O.toSetting.p : ℂ) * O.nup / O.Nφ) := by
  show trc (O.toSetting.P * -O.n 0) = _
  rw [mul_neg, trc_neg, O.trc_P_n 0]

/-- **Lemma 7.1(e)**, its finite part: `Tr(P Θ^* K_- Θ) = Tr(P K_-)`, hence `Tr(P T̃) = Tr(P T_-)`
exactly (the locality clauses of (e) are absent by design; this identity is not needed by
Corollary 7.2, where `index_core` absorbs it through (U2)). -/
theorem trc_P_Ttilde :
    trc (O.toSetting.P * O.toSetting.Ttilde) = trc (O.toSetting.P * O.toSetting.Tminus) := by
  have hK : trc (O.toSetting.P * O.toSetting.KUminus) =
      trc (O.toSetting.P * O.toSetting.Kminus) :=
    O.trc_P_conj O.toSetting.Kminus
  rw [Setting.Ttilde, mul_add, mul_sub, trc_add, trc_sub, hK, sub_add_cancel]

/-! ## The inputs that remain for `U = Θ`, and Corollaries 7.2–7.4 -/

/-- The asymptotic inputs of `index_core` that do not hold exactly for `U = Θ`, each `≤ ε`:
the **16** separated commutators of Lemma 6.13(ii) for `U = Θ` (the 21 of `SepBounds` minus the
five of Lemma 6.13(i) proved above), in the orientation of `index_core`; the four clustering
commutators of `index_core` (Corollary 6.15); and the two norms: `‖n_0‖ = ‖T_-‖ ≤ M`,
`‖K_-‖ ≤ M`. ((U2) and (U4) hold exactly and are not inputs.) -/
structure Inputs (ε M : ℝ) : Prop where
  /- Lemma 6.13(ii), class 1: `[A, Q_m]`, `A ∈ {K_-, K^U_-, K_+, K^U_+}`. -/
  sep_Kminus_Qmid : ‖⁅O.toSetting.Kminus, O.toSetting.Qmid⁆‖ ≤ ε
  sep_KUminus_Qmid : ‖⁅O.toSetting.KUminus, O.toSetting.Qmid⁆‖ ≤ ε
  sep_Kplus_Qmid : ‖⁅O.toSetting.Kplus, O.toSetting.Qmid⁆‖ ≤ ε
  sep_KUplus_Qmid : ‖⁅O.toSetting.KUplus, O.toSetting.Qmid⁆‖ ≤ ε
  /- Lemma 6.13(ii), class 2: `(Q_-, B_+)`, `B_+ ∈ {K_+, K^U_+}`; `(A_-, Q_+)`,
  `A_- ∈ {K_-, K^U_-}`. -/
  sep_Qminus_Kplus : ‖⁅O.toSetting.Qminus, O.toSetting.Kplus⁆‖ ≤ ε
  sep_Qminus_KUplus : ‖⁅O.toSetting.Qminus, O.toSetting.KUplus⁆‖ ≤ ε
  sep_Kminus_Qplus : ‖⁅O.toSetting.Kminus, O.toSetting.Qplus⁆‖ ≤ ε
  sep_KUminus_Qplus : ‖⁅O.toSetting.KUminus, O.toSetting.Qplus⁆‖ ≤ ε
  /- Lemma 6.13(ii), class 3: `(A_-, B_+)`, `A_- ∈ {T_-, K_-, K^U_-}`,
  `B_+ ∈ {T_+, K_+, K^U_+}`, except `(T_-, T_+)`. -/
  sep_Tminus_Kplus : ‖⁅O.toSetting.Tminus, O.toSetting.Kplus⁆‖ ≤ ε
  sep_Tminus_KUplus : ‖⁅O.toSetting.Tminus, O.toSetting.KUplus⁆‖ ≤ ε
  sep_Kminus_Tplus : ‖⁅O.toSetting.Kminus, O.toSetting.Tplus⁆‖ ≤ ε
  sep_Kminus_Kplus : ‖⁅O.toSetting.Kminus, O.toSetting.Kplus⁆‖ ≤ ε
  sep_Kminus_KUplus : ‖⁅O.toSetting.Kminus, O.toSetting.KUplus⁆‖ ≤ ε
  sep_KUminus_Tplus : ‖⁅O.toSetting.KUminus, O.toSetting.Tplus⁆‖ ≤ ε
  sep_KUminus_Kplus : ‖⁅O.toSetting.KUminus, O.toSetting.Kplus⁆‖ ≤ ε
  sep_KUminus_KUplus : ‖⁅O.toSetting.KUminus, O.toSetting.KUplus⁆‖ ≤ ε
  /- Corollary 6.15 (through Lemma 6.14 and Proposition 6.10(ii)), as in `index_core`. -/
  clu_M : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
    ‖⁅O.toSetting.Qf (O.toSetting.Mplus φ), O.toSetting.Mminus φ⁆‖ ≤ ε
  clu_M_adj : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
    ‖⁅O.toSetting.Qf (star (O.toSetting.Mplus φ)), star (O.toSetting.Mminus φ)⁆‖ ≤ ε
  clu_O : ‖⁅O.toSetting.Qf O.toSetting.Oplus, O.toSetting.Ominus⁆‖ ≤ ε
  clu_O_adj : ‖⁅O.toSetting.Qf (star O.toSetting.Oplus), star O.toSetting.Ominus⁆‖ ≤ ε
  /- The norms: `‖T_-‖ = ‖n_0‖` and `‖K_-‖`. -/
  norm_n_zero : ‖O.n 0‖ ≤ M
  norm_Kminus : ‖O.toSetting.Kminus‖ ≤ M

variable {O}

/-- **Corollary 7.2, quantitatively.** For the magnetic translation, `p n_{↑,N} / N_φ` is within
`400 p (M + 1) √ε` of an integer. -/
theorem translation_corollary {ε M : ℝ} (h : O.Inputs ε M) :
    ∃ k : ℤ, |(O.toSetting.p : ℝ) * O.nup / O.Nφ - k| ≤ 400 * O.toSetting.p * (M + 1) * √ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans h.sep_Kminus_Qmid
  have z : ∀ {X Y : E →L[ℂ] E}, ⁅X, Y⁆ = 0 → ‖⁅X, Y⁆‖ ≤ ε := fun hXY => by
    rw [hXY, norm_zero]; exact hε
  have hS : O.toSetting.SepBounds ε :=
    ⟨h.sep_Kminus_Qmid, h.sep_KUminus_Qmid, h.sep_Kplus_Qmid, h.sep_KUplus_Qmid,
      z O.lie_Tminus_Qmid, z O.lie_Tplus_Qmid, h.sep_Qminus_Kplus, h.sep_Qminus_KUplus,
      h.sep_Kminus_Qplus, h.sep_KUminus_Qplus, z O.lie_Qminus_Tplus, z O.lie_Tminus_Qplus,
      z O.lie_Tminus_Tplus, h.sep_Tminus_Kplus, h.sep_Tminus_KUplus, h.sep_Kminus_Tplus,
      h.sep_Kminus_Kplus, h.sep_Kminus_KUplus, h.sep_KUminus_Tplus, h.sep_KUminus_Kplus,
      h.sep_KUminus_KUplus⟩
  have hU2 : ‖⁅O.toSetting.U, O.toSetting.P⁆‖ ≤ ε := by rw [O.norm_lie_U_P]; exact hε
  have hU4 : ‖NormedSpace.exp ((2 * π * I) • (O.toSetting.Q + O.toSetting.Tplus)) - 1‖ ≤ ε := by
    rw [O.exp_Q_add_Tplus, sub_self, norm_zero]; exact hε
  have hT : ‖O.toSetting.Tminus‖ ≤ M := by
    show ‖-O.n 0‖ ≤ M
    rw [norm_neg]; exact h.norm_n_zero
  obtain ⟨n, hn⟩ := index_core_400 O.toSetting ε M hS hU2 hU4 h.clu_M h.clu_M_adj h.clu_O
    h.clu_O_adj hT h.norm_Kminus
  have htr : LinearMap.trace ℂ E (O.toSetting.P * O.toSetting.Tminus : E →L[ℂ] E).toLinearMap =
      -((O.toSetting.p : ℂ) * O.nup / O.Nφ) := O.trc_P_Tminus
  have hreal : -((O.toSetting.p : ℂ) * O.nup / O.Nφ) - (n : ℂ) =
      ((-((O.toSetting.p : ℝ) * O.nup / O.Nφ) - n : ℝ) : ℂ) := by
    push_cast; ring
  rw [htr, hreal, Complex.norm_real, Real.norm_eq_abs] at hn
  refine ⟨-n, ?_⟩
  have e : (O.toSetting.p : ℝ) * O.nup / O.Nφ - ((-n : ℤ) : ℝ) =
      -(-((O.toSetting.p : ℝ) * O.nup / O.Nφ) - n) := by
    push_cast; ring
  rw [e, abs_neg]
  exact hn

/-- **Corollary 7.3, quantitatively.** At `n_{↑,N} / N_φ = 1/4` (the sectors `(N/2, N/2)` with
`N_φ = 2N`), if `400 p (M + 1) √ε < 1/4`, then `p ∈ 4ℤ`. -/
theorem four_dvd_p {ε M : ℝ} (h : O.Inputs ε M) (hquarter : 4 * O.nup = O.Nφ)
    (hsmall : 400 * O.toSetting.p * (M + 1) * √ε < 1 / 4) : 4 ∣ O.toSetting.p := by
  obtain ⟨k, hk⟩ := translation_corollary h
  have hNφ : (O.Nφ : ℝ) = 4 * O.nup := by exact_mod_cast hquarter.symm
  have hnup : (O.nup : ℝ) ≠ 0 := by
    intro h0
    have h1 : (O.Nφ : ℝ) = 0 := by rw [hNφ, h0, mul_zero]
    exact NeZero.ne O.Nφ (by exact_mod_cast h1)
  have hq : (O.toSetting.p : ℝ) * O.nup / O.Nφ = (O.toSetting.p : ℝ) / 4 := by
    rw [hNφ]
    field_simp
  rw [hq] at hk
  have hlt : |(((O.toSetting.p : ℤ) - 4 * k : ℤ) : ℝ)| < 1 := by
    have e : (((O.toSetting.p : ℤ) - 4 * k : ℤ) : ℝ) = 4 * ((O.toSetting.p : ℝ) / 4 - k) := by
      push_cast; ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  have h0 : (O.toSetting.p : ℤ) - 4 * k = 0 := by
    rw [← Int.abs_lt_one_iff]
    exact_mod_cast hlt
  have h4 : (4 : ℤ) ∣ (O.toSetting.p : ℤ) := ⟨k, by omega⟩
  exact_mod_cast h4

/-- **Corollary 7.4, its finite content, sectors `n^+_N = ((N+1)/2, (N-1)/2)`**: with `N_φ = 2N`
and `2 n_{↑,N} = N + 1`, `p/4 + p/(4N)` is within `400 p (M + 1) √ε` of an integer. -/
theorem odd_plus {ε M : ℝ} (h : O.Inputs ε M) (hNφ : O.Nφ = 2 * O.N) (hup : 2 * O.nup = O.N + 1) :
    ∃ k : ℤ, |(O.toSetting.p : ℝ) / 4 + O.toSetting.p / (4 * O.N) - k| ≤
      400 * O.toSetting.p * (M + 1) * √ε := by
  obtain ⟨k, hk⟩ := translation_corollary h
  refine ⟨k, ?_⟩
  have h1 : (O.Nφ : ℝ) = 2 * O.N := by exact_mod_cast hNφ
  have h2 : (O.nup : ℝ) = (O.N + 1) / 2 := by
    have h3 : (2 * O.nup : ℝ) = O.N + 1 := by exact_mod_cast hup
    linarith
  have hN : (O.N : ℝ) ≠ 0 := by
    intro h0
    have h4 : (O.Nφ : ℝ) = 0 := by rw [h1, h0, mul_zero]
    exact NeZero.ne O.Nφ (by exact_mod_cast h4)
  have e : (O.toSetting.p : ℝ) * O.nup / O.Nφ =
      (O.toSetting.p : ℝ) / 4 + O.toSetting.p / (4 * O.N) := by
    rw [h1, h2]
    field_simp
    ring
  rw [← e]
  exact hk

/-- **Corollary 7.4, its finite content, sectors `n^-_N = ((N-1)/2, (N+1)/2)`**: with `N_φ = 2N`
and `2 n_{↑,N} + 1 = N`, `p/4 - p/(4N)` is within `400 p (M + 1) √ε` of an integer. -/
theorem odd_minus {ε M : ℝ} (h : O.Inputs ε M) (hNφ : O.Nφ = 2 * O.N) (hup : 2 * O.nup + 1 = O.N) :
    ∃ k : ℤ, |(O.toSetting.p : ℝ) / 4 - O.toSetting.p / (4 * O.N) - k| ≤
      400 * O.toSetting.p * (M + 1) * √ε := by
  obtain ⟨k, hk⟩ := translation_corollary h
  refine ⟨k, ?_⟩
  have h1 : (O.Nφ : ℝ) = 2 * O.N := by exact_mod_cast hNφ
  have h2 : (O.nup : ℝ) = (O.N - 1) / 2 := by
    have h3 : (2 * O.nup + 1 : ℝ) = O.N := by exact_mod_cast hup
    linarith
  have hN : (O.N : ℝ) ≠ 0 := by
    intro h0
    have h4 : (O.Nφ : ℝ) = 0 := by rw [h1, h0, mul_zero]
    exact NeZero.ne O.Nφ (by exact_mod_cast h4)
  have e : (O.toSetting.p : ℝ) * O.nup / O.Nφ =
      (O.toSetting.p : ℝ) / 4 - O.toSetting.p / (4 * O.N) := by
    rw [h1, h2]
    field_simp
    ring
  rw [← e]
  exact hk

end Orbital

end HRTorus.IndexCore

end -- noncomputable section

/-! ## What Lean prints -/

#print HRTorus.IndexCore.bandΓ
#print HRTorus.IndexCore.quarterMinus
#print HRTorus.IndexCore.quarterPlus
#print HRTorus.IndexCore.quarterMid
#check @HRTorus.IndexCore.quarters_partition
#print HRTorus.IndexCore.Orbital
#print HRTorus.IndexCore.Orbital.Qb
#check @HRTorus.IndexCore.Orbital.isSelfAdjoint_Qb
#check @HRTorus.IndexCore.Orbital.commute_Qb
#check @HRTorus.IndexCore.Orbital.exp_Qb
#check @HRTorus.IndexCore.Orbital.commute_Psec_Qb
#check @HRTorus.IndexCore.Orbital.Qb_union
#check @HRTorus.IndexCore.Orbital.Qb_bands
#check @HRTorus.IndexCore.Orbital.transport_Γ
#print HRTorus.IndexCore.Orbital.toSetting
#check @HRTorus.IndexCore.Orbital.commute_Θ_P
#check @HRTorus.IndexCore.Orbital.commute_Θ_sum_n
#check @HRTorus.IndexCore.Orbital.norm_lie_U_P
#check @HRTorus.IndexCore.Orbital.exp_Q_add_Tplus
#check @HRTorus.IndexCore.Orbital.exp_Q_add_Tminus
#check @HRTorus.IndexCore.Orbital.exp_Qplus_add_Tplus
#check @HRTorus.IndexCore.Orbital.lie_Tminus_Qmid
#check @HRTorus.IndexCore.Orbital.lie_Tplus_Qmid
#check @HRTorus.IndexCore.Orbital.lie_Qminus_Tplus
#check @HRTorus.IndexCore.Orbital.lie_Tminus_Qplus
#check @HRTorus.IndexCore.Orbital.lie_Tminus_Tplus
#check @HRTorus.IndexCore.Orbital.trc_P_n
#check @HRTorus.IndexCore.Orbital.trc_P_Tminus
#check @HRTorus.IndexCore.Orbital.trc_P_Ttilde
#print HRTorus.IndexCore.Orbital.Inputs
#check @HRTorus.IndexCore.Orbital.translation_corollary
#check @HRTorus.IndexCore.Orbital.four_dvd_p
#check @HRTorus.IndexCore.Orbital.odd_plus
#check @HRTorus.IndexCore.Orbital.odd_minus
-- Phase (b): every declaration should depend on `[propext, Classical.choice, Quot.sound]` only.
#print axioms HRTorus.IndexCore.bandΓ
#print axioms HRTorus.IndexCore.quarterMinus
#print axioms HRTorus.IndexCore.quarterPlus
#print axioms HRTorus.IndexCore.quarterMid
#print axioms HRTorus.IndexCore.Orbital
#print axioms HRTorus.IndexCore.Orbital.Qb
#print axioms HRTorus.IndexCore.Orbital.toSetting
#print axioms HRTorus.IndexCore.Orbital.Inputs
#print axioms HRTorus.IndexCore.Orbital.translation_corollary
#print axioms HRTorus.IndexCore.Orbital.four_dvd_p
