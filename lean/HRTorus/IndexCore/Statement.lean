import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# The finite-dimensional core of the HR index theorem: the statement

Written by Claude Opus 5.5 (an AI model), 2026-10-23. **The setting and the
definitions.** The main theorem `HRTorus.IndexCore.index_core` was first stated in this file with
`sorry`; its statement was later moved verbatim to `Main.lean`, where it is proved. This
file contains no `sorry`. The paper is the HR paper (`papers/hr/` in this repository), Section 6
and Appendix A.

## What is formalized

Section 6 of the paper proves (Theorem 6.18) that `Tr(P_N T_{-,N})` is within `O(N^{-∞})` of an
integer. Its proof is a finite-dimensional argument (Lemma 6.7, Proposition 6.10(i)-(ii),
Lemmas 6.13-6.17, Lemmas A.6, A.8, A.9) fed by finitely many asymptotic inputs (locality,
Lemma 5.13). Here every such input is one explicit hypothesis `… ≤ ε`, and the conclusion is
quantitative: `dist(Tr(P T₋), ℤ) ≤ C(p, M) · √ε`.

**The square root.** The conclusion has `√ε`, not `ε`: the paper's Lemma 6.14 (BBDF's Lemma 4.2)
bounds `‖[V₋, P]‖` by `√(2 ε̄)` from quantities of size `ε̄`, and that square root is sharp for
the lemma as stated (by a 2×2 example). It is harmless for `O(N^{-∞})`, as the paper
says at the end of the proof of Lemma 6.14.

## Conventions

* The ambient space is any finite-dimensional complex inner product space `E` (the Fock space
  `ℱ` of the paper is one); operators are `E →L[ℂ] E` with the operator norm, `star` is the
  adjoint, `⁅A, B⁆ = A * B - B * A`. `[CompleteSpace E]` follows from finite dimension
  (`FiniteDimensional.complete`); it is listed because Mathlib's adjoint instance asks for it.
* The spectral calculus of the self-adjoint `H` uses the orthonormal eigenbasis that Mathlib's
  spectral theorem provides (`LinearMap.IsSymmetric.eigenvectorBasis`): `P_E = 1_{E}(H)` is the
  sum of the rank-one projections onto the basis vectors with eigenvalue `E`, which is the
  orthogonal projection onto the `E`-eigenspace whatever basis is chosen.
* The paper's names map as follows: `Q_-, Q_m, Q_+` ↦ `Qminus, Qmid, Qplus`; `Π = Π_{n_N}` ↦
  `Psec`; `T_±, J_±, K_±` ↦ `Tminus/Tplus` etc.; `\widehat W_γ` ↦ `W`; the clustering step `g` ↦
  `g`; `\mathcal Q = g(ad_H)` ↦ `Qf`; `\overline Q` ↦ `Qbar`; `\mathcal M_±(φ)` ↦ `Mminus/Mplus φ`;
  `e^{2πi \overline Q_±}` ↦ `Ominus/Oplus`; `\widetilde T_-` ↦ `Ttilde`.
-/

open scoped InnerProductSpace ComplexConjugate Real
open Complex (I)

noncomputable section
open Classical

namespace HRTorus.IndexCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-! ## Spectral calculus of a self-adjoint operator -/

section Spectral

variable (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)

/-- Mathlib's orthonormal basis of eigenvectors of `H` (the spectral theorem). -/
def eigBasis : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E :=
  hH.isSymmetric.eigenvectorBasis rfl

/-- The eigenvalues of `H`, `H (eigBasis i) = eigVal i • eigBasis i`, with multiplicity. -/
def eigVal : Fin (Module.finrank ℂ E) → ℝ :=
  hH.isSymmetric.eigenvalues rfl

/-- The spectrum `σ(H)`, as a finite set of reals. -/
def spec : Finset ℝ :=
  Finset.univ.image (eigVal H hH)

/-- `P_E = 1_{E}(H)`: the orthogonal projection onto the eigenspace of `μ` (zero if `μ ∉ σ(H)`). -/
def eigProj (μ : ℝ) : E →L[ℂ] E :=
  ∑ i ∈ Finset.univ.filter (fun i => eigVal H hH i = μ),
    InnerProductSpace.rankOne ℂ (eigBasis H hH i) (eigBasis H hH i)

/-- `1_S(H) = ∑_{E ∈ σ(H) ∩ S} P_E`. -/
def specProj (S : Set ℝ) : E →L[ℂ] E :=
  ∑ μ ∈ (spec H hH).filter (· ∈ S), eigProj H hH μ

/-- The double spectral sum `∑_{E, E' ∈ σ(H)} f(E, E') P_E A P_{E'}` (a Schur multiplier in the
eigenbasis of `H`). It is the form of `K_±` in Lemma 5.9 (last display) and Lemma 6.7, and the
definition of the clustering filter `\mathcal Q(A) = g(ad_H)(A)` in Definition 5.8. -/
def spectralSum (f : ℝ → ℝ → ℂ) (A : E →L[ℂ] E) : E →L[ℂ] E :=
  ∑ μ ∈ spec H hH, ∑ ν ∈ spec H hH, f μ ν • (eigProj H hH μ * A * eigProj H hH ν)

end Spectral

/-! ## The setting: the exact (non-asymptotic) data and hypotheses of Section 6 -/

/-- The exact data of Section 6 on one torus (one `N`): Setting 6.1, the exact parts of
Assumptions 6.3 and 6.4, Lemma 6.6(i), and the two properties of the filters `\widehat W_γ`
(Lemma 5.9) and `g` (Definition 5.8, Remark 6.20) that the finite-dimensional argument uses.
No field is asymptotic; the asymptotic inputs are the hypotheses of `index_core`. -/
structure Setting (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E] where
  /-- The Hamiltonian `H_N` (Setting 6.1, (H1)). -/
  H : E →L[ℂ] E
  H_sa : IsSelfAdjoint H
  /-- The sector projection `Π = Π_{n_N}` (Assumption 6.3). -/
  Psec : E →L[ℂ] E
  Psec_proj : IsStarProjection Psec
  /-- `H` is sector-preserving (`[h_R, N_σ] = 0`, Lemma 2.6(ii)). -/
  Psec_H : Commute Psec H
  /-- The band charges `Q_- = Q_{Γ_-}`, `Q_m = Q_{Γ_mid}`, `Q_+ = Q_{Γ_+}` (Setting 6.1); their
  properties are those of Lemma 4.10: self-adjoint, mutually commuting, `e^{2πi Q_B} = 1`, and
  sector-preserving. -/
  Qminus : E →L[ℂ] E
  Qmid : E →L[ℂ] E
  Qplus : E →L[ℂ] E
  Qminus_sa : IsSelfAdjoint Qminus
  Qmid_sa : IsSelfAdjoint Qmid
  Qplus_sa : IsSelfAdjoint Qplus
  comm_Qminus_Qmid : Commute Qminus Qmid
  comm_Qmid_Qplus : Commute Qmid Qplus
  comm_Qminus_Qplus : Commute Qminus Qplus
  exp_Qminus : NormedSpace.exp ((2 * π * I) • Qminus) = 1
  exp_Qmid : NormedSpace.exp ((2 * π * I) • Qmid) = 1
  exp_Qplus : NormedSpace.exp ((2 * π * I) • Qplus) = 1
  Psec_Qminus : Commute Psec Qminus
  Psec_Qmid : Commute Psec Qmid
  Psec_Qplus : Commute Psec Qplus
  /-- Assumption 6.3: the gap `γ`, the width `Δ`, and an interval `[a, b]` with `b - a ≤ Δ`
  containing the low eigenvalues `E_1, …, E_p` of `H|_{sector}`; every other eigenvalue in the
  sector is `≥ b + γ`. (With `a = E_1`, `b = E_p` this is `E_p - E_1 ≤ Δ`, `E_{p+1} - E_p ≥ γ`.)
  The paper's `γ > 2Δ` is weakened to Remark 6.20's `γ > Δ`. -/
  γ : ℝ
  Δ : ℝ
  a : ℝ
  b : ℝ
  Δ_nonneg : 0 ≤ Δ
  Δ_lt_γ : Δ < γ
  width : b - a ≤ Δ
  gap : ∀ (μ : ℝ) (v : E), v ≠ 0 → Psec v = v → H v = (μ : ℂ) • v → μ ∈ Set.Icc a b ∨ b + γ ≤ μ
  /-- Assumption 6.4: the unitary `U`, sector-preserving ((U1)), with `U^* Q U - Q = T_- + T_+`
  for self-adjoint sector-preserving `T_±` ((U4), its exact part). -/
  U : E →L[ℂ] E
  U_unitary : U ∈ unitary (E →L[ℂ] E)
  Psec_U : Commute Psec U
  Tminus : E →L[ℂ] E
  Tplus : E →L[ℂ] E
  Tminus_sa : IsSelfAdjoint Tminus
  Tplus_sa : IsSelfAdjoint Tplus
  Psec_Tminus : Commute Psec Tminus
  Psec_Tplus : Commute Psec Tplus
  transport : star U * (Qminus + Qmid + Qplus) * U - (Qminus + Qmid + Qplus) = Tminus + Tplus
  /-- The currents `J_± = i[H_{𝕋^±}, Q]` (Definition 6.5) through the properties Lemma 6.6(i)
  proves: self-adjoint, sector-preserving, and `J_- + J_+ = i[H_N, Q]`. -/
  Jminus : E →L[ℂ] E
  Jplus : E →L[ℂ] E
  Jminus_sa : IsSelfAdjoint Jminus
  Jplus_sa : IsSelfAdjoint Jplus
  Psec_Jminus : Commute Psec Jminus
  Psec_Jplus : Commute Psec Jplus
  current_split : Jminus + Jplus = I • ⁅H, Qminus + Qmid + Qplus⁆
  /-- The frequency response `\widehat W_γ` of the generator filter (Definition 5.8,
  Lemma 5.9): `\widehat W_γ(ω) = i/ω` for `|ω| ≥ γ`, and `\widehat W_γ(-ω) = conj(\widehat W_γ(ω))`
  (`ϑ` even and real), which makes `K_±` self-adjoint. -/
  W : ℝ → ℂ
  W_eq : ∀ ω : ℝ, γ ≤ |ω| → W ω = I / ω
  W_conj : ∀ ω : ℝ, W (-ω) = conj (W ω)
  /-- The clustering step `g` (Definition 5.8, Remark 6.20): the two properties the proofs use,
  `g = 0` on `[-Δ, ∞)` and `g = 1` on `(-∞, -γ]`. -/
  g : ℝ → ℂ
  g_zero : ∀ ω : ℝ, -Δ ≤ ω → g ω = 0
  g_one : ∀ ω : ℝ, ω ≤ -γ → g ω = 1

namespace Setting

variable (S : Setting E)

/-- `Q = Q_- + Q_m + Q_+ = Q_{Γ}` (Setting 6.1). -/
def Q : E →L[ℂ] E := S.Qminus + S.Qmid + S.Qplus

/-- `P = ∑_{E ∈ [E_1, E_p]} P_E Π`: the spectral projection of `H|_{sector}` onto `[a, b]`,
extended by zero (Assumption 6.3; proofs of Lemma 6.7 and Proposition 6.10). -/
def P : E →L[ℂ] E := specProj S.H S.H_sa (Set.Icc S.a S.b) * S.Psec

/-- `p = rank P` (Assumption 6.3). -/
def p : ℕ := Module.finrank ℂ (LinearMap.range (S.P : E →ₗ[ℂ] E))

/-- `K_- = ∑_{E,E'} \widehat W_γ(E' - E) P_E J_- P_{E'}` (Definition 6.5 through Lemma 5.9). -/
def Kminus : E →L[ℂ] E := spectralSum S.H S.H_sa (fun μ ν => S.W (ν - μ)) S.Jminus

/-- `K_+ = ∑_{E,E'} \widehat W_γ(E' - E) P_E J_+ P_{E'}` (Definition 6.5 through Lemma 5.9). -/
def Kplus : E →L[ℂ] E := spectralSum S.H S.H_sa (fun μ ν => S.W (ν - μ)) S.Jplus

/-- `K^U_- = U^* K_- U` (Definition 6.11). -/
def KUminus : E →L[ℂ] E := star S.U * S.Kminus * S.U

/-- `K^U_+ = U^* K_+ U` (Definition 6.11). -/
def KUplus : E →L[ℂ] E := star S.U * S.Kplus * S.U

/-- `\overline Q = Q - K_- - K_+` (Definition 6.5). -/
def Qbar : E →L[ℂ] E := S.Q - S.Kminus - S.Kplus

/-- `\overline Q_- = Q_- - K_-` (Definition 6.11). -/
def QbarMinus : E →L[ℂ] E := S.Qminus - S.Kminus

/-- `\overline Q_+ = Q_+ - K_+` (Definition 6.11). -/
def QbarPlus : E →L[ℂ] E := S.Qplus - S.Kplus

/-- `\overline Q^U_- = Q_- + T_- - K^U_-` (Definition 6.11). -/
def QbarUMinus : E →L[ℂ] E := S.Qminus + S.Tminus - S.KUminus

/-- `\overline Q^U_+ = Q_+ + T_+ - K^U_+` (Definition 6.11). -/
def QbarUPlus : E →L[ℂ] E := S.Qplus + S.Tplus - S.KUplus

/-- `\widetilde T_- = \overline Q^U_- - \overline Q_- = T_- - K^U_- + K_-` (Definition 6.11). -/
def Ttilde : E →L[ℂ] E := S.Tminus - S.KUminus + S.Kminus

/-- `\mathcal M_-(φ) = e^{iφ \overline Q^U_-} e^{-iφ \overline Q_-}` (Definition 6.11). -/
def Mminus (φ : ℝ) : E →L[ℂ] E :=
  NormedSpace.exp ((I * φ) • S.QbarUMinus) * NormedSpace.exp ((-(I * φ)) • S.QbarMinus)

/-- `\mathcal M_+(φ) = e^{iφ \overline Q^U_+} e^{-iφ \overline Q_+}` (Definition 6.11). -/
def Mplus (φ : ℝ) : E →L[ℂ] E :=
  NormedSpace.exp ((I * φ) • S.QbarUPlus) * NormedSpace.exp ((-(I * φ)) • S.QbarPlus)

/-- `e^{2πi \overline Q_-}` (Lemma 6.12, Corollary 6.15). -/
def Ominus : E →L[ℂ] E := NormedSpace.exp ((2 * π * I) • S.QbarMinus)

/-- `e^{2πi \overline Q_+}` (Lemma 6.12, Corollary 6.15). -/
def Oplus : E →L[ℂ] E := NormedSpace.exp ((2 * π * I) • S.QbarPlus)

/-- The clustering filter `\mathcal Q(A) = g(ad_H)(A) = ∑_{E,E'} g(E - E') P_E A P_{E'}`
(Definition 5.8). -/
def Qf (A : E →L[ℂ] E) : E →L[ℂ] E := spectralSum S.H S.H_sa (fun μ ν => S.g (μ - ν)) A

end Setting

/-- The constant `C(p, M)` of the conclusion. A hand derivation gives, for
`ε ≤ ε_* = 1/(648π² + 8)`, the bound `p (386.5 M + 16.7) √ε`, and for `ε > ε_*` the trivial bound
`1/2 ≤ 40.1 · √ε`; the stated `1000 p (M + 1)` covers both with a factor of about 2.5 to spare
on the hand arithmetic. Linear in `p` and `M`, as Remark 6.19 says of the paper's constants. -/
def indexConst (p : ℕ) (M : ℝ) : ℝ := 1000 * p * (M + 1)

end HRTorus.IndexCore

end -- noncomputable section (and `open Classical`)

/-! ## What Lean prints -/

#print HRTorus.IndexCore.Setting
#print HRTorus.IndexCore.spectralSum
#print HRTorus.IndexCore.eigProj
#print HRTorus.IndexCore.Setting.P
#print HRTorus.IndexCore.Setting.Kminus
#print HRTorus.IndexCore.Setting.Qf
#print HRTorus.IndexCore.Setting.Mminus
#print HRTorus.IndexCore.Setting.p
#print HRTorus.IndexCore.Setting.Q
#print HRTorus.IndexCore.Setting.Kplus
#print HRTorus.IndexCore.Setting.KUminus
#print HRTorus.IndexCore.Setting.KUplus
#print HRTorus.IndexCore.Setting.Qbar
#print HRTorus.IndexCore.Setting.QbarMinus
#print HRTorus.IndexCore.Setting.QbarPlus
#print HRTorus.IndexCore.Setting.QbarUMinus
#print HRTorus.IndexCore.Setting.QbarUPlus
#print HRTorus.IndexCore.Setting.Mplus
#print HRTorus.IndexCore.Setting.Ominus
#print HRTorus.IndexCore.Setting.Oplus
#print HRTorus.IndexCore.specProj
#print HRTorus.IndexCore.spec
#print HRTorus.IndexCore.indexConst
#print axioms HRTorus.IndexCore.Setting.Kminus
#print axioms HRTorus.IndexCore.Setting.Qf
#print axioms HRTorus.IndexCore.Setting.P
#print axioms HRTorus.IndexCore.Setting.Mminus
#print axioms HRTorus.IndexCore.Setting.Oplus
