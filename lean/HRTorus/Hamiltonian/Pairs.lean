import HRTorus.Fock.Embedding
import HRTorus.Fock.Hamiltonian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Triplet pairs, the local terms, the operator integral and the jets (T-0056 block C, `Hamiltonian.Pairs`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **The definitions and statements were written first and
reviewed against the paper before any proof (review L9a, accepted with no change); the proof phase proved every
theorem of this module — there is no `sorry` here, and nothing here depends on an open statement — with the proof
devices in sections (or docstrings) marked as such, among them one device definition, `tripletPhase`. Lemma 4.3 is
proved by a real-variable route (its devices' section says how), not by the paper's holomorphic function `Ξ̃`.**
The paper: the HR paper, `papers/hr/sections/04-hamiltonian.tex` — Definition 4.1 `def:pairs` and the remarks after
it, Lemma 4.3 `lem:jets`, Lemma 4.5 `lem:covariance` (all but its last clause, which is about `H_N`), and from the
proof of Proposition 4.4 `prop:slotH`(i) the norm bounds of the pair operators. Of §§4.1–4.2, everything that does not
mention `H_N` is here; Theorem 4.2 and the clauses about `H_N` are in `HRTorus.Hamiltonian.LocalForm`, Proposition 4.4
and the class in `HRTorus.Hamiltonian.SlotLocal`, the band charges in `HRTorus.Hamiltonian.BandCharges`. The proof
phase added the imports of `HRTorus.Fock.Hamiltonian` (for block A's `torusIntegral_shift`, in the proof of Lemma 4.5)
and of `Mathlib.Analysis.Calculus.FDeriv.Symmetric` (the symmetry of second derivatives, for Lemma 4.3).

## The model

* The triplet labels `ν ∈ {+, 0, −}` are the type `Triplet`; the triplet spinors `χ^ν` are `2 × 2` matrices indexed by
  the pilot's `Spin` (`chi`).
* `c_ν(f, g)` (`cpair`) is the paper's sum of products of block A's `c(f ⊗ σ)` (`cf`, `spinTensor`) on the physical Fock
  space; `ĉ_ν(h, h')` (`cpairHat`) the same sum with block B's `ĉ(g)` (`chatVec`), for any finite slot type `S` (used at
  `S := Slot δ₀ T`). Operator norms are block A's and block B's: `‖toCLM T A‖` on the physical side, `‖opCLM A‖` on any
  Jordan–Wigner space (`toCLM_eq_opCLM`).
* `b_ν(n)` (`bcen`) is the `tsum` over `d ∈ ℕ` of the terms `bcenTerm` (the terms with `d ≢ n (mod 2)` are `0`), in the
  topology of the operators (Mathlib's product topology on matrices: summation entrywise); the summability, absolute in
  the operator norm, is the statement `summable_bcenTerm`.
* **The operator-valued integral** `∫_D h_R dR` is **entrywise** (`opIntegral`): the matrix whose `(m, m')` entry is the
  Bochner integral `∫ R in D, (h R) m m'` for Lebesgue measure on `ℝ × ℝ` (block A's `fundDom`, `torusIntegral`). On the
  finite-dimensional space of operators this is the Bochner integral in any norm; `opCLM_opIntegral` is the bridge to
  Mathlib's Bochner integral of `R ↦ opCLM (h R)`, and `iota_opIntegral` the commutation with `ι`.
* Points of `𝕋_N` are their lifts `R ∈ ℝ × ℝ` (as in `SlotFrame`); a function of `R ∈ 𝕋_N` is a periodic function on
  `ℝ²` (`hR_add_Lx`, `hR_add_Ly`), and **a Borel set `𝒟 ⊂ 𝕋_N` is its periodic preimage in `ℝ²`** (`IsTorusSet`; block
  B's convention for subsets of `ℝ/L_xℤ`, one dimension up). `∫_𝒟` is the integral over `𝒟 ∩ [0, L_x) × [0, L_y)`, and
  `𝒟 + κe_x` is the pointwise translate `(κ, 0) +ᵥ 𝒟`.
* Smoothness and Borel measurability of `R ↦ B_ν(R)`, `R ↦ h_R` are stated **entrywise** (Mathlib has no norm or
  measurable-space instance on matrices; for a finite-dimensional space this is the same as the statement for the map).
* **Lemma 4.3** is stated for a function `Φ` on `ℝ² × ℝ² = (ℝ × ℝ) × (ℝ × ℝ)`, smooth on an open set `U` containing the
  diagonal (`ContDiffOn` on `U`; its values off `U` never enter), with the covariant derivatives of (2.1) taken in each
  variable by block A's `Dx`, `Dy` (`D1x`, `D1y`, `D2x`, `D2y`, `D1`); `F_R(r) := |Φ(R + r/2, R − r/2)|²` is real-valued
  (`jetF`) and `∇²` is the real Laplacian `lapR`, written as block A's `lap` is (iterated one-variable derivatives). The
  symmetry hypotheses are asked where both sides are defined (`(r₁, r₂) ∈ U` and `(r₂, r₁) ∈ U`).
-/

open MeasureTheory
open scoped InnerProductSpace Matrix Real Pointwise ContDiff
open Complex (I)

noncomputable section

namespace HRTorus.Hamiltonian

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op IsEven CAR Alg)

/-! ## Definition 4.1: triplet spinors and pair operators -/

/-- The triplet labels `ν ∈ {+, 0, −}` of **Definition 4.1** ("`$\nu\in\{+,0,-\}$`"). -/
inductive Triplet
  | plus
  | zero
  | minus
  deriving DecidableEq, Inhabited

/-- `Triplet` is finite (written out, as the pilot's `Spin`). -/
instance : Fintype Triplet where
  elems := {Triplet.plus, Triplet.zero, Triplet.minus}
  complete := by intro x; cases x <;> simp

/-- **Definition 4.1**: "`The \emph{triplet spinors} are the symmetric matrices $\chi^\nu=(\chi^\nu_{\sigma\sigma'})_{\sigma,\sigma'\in\{\up,\dn\}}$, $\nu\in\{+,0,-\}$, with $\chi^+_{\up\up}=1$, $\chi^-_{\dn\dn}=1$, $\chi^0_{\up\dn}=\chi^0_{\dn\up}=2^{-1/2}$, and all other entries zero.`" -/
def chi : Triplet → Matrix Spin Spin ℂ
  | .plus => Matrix.of fun σ σ' => if σ = .up ∧ σ' = .up then 1 else 0
  | .zero => Matrix.of fun σ σ' => if σ ≠ σ' then (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) else 0
  | .minus => Matrix.of fun σ σ' => if σ = .dn ∧ σ' = .dn then 1 else 0

/-- **Definition 4.1**: "`For $f,g\in\hN$ and $h,h'\in\ell^2(\Slots)$ let`"
"`\cpair\nu(f,g):=\sum_{\sigma,\sigma'}\overline{\chi^\nu_{\sigma\sigma'}}\,c(f\otimes\sigma')\,c(g\otimes\sigma)`" — on the
physical Fock space, with block A's `c(f ⊗ σ)` (`cf`, `spinTensor`). -/
def cpair (T : Torus) (ν : Triplet) (f g : Space T) : FockOp T :=
  ∑ σ : Spin, ∑ σ' : Spin, star (chi ν σ σ') • (cf T (spinTensor f σ') * cf T (spinTensor g σ))

/-- **Definition 4.1**: "`\cpairhat\nu(h,h'):=\sum_{\sigma,\sigma'}\overline{\chi^\nu_{\sigma\sigma'}}\,\chat(h\otimes\sigma')\,\chat(h'\otimes\sigma)`"
for `h, h' ∈ ℓ²(S)`, any finite slot type `S` (block B's `ĉ(g)`, `chatVec`; used at `S := Slot δ₀ T`). -/
def cpairHat {S : Type*} [Fintype S] [DecidableEq S] (ν : Triplet) (h h' : EuclideanSpace ℂ S) : Op S :=
  ∑ σ : Spin, ∑ σ' : Spin, star (chi ν σ σ') • (chatVec (spinTensor h σ') * chatVec (spinTensor h' σ))

/-- **Definition 4.1**: "`B_\nu(R):=\cpair\nu(\ev R,\evD R),\qquad h_R:=8\pi\sum_{\nu\in\{+,0,-\}}B_\nu(R)^*B_\nu(R).`" —
`B_ν(R)`, for `R ∈ ℝ²` (block A's `ev`, `evD`). -/
def Bν (T : Torus) (ν : Triplet) (R : ℝ × ℝ) : FockOp T :=
  cpair T ν (ev T R) (evD T R)

/-- **Definition 4.1**: the local term "`h_R:=8\pi\sum_{\nu\in\{+,0,-\}}B_\nu(R)^*B_\nu(R).`" -/
def hR (T : Torus) (R : ℝ × ℝ) : FockOp T :=
  ((8 * π : ℝ) : ℂ) • ∑ ν : Triplet, (Bν T ν R)ᴴ * Bν T ν R

/-- The term of index `d ∈ ℕ` of the series defining `b_ν(n)`: `2d e^{−κ²d²/4} c_ν(ψ_{[(n−d)/2]}, ψ_{[(n+d)/2]})` if
`d ≡ n (mod 2)` (then `(n ∓ d)/2` are integers, and `[·]` is the class in `ℤ_{N_φ}`), and `0` otherwise. -/
def bcenTerm (T : Torus) (ν : Triplet) (n : ℤ) (d : ℕ) : FockOp T :=
  if (d : ℤ) ≡ n [ZMOD 2] then
    ((2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) : ℝ) : ℂ) •
      cpair T ν (orb T (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ)) (orb T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ))
  else 0

/-- **Definition 4.1**: "`For $n\in\Z$ let`"
"`\bcen\nu n:=\sum_{d\in\N,\ d\equiv n\ (\mathrm{mod}\ 2)}2d\,e^{-\kappa^2d^2/4}\, \cpair\nu\bigl(\psi_{[(n-d)/2]},\psi_{[(n+d)/2]}\bigr),`"
— the sum of `bcenTerm` over `d ∈ ℕ` (a `tsum`; its convergence is `summable_bcenTerm`). -/
def bcen (T : Torus) (ν : Triplet) (n : ℤ) : FockOp T :=
  ∑' d : ℕ, bcenTerm T ν n d

/-! ### Proof devices for Definition 4.1 and the remarks after it (phase (b); not statements of the paper) -/

section Devices41

theorem chi_symm_apply (ν : Triplet) (σ σ' : Spin) : chi ν σ' σ = chi ν σ σ' := by
  cases ν <;> cases σ <;> cases σ' <;> simp [chi]

theorem spinTensor_add' {ι : Type*} [Fintype ι] (g h : EuclideanSpace ℂ ι) (σ : Spin) :
    spinTensor (g + h) σ = spinTensor g σ + spinTensor h σ := by
  refine PiLp.ext fun μ => ?_
  simp only [spinTensor, PiLp.add_apply, WithLp.ofLp_toLp]
  split_ifs <;> simp

theorem spinTensor_smul' {ι : Type*} [Fintype ι] (a : ℂ) (g : EuclideanSpace ℂ ι) (σ : Spin) :
    spinTensor (a • g) σ = a • spinTensor g σ := by
  refine PiLp.ext fun μ => ?_
  simp only [spinTensor, PiLp.smul_apply, WithLp.ofLp_toLp, smul_eq_mul]
  split_ifs <;> simp

theorem spinTensor_zero' {ι : Type*} [Fintype ι] (σ : Spin) : spinTensor (0 : EuclideanSpace ℂ ι) σ = 0 := by
  refine PiLp.ext fun μ => ?_
  simp only [spinTensor, PiLp.zero_apply, WithLp.ofLp_toLp]
  split_ifs <;> simp

theorem norm_spinTensor {ι : Type*} [Fintype ι] (g : EuclideanSpace ℂ ι) (σ : Spin) :
    ‖spinTensor g σ‖ = ‖g‖ := by
  have h := inner_spinTensor g g σ σ
  rw [if_pos rfl, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖spinTensor g σ‖ ^ 2 = ‖g‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem cpairHat_smul_smul (ν : Triplet) (a b : ℂ) (h h' : EuclideanSpace ℂ S) :
    cpairHat ν (a • h) (b • h') = (star a * star b) • cpairHat ν h h' := by
  simp only [cpairHat, spinTensor_smul', chatVec_smul, smul_mul_smul_comm, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
  congr 1
  ring

theorem opCLM_mul (A B : Op S) : opCLM (A * B) = opCLM A * opCLM B :=
  map_mul (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)) A B

theorem opCLM_conjTranspose (A : Op S) : opCLM Aᴴ = star (opCLM A) :=
  map_star (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)) A

theorem norm_opCLM_mul_le (A B : Op S) : ‖opCLM (A * B)‖ ≤ ‖opCLM A‖ * ‖opCLM B‖ := by
  rw [opCLM_mul]; exact norm_mul_le _ _

theorem chatVec_mul_self (g : EuclideanSpace ℂ (Mode S)) : chatVec g * chatVec g = 0 := by
  have h := chatVec_anticomm g g
  have h2 : (2 : ℂ) • (chatVec g * chatVec g) = 0 := by rw [two_smul]; exact h
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem opCLM_add (A B : Op S) : opCLM (A + B) = opCLM A + opCLM B :=
  map_add (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)) A B

theorem opCLM_smul (c : ℂ) (A : Op S) : opCLM (c • A) = c • opCLM A :=
  map_smul (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)) c A

theorem opCLM_one : opCLM (1 : Op S) = 1 :=
  map_one (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ))

theorem opCLM_zero : opCLM (0 : Op S) = 0 :=
  map_zero (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ))

theorem opCLM_sum {ι : Type*} (s : Finset ι) (A : ι → Op S) : opCLM (∑ i ∈ s, A i) = ∑ i ∈ s, opCLM (A i) :=
  map_sum (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)) A s

theorem opCLM_injective : Function.Injective (fun A : Op S => opCLM A) :=
  (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)).injective

theorem norm_star_mul_self_CLM (a : EuclideanSpace ℂ (Conf S) →L[ℂ] EuclideanSpace ℂ (Conf S)) :
    ‖star a * a‖ = ‖a‖ * ‖a‖ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.norm_adjoint_comp_self a

theorem norm_opCLM_conjTranspose_mul_self (A : Op S) : ‖opCLM (Aᴴ * A)‖ = ‖opCLM A‖ * ‖opCLM A‖ := by
  rw [opCLM_mul, opCLM_conjTranspose]; exact norm_star_mul_self_CLM _

theorem norm_chatVec' (g : EuclideanSpace ℂ (Mode S)) : ‖opCLM (chatVec g)‖ = ‖g‖ := by
  have hxx := chatVec_mul_self g
  have hcar := chatVec_anticomm_star g g
  have hin : ⟪g, g⟫_ℂ = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [hin] at hcar
  generalize chatVec g = x at hxx hcar ⊢
  have h1 : x * xᴴ = ((‖g‖ ^ 2 : ℝ) : ℂ) • (1 : Op S) - xᴴ * x := eq_sub_of_add_eq hcar
  have h2 : xᴴ * xᴴ = 0 := by rw [← Matrix.conjTranspose_mul, hxx, Matrix.conjTranspose_zero]
  have hPP : (xᴴ * x) * (xᴴ * x) = ((‖g‖ ^ 2 : ℝ) : ℂ) • (xᴴ * x) := by
    calc (xᴴ * x) * (xᴴ * x) = xᴴ * (x * xᴴ) * x := by simp only [Matrix.mul_assoc]
      _ = xᴴ * (((‖g‖ ^ 2 : ℝ) : ℂ) • (1 : Op S) - xᴴ * x) * x := by rw [h1]
      _ = ((‖g‖ ^ 2 : ℝ) : ℂ) • (xᴴ * x) - (xᴴ * xᴴ) * (x * x) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, smul_one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Matrix.mul_assoc]
      _ = ((‖g‖ ^ 2 : ℝ) : ℂ) • (xᴴ * x) := by rw [h2, Matrix.zero_mul, sub_zero]
  have hP1 := norm_opCLM_conjTranspose_mul_self x
  have hPsa : (xᴴ * x)ᴴ = xᴴ * x := by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hP2 : ‖opCLM (xᴴ * x)‖ * ‖opCLM (xᴴ * x)‖ = ‖g‖ ^ 2 * ‖opCLM (xᴴ * x)‖ := by
    have e1 := norm_opCLM_conjTranspose_mul_self (xᴴ * x)
    rw [hPsa, hPP, opCLM_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at e1
    exact e1.symm
  by_cases hx0 : ‖opCLM x‖ = 0
  · have ha0 : x = 0 := by
      apply opCLM_injective
      simp only [opCLM_zero]
      exact norm_eq_zero.mp hx0
    rw [ha0] at hcar
    simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero] at hcar
    have hg : ((‖g‖ ^ 2 : ℝ) : ℂ) = 0 := by
      have h1ne : (1 : Op S) ≠ 0 := one_ne_zero
      exact (smul_eq_zero.mp hcar.symm).resolve_right h1ne
    have hg' : ‖g‖ = 0 := by
      have : ‖g‖ ^ 2 = 0 := by exact_mod_cast hg
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    rw [hx0, hg']
  · have hPne : ‖opCLM (xᴴ * x)‖ ≠ 0 := by rw [hP1]; exact mul_ne_zero hx0 hx0
    have hPeq : ‖opCLM (xᴴ * x)‖ = ‖g‖ ^ 2 := mul_right_cancel₀ hPne hP2
    rw [hP1] at hPeq
    have : ‖opCLM x‖ ^ 2 = ‖g‖ ^ 2 := by rw [sq]; exact hPeq
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

theorem norm_chatVec_mul_le (g g' : EuclideanSpace ℂ (Mode S)) :
    ‖opCLM (chatVec g * chatVec g')‖ ≤ ‖g‖ * ‖g'‖ := by
  calc ‖opCLM (chatVec g * chatVec g')‖ ≤ ‖opCLM (chatVec g)‖ * ‖opCLM (chatVec g')‖ := norm_opCLM_mul_le _ _
    _ = ‖g‖ * ‖g'‖ := by rw [norm_chatVec', norm_chatVec']

theorem cpairHat_plus (h h' : EuclideanSpace ℂ S) :
    cpairHat .plus h h' = chatVec (spinTensor h .up) * chatVec (spinTensor h' .up) := by
  simp [cpairHat, HRTorus.Fermion.Pilot.JW.sum_spin, chi]

theorem cpairHat_minus (h h' : EuclideanSpace ℂ S) :
    cpairHat .minus h h' = chatVec (spinTensor h .dn) * chatVec (spinTensor h' .dn) := by
  simp [cpairHat, HRTorus.Fermion.Pilot.JW.sum_spin, chi]

theorem cpairHat_zero (h h' : EuclideanSpace ℂ S) :
    cpairHat .zero h h' = (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      (chatVec (spinTensor h .dn) * chatVec (spinTensor h' .up) +
        chatVec (spinTensor h .up) * chatVec (spinTensor h' .dn)) := by
  simp [cpairHat, HRTorus.Fermion.Pilot.JW.sum_spin, chi, smul_add, Complex.conj_ofReal]

theorem two_mul_rpow_neg_half : (2 : ℝ) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Real.sqrt_eq_rpow, Real.rpow_neg h2.le, ← div_eq_mul_inv,
    div_eq_iff (Real.rpow_pos_of_pos h2 _).ne', ← Real.rpow_add h2]
  norm_num

theorem norm_cpairHat_le' (ν : Triplet) (h h' : EuclideanSpace ℂ S) :
    ‖opCLM (cpairHat ν h h')‖ ≤ (if ν = .zero then Real.sqrt 2 else 1) * ‖h‖ * ‖h'‖ := by
  cases ν with
  | plus =>
    rw [cpairHat_plus]
    simpa [norm_spinTensor] using norm_chatVec_mul_le (spinTensor h .up) (spinTensor h' .up)
  | minus =>
    rw [cpairHat_minus]
    simpa [norm_spinTensor] using norm_chatVec_mul_le (spinTensor h .dn) (spinTensor h' .dn)
  | zero =>
    rw [cpairHat_zero, opCLM_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by norm_num) _), if_pos rfl]
    have h1 := norm_chatVec_mul_le (spinTensor h .dn) (spinTensor h' .up)
    have h2 := norm_chatVec_mul_le (spinTensor h .up) (spinTensor h' .dn)
    simp only [norm_spinTensor] at h1 h2
    have hsum : ‖opCLM (chatVec (spinTensor h .dn) * chatVec (spinTensor h' .up) +
        chatVec (spinTensor h .up) * chatVec (spinTensor h' .dn))‖ ≤ 2 * (‖h‖ * ‖h'‖) := by
      rw [opCLM_add]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ ‖h‖ * ‖h'‖ + ‖h‖ * ‖h'‖ := add_le_add h1 h2
        _ = 2 * (‖h‖ * ‖h'‖) := by ring
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
    calc (2 : ℝ) ^ (-(1 / 2 : ℝ)) * ‖_‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * (‖h‖ * ‖h'‖)) :=
          mul_le_mul_of_nonneg_left hsum hpos
      _ = (2 * (2 : ℝ) ^ (-(1 / 2 : ℝ))) * ‖h‖ * ‖h'‖ := by ring
      _ = Real.sqrt 2 * ‖h‖ * ‖h'‖ := by rw [two_mul_rpow_neg_half]

theorem phase_star_mul_self {z : ℂ} (hz : z.re = 0) : star (Complex.exp z) * Complex.exp z = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have : (starRingEnd ℂ) z + z = 0 := by
    apply Complex.ext <;> simp [hz]
  rw [this, Complex.exp_zero]

theorem cpairHat_zero_left (ν : Triplet) (h' : EuclideanSpace ℂ S) : cpairHat ν 0 h' = 0 := by
  simp [cpairHat, spinTensor_zero', chatVec, cVec]

theorem cpairHat_zero_right (ν : Triplet) (h : EuclideanSpace ℂ S) : cpairHat ν h 0 = 0 := by
  simp [cpairHat, spinTensor_zero', chatVec, cVec]

theorem cpairHat_add_left (ν : Triplet) (h h₁ h' : EuclideanSpace ℂ S) :
    cpairHat ν (h + h₁) h' = cpairHat ν h h' + cpairHat ν h₁ h' := by
  simp only [cpairHat, spinTensor_add', chatVec_add, add_mul, smul_add, Finset.sum_add_distrib]

theorem cpairHat_add_right (ν : Triplet) (h h' h₁ : EuclideanSpace ℂ S) :
    cpairHat ν h (h' + h₁) = cpairHat ν h h' + cpairHat ν h h₁ := by
  simp only [cpairHat, spinTensor_add', chatVec_add, mul_add, smul_add, Finset.sum_add_distrib]

theorem cpairHat_smul_left (ν : Triplet) (a : ℂ) (h h' : EuclideanSpace ℂ S) :
    cpairHat ν (a • h) h' = star a • cpairHat ν h h' := by
  have := cpairHat_smul_smul ν a 1 h h'
  simpa using this

theorem cpairHat_smul_right (ν : Triplet) (a : ℂ) (h h' : EuclideanSpace ℂ S) :
    cpairHat ν h (a • h') = star a • cpairHat ν h h' := by
  have := cpairHat_smul_smul ν 1 a h h'
  simpa using this

theorem cpairHat_sum_left {ι : Type*} (ν : Triplet) (s : Finset ι) (a : ι → ℂ) (f : ι → EuclideanSpace ℂ S)
    (h' : EuclideanSpace ℂ S) :
    cpairHat ν (∑ i ∈ s, a i • f i) h' = ∑ i ∈ s, star (a i) • cpairHat ν (f i) h' := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cpairHat_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, cpairHat_add_left, cpairHat_smul_left, ih]

theorem cpairHat_sum_right {ι : Type*} (ν : Triplet) (s : Finset ι) (a : ι → ℂ) (h : EuclideanSpace ℂ S)
    (f : ι → EuclideanSpace ℂ S) :
    cpairHat ν h (∑ i ∈ s, a i • f i) = ∑ i ∈ s, star (a i) • cpairHat ν h (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cpairHat_zero_right]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, cpairHat_add_right, cpairHat_smul_right, ih]

/-- The gauge phase of the triplet `ν`: `φ_↑ + φ_↑`, `φ_↑ + φ_↓`, `φ_↓ + φ_↓`. -/
def tripletPhase (ν : Triplet) (φ : Spin → ℝ) : ℝ :=
  match ν with
  | .plus => φ .up + φ .up
  | .zero => φ .up + φ .dn
  | .minus => φ .dn + φ .dn

theorem gauge_mul' (φ : Spin → ℝ) (A B : Op S) :
    Fermion.Pilot.JW.gauge φ (A * B) = Fermion.Pilot.JW.gauge φ A * Fermion.Pilot.JW.gauge φ B := by
  rw [gauge_eq_conjAut, gauge_eq_conjAut, gauge_eq_conjAut, map_mul]

theorem gauge_conjTranspose' (φ : Spin → ℝ) (A : Op S) :
    Fermion.Pilot.JW.gauge φ Aᴴ = (Fermion.Pilot.JW.gauge φ A)ᴴ := by
  rw [gauge_eq_conjAut, gauge_eq_conjAut]
  exact map_star _ A

theorem gauge_smul' (φ : Spin → ℝ) (c : ℂ) (A : Op S) :
    Fermion.Pilot.JW.gauge φ (c • A) = c • Fermion.Pilot.JW.gauge φ A := by
  rw [gauge_eq_conjAut, gauge_eq_conjAut, map_smul]

theorem gauge_add' (φ : Spin → ℝ) (A B : Op S) :
    Fermion.Pilot.JW.gauge φ (A + B) = Fermion.Pilot.JW.gauge φ A + Fermion.Pilot.JW.gauge φ B := by
  rw [gauge_eq_conjAut, gauge_eq_conjAut, gauge_eq_conjAut, map_add]

theorem gauge_cpairHat (φ : Spin → ℝ) (ν : Triplet) (h h' : EuclideanSpace ℂ S) :
    Fermion.Pilot.JW.gauge φ (cpairHat ν h h') =
      Complex.exp (-(I * (tripletPhase ν φ : ℂ))) • cpairHat ν h h' := by
  cases ν with
  | plus =>
    rw [cpairHat_plus, gauge_mul', gauge_chatVec_spinTensor, gauge_chatVec_spinTensor, smul_mul_smul_comm,
      ← Complex.exp_add]
    congr 2
    simp only [tripletPhase]; push_cast; ring
  | minus =>
    rw [cpairHat_minus, gauge_mul', gauge_chatVec_spinTensor, gauge_chatVec_spinTensor, smul_mul_smul_comm,
      ← Complex.exp_add]
    congr 2
    simp only [tripletPhase]; push_cast; ring
  | zero =>
    rw [cpairHat_zero, gauge_smul', gauge_add', gauge_mul', gauge_mul', gauge_chatVec_spinTensor,
      gauge_chatVec_spinTensor, gauge_chatVec_spinTensor, gauge_chatVec_spinTensor, smul_mul_smul_comm,
      smul_mul_smul_comm, ← Complex.exp_add, ← Complex.exp_add]
    have e1 : -(I * ((φ Spin.dn : ℝ) : ℂ)) + -(I * ((φ Spin.up : ℝ) : ℂ)) =
        -(I * (tripletPhase .zero φ : ℂ)) := by simp only [tripletPhase]; push_cast; ring
    have e2 : -(I * ((φ Spin.up : ℝ) : ℂ)) + -(I * ((φ Spin.dn : ℝ) : ℂ)) =
        -(I * (tripletPhase .zero φ : ℂ)) := by simp only [tripletPhase]; push_cast; ring
    rw [e1, e2, ← smul_add, smul_comm]

theorem isSectorPreservingS_star_cpairHat (ν : Triplet) (h h' : EuclideanSpace ℂ S) :
    IsSectorPreservingS ((cpairHat ν h h')ᴴ * cpairHat ν h h') := by
  rw [isSectorPreservingS_iff_gauge]
  intro φ
  rw [gauge_mul', gauge_conjTranspose', gauge_cpairHat, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, phase_star_mul_self (by simp), one_smul]

theorem isSectorPreservingS_smul_sum {ι : Type*} (s : Finset ι) (c : ℂ) (A : ι → Op S)
    (hA : ∀ i ∈ s, IsSectorPreservingS (A i)) : IsSectorPreservingS (c • ∑ i ∈ s, A i) := by
  refine ⟨((Commute.sum_left _ _ _ fun i hi => (hA i hi).1)).smul_left c,
    ((Commute.sum_left _ _ _ fun i hi => (hA i hi).2)).smul_left c⟩

theorem summable_of_summable_norm_opCLM {f : ℕ → Op S} (hf : Summable fun d => ‖opCLM (f d)‖) :
    Summable f := by
  have h1 : Summable fun d => opCLM (f d) := Summable.of_norm hf
  let e := (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)).symm
  have hcont : Continuous e :=
    (e.toAlgEquiv.toLinearEquiv.toLinearMap).continuous_of_finiteDimensional
  have h2 := h1.map e hcont
  convert h2 using 1
  funext d
  simp [e]

/-- The partial derivative in `x` of a smooth function on `ℝ²` is smooth. -/
theorem contDiff_partial_x {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun r : ℝ × ℝ => deriv (fun x : ℝ => f (x, r.2)) r.1 := by
  have e : (fun r : ℝ × ℝ => deriv (fun x : ℝ => f (x, r.2)) r.1) = fun r => fderiv ℝ f r ((1 : ℝ), (0 : ℝ)) := by
    funext r
    have hd : HasFDerivAt f (fderiv ℝ f r) r := ((hf.differentiable (by simp)) r).hasFDerivAt
    have hc : HasDerivAt (fun x : ℝ => (x, r.2)) ((1 : ℝ), (0 : ℝ)) r.1 :=
      (hasDerivAt_id r.1).prodMk (hasDerivAt_const r.1 r.2)
    exact (hd.comp_hasDerivAt r.1 hc).deriv
  rw [e]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The partial derivative in `y` of a smooth function on `ℝ²` is smooth. -/
theorem contDiff_partial_y {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun r : ℝ × ℝ => deriv (fun y : ℝ => f (r.1, y)) r.2 := by
  have e : (fun r : ℝ × ℝ => deriv (fun y : ℝ => f (r.1, y)) r.2) = fun r => fderiv ℝ f r ((0 : ℝ), (1 : ℝ)) := by
    funext r
    have hd : HasFDerivAt f (fderiv ℝ f r) r := ((hf.differentiable (by simp)) r).hasFDerivAt
    have hc : HasDerivAt (fun y : ℝ => (r.1, y)) ((0 : ℝ), (1 : ℝ)) r.2 :=
      (hasDerivAt_const r.2 r.1).prodMk (hasDerivAt_id r.2)
    exact (hd.comp_hasDerivAt r.2 hc).deriv
  rw [e]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_Dcov {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dcov f) := by
  have hx := contDiff_partial_x hf
  have hy := contDiff_partial_y hf
  have h1 : ContDiff ℝ ∞ fun r : ℝ × ℝ => ((r.1 : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  have e : Dcov f = fun r => (1 / 2 : ℂ) * (deriv (fun x : ℝ => f (x, r.2)) r.1 -
      I * (deriv (fun y : ℝ => f (r.1, y)) r.2 - I * (r.1 : ℂ) * f r)) := rfl
  rw [e]
  exact contDiff_const.mul (hx.sub (contDiff_const.mul (hy.sub ((contDiff_const.mul h1).mul hf))))

theorem contDiff_star' {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ fun r => star (f r) := by
  have h : (fun r => star (f r)) = fun r => Complex.conjCLE (f r) := by
    funext r; simp [Complex.conjCLE_apply]
  rw [h]
  exact Complex.conjCLE.contDiff.comp hf

theorem Θ_conj_mul (T : Torus) (A B : FockOp T) :
    (Θ T)ᴴ * (A * B) * Θ T = ((Θ T)ᴴ * A * Θ T) * ((Θ T)ᴴ * B * Θ T) := by
  have hu : Θ T * (Θ T)ᴴ = 1 := mul_conjTranspose_self_of_mem_unitary (Θ_mem_unitary T)
  rw [show (Θ T)ᴴ * A * Θ T * ((Θ T)ᴴ * B * Θ T) = (Θ T)ᴴ * A * (Θ T * (Θ T)ᴴ) * B * Θ T by
    simp only [Matrix.mul_assoc], hu, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem Θ_conj_conjTranspose (T : Torus) (A : FockOp T) :
    (Θ T)ᴴ * Aᴴ * Θ T = ((Θ T)ᴴ * A * Θ T)ᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem Θ_conj_cf_spin (T : Torus) (f : Space T) (σ : Spin) :
    (Θ T)ᴴ * cf T (spinTensor f σ) * Θ T = cf T (spinTensor (thx T f) σ) := by
  rw [Θ_conj_cf, thx2_spinTensor]

theorem Θ_conj_cpair (T : Torus) (ν : Triplet) (f g : Space T) :
    (Θ T)ᴴ * cpair T ν f g * Θ T = cpair T ν (thx T f) (thx T g) := by
  simp only [cpair, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Θ_conj_mul, Θ_conj_cf_spin]

end Devices41

/-! ### Statements: Definition 4.1 and the remarks after it -/

/-- **Definition 4.1**: the triplet spinors are "`the symmetric matrices`". -/
theorem chi_transpose (ν : Triplet) : (chi ν)ᵀ = chi ν := by
  ext σ σ'
  rw [Matrix.transpose_apply]
  exact chi_symm_apply ν σ σ'

/-- **Definition 4.1**: "`so that $\cpair\nu(g,f)=-\cpair\nu(f,g)$`". -/
theorem cpair_swap (T : Torus) (ν : Triplet) (f g : Space T) : cpair T ν g f = -cpair T ν f g := by
  have hc : ∀ σ σ' : Spin, cf T (spinTensor g σ') * cf T (spinTensor f σ) =
      -(cf T (spinTensor f σ) * cf T (spinTensor g σ')) :=
    fun σ σ' => eq_neg_of_add_eq_zero_left (cf_anticomm T _ _)
  simp only [cpair, hc, smul_neg, Finset.sum_neg_distrib]
  rw [neg_inj, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
  rw [chi_symm_apply]

/-- The remark after **Definition 4.1**: "`in particular $\cpair\nu(f,f)=0$`". -/
theorem cpair_self (T : Torus) (ν : Triplet) (f : Space T) : cpair T ν f f = 0 := by
  have h := cpair_swap T ν f f
  have h2 : (2 : ℂ) • cpair T ν f f = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The remark after **Definition 4.1**: "`Both $\cpair\nu$ and $\cpairhat\nu$ are conjugate-linear in each argument`" —
`c_ν`, the first argument. -/
theorem cpair_smul_add_left (T : Torus) (ν : Triplet) (a : ℂ) (f f' g : Space T) :
    cpair T ν (a • f + f') g = star a • cpair T ν f g + cpair T ν f' g := by
  have e : ∀ x y : Space T, cpair T ν x y = cpairHat (S := ZMod T.Nφ) ν x y := fun _ _ => rfl
  rw [e, e, e, cpairHat_add_left, cpairHat_smul_left]

/-- The same, `c_ν`, the second argument. -/
theorem cpair_smul_add_right (T : Torus) (ν : Triplet) (a : ℂ) (f g g' : Space T) :
    cpair T ν f (a • g + g') = star a • cpair T ν f g + cpair T ν f g' := by
  have e : ∀ x y : Space T, cpair T ν x y = cpairHat (S := ZMod T.Nφ) ν x y := fun _ _ => rfl
  rw [e, e, e, cpairHat_add_right, cpairHat_smul_right]

/-- The same, `ĉ_ν`, the first argument. -/
theorem cpairHat_smul_add_left {S : Type*} [Fintype S] [DecidableEq S] (ν : Triplet) (a : ℂ)
    (h h₁ h' : EuclideanSpace ℂ S) :
    cpairHat ν (a • h + h₁) h' = star a • cpairHat ν h h' + cpairHat ν h₁ h' := by
  rw [cpairHat_add_left, cpairHat_smul_left]

/-- The same, `ĉ_ν`, the second argument. -/
theorem cpairHat_smul_add_right {S : Type*} [Fintype S] [DecidableEq S] (ν : Triplet) (a : ℂ)
    (h h' h₁ : EuclideanSpace ℂ S) :
    cpairHat ν h (a • h' + h₁) = star a • cpairHat ν h h' + cpairHat ν h h₁ := by
  rw [cpairHat_add_right, cpairHat_smul_right]

/-- `c_ν` is `ĉ_ν` at the slot type `S = ℤ_{N_φ}` (block B's bridge `cf_eq_chatVec`; a model statement). -/
theorem cpair_eq_cpairHat (T : Torus) (ν : Triplet) (f g : Space T) :
    cpair T ν f g = cpairHat (S := ZMod T.Nφ) ν f g := by
  rfl

/-- **Definition 4.1**: "`and $\iota(\cpair\nu(f,g))=\cpairhat\nu(\Sa f,\Sa g)$`" (the remark after it: "`because $\iota(c(f\otimes\sigma))=\chat(\Sa f\otimes\sigma)$`"). -/
theorem iota_cpair {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀)
    (ν : Triplet) (f g : Space T) :
    iota η δ₀ T (cpair T ν f g) = cpairHat ν (analysis η δ₀ T f) (analysis η δ₀ T g) := by
  rw [← iotaHom_apply hη hδ₀ hT]
  simp only [cpair, cpairHat, map_sum, map_smul, map_mul, iotaHom_apply, iota_cf hη hδ₀ hT, analysis2_spinTensor]

/-- The proof of **Proposition 4.4(i)**: "`$\norm{c(f)}=\norm f$. The same holds for $\chat$.`" — for `ĉ(g)` on any
Jordan–Wigner space, hence for `c(f)` (`cf_eq_chatVec`, `toCLM_eq_opCLM`). -/
theorem norm_chatVec {S : Type*} [Fintype S] [DecidableEq S] (g : EuclideanSpace ℂ (Mode S)) :
    ‖opCLM (chatVec g)‖ = ‖g‖ := by
  exact norm_chatVec' g

/-- The proof of **Proposition 4.4(i)**:
"`\norm{\cpair\pm(f,g)}\le\norm f\norm g,\qquad\norm{\cpair0(f,g)}\le\sqrt2\norm f\norm g,`" — `ν = ±`. -/
theorem norm_cpair_le_of_ne_zero (T : Torus) {ν : Triplet} (hν : ν ≠ .zero) (f g : Space T) :
    ‖toCLM T (cpair T ν f g)‖ ≤ ‖f‖ * ‖g‖ := by
  rw [toCLM_eq_opCLM, cpair_eq_cpairHat]
  have := norm_cpairHat_le' ν f g
  rwa [if_neg hν, one_mul] at this

/-- The proof of **Proposition 4.4(i)**: `‖c_0(f, g)‖ ≤ √2 ‖f‖ ‖g‖`. -/
theorem norm_cpair_zero_le (T : Torus) (f g : Space T) :
    ‖toCLM T (cpair T .zero f g)‖ ≤ Real.sqrt 2 * ‖f‖ * ‖g‖ := by
  rw [toCLM_eq_opCLM, cpair_eq_cpairHat]
  simpa using norm_cpairHat_le' Triplet.zero f g

/-- The remark after **Definition 4.1**: "`The series defining $\bcen\nu n$ converges absolutely since $\norm{\cpair\nu(f,g)}\le\sqrt2\norm f\norm g$`". -/
theorem norm_cpair_le (T : Torus) (ν : Triplet) (f g : Space T) :
    ‖toCLM T (cpair T ν f g)‖ ≤ Real.sqrt 2 * ‖f‖ * ‖g‖ := by
  rw [toCLM_eq_opCLM, cpair_eq_cpairHat]
  have h := norm_cpairHat_le' ν f g
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  split_ifs at h with hν
  · exact h
  · calc _ ≤ 1 * ‖f‖ * ‖g‖ := h
      _ ≤ Real.sqrt 2 * ‖f‖ * ‖g‖ := by gcongr

/-- The proof of **Proposition 4.4(i)**: "`and likewise for $\cpairhat\nu$.`" — `ν = ±`. -/
theorem norm_cpairHat_le_of_ne_zero {S : Type*} [Fintype S] [DecidableEq S] {ν : Triplet} (hν : ν ≠ .zero)
    (h h' : EuclideanSpace ℂ S) : ‖opCLM (cpairHat ν h h')‖ ≤ ‖h‖ * ‖h'‖ := by
  have := norm_cpairHat_le' ν h h'
  rwa [if_neg hν, one_mul] at this

/-- The proof of **Proposition 4.4(i)**, "`and likewise for $\cpairhat\nu$.`" — `ν = 0`. -/
theorem norm_cpairHat_zero_le {S : Type*} [Fintype S] [DecidableEq S] (h h' : EuclideanSpace ℂ S) :
    ‖opCLM (cpairHat .zero h h')‖ ≤ Real.sqrt 2 * ‖h‖ * ‖h'‖ := by
  simpa using norm_cpairHat_le' Triplet.zero h h'

/-- **Definition 4.1**: "`an absolutely convergent sum with $\bcen\nu{n+2\Nphi}=\bcen\nu n$.`" — the convergence,
absolute in the operator norm, and the summability in the operators. -/
theorem summable_bcenTerm (T : Torus) (ν : Triplet) (n : ℤ) :
    Summable (fun d : ℕ => ‖toCLM T (bcenTerm T ν n d)‖) ∧ Summable (bcenTerm T ν n) := by
  have hκ : 0 < T.κ ^ 2 / 4 := by have := T.κ_pos; positivity
  have hb : ∀ d : ℕ, ‖toCLM T (bcenTerm T ν n d)‖ ≤
      2 * Real.sqrt 2 * ((d : ℝ) ^ 1 * Real.exp (-(T.κ ^ 2 / 4) * d)) := by
    intro d
    unfold bcenTerm
    split_ifs
    · rw [toCLM_eq_opCLM, opCLM_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := norm_cpair_le T ν (orb T (((n - (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ))
        (orb T (((n + (d : ℤ)) / 2 : ℤ) : ZMod T.Nφ))
      rw [toCLM_eq_opCLM] at h1
      simp only [orb, EuclideanSpace.norm_single, norm_one, mul_one] at h1
      have hexp : Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) ≤ Real.exp (-(T.κ ^ 2 / 4) * d) := by
        apply Real.exp_le_exp.mpr
        have hd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h | h
          · simp [h]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h
            nlinarith
        have hk : 0 ≤ T.κ ^ 2 := sq_nonneg _
        nlinarith
      have hnn : 0 ≤ 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) := by positivity
      rw [abs_of_nonneg hnn]
      calc 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) * ‖opCLM (cpair T ν _ _)‖
          ≤ 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_left h1 hnn
        _ ≤ 2 * (d : ℝ) * Real.exp (-(T.κ ^ 2 / 4) * d) * Real.sqrt 2 := by gcongr
        _ = 2 * Real.sqrt 2 * ((d : ℝ) ^ 1 * Real.exp (-(T.κ ^ 2 / 4) * d)) := by ring
    · rw [toCLM_eq_opCLM, opCLM_zero, norm_zero]; positivity
  have hs : Summable fun d : ℕ => 2 * Real.sqrt 2 * ((d : ℝ) ^ 1 * Real.exp (-(T.κ ^ 2 / 4) * d)) :=
    (Real.summable_pow_mul_exp_neg_nat_mul 1 hκ).mul_left _
  have h1 : Summable fun d : ℕ => ‖toCLM T (bcenTerm T ν n d)‖ :=
    Summable.of_nonneg_of_le (fun d => norm_nonneg _) hb hs
  exact ⟨h1, summable_of_summable_norm_opCLM h1⟩

/-- **Definition 4.1**: "`with $\bcen\nu{n+2\Nphi}=\bcen\nu n$.`" (the remark after it: "`$\bcen\nu{n+2\Nphi}=\bcen\nu n$ because $(n+2\Nphi\pm d)/2=(n\pm d)/2+\Nphi$`"). -/
theorem bcen_add_two_Nφ (T : Torus) (ν : Triplet) (n : ℤ) : bcen T ν (n + 2 * (T.Nφ : ℤ)) = bcen T ν n := by
  unfold bcen
  congr 1
  funext d
  unfold bcenTerm
  have hmod : ((d : ℤ) ≡ n + 2 * (T.Nφ : ℤ) [ZMOD 2]) ↔ ((d : ℤ) ≡ n [ZMOD 2]) := by
    simp only [Int.ModEq, Int.add_mul_emod_self_left]
  have e1 : ((n + 2 * (T.Nφ : ℤ) - (d : ℤ)) / 2 : ℤ) = (n - (d : ℤ)) / 2 + T.Nφ := by
    rw [show n + 2 * (T.Nφ : ℤ) - d = (n - d) + T.Nφ * 2 by ring, Int.add_mul_ediv_right _ _ two_ne_zero]
  have e2 : ((n + 2 * (T.Nφ : ℤ) + (d : ℤ)) / 2 : ℤ) = (n + (d : ℤ)) / 2 + T.Nφ := by
    rw [show n + 2 * (T.Nφ : ℤ) + d = (n + d) + T.Nφ * 2 by ring, Int.add_mul_ediv_right _ _ two_ne_zero]
  have hc : ∀ x : ℤ, ((x + (T.Nφ : ℤ) : ℤ) : ZMod T.Nφ) = (x : ZMod T.Nφ) := by
    intro x; push_cast; simp
  simp only [hmod, e1, e2, hc]

/-- The remark after **Definition 4.1**: "`By Lemma~\ref{lem:evaluation}(i), $B_\nu(R+(0,L_y))=B_\nu(R)$ and $B_\nu(R+(L_x,0))=e^{2\iu L_xR_y}B_\nu(R)$, so $h_R$ is a function of $R\in\Tor_N$.`" — the first. -/
theorem Bν_add_Ly (T : Torus) (ν : Triplet) (R : ℝ × ℝ) : Bν T ν (R + (0, T.Ly)) = Bν T ν R := by
  simp only [Bν, ev_add_Ly, evD_add_Ly]

/-- The same: `B_ν(R + (L_x, 0)) = e^{2iL_xR_y} B_ν(R)`. -/
theorem Bν_add_Lx (T : Torus) (ν : Triplet) (R : ℝ × ℝ) :
    Bν T ν (R + (T.Lx, 0)) = Complex.exp (2 * I * (T.Lx : ℂ) * (R.2 : ℂ)) • Bν T ν R := by
  simp only [Bν]
  rw [ev_add_Lx, evD_add_Lx, cpair_eq_cpairHat, cpairHat_smul_smul, ← cpair_eq_cpairHat]
  congr 1
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The same: "`so $h_R$ is a function of $R\in\Tor_N$`" — periodic in `R_y`. -/
theorem hR_add_Ly (T : Torus) (R : ℝ × ℝ) : hR T (R + (0, T.Ly)) = hR T R := by
  simp only [hR, Bν_add_Ly]

/-- The same — periodic in `R_x`. -/
theorem hR_add_Lx (T : Torus) (R : ℝ × ℝ) : hR T (R + (T.Lx, 0)) = hR T R := by
  simp only [hR, Bν_add_Lx, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [mul_comm, phase_star_mul_self (by simp), one_smul]

/-- The remark after **Definition 4.1**: "`By conjugate linearity, $c(f\otimes\sigma)=\sum_j\ip f{\psi_j}c_{j\sigma}$ for $f\in\hN$`". -/
theorem cf_spinTensor_eq_sum (T : Torus) (f : Space T) (σ : Spin) :
    cf T (spinTensor f σ) = ∑ j, ⟪f, orb T j⟫_ℂ • cjs T j σ := by
  rw [cf, cVec, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [HRTorus.Fermion.Pilot.JW.sum_spin, cjs_eq]
  cases σ <;> simp [spinTensor, orb, EuclideanSpace.inner_single_right]

/-- The same: "`in particular $c(\ev R\otimes\sigma)=\sum_j\psi_j(R)c_{j\sigma}$ and $c(\evD R\otimes\sigma)=\sum_j(D\psi_j)(R)c_{j\sigma}$`" — the first. -/
theorem cf_spinTensor_ev (T : Torus) (R : ℝ × ℝ) (σ : Spin) :
    cf T (spinTensor (ev T R) σ) = ∑ j, psi T j R • cjs T j σ := by
  rw [cf_spinTensor_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ⟪ev T R, orb T j⟫_ℂ = psi T j R by simp [orb, EuclideanSpace.inner_single_right, ev_apply]]

/-- The same, the second: `c(e'_R ⊗ σ) = Σ_j (Dψ_j)(R) c_{jσ}`. -/
theorem cf_spinTensor_evD (T : Torus) (R : ℝ × ℝ) (σ : Spin) :
    cf T (spinTensor (evD T R) σ) = ∑ j, Dcov (psi T j) R • cjs T j σ := by
  rw [cf_spinTensor_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ⟪evD T R, orb T j⟫_ℂ = Dcov (psi T j) R by simp [orb, EuclideanSpace.inner_single_right, evD_apply]]

/-- The remark after **Definition 4.1**: "`so that $B_\nu(R)=\sum_{j,j'}\psi_j(R)\,(D\psi_{j'})(R)\,\cpair\nu(\psi_j,\psi_{j'})$`". -/
theorem Bν_eq_sum (T : Torus) (ν : Triplet) (R : ℝ × ℝ) :
    Bν T ν R = ∑ j, ∑ j', (psi T j R * Dcov (psi T j') R) • cpair T ν (orb T j) (orb T j') := by
  rw [Bν, ev, evD, cpair_eq_cpairHat, cpairHat_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cpairHat_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [smul_smul, star_star, star_star, cpair_eq_cpairHat]

/-- The remark after **Definition 4.1**: "`so $R\mapsto B_\nu(R)$ is a finite linear combination of fixed operators with smooth coefficients`"
— the entries are smooth functions of `R ∈ ℝ²`. -/
theorem Bν_contDiff (T : Torus) (ν : Triplet) (m m' : Conf (ZMod T.Nφ)) :
    ContDiff ℝ ∞ fun R : ℝ × ℝ => Bν T ν R m m' := by
  have e : (fun R : ℝ × ℝ => Bν T ν R m m') = fun R => ∑ j, ∑ j',
      (psi T j R * Dcov (psi T j') R) * cpair T ν (orb T j) (orb T j') m m' := by
    funext R
    rw [Bν_eq_sum]
    simp [Matrix.sum_apply, Matrix.smul_apply]
  rw [e]
  refine ContDiff.sum fun j _ => ContDiff.sum fun j' _ => ?_
  exact ((psi_contDiff T j).mul (contDiff_Dcov (psi_contDiff T j'))).mul contDiff_const

/-- The remark after **Definition 4.1**: "`the map $R\mapsto h_R$ is therefore smooth`" (entrywise). -/
theorem hR_contDiff (T : Torus) (m m' : Conf (ZMod T.Nφ)) : ContDiff ℝ ∞ fun R : ℝ × ℝ => hR T R m m' := by
  have e : (fun R : ℝ × ℝ => hR T R m m') = fun R => ((8 * π : ℝ) : ℂ) *
      ∑ ν : Triplet, ∑ k, star (Bν T ν R k m) * Bν T ν R k m' := by
    funext R
    simp [hR, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]
  refine contDiff_const.mul (ContDiff.sum fun ν _ => ContDiff.sum fun k _ => ?_)
  exact (contDiff_star' (Bν_contDiff T ν k m)).mul (Bν_contDiff T ν k m')

/-- The proof of **Corollary 4.8**: "`The map $R\mapsto h_R$ is smooth (see the remarks after Definition~\ref{def:pairs}), hence Borel measurable, and each $h_R$ is self-adjoint.`"
— Borel measurable (entrywise). -/
theorem hR_measurable (T : Torus) (m m' : Conf (ZMod T.Nφ)) : Measurable fun R : ℝ × ℝ => hR T R m m' := by
  exact (hR_contDiff T m m').continuous.measurable

/-- The same: "`and each $h_R$ is self-adjoint`". -/
theorem hR_isSelfAdjoint (T : Torus) (R : ℝ × ℝ) : IsSelfAdjoint (hR T R) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  simp only [hR, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  simp [Complex.star_def, Complex.conj_ofReal]

/-- The proof of **Corollary 4.8**: "`and $h_R$ commutes with $\Nup$ and $\Ndn$, that is, it is sector-preserving.`" -/
theorem hR_isSectorPreserving (T : Torus) (R : ℝ × ℝ) : IsSectorPreserving T (hR T R) := by
  rw [isSectorPreserving_iff_S, hR]
  exact isSectorPreservingS_smul_sum _ _ _ fun ν _ => isSectorPreservingS_star_cpairHat (S := ZMod T.Nφ) ν _ _

/-! ## The operator-valued integral and the Borel sets of `𝕋_N` (model) -/

/-- The operator integral `∫_D h_R dR` over a set `D ⊆ ℝ²` for Lebesgue measure, entrywise (a model definition; the module
docstring): the `(m, m')` entry is `∫ R in D, (h R) m m'`. -/
def opIntegral {S : Type*} [Fintype S] [DecidableEq S] (D : Set (ℝ × ℝ)) (h : ℝ × ℝ → Op S) : Op S :=
  Matrix.of fun m m' => ∫ R in D, h R m m'

/-- A Borel set `𝒟 ⊂ 𝕋_N`, given by its preimage in `ℝ²`: a Borel subset of `ℝ²` invariant under the periods
`(L_x, 0)` and `(0, L_y)`. -/
def IsTorusSet (T : Torus) (D : Set (ℝ × ℝ)) : Prop :=
  MeasurableSet D ∧ (∀ R : ℝ × ℝ, R + (T.Lx, 0) ∈ D ↔ R ∈ D) ∧ (∀ R : ℝ × ℝ, R + (0, T.Ly) ∈ D ↔ R ∈ D)

/-- **Lemma 4.5**: "`with $H_{\mathcal D}:=\int_{\mathcal D}h_R\,\dd R$ for a Borel set $\mathcal D\subset\Tor_N$`" — the
integral over the part `𝒟 ∩ [0, L_x) × [0, L_y)` of the periodic preimage in the fundamental domain. -/
def HD (T : Torus) (D : Set (ℝ × ℝ)) : FockOp T :=
  opIntegral (D ∩ fundDom T) (hR T)

/-! ### Proof devices for the operator integral and Lemma 4.5 (phase (b); not statements of the paper) -/

theorem matrix_eq_sum_smul_single {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    A = ∑ m, ∑ m', A m m' • Matrix.single m m' (1 : ℂ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

theorem opIntegral_map {S S' : Type*} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S']
    (Φ : Op S →ₗ[ℂ] Op S') (D : Set (ℝ × ℝ)) (h : ℝ × ℝ → Op S)
    (hint : ∀ m m' : Conf S, IntegrableOn (fun R => h R m m') D) :
    Φ (opIntegral D h) = opIntegral D fun R => Φ (h R) := by
  have hΦ : ∀ A : Op S, Φ A = ∑ m, ∑ m', A m m' • Φ (Matrix.single m m' (1 : ℂ)) := by
    intro A
    conv_lhs => rw [matrix_eq_sum_smul_single A]
    simp only [map_sum, map_smul]
  ext k k'
  rw [hΦ]
  simp only [opIntegral, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have e : (fun R => (Φ (h R)) k k') =
      fun R => ∑ m, ∑ m', h R m m' * (Φ (Matrix.single m m' (1 : ℂ))) k k' := by
    funext R
    rw [hΦ (h R)]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [e, integral_finset_sum _ (fun m _ => integrable_finset_sum _ (fun m' _ => (hint m m').mul_const _))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finset_sum _ (fun m' _ => (hint m m').mul_const _)]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [integral_mul_const]

theorem integrableOn_inter_fundDom {g : ℝ × ℝ → ℂ} (hg : Continuous g) (T : Torus) (D : Set (ℝ × ℝ)) :
    IntegrableOn g (D ∩ fundDom T) := by
  have hsub : D ∩ fundDom T ⊆ Set.Icc ((0 : ℝ), (0 : ℝ)) (T.Lx, T.Ly) := by
    rintro ⟨x, y⟩ ⟨_, hx, hy⟩
    simp only [Set.mem_Ico] at hx hy
    exact ⟨⟨hx.1, hy.1⟩, ⟨hx.2.le, hy.2.le⟩⟩
  exact (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub

theorem setIntegral_inter_fundDom_shift (T : Torus) {D : Set (ℝ × ℝ)} (hD : IsTorusSet T D) (g : ℝ × ℝ → ℂ)
    (hg : ∀ R : ℝ × ℝ, g (R + (T.Lx, 0)) = g R) :
    ∫ R in D ∩ fundDom T, g (R + (T.κ, 0)) = ∫ R in (((T.κ, 0) : ℝ × ℝ) +ᵥ D) ∩ fundDom T, g R := by
  have hvadd : ∀ R : ℝ × ℝ, R ∈ ((T.κ, 0) : ℝ × ℝ) +ᵥ D ↔ R - (T.κ, 0) ∈ D := by
    intro R
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
  have hD'm : MeasurableSet (((T.κ, 0) : ℝ × ℝ) +ᵥ D) := by
    have : (((T.κ, 0) : ℝ × ℝ) +ᵥ D) = (fun R => R - ((T.κ, 0) : ℝ × ℝ)) ⁻¹' D := by
      ext R; rw [hvadd]; rfl
    rw [this]; exact hD.1.preimage (measurable_id.sub_const _)
  set G : ℝ × ℝ → ℂ := (((T.κ, 0) : ℝ × ℝ) +ᵥ D).indicator g with hG
  have hGper : ∀ x y : ℝ, G (x + T.Lx, y) = G (x, y) := by
    intro x y
    simp only [hG, Set.indicator]
    have h1 : ((x + T.Lx, y) : ℝ × ℝ) ∈ ((T.κ, 0) : ℝ × ℝ) +ᵥ D ↔
        ((x, y) : ℝ × ℝ) ∈ ((T.κ, 0) : ℝ × ℝ) +ᵥ D := by
      rw [hvadd, hvadd]
      have := hD.2.1 ((x, y) - ((T.κ, 0) : ℝ × ℝ))
      rw [show ((x, y) - ((T.κ, 0) : ℝ × ℝ)) + (T.Lx, 0) = ((x + T.Lx, y) : ℝ × ℝ) - (T.κ, 0) by
        ext <;> simp <;> ring] at this
      exact this
    have h2 : g (x + T.Lx, y) = g (x, y) := by
      have := hg (x, y)
      rwa [show ((x, y) : ℝ × ℝ) + (T.Lx, 0) = (x + T.Lx, y) by ext <;> simp] at this
    by_cases hm : ((x, y) : ℝ × ℝ) ∈ ((T.κ, 0) : ℝ × ℝ) +ᵥ D
    · rw [if_pos (h1.mpr hm), if_pos hm, h2]
    · rw [if_neg (fun h => hm (h1.mp h)), if_neg hm]
  have hL : ∫ R in D ∩ fundDom T, g (R + (T.κ, 0)) = torusIntegral T (fun r => G (r.1 - -T.κ, r.2)) := by
    rw [Set.inter_comm, ← setIntegral_indicator hD.1, torusIntegral]
    refine setIntegral_congr_fun (measurableSet_Ico.prod measurableSet_Ico) fun r _ => ?_
    simp only [hG, Set.indicator]
    have e : ((r.1 - -T.κ, r.2) : ℝ × ℝ) = r + (T.κ, 0) := by ext <;> simp
    rw [e]
    have hm : r + (T.κ, 0) ∈ ((T.κ, 0) : ℝ × ℝ) +ᵥ D ↔ r ∈ D := by rw [hvadd, add_sub_cancel_right]
    by_cases h : r ∈ D
    · rw [if_pos h, if_pos (hm.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (hm.mp h'))]
  have hR : ∫ R in (((T.κ, 0) : ℝ × ℝ) +ᵥ D) ∩ fundDom T, g R = torusIntegral T G := by
    rw [Set.inter_comm, ← setIntegral_indicator hD'm, torusIntegral]
  rw [hL, hR, torusIntegral_shift T G hGper (-T.κ)]

/-- The entrywise integral is the Bochner integral of `R ↦ opCLM (h R)` (a model statement: the bridge to Mathlib's
integral in the normed space of operators, for entrywise integrable `h`). -/
theorem opCLM_opIntegral {S : Type*} [Fintype S] [DecidableEq S] (D : Set (ℝ × ℝ)) (h : ℝ × ℝ → Op S)
    (hint : ∀ m m' : Conf S, IntegrableOn (fun R => h R m m') D) :
    opCLM (opIntegral D h) = ∫ R in D, opCLM (h R) := by
  have hΦ : ∀ A : Op S, opCLM A = ∑ m, ∑ m', A m m' • opCLM (Matrix.single m m' (1 : ℂ)) := by
    intro A
    conv_lhs => rw [matrix_eq_sum_smul_single A]
    simp only [opCLM_sum, opCLM_smul]
  have e : (fun R => opCLM (h R)) = fun R => ∑ m, ∑ m', h R m m' • opCLM (Matrix.single m m' (1 : ℂ)) :=
    funext fun R => hΦ (h R)
  rw [hΦ, e, integral_finset_sum _ (fun m _ => integrable_finset_sum _ (fun m' _ => (hint m m').smul_const _))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finset_sum _ (fun m' _ => (hint m m').smul_const _)]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [integral_smul_const]
  rfl

/-- `ι` commutes with the operator integral, for entrywise integrable `h` (a model statement; `ι` is linear on a
finite-dimensional space). -/
theorem iota_opIntegral {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀)
    (D : Set (ℝ × ℝ)) (h : ℝ × ℝ → FockOp T) (hint : ∀ m m' : Conf (ZMod T.Nφ), IntegrableOn (fun R => h R m m') D) :
    iota η δ₀ T (opIntegral D h) = opIntegral D fun R => iota η δ₀ T (h R) := by
  have := opIntegral_map (iotaHom hη hδ₀ hT).toAlgHom.toLinearMap D h hint
  simpa [iotaHom_apply] using this

/-! ## Lemma 4.5: covariance (the clauses about `B_ν`, `h_R` and `H_𝒟`) -/

/-- **Lemma 4.5**: "`For every torus as in Definition~\ref{def:torus} and every $R\in\R^2$, $\Theta^*B_\nu(R)\Theta=e^{-2\iu\kappa R_y}B_\nu(R+\kappa\ex)$ and $\Theta^*h_R\Theta=h_{R+\kappa\ex}$.`"
— the first (`e_x = (1, 0)`). -/
theorem Θ_conj_Bν (T : Torus) (ν : Triplet) (R : ℝ × ℝ) :
    (Θ T)ᴴ * Bν T ν R * Θ T = Complex.exp (-(2 * I * (T.κ : ℂ) * (R.2 : ℂ))) • Bν T ν (R + (T.κ, 0)) := by
  simp only [Bν]
  rw [Θ_conj_cpair, thx_ev, thx_evD, cpair_eq_cpairHat, cpairHat_smul_smul, ← cpair_eq_cpairHat]
  congr 1
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **Lemma 4.5**, the second: `Θ* h_R Θ = h_{R+κe_x}`. -/
theorem Θ_conj_hR (T : Torus) (R : ℝ × ℝ) : (Θ T)ᴴ * hR T R * Θ T = hR T (R + (T.κ, 0)) := by
  simp only [hR, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine congrArg (((8 * π : ℝ) : ℂ) • ·) (Finset.sum_congr rfl fun ν _ => ?_)
  rw [Θ_conj_mul, Θ_conj_conjTranspose, Θ_conj_Bν, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, phase_star_mul_self (by simp), one_smul]

/-- **Lemma 4.5**: "`Consequently, with $H_{\mathcal D}:=\int_{\mathcal D}h_R\,\dd R$ for a Borel set $\mathcal D\subset\Tor_N$, $\Theta^*H_{\mathcal D}\Theta=H_{\mathcal D+\kappa\ex}$; in particular $[\Theta,H_N]=0$.`"
— the identity for `H_𝒟` (the last clause is `LocalForm.commute_Θ_HN`). -/
theorem Θ_conj_HD (T : Torus) {D : Set (ℝ × ℝ)} (hD : IsTorusSet T D) :
    (Θ T)ᴴ * HD T D * Θ T = HD T (((T.κ, 0) : ℝ × ℝ) +ᵥ D) := by
  have hint : ∀ m m' : Conf (ZMod T.Nφ), IntegrableOn (fun R => hR T R m m') (D ∩ fundDom T) :=
    fun m m' => integrableOn_inter_fundDom (hR_contDiff T m m').continuous T D
  let Φ : FockOp T →ₗ[ℂ] FockOp T := (LinearMap.mulLeft ℂ (Θ T)ᴴ).comp (LinearMap.mulRight ℂ (Θ T))
  have hΦ : ∀ A : FockOp T, Φ A = (Θ T)ᴴ * A * Θ T := fun A => by
    simp only [Φ, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.mul_assoc]
  rw [HD, ← hΦ, opIntegral_map Φ _ _ hint]
  simp only [hΦ, Θ_conj_hR]
  ext m m'
  simp only [HD, opIntegral, Matrix.of_apply]
  exact setIntegral_inter_fundDom_shift T hD (fun R => hR T R m m') (fun R => by rw [hR_add_Lx])

/-! ## Lemma 4.3: jets on the diagonal -/

/-- "`$\nabla^2=\partial_x^2+\partial_y^2$`" for a real function on `ℝ²`, by iterated one-variable derivatives (the real
counterpart of block A's `lap`). -/
def lapR (F : ℝ × ℝ → ℝ) (r : ℝ × ℝ) : ℝ :=
  deriv (fun x : ℝ => deriv (fun x' : ℝ => F (x', r.2)) x) r.1 +
    deriv (fun y : ℝ => deriv (fun y' : ℝ => F (r.1, y')) y) r.2

/-- **Lemma 4.3**: "`where $D_{x_i},D_{y_i}$ are the covariant derivatives \eqref{eq:covariant} in $r_i=(x_i,y_i)$`" —
`D_{x_1}`, block A's `Dx` in the first variable. -/
def D1x (Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  Dx (fun r₁ => Φ (r₁, p.2)) p.1

/-- `D_{y_1}`: block A's `Dy` in the first variable. -/
def D1y (Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  Dy (fun r₁ => Φ (r₁, p.2)) p.1

/-- `D_{x_2}`: block A's `Dx` in the second variable. -/
def D2x (Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  Dx (fun r₂ => Φ (p.1, r₂)) p.2

/-- `D_{y_2}`: block A's `Dy` in the second variable. -/
def D2y (Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  Dy (fun r₂ => Φ (p.1, r₂)) p.2

/-- **Lemma 4.3(b)**: "`where $D_1:=\frac12(D_{x_1}-\iu D_{y_1})$`". -/
def D1 (Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  (1 / 2 : ℂ) * (D1x Φ p - I * D1y Φ p)

/-- **Lemma 4.3**: "`For $R\in\R^2$ and small $r\in\R^2$ let $F_R(r):=\abs{\Phi(R+r/2,R-r/2)}^2$.`" (defined for every `r`;
only its values near `r = 0` enter the statements). -/
def jetF (Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ) (R r : ℝ × ℝ) : ℝ :=
  ‖Φ (R + (1 / 2 : ℝ) • r, R - (1 / 2 : ℝ) • r)‖ ^ 2

/-! ### Proof devices for Lemma 4.3 (phase (b); not statements of the paper)

A real-variable route: the Laplacian of `F_R` at `0` is computed along the two lines `s ↦ (R, R) + s v` (`v` the
directions of `r_x`, `r_y`), and the lowest-Landau-level equations, differentiated once at `(R, R)`, with the symmetry
of the second derivative, give `∇²(Φ(R + r/2, R − r/2))|_{r=0} = −Φ(R, R)/2`; hence
`F_R(0) + (∇²F_R)(0) = |(∂_{x₁} − ∂_{x₂})Φ(R, R)|²`, which the (anti)symmetry of `Φ` evaluates. This replaces the
paper's holomorphic function `Ξ̃` (the same computation in the coordinates `ω₁, ω₂`). -/

theorem jets_line_mem {U : Set ((ℝ × ℝ) × (ℝ × ℝ))} (hU : IsOpen U) {p : (ℝ × ℝ) × (ℝ × ℝ)} (hp : p ∈ U)
    (v : (ℝ × ℝ) × (ℝ × ℝ)) : ∀ᶠ s in nhds (0 : ℝ), p + s • v ∈ U := by
  have hcont : Continuous (fun s : ℝ => p + s • v) := by fun_prop
  have h0 : p + (0 : ℝ) • v ∈ U := by simpa using hp
  exact hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)

theorem jets_hasDerivAt_line (p v : (ℝ × ℝ) × (ℝ × ℝ)) (s : ℝ) :
    HasDerivAt (fun s' : ℝ => p + s' • v) v s := by
  simpa using ((hasDerivAt_id' (x := s)).smul_const v).const_add p

theorem jets_hasDerivAt_comp {U : Set ((ℝ × ℝ) × (ℝ × ℝ))} (hU : IsOpen U) {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ}
    (hΦ : ContDiffOn ℝ ∞ Φ U) {p : (ℝ × ℝ) × (ℝ × ℝ)} (hp : p ∈ U) (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    HasDerivAt (fun s : ℝ => Φ (p + s • v)) (fderiv ℝ Φ p v) 0 := by
  have hd : HasFDerivAt Φ (fderiv ℝ Φ p) (p + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact ((hΦ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  exact hd.comp_hasDerivAt (0 : ℝ) (jets_hasDerivAt_line p v 0)

theorem jets_hasDerivAt_fderiv {U : Set ((ℝ × ℝ) × (ℝ × ℝ))} (hU : IsOpen U) {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ}
    (hΦ : ContDiffOn ℝ ∞ Φ U) {p : (ℝ × ℝ) × (ℝ × ℝ)} (hp : p ∈ U) (v e : (ℝ × ℝ) × (ℝ × ℝ)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ Φ (p + s • v) e) (fderiv ℝ (fderiv ℝ Φ) p v e) 0 := by
  have hc : ContDiffAt ℝ ∞ (fderiv ℝ Φ) p :=
    (hΦ.contDiffAt (hU.mem_nhds hp)).fderiv_right (m := ∞) (by simp)
  have hd : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) p) (p + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact (hc.differentiableAt (by simp)).hasFDerivAt
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ Φ (p + s • v)) (fderiv ℝ (fderiv ℝ Φ) p v) 0 :=
    hd.comp_hasDerivAt (0 : ℝ) (jets_hasDerivAt_line p v 0)
  have h2 := h1.clm_apply (hasDerivAt_const (0 : ℝ) e)
  rw [map_zero, add_zero] at h2
  exact h2

/-- Device: `d²/ds² ‖Φ(p + s v)‖²` at `0`. -/
theorem jets_deriv2_normSq {U : Set ((ℝ × ℝ) × (ℝ × ℝ))} (hU : IsOpen U) {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ}
    (hΦ : ContDiffOn ℝ ∞ Φ U) {p : (ℝ × ℝ) × (ℝ × ℝ)} (hp : p ∈ U) (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    deriv (fun s : ℝ => deriv (fun s' : ℝ => ‖Φ (p + s' • v)‖ ^ 2) s) 0 =
      2 * ‖fderiv ℝ Φ p v‖ ^ 2 + 2 * inner ℝ (Φ p) (fderiv ℝ (fderiv ℝ Φ) p v v) := by
  have hd1 : (fun s : ℝ => deriv (fun s' : ℝ => ‖Φ (p + s' • v)‖ ^ 2) s) =ᶠ[nhds 0]
      fun s => 2 * inner ℝ (Φ (p + s • v)) (fderiv ℝ Φ (p + s • v) v) := by
    filter_upwards [jets_line_mem hU hp v] with s hs
    have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (p + s • v)) (p + s • v) :=
      ((hΦ.contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)).hasFDerivAt
    exact ((hΦd.comp_hasDerivAt s (jets_hasDerivAt_line p v s)).norm_sq).deriv
  rw [hd1.deriv_eq]
  have h := ((jets_hasDerivAt_comp hU hΦ hp v).inner (𝕜 := ℝ) (jets_hasDerivAt_fderiv hU hΦ hp v v)).const_mul 2
  rw [h.deriv]
  simp only [zero_smul, add_zero, real_inner_self_eq_norm_sq]
  ring

/-- Device: a function of `s` vanishing near `0` has derivative `0` there. -/
theorem jets_deriv_eq_zero {g : ℝ → ℂ} {g' : ℂ} (hg : HasDerivAt g g' 0) (h0 : g =ᶠ[nhds 0] fun _ => 0) :
    g' = 0 :=
  hg.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq h0)

/-- Device: an equation `∂_e Φ + i ∂_{e'} Φ + c Φ = 0` on `U`, `c` linear, differentiated at `p` in the direction `w`. -/
theorem jets_lll_deriv {U : Set ((ℝ × ℝ) × (ℝ × ℝ))} (hU : IsOpen U) {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ}
    (hΦ : ContDiffOn ℝ ∞ Φ U) {p : (ℝ × ℝ) × (ℝ × ℝ)} (hp : p ∈ U) (e e' : (ℝ × ℝ) × (ℝ × ℝ))
    (c : (ℝ × ℝ) × (ℝ × ℝ) → ℝ) (hc : ∀ (w : (ℝ × ℝ) × (ℝ × ℝ)) (s : ℝ), c (p + s • w) = c p + s * c w)
    (hzero : ∀ q ∈ U, fderiv ℝ Φ q e + I * fderiv ℝ Φ q e' + (c q : ℂ) * Φ q = 0) (w : (ℝ × ℝ) × (ℝ × ℝ)) :
    fderiv ℝ (fderiv ℝ Φ) p w e + I * fderiv ℝ (fderiv ℝ Φ) p w e' + (c w : ℂ) * Φ p +
      (c p : ℂ) * fderiv ℝ Φ p w = 0 := by
  have hcd : HasDerivAt (fun s : ℝ => ((c (p + s • w) : ℝ) : ℂ)) (c w : ℂ) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => c p + s * c w) (c w) 0 := by
      simpa using ((hasDerivAt_id' (x := (0 : ℝ))).mul_const (c w)).const_add (c p)
    have h2 := h1.ofReal_comp
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hc]
  have hg := ((jets_hasDerivAt_fderiv hU hΦ hp w e).add
    ((jets_hasDerivAt_fderiv hU hΦ hp w e').const_mul I)).add (hcd.mul (jets_hasDerivAt_comp hU hΦ hp w))
  have h0 : (fun s : ℝ => fderiv ℝ Φ (p + s • w) e + I * fderiv ℝ Φ (p + s • w) e' +
      ((c (p + s • w) : ℝ) : ℂ) * Φ (p + s • w)) =ᶠ[nhds 0] fun _ => 0 := by
    filter_upwards [jets_line_mem hU hp w] with s hs
    exact hzero _ hs
  have h := jets_deriv_eq_zero hg h0
  simp only [zero_smul, add_zero, hc, zero_mul] at h
  linear_combination h

theorem jets_D1x {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ} {p : (ℝ × ℝ) × (ℝ × ℝ)} (h : DifferentiableAt ℝ Φ p) :
    D1x Φ p = fderiv ℝ Φ p ((1, 0), (0, 0)) := by
  have hc : HasDerivAt (fun t : ℝ => (((t, p.1.2), p.2) : (ℝ × ℝ) × (ℝ × ℝ))) ((1, 0), (0, 0)) p.1.1 :=
    ((hasDerivAt_id' (x := p.1.1)).prodMk (hasDerivAt_const p.1.1 p.1.2)).prodMk (hasDerivAt_const p.1.1 p.2)
  exact (h.hasFDerivAt.comp_hasDerivAt p.1.1 hc).deriv

theorem jets_D1y {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ} {p : (ℝ × ℝ) × (ℝ × ℝ)} (h : DifferentiableAt ℝ Φ p) :
    D1y Φ p = fderiv ℝ Φ p ((0, 1), (0, 0)) - I * (p.1.1 : ℂ) * Φ p := by
  have hc : HasDerivAt (fun t : ℝ => (((p.1.1, t), p.2) : (ℝ × ℝ) × (ℝ × ℝ))) ((0, 1), (0, 0)) p.1.2 :=
    ((hasDerivAt_const p.1.2 p.1.1).prodMk (hasDerivAt_id' (x := p.1.2))).prodMk (hasDerivAt_const p.1.2 p.2)
  show deriv (fun y : ℝ => Φ ((p.1.1, y), p.2)) p.1.2 - I * (p.1.1 : ℂ) * Φ (p.1, p.2) = _
  rw [show (fun y : ℝ => Φ ((p.1.1, y), p.2)) = Φ ∘ (fun t : ℝ => (((p.1.1, t), p.2) : (ℝ × ℝ) × (ℝ × ℝ))) from rfl,
    (h.hasFDerivAt.comp_hasDerivAt p.1.2 hc).deriv]

theorem jets_D2x {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ} {p : (ℝ × ℝ) × (ℝ × ℝ)} (h : DifferentiableAt ℝ Φ p) :
    D2x Φ p = fderiv ℝ Φ p ((0, 0), (1, 0)) := by
  have hc : HasDerivAt (fun t : ℝ => ((p.1, (t, p.2.2)) : (ℝ × ℝ) × (ℝ × ℝ))) ((0, 0), (1, 0)) p.2.1 :=
    (hasDerivAt_const p.2.1 p.1).prodMk ((hasDerivAt_id' (x := p.2.1)).prodMk (hasDerivAt_const p.2.1 p.2.2))
  exact (h.hasFDerivAt.comp_hasDerivAt p.2.1 hc).deriv

theorem jets_D2y {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ} {p : (ℝ × ℝ) × (ℝ × ℝ)} (h : DifferentiableAt ℝ Φ p) :
    D2y Φ p = fderiv ℝ Φ p ((0, 0), (0, 1)) - I * (p.2.1 : ℂ) * Φ p := by
  have hc : HasDerivAt (fun t : ℝ => ((p.1, (p.2.1, t)) : (ℝ × ℝ) × (ℝ × ℝ))) ((0, 0), (0, 1)) p.2.2 :=
    (hasDerivAt_const p.2.2 p.1).prodMk ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id' (x := p.2.2)))
  show deriv (fun y : ℝ => Φ (p.1, (p.2.1, y))) p.2.2 - I * (p.2.1 : ℂ) * Φ (p.1, p.2) = _
  rw [show (fun y : ℝ => Φ (p.1, (p.2.1, y))) = Φ ∘ (fun t : ℝ => ((p.1, (p.2.1, t)) : (ℝ × ℝ) × (ℝ × ℝ))) from rfl,
    (h.hasFDerivAt.comp_hasDerivAt p.2.2 hc).deriv]

/-- Device: the core of Lemma 4.3, `F_R(0) = |Φ(R,R)|²` and `F_R(0) + (∇²F_R)(0) = |½(∂_{x₁} − ∂_{x₂})Φ(R,R)|² · 4`. -/
theorem jets_core {U : Set ((ℝ × ℝ) × (ℝ × ℝ))} (hU : IsOpen U) (hdiag : ∀ R : ℝ × ℝ, (R, R) ∈ U)
    {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ} (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hlll₁ : ∀ p ∈ U, D1x Φ p + I * D1y Φ p = 0) (hlll₂ : ∀ p ∈ U, D2x Φ p + I * D2y Φ p = 0) (R : ℝ × ℝ) :
    jetF Φ R 0 = ‖Φ (R, R)‖ ^ 2 ∧
      jetF Φ R 0 + lapR (jetF Φ R) 0 =
        4 * ‖(1 / 2 : ℂ) * (fderiv ℝ Φ (R, R) ((1, 0), (0, 0)) - fderiv ℝ Φ (R, R) ((0, 0), (1, 0)))‖ ^ 2 := by
  have hp := hdiag R
  set p : (ℝ × ℝ) × (ℝ × ℝ) := (R, R) with hpdef
  have hdiff : ∀ q ∈ U, DifferentiableAt ℝ Φ q := fun q hq =>
    (hΦ.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
  set ex1 : (ℝ × ℝ) × (ℝ × ℝ) := ((1, 0), (0, 0))
  set ey1 : (ℝ × ℝ) × (ℝ × ℝ) := ((0, 1), (0, 0))
  set ex2 : (ℝ × ℝ) × (ℝ × ℝ) := ((0, 0), (1, 0))
  set ey2 : (ℝ × ℝ) × (ℝ × ℝ) := ((0, 0), (0, 1))
  -- the equations of the lowest Landau level, in `fderiv` form
  have hL1 : ∀ q ∈ U, fderiv ℝ Φ q ex1 + I * fderiv ℝ Φ q ey1 + ((q.1.1 : ℝ) : ℂ) * Φ q = 0 := by
    intro q hq
    have h := hlll₁ q hq
    rw [jets_D1x (hdiff q hq), jets_D1y (hdiff q hq)] at h
    linear_combination h + (q.1.1 : ℂ) * Φ q * Complex.I_sq
  have hL2 : ∀ q ∈ U, fderiv ℝ Φ q ex2 + I * fderiv ℝ Φ q ey2 + ((q.2.1 : ℝ) : ℂ) * Φ q = 0 := by
    intro q hq
    have h := hlll₂ q hq
    rw [jets_D2x (hdiff q hq), jets_D2y (hdiff q hq)] at h
    linear_combination h + (q.2.1 : ℂ) * Φ q * Complex.I_sq
  have hc1 : ∀ (w : (ℝ × ℝ) × (ℝ × ℝ)) (s : ℝ), (p + s • w).1.1 = p.1.1 + s * w.1.1 := fun w s => by simp
  have hc2 : ∀ (w : (ℝ × ℝ) × (ℝ × ℝ)) (s : ℝ), (p + s • w).2.1 = p.2.1 + s * w.2.1 := fun w s => by simp
  have LL1 := jets_lll_deriv hU hΦ hp ex1 ey1 (fun q => q.1.1) hc1 hL1
  have LL2 := jets_lll_deriv hU hΦ hp ex2 ey2 (fun q => q.2.1) hc2 hL2
  have k0 : p.2.1 = p.1.1 := rfl
  have E7 := hL1 p hp
  have E8 := hL2 p hp
  simp only [k0] at E8
  -- the symmetry of the second derivative
  have hsymm : IsSymmSndFDerivAt ℝ Φ p := (hΦ.contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt (by simp)
  -- the jet along the two lines
  set vx : (ℝ × ℝ) × (ℝ × ℝ) := ((1 / 2, 0), (-(1 / 2), 0)) with hvx
  set vy : (ℝ × ℝ) × (ℝ × ℝ) := ((0, 1 / 2), (0, -(1 / 2))) with hvy
  have hlx : (fun x' : ℝ => jetF Φ R (x', 0)) = fun x' => ‖Φ (p + x' • vx)‖ ^ 2 := by
    funext x'
    simp only [jetF]
    congr 3
    ext <;> simp [hpdef, hvx] <;> ring
  have hly : (fun y' : ℝ => jetF Φ R (0, y')) = fun y' => ‖Φ (p + y' • vy)‖ ^ 2 := by
    funext y'
    simp only [jetF]
    congr 3
    ext <;> simp [hpdef, hvy] <;> ring
  have hF0 : jetF Φ R 0 = ‖Φ p‖ ^ 2 := by simp [jetF, hpdef]
  refine ⟨hF0, ?_⟩
  have hlap : lapR (jetF Φ R) 0 = deriv (fun x : ℝ => deriv (fun x' : ℝ => jetF Φ R (x', 0)) x) 0 +
      deriv (fun y : ℝ => deriv (fun y' : ℝ => jetF Φ R (0, y')) y) 0 := by
    simp [lapR]
  rw [hlap, hlx, hly, jets_deriv2_normSq hU hΦ hp vx, jets_deriv2_normSq hU hΦ hp vy, hF0]
  -- linear algebra on the first and second derivatives at `p`
  have hvx' : vx = (1 / 2 : ℝ) • ex1 - (1 / 2 : ℝ) • ex2 := by ext <;> simp [hvx] <;> norm_num
  have hvy' : vy = (1 / 2 : ℝ) • ey1 - (1 / 2 : ℝ) • ey2 := by ext <;> simp [hvy] <;> norm_num
  have hd1x : fderiv ℝ Φ p vx = (1 / 2 : ℂ) * (fderiv ℝ Φ p ex1 - fderiv ℝ Φ p ex2) := by
    rw [hvx', map_sub, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hd1y : fderiv ℝ Φ p vy = (1 / 2 : ℂ) * (fderiv ℝ Φ p ey1 - fderiv ℝ Φ p ey2) := by
    rw [hvy', map_sub, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hS : fderiv ℝ (fderiv ℝ Φ) p vx vx + fderiv ℝ (fderiv ℝ Φ) p vy vy = -(1 / 2 : ℂ) * Φ p := by
    rw [hvx', hvy']
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      Complex.real_smul]
    have k1 : ex1.1.1 = 1 := rfl
    have k2 : ey1.1.1 = 0 := rfl
    have k3 : ex2.1.1 = 0 := rfl
    have k4 : ex2.2.1 = 1 := rfl
    have k5 : ey2.2.1 = 0 := rfl
    have k6 : ey1.2.1 = 0 := rfl
    have E1 := LL1 ex1
    have E2 := LL1 ey1
    have E3 := LL2 ex2
    have E4 := LL2 ey2
    have E5 := LL1 ex2
    have E6 := LL2 ey1
    have s1 := hsymm ex1 ey1
    have s2 := hsymm ex2 ey2
    have s3 := hsymm ex2 ey1
    have s4 := hsymm ex1 ex2
    have s5 := hsymm ey1 ey2
    simp only [k0, k1, k2, k3, k4, k5, k6, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
      add_zero] at E1 E2 E3 E4 E5 E6
    push_cast
    linear_combination (1 / 4 : ℂ) * (E1 + E3 - I * E2 - I * E4 - 2 * E5 + 2 * I * E6 - (p.1.1 : ℂ) * E7 +
      (p.1.1 : ℂ) * E8 - I * s1 - I * s2 + 2 * I * s3 - s4 + s5 +
      (fderiv ℝ (fderiv ℝ Φ) p ey1 ey1 + fderiv ℝ (fderiv ℝ Φ) p ey2 ey2 -
        2 * fderiv ℝ (fderiv ℝ Φ) p ey1 ey2) * Complex.I_sq)
  -- `∂_{r_y}` of the line is `i ∂_{r_x}` (from the two equations at `p`)
  have hB : fderiv ℝ Φ p vy = I * fderiv ℝ Φ p vx := by
    rw [hd1x, hd1y]
    linear_combination (-(1 / 2 : ℂ) * I) * (E7 - E8) + (1 / 2 : ℂ) * (fderiv ℝ Φ p ey1 - fderiv ℝ Φ p ey2) *
      Complex.I_sq
  have hin : inner ℝ (Φ p) (fderiv ℝ (fderiv ℝ Φ) p vx vx) + inner ℝ (Φ p) (fderiv ℝ (fderiv ℝ Φ) p vy vy) =
      -(1 / 2) * ‖Φ p‖ ^ 2 := by
    rw [← inner_add_right, hS, show (-(1 / 2 : ℂ)) * Φ p = (-(1 / 2) : ℝ) • Φ p by
      rw [Complex.real_smul]; push_cast; ring, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hnB : ‖fderiv ℝ Φ p vy‖ ^ 2 = ‖fderiv ℝ Φ p vx‖ ^ 2 := by
    rw [hB, norm_mul, Complex.norm_I, one_mul]
  rw [← hd1x]
  linarith [hin, hnB]

/-- **Lemma 4.3(a)**: "`Let $U\subset\R^2\times\R^2$ be an open neighbourhood of the diagonal, and let $\Phi:U\to\C$ be smooth and of the lowest Landau level in each variable, $(D_{x_1}+\iu D_{y_1})\Phi=(D_{x_2}+\iu D_{y_2})\Phi=0$, where $D_{x_i},D_{y_i}$ are the covariant derivatives \eqref{eq:covariant} in $r_i=(x_i,y_i)$.`"
"`If $\Phi(r_1,r_2)=\Phi(r_2,r_1)$, then $F_R(0)+(\nabla^2F_R)(0)=0$ for every $R$.`" -/
theorem jets_symm {U : Set ((ℝ × ℝ) × (ℝ × ℝ))} (hU : IsOpen U) (hdiag : ∀ R : ℝ × ℝ, (R, R) ∈ U)
    {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ} (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hlll₁ : ∀ p ∈ U, D1x Φ p + I * D1y Φ p = 0) (hlll₂ : ∀ p ∈ U, D2x Φ p + I * D2y Φ p = 0)
    (hsymm : ∀ r₁ r₂ : ℝ × ℝ, (r₁, r₂) ∈ U → (r₂, r₁) ∈ U → Φ (r₁, r₂) = Φ (r₂, r₁)) (R : ℝ × ℝ) :
    jetF Φ R 0 + lapR (jetF Φ R) 0 = 0 := by
  -- block C's proof (L9): `jets_core`, and `∂_{x₁}Φ = ∂_{x₂}Φ` on the diagonal by the symmetry
  have hp := hdiag R
  obtain ⟨-, hcore⟩ := jets_core hU hdiag hΦ hlll₁ hlll₂ R
  rw [hcore]
  have h1 := jets_hasDerivAt_comp hU hΦ hp ((1, 0), (0, 0))
  have h2 := jets_hasDerivAt_comp hU hΦ hp ((0, 0), (1, 0))
  have heq : (fun s : ℝ => Φ ((R, R) + s • (((0, 0), (1, 0)) : (ℝ × ℝ) × (ℝ × ℝ)))) =ᶠ[nhds 0]
      fun s => Φ ((R, R) + s • (((1, 0), (0, 0)) : (ℝ × ℝ) × (ℝ × ℝ))) := by
    filter_upwards [jets_line_mem hU hp ((1, 0), (0, 0)), jets_line_mem hU hp ((0, 0), (1, 0))] with s h1s h2s
    have hsw : ((R, R) + s • (((0, 0), (1, 0)) : (ℝ × ℝ) × (ℝ × ℝ))) =
        (((R, R) + s • (((1, 0), (0, 0)) : (ℝ × ℝ) × (ℝ × ℝ))).2,
          ((R, R) + s • (((1, 0), (0, 0)) : (ℝ × ℝ) × (ℝ × ℝ))).1) := by
      ext <;> simp
    rw [hsw] at h2s ⊢
    exact (hsymm _ _ h1s h2s).symm
  have hA := h1.unique (h2.congr_of_eventuallyEq heq.symm)
  rw [hA, sub_self, mul_zero, norm_zero]
  norm_num

/-- **Lemma 4.3(b)**: "`If $\Phi(r_1,r_2)=-\Phi(r_2,r_1)$, then $F_R(0)=0$ and $(\nabla^2F_R)(0)=4\abs{(D_1\Phi)(R,R)}^2$ for every $R$, where $D_1:=\frac12(D_{x_1}-\iu D_{y_1})$.`"
(the hypotheses on `U` and `Φ` those of (a)). -/
theorem jets_antisymm {U : Set ((ℝ × ℝ) × (ℝ × ℝ))} (hU : IsOpen U) (hdiag : ∀ R : ℝ × ℝ, (R, R) ∈ U)
    {Φ : (ℝ × ℝ) × (ℝ × ℝ) → ℂ} (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hlll₁ : ∀ p ∈ U, D1x Φ p + I * D1y Φ p = 0) (hlll₂ : ∀ p ∈ U, D2x Φ p + I * D2y Φ p = 0)
    (hanti : ∀ r₁ r₂ : ℝ × ℝ, (r₁, r₂) ∈ U → (r₂, r₁) ∈ U → Φ (r₁, r₂) = -Φ (r₂, r₁)) (R : ℝ × ℝ) :
    jetF Φ R 0 = 0 ∧ lapR (jetF Φ R) 0 = 4 * ‖D1 Φ (R, R)‖ ^ 2 := by
  -- block C's proof (L9): `jets_core`, `Φ(R, R) = 0` and `∂_{x₂}Φ = −∂_{x₁}Φ` on the diagonal by the antisymmetry
  have hp := hdiag R
  obtain ⟨hF0, hcore⟩ := jets_core hU hdiag hΦ hlll₁ hlll₂ R
  have hΦ0 : Φ (R, R) = 0 := by
    have h := hanti R R hp hp
    have h2 : (2 : ℂ) * Φ (R, R) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have h1 := jets_hasDerivAt_comp hU hΦ hp ((1, 0), (0, 0))
  have h2 := jets_hasDerivAt_comp hU hΦ hp ((0, 0), (1, 0))
  have heq : (fun s : ℝ => Φ ((R, R) + s • (((0, 0), (1, 0)) : (ℝ × ℝ) × (ℝ × ℝ)))) =ᶠ[nhds 0]
      fun s => -Φ ((R, R) + s • (((1, 0), (0, 0)) : (ℝ × ℝ) × (ℝ × ℝ))) := by
    filter_upwards [jets_line_mem hU hp ((1, 0), (0, 0)), jets_line_mem hU hp ((0, 0), (1, 0))] with s h1s h2s
    have hsw : ((R, R) + s • (((0, 0), (1, 0)) : (ℝ × ℝ) × (ℝ × ℝ))) =
        (((R, R) + s • (((1, 0), (0, 0)) : (ℝ × ℝ) × (ℝ × ℝ))).2,
          ((R, R) + s • (((1, 0), (0, 0)) : (ℝ × ℝ) × (ℝ × ℝ))).1) := by
      ext <;> simp
    rw [hsw] at h2s ⊢
    have h := hanti _ _ h1s h2s
    exact (neg_eq_iff_eq_neg.mpr h).symm
  have hA := h1.neg.unique (h2.congr_of_eventuallyEq heq.symm)
  have hF0' : jetF Φ R 0 = 0 := by rw [hF0, hΦ0, norm_zero]; norm_num
  refine ⟨hF0', ?_⟩
  have hD1 : D1 Φ (R, R) = fderiv ℝ Φ (R, R) ((1, 0), (0, 0)) := by
    have hd := (hΦ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    have hL := hlll₁ (R, R) hp
    unfold D1
    rw [jets_D1x hd, jets_D1y hd] at hL ⊢
    rw [hΦ0] at hL ⊢
    linear_combination (-(1 / 2 : ℂ)) * hL
  rw [hF0', zero_add, ← hA] at hcore
  rw [hcore, hD1]
  congr 2
  rw [show (1 / 2 : ℂ) * (fderiv ℝ Φ (R, R) ((1, 0), (0, 0)) - -fderiv ℝ Φ (R, R) ((1, 0), (0, 0))) =
    fderiv ℝ Φ (R, R) ((1, 0), (0, 0)) by ring]

end HRTorus.Hamiltonian
