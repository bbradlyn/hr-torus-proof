import HRTorus.Assembly.Setting

/-!
# The inputs of the index core for `U = Θ` (`Assembly.Inputs`)

Written by Claude Opus 5.5 (an AI model), 2026-10-25. **The definitions and statements were written first
and reviewed against the paper (the statement phase); proof phase rounds one and two added the proofs and the proof
devices, each section of which is marked as such. No theorem of this module is `sorry`. Round two moved
`factorization_isONegInf` (Lemma 6.13(iii), its text unchanged) after `eps_isONegInf`, because its proof is the core's
quantitative factorization at the orbital structure of each `N` (`inputs_orbOf`).**
The paper: the HR paper, `papers/hr/sections/06-index-theorem.tex` — Proposition 6.10 `prop:clustering`, Definition
6.11 `def:bbdfobjects`, Lemma 6.12 `lem:objects`, Lemma 6.13 `lem:commutation`, the inputs that Corollary 6.15
`cor:Zcommute` and Remark 6.21 `rem:lean` name, and Theorem 6.18 `thm:index` for `U = Θ`; the core is
`HRTorus.IndexCore` (`Setting`, `Orbital`, `Orbital.Inputs`, `index_core_400`).

## The model

* **`U = Θ` throughout** (the brief: Assumption 6.4 is discharged for `U = Θ` by §7, and §6's statements are made for the
  transport unitary the proof of Theorem 8.1 uses). `T_- = −n_{0↑}`, `T_+ = n_{N↑}` (Lemma 7.1(b)). Definition 6.11's
  objects are sequences of operators on `𝓗_N` (`ArgData.KUminus`, …, `ArgData.Mminus φ`, `ArgData.Ttilde`,
  `ArgData.Ominus`), with the dressing at the data's cutoff `ϑ` and gap `γ` (`ArgData.Km` = `K_-`, …) and the clustering
  filter `𝒬(A) = g(ad_{H_N})(A)` of block D (`clusterFilter (gClust γ ζ) (H N) A`, `ArgData.Qf`).
* **Lemma 6.12's table** is stated row by row (`table_*`), each row with its set, its norm bound `C N^m` and its prefactor
  exponent, the norms and exponents of the table for `U = Θ`; the rows of the unitaries and of `𝒬` uniformly in
  `φ ∈ [0, 2π]` (one set of constants for every `φ`).
* **Lemma 6.13(ii)'s sixteen pairs** are `ArgData.sepPairs` (in the order and orientation of the core's `Orbital.Inputs`),
  each `O(N^{−∞})` in block D's sense (`IsONegInf`, the parameter type `Unit`).
* **The bridge to the core.** At each `N ∈ 𝒩` the core's `Orbital (FockSpace (𝕋_N))` is `orbOf D N hN h`: the data of the
  setting (`H_N`, `Π^{𝐧_N}`, `n_j = n_{j↑}`, `Θ`, the quarters, `γ`, `Δ`, `a = E_1`, `b = E_p`, `J_±`, `Ŵ_γ`, `g`), its
  proof fields from block A's `orbitalFit_spin` and from `OrbObligations D N` — a `Prop` structure collecting the facts
  that are theorems to be proved (Lemma 6.6(i), the bridge of Assumption 6.3, Lemma 5.9, …); `obligations` states that
  they hold for every `N ∈ 𝒩`. `orbOf_objects` identifies the core's derived objects (`K_±`, `P`, `𝒬`, `𝓜_±`, …) with
  the paper's under `toCLM`, through the bridges `toCLM_spectralSum` (block D's spectral sums are the core's).
* **The explicit `ε(N)` and `M(N)`**: `ArgData.eps N` is the largest of the twenty quantities of `Orbital.Inputs` (the
  sixteen separated commutators and the four clustering commutators, the latter with their supremum over
  `φ ∈ [0, 2π]`), so that `Orbital.Inputs (eps N) (Mb N)` holds by definition once the identifications are proved; its
  content is `eps_isONegInf` (`O(N^{−∞})` for real sequences, `IsONegInfR`). `ArgData.Mb N = (1 + 4πC_h‖W_γ‖₁) N²` is the
  polynomial bound of Lemma 6.6(i) and Lemma 6.8 (`‖n_0‖ = 1`, `‖K_-‖ ≤ ‖W_γ‖₁ · 4πC_h N²`). The limit step is
  `eventually_small`: `400 p (M(N) + 1) √ε(N) < 1/4` for all large `N ∈ 𝒩`, `p` being independent of `N`.
-/

open scoped InnerProductSpace Matrix ENNReal Real ComplexConjugate
open Complex (I)
open MeasureTheory Filter

noncomputable section

namespace HRTorus.Assembly

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian HRTorus.Locality
open HRTorus.IndexCore (bandΓ quarterMinus quarterMid quarterPlus quarters_partition)
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op IsEven CAR Alg)

variable {η : ℝ → ℝ} {δ₀ : ℝ}

/-! ## `O(N^{−∞})` for real sequences -/

/-- "`$\Onf$, $\eqN$ & bounded by $C_kN^{-k}$ for every $k$`" (the notation table), for a real sequence on a set `𝒩` of
indices. -/
def IsONegInfR (s : Set ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ N ∈ s, |a N| ≤ C * (N : ℝ) ^ (-(k : ℝ))

/-! ## Definition 6.11 for `U = Θ`, and the clustering filter -/

namespace ArgData

variable (D : ArgData η δ₀)

/-- `K_-` at the data's cutoff and gap (Definition 6.5). -/
def Km (N : ℕ) : FockOp (D.T N) := D.Kminus D.ϑ D.γ N

/-- `K_+` at the data's cutoff and gap. -/
def Kp (N : ℕ) : FockOp (D.T N) := D.Kplus D.ϑ D.γ N

/-- `K` at the data's cutoff and gap. -/
def Kf (N : ℕ) : FockOp (D.T N) := D.Kfull D.ϑ D.γ N

/-- `Q̄` at the data's cutoff and gap. -/
def Qb (N : ℕ) : FockOp (D.T N) := D.Qbar D.ϑ D.γ N

/-- Lemma 7.1(b): "`With $T_-:=-n_{0\up}$ and $T_+:=n_{N\up}$`" — `T_-`. -/
def Tminus (N : ℕ) : FockOp (D.T N) := -njs (D.T N) 0 .up

/-- Lemma 7.1(b): `T_+ = n_{N↑}`. -/
def Tplus (N : ℕ) : FockOp (D.T N) := njs (D.T N) (N : ZMod (D.T N).Nφ) .up

/-- **Definition 6.11**: "`K^U_\pm:=U^*K_\pm U`" for `U = Θ` — `K^U_-`. -/
def KUminus (N : ℕ) : FockOp (D.T N) := (Θ (D.T N))ᴴ * D.Km N * Θ (D.T N)

/-- **Definition 6.11**: `K^U_+`. -/
def KUplus (N : ℕ) : FockOp (D.T N) := (Θ (D.T N))ᴴ * D.Kp N * Θ (D.T N)

/-- **Definition 6.11**: "`\Qb_\pm:=Q_\pm-K_\pm`" — `Q̄_-`. -/
def QbarMinus (N : ℕ) : FockOp (D.T N) := D.Qminus N - D.Km N

/-- **Definition 6.11**: `Q̄_+`. -/
def QbarPlus (N : ℕ) : FockOp (D.T N) := D.Qplus N - D.Kp N

/-- **Definition 6.11**: "`\Qb^U_\pm:=Q_\pm+T_\pm-K^U_\pm`" — `Q̄^U_-`. -/
def QbarUMinus (N : ℕ) : FockOp (D.T N) := D.Qminus N + D.Tminus N - D.KUminus N

/-- **Definition 6.11**: `Q̄^U_+`. -/
def QbarUPlus (N : ℕ) : FockOp (D.T N) := D.Qplus N + D.Tplus N - D.KUplus N

/-- **Definition 6.11**: "`\Qb^U:=U^*\Qb U`". -/
def QbarU (N : ℕ) : FockOp (D.T N) := (Θ (D.T N))ᴴ * D.Qb N * Θ (D.T N)

/-- **Definition 6.11**: "`\mathcal M(\varphi):=U^*e^{\iu\varphi\Qb}Ue^{-\iu\varphi\Qb}=e^{\iu\varphi\Qb^U}e^{-\iu\varphi\Qb}`"
(the second form). -/
def Mfull (φ : ℝ) (N : ℕ) : FockOp (D.T N) :=
  NormedSpace.exp ((I * (φ : ℂ)) • D.QbarU N) * NormedSpace.exp ((-(I * (φ : ℂ))) • D.Qb N)

/-- **Definition 6.11**: "`\mathcal M_\pm(\varphi):=e^{\iu\varphi\Qb^U_\pm}e^{-\iu\varphi\Qb_\pm}`" — `𝓜_-(φ)`. -/
def Mminus (φ : ℝ) (N : ℕ) : FockOp (D.T N) :=
  NormedSpace.exp ((I * (φ : ℂ)) • D.QbarUMinus N) * NormedSpace.exp ((-(I * (φ : ℂ))) • D.QbarMinus N)

/-- **Definition 6.11**: `𝓜_+(φ)`. -/
def Mplus (φ : ℝ) (N : ℕ) : FockOp (D.T N) :=
  NormedSpace.exp ((I * (φ : ℂ)) • D.QbarUPlus N) * NormedSpace.exp ((-(I * (φ : ℂ))) • D.QbarPlus N)

/-- **Definition 6.11**: "`\Tt:=\Qb^U_--\Qb_-=T_--K^U_-+K_-`" (the last form). -/
def Ttilde (N : ℕ) : FockOp (D.T N) := D.Tminus N - D.KUminus N + D.Km N

/-- Lemma 6.12: `e^{2πi Q̄_-}`. -/
def Ominus (N : ℕ) : FockOp (D.T N) := NormedSpace.exp ((2 * π * I : ℂ) • D.QbarMinus N)

/-- Lemma 6.12: `e^{2πi Q̄_+}`. -/
def Oplus (N : ℕ) : FockOp (D.T N) := NormedSpace.exp ((2 * π * I : ℂ) • D.QbarPlus N)

/-- Proposition 6.10: "`let $\Qf$ be the clustering filter of Definition~\ref{def:filters} for the $\Delta$ and $\gamma$ of the assumption`"
— block D's `clusterFilter` of `H_N` with `g = gClust γ ζ`. -/
def Qf (N : ℕ) (A : FockOp (D.T N)) : FockOp (D.T N) := clusterFilter (gClust D.γ D.ζ) (D.H N) A

/-! ## The sixteen separated pairs, and the explicit `ε(N)`, `M(N)` -/

/-- **Lemma 6.13(ii)** for `U = Θ`: "`For $U=\Theta$ these are sixteen pairs.`" — in the order and orientation of the
core's `Orbital.Inputs`: class 1 `(K_-, Q_m)`, `(K^U_-, Q_m)`, `(K_+, Q_m)`, `(K^U_+, Q_m)`; class 2 `(Q_-, K_+)`, `(Q_-, K^U_+)`,
`(K_-, Q_+)`, `(K^U_-, Q_+)`; class 3 `(T_-, K_+)`, `(T_-, K^U_+)`, `(K_-, T_+)`, `(K_-, K_+)`, `(K_-, K^U_+)`, `(K^U_-, T_+)`,
`(K^U_-, K_+)`, `(K^U_-, K^U_+)`. -/
def sepPairs : Fin 16 → ((N : ℕ) → FockOp (D.T N)) × ((N : ℕ) → FockOp (D.T N)) :=
  ![(D.Km, D.Qmid), (D.KUminus, D.Qmid), (D.Kp, D.Qmid), (D.KUplus, D.Qmid),
    (D.Qminus, D.Kp), (D.Qminus, D.KUplus), (D.Km, D.Qplus), (D.KUminus, D.Qplus),
    (D.Tminus, D.Kp), (D.Tminus, D.KUplus), (D.Km, D.Tplus), (D.Km, D.Kp), (D.Km, D.KUplus),
    (D.KUminus, D.Tplus), (D.KUminus, D.Kp), (D.KUminus, D.KUplus)]

/-- The commutator of the `i`-th separated pair. -/
def sepComm (i : Fin 16) (N : ℕ) : FockOp (D.T N) :=
  (D.sepPairs i).1 N * (D.sepPairs i).2 N - (D.sepPairs i).2 N * (D.sepPairs i).1 N

/-- The largest of the sixteen separated commutators at `N`. -/
def epsSep (N : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : Fin 16 => ‖toCLM (D.T N) (D.sepComm i N)‖

/-- The four clustering quantities of the core's `Orbital.Inputs` at `N` (Corollary 6.15's inputs), the first two
with their supremum over `φ ∈ [0, 2π]`: `‖[𝒬(𝓜_+(φ)), 𝓜_-(φ)]‖`, `‖[𝒬(𝓜_+(φ)^*), 𝓜_-(φ)^*]‖`,
`‖[𝒬(e^{2πiQ̄_+}), e^{2πiQ̄_-}]‖`, `‖[𝒬((e^{2πiQ̄_+})^*), (e^{2πiQ̄_-})^*]‖`. -/
def epsClu (N : ℕ) : ℝ :=
  max
    (max (⨆ φ : Set.Icc (0 : ℝ) (2 * π),
        ‖toCLM (D.T N) (D.Qf N (D.Mplus φ N) * D.Mminus φ N - D.Mminus φ N * D.Qf N (D.Mplus φ N))‖)
      (⨆ φ : Set.Icc (0 : ℝ) (2 * π),
        ‖toCLM (D.T N) (D.Qf N ((D.Mplus φ N)ᴴ) * (D.Mminus φ N)ᴴ - (D.Mminus φ N)ᴴ * D.Qf N ((D.Mplus φ N)ᴴ))‖))
    (max ‖toCLM (D.T N) (D.Qf N (D.Oplus N) * D.Ominus N - D.Ominus N * D.Qf N (D.Oplus N))‖
      ‖toCLM (D.T N) (D.Qf N ((D.Oplus N)ᴴ) * (D.Ominus N)ᴴ - (D.Ominus N)ᴴ * D.Qf N ((D.Oplus N)ᴴ))‖)

/-- **The explicit `ε(N)`**: the largest of the twenty `ε`-quantities of the core's `Orbital.Inputs` at `N`. -/
def eps (N : ℕ) : ℝ := max (D.epsSep N) (D.epsClu N)

/-- **The explicit `M(N)`**: `(1 + 4πC_h‖W_γ‖₁) N²` (Lemma 6.6(i) and Lemma 6.8; `‖W_γ‖₁ = M_0(W_γ)`). -/
def Mb (N : ℕ) : ℝ := (1 + 4 * π * D.d.Ch * moment (Wfilt D.ϑ D.γ) 0) * (N : ℝ) ^ 2

end ArgData

/-! ## The orbital structure of the core at each `N` -/

/-- The facts at `N` that the core's `Orbital` needs beyond its data and block A's `orbitalFit_spin`: (H1)'s
self-adjointness and sector preservation of `H_N`, `[Θ, H_N] = 0` ((H2)), Assumption 6.3 in the core's form (the
bridge `gap_of_secEig`), Lemma 6.6(i) for `J_±`, Lemma 5.9's `Ŵ_γ(ω) = i/ω` for `|ω| ≥ γ` and its conjugation symmetry,
and the two properties of `g` (Definition 5.8). Each is a theorem to be proved (`obligations`). -/
structure OrbObligations (D : ArgData η δ₀) (N : ℕ) : Prop where
  H_sa : IsSelfAdjoint (toCLM (D.T N) (D.H N))
  Psec_H : Commute (toCLM (D.T N) (Psec (D.T N) (D.nn N))) (toCLM (D.T N) (D.H N))
  Θ_H : Commute (toCLM (D.T N) (Θ (D.T N))) (toCLM (D.T N) (D.H N))
  Δ_nonneg : 0 ≤ D.Δ
  Δ_lt_γ : D.Δ < D.γ
  width : D.E N D.p - D.E N 1 ≤ D.Δ
  gap : ∀ (μ : ℝ) (v : FockSpace (D.T N)), v ≠ 0 → toCLM (D.T N) (Psec (D.T N) (D.nn N)) v = v →
    toCLM (D.T N) (D.H N) v = (μ : ℂ) • v → μ ∈ Set.Icc (D.E N 1) (D.E N D.p) ∨ D.E N D.p + D.γ ≤ μ
  Jminus_sa : IsSelfAdjoint (toCLM (D.T N) (D.Jminus N))
  Jplus_sa : IsSelfAdjoint (toCLM (D.T N) (D.Jplus N))
  Psec_Jminus : Commute (toCLM (D.T N) (Psec (D.T N) (D.nn N))) (toCLM (D.T N) (D.Jminus N))
  Psec_Jplus : Commute (toCLM (D.T N) (Psec (D.T N) (D.nn N))) (toCLM (D.T N) (D.Jplus N))
  current_split : toCLM (D.T N) (D.Jminus N) + toCLM (D.T N) (D.Jplus N) =
    I • ⁅toCLM (D.T N) (D.H N), ∑ j ∈ bandΓ (D.T N).Nφ N, toCLM (D.T N) (njs (D.T N) j .up)⁆
  W_eq : ∀ ω : ℝ, D.γ ≤ |ω| → What D.ϑ D.γ ω = I / ω
  W_conj : ∀ ω : ℝ, What D.ϑ D.γ (-ω) = conj (What D.ϑ D.γ ω)
  g_zero : ∀ ω : ℝ, -D.Δ ≤ ω → ((gClust D.γ D.ζ ω : ℝ) : ℂ) = 0
  g_one : ∀ ω : ℝ, ω ≤ -D.γ → ((gClust D.γ D.ζ ω : ℝ) : ℂ) = 1

/-- **The core's orbital structure for the data at `N ∈ 𝒩`** (Section 7's `Orbital`): `H = H_N`, `Π = Π^{𝐧_N}`,
`N_φ = 2N`, the band length `N`, `n_j = n_{j↑}`, `nup = n_{↑,N}`, the quarters of Setting 6.1, `γ`, `Δ`, `a = E_1`,
`b = E_p`, `Θ`, `J_±`, `W = Ŵ_γ`, `g`. -/
def orbOf (D : ArgData η δ₀) (N : ℕ) (hN : N ∈ D.Ts.idx) (h : OrbObligations D N) :
    IndexCore.Orbital (FockSpace (D.T N)) where
  H := toCLM (D.T N) (D.H N)
  H_sa := h.H_sa
  Psec := toCLM (D.T N) (Psec (D.T N) (D.nn N))
  Psec_proj := (orbitalFit_spin (D.T N) .up (D.nn N)).Psec_proj
  Psec_H := h.Psec_H
  Nφ := (D.T N).Nφ
  N := N
  N_le_Nφ := by
    show N ≤ 2 * (D.Ts.T N).N
    rw [D.Ts.T_N N hN]
    omega
  n := fun j => toCLM (D.T N) (njs (D.T N) j .up)
  n_sa := (orbitalFit_spin (D.T N) .up (D.nn N)).n_sa
  n_comm := (orbitalFit_spin (D.T N) .up (D.nn N)).n_comm
  exp_n := (orbitalFit_spin (D.T N) .up (D.nn N)).exp_n
  Psec_n := (orbitalFit_spin (D.T N) .up (D.nn N)).Psec_n
  nup := ((D.nn N).1 : ℕ)
  sum_n_Psec := by simpa using (orbitalFit_spin (D.T N) .up (D.nn N)).sum_n_Psec
  Γminus := quarterMinus (D.T N).Nφ N
  Γmid := quarterMid (D.T N).Nφ N
  Γplus := quarterPlus (D.T N).Nφ N
  disjoint_minus_mid := (quarters_partition (by
    show N ≤ 2 * (D.Ts.T N).N
    rw [D.Ts.T_N N hN]
    omega)).1
  disjoint_minus_plus := (quarters_partition (by
    show N ≤ 2 * (D.Ts.T N).N
    rw [D.Ts.T_N N hN]
    omega)).2.1
  disjoint_mid_plus := (quarters_partition (by
    show N ≤ 2 * (D.Ts.T N).N
    rw [D.Ts.T_N N hN]
    omega)).2.2.1
  bands_union := (quarters_partition (by
    show N ≤ 2 * (D.Ts.T N).N
    rw [D.Ts.T_N N hN]
    omega)).2.2.2
  γ := D.γ
  Δ := D.Δ
  a := D.E N 1
  b := D.E N D.p
  Δ_nonneg := h.Δ_nonneg
  Δ_lt_γ := h.Δ_lt_γ
  width := h.width
  gap := h.gap
  Θ := toCLM (D.T N) (Θ (D.T N))
  Θ_unitary := (orbitalFit_spin (D.T N) .up (D.nn N)).Θ_unitary
  Psec_Θ := (orbitalFit_spin (D.T N) .up (D.nn N)).Psec_Θ
  Θ_H := h.Θ_H
  Θ_n := (orbitalFit_spin (D.T N) .up (D.nn N)).Θ_n
  Jminus := toCLM (D.T N) (D.Jminus N)
  Jplus := toCLM (D.T N) (D.Jplus N)
  Jminus_sa := h.Jminus_sa
  Jplus_sa := h.Jplus_sa
  Psec_Jminus := h.Psec_Jminus
  Psec_Jplus := h.Psec_Jplus
  current_split := h.current_split
  W := What D.ϑ D.γ
  W_eq := h.W_eq
  W_conj := h.W_conj
  g := fun ω => ((gClust D.γ D.ζ ω : ℝ) : ℂ)
  g_zero := h.g_zero
  g_one := h.g_one

/-! ## Statements -/

/-! ### The bridges between block D's spectral sums and the core's

The proofs are the devices of `Assembly.Setting` (`specFinset_eq_spec_dev`, `toCLM_specProj_dev`,
`toCLM_spectralSum_dev`), placed there for Lemma 6.7. -/

/-- Block D's spectrum `specFinset H` is the core's `spec` of `toCLM H`. -/
theorem specFinset_eq_spec {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hH' : IsSelfAdjoint (toCLM T H)) :
    specFinset H = IndexCore.spec (toCLM T H) hH' :=
  specFinset_eq_spec_dev hH hH'

/-- Block D's spectral projection `1_{E}(H)` is the core's `eigProj` under `toCLM`. -/
theorem toCLM_specProj {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hH' : IsSelfAdjoint (toCLM T H))
    (E : ℝ) : toCLM T (Locality.specProj H E) = IndexCore.eigProj (toCLM T H) hH' E :=
  toCLM_specProj_dev hH hH' E

/-- Block D's double spectral sums are the core's `spectralSum` under `toCLM`. -/
theorem toCLM_spectralSum {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hH' : IsSelfAdjoint (toCLM T H))
    (f : ℝ → ℝ → ℂ) (A : FockOp T) :
    toCLM T (∑ E ∈ specFinset H, ∑ E' ∈ specFinset H, f E E' • (Locality.specProj H E * A * Locality.specProj H E')) =
      IndexCore.spectralSum (toCLM T H) hH' f (toCLM T A) :=
  toCLM_spectralSum_dev hH hH' f A

/-- The core's trace `trc` of `toCLM A` is the matrix trace of `A`. -/
theorem trc_toCLM {T : Torus} (A : FockOp T) : IndexCore.trc (toCLM T A) = Matrix.trace A := by
  have e : ((toCLM T A : FockSpace T →L[ℂ] FockSpace T) : FockSpace T →ₗ[ℂ] FockSpace T) =
      Matrix.toLin (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis
        (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis A := rfl
  unfold IndexCore.trc
  rw [e, LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis,
    LinearMap.toMatrix_toLin]

/-! ### Proposition 6.10 (in-sector clustering) -/

/-! #### Proof device for Proposition 6.10(i)–(ii) (phase (b), round two; not a statement of the paper)

The core's `Setting` of valid data at `N` with `U = 1`, `T_± = 0` (as `Assembly.Setting`'s `coreSetting_dev`) but the
data's own `Ŵ_γ` and `g` (Definition 5.8, from `D.Valid`), so that its `𝒬` and `P` are the paper's (`toCLM_spectralSum`,
`toCLM_cfc_indicator`) and the core's `Qf_mul_P`, `P_mul_Qf`, `compression_eq`, `norm_clustering_inner`,
`norm_clustering_vec` apply; Proposition 6.10(i)–(ii) uses neither the transport nor (H2). -/

section ClusterDevices

/-- The core's `Setting` of valid data at `N` (the section docstring). -/
def coreSettingV_dev (D : ArgData η δ₀) (hD : D.Valid) {N : ℕ} (hN : N ∈ D.Ts.idx) :
    IndexCore.Setting (FockSpace (D.T N)) where
  H := toCLM (D.T N) (D.H N)
  H_sa := isSelfAdjoint_toCLM_dev (D.d.H_isSelfAdjoint N hN)
  Psec := toCLM (D.T N) (Psec (D.T N) (D.nn N))
  Psec_proj := (orbitalFit_spin (D.T N) .up (D.nn N)).Psec_proj
  Psec_H := commute_Psec_toCLM_dev _ (H_isSectorPreserving_dev D.toIxSetting hN)
  Qminus := toCLM (D.T N) (D.Qminus N)
  Qmid := toCLM (D.T N) (D.Qmid N)
  Qplus := toCLM (D.T N) (D.Qplus N)
  Qminus_sa := isSelfAdjoint_toCLM_dev (Qband_isSelfAdjoint _ _)
  Qmid_sa := isSelfAdjoint_toCLM_dev (Qband_isSelfAdjoint _ _)
  Qplus_sa := isSelfAdjoint_toCLM_dev (Qband_isSelfAdjoint _ _)
  comm_Qminus_Qmid := commute_toCLM_dev (commute_Qband _ _ _)
  comm_Qmid_Qplus := commute_toCLM_dev (commute_Qband _ _ _)
  comm_Qminus_Qplus := commute_toCLM_dev (commute_Qband _ _ _)
  exp_Qminus := exp_toCLM_Qband_dev _ _
  exp_Qmid := exp_toCLM_Qband_dev _ _
  exp_Qplus := exp_toCLM_Qband_dev _ _
  Psec_Qminus := commute_Psec_toCLM_dev _ (Qband_isSectorPreserving _ _)
  Psec_Qmid := commute_Psec_toCLM_dev _ (Qband_isSectorPreserving _ _)
  Psec_Qplus := commute_Psec_toCLM_dev _ (Qband_isSectorPreserving _ _)
  γ := D.γ
  Δ := D.Δ
  a := D.E N 1
  b := D.E N D.p
  Δ_nonneg := hD.gap.Δ_nonneg
  Δ_lt_γ := by linarith [hD.gap.Δ_nonneg, hD.gap.two_mul_Δ_lt]
  width := hD.gap.spread N hN
  gap := fun μ v hv0 hv hHv => gap_of_secEig (D.d.H_isSelfAdjoint N hN)
    (H_isSectorPreserving_dev D.toIxSetting hN) (by linarith [hD.gap.Δ_nonneg, hD.gap.two_mul_Δ_lt])
    (hD.gap.gap N hN) μ v hv0 hv hHv
  U := 1
  U_unitary := one_mem _
  Psec_U := Commute.one_right _
  Tminus := 0
  Tplus := 0
  Tminus_sa := IsSelfAdjoint.zero _
  Tplus_sa := IsSelfAdjoint.zero _
  Psec_Tminus := Commute.zero_right _
  Psec_Tplus := Commute.zero_right _
  transport := by simp
  Jminus := toCLM (D.T N) (D.Jminus N)
  Jplus := toCLM (D.T N) (D.Jplus N)
  Jminus_sa := isSelfAdjoint_toCLM_dev (J_isSelfAdjoint D.toIxSetting N hN).1
  Jplus_sa := isSelfAdjoint_toCLM_dev (J_isSelfAdjoint D.toIxSetting N hN).2.2.1
  Psec_Jminus := commute_Psec_toCLM_dev _ (J_isSelfAdjoint D.toIxSetting N hN).2.1
  Psec_Jplus := commute_Psec_toCLM_dev _ (J_isSelfAdjoint D.toIxSetting N hN).2.2.2
  current_split := by
    rw [← toCLM_add_dev, Jminus_add_Jplus D.toIxSetting N hN, ← toCLM_add_dev, ← toCLM_add_dev,
      ← Q_eq_add_dev D.toIxSetting hN, toCLM_smul_dev, toCLM_sub', toCLM_mul', toCLM_mul', Ring.lie_def]
  W := What D.ϑ D.γ
  W_eq := fun ω hω => What_eq_dev hD.cutoff (by linarith [hD.gap.Δ_nonneg, hD.gap.two_mul_Δ_lt]) ω hω
  W_conj := fun ω => What_conj_dev hD.cutoff D.γ ω
  g := fun ω => ((gClust D.γ D.ζ ω : ℝ) : ℂ)
  g_zero := fun ω hω => by rw [gClust_eq_zero hD.clust hω, Complex.ofReal_zero]
  g_one := fun ω hω => by rw [gClust_eq_one hD.clust (by linarith [hD.gap.Δ_nonneg]), Complex.ofReal_one]

theorem coreSettingV_P_dev (D : ArgData η δ₀) (hD : D.Valid) {N : ℕ} (hN : N ∈ D.Ts.idx) :
    (coreSettingV_dev D hD hN).P = toCLM (D.T N) (D.P N) := by
  unfold ArgData.P
  rw [toCLM_mul', toCLM_cfc_indicator (D.d.H_isSelfAdjoint N hN) (isSelfAdjoint_toCLM_dev (D.d.H_isSelfAdjoint N hN))]
  rfl

theorem coreSettingV_Qf_dev (D : ArgData η δ₀) (hD : D.Valid) {N : ℕ} (hN : N ∈ D.Ts.idx) (A : FockOp (D.T N)) :
    (coreSettingV_dev D hD hN).Qf (toCLM (D.T N) A) = toCLM (D.T N) (D.Qf N A) := by
  unfold ArgData.Qf clusterFilter
  rw [toCLM_spectralSum_dev (D.d.H_isSelfAdjoint N hN) (isSelfAdjoint_toCLM_dev (D.d.H_isSelfAdjoint N hN))]
  rfl

end ClusterDevices

/-- **Proposition 6.10(i)**: "`If $A$ is sector-preserving, then $\Qf(A)P=0$ and $P\Qf(A)=PA(\one-P)$.`" -/
theorem Qf_mul_P (D : ArgData η δ₀) (hD : D.Valid) :
    ∀ N ∈ D.Ts.idx, ∀ A : FockOp (D.T N), IsSectorPreserving (D.T N) A →
      D.Qf N A * D.P N = 0 ∧ D.P N * D.Qf N A = D.P N * A * (1 - D.P N) := by
  intro N hN A hA
  have hc : Commute (coreSettingV_dev D hD hN).Psec (toCLM (D.T N) A) := commute_Psec_toCLM_dev _ hA
  have h1 := (coreSettingV_dev D hD hN).Qf_mul_P hc
  have h2 := (coreSettingV_dev D hD hN).P_mul_Qf hc
  rw [coreSettingV_Qf_dev, coreSettingV_P_dev] at h1 h2
  refine ⟨toCLM_injective_dev _ ?_, toCLM_injective_dev _ ?_⟩
  · rw [toCLM_mul', h1, toCLM_zero_dev]
  · rw [toCLM_mul', h2, toCLM_mul', toCLM_mul', toCLM_sub', toCLM_one_dev]

/-- **Proposition 6.10(ii)**: "`If $A$ is sector-preserving and $B$ is any operator, then $PA(\one-P)BP=P[\Qf(A),B]P$; in particular, for every unit vector $\Omega\in\ran P$,`"
"`\abs{\ip\Omega{AB\Omega}-\ip\Omega{APB\Omega}}\le\norm{[\Qf(A),B]},\qquad\norm{PAB\Omega-PAPB\Omega}\le\norm{[\Qf(A),B]}.`" -/
theorem P_mul_comm_mul_P (D : ArgData η δ₀) (hD : D.Valid) :
    ∀ N ∈ D.Ts.idx, ∀ A B : FockOp (D.T N), IsSectorPreserving (D.T N) A →
      D.P N * A * (1 - D.P N) * B * D.P N = D.P N * (D.Qf N A * B - B * D.Qf N A) * D.P N ∧
        ∀ Ω : FockSpace (D.T N), ‖Ω‖ = 1 → toCLM (D.T N) (D.P N) Ω = Ω →
          ‖⟪Ω, toCLM (D.T N) (A * B) Ω⟫_ℂ - ⟪Ω, toCLM (D.T N) (A * D.P N * B) Ω⟫_ℂ‖ ≤
              ‖toCLM (D.T N) (D.Qf N A * B - B * D.Qf N A)‖ ∧
            ‖toCLM (D.T N) (D.P N * A * B) Ω - toCLM (D.T N) (D.P N * A * D.P N * B) Ω‖ ≤
              ‖toCLM (D.T N) (D.Qf N A * B - B * D.Qf N A)‖ := by
  intro N hN A B hA
  have hc : Commute (coreSettingV_dev D hD hN).Psec (toCLM (D.T N) A) := commute_Psec_toCLM_dev _ hA
  have hlie : ⁅(coreSettingV_dev D hD hN).Qf (toCLM (D.T N) A), toCLM (D.T N) B⁆ =
      toCLM (D.T N) (D.Qf N A * B - B * D.Qf N A) := by
    rw [coreSettingV_Qf_dev, Ring.lie_def, toCLM_sub', toCLM_mul', toCLM_mul']
  have hP := coreSettingV_P_dev D hD hN
  refine ⟨?_, fun Ω h1 hΩ => ⟨?_, ?_⟩⟩
  · have h := (coreSettingV_dev D hD hN).compression_eq hc (toCLM (D.T N) B)
    rw [hlie, hP] at h
    apply toCLM_injective_dev
    simp only [toCLM_mul', toCLM_sub', toCLM_one_dev]
    rw [h, toCLM_sub', toCLM_mul', toCLM_mul']
  · have hΩ' : (coreSettingV_dev D hD hN).P Ω = Ω := by rw [hP]; exact hΩ
    have h := (coreSettingV_dev D hD hN).norm_clustering_inner hc (toCLM (D.T N) B) hΩ' h1
    rw [hlie, hP] at h
    simpa [toCLM_mul', mul_apply_eq_comp] using h
  · have hΩ' : (coreSettingV_dev D hD hN).P Ω = Ω := by rw [hP]; exact hΩ
    have h := (coreSettingV_dev D hD hN).norm_clustering_vec hc (toCLM (D.T N) B) hΩ' h1
    rw [hlie, hP] at h
    simpa [toCLM_mul', mul_apply_eq_comp] using h

/-- **Proposition 6.10(iii)**: "`If moreover $A\in\AS_X$ and $B\in\AS_Y$ are even, with $\norm{A_N},\norm{B_N}\le CN^{m}$, $\abs{X_N}\le CN^{m}$ and $d(X_N,Y_N)\ge c\sqrt N-C$, then the right-hand sides in (ii) are $\Onf$.`"
— for families depending on a parameter, with one prefactor exponent and one set of constants each (block B's
uniformity, the form the proofs of Lemmas 6.12 and 6.14 use; the parameter-free statement is `P = Unit`). -/
theorem clustering_isONegInf (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid)
    {P : Type*} (A B : P → (N : ℕ) → FockOp (D.T N)) (X Y : P → (N : ℕ) → Finset (Slot δ₀ (D.T N)))
    {C m c mA mB : ℝ} {CA CB : ℕ → ℝ} (hc : 0 < c)
    (hAsp : ∀ p, ∀ N ∈ D.Ts.idx, IsSectorPreserving (D.T N) (A p N))
    (hAe : ∀ p, ∀ N ∈ D.Ts.idx, IsEven (A p N)) (hBe : ∀ p, ∀ N ∈ D.Ts.idx, IsEven (B p N))
    (hAS : ∀ p, ASBound η δ₀ D.Ts (X p) (A p) mA CA) (hBS : ∀ p, ASBound η δ₀ D.Ts (Y p) (B p) mB CB)
    (hAn : ∀ p, ∀ N ∈ D.Ts.idx, ‖toCLM (D.T N) (A p N)‖ ≤ C * (N : ℝ) ^ m)
    (hBn : ∀ p, ∀ N ∈ D.Ts.idx, ‖toCLM (D.T N) (B p N)‖ ≤ C * (N : ℝ) ^ m)
    (hX : ∀ p, ∀ N ∈ D.Ts.idx, ((X p N).card : ℝ) ≤ C * (N : ℝ) ^ m)
    (hd : ∀ p, ∀ N ∈ D.Ts.idx, ENNReal.ofReal (c * Real.sqrt N - C) ≤ slotSetDist (X p N) (Y p N)) :
    IsONegInf D.Ts fun p N => D.Qf N (A p N) * B p N - B p N * D.Qf N (A p N) := by
  obtain ⟨mq, hmq⟩ : ∃ mq : ℝ, mq = max m 0 := ⟨_, rfl⟩
  have hmq0 : 0 ≤ mq := by rw [hmq]; exact le_max_right _ _
  have hmm : m ≤ mq := by rw [hmq]; exact le_max_left _ _
  have hNpow : ∀ N ∈ D.Ts.idx, ∀ {a b : ℝ}, a ≤ b → (N : ℝ) ^ a ≤ (N : ℝ) ^ b := fun N hN a b hab =>
    Real.rpow_le_rpow_of_exponent_le (one_le_of_mem_idx D.Ts hN) hab
  have hNnn : ∀ N ∈ D.Ts.idx, ∀ a : ℝ, 0 ≤ (N : ℝ) ^ a := fun N hN a =>
    Real.rpow_nonneg (by linarith [one_le_of_mem_idx D.Ts hN]) a
  have hup : ∀ N ∈ D.Ts.idx, ∀ x : ℝ, x ≤ C * (N : ℝ) ^ m → x ≤ |C| * (N : ℝ) ^ mq := fun N hN x hx =>
    hx.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (hNnn N hN m)).trans
      (mul_le_mul_of_nonneg_left (hNpow N hN hmm) (abs_nonneg C)))
  obtain ⟨C'k, C', hC'⟩ := almostSupported_clusterFilter hδ₀ hD.clust |C| mA mq mq hmq0 CA D.d.Ch D.d.CH
  have hQ := fun p => hC' η hη D.Ts D.H D.d rfl rfl (X p) (A p) (hAe p) (hAS p)
    (fun N hN => hup N hN _ (hAn p N hN)) (fun N hN => hup N hN _ (hX p N hN))
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max (1 + max mA mq + mq) (1 + mq) := ⟨_, rfl⟩
  have hM1 : 1 + max mA mq + mq ≤ M := by rw [hM]; exact le_max_left _ _
  have hM2 : 1 + mq ≤ M := by rw [hM]; exact le_max_right _ _
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = max (|C'| + |C|) (|C| + |c|) := ⟨_, rfl⟩
  have hCb1 : |C'| + |C| ≤ Cb := by rw [hCb]; exact le_max_left _ _
  have hCb2 : |C| ≤ Cb := by rw [hCb]; linarith [le_max_left (|C'| + |C|) (|C| + |c|), abs_nonneg C']
  obtain ⟨Cr, hCr⟩ := bookkeeping_comm hc Cb (max M mB) (le_max_of_le_left hM0) C'k CB
  intro k
  refine ⟨Cr k, fun p N hN => ?_⟩
  refine hCr η δ₀ hη hδ₀ D.Ts D.cstar D.Lx_ge P X Y (fun p N => D.Qf N (A p N)) B
    (fun p N hN => ⟨?_, hBe p N hN⟩) (fun p N hN => ⟨?_, ?_⟩) ⟨1 + max mA mq + mq, le_max_of_le_left hM1, fun p => (hQ p).1⟩
    ⟨mB, le_max_right _ _, hBS⟩ (fun p N hN => le_trans (ENNReal.ofReal_le_ofReal ?_) (hd p N hN)) k p N hN
  · exact (isSectorPreserving_specSum_dev (D.d.H_isSelfAdjoint N hN) (H_isSectorPreserving_dev D.toIxSetting hN)
      (hAsp p N hN) _).isEven
  · calc ‖toCLM (D.T N) (D.Qf N (A p N))‖ ≤ C' * (N : ℝ) ^ (1 + mq) := (hQ p).2 N hN
      _ ≤ Cb * (N : ℝ) ^ max M mB :=
          mul_le_mul (by linarith [le_abs_self C', abs_nonneg C]) (hNpow N hN (le_max_of_le_left hM2))
            (hNnn N hN _) (by linarith [abs_nonneg C', abs_nonneg C])
  · calc ‖toCLM (D.T N) (B p N)‖ ≤ |C| * (N : ℝ) ^ mq := hup N hN _ (hBn p N hN)
      _ ≤ Cb * (N : ℝ) ^ max M mB :=
          mul_le_mul hCb2 (hNpow N hN (le_max_of_le_left (by linarith))) (hNnn N hN _)
            (by linarith [abs_nonneg C, abs_nonneg C'])
  · linarith [le_abs_self C, abs_nonneg C']

/-! #### Proof devices for the table of Lemma 6.12 and for Lemma 6.13(i) (phase (b); not statements of the paper)

The first six are the devices of round one for Lemma 7.1, moved here from `Assembly.Translation` in round two so that
the rows of `T_±` and the exact relations can use them (`Assembly.Translation` imports this module); `asBound_exact_dev`
(round two) is almost support with error `0`, for an operator whose image lies in `Alg(Z_N)` exactly. -/

section TableDevices

theorem natCast_injOn_dev {n m : ℕ} (hm : m ≤ n) :
    Set.InjOn (fun k : ℕ => (k : ZMod n)) (Finset.range m : Set ℕ) := by
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have h := (ZMod.natCast_eq_natCast_iff' a b n).mp hab
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h

theorem natCast_mem_image_range_dev {n m k : ℕ} (hm : m ≤ n) (hk : k < n) :
    (k : ZMod n) ∈ (Finset.range m).image (fun k : ℕ => (k : ZMod n)) ↔ k < m := by
  constructor
  · intro h
    obtain ⟨k', hk', hkk'⟩ := Finset.mem_image.mp h
    have h1 := (ZMod.natCast_eq_natCast_iff' k' k n).mp hkk'
    rw [Finset.mem_range] at hk'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hk] at h1
    omega
  · intro h
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr h, rfl⟩

theorem Qband_bandΓ_eq_sum_dev (T : Torus) {N s : ℕ} (hs : s + N ≤ T.Nφ) :
    Qband T ((Finset.range N).image fun k : ℕ => ((k + s : ℕ) : ZMod T.Nφ)) =
      ∑ k ∈ Finset.range N, njs T ((k + s : ℕ) : ZMod T.Nφ) .up := by
  unfold Qband
  rw [Finset.sum_image]
  intro a ha b hb hab
  have hinj := natCast_injOn_dev (n := T.Nφ) (m := N + s) (by omega)
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have := hinj (by simp; omega : a + s ∈ (Finset.range (N + s) : Set ℕ))
    (by simp; omega : b + s ∈ (Finset.range (N + s) : Set ℕ)) hab
  omega

theorem N_lt_Nφ_dev (D : ArgData η δ₀) {N : ℕ} (hN : N ∈ D.Ts.idx) : N < (D.T N).Nφ ∧ 0 < N := by
  have h1 := (D.T N).N_pos
  have h2 : (D.T N).N = N := D.Ts.T_N N hN
  have h3 : (D.T N).Nφ = 2 * (D.T N).N := rfl
  constructor <;> omega

/-- `Θ^* Q_Γ Θ − Q_Γ = n_{N↑} − n_{0↑}` (block C's `Θ_conj_Qband` and a telescoping sum). -/
theorem theta_transport_dev (D : ArgData η δ₀) {N : ℕ} (hN : N ∈ D.Ts.idx) :
    (Θ (D.T N))ᴴ * D.Q N * Θ (D.T N) - D.Q N =
      njs (D.T N) (N : ZMod (D.T N).Nφ) .up - njs (D.T N) 0 .up := by
  obtain ⟨hlt, hpos⟩ := N_lt_Nφ_dev D hN
  unfold IxSetting.Q
  rw [Θ_conj_Qband]
  have e1 : (bandΓ (D.T N).Nφ N).image (fun j => j + 1) =
      (Finset.range N).image fun k : ℕ => ((k + 1 : ℕ) : ZMod (D.T N).Nφ) := by
    unfold bandΓ
    rw [Finset.image_image]
    congr 1
    funext k
    simp
  have e0 : bandΓ (D.T N).Nφ N = (Finset.range N).image fun k : ℕ => ((k + 0 : ℕ) : ZMod (D.T N).Nφ) := by
    unfold bandΓ
    rfl
  rw [e1, Qband_bandΓ_eq_sum_dev _ (by omega), e0, Qband_bandΓ_eq_sum_dev _ (by omega), ← Finset.sum_sub_distrib]
  simp only [add_zero]
  rw [Finset.sum_range_sub (fun k : ℕ => njs (D.T N) ((k : ℕ) : ZMod (D.T N).Nφ) .up)]
  simp

theorem norm_toCLM_njs_dev (T : Torus) (j : ZMod T.Nφ) : ‖toCLM T (njs T j .up)‖ = 1 := by
  have hP := isStarProjection_njs T j .up
  have hne : njs T j .up ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun h0 (fun _ => true)) (fun _ => true)
    rw [njs_eq_diag] at h1
    simp at h1
  have h2 : ‖toCLM T (njs T j .up)‖ * ‖toCLM T (njs T j .up)‖ = ‖toCLM T (njs T j .up)‖ := by
    have hc := CStarRing.norm_star_mul_self (x := toCLM T (njs T j .up))
    rw [← toCLM_star_dev, ← toCLM_mul', hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq] at hc
    exact hc.symm
  have h3 : ‖toCLM T (njs T j .up)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    apply hne
    apply toCLM_injective_dev T
    rw [h, toCLM_zero_dev]
  exact mul_left_cancel₀ h3 (h2.trans (mul_one _).symm)

theorem asBound_exact_dev {Ts : TorusSeq δ₀} {Z : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))}
    {A : (N : ℕ) → FockOp (Ts.T N)} (h : ∀ N ∈ Ts.idx, iota η δ₀ (Ts.T N) (A N) ∈ Alg (Z N)) :
    ASBound η δ₀ Ts Z A 0 (fun _ => 0) := by
  refine ⟨le_rfl, fun k N hN r hr => ⟨iota η δ₀ (Ts.T N) (A N), Alg_mono (subset_fat _ hr) (h N hN), ?_⟩⟩
  simp

end TableDevices

/-! ### Lemma 6.12 (localization and size) for `U = Θ`, row by row -/

/-- **Lemma 6.12**, the row "`$Q$, $Q_\pm$, $Q_m$ & $\le N$ & $\Col\Gam$, $\Col\Gamma_\pm$, $\Col\Gmid$ (exactly) & $0$`": even,
sector-preserving, norm at most `N`, almost supported in the column of the band with error `0` at every radius. -/
theorem table_Q (hη : IsProfile η) (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) :
    (∀ N ∈ S.Ts.idx,
      IsEven (S.Q N) ∧ IsSectorPreserving (S.T N) (S.Q N) ∧ ‖toCLM (S.T N) (S.Q N)‖ ≤ N ∧
      IsEven (S.Qminus N) ∧ IsSectorPreserving (S.T N) (S.Qminus N) ∧ ‖toCLM (S.T N) (S.Qminus N)‖ ≤ N ∧
      IsEven (S.Qmid N) ∧ IsSectorPreserving (S.T N) (S.Qmid N) ∧ ‖toCLM (S.T N) (S.Qmid N)‖ ≤ N ∧
      IsEven (S.Qplus N) ∧ IsSectorPreserving (S.T N) (S.Qplus N) ∧ ‖toCLM (S.T N) (S.Qplus N)‖ ≤ N) ∧
    ASBound η δ₀ S.Ts (fun N => colBand δ₀ (S.T N) (bandΓ (S.T N).Nφ N)) S.Q 0 (fun _ => 0) ∧
    ASBound η δ₀ S.Ts (fun N => colBand δ₀ (S.T N) (quarterMinus (S.T N).Nφ N)) S.Qminus 0 (fun _ => 0) ∧
    ASBound η δ₀ S.Ts (fun N => colBand δ₀ (S.T N) (quarterMid (S.T N).Nφ N)) S.Qmid 0 (fun _ => 0) ∧
    ASBound η δ₀ S.Ts (fun N => colBand δ₀ (S.T N) (quarterPlus (S.T N).Nφ N)) S.Qplus 0 (fun _ => 0) := by
  have hE : ∀ N : ℕ, ∀ B : Finset (ZMod (S.T N).Nφ), B.card ≤ N →
      IsEven (Qband (S.T N) B) ∧ IsSectorPreserving (S.T N) (Qband (S.T N) B) ∧
        ‖toCLM (S.T N) (Qband (S.T N) B)‖ ≤ N :=
    fun N B hB => ⟨(Qband_isSectorPreserving _ B).isEven, Qband_isSectorPreserving _ B,
      (norm_Qband_le _ B).trans (by exact_mod_cast hB)⟩
  have hc1 : ∀ N : ℕ, (quarterMinus (S.T N).Nφ N).card ≤ N := fun N =>
    Finset.card_image_le.trans ((Finset.card_range _).le.trans (Nat.div_le_self N 4))
  have hc2 : ∀ N : ℕ, (quarterPlus (S.T N).Nφ N).card ≤ N := fun N =>
    Finset.card_image_le.trans ((Nat.card_Ico _ _).le.trans (Nat.sub_le _ _))
  have hc3 : ∀ N : ℕ, (quarterMid (S.T N).Nφ N).card ≤ N := fun N =>
    (Finset.card_le_card Finset.sdiff_subset).trans (card_bandΓ_le_dev _ N)
  have hA : ∀ B : (N : ℕ) → Finset (ZMod (S.T N).Nφ), ASBound η δ₀ S.Ts (fun N => colBand δ₀ (S.T N) (B N))
      (fun N => Qband (S.T N) (B N)) 0 (fun _ => 0) :=
    fun B => asBound_exact_dev fun N hN => iota_Qband_mem_Alg hη hδ₀ (S.Ts.admissible N hN) (B N)
  refine ⟨fun N _ => ?_, hA fun N => bandΓ (S.T N).Nφ N, hA fun N => quarterMinus (S.T N).Nφ N,
    hA fun N => quarterMid (S.T N).Nφ N, hA fun N => quarterPlus (S.T N).Nφ N⟩
  obtain ⟨a1, a2, a3⟩ := hE N _ (card_bandΓ_le_dev _ N)
  obtain ⟨b1, b2, b3⟩ := hE N _ (hc1 N)
  obtain ⟨c1, c2, c3⟩ := hE N _ (hc3 N)
  obtain ⟨d1, d2, d3⟩ := hE N _ (hc2 N)
  exact ⟨a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3⟩

/-- **Lemma 6.12**, the row "`$T_-=-n_{0\up}$, $T_+=n_{N\up}$ & $1$ & $\partial_\pm$ (exactly) & $0$`". -/
theorem table_T (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) :
    (∀ N ∈ D.Ts.idx,
      IsEven (D.Tminus N) ∧ IsSectorPreserving (D.T N) (D.Tminus N) ∧ ‖toCLM (D.T N) (D.Tminus N)‖ = 1 ∧
      IsEven (D.Tplus N) ∧ IsSectorPreserving (D.T N) (D.Tplus N) ∧ ‖toCLM (D.T N) (D.Tplus N)‖ = 1) ∧
    ASBound η δ₀ D.Ts D.cutMinus D.Tminus 0 (fun _ => 0) ∧ ASBound η δ₀ D.Ts D.cutPlus D.Tplus 0 (fun _ => 0) := by
  have hι : ∀ N ∈ D.Ts.idx, iota η δ₀ (D.T N) (D.Tminus N) ∈ Alg (D.cutMinus N) ∧
      iota η δ₀ (D.T N) (D.Tplus N) ∈ Alg (D.cutPlus N) := by
    intro N hN
    obtain ⟨hlt, -⟩ := N_lt_Nφ_dev D hN
    have hT := D.Ts.admissible N hN
    have hι0 := iota_njs_mem_Alg hη hδ₀ hT (0 : ZMod (D.T N).Nφ)
    rw [ZMod.val_zero, Nat.cast_zero] at hι0
    have hιN := iota_njs_mem_Alg hη hδ₀ hT (N : ZMod (D.T N).Nφ)
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hιN
    refine ⟨?_, hιN⟩
    unfold ArgData.Tminus
    rw [← iotaHom_apply hη hδ₀ hT, map_neg, iotaHom_apply hη hδ₀ hT, ← neg_one_smul ℂ]
    exact Alg_smul_mem _ hι0
  refine ⟨fun N _ => ?_, asBound_exact_dev fun N hN => (hι N hN).1, asBound_exact_dev fun N hN => (hι N hN).2⟩
  have hs0 : IsSectorPreserving (D.T N) (D.Tminus N) :=
    ⟨(njs_commute_Nsig _ _ _ _).neg_left, (njs_commute_Nsig _ _ _ _).neg_left⟩
  have hsN : IsSectorPreserving (D.T N) (D.Tplus N) := ⟨njs_commute_Nsig _ _ _ _, njs_commute_Nsig _ _ _ _⟩
  refine ⟨hs0.isEven, hs0, ?_, hsN.isEven, hsN, norm_toCLM_njs_dev _ _⟩
  unfold ArgData.Tminus
  rw [toCLM_neg_dev, norm_neg, norm_toCLM_njs_dev]

/-- **Lemma 6.12**, the row "`$J_\pm$ & $\le CN^2$ & $\partial_\pm$ & $2$`" (even and sector-preserving). -/
theorem table_J (hη : IsProfile η) (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) :
    (∀ N ∈ S.Ts.idx, IsEven (S.Jminus N) ∧ IsSectorPreserving (S.T N) (S.Jminus N) ∧
      IsEven (S.Jplus N) ∧ IsSectorPreserving (S.T N) (S.Jplus N)) ∧
    (∃ C : ℝ, ∀ N ∈ S.Ts.idx, ‖toCLM (S.T N) (S.Jminus N)‖ ≤ C * (N : ℝ) ^ 2 ∧
      ‖toCLM (S.T N) (S.Jplus N)‖ ≤ C * (N : ℝ) ^ 2) ∧
    ∃ C : ℕ → ℝ, ASBound η δ₀ S.Ts S.cutMinus S.Jminus 2 C ∧ ASBound η δ₀ S.Ts S.cutPlus S.Jplus 2 C := by
  obtain ⟨C, hC⟩ := J_almostSupported hδ₀ S.d.Ch S.d.CH
  obtain ⟨h1, h2, -⟩ := hC η hη S rfl rfl
  refine ⟨fun N hN => ?_, ⟨4 * π * S.d.Ch, norm_J_le S⟩, C, h1, h2⟩
  obtain ⟨-, k2, -, k4⟩ := J_isSelfAdjoint S N hN
  exact ⟨k2.isEven, k2, k4.isEven, k4⟩

/-! #### Proof devices for the rows of `K^U_±` (phase (b), round two; not statements of the paper)

Lemma 7.1(e)'s proof: under (H2), `Θ^* H_𝒟 Θ = H_{𝒟+κe_x}` (`theta_conj_HDd_dev`, by block C's
`setIntegral_inter_fundDom_shift`) and `Θ^* Q_𝓑 Θ = Q_{𝓑+1}`, so `Θ^* J_± Θ` is Lemma 6.6(iii)'s current for `j₀ = 1`
(`theta_conj_curr_dev`); `[Θ, H_N] = 0` passes through the dressing (`theta_conj_dress_dev`), so `K^U_± = Θ^* K_± Θ` is
its dressing (`KU_eq_dev`). Finally `Col(j + 1)^{(r)} ⊆ Col(j)^{(r + 4δ₀)}` (`col_succ_fat_dev`: `κ + δ_x ≤ 4δ₀`) moves the
almost support from `Col(1)`, `Col(N + 1)` to the cuts (`asBound_enlarge_dev`, the paper's last step, with
`(1 + a)^k` for `a = 4δ₀`). These devices are also used by `Assembly.Translation`'s Lemma 7.1(e). -/

section KUDevices

open scoped Pointwise in
theorem theta_conj_HDd_dev (S : IxSetting η δ₀) (hH2 : S.d.H2) {N : ℕ} (hN : N ∈ S.Ts.idx) {D : Set (ℝ × ℝ)}
    (hD : IsTorusSet (S.T N) D) :
    (Θ (S.T N))ᴴ * S.HDd N D * Θ (S.T N) = S.HDd N ((((S.T N).κ, 0) : ℝ × ℝ) +ᵥ D) := by
  have hd' : ∀ R : ℝ × ℝ, (Θ (S.T N))ᴴ * S.d.h N R * Θ (S.T N) = S.d.h N (R + ((S.T N).κ, 0)) := hH2 N hN
  have hint : ∀ m m' : Conf (ZMod (S.T N).Nφ), IntegrableOn (fun R => S.d.h N R m m') (D ∩ fundDom (S.T N)) :=
    fun m m' => (integrableOn_h S.d hN m m').mono_set Set.inter_subset_right
  let Φ : FockOp (S.T N) →ₗ[ℂ] FockOp (S.T N) :=
    (LinearMap.mulLeft ℂ (Θ (S.T N))ᴴ).comp (LinearMap.mulRight ℂ (Θ (S.T N)))
  have hΦ : ∀ A : FockOp (S.T N), Φ A = (Θ (S.T N))ᴴ * A * Θ (S.T N) := fun A => by
    simp only [Φ, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.mul_assoc]
  unfold IxSetting.HDd
  rw [← hΦ, opIntegral_map Φ _ _ hint]
  simp only [hΦ, hd']
  ext m m'
  simp only [opIntegral, Matrix.of_apply]
  exact setIntegral_inter_fundDom_shift (S.T N) hD (fun R => S.d.h N R m m') (fun R => by rw [S.d.h_add_Lx N hN R])

open scoped Pointwise in
theorem theta_conj_curr_dev (S : IxSetting η δ₀) (hH2 : S.d.H2) {N : ℕ} (hN : N ∈ S.Ts.idx) {D : Set (ℝ × ℝ)}
    (hD : IsTorusSet (S.T N) D) (B : Finset (ZMod (S.T N).Nφ)) :
    (Θ (S.T N))ᴴ * S.curr N D B * Θ (S.T N) =
      S.curr N ((((S.T N).κ, 0) : ℝ × ℝ) +ᵥ D) (B.image fun j => j + 1) := by
  have hu : Θ (S.T N) * (Θ (S.T N))ᴴ = 1 := mul_conjTranspose_self_of_mem_unitary (Θ_mem_unitary _)
  have hmul : ∀ X Y : FockOp (S.T N), (Θ (S.T N))ᴴ * (X * Y) * Θ (S.T N) =
      ((Θ (S.T N))ᴴ * X * Θ (S.T N)) * ((Θ (S.T N))ᴴ * Y * Θ (S.T N)) := by
    intro X Y
    calc (Θ (S.T N))ᴴ * (X * Y) * Θ (S.T N) =
        (Θ (S.T N))ᴴ * X * (Θ (S.T N) * (Θ (S.T N))ᴴ) * Y * Θ (S.T N) := by
          rw [hu, mul_one]
          simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  unfold IxSetting.curr
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hmul, hmul, theta_conj_HDd_dev S hH2 hN hD, Θ_conj_Qband]

theorem theta_conj_dress_dev {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) {γ : ℝ} (hγ : 0 < γ) {T : Torus} {H : FockOp T}
    (hH : IsSelfAdjoint H) (hΘH : Commute (Θ T) H) (A : FockOp T) :
    (Θ T)ᴴ * dress ϑ γ H A * Θ T = dress ϑ γ H ((Θ T)ᴴ * A * Θ T) := by
  have hWi := (hasFiniteMoments_Wfilt hϑ hγ).1
  have hτc : Continuous fun t => opCLM (dyn H t A) := continuous_opCLM_dyn _ _
  have hτn : ∀ t, ‖opCLM (dyn H t A)‖ ≤ ‖opCLM A‖ := fun t => le_of_eq (norm_dyn hH t A)
  have hint : ∀ m m', IntegrableOn (fun t => (Wfilt ϑ γ t • dyn H t A) m m') Set.univ :=
    fun m m' => integrable_entry_smul hWi hτc hτn _ m m'
  let Φ : FockOp T →ₗ[ℂ] FockOp T := (LinearMap.mulLeft ℂ (Θ T)ᴴ).comp (LinearMap.mulRight ℂ (Θ T))
  have hΦ : ∀ X : FockOp T, Φ X = (Θ T)ᴴ * X * Θ T := fun X => by
    simp only [Φ, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.mul_assoc]
  have hΘs : Commute (Θ T)ᴴ H := by
    have h := hΘH.star_star
    rwa [hH.star_eq, Matrix.star_eq_conjTranspose] at h
  have hdyn : ∀ t : ℝ, (Θ T)ᴴ * dyn H t A * Θ T = dyn H t ((Θ T)ᴴ * A * Θ T) := by
    intro t
    unfold dyn
    have h1 : Commute (Θ T)ᴴ (NormedSpace.exp ((I * (t : ℂ)) • H)) := (hΘs.smul_right _).exp_right
    have h2 : Commute (Θ T) (NormedSpace.exp ((-(I * (t : ℂ))) • H)) := (hΘH.smul_right _).exp_right
    calc (Θ T)ᴴ * (NormedSpace.exp ((I * (t : ℂ)) • H) * A * NormedSpace.exp ((-(I * (t : ℂ))) • H)) * Θ T
        = ((Θ T)ᴴ * NormedSpace.exp ((I * (t : ℂ)) • H)) * A *
            (NormedSpace.exp ((-(I * (t : ℂ))) • H) * Θ T) := by simp only [mul_assoc]
      _ = (NormedSpace.exp ((I * (t : ℂ)) • H) * (Θ T)ᴴ) * A *
            (Θ T * NormedSpace.exp ((-(I * (t : ℂ))) • H)) := by rw [h1.eq, ← h2.eq]
      _ = NormedSpace.exp ((I * (t : ℂ)) • H) * ((Θ T)ᴴ * A * Θ T) *
            NormedSpace.exp ((-(I * (t : ℂ))) • H) := by simp only [mul_assoc]
  unfold dress
  rw [← hΦ, opIntegralOn_map Φ _ _ hint]
  simp only [hΦ, Matrix.mul_smul, Matrix.smul_mul, hdyn]

open scoped Pointwise in
/-- `K^U_∓` is the dressing of Lemma 6.6(iii)'s current for `j₀ = 1`. -/
theorem KU_eq_dev (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) {N : ℕ} (hN : N ∈ D.Ts.idx) :
    D.KUminus N = dress D.ϑ D.γ (D.H N) (D.JminusShift 1 N) ∧
      D.KUplus N = dress D.ϑ D.γ (D.H N) (D.JplusShift 1 N) := by
  have hγ : 0 < D.γ := by linarith [hD.gap.Δ_nonneg, hD.gap.two_mul_Δ_lt]
  have hH := D.d.H_isSelfAdjoint N hN
  have hΘH := D.d.commute_Θ_of_H2 hH2 N hN
  obtain ⟨h1, h2, -, -⟩ := isTorusSet_half (D.T N) 0
  have hv : ∀ E : Set (ℝ × ℝ), ((((D.T N).κ, 0) : ℝ × ℝ) +ᵥ E) = shiftX (D.T N) 1 E := fun E => by
    ext R
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
    simp [shiftX]
  have hb : (bandΓ (D.T N).Nφ N).image (fun j => j + 1) = bandShift (D.T N).Nφ N 1 := by
    simp [bandShift]
  unfold ArgData.KUminus ArgData.KUplus ArgData.Km ArgData.Kp IxSetting.Kminus IxSetting.Kplus
  rw [theta_conj_dress_dev hD.cutoff hγ hH hΘH, theta_conj_dress_dev hD.cutoff hγ hH hΘH]
  unfold IxSetting.Jminus IxSetting.Jplus
  rw [theta_conj_curr_dev D.toIxSetting hH2 hN h1, theta_conj_curr_dev D.toIxSetting hH2 hN h2, hv, hv, hb]
  exact ⟨rfl, rfl⟩

theorem col_succ_fat_dev (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (j : ℤ) {r : ℝ} :
    fat (col δ₀ T (j + 1)) r ⊆ fat (col δ₀ T j) (r + 4 * δ₀) := by
  have hδx := δx_pos hδ₀ hT
  have hδx2 : δx δ₀ T ≤ 2 * δ₀ := (consistency_ii hδ₀ hT).2.2.1
  have hκ := T.κ_pos
  have hκ2 := κ_le hδ₀ hT
  have h1 : col δ₀ T (j + 1) ⊆ fat (col δ₀ T j) (T.κ + δx δ₀ T) := by
    intro s hs
    rw [col_eq_strip hδ₀ hT j]
    refine strip_cthickening_subset hδ₀ hT (by linarith) hκ.le ?_
    rw [col_eq_strip hδ₀ hT (j + 1), mem_strip, mem_circImage] at hs
    obtain ⟨m, hm⟩ := hs
    rw [mem_strip, cthickening_circImage_Ioo T.Lx_pos (by linarith) hκ.le, mem_circImage]
    refine ⟨m, ?_⟩
    rw [Set.mem_Ioo] at hm
    push_cast at hm
    rw [Set.mem_Icc]
    constructor <;> linarith [hm.1, hm.2]
  calc fat (col δ₀ T (j + 1)) r ⊆ fat (fat (col δ₀ T j) (T.κ + δx δ₀ T)) r := fat_mono_left h1 r
    _ ⊆ fat (col δ₀ T j) (T.κ + δx δ₀ T + r) := fat_fat_subset _ _ _
    _ ⊆ fat (col δ₀ T j) (r + 4 * δ₀) := fat_mono_right _ (by linarith)

theorem asBound_enlarge_dev (hη : IsProfile η) (hδ₀ : 0 < δ₀) {Ts : TorusSeq δ₀}
    {X Y : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))} {A : (N : ℕ) → FockOp (Ts.T N)} {m a CA : ℝ} {C : ℕ → ℝ}
    (ha : 0 ≤ a) (hXY : ∀ N ∈ Ts.idx, ∀ r : ℝ, 0 ≤ r → fat (X N) r ⊆ fat (Y N) (r + a))
    (hA : ASBound η δ₀ Ts X A m C) (hn : ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (A N)‖ ≤ CA * (N : ℝ) ^ m) :
    ASBound η δ₀ Ts Y A m (fun k => (1 + a) ^ k * (|C k| + |CA|)) := by
  refine ⟨hA.1, fun k N hN r hr => ?_⟩
  have hT := Ts.admissible N hN
  have hN1 := one_le_of_mem_idx Ts hN
  have hNm : 0 ≤ (N : ℝ) ^ m := Real.rpow_nonneg (by linarith) _
  have hr1 : 0 ≤ (1 + r) ^ (-(k : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hak : 0 ≤ (1 + a) ^ k := by positivity
  rcases le_or_gt a r with har | har
  · obtain ⟨A', hA', hb⟩ := hA.2 k N hN (r - a) (by linarith)
    have hsub : fat (X N) (r - a) ⊆ fat (Y N) r := by
      have h := hXY N hN (r - a) (by linarith)
      rwa [sub_add_cancel] at h
    refine ⟨A', Alg_mono hsub hA', hb.trans ?_⟩
    have hk := rpow_neg_le_dev (a := 1 + r) (b := 1 + (r - a)) (c := 1 + a) (by linarith) (by linarith)
      (by nlinarith [mul_nonneg ha (sub_nonneg.mpr har)]) k
    have h0 : 0 ≤ (1 + a) ^ k * |CA| * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ)) := by positivity
    calc C k * (N : ℝ) ^ m * (1 + (r - a)) ^ (-(k : ℝ)) ≤
        |C k| * (N : ℝ) ^ m * ((1 + a) ^ k * (1 + r) ^ (-(k : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hNm) hk (Real.rpow_nonneg (by linarith) _)
            (mul_nonneg (abs_nonneg _) hNm)
      _ ≤ (1 + a) ^ k * (|C k| + |CA|) * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ)) := by linarith
  · refine ⟨0, Alg_zero_mem _, ?_⟩
    rw [sub_zero, norm_iota hη hδ₀ hT]
    have hk := rpow_neg_le_dev (a := 1 + r) (b := 1) (c := 1 + a) (by linarith) one_pos
      (by linarith) k
    rw [Real.one_rpow] at hk
    have h0 : 0 ≤ (1 + a) ^ k * |C k| * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ)) := by positivity
    calc ‖toCLM (Ts.T N) (A N)‖ ≤ CA * (N : ℝ) ^ m := hn N hN
      _ ≤ |CA| * (N : ℝ) ^ m := mul_le_mul_of_nonneg_right (le_abs_self _) hNm
      _ ≤ |CA| * (N : ℝ) ^ m * ((1 + a) ^ k * (1 + r) ^ (-(k : ℝ))) :=
          le_mul_of_one_le_right (by positivity) hk
      _ ≤ (1 + a) ^ k * (|C k| + |CA|) * (N : ℝ) ^ m * (1 + r) ^ (-(k : ℝ)) := by linarith

end KUDevices

/-- **Lemma 6.12**, the row "`$K_\pm$, $K^U_\pm$ & $\le CN^2$ & $\partial_\pm$ & $5/2$`" for `U = Θ`. -/
theorem table_K (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    (∀ N ∈ D.Ts.idx, IsEven (D.Km N) ∧ IsSectorPreserving (D.T N) (D.Km N) ∧
      IsEven (D.Kp N) ∧ IsSectorPreserving (D.T N) (D.Kp N) ∧
      IsEven (D.KUminus N) ∧ IsSectorPreserving (D.T N) (D.KUminus N) ∧
      IsEven (D.KUplus N) ∧ IsSectorPreserving (D.T N) (D.KUplus N)) ∧
    (∃ C : ℝ, ∀ N ∈ D.Ts.idx, ‖toCLM (D.T N) (D.Km N)‖ ≤ C * (N : ℝ) ^ 2 ∧
      ‖toCLM (D.T N) (D.Kp N)‖ ≤ C * (N : ℝ) ^ 2 ∧ ‖toCLM (D.T N) (D.KUminus N)‖ ≤ C * (N : ℝ) ^ 2 ∧
      ‖toCLM (D.T N) (D.KUplus N)‖ ≤ C * (N : ℝ) ^ 2) ∧
    ∃ C : ℕ → ℝ, ASBound η δ₀ D.Ts D.cutMinus D.Km (5 / 2) C ∧ ASBound η δ₀ D.Ts D.cutPlus D.Kp (5 / 2) C ∧
      ASBound η δ₀ D.Ts D.cutMinus D.KUminus (5 / 2) C ∧ ASBound η δ₀ D.Ts D.cutPlus D.KUplus (5 / 2) C := by
  have hγ : 0 < D.γ := by linarith [hD.gap.Δ_nonneg, hD.gap.two_mul_Δ_lt]
  have hM0 : 0 ≤ moment (Wfilt D.ϑ D.γ) 0 := MeasureTheory.integral_nonneg fun t => by positivity
  obtain ⟨C, hC⟩ := K_almostSupported hδ₀ hD.cutoff hγ D.d.Ch D.d.CH D.cstar
  obtain ⟨hKm, hKp, hKs⟩ := hC η hη D.toIxSetting rfl rfl rfl
  have hKU := fun N (hN : N ∈ D.Ts.idx) => KU_eq_dev D hD hH2 hN
  -- the norms: `‖K‖ ≤ M_0(W_γ) ‖J‖ ≤ M_0(W_γ) 4π|C_h| N²`
  have hnorm : ∀ N ∈ D.Ts.idx,
      ‖toCLM (D.T N) (D.Km N)‖ ≤ moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|) * (N : ℝ) ^ 2 ∧
      ‖toCLM (D.T N) (D.Kp N)‖ ≤ moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|) * (N : ℝ) ^ 2 ∧
      ‖toCLM (D.T N) (D.KUminus N)‖ ≤ moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|) * (N : ℝ) ^ 2 ∧
      ‖toCLM (D.T N) (D.KUplus N)‖ ≤ moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|) * (N : ℝ) ^ 2 := by
    intro N hN
    have hCh : 4 * π * D.d.Ch * (N : ℝ) ^ 2 ≤ 4 * π * |D.d.Ch| * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)) (by positivity)
    have hb : ∀ J : FockOp (D.T N), ‖toCLM (D.T N) J‖ ≤ 4 * π * D.d.Ch * (N : ℝ) ^ 2 →
        moment (Wfilt D.ϑ D.γ) 0 * ‖toCLM (D.T N) J‖ ≤
          moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|) * (N : ℝ) ^ 2 := fun J hJ => by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hJ.trans hCh) hM0
    obtain ⟨k1, k2⟩ := norm_K_le hD.cutoff hγ D.toIxSetting N hN
    obtain ⟨k3, k4⟩ := norm_KShift_le hD.cutoff hγ D.toIxSetting 1 N hN
    obtain ⟨j1, j2⟩ := norm_J_le D.toIxSetting N hN
    obtain ⟨-, -, -, -, -, j3, j4⟩ := JShift_props D.toIxSetting 1 N hN
    rw [(hKU N hN).1, (hKU N hN).2]
    exact ⟨k1.trans (hb _ j1), k2.trans (hb _ j2), k3.trans (hb _ j3), k4.trans (hb _ j4)⟩
  have hn52 : ∀ A : (N : ℕ) → FockOp (D.T N),
      (∀ N ∈ D.Ts.idx, ‖toCLM (D.T N) (A N)‖ ≤ moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|) * (N : ℝ) ^ 2) →
      ∀ N ∈ D.Ts.idx, ‖toCLM (D.Ts.T N) (A N)‖ ≤
        moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|) * (N : ℝ) ^ (5 / 2 : ℝ) := by
    intro A hA N hN
    have hN1 := one_le_of_mem_idx D.Ts hN
    have h2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    exact (hA N hN).trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  -- `K^U_∓` from the currents for `j₀ = 1`, moved to the cuts
  have hU1 : ASBound η δ₀ D.Ts D.cutMinus D.KUminus (5 / 2)
      (fun k => (1 + 4 * δ₀) ^ k * (|C k| + |moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|)|)) := by
    refine asBound_enlarge_dev hη hδ₀ (X := fun N => col δ₀ (D.T N) 1) (by positivity) (fun N hN r _ => ?_)
      (asBound_congr (hKs 1).1 fun N hN => (hKU N hN).1.symm) (hn52 _ fun N hN => (hnorm N hN).2.2.1)
    have h := col_succ_fat_dev hδ₀ (D.Ts.admissible N hN) 0 (r := r)
    rwa [zero_add] at h
  have hU2 : ASBound η δ₀ D.Ts D.cutPlus D.KUplus (5 / 2)
      (fun k => (1 + 4 * δ₀) ^ k * (|C k| + |moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|)|)) := by
    refine asBound_enlarge_dev hη hδ₀ (X := fun N => col δ₀ (D.T N) (1 + N)) (by positivity) (fun N hN r _ => ?_)
      (asBound_congr (hKs 1).2 fun N hN => (hKU N hN).2.symm) (hn52 _ fun N hN => (hnorm N hN).2.2.2)
    have h := col_succ_fat_dev hδ₀ (D.Ts.admissible N hN) (N : ℤ) (r := r)
    rwa [add_comm (N : ℤ) 1] at h
  refine ⟨fun N hN => ?_, ⟨_, hnorm⟩, fun k => |C k| + (1 + 4 * δ₀) ^ k * (|C k| +
    |moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|)|), asBound_mono_const hKm fun k => ?_,
    asBound_mono_const hKp fun k => ?_, asBound_mono_const hU1 fun k => ?_, asBound_mono_const hU2 fun k => ?_⟩
  · obtain ⟨-, k2, -, k4⟩ := K_isSelfAdjoint hD.cutoff hγ D.toIxSetting N hN
    have hH := D.d.H_isSelfAdjoint N hN
    have hHs := H_isSectorPreserving_dev D.toIxSetting hN
    obtain ⟨-, j1, j2, j3, j4, -, -⟩ := JShift_props D.toIxSetting 1 N hN
    obtain ⟨-, u2⟩ := dress_props_dev hD.cutoff hγ hH hHs j1 j2
    obtain ⟨-, u4⟩ := dress_props_dev hD.cutoff hγ hH hHs j3 j4
    rw [(hKU N hN).1, (hKU N hN).2]
    exact ⟨k2.isEven, k2, k4.isEven, k4, u2.isEven, u2, u4.isEven, u4⟩
  · have := abs_nonneg (C k)
    have : 0 ≤ (1 + 4 * δ₀) ^ k * (|C k| + |moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|)|) := by positivity
    linarith [le_abs_self (C k)]
  · have : 0 ≤ (1 + 4 * δ₀) ^ k * (|C k| + |moment (Wfilt D.ϑ D.γ) 0 * (4 * π * |D.d.Ch|)|) := by positivity
    linarith [le_abs_self (C k)]
  · linarith [abs_nonneg (C k)]
  · linarith [abs_nonneg (C k)]

/-! #### Proof devices for the clustering inputs (phase (b), round two; not statements of the paper)

`d(X, Y) = d(Y, X)` (`slotSetDist_comm_dev`), and `|Col(j)| ≤ (4δ₀/π + 1/2)(4π/c_*) N^{1/2}` for every `j`
(`card_col_le_dev`: block C's two windows of `Col(j)`, Lemma 6.2's bound on `L_y`). -/

section CluDevices

theorem slotSetDist_comm_dev {T : Torus} (X Y : Finset (Slot δ₀ T)) : slotSetDist X Y = slotSetDist Y X := by
  have key : ∀ X Y : Finset (Slot δ₀ T), slotSetDist X Y ≤ slotSetDist Y X := by
    intro X Y
    unfold slotSetDist
    refine Finset.le_inf fun p hp => ?_
    rw [Finset.mem_product] at hp
    refine (Finset.inf_le (b := (p.2, p.1)) (Finset.mem_product.mpr ⟨hp.2, hp.1⟩)).trans_eq ?_
    simp only
    rw [slotDist_comm']
  exact le_antisymm (key X Y) (key Y X)

theorem card_col_le_dev (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) (j : ℤ) {N : ℕ} (hN : N ∈ S.Ts.idx) :
    ((col δ₀ (S.T N) j).card : ℝ) ≤ (4 * δ₀ / π + 1 / 2) * (4 * π / S.cstar) * (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hT : (S.T N).Admissible δ₀ := S.Ts.admissible N hN
  have hTN : (S.T N).N = N := S.Ts.T_N N hN
  obtain ⟨-, -, h3, h4⟩ := card_cut_le hδ₀ hT S.cstar_pos (by rw [hTN]; exact S.Lx_ge N hN)
  obtain ⟨W, hW, hcolW⟩ := col_windows hδ₀ hT j
  have h5 : (col δ₀ (S.T N) j).card ≤ 2 * ny δ₀ (S.T N) := by
    rw [hcolW, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ hW
  have h6 : ((col δ₀ (S.T N) j).card : ℝ) ≤ 2 * ny δ₀ (S.T N) := by exact_mod_cast h5
  rw [hTN] at h4
  rw [← Real.sqrt_eq_rpow]
  calc ((col δ₀ (S.T N) j).card : ℝ) ≤ 2 * ny δ₀ (S.T N) := h6
    _ ≤ (4 * δ₀ / π + 1 / 2) * (S.T N).Ly := h3
    _ ≤ (4 * δ₀ / π + 1 / 2) * (4 * π / S.cstar * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (4 * δ₀ / π + 1 / 2) * (4 * π / S.cstar) * Real.sqrt N := by ring

end CluDevices

/-! #### Proof devices for the rows of the unitaries (phase (b), round two; not statements of the paper)

The proof's (F2) — the product of two almost supported operators of norm at most `1` keeps the larger prefactor
exponent (`asBound_mul_unit_dev`, with the approximant of the first factor replaced by `0` when its error exceeds `1`)
— and its factorization `𝓜_-(φ) = [e^{iφ(Q_-+Ξ^U_-)}e^{-iφQ_-}][e^{iφ(Q_-+Ξ_-)}e^{-iφQ_-}]^*` with block C's
Lemma 5.12(d) for each bracket (`Mrow_dev`, one row at a time, for a cut `Col(j_N)` and a band); the unitarity of
`e^{cX}` for self-adjoint `X` and imaginary `c` in the matrices (`exp_mem_unitary_dev`), sector preservation of
exponentials, products and adjoints (`sp_*_dev`), and the almost-support calculus for differences and for a change of
the sets off `𝒩` (`asBound_sub_dev`, `asBound_congr_set_dev`). -/

section MDevices

theorem Nsig_isSelfAdjoint_dev (T : Torus) (σ : Spin) : IsSelfAdjoint (Nsig T σ) := by
  rw [IsSelfAdjoint, Nsig_eq_diag, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext m
  simp

theorem sp_exp_dev {T : Torus} {X : FockOp T} (hX : IsSectorPreserving T X) (c : ℂ) :
    IsSectorPreserving T (NormedSpace.exp (c • X)) :=
  ⟨(hX.1.smul_left c).exp_left, (hX.2.smul_left c).exp_left⟩

theorem sp_mul_dev {T : Torus} {X Y : FockOp T} (hX : IsSectorPreserving T X) (hY : IsSectorPreserving T Y) :
    IsSectorPreserving T (X * Y) :=
  ⟨hX.1.mul_left hY.1, hX.2.mul_left hY.2⟩

theorem sp_add_dev {T : Torus} {X Y : FockOp T} (hX : IsSectorPreserving T X) (hY : IsSectorPreserving T Y) :
    IsSectorPreserving T (X + Y) :=
  ⟨hX.1.add_left hY.1, hX.2.add_left hY.2⟩

theorem sp_sub_dev {T : Torus} {X Y : FockOp T} (hX : IsSectorPreserving T X) (hY : IsSectorPreserving T Y) :
    IsSectorPreserving T (X - Y) :=
  ⟨hX.1.sub_left hY.1, hX.2.sub_left hY.2⟩

theorem sp_conjTranspose_dev {T : Torus} {X : FockOp T} (hX : IsSectorPreserving T X) :
    IsSectorPreserving T Xᴴ := by
  have h1 := hX.1.star_star
  have h2 := hX.2.star_star
  rw [(Nsig_isSelfAdjoint_dev T _).star_eq, Matrix.star_eq_conjTranspose] at h1 h2
  exact ⟨h1, h2⟩

theorem conjTranspose_exp_smul_dev {T : Torus} {X : FockOp T} (hX : IsSelfAdjoint X) (c : ℂ) :
    (NormedSpace.exp (c • X))ᴴ = NormedSpace.exp ((starRingEnd ℂ c) • X) := by
  have hX' : Xᴴ = X := by rw [← Matrix.star_eq_conjTranspose]; exact hX.star_eq
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hX']
  rfl

theorem exp_smul_mul_exp_neg_dev {T : Torus} (X : FockOp T) (c : ℂ) :
    NormedSpace.exp (c • X) * NormedSpace.exp ((-c) • X) = 1 ∧
      NormedSpace.exp ((-c) • X) * NormedSpace.exp (c • X) = 1 := by
  have h1 : Commute (c • X) ((-c) • X) := ((Commute.refl X).smul_left c).smul_right (-c)
  constructor
  · rw [← Matrix.exp_add_of_commute _ _ h1, ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  · rw [← Matrix.exp_add_of_commute _ _ h1.symm, ← add_smul, neg_add_cancel, zero_smul, NormedSpace.exp_zero]

theorem exp_mem_unitary_dev {T : Torus} {X : FockOp T} (hX : IsSelfAdjoint X) {c : ℂ}
    (hc : starRingEnd ℂ c = -c) : NormedSpace.exp (c • X) ∈ unitary (FockOp T) := by
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, conjTranspose_exp_smul_dev hX, hc]
  exact ⟨(exp_smul_mul_exp_neg_dev X c).2, (exp_smul_mul_exp_neg_dev X c).1⟩

theorem norm_toCLM_le_one_dev {T : Torus} {U : FockOp T} (hU : U ∈ unitary (FockOp T)) : ‖toCLM T U‖ ≤ 1 := by
  have hU' : toCLM T U ∈ unitary (FockSpace T →L[ℂ] FockSpace T) := by
    rw [Unitary.mem_iff] at hU ⊢
    rw [← toCLM_star_dev, ← toCLM_mul', ← toCLM_mul', hU.1, hU.2, toCLM_one_dev]
    exact ⟨rfl, rfl⟩
  have h : ‖toCLM T U * 1‖ = ‖(1 : FockSpace T →L[ℂ] FockSpace T)‖ := CStarRing.norm_coe_unitary_mul ⟨_, hU'⟩ 1
  rw [mul_one] at h
  rw [h]
  exact ContinuousLinearMap.norm_id_le

theorem asBound_congr_set_dev {Ts : TorusSeq δ₀} {X Y : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))}
    {A : (N : ℕ) → FockOp (Ts.T N)} {m : ℝ} {C : ℕ → ℝ} (hXY : ∀ N ∈ Ts.idx, X N = Y N)
    (h : ASBound η δ₀ Ts X A m C) : ASBound η δ₀ Ts Y A m C :=
  ⟨h.1, fun k N hN r hr => by rw [← hXY N hN]; exact h.2 k N hN r hr⟩

theorem asBound_sub_dev (hη : IsProfile η) (hδ₀ : 0 < δ₀) {Ts : TorusSeq δ₀}
    {X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))} {A B : (N : ℕ) → FockOp (Ts.T N)} {mA mB : ℝ} {CA CB : ℕ → ℝ}
    (hA : ASBound η δ₀ Ts X A mA CA) (hB : ASBound η δ₀ Ts X B mB CB) :
    ASBound η δ₀ Ts X (fun N => A N - B N) (max mA mB) (fun k => |CA k| + |CB k|) := by
  have h := asBound_add hη hδ₀ hA (asBound_smul hη hδ₀ hB (-1))
  refine asBound_mono_const (asBound_congr h fun N _ => by simp [sub_eq_add_neg]) fun k => ?_
  simp

/-- The proof's (F2): `AB ∈ 𝒜𝒮_X` with prefactor exponent `max{m_A, m_B}` when `‖A_N‖, ‖B_N‖ ≤ 1`. -/
theorem asBound_mul_unit_dev (hη : IsProfile η) (hδ₀ : 0 < δ₀) {Ts : TorusSeq δ₀}
    {X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))} {A B : (N : ℕ) → FockOp (Ts.T N)} {mA mB : ℝ} {CA CB : ℕ → ℝ}
    (hA : ASBound η δ₀ Ts X A mA CA) (hB : ASBound η δ₀ Ts X B mB CB)
    (hAn : ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (A N)‖ ≤ 1) (hBn : ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (B N)‖ ≤ 1) :
    ASBound η δ₀ Ts X (fun N => A N * B N) (max mA mB) (fun k => |CA k| + 2 * |CB k|) := by
  refine ⟨le_max_of_le_left hA.1, fun k N hN r hr => ?_⟩
  have hT := Ts.admissible N hN
  have hN1 := one_le_of_mem_idx Ts hN
  have hρ : 0 ≤ (1 + r) ^ (-(k : ℝ)) := Real.rpow_nonneg (by linarith) _
  obtain ⟨A', hA', ha⟩ := hA.2 k N hN r hr
  obtain ⟨B', hB', hb⟩ := hB.2 k N hN r hr
  have hιA : ‖opCLM (iota η δ₀ (Ts.T N) (A N))‖ ≤ 1 := by rw [norm_iota hη hδ₀ hT]; exact hAn N hN
  have hιB : ‖opCLM (iota η δ₀ (Ts.T N) (B N))‖ ≤ 1 := by rw [norm_iota hη hδ₀ hT]; exact hBn N hN
  obtain ⟨A'', hA''m, hA''e, hA''n⟩ : ∃ A'' ∈ Alg (fat (X N) r),
      ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A'')‖ ≤ CA k * (N : ℝ) ^ mA * (1 + r) ^ (-(k : ℝ)) ∧
        ‖opCLM A''‖ ≤ 2 := by
    by_cases h1 : ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A')‖ ≤ 1
    · refine ⟨A', hA', ha, ?_⟩
      have e : A' = iota η δ₀ (Ts.T N) (A N) - (iota η δ₀ (Ts.T N) (A N) - A') := by abel
      rw [e, opCLM_sub']
      exact (norm_sub_le _ _).trans (by linarith)
    · push Not at h1
      refine ⟨0, Alg_zero_mem _, ?_, ?_⟩
      · rw [sub_zero]
        linarith
      · rw [opCLM_zero', norm_zero]
        norm_num
  refine ⟨A'' * B', Alg_mul_mem hA''m hB', ?_⟩
  have e : iota η δ₀ (Ts.T N) (A N * B N) - A'' * B' =
      (iota η δ₀ (Ts.T N) (A N) - A'') * iota η δ₀ (Ts.T N) (B N) + A'' * (iota η δ₀ (Ts.T N) (B N) - B') := by
    rw [iota_mul hη hδ₀ hT]
    noncomm_ring
  have hNa : (N : ℝ) ^ mA ≤ (N : ℝ) ^ max mA mB := Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)
  have hNb : (N : ℝ) ^ mB ≤ (N : ℝ) ^ max mA mB := Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)
  have hNa0 : 0 ≤ (N : ℝ) ^ mA := Real.rpow_nonneg (by linarith) _
  have hNb0 : 0 ≤ (N : ℝ) ^ mB := Real.rpow_nonneg (by linarith) _
  rw [e, opCLM_add']
  calc ‖opCLM ((iota η δ₀ (Ts.T N) (A N) - A'') * iota η δ₀ (Ts.T N) (B N)) +
        opCLM (A'' * (iota η δ₀ (Ts.T N) (B N) - B'))‖
      ≤ ‖opCLM (iota η δ₀ (Ts.T N) (A N) - A'')‖ * ‖opCLM (iota η δ₀ (Ts.T N) (B N))‖ +
          ‖opCLM A''‖ * ‖opCLM (iota η δ₀ (Ts.T N) (B N) - B')‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_opCLM_mul_le _ _) (norm_opCLM_mul_le _ _))
    _ ≤ (CA k * (N : ℝ) ^ mA * (1 + r) ^ (-(k : ℝ))) * 1 + 2 * (CB k * (N : ℝ) ^ mB * (1 + r) ^ (-(k : ℝ))) :=
        add_le_add (mul_le_mul hA''e hιB (norm_nonneg _) ((norm_nonneg _).trans hA''e))
          (mul_le_mul hA''n hb (norm_nonneg _) (by norm_num))
    _ ≤ (|CA k| + 2 * |CB k|) * (N : ℝ) ^ max mA mB * (1 + r) ^ (-(k : ℝ)) := by
        have h1 : CA k * (N : ℝ) ^ mA ≤ |CA k| * (N : ℝ) ^ max mA mB :=
          mul_le_mul (le_abs_self _) hNa hNa0 (abs_nonneg _)
        have h2 : CB k * (N : ℝ) ^ mB ≤ |CB k| * (N : ℝ) ^ max mA mB :=
          mul_le_mul (le_abs_self _) hNb hNb0 (abs_nonneg _)
        have h3 := mul_le_mul_of_nonneg_right h1 hρ
        have h4 := mul_le_mul_of_nonneg_right h2 hρ
        nlinarith

/-- One row of the unitaries: for the cut `Col(j_N)`, a band `𝓑_N` and self-adjoint `Ξ^U`, `Ξ` almost supported in the
cut with prefactor exponent `5/2` and norm at most `C N^{5/2}`, the operators `e^{iφ(Q_𝓑+Ξ^U)} e^{-iφ(Q_𝓑+Ξ)}`
(uniformly in `φ ∈ [0, 2π]`) and `e^{±2πi(Q_𝓑+Ξ)}` are almost supported in the cut with prefactor exponent `5/2`. -/
theorem Mrow_dev (hη : IsProfile η) (hδ₀ : 0 < δ₀) (Ts : TorusSeq δ₀) (j : ℕ → ℤ)
    (B : (N : ℕ) → Finset (ZMod (Ts.T N).Nφ)) (XU X : (N : ℕ) → FockOp (Ts.T N)) {C : ℝ} {CU CX : ℕ → ℝ}
    (hXUs : ∀ N ∈ Ts.idx, IsSelfAdjoint (XU N)) (hXs : ∀ N ∈ Ts.idx, IsSelfAdjoint (X N))
    (hXUa : ASBound η δ₀ Ts (fun N => col δ₀ (Ts.T N) (j N)) XU (5 / 2) CU)
    (hXa : ASBound η δ₀ Ts (fun N => col δ₀ (Ts.T N) (j N)) X (5 / 2) CX)
    (hXUn : ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (XU N)‖ ≤ C * (N : ℝ) ^ (5 / 2 : ℝ))
    (hXn : ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (X N)‖ ≤ C * (N : ℝ) ^ (5 / 2 : ℝ)) :
    ∃ C' : ℕ → ℝ,
      (∀ φ ∈ Set.Icc (0 : ℝ) (2 * π), ASBound η δ₀ Ts (fun N => col δ₀ (Ts.T N) (j N))
        (fun N => NormedSpace.exp ((I * (φ : ℂ)) • (Qband (Ts.T N) (B N) + XU N)) *
          NormedSpace.exp ((-(I * (φ : ℂ))) • (Qband (Ts.T N) (B N) + X N))) (5 / 2) C') ∧
      ASBound η δ₀ Ts (fun N => col δ₀ (Ts.T N) (j N))
        (fun N => NormedSpace.exp ((2 * π * I : ℂ) • (Qband (Ts.T N) (B N) + X N))) (5 / 2) C' ∧
      ASBound η δ₀ Ts (fun N => col δ₀ (Ts.T N) (j N))
        (fun N => NormedSpace.exp ((-(2 * π * I : ℂ)) • (Qband (Ts.T N) (B N) + X N))) (5 / 2) C' := by
  have hZ : ∀ N ∈ Ts.idx, col δ₀ (Ts.T N) (j N) = strip δ₀ (Ts.T N) (circImage (Ts.T N).Lx
      (Set.Ioo ((Ts.T N).κ * (j N : ℝ) - δx δ₀ (Ts.T N)) ((Ts.T N).κ * (j N : ℝ) + δx δ₀ (Ts.T N)))) :=
    fun N hN => col_eq_strip hδ₀ (Ts.admissible N hN) (j N)
  have hZ' := fun N (hN : N ∈ Ts.idx) => (hZ N hN).symm
  have hab : ∀ N ∈ Ts.idx, 2 * δx δ₀ (Ts.T N) ≤
      ((Ts.T N).κ * (j N : ℝ) + δx δ₀ (Ts.T N)) - ((Ts.T N).κ * (j N : ℝ) - δx δ₀ (Ts.T N)) :=
    fun N _ => by linarith
  obtain ⟨C1, hC1⟩ := exp_Qband_add_almostSupported hδ₀ C CU
  obtain ⟨C2, hC2⟩ := exp_Qband_add_almostSupported hδ₀ C CX
  have hV1 := fun φ (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * π)) => asBound_congr_set_dev hZ'
    (hC1 η hη Ts _ _ hab XU (5 / 2) (asBound_congr_set_dev hZ hXUa) hXUs hXUn B φ hφ)
  have hV2 := fun φ (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * π)) => asBound_congr_set_dev hZ'
    (hC2 η hη Ts _ _ hab X (5 / 2) (asBound_congr_set_dev hZ hXa) hXs hXn B φ hφ)
  have hQs : ∀ N, IsSelfAdjoint (Qband (Ts.T N) (B N)) := fun N => Qband_isSelfAdjoint _ _
  have hc1 : ∀ φ : ℝ, starRingEnd ℂ (I * (φ : ℂ)) = -(I * (φ : ℂ)) := fun φ => by simp
  have hc2 : ∀ φ : ℝ, starRingEnd ℂ (-(I * (φ : ℂ))) = -(-(I * (φ : ℂ))) := fun φ => by simp
  have hU : ∀ N ∈ Ts.idx, ∀ φ : ℝ, ∀ Y : FockOp (Ts.T N), IsSelfAdjoint Y →
      NormedSpace.exp ((I * (φ : ℂ)) • (Qband (Ts.T N) (B N) + Y)) *
        NormedSpace.exp ((-(I * (φ : ℂ))) • Qband (Ts.T N) (B N)) ∈ unitary (FockOp (Ts.T N)) :=
    fun N _ φ Y hY => Submonoid.mul_mem _ (exp_mem_unitary_dev ((hQs N).add hY) (hc1 φ))
      (exp_mem_unitary_dev (hQs N) (hc2 φ))
  have hM := fun φ (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * π)) => asBound_mul_unit_dev hη hδ₀ (hV1 φ hφ)
    (asBound_star hη hδ₀ (hV2 φ hφ)) (fun N hN => norm_toCLM_le_one_dev (hU N hN φ _ (hXUs N hN)))
    (fun N hN => norm_toCLM_le_one_dev (by
      rw [← Matrix.star_eq_conjTranspose]
      exact Unitary.star_mem (hU N hN φ _ (hXs N hN))))
  have hid : ∀ φ : ℝ, ∀ N ∈ Ts.idx,
      NormedSpace.exp ((I * (φ : ℂ)) • (Qband (Ts.T N) (B N) + XU N)) *
          NormedSpace.exp ((-(I * (φ : ℂ))) • Qband (Ts.T N) (B N)) *
        (NormedSpace.exp ((I * (φ : ℂ)) • (Qband (Ts.T N) (B N) + X N)) *
          NormedSpace.exp ((-(I * (φ : ℂ))) • Qband (Ts.T N) (B N)))ᴴ =
      NormedSpace.exp ((I * (φ : ℂ)) • (Qband (Ts.T N) (B N) + XU N)) *
        NormedSpace.exp ((-(I * (φ : ℂ))) • (Qband (Ts.T N) (B N) + X N)) := by
    intro φ N hN
    rw [Matrix.conjTranspose_mul, conjTranspose_exp_smul_dev (hQs N), conjTranspose_exp_smul_dev ((hQs N).add (hXs N hN)),
      hc1, hc2, neg_neg, mul_assoc, ← mul_assoc (NormedSpace.exp ((-(I * (φ : ℂ))) • Qband (Ts.T N) (B N))),
      (exp_smul_mul_exp_neg_dev (Qband (Ts.T N) (B N)) (I * (φ : ℂ))).2, one_mul]
  have h2π : (2 * π : ℝ) ∈ Set.Icc (0 : ℝ) (2 * π) := ⟨by positivity, le_rfl⟩
  have hO : ∀ N ∈ Ts.idx, NormedSpace.exp ((I * ((2 * π : ℝ) : ℂ)) • (Qband (Ts.T N) (B N) + X N)) *
      NormedSpace.exp ((-(I * ((2 * π : ℝ) : ℂ))) • Qband (Ts.T N) (B N)) =
      NormedSpace.exp ((2 * π * I : ℂ) • (Qband (Ts.T N) (B N) + X N)) := by
    intro N _
    have e1 : (I * ((2 * π : ℝ) : ℂ)) = (2 * π * I : ℂ) := by push_cast; ring
    have e2 : (-(I * ((2 * π : ℝ) : ℂ))) • Qband (Ts.T N) (B N) = -((2 * π * I : ℂ) • Qband (Ts.T N) (B N)) := by
      rw [e1, neg_smul]
    rw [e2, e1, Matrix.exp_neg, exp_Qband, inv_one, mul_one]
  have hOs : ∀ N ∈ Ts.idx, (NormedSpace.exp ((2 * π * I : ℂ) • (Qband (Ts.T N) (B N) + X N)))ᴴ =
      NormedSpace.exp ((-(2 * π * I : ℂ)) • (Qband (Ts.T N) (B N) + X N)) := by
    intro N hN
    have hc : starRingEnd ℂ (2 * π * I : ℂ) = -(2 * π * I : ℂ) := by
      rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      ring
    rw [conjTranspose_exp_smul_dev ((hQs N).add (hXs N hN)), hc]
  have hO2 := asBound_congr (hV2 (2 * π) h2π) hO
  refine ⟨fun k => |C1 k| + 2 * |C2 k| + |C2 k|, fun φ hφ => ?_, ?_, ?_⟩
  · have h := asBound_congr (hM φ hφ) (hid φ)
    rw [max_self] at h
    exact asBound_mono_const h fun k => by linarith [abs_nonneg (C2 k)]
  · exact asBound_mono_const hO2 fun k => by linarith [abs_nonneg (C1 k), abs_nonneg (C2 k), le_abs_self (C2 k)]
  · exact asBound_mono_const (asBound_congr (asBound_star hη hδ₀ hO2) hOs)
      fun k => by linarith [abs_nonneg (C1 k), abs_nonneg (C2 k), le_abs_self (C2 k)]

end MDevices

/-- **Lemma 6.12**, the row "`$\Qb_\pm$, $\Qb^U_\pm$ & $\le CN^2$ & $\Col\Gamma_\pm\cup\partial_\pm$ & $5/2$`" for `U = Θ`. -/
theorem table_Qbar (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    (∀ N ∈ D.Ts.idx, IsEven (D.QbarMinus N) ∧ IsSectorPreserving (D.T N) (D.QbarMinus N) ∧
      IsEven (D.QbarPlus N) ∧ IsSectorPreserving (D.T N) (D.QbarPlus N) ∧
      IsEven (D.QbarUMinus N) ∧ IsSectorPreserving (D.T N) (D.QbarUMinus N) ∧
      IsEven (D.QbarUPlus N) ∧ IsSectorPreserving (D.T N) (D.QbarUPlus N)) ∧
    (∃ C : ℝ, ∀ N ∈ D.Ts.idx, ‖toCLM (D.T N) (D.QbarMinus N)‖ ≤ C * (N : ℝ) ^ 2 ∧
      ‖toCLM (D.T N) (D.QbarPlus N)‖ ≤ C * (N : ℝ) ^ 2 ∧ ‖toCLM (D.T N) (D.QbarUMinus N)‖ ≤ C * (N : ℝ) ^ 2 ∧
      ‖toCLM (D.T N) (D.QbarUPlus N)‖ ≤ C * (N : ℝ) ^ 2) ∧
    ∃ C : ℕ → ℝ,
      ASBound η δ₀ D.Ts (fun N => colBand δ₀ (D.T N) (quarterMinus (D.T N).Nφ N) ∪ D.cutMinus N) D.QbarMinus
          (5 / 2) C ∧
        ASBound η δ₀ D.Ts (fun N => colBand δ₀ (D.T N) (quarterPlus (D.T N).Nφ N) ∪ D.cutPlus N) D.QbarPlus
          (5 / 2) C ∧
        ASBound η δ₀ D.Ts (fun N => colBand δ₀ (D.T N) (quarterMinus (D.T N).Nφ N) ∪ D.cutMinus N) D.QbarUMinus
          (5 / 2) C ∧
        ASBound η δ₀ D.Ts (fun N => colBand δ₀ (D.T N) (quarterPlus (D.T N).Nφ N) ∪ D.cutPlus N) D.QbarUPlus
          (5 / 2) C := by
  obtain ⟨hQe, -, hQmAS, -, hQpAS⟩ := table_Q hη hδ₀ D.toIxSetting
  obtain ⟨hTe, hTmAS, hTpAS⟩ := table_T hη hδ₀ D
  obtain ⟨hKe, ⟨CK, hKn⟩, CKa, hKmAS, hKpAS, hKUmAS, hKUpAS⟩ := table_K hη hδ₀ D hD hH2
  have hmono : ∀ {X Y : (N : ℕ) → Finset (Slot δ₀ (D.T N))} {A : (N : ℕ) → FockOp (D.T N)} {m : ℝ}
      {C : ℕ → ℝ}, (∀ N, X N ⊆ Y N) → ASBound η δ₀ D.Ts X A m C → ASBound η δ₀ D.Ts Y A m C :=
    fun hXY h => ⟨h.1, fun k N hN r hr => by
      obtain ⟨A', hA', hb⟩ := h.2 k N hN r hr
      exact ⟨A', Alg_mono (fat_mono_left (hXY N) r) hA', hb⟩⟩
  have h0 : max (0 : ℝ) (5 / 2) = 5 / 2 := by norm_num
  have h00 : max (max (0 : ℝ) 0) (5 / 2) = 5 / 2 := by norm_num
  have a1 := asBound_sub_dev hη hδ₀ (hmono (fun N => Finset.subset_union_left) hQmAS)
    (hmono (fun N => Finset.subset_union_right) hKmAS)
  have a2 := asBound_sub_dev hη hδ₀ (hmono (fun N => Finset.subset_union_left) hQpAS)
    (hmono (fun N => Finset.subset_union_right) hKpAS)
  have a3 := asBound_sub_dev hη hδ₀ (asBound_add hη hδ₀ (hmono (fun N => Finset.subset_union_left) hQmAS)
    (hmono (fun N => Finset.subset_union_right) hTmAS)) (hmono (fun N => Finset.subset_union_right) hKUmAS)
  have a4 := asBound_sub_dev hη hδ₀ (asBound_add hη hδ₀ (hmono (fun N => Finset.subset_union_left) hQpAS)
    (hmono (fun N => Finset.subset_union_right) hTpAS)) (hmono (fun N => Finset.subset_union_right) hKUpAS)
  rw [h0] at a1 a2
  rw [h00] at a3 a4
  have hN2 : ∀ N ∈ D.Ts.idx, (N : ℝ) ≤ (N : ℝ) ^ 2 ∧ (1 : ℝ) ≤ (N : ℝ) ^ 2 := fun N hN => by
    have hN1 := one_le_of_mem_idx D.Ts hN
    constructor <;> nlinarith
  refine ⟨fun N hN => ?_, ⟨2 + |CK|, fun N hN => ?_⟩, fun k => |(fun _ => (0 : ℝ)) k| + |(fun _ => (0 : ℝ)) k| +
    |CKa k| + |CKa k|, asBound_mono_const a1 fun k => ?_, asBound_mono_const a2 fun k => ?_,
    asBound_mono_const a3 fun k => ?_, asBound_mono_const a4 fun k => ?_⟩
  · have p1 : IsSectorPreserving (D.T N) (D.QbarMinus N) :=
      sp_sub_dev (Qband_isSectorPreserving _ _) (hKe N hN).2.1
    have p2 : IsSectorPreserving (D.T N) (D.QbarPlus N) :=
      sp_sub_dev (Qband_isSectorPreserving _ _) (hKe N hN).2.2.2.1
    have p3 : IsSectorPreserving (D.T N) (D.QbarUMinus N) :=
      sp_sub_dev (sp_add_dev (Qband_isSectorPreserving _ _) (hTe N hN).2.1) (hKe N hN).2.2.2.2.2.1
    have p4 : IsSectorPreserving (D.T N) (D.QbarUPlus N) :=
      sp_sub_dev (sp_add_dev (Qband_isSectorPreserving _ _) (hTe N hN).2.2.2.2.1) (hKe N hN).2.2.2.2.2.2.2
    exact ⟨p1.isEven, p1, p2.isEven, p2, p3.isEven, p3, p4.isEven, p4⟩
  · obtain ⟨n1, n2, n3, n4⟩ := hKn N hN
    have qm := (hQe N hN).2.2.2.2.2.1
    have qp := (hQe N hN).2.2.2.2.2.2.2.2.2.2.2
    have tm := (hTe N hN).2.2.1
    have tp := (hTe N hN).2.2.2.2.2
    obtain ⟨hNa, hNb⟩ := hN2 N hN
    have hCK : CK * (N : ℝ) ^ 2 ≤ |CK| * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    unfold ArgData.QbarMinus ArgData.QbarPlus ArgData.QbarUMinus ArgData.QbarUPlus
    simp only [toCLM_sub', toCLM_add_dev]
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith [norm_sub_le (toCLM (D.T N) (D.Qminus N)) (toCLM (D.T N) (D.Km N))]
    · nlinarith [norm_sub_le (toCLM (D.T N) (D.Qplus N)) (toCLM (D.T N) (D.Kp N))]
    · nlinarith [norm_sub_le (toCLM (D.T N) (D.Qminus N) + toCLM (D.T N) (D.Tminus N)) (toCLM (D.T N) (D.KUminus N)),
        norm_add_le (toCLM (D.T N) (D.Qminus N)) (toCLM (D.T N) (D.Tminus N))]
    · nlinarith [norm_sub_le (toCLM (D.T N) (D.Qplus N) + toCLM (D.T N) (D.Tplus N)) (toCLM (D.T N) (D.KUplus N)),
        norm_add_le (toCLM (D.T N) (D.Qplus N)) (toCLM (D.T N) (D.Tplus N))]
  all_goals simp only [abs_zero, zero_add]
  all_goals linarith [abs_nonneg (CKa k)]

/-- **Lemma 6.12**, the row "`$\Tt$ & $\le CN^2$ & $\cutm$ & $5/2$`" for `U = Θ`. -/
theorem table_Ttilde (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    (∀ N ∈ D.Ts.idx, IsEven (D.Ttilde N) ∧ IsSectorPreserving (D.T N) (D.Ttilde N)) ∧
    (∃ C : ℝ, ∀ N ∈ D.Ts.idx, ‖toCLM (D.T N) (D.Ttilde N)‖ ≤ C * (N : ℝ) ^ 2) ∧
    ∃ C : ℕ → ℝ, ASBound η δ₀ D.Ts D.cutMinus D.Ttilde (5 / 2) C := by
  obtain ⟨hTe, hTmAS, -⟩ := table_T hη hδ₀ D
  obtain ⟨hKe, ⟨CK, hKn⟩, CKa, hKmAS, -, hKUmAS, -⟩ := table_K hη hδ₀ D hD hH2
  have a := asBound_add hη hδ₀ (asBound_sub_dev hη hδ₀ hTmAS hKUmAS) hKmAS
  have h0 : max (max (0 : ℝ) (5 / 2)) (5 / 2) = 5 / 2 := by norm_num
  rw [h0] at a
  refine ⟨fun N hN => ?_, ⟨1 + 2 * |CK|, fun N hN => ?_⟩, _, a⟩
  · have p : IsSectorPreserving (D.T N) (D.Ttilde N) :=
      sp_add_dev (sp_sub_dev (hTe N hN).2.1 (hKe N hN).2.2.2.2.2.1) (hKe N hN).2.1
    exact ⟨p.isEven, p⟩
  · obtain ⟨n1, -, n3, -⟩ := hKn N hN
    have tm := (hTe N hN).2.2.1
    have hN1 := one_le_of_mem_idx D.Ts hN
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hCK : CK * (N : ℝ) ^ 2 ≤ |CK| * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    unfold ArgData.Ttilde
    rw [toCLM_add_dev, toCLM_sub']
    have h1 := norm_add_le (toCLM (D.T N) (D.Tminus N) - toCLM (D.T N) (D.KUminus N)) (toCLM (D.T N) (D.Km N))
    have h2 := norm_sub_le (toCLM (D.T N) (D.Tminus N)) (toCLM (D.T N) (D.KUminus N))
    nlinarith

/-- **Lemma 6.12**, the row "`$\mathcal M_\pm(\varphi)$, $e^{\pm2\pi\iu\Qb_\pm}$ (unitary) & $1$ & $\partial_\pm$ & $5/2$`" for
`U = Θ`, "`uniformly in $\varphi\in[0,2\pi]$`" (one set of constants for every `φ`). -/
theorem table_M (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    (∀ N ∈ D.Ts.idx, ∀ φ : ℝ,
      D.Mminus φ N ∈ unitary (FockOp (D.T N)) ∧ IsEven (D.Mminus φ N) ∧
        IsSectorPreserving (D.T N) (D.Mminus φ N) ∧
      D.Mplus φ N ∈ unitary (FockOp (D.T N)) ∧ IsEven (D.Mplus φ N) ∧
        IsSectorPreserving (D.T N) (D.Mplus φ N)) ∧
    (∀ N ∈ D.Ts.idx,
      D.Ominus N ∈ unitary (FockOp (D.T N)) ∧ IsEven (D.Ominus N) ∧ IsSectorPreserving (D.T N) (D.Ominus N) ∧
      D.Oplus N ∈ unitary (FockOp (D.T N)) ∧ IsEven (D.Oplus N) ∧ IsSectorPreserving (D.T N) (D.Oplus N)) ∧
    ∃ C : ℕ → ℝ,
      (∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
        ASBound η δ₀ D.Ts D.cutMinus (D.Mminus φ) (5 / 2) C ∧ ASBound η δ₀ D.Ts D.cutPlus (D.Mplus φ) (5 / 2) C) ∧
      ASBound η δ₀ D.Ts D.cutMinus D.Ominus (5 / 2) C ∧ ASBound η δ₀ D.Ts D.cutPlus D.Oplus (5 / 2) C ∧
      ASBound η δ₀ D.Ts D.cutMinus (fun N => NormedSpace.exp ((-(2 * π * I : ℂ)) • D.QbarMinus N)) (5 / 2) C ∧
      ASBound η δ₀ D.Ts D.cutPlus (fun N => NormedSpace.exp ((-(2 * π * I : ℂ)) • D.QbarPlus N)) (5 / 2) C := by
  have hγ : 0 < D.γ := by linarith [hD.gap.Δ_nonneg, hD.gap.two_mul_Δ_lt]
  obtain ⟨hTe, hTmAS, hTpAS⟩ := table_T hη hδ₀ D
  obtain ⟨hKe, ⟨CK, hKn⟩, CKa, hKmAS, hKpAS, hKUmAS, hKUpAS⟩ := table_K hη hδ₀ D hD hH2
  have hsa : ∀ N ∈ D.Ts.idx, IsSelfAdjoint (D.Tminus N) ∧ IsSelfAdjoint (D.Tplus N) ∧
      IsSelfAdjoint (D.Km N) ∧ IsSelfAdjoint (D.Kp N) ∧ IsSelfAdjoint (D.KUminus N) ∧
      IsSelfAdjoint (D.KUplus N) := by
    intro N hN
    have hH := D.d.H_isSelfAdjoint N hN
    have hHs := H_isSectorPreserving_dev D.toIxSetting hN
    obtain ⟨k1, -, k3, -⟩ := K_isSelfAdjoint hD.cutoff hγ D.toIxSetting N hN
    obtain ⟨-, j1, j2, j3, j4, -, -⟩ := JShift_props D.toIxSetting 1 N hN
    obtain ⟨u1, -⟩ := dress_props_dev hD.cutoff hγ hH hHs j1 j2
    obtain ⟨u3, -⟩ := dress_props_dev hD.cutoff hγ hH hHs j3 j4
    obtain ⟨e1, e2⟩ := KU_eq_dev D hD hH2 hN
    refine ⟨(isStarProjection_njs (D.T N) 0 .up).isSelfAdjoint.neg,
      (isStarProjection_njs (D.T N) _ .up).isSelfAdjoint, k1, k3, ?_, ?_⟩
    · rw [e1]
      exact u1
    · rw [e2]
      exact u3
  -- the norms of `Ξ^U_∓ = T_∓ − K^U_∓` and `Ξ_∓ = −K_∓`
  have hpow : ∀ N ∈ D.Ts.idx, (1 : ℝ) ≤ (N : ℝ) ^ (5 / 2 : ℝ) ∧ (N : ℝ) ^ 2 ≤ (N : ℝ) ^ (5 / 2 : ℝ) := by
    intro N hN
    have hN1 := one_le_of_mem_idx D.Ts hN
    refine ⟨Real.one_le_rpow hN1 (by norm_num), ?_⟩
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hnK : ∀ N ∈ D.Ts.idx, ∀ Y : FockOp (D.T N), ‖toCLM (D.T N) Y‖ ≤ CK * (N : ℝ) ^ 2 →
      1 + ‖toCLM (D.T N) Y‖ ≤ (1 + |CK|) * (N : ℝ) ^ (5 / 2 : ℝ) := fun N hN Y hY => by
    have h1 : CK * (N : ℝ) ^ 2 ≤ |CK| * (N : ℝ) ^ (5 / 2 : ℝ) :=
      mul_le_mul (le_abs_self _) (hpow N hN).2 (by positivity) (abs_nonneg _)
    nlinarith [(hpow N hN).1]
  have hnT : ∀ N ∈ D.Ts.idx, ∀ Tt Y : FockOp (D.T N), ‖toCLM (D.T N) Tt‖ = 1 →
      ‖toCLM (D.T N) Y‖ ≤ CK * (N : ℝ) ^ 2 →
      ‖toCLM (D.T N) (Tt - Y)‖ ≤ (1 + |CK|) * (N : ℝ) ^ (5 / 2 : ℝ) := fun N hN Tt Y hT hY => by
    rw [toCLM_sub']
    exact (norm_sub_le _ _).trans (by rw [hT]; exact hnK N hN Y hY)
  have hnN : ∀ N ∈ D.Ts.idx, ∀ Y : FockOp (D.T N), ‖toCLM (D.T N) Y‖ ≤ CK * (N : ℝ) ^ 2 →
      ‖toCLM (D.T N) (-Y)‖ ≤ (1 + |CK|) * (N : ℝ) ^ (5 / 2 : ℝ) := fun N hN Y hY => by
    rw [toCLM_neg_dev, norm_neg]
    linarith [hnK N hN Y hY]
  have h52 : max (0 : ℝ) (5 / 2) = 5 / 2 := by norm_num
  have hXUm := asBound_sub_dev hη hδ₀ hTmAS hKUmAS
  have hXUp := asBound_sub_dev hη hδ₀ hTpAS hKUpAS
  rw [h52] at hXUm hXUp
  have hXm := asBound_congr (asBound_smul hη hδ₀ hKmAS (-1)) fun N _ => neg_one_smul ℂ (D.Km N)
  have hXp := asBound_congr (asBound_smul hη hδ₀ hKpAS (-1)) fun N _ => neg_one_smul ℂ (D.Kp N)
  obtain ⟨Cm, hCm1, hCm2, hCm3⟩ := Mrow_dev hη hδ₀ D.Ts (fun _ => 0) (fun N => quarterMinus (D.T N).Nφ N)
    (fun N => D.Tminus N - D.KUminus N) (fun N => -D.Km N)
    (fun N hN => (hsa N hN).1.sub (hsa N hN).2.2.2.2.1) (fun N hN => (hsa N hN).2.2.1.neg) hXUm hXm
    (fun N hN => hnT N hN _ _ (hTe N hN).2.2.1 (hKn N hN).2.2.1) (fun N hN => hnN N hN _ (hKn N hN).1)
  obtain ⟨Cp, hCp1, hCp2, hCp3⟩ := Mrow_dev hη hδ₀ D.Ts (fun N => (N : ℤ)) (fun N => quarterPlus (D.T N).Nφ N)
    (fun N => D.Tplus N - D.KUplus N) (fun N => -D.Kp N)
    (fun N hN => (hsa N hN).2.1.sub (hsa N hN).2.2.2.2.2) (fun N hN => (hsa N hN).2.2.2.1.neg) hXUp hXp
    (fun N hN => hnT N hN _ _ (hTe N hN).2.2.2.2.2 (hKn N hN).2.2.2) (fun N hN => hnN N hN _ (hKn N hN).2.1)
  -- the identifications
  have eUm : ∀ N, D.QbarUMinus N = Qband (D.T N) (quarterMinus (D.T N).Nφ N) + (D.Tminus N - D.KUminus N) :=
    fun N => add_sub_assoc _ _ _
  have eUp : ∀ N, D.QbarUPlus N = Qband (D.T N) (quarterPlus (D.T N).Nφ N) + (D.Tplus N - D.KUplus N) :=
    fun N => add_sub_assoc _ _ _
  have eBm : ∀ N, D.QbarMinus N = Qband (D.T N) (quarterMinus (D.T N).Nφ N) + -D.Km N :=
    fun N => sub_eq_add_neg _ _
  have eBp : ∀ N, D.QbarPlus N = Qband (D.T N) (quarterPlus (D.T N).Nφ N) + -D.Kp N :=
    fun N => sub_eq_add_neg _ _
  -- self-adjointness and sector preservation of `Q̄_∓`, `Q̄^U_∓`
  have hsaQ : ∀ N ∈ D.Ts.idx, IsSelfAdjoint (D.QbarUMinus N) ∧ IsSelfAdjoint (D.QbarMinus N) ∧
      IsSelfAdjoint (D.QbarUPlus N) ∧ IsSelfAdjoint (D.QbarPlus N) := by
    intro N hN
    rw [eUm, eBm, eUp, eBp]
    exact ⟨(Qband_isSelfAdjoint _ _).add ((hsa N hN).1.sub (hsa N hN).2.2.2.2.1),
      (Qband_isSelfAdjoint _ _).add (hsa N hN).2.2.1.neg,
      (Qband_isSelfAdjoint _ _).add ((hsa N hN).2.1.sub (hsa N hN).2.2.2.2.2),
      (Qband_isSelfAdjoint _ _).add (hsa N hN).2.2.2.1.neg⟩
  have hspQ : ∀ N ∈ D.Ts.idx, IsSectorPreserving (D.T N) (D.QbarUMinus N) ∧
      IsSectorPreserving (D.T N) (D.QbarMinus N) ∧ IsSectorPreserving (D.T N) (D.QbarUPlus N) ∧
      IsSectorPreserving (D.T N) (D.QbarPlus N) := by
    intro N hN
    exact ⟨sp_sub_dev (sp_add_dev (Qband_isSectorPreserving _ _) (hTe N hN).2.1) (hKe N hN).2.2.2.2.2.1,
      sp_sub_dev (Qband_isSectorPreserving _ _) (hKe N hN).2.1,
      sp_sub_dev (sp_add_dev (Qband_isSectorPreserving _ _) (hTe N hN).2.2.2.2.1) (hKe N hN).2.2.2.2.2.2.2,
      sp_sub_dev (Qband_isSectorPreserving _ _) (hKe N hN).2.2.2.1⟩
  have hc1 : ∀ φ : ℝ, starRingEnd ℂ (I * (φ : ℂ)) = -(I * (φ : ℂ)) := fun φ => by simp
  have hc2 : ∀ φ : ℝ, starRingEnd ℂ (-(I * (φ : ℂ))) = -(-(I * (φ : ℂ))) := fun φ => by simp
  have hc3 : starRingEnd ℂ (2 * π * I : ℂ) = -(2 * π * I : ℂ) := by
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  refine ⟨fun N hN φ => ?_, fun N hN => ?_, fun k => |Cm k| + |Cp k|, fun φ hφ => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s1, s2, s3, s4⟩ := hsaQ N hN
    obtain ⟨p1, p2, p3, p4⟩ := hspQ N hN
    have hm : IsSectorPreserving (D.T N) (D.Mminus φ N) := sp_mul_dev (sp_exp_dev p1 _) (sp_exp_dev p2 _)
    have hp : IsSectorPreserving (D.T N) (D.Mplus φ N) := sp_mul_dev (sp_exp_dev p3 _) (sp_exp_dev p4 _)
    exact ⟨Submonoid.mul_mem _ (exp_mem_unitary_dev s1 (hc1 φ)) (exp_mem_unitary_dev s2 (hc2 φ)), hm.isEven, hm,
      Submonoid.mul_mem _ (exp_mem_unitary_dev s3 (hc1 φ)) (exp_mem_unitary_dev s4 (hc2 φ)), hp.isEven, hp⟩
  · obtain ⟨-, s2, -, s4⟩ := hsaQ N hN
    obtain ⟨-, p2, -, p4⟩ := hspQ N hN
    have hm : IsSectorPreserving (D.T N) (D.Ominus N) := sp_exp_dev p2 _
    have hp : IsSectorPreserving (D.T N) (D.Oplus N) := sp_exp_dev p4 _
    exact ⟨exp_mem_unitary_dev s2 hc3, hm.isEven, hm, exp_mem_unitary_dev s4 hc3, hp.isEven, hp⟩
  · refine asBound_mono_const (asBound_congr (hCm1 φ hφ) fun N _ => ?_) fun k => ?_
    · unfold ArgData.Mminus
      rw [eUm, eBm]
    · linarith [abs_nonneg (Cp k), le_abs_self (Cm k)]
  · refine asBound_mono_const (asBound_congr (hCp1 φ hφ) fun N _ => ?_) fun k => ?_
    · unfold ArgData.Mplus
      rw [eUp, eBp]
    · linarith [abs_nonneg (Cm k), le_abs_self (Cp k)]
  · refine asBound_mono_const (asBound_congr hCm2 fun N _ => ?_) fun k => ?_
    · unfold ArgData.Ominus
      rw [eBm]
    · linarith [abs_nonneg (Cp k), le_abs_self (Cm k)]
  · refine asBound_mono_const (asBound_congr hCp2 fun N _ => ?_) fun k => ?_
    · unfold ArgData.Oplus
      rw [eBp]
    · linarith [abs_nonneg (Cm k), le_abs_self (Cp k)]
  · refine asBound_mono_const (asBound_congr hCm3 fun N _ => ?_) fun k => ?_
    · rw [eBm]
    · linarith [abs_nonneg (Cp k), le_abs_self (Cm k)]
  · refine asBound_mono_const (asBound_congr hCp3 fun N _ => ?_) fun k => ?_
    · rw [eBp]
    · linarith [abs_nonneg (Cm k), le_abs_self (Cp k)]

/-- **Lemma 6.12**, the row "`$\Qf(V)$, $\Qf(V^*)$, $V\in\{\mathcal M_\pm(\varphi),e^{2\pi\iu\Qb_\pm}\}$ & $\le CN$ & $\partial_\pm$ & $\le9/2$`"
for `U = Θ`, uniformly in `φ ∈ [0, 2π]`: even, sector-preserving, norm at most `CN`, almost supported in the cut with
prefactor exponent `9/2` ("`one may take $m_*=9/2$`"). -/
theorem table_Qf (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    (∀ N ∈ D.Ts.idx, ∀ φ : ℝ,
      IsEven (D.Qf N (D.Mminus φ N)) ∧ IsSectorPreserving (D.T N) (D.Qf N (D.Mminus φ N)) ∧
      IsEven (D.Qf N ((D.Mminus φ N)ᴴ)) ∧ IsSectorPreserving (D.T N) (D.Qf N ((D.Mminus φ N)ᴴ)) ∧
      IsEven (D.Qf N (D.Mplus φ N)) ∧ IsSectorPreserving (D.T N) (D.Qf N (D.Mplus φ N)) ∧
      IsEven (D.Qf N ((D.Mplus φ N)ᴴ)) ∧ IsSectorPreserving (D.T N) (D.Qf N ((D.Mplus φ N)ᴴ))) ∧
    (∀ N ∈ D.Ts.idx,
      IsEven (D.Qf N (D.Ominus N)) ∧ IsSectorPreserving (D.T N) (D.Qf N (D.Ominus N)) ∧
      IsEven (D.Qf N ((D.Ominus N)ᴴ)) ∧ IsSectorPreserving (D.T N) (D.Qf N ((D.Ominus N)ᴴ)) ∧
      IsEven (D.Qf N (D.Oplus N)) ∧ IsSectorPreserving (D.T N) (D.Qf N (D.Oplus N)) ∧
      IsEven (D.Qf N ((D.Oplus N)ᴴ)) ∧ IsSectorPreserving (D.T N) (D.Qf N ((D.Oplus N)ᴴ))) ∧
    (∃ C : ℝ, ∀ N ∈ D.Ts.idx, (∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
        ‖toCLM (D.T N) (D.Qf N (D.Mminus φ N))‖ ≤ C * N ∧ ‖toCLM (D.T N) (D.Qf N ((D.Mminus φ N)ᴴ))‖ ≤ C * N ∧
        ‖toCLM (D.T N) (D.Qf N (D.Mplus φ N))‖ ≤ C * N ∧ ‖toCLM (D.T N) (D.Qf N ((D.Mplus φ N)ᴴ))‖ ≤ C * N) ∧
      ‖toCLM (D.T N) (D.Qf N (D.Ominus N))‖ ≤ C * N ∧ ‖toCLM (D.T N) (D.Qf N ((D.Ominus N)ᴴ))‖ ≤ C * N ∧
      ‖toCLM (D.T N) (D.Qf N (D.Oplus N))‖ ≤ C * N ∧ ‖toCLM (D.T N) (D.Qf N ((D.Oplus N)ᴴ))‖ ≤ C * N) ∧
    ∃ C : ℕ → ℝ,
      (∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
        ASBound η δ₀ D.Ts D.cutMinus (fun N => D.Qf N (D.Mminus φ N)) (9 / 2) C ∧
        ASBound η δ₀ D.Ts D.cutMinus (fun N => D.Qf N ((D.Mminus φ N)ᴴ)) (9 / 2) C ∧
        ASBound η δ₀ D.Ts D.cutPlus (fun N => D.Qf N (D.Mplus φ N)) (9 / 2) C ∧
        ASBound η δ₀ D.Ts D.cutPlus (fun N => D.Qf N ((D.Mplus φ N)ᴴ)) (9 / 2) C) ∧
      ASBound η δ₀ D.Ts D.cutMinus (fun N => D.Qf N (D.Ominus N)) (9 / 2) C ∧
      ASBound η δ₀ D.Ts D.cutMinus (fun N => D.Qf N ((D.Ominus N)ᴴ)) (9 / 2) C ∧
      ASBound η δ₀ D.Ts D.cutPlus (fun N => D.Qf N (D.Oplus N)) (9 / 2) C ∧
      ASBound η δ₀ D.Ts D.cutPlus (fun N => D.Qf N ((D.Oplus N)ᴴ)) (9 / 2) C := by
  obtain ⟨hMu, hOu, CM, hMAS, hOmAS, hOpAS, -, -⟩ := table_M hη hδ₀ D hD hH2
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = max 1 ((4 * δ₀ / π + 1 / 2) * (4 * π / D.cstar)) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C₀ := by rw [hC₀]; exact le_max_left _ _
  have hC2 : (4 * δ₀ / π + 1 / 2) * (4 * π / D.cstar) ≤ C₀ := by rw [hC₀]; exact le_max_right _ _
  obtain ⟨C'k, C', hC'⟩ := almostSupported_clusterFilter hδ₀ hD.clust C₀ (5 / 2) 0 (1 / 2) (by norm_num) CM
    D.d.Ch D.d.CH
  have he : (1 + max (5 / 2 : ℝ) 0 + 1 / 2) ≤ 9 / 2 := by norm_num
  have hmono : ∀ {X : (N : ℕ) → Finset (Slot δ₀ (D.T N))} {A : (N : ℕ) → FockOp (D.T N)} {m m' : ℝ}
      {C : ℕ → ℝ}, m ≤ m' → ASBound η δ₀ D.Ts X A m C → ASBound η δ₀ D.Ts X A m' (fun k => |C k|) :=
    fun hmm h => ⟨h.1.trans hmm, fun k N hN r hr => by
      obtain ⟨A', hA', hb⟩ := h.2 k N hN r hr
      refine ⟨A', hA', hb.trans ?_⟩
      have hN1 := one_le_of_mem_idx D.Ts hN
      have hρ : 0 ≤ (1 + r) ^ (-(k : ℝ)) := Real.rpow_nonneg (by linarith) _
      exact mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hN1 hmm)
        (Real.rpow_nonneg (by linarith) _) (abs_nonneg _)) hρ⟩
  have key : ∀ (j : ℕ → ℤ) (V : (N : ℕ) → FockOp (D.T N)), (∀ N ∈ D.Ts.idx, V N ∈ unitary (FockOp (D.T N))) →
      (∀ N ∈ D.Ts.idx, IsSectorPreserving (D.T N) (V N)) →
      ASBound η δ₀ D.Ts (fun N => col δ₀ (D.T N) (j N)) V (5 / 2) CM →
      ASBound η δ₀ D.Ts (fun N => col δ₀ (D.T N) (j N)) (fun N => D.Qf N (V N)) (9 / 2) (fun k => |C'k k|) ∧
        ∀ N ∈ D.Ts.idx, ‖toCLM (D.T N) (D.Qf N (V N))‖ ≤ C' * N := by
    intro j V hVu hVs hVa
    have h := hC' η hη D.Ts D.H D.d rfl rfl _ V (fun N hN => (hVs N hN).isEven) hVa
      (fun N hN => by
        rw [Real.rpow_zero, mul_one]
        exact (norm_toCLM_le_one_dev (hVu N hN)).trans hC1)
      (fun N hN => (card_col_le_dev hδ₀ D.toIxSetting (j N) hN).trans
        (mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg (Nat.cast_nonneg N) _)))
    refine ⟨hmono he h.1, fun N hN => ?_⟩
    have h2 := h.2 N hN
    rwa [add_zero, Real.rpow_one] at h2
  have hstar : ∀ N ∈ D.Ts.idx, ∀ U : FockOp (D.T N), U ∈ unitary (FockOp (D.T N)) → Uᴴ ∈ unitary (FockOp (D.T N)) :=
    fun N _ U hU => by
      rw [← Matrix.star_eq_conjTranspose]
      exact Unitary.star_mem hU
  have hsp : ∀ N ∈ D.Ts.idx, ∀ V : FockOp (D.T N), IsSectorPreserving (D.T N) V →
      IsEven (D.Qf N V) ∧ IsSectorPreserving (D.T N) (D.Qf N V) := fun N hN V hV => by
    have h := isSectorPreserving_specSum_dev (D.d.H_isSelfAdjoint N hN) (H_isSectorPreserving_dev D.toIxSetting hN)
      hV (fun E E' => ((gClust D.γ D.ζ (E - E') : ℝ) : ℂ))
    exact ⟨h.isEven, h⟩
  have kM1 := fun φ (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * π)) => key (fun _ => 0) (D.Mminus φ)
    (fun N hN => (hMu N hN φ).1) (fun N hN => (hMu N hN φ).2.2.1) (hMAS φ hφ).1
  have kM2 := fun φ (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * π)) => key (fun _ => 0) (fun N => (D.Mminus φ N)ᴴ)
    (fun N hN => hstar N hN _ (hMu N hN φ).1) (fun N hN => sp_conjTranspose_dev (hMu N hN φ).2.2.1)
    (asBound_star hη hδ₀ (hMAS φ hφ).1)
  have kM3 := fun φ (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * π)) => key (fun N => (N : ℤ)) (D.Mplus φ)
    (fun N hN => (hMu N hN φ).2.2.2.1) (fun N hN => (hMu N hN φ).2.2.2.2.2) (hMAS φ hφ).2
  have kM4 := fun φ (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * π)) => key (fun N => (N : ℤ)) (fun N => (D.Mplus φ N)ᴴ)
    (fun N hN => hstar N hN _ (hMu N hN φ).2.2.2.1) (fun N hN => sp_conjTranspose_dev (hMu N hN φ).2.2.2.2.2)
    (asBound_star hη hδ₀ (hMAS φ hφ).2)
  have kO1 := key (fun _ => 0) D.Ominus (fun N hN => (hOu N hN).1) (fun N hN => (hOu N hN).2.2.1) hOmAS
  have kO2 := key (fun _ => 0) (fun N => (D.Ominus N)ᴴ) (fun N hN => hstar N hN _ (hOu N hN).1)
    (fun N hN => sp_conjTranspose_dev (hOu N hN).2.2.1) (asBound_star hη hδ₀ hOmAS)
  have kO3 := key (fun N => (N : ℤ)) D.Oplus (fun N hN => (hOu N hN).2.2.2.1) (fun N hN => (hOu N hN).2.2.2.2.2)
    hOpAS
  have kO4 := key (fun N => (N : ℤ)) (fun N => (D.Oplus N)ᴴ) (fun N hN => hstar N hN _ (hOu N hN).2.2.2.1)
    (fun N hN => sp_conjTranspose_dev (hOu N hN).2.2.2.2.2) (asBound_star hη hδ₀ hOpAS)
  refine ⟨fun N hN φ => ?_, fun N hN => ?_, ⟨C', fun N hN => ⟨fun φ hφ => ⟨(kM1 φ hφ).2 N hN, (kM2 φ hφ).2 N hN,
    (kM3 φ hφ).2 N hN, (kM4 φ hφ).2 N hN⟩, kO1.2 N hN, kO2.2 N hN, kO3.2 N hN, kO4.2 N hN⟩⟩,
    fun k => |C'k k|, fun φ hφ => ⟨(kM1 φ hφ).1, (kM2 φ hφ).1, (kM3 φ hφ).1, (kM4 φ hφ).1⟩, kO1.1, kO2.1, kO3.1, kO4.1⟩
  · obtain ⟨a1, a2⟩ := hsp N hN _ (hMu N hN φ).2.2.1
    obtain ⟨b1, b2⟩ := hsp N hN _ (sp_conjTranspose_dev (hMu N hN φ).2.2.1)
    obtain ⟨c1, c2⟩ := hsp N hN _ (hMu N hN φ).2.2.2.2.2
    obtain ⟨d1, d2⟩ := hsp N hN _ (sp_conjTranspose_dev (hMu N hN φ).2.2.2.2.2)
    exact ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩
  · obtain ⟨a1, a2⟩ := hsp N hN _ (hOu N hN).2.2.1
    obtain ⟨b1, b2⟩ := hsp N hN _ (sp_conjTranspose_dev (hOu N hN).2.2.1)
    obtain ⟨c1, c2⟩ := hsp N hN _ (hOu N hN).2.2.2.2.2
    obtain ⟨d1, d2⟩ := hsp N hN _ (sp_conjTranspose_dev (hOu N hN).2.2.2.2.2)
    exact ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩

/-! ### Lemma 6.13 (commutation relations) for `U = Θ` -/

/-- **Lemma 6.13(i)** (exact relations): "`$\Qb=\Qb_-+Q_m+\Qb_+$ and $\Qb^U=\Qb^U_-+Q_m+\Qb^U_+$; $[Q_-,Q_m]=[Q_m,Q_+]=[Q_-,Q_+]=0$; and for $U=\Theta$ also $[Q_m,T_\pm]=[Q_\mp,T_\pm]=[T_-,T_+]=0$.`" -/
theorem exact_relations (D : ArgData η δ₀) :
    ∀ N ∈ D.Ts.idx,
      D.Qb N = D.QbarMinus N + D.Qmid N + D.QbarPlus N ∧
      D.QbarU N = D.QbarUMinus N + D.Qmid N + D.QbarUPlus N ∧
      Commute (D.Qminus N) (D.Qmid N) ∧ Commute (D.Qmid N) (D.Qplus N) ∧ Commute (D.Qminus N) (D.Qplus N) ∧
      Commute (D.Qmid N) (D.Tminus N) ∧ Commute (D.Qmid N) (D.Tplus N) ∧
      Commute (D.Qplus N) (D.Tminus N) ∧ Commute (D.Qminus N) (D.Tplus N) ∧
      Commute (D.Tminus N) (D.Tplus N) := by
  intro N hN
  have hQ := Q_eq_add_dev D.toIxSetting hN
  have hb : D.Qb N = D.QbarMinus N + D.Qmid N + D.QbarPlus N := by
    unfold ArgData.Qb IxSetting.Qbar ArgData.QbarMinus ArgData.QbarPlus ArgData.Km ArgData.Kp
    rw [hQ]
    abel
  have hbU : D.QbarU N = D.QbarUMinus N + D.Qmid N + D.QbarUPlus N := by
    have e : D.QbarU N = (Θ (D.T N))ᴴ * D.Q N * Θ (D.T N) - D.KUminus N - D.KUplus N := by
      unfold ArgData.QbarU ArgData.KUminus ArgData.KUplus ArgData.Qb IxSetting.Qbar ArgData.Km ArgData.Kp
      simp only [mul_sub, sub_mul]
    rw [e, sub_eq_iff_eq_add.mp (theta_transport_dev D hN)]
    unfold ArgData.QbarUMinus ArgData.QbarUPlus ArgData.Tminus ArgData.Tplus
    rw [hQ]
    abel
  have hQn : ∀ (B : Finset (ZMod (D.T N).Nφ)) (j : ZMod (D.T N).Nφ),
      Commute (Qband (D.T N) B) (njs (D.T N) j .up) :=
    fun B j => Commute.sum_left _ _ _ fun j' _ => commute_njs _ _ _ _ _
  exact ⟨hb, hbU, commute_Qband _ _ _, commute_Qband _ _ _, commute_Qband _ _ _, (hQn _ _).neg_right, hQn _ _,
    (hQn _ _).neg_right, hQn _ _, (commute_njs _ _ _ _ _).neg_left⟩

/-! #### Proof devices for Lemma 6.13(ii) (phase (b), round two; not statements of the paper)

Block C's Lemma 5.13 (`bookkeeping_comm`) for one pair (`comm_isONegInf_dev`, with the common exponent `m_* = 5/2`
and the norm bound `(1 + |C_K|) N^{5/2}`), its orientation swap (`comm_swap_dev`), and the separations of Lemma 6.2 in
the form `d ≥ c√N − C` for every `N ∈ 𝒩` (`sep_all_dev`, `c = c_*/16`, `C = c √N₀` with Lemma 6.2's threshold `N₀`). -/

section SepPairDevices

/-- The constant `C` of the separations `d ≥ (c_*/16)√N − C` (`N₀ = ⌈(96δ₀/c_*)²⌉`). -/
def sepC_dev (δ₀ cstar : ℝ) : ℝ := cstar / 16 * Real.sqrt (⌈(96 * δ₀ / cstar) ^ 2⌉₊ : ℕ)

theorem sep_all_dev (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx) :
    ENNReal.ofReal (S.cstar / 16 * Real.sqrt N - sepC_dev δ₀ S.cstar) ≤
        slotSetDist (col δ₀ (S.T N) 0) (col δ₀ (S.T N) N) ∧
      ENNReal.ofReal (S.cstar / 16 * Real.sqrt N - sepC_dev δ₀ S.cstar) ≤
        slotSetDist (col δ₀ (S.T N) 0) (colBand δ₀ (S.T N) (quarterMid (S.T N).Nφ N)) ∧
      ENNReal.ofReal (S.cstar / 16 * Real.sqrt N - sepC_dev δ₀ S.cstar) ≤
        slotSetDist (col δ₀ (S.T N) N) (colBand δ₀ (S.T N) (quarterMid (S.T N).Nφ N)) ∧
      ENNReal.ofReal (S.cstar / 16 * Real.sqrt N - sepC_dev δ₀ S.cstar) ≤
        slotSetDist (col δ₀ (S.T N) 0) (colBand δ₀ (S.T N) (quarterPlus (S.T N).Nφ N)) ∧
      ENNReal.ofReal (S.cstar / 16 * Real.sqrt N - sepC_dev δ₀ S.cstar) ≤
        slotSetDist (col δ₀ (S.T N) N) (colBand δ₀ (S.T N) (quarterMinus (S.T N).Nφ N)) := by
  have hT : (S.T N).Admissible δ₀ := S.Ts.admissible N hN
  have hTN : (S.T N).N = N := S.Ts.T_N N hN
  have hc := S.cstar_pos
  have hLx : S.cstar * Real.sqrt (S.T N).N ≤ (S.T N).Lx := by rw [hTN]; exact S.Lx_ge N hN
  have hs1 := sep_cuts hδ₀ hT
  obtain ⟨hs2, hs3⟩ := sep_cut_mid hδ₀ hT
  obtain ⟨hs4, hs5⟩ := sep_cut_opposite hδ₀ hT
  rw [hTN] at hs1 hs2 hs3 hs4 hs5
  have key : ∀ (f : ℝ) (X Y : Finset (Slot δ₀ (S.T N))), ENNReal.ofReal f ≤ slotSetDist X Y →
      (⌈(96 * δ₀ / S.cstar) ^ 2⌉₊ ≤ N → S.cstar / 16 * Real.sqrt N ≤ f) →
      ENNReal.ofReal (S.cstar / 16 * Real.sqrt N - sepC_dev δ₀ S.cstar) ≤ slotSetDist X Y := by
    intro f X Y hXY hf
    have hC0 : 0 ≤ sepC_dev δ₀ S.cstar := by unfold sepC_dev; positivity
    rcases le_or_gt ⌈(96 * δ₀ / S.cstar) ^ 2⌉₊ N with h | h
    · exact le_trans (ENNReal.ofReal_le_ofReal (by linarith [hf h])) hXY
    · have h1 : Real.sqrt N ≤ Real.sqrt (⌈(96 * δ₀ / S.cstar) ^ 2⌉₊ : ℕ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast h.le)
      have h2 : S.cstar / 16 * Real.sqrt N - sepC_dev δ₀ S.cstar ≤ 0 := by
        unfold sepC_dev
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ S.cstar / 16)
        linarith
      rw [ENNReal.ofReal_of_nonpos h2]
      exact zero_le
  have hge : ⌈(96 * δ₀ / S.cstar) ^ 2⌉₊ ≤ N →
      S.cstar / 16 * Real.sqrt N ≤ (S.T N).Lx / 2 - 2 * δx δ₀ (S.T N) ∧
      S.cstar / 16 * Real.sqrt N ≤ (S.T N).Lx / 4 - 2 * δx δ₀ (S.T N) ∧
      S.cstar / 16 * Real.sqrt N ≤ (S.T N).Lx / 8 - (S.T N).κ - 2 * δx δ₀ (S.T N) ∧
      S.cstar / 16 * Real.sqrt N ≤ 3 * (S.T N).Lx / 8 - 2 * δx δ₀ (S.T N) := fun h => by
    have h' := sep_ge hδ₀ hT hc hLx (by rw [hTN]; exact h)
    rw [hTN] at h'
    exact h'
  exact ⟨key _ _ _ hs1 fun h => (hge h).1, key _ _ _ hs2 fun h => (hge h).2.2.1,
    key _ _ _ hs3 fun h => (hge h).2.2.1, key _ _ _ hs4 fun h => (hge h).2.2.2,
    key _ _ _ hs5 fun h => (hge h).2.2.2⟩

theorem comm_isONegInf_dev (hη : IsProfile η) (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) {C₀ : ℝ} (hc : 0 < S.cstar / 16)
    {A B : (N : ℕ) → FockOp (S.T N)} {X Y : (N : ℕ) → Finset (Slot δ₀ (S.T N))} {mA mB : ℝ} {CA CB : ℕ → ℝ}
    (hmA : mA ≤ 5 / 2) (hmB : mB ≤ 5 / 2) (he : ∀ N ∈ S.Ts.idx, IsEven (A N) ∧ IsEven (B N))
    (hn : ∀ N ∈ S.Ts.idx, ‖toCLM (S.T N) (A N)‖ ≤ C₀ * (N : ℝ) ^ (5 / 2 : ℝ) ∧
      ‖toCLM (S.T N) (B N)‖ ≤ C₀ * (N : ℝ) ^ (5 / 2 : ℝ))
    (hA : ASBound η δ₀ S.Ts X A mA CA) (hB : ASBound η δ₀ S.Ts Y B mB CB)
    (hd : ∀ N ∈ S.Ts.idx, ENNReal.ofReal (S.cstar / 16 * Real.sqrt N - sepC_dev δ₀ S.cstar) ≤
      slotSetDist (X N) (Y N)) :
    IsONegInf S.Ts (fun (_ : Unit) N => A N * B N - B N * A N) := by
  obtain ⟨Cr, hCr⟩ := bookkeeping_comm hc (max C₀ (sepC_dev δ₀ S.cstar)) (5 / 2) (by norm_num) CA CB
  intro k
  refine ⟨Cr k, fun _ N hN => ?_⟩
  have hNp : ∀ N ∈ S.Ts.idx, 0 ≤ (N : ℝ) ^ (5 / 2 : ℝ) := fun N hN =>
    Real.rpow_nonneg (by linarith [one_le_of_mem_idx S.Ts hN]) _
  exact hCr η δ₀ hη hδ₀ S.Ts S.cstar S.Lx_ge Unit (fun _ => X) (fun _ => Y) (fun _ => A) (fun _ => B)
    (fun _ N hN => he N hN)
    (fun _ N hN => ⟨(hn N hN).1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hNp N hN)),
      (hn N hN).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hNp N hN))⟩)
    ⟨mA, hmA, fun _ => hA⟩ ⟨mB, hmB, fun _ => hB⟩
    (fun _ N hN => le_trans (ENNReal.ofReal_le_ofReal (by linarith [le_max_right C₀ (sepC_dev δ₀ S.cstar)]))
      (hd N hN)) k () N hN

theorem comm_swap_dev {Ts : TorusSeq δ₀} {P : Type*} {A B : P → (N : ℕ) → FockOp (Ts.T N)}
    (h : IsONegInf Ts fun p N => B p N * A p N - A p N * B p N) :
    IsONegInf Ts fun p N => A p N * B p N - B p N * A p N := by
  intro k
  obtain ⟨C, hC⟩ := h k
  refine ⟨C, fun p N hN => ?_⟩
  have e : A p N * B p N - B p N * A p N = -(B p N * A p N - A p N * B p N) := by abel
  dsimp only
  rw [e, toCLM_neg_dev, norm_neg]
  exact hC p N hN

end SepPairDevices

/-- **Lemma 6.13(ii)** (separated pairs) for `U = Θ`: "`The commutators $[A,Q_m]$ with $A\in\{K_-,K^U_-,K_+,K^U_+\}$, and $[A_-,B_+]$ with $A_-\in\{Q_-,T_-,K_-,K^U_-\}$ and $B_+\in\{Q_+,T_+,K_+,K^U_+\}$ not covered by (i), are $\Onf$`"
— the sixteen pairs `sepPairs`. -/
theorem sep_isONegInf (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    ∀ i : Fin 16, IsONegInf D.Ts fun (_ : Unit) N => D.sepComm i N := by
  obtain ⟨hQe, -, hQmAS, hQmidAS, hQpAS⟩ := table_Q hη hδ₀ D.toIxSetting
  obtain ⟨hTe, hTmAS, hTpAS⟩ := table_T hη hδ₀ D
  obtain ⟨hKe, ⟨CK, hKn⟩, CKa, hKmAS, hKpAS, hKUmAS, hKUpAS⟩ := table_K hη hδ₀ D hD hH2
  have hc : 0 < D.cstar / 16 := by have := D.cstar_pos; positivity
  have hsep := fun N (hN : N ∈ D.Ts.idx) => sep_all_dev hδ₀ D.toIxSetting hN
  have hpow : ∀ N ∈ D.Ts.idx, (N : ℝ) ≤ (N : ℝ) ^ (5 / 2 : ℝ) ∧ (1 : ℝ) ≤ (N : ℝ) ^ (5 / 2 : ℝ) ∧
      (N : ℝ) ^ 2 ≤ (N : ℝ) ^ (5 / 2 : ℝ) := by
    intro N hN
    have hN1 := one_le_of_mem_idx D.Ts hN
    refine ⟨?_, Real.one_le_rpow hN1 (by norm_num), ?_⟩
    · have h := Real.rpow_le_rpow_of_exponent_le hN1 (show (1 : ℝ) ≤ 5 / 2 by norm_num)
      rwa [Real.rpow_one] at h
    · rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hC0 : (1 : ℝ) ≤ 1 + |CK| := by linarith [abs_nonneg CK]
  have nQ : ∀ N ∈ D.Ts.idx, ∀ X : FockOp (D.T N), ‖toCLM (D.T N) X‖ ≤ N →
      ‖toCLM (D.T N) X‖ ≤ (1 + |CK|) * (N : ℝ) ^ (5 / 2 : ℝ) := fun N hN X hX =>
    hX.trans ((hpow N hN).1.trans (le_mul_of_one_le_left (by linarith [(hpow N hN).2.1]) hC0))
  have nT : ∀ N ∈ D.Ts.idx, ∀ X : FockOp (D.T N), ‖toCLM (D.T N) X‖ = 1 →
      ‖toCLM (D.T N) X‖ ≤ (1 + |CK|) * (N : ℝ) ^ (5 / 2 : ℝ) := fun N hN X hX => by
    rw [hX]
    exact (hpow N hN).2.1.trans (le_mul_of_one_le_left (by linarith [(hpow N hN).2.1]) hC0)
  have nK : ∀ N ∈ D.Ts.idx, ∀ X : FockOp (D.T N), ‖toCLM (D.T N) X‖ ≤ CK * (N : ℝ) ^ 2 →
      ‖toCLM (D.T N) X‖ ≤ (1 + |CK|) * (N : ℝ) ^ (5 / 2 : ℝ) := fun N hN X hX => by
    refine hX.trans ?_
    calc CK * (N : ℝ) ^ 2 ≤ |CK| * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |CK| * (N : ℝ) ^ (5 / 2 : ℝ) := mul_le_mul_of_nonneg_left (hpow N hN).2.2 (abs_nonneg _)
      _ ≤ (1 + |CK|) * (N : ℝ) ^ (5 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith [(hpow N hN).2.1])
  intro i
  fin_cases i
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).1, (hQe N hN).2.2.2.2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).1, nQ N hN _ (hQe N hN).2.2.2.2.2.2.2.2.1⟩) hKmAS hQmidAS
      (fun N hN => (hsep N hN).2.1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).2.2.2.2.1, (hQe N hN).2.2.2.2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).2.2.1, nQ N hN _ (hQe N hN).2.2.2.2.2.2.2.2.1⟩) hKUmAS hQmidAS
      (fun N hN => (hsep N hN).2.1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).2.2.1, (hQe N hN).2.2.2.2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).2.1, nQ N hN _ (hQe N hN).2.2.2.2.2.2.2.2.1⟩) hKpAS hQmidAS
      (fun N hN => (hsep N hN).2.2.1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).2.2.2.2.2.2.1, (hQe N hN).2.2.2.2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).2.2.2, nQ N hN _ (hQe N hN).2.2.2.2.2.2.2.2.1⟩) hKUpAS hQmidAS
      (fun N hN => (hsep N hN).2.2.1)
  · exact comm_swap_dev (comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).2.2.1, (hQe N hN).2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).2.1, nQ N hN _ (hQe N hN).2.2.2.2.2.1⟩) hKpAS hQmAS
      (fun N hN => (hsep N hN).2.2.2.2))
  · exact comm_swap_dev (comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).2.2.2.2.2.2.1, (hQe N hN).2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).2.2.2, nQ N hN _ (hQe N hN).2.2.2.2.2.1⟩) hKUpAS hQmAS
      (fun N hN => (hsep N hN).2.2.2.2))
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).1, (hQe N hN).2.2.2.2.2.2.2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).1, nQ N hN _ (hQe N hN).2.2.2.2.2.2.2.2.2.2.2⟩) hKmAS hQpAS
      (fun N hN => (hsep N hN).2.2.2.1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).2.2.2.2.1, (hQe N hN).2.2.2.2.2.2.2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).2.2.1, nQ N hN _ (hQe N hN).2.2.2.2.2.2.2.2.2.2.2⟩) hKUmAS hQpAS
      (fun N hN => (hsep N hN).2.2.2.1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hTe N hN).1, (hKe N hN).2.2.1⟩)
      (fun N hN => ⟨nT N hN _ (hTe N hN).2.2.1, nK N hN _ (hKn N hN).2.1⟩) hTmAS hKpAS
      (fun N hN => (hsep N hN).1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hTe N hN).1, (hKe N hN).2.2.2.2.2.2.1⟩)
      (fun N hN => ⟨nT N hN _ (hTe N hN).2.2.1, nK N hN _ (hKn N hN).2.2.2⟩) hTmAS hKUpAS
      (fun N hN => (hsep N hN).1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).1, (hTe N hN).2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).1, nT N hN _ (hTe N hN).2.2.2.2.2⟩) hKmAS hTpAS
      (fun N hN => (hsep N hN).1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).1, (hKe N hN).2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).1, nK N hN _ (hKn N hN).2.1⟩) hKmAS hKpAS
      (fun N hN => (hsep N hN).1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).1, (hKe N hN).2.2.2.2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).1, nK N hN _ (hKn N hN).2.2.2⟩) hKmAS hKUpAS
      (fun N hN => (hsep N hN).1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).2.2.2.2.1, (hTe N hN).2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).2.2.1, nT N hN _ (hTe N hN).2.2.2.2.2⟩) hKUmAS hTpAS
      (fun N hN => (hsep N hN).1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).2.2.2.2.1, (hKe N hN).2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).2.2.1, nK N hN _ (hKn N hN).2.1⟩) hKUmAS hKpAS
      (fun N hN => (hsep N hN).1)
  · exact comm_isONegInf_dev hη hδ₀ D.toIxSetting hc (by norm_num) (by norm_num)
      (fun N hN => ⟨(hKe N hN).2.2.2.2.1, (hKe N hN).2.2.2.2.2.2.1⟩)
      (fun N hN => ⟨nK N hN _ (hKn N hN).2.2.1, nK N hN _ (hKn N hN).2.2.2⟩) hKUmAS hKUpAS
      (fun N hN => (hsep N hN).1)

/-! #### Proof devices for Lemma 6.13(iii) (phase (b), round two; not statements of the paper)

`O(N^{−∞})` is closed under sums, differences and a change off `𝒩`; each commutator of (iii) is a signed sum of the
sixteen of (ii) plus commutators that vanish by (i) (the expansions are in the proofs). -/

section ConseqDevices

theorem isONegInf_add_dev {Ts : TorusSeq δ₀} {P : Type*} {a b : P → (N : ℕ) → FockOp (Ts.T N)}
    (ha : IsONegInf Ts a) (hb : IsONegInf Ts b) : IsONegInf Ts fun p N => a p N + b p N := by
  intro k
  obtain ⟨C1, h1⟩ := ha k
  obtain ⟨C2, h2⟩ := hb k
  refine ⟨C1 + C2, fun p N hN => ?_⟩
  dsimp only
  rw [toCLM_add_dev, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h1 p N hN) (h2 p N hN))

theorem isONegInf_sub_dev {Ts : TorusSeq δ₀} {P : Type*} {a b : P → (N : ℕ) → FockOp (Ts.T N)}
    (ha : IsONegInf Ts a) (hb : IsONegInf Ts b) : IsONegInf Ts fun p N => a p N - b p N := by
  intro k
  obtain ⟨C1, h1⟩ := ha k
  obtain ⟨C2, h2⟩ := hb k
  refine ⟨C1 + C2, fun p N hN => ?_⟩
  dsimp only
  rw [toCLM_sub', add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (h1 p N hN) (h2 p N hN))

theorem isONegInf_congr_dev {Ts : TorusSeq δ₀} {P : Type*} {a b : P → (N : ℕ) → FockOp (Ts.T N)}
    (hab : ∀ p, ∀ N ∈ Ts.idx, a p N = b p N) (ha : IsONegInf Ts a) : IsONegInf Ts b := by
  intro k
  obtain ⟨C, h⟩ := ha k
  exact ⟨C, fun p N hN => by rw [← hab p N hN]; exact h p N hN⟩

end ConseqDevices

/-- **Lemma 6.13(iii)** (consequences): "`$[Q_m,A]\eqN0$ for $A\in\{\Qb_\pm,\Qb^U_\pm,\Tt\}$`". -/
theorem comm_Qmid_isONegInf (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid)
    (hH2 : D.d.H2) :
    IsONegInf D.Ts (fun (_ : Unit) N => D.Qmid N * D.QbarMinus N - D.QbarMinus N * D.Qmid N) ∧
    IsONegInf D.Ts (fun (_ : Unit) N => D.Qmid N * D.QbarPlus N - D.QbarPlus N * D.Qmid N) ∧
    IsONegInf D.Ts (fun (_ : Unit) N => D.Qmid N * D.QbarUMinus N - D.QbarUMinus N * D.Qmid N) ∧
    IsONegInf D.Ts (fun (_ : Unit) N => D.Qmid N * D.QbarUPlus N - D.QbarUPlus N * D.Qmid N) ∧
    IsONegInf D.Ts (fun (_ : Unit) N => D.Qmid N * D.Ttilde N - D.Ttilde N * D.Qmid N) := by
  have s := sep_isONegInf hη hδ₀ D hD hH2
  have s0 : IsONegInf D.Ts fun (_ : Unit) N => D.Km N * D.Qmid N - D.Qmid N * D.Km N := s 0
  have s1 : IsONegInf D.Ts fun (_ : Unit) N => D.KUminus N * D.Qmid N - D.Qmid N * D.KUminus N := s 1
  have s2 : IsONegInf D.Ts fun (_ : Unit) N => D.Kp N * D.Qmid N - D.Qmid N * D.Kp N := s 2
  have s3 : IsONegInf D.Ts fun (_ : Unit) N => D.KUplus N * D.Qmid N - D.Qmid N * D.KUplus N := s 3
  have z : ∀ N ∈ D.Ts.idx, ∀ X Y : FockOp (D.T N), Commute X Y → X * Y - Y * X = 0 :=
    fun _ _ X Y h => sub_eq_zero.mpr h.eq
  refine ⟨isONegInf_congr_dev (fun _ N hN => ?_) s0, isONegInf_congr_dev (fun _ N hN => ?_) s2,
    isONegInf_congr_dev (fun _ N hN => ?_) s1, isONegInf_congr_dev (fun _ N hN => ?_) s3,
    isONegInf_congr_dev (fun _ N hN => ?_) (isONegInf_sub_dev s1 s0)⟩ <;>
    obtain ⟨-, -, c1, c2, c3, c4, c5, c6, c7, c8⟩ := exact_relations D N hN
  · unfold ArgData.QbarMinus
    calc D.Km N * D.Qmid N - D.Qmid N * D.Km N
        = D.Km N * D.Qmid N - D.Qmid N * D.Km N - (D.Qminus N * D.Qmid N - D.Qmid N * D.Qminus N) := by
          rw [z N hN _ _ c1, sub_zero]
      _ = _ := by noncomm_ring
  · unfold ArgData.QbarPlus
    calc D.Kp N * D.Qmid N - D.Qmid N * D.Kp N
        = D.Kp N * D.Qmid N - D.Qmid N * D.Kp N + (D.Qmid N * D.Qplus N - D.Qplus N * D.Qmid N) := by
          rw [z N hN _ _ c2, add_zero]
      _ = _ := by noncomm_ring
  · unfold ArgData.QbarUMinus
    calc D.KUminus N * D.Qmid N - D.Qmid N * D.KUminus N
        = D.KUminus N * D.Qmid N - D.Qmid N * D.KUminus N - (D.Qminus N * D.Qmid N - D.Qmid N * D.Qminus N) +
            (D.Qmid N * D.Tminus N - D.Tminus N * D.Qmid N) := by
          rw [z N hN _ _ c1, z N hN _ _ c4, sub_zero, add_zero]
      _ = _ := by noncomm_ring
  · unfold ArgData.QbarUPlus
    calc D.KUplus N * D.Qmid N - D.Qmid N * D.KUplus N
        = D.KUplus N * D.Qmid N - D.Qmid N * D.KUplus N + (D.Qmid N * D.Qplus N - D.Qplus N * D.Qmid N) +
            (D.Qmid N * D.Tplus N - D.Tplus N * D.Qmid N) := by
          rw [z N hN _ _ c2, z N hN _ _ c5, add_zero, add_zero]
      _ = _ := by noncomm_ring
  · unfold ArgData.Ttilde
    calc D.KUminus N * D.Qmid N - D.Qmid N * D.KUminus N - (D.Km N * D.Qmid N - D.Qmid N * D.Km N)
        = D.KUminus N * D.Qmid N - D.Qmid N * D.KUminus N - (D.Km N * D.Qmid N - D.Qmid N * D.Km N) +
            (D.Qmid N * D.Tminus N - D.Tminus N * D.Qmid N) := by
          rw [z N hN _ _ c4, add_zero]
      _ = _ := by noncomm_ring

/-- **Lemma 6.13(iii)**: "`$[A_-,B_+]\eqN0$ for $A_-\in\{\Qb_-,\Qb^U_-,\Tt\}$ and $B_+\in\{\Qb_+,\Qb^U_+\}$`". -/
theorem comm_minus_plus_isONegInf (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid)
    (hH2 : D.d.H2) :
    IsONegInf D.Ts (fun (_ : Unit) N => D.QbarMinus N * D.QbarPlus N - D.QbarPlus N * D.QbarMinus N) ∧
    IsONegInf D.Ts (fun (_ : Unit) N => D.QbarMinus N * D.QbarUPlus N - D.QbarUPlus N * D.QbarMinus N) ∧
    IsONegInf D.Ts (fun (_ : Unit) N => D.QbarUMinus N * D.QbarPlus N - D.QbarPlus N * D.QbarUMinus N) ∧
    IsONegInf D.Ts (fun (_ : Unit) N => D.QbarUMinus N * D.QbarUPlus N - D.QbarUPlus N * D.QbarUMinus N) ∧
    IsONegInf D.Ts (fun (_ : Unit) N => D.Ttilde N * D.QbarPlus N - D.QbarPlus N * D.Ttilde N) ∧
    IsONegInf D.Ts (fun (_ : Unit) N => D.Ttilde N * D.QbarUPlus N - D.QbarUPlus N * D.Ttilde N) := by
  have s := sep_isONegInf hη hδ₀ D hD hH2
  have s4 : IsONegInf D.Ts fun (_ : Unit) N => D.Qminus N * D.Kp N - D.Kp N * D.Qminus N := s 4
  have s5 : IsONegInf D.Ts fun (_ : Unit) N => D.Qminus N * D.KUplus N - D.KUplus N * D.Qminus N := s 5
  have s6 : IsONegInf D.Ts fun (_ : Unit) N => D.Km N * D.Qplus N - D.Qplus N * D.Km N := s 6
  have s7 : IsONegInf D.Ts fun (_ : Unit) N => D.KUminus N * D.Qplus N - D.Qplus N * D.KUminus N := s 7
  have s8 : IsONegInf D.Ts fun (_ : Unit) N => D.Tminus N * D.Kp N - D.Kp N * D.Tminus N := s 8
  have s9 : IsONegInf D.Ts fun (_ : Unit) N => D.Tminus N * D.KUplus N - D.KUplus N * D.Tminus N := s 9
  have s10 : IsONegInf D.Ts fun (_ : Unit) N => D.Km N * D.Tplus N - D.Tplus N * D.Km N := s 10
  have s11 : IsONegInf D.Ts fun (_ : Unit) N => D.Km N * D.Kp N - D.Kp N * D.Km N := s 11
  have s12 : IsONegInf D.Ts fun (_ : Unit) N => D.Km N * D.KUplus N - D.KUplus N * D.Km N := s 12
  have s13 : IsONegInf D.Ts fun (_ : Unit) N => D.KUminus N * D.Tplus N - D.Tplus N * D.KUminus N := s 13
  have s14 : IsONegInf D.Ts fun (_ : Unit) N => D.KUminus N * D.Kp N - D.Kp N * D.KUminus N := s 14
  have s15 : IsONegInf D.Ts fun (_ : Unit) N => D.KUminus N * D.KUplus N - D.KUplus N * D.KUminus N := s 15
  have z : ∀ N ∈ D.Ts.idx, ∀ X Y : FockOp (D.T N), Commute X Y → X * Y - Y * X = 0 :=
    fun _ _ X Y h => sub_eq_zero.mpr h.eq
  refine ⟨isONegInf_congr_dev (fun _ N hN => ?_) (isONegInf_sub_dev (isONegInf_sub_dev s11 s4) s6),
    isONegInf_congr_dev (fun _ N hN => ?_)
      (isONegInf_sub_dev (isONegInf_sub_dev (isONegInf_sub_dev s12 s5) s6) s10),
    isONegInf_congr_dev (fun _ N hN => ?_)
      (isONegInf_sub_dev (isONegInf_sub_dev (isONegInf_sub_dev s14 s4) s8) s7),
    isONegInf_congr_dev (fun _ N hN => ?_)
      (isONegInf_sub_dev (isONegInf_sub_dev (isONegInf_sub_dev (isONegInf_sub_dev s15 s5) s9) s7) s13),
    isONegInf_congr_dev (fun _ N hN => ?_)
      (isONegInf_sub_dev (isONegInf_sub_dev (isONegInf_sub_dev (isONegInf_add_dev s14 s6) s8) s7) s11),
    isONegInf_congr_dev (fun _ N hN => ?_)
      (isONegInf_sub_dev (isONegInf_sub_dev (isONegInf_sub_dev (isONegInf_sub_dev
        (isONegInf_add_dev (isONegInf_add_dev s15 s6) s10) s9) s7) s13) s12)⟩ <;>
    obtain ⟨-, -, c1, c2, c3, c4, c5, c6, c7, c8⟩ := exact_relations D N hN
  · unfold ArgData.QbarMinus ArgData.QbarPlus
    calc D.Km N * D.Kp N - D.Kp N * D.Km N - (D.Qminus N * D.Kp N - D.Kp N * D.Qminus N) -
          (D.Km N * D.Qplus N - D.Qplus N * D.Km N)
        = D.Km N * D.Kp N - D.Kp N * D.Km N - (D.Qminus N * D.Kp N - D.Kp N * D.Qminus N) -
          (D.Km N * D.Qplus N - D.Qplus N * D.Km N) + (D.Qminus N * D.Qplus N - D.Qplus N * D.Qminus N) := by
          rw [z N hN _ _ c3, add_zero]
      _ = _ := by noncomm_ring
  · unfold ArgData.QbarMinus ArgData.QbarUPlus
    calc D.Km N * D.KUplus N - D.KUplus N * D.Km N - (D.Qminus N * D.KUplus N - D.KUplus N * D.Qminus N) -
          (D.Km N * D.Qplus N - D.Qplus N * D.Km N) - (D.Km N * D.Tplus N - D.Tplus N * D.Km N)
        = D.Km N * D.KUplus N - D.KUplus N * D.Km N - (D.Qminus N * D.KUplus N - D.KUplus N * D.Qminus N) -
          (D.Km N * D.Qplus N - D.Qplus N * D.Km N) - (D.Km N * D.Tplus N - D.Tplus N * D.Km N) +
          (D.Qminus N * D.Qplus N - D.Qplus N * D.Qminus N) + (D.Qminus N * D.Tplus N - D.Tplus N * D.Qminus N) := by
          rw [z N hN _ _ c3, z N hN _ _ c7, add_zero, add_zero]
      _ = _ := by noncomm_ring
  · unfold ArgData.QbarUMinus ArgData.QbarPlus
    calc D.KUminus N * D.Kp N - D.Kp N * D.KUminus N - (D.Qminus N * D.Kp N - D.Kp N * D.Qminus N) -
          (D.Tminus N * D.Kp N - D.Kp N * D.Tminus N) - (D.KUminus N * D.Qplus N - D.Qplus N * D.KUminus N)
        = D.KUminus N * D.Kp N - D.Kp N * D.KUminus N - (D.Qminus N * D.Kp N - D.Kp N * D.Qminus N) -
          (D.Tminus N * D.Kp N - D.Kp N * D.Tminus N) - (D.KUminus N * D.Qplus N - D.Qplus N * D.KUminus N) +
          (D.Qminus N * D.Qplus N - D.Qplus N * D.Qminus N) - (D.Qplus N * D.Tminus N - D.Tminus N * D.Qplus N) := by
          rw [z N hN _ _ c3, z N hN _ _ c6, add_zero, sub_zero]
      _ = _ := by noncomm_ring
  · unfold ArgData.QbarUMinus ArgData.QbarUPlus
    calc D.KUminus N * D.KUplus N - D.KUplus N * D.KUminus N -
          (D.Qminus N * D.KUplus N - D.KUplus N * D.Qminus N) - (D.Tminus N * D.KUplus N - D.KUplus N * D.Tminus N) -
          (D.KUminus N * D.Qplus N - D.Qplus N * D.KUminus N) - (D.KUminus N * D.Tplus N - D.Tplus N * D.KUminus N)
        = D.KUminus N * D.KUplus N - D.KUplus N * D.KUminus N -
          (D.Qminus N * D.KUplus N - D.KUplus N * D.Qminus N) - (D.Tminus N * D.KUplus N - D.KUplus N * D.Tminus N) -
          (D.KUminus N * D.Qplus N - D.Qplus N * D.KUminus N) - (D.KUminus N * D.Tplus N - D.Tplus N * D.KUminus N) +
          (D.Qminus N * D.Qplus N - D.Qplus N * D.Qminus N) + (D.Qminus N * D.Tplus N - D.Tplus N * D.Qminus N) -
          (D.Qplus N * D.Tminus N - D.Tminus N * D.Qplus N) + (D.Tminus N * D.Tplus N - D.Tplus N * D.Tminus N) := by
          rw [z N hN _ _ c3, z N hN _ _ c7, z N hN _ _ c6, z N hN _ _ c8, add_zero, add_zero, sub_zero, add_zero]
      _ = _ := by noncomm_ring
  · unfold ArgData.Ttilde ArgData.QbarPlus
    calc D.KUminus N * D.Kp N - D.Kp N * D.KUminus N + (D.Km N * D.Qplus N - D.Qplus N * D.Km N) -
          (D.Tminus N * D.Kp N - D.Kp N * D.Tminus N) - (D.KUminus N * D.Qplus N - D.Qplus N * D.KUminus N) -
          (D.Km N * D.Kp N - D.Kp N * D.Km N)
        = D.KUminus N * D.Kp N - D.Kp N * D.KUminus N + (D.Km N * D.Qplus N - D.Qplus N * D.Km N) -
          (D.Tminus N * D.Kp N - D.Kp N * D.Tminus N) - (D.KUminus N * D.Qplus N - D.Qplus N * D.KUminus N) -
          (D.Km N * D.Kp N - D.Kp N * D.Km N) - (D.Qplus N * D.Tminus N - D.Tminus N * D.Qplus N) := by
          rw [z N hN _ _ c6, sub_zero]
      _ = _ := by noncomm_ring
  · unfold ArgData.Ttilde ArgData.QbarUPlus
    calc D.KUminus N * D.KUplus N - D.KUplus N * D.KUminus N + (D.Km N * D.Qplus N - D.Qplus N * D.Km N) +
          (D.Km N * D.Tplus N - D.Tplus N * D.Km N) - (D.Tminus N * D.KUplus N - D.KUplus N * D.Tminus N) -
          (D.KUminus N * D.Qplus N - D.Qplus N * D.KUminus N) - (D.KUminus N * D.Tplus N - D.Tplus N * D.KUminus N) -
          (D.Km N * D.KUplus N - D.KUplus N * D.Km N)
        = D.KUminus N * D.KUplus N - D.KUplus N * D.KUminus N + (D.Km N * D.Qplus N - D.Qplus N * D.Km N) +
          (D.Km N * D.Tplus N - D.Tplus N * D.Km N) - (D.Tminus N * D.KUplus N - D.KUplus N * D.Tminus N) -
          (D.KUminus N * D.Qplus N - D.Qplus N * D.KUminus N) - (D.KUminus N * D.Tplus N - D.Tplus N * D.KUminus N) -
          (D.Km N * D.KUplus N - D.KUplus N * D.Km N) - (D.Qplus N * D.Tminus N - D.Tminus N * D.Qplus N) +
          (D.Tminus N * D.Tplus N - D.Tplus N * D.Tminus N) := by
          rw [z N hN _ _ c6, z N hN _ _ c8, sub_zero, add_zero]
      _ = _ := by noncomm_ring

/-- **Lemma 6.13(iii)**: "`$[P,e^{2\pi\iu\Qb}]=0$; and $[P,\mathcal M(\varphi)]\eqN0$, with equality if $[U,P]=0$`" — for
`U = Θ` both exactly. -/
theorem commute_P_exp (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    ∀ N ∈ D.Ts.idx, Commute (D.P N) (NormedSpace.exp ((2 * π * I : ℂ) • D.Qb N)) ∧
      ∀ φ : ℝ, Commute (D.P N) (D.Mfull φ N) := by
  intro N hN
  have hA := hD.gap
  have hPQb : Commute (D.P N) (D.Qb N) := (K_comm_P D hA hD.cutoff N hN).2.symm
  have hΘs := Θ_isSectorPreserving (D.T N)
  have hΘH := D.d.commute_Θ_of_H2 hH2 N hN
  have hH := D.d.H_isSelfAdjoint N hN
  have h1 : Commute (cfc ((Set.Icc (D.E N 1) (D.E N D.p)).indicator (1 : ℝ → ℝ)) (D.H N)) (Θ (D.T N)) :=
    Commute.cfc (𝕜 := ℝ) hΘH.symm (by rw [hH.star_eq]; exact hΘH.symm) _
  have h2 : Commute (Psec (D.T N) (D.nn N)) (Θ (D.T N)) :=
    ((isSectorPreserving_iff_commute _ _).mp hΘs (D.nn N)).symm
  have hPΘ : Commute (D.P N) (Θ (D.T N)) := by
    unfold ArgData.P
    exact h1.mul_left h2
  have hPΘs : Commute (D.P N) (Θ (D.T N))ᴴ := by
    have h3 := hPΘ.star_star
    rwa [(ArgData.P_props D hA N hN).1.isSelfAdjoint.star_eq, Matrix.star_eq_conjTranspose] at h3
  have hPQbU : Commute (D.P N) (D.QbarU N) := by
    unfold ArgData.QbarU
    exact (hPΘs.mul_right hPQb).mul_right hPΘ
  refine ⟨(hPQb.smul_right _).exp_right, fun φ => ?_⟩
  unfold ArgData.Mfull
  exact ((hPQbU.smul_right _).exp_right).mul_right ((hPQb.smul_right _).exp_right)

/-- **Corollary 6.15's inputs** (the clustering commutators that the proof of Lemma 6.14 shows to be `O(N^{−∞})`,
through Proposition 6.10(iii)): "`\bigl(\Qf(\mathcal M_+(\varphi)),\mathcal M_-(\varphi)\bigr)`" and its adjoint pair uniformly in
`φ ∈ [0, 2π]`, "`\bigl(\Qf(e^{2\pi\iu\Qb_+}),e^{2\pi\iu\Qb_-}\bigr)`" and its adjoint pair — the four of the core's
`Orbital.Inputs`. -/
theorem clu_isONegInf (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    IsONegInf D.Ts (fun (φ : Set.Icc (0 : ℝ) (2 * π)) N =>
      D.Qf N (D.Mplus φ N) * D.Mminus φ N - D.Mminus φ N * D.Qf N (D.Mplus φ N)) ∧
    IsONegInf D.Ts (fun (φ : Set.Icc (0 : ℝ) (2 * π)) N =>
      D.Qf N ((D.Mplus φ N)ᴴ) * (D.Mminus φ N)ᴴ - (D.Mminus φ N)ᴴ * D.Qf N ((D.Mplus φ N)ᴴ)) ∧
    IsONegInf D.Ts (fun (_ : Unit) N => D.Qf N (D.Oplus N) * D.Ominus N - D.Ominus N * D.Qf N (D.Oplus N)) ∧
    IsONegInf D.Ts (fun (_ : Unit) N =>
      D.Qf N ((D.Oplus N)ᴴ) * (D.Ominus N)ᴴ - (D.Ominus N)ᴴ * D.Qf N ((D.Oplus N)ᴴ)) := by
  obtain ⟨hMu, hOu, CM, hMAS, hOmAS, hOpAS, -, -⟩ := table_M hη hδ₀ D hD hH2
  have hc : 0 < D.cstar / 16 := by have := D.cstar_pos; positivity
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max 1 (max ((4 * δ₀ / π + 1 / 2) * (4 * π / D.cstar)) (sepC_dev δ₀ D.cstar)) :=
    ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by rw [hC]; exact le_max_left _ _
  have hC2 : (4 * δ₀ / π + 1 / 2) * (4 * π / D.cstar) ≤ C := by
    rw [hC]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : sepC_dev δ₀ D.cstar ≤ C := by rw [hC]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hn1 : ∀ N ∈ D.Ts.idx, ∀ U : FockOp (D.T N), U ∈ unitary (FockOp (D.T N)) →
      ‖toCLM (D.T N) U‖ ≤ C * (N : ℝ) ^ (1 / 2 : ℝ) ∧ ‖toCLM (D.T N) Uᴴ‖ ≤ C * (N : ℝ) ^ (1 / 2 : ℝ) := by
    intro N hN U hU
    have h1 : (1 : ℝ) ≤ C * (N : ℝ) ^ (1 / 2 : ℝ) := by
      have := Real.one_le_rpow (one_le_of_mem_idx D.Ts hN) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      nlinarith
    have hU' : Uᴴ ∈ unitary (FockOp (D.T N)) := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Unitary.star_mem hU
    exact ⟨(norm_toCLM_le_one_dev hU).trans h1, (norm_toCLM_le_one_dev hU').trans h1⟩
  have hX : ∀ j : ℤ, ∀ N ∈ D.Ts.idx, ((col δ₀ (D.T N) j).card : ℝ) ≤ C * (N : ℝ) ^ (1 / 2 : ℝ) := fun j N hN =>
    (card_col_le_dev hδ₀ D.toIxSetting j hN).trans (mul_le_mul_of_nonneg_right hC2
      (Real.rpow_nonneg (by linarith [one_le_of_mem_idx D.Ts hN]) _))
  have hd : ∀ N ∈ D.Ts.idx, ENNReal.ofReal (D.cstar / 16 * Real.sqrt N - C) ≤
      slotSetDist (D.cutPlus N) (D.cutMinus N) := fun N hN => by
    rw [slotSetDist_comm_dev]
    exact le_trans (ENNReal.ofReal_le_ofReal (by linarith)) (sep_all_dev hδ₀ D.toIxSetting hN).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact clustering_isONegInf hη hδ₀ D hD (fun (φ : Set.Icc (0 : ℝ) (2 * π)) N => D.Mplus φ N)
      (fun φ N => D.Mminus φ N) (fun _ => D.cutPlus) (fun _ => D.cutMinus) hc
      (fun φ N hN => (hMu N hN φ).2.2.2.2.2) (fun φ N hN => (hMu N hN φ).2.2.2.2.1)
      (fun φ N hN => (hMu N hN φ).2.1) (fun φ => (hMAS φ φ.2).2) (fun φ => (hMAS φ φ.2).1)
      (fun φ N hN => (hn1 N hN _ (hMu N hN φ).2.2.2.1).1) (fun φ N hN => (hn1 N hN _ (hMu N hN φ).1).1)
      (fun _ N hN => hX N N hN) (fun _ N hN => hd N hN)
  · exact clustering_isONegInf hη hδ₀ D hD (fun (φ : Set.Icc (0 : ℝ) (2 * π)) N => (D.Mplus φ N)ᴴ)
      (fun φ N => (D.Mminus φ N)ᴴ) (fun _ => D.cutPlus) (fun _ => D.cutMinus) hc
      (fun φ N hN => sp_conjTranspose_dev (hMu N hN φ).2.2.2.2.2)
      (fun φ N hN => (sp_conjTranspose_dev (hMu N hN φ).2.2.2.2.2).isEven)
      (fun φ N hN => (sp_conjTranspose_dev (hMu N hN φ).2.2.1).isEven)
      (fun φ => asBound_star hη hδ₀ (hMAS φ φ.2).2) (fun φ => asBound_star hη hδ₀ (hMAS φ φ.2).1)
      (fun φ N hN => (hn1 N hN _ (hMu N hN φ).2.2.2.1).2) (fun φ N hN => (hn1 N hN _ (hMu N hN φ).1).2)
      (fun _ N hN => hX N N hN) (fun _ N hN => hd N hN)
  · exact clustering_isONegInf hη hδ₀ D hD (fun (_ : Unit) N => D.Oplus N) (fun _ N => D.Ominus N)
      (fun _ => D.cutPlus) (fun _ => D.cutMinus) hc
      (fun _ N hN => (hOu N hN).2.2.2.2.2) (fun _ N hN => (hOu N hN).2.2.2.2.1)
      (fun _ N hN => (hOu N hN).2.1) (fun _ => hOpAS) (fun _ => hOmAS)
      (fun _ N hN => (hn1 N hN _ (hOu N hN).2.2.2.1).1) (fun _ N hN => (hn1 N hN _ (hOu N hN).1).1)
      (fun _ N hN => hX N N hN) (fun _ N hN => hd N hN)
  · exact clustering_isONegInf hη hδ₀ D hD (fun (_ : Unit) N => (D.Oplus N)ᴴ) (fun _ N => (D.Ominus N)ᴴ)
      (fun _ => D.cutPlus) (fun _ => D.cutMinus) hc
      (fun _ N hN => sp_conjTranspose_dev (hOu N hN).2.2.2.2.2)
      (fun _ N hN => (sp_conjTranspose_dev (hOu N hN).2.2.2.2.2).isEven)
      (fun _ N hN => (sp_conjTranspose_dev (hOu N hN).2.2.1).isEven)
      (fun _ => asBound_star hη hδ₀ hOpAS) (fun _ => asBound_star hη hδ₀ hOmAS)
      (fun _ N hN => (hn1 N hN _ (hOu N hN).2.2.2.1).2) (fun _ N hN => (hn1 N hN _ (hOu N hN).1).2)
      (fun _ N hN => hX N N hN) (fun _ N hN => hd N hN)

/-! ### The orbital structure, its objects, and the discharge of `Orbital.Inputs` -/

/-! #### Proof devices for the orbital structure (phase (b), round one; not statements of the paper) -/

section OrbDevices

theorem orbOf_Kminus_dev (D : ArgData η δ₀) (hD : D.Valid) {N : ℕ} (hN : N ∈ D.Ts.idx) (h : OrbObligations D N) :
    (orbOf D N hN h).toSetting.Kminus = toCLM (D.T N) (D.Km N) := by
  have hγ : 0 < D.γ := by linarith [hD.gap.Δ_nonneg, hD.gap.two_mul_Δ_lt]
  unfold ArgData.Km IxSetting.Kminus
  rw [dress_eq_dev hD.cutoff hγ (D.d.H_isSelfAdjoint N hN), toCLM_spectralSum_dev (D.d.H_isSelfAdjoint N hN) h.H_sa]
  rfl

theorem orbOf_Kplus_dev (D : ArgData η δ₀) (hD : D.Valid) {N : ℕ} (hN : N ∈ D.Ts.idx) (h : OrbObligations D N) :
    (orbOf D N hN h).toSetting.Kplus = toCLM (D.T N) (D.Kp N) := by
  have hγ : 0 < D.γ := by linarith [hD.gap.Δ_nonneg, hD.gap.two_mul_Δ_lt]
  unfold ArgData.Kp IxSetting.Kplus
  rw [dress_eq_dev hD.cutoff hγ (D.d.H_isSelfAdjoint N hN), toCLM_spectralSum_dev (D.d.H_isSelfAdjoint N hN) h.H_sa]
  rfl

theorem orbOf_Qb_dev (D : ArgData η δ₀) {N : ℕ} (hN : N ∈ D.Ts.idx) (h : OrbObligations D N)
    (B : Finset (ZMod (D.T N).Nφ)) : (orbOf D N hN h).Qb B = toCLM (D.T N) (Qband (D.T N) B) := by
  show ∑ j ∈ B, toCLM (D.T N) (njs (D.T N) j .up) = _
  unfold Qband
  rw [toCLM_sum']

theorem orbOf_P_dev (D : ArgData η δ₀) {N : ℕ} (hN : N ∈ D.Ts.idx) (h : OrbObligations D N) :
    (orbOf D N hN h).toSetting.P = toCLM (D.T N) (D.P N) := by
  unfold ArgData.P
  rw [toCLM_mul', toCLM_cfc_indicator (D.d.H_isSelfAdjoint N hN) h.H_sa]
  rfl

theorem orbOf_Qf_dev (D : ArgData η δ₀) {N : ℕ} (hN : N ∈ D.Ts.idx) (h : OrbObligations D N) (A : FockOp (D.T N)) :
    (orbOf D N hN h).toSetting.Qf (toCLM (D.T N) A) = toCLM (D.T N) (D.Qf N A) := by
  unfold ArgData.Qf clusterFilter
  rw [toCLM_spectralSum_dev (D.d.H_isSelfAdjoint N hN) h.H_sa]
  rfl

theorem norm_le_one_of_mem_unitary_dev {T : Torus} {U : FockSpace T →L[ℂ] FockSpace T}
    (hU : U ∈ unitary (FockSpace T →L[ℂ] FockSpace T)) : ‖U‖ ≤ 1 := by
  have h : ‖U * 1‖ = ‖(1 : FockSpace T →L[ℂ] FockSpace T)‖ := CStarRing.norm_coe_unitary_mul ⟨U, hU⟩ 1
  rw [mul_one] at h
  rw [h]
  exact ContinuousLinearMap.norm_id_le

theorem norm_spectralSum_le_dev {T : Torus} (H : FockSpace T →L[ℂ] FockSpace T) (hH : IsSelfAdjoint H)
    (f : ℝ → ℝ → ℂ) (A : FockSpace T →L[ℂ] FockSpace T) :
    ‖IndexCore.spectralSum H hH f A‖ ≤ (∑ μ ∈ IndexCore.spec H hH, ∑ ν ∈ IndexCore.spec H hH,
      ‖f μ ν‖ * ‖IndexCore.eigProj H hH μ‖ * ‖IndexCore.eigProj H hH ν‖) * ‖A‖ := by
  rw [IndexCore.spectralSum_def, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
  rw [norm_smul]
  calc ‖f μ ν‖ * ‖IndexCore.eigProj H hH μ * A * IndexCore.eigProj H hH ν‖
      ≤ ‖f μ ν‖ * (‖IndexCore.eigProj H hH μ‖ * ‖A‖ * ‖IndexCore.eigProj H hH ν‖) := by
        gcongr
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖f μ ν‖ * ‖IndexCore.eigProj H hH μ‖ * ‖IndexCore.eigProj H hH ν‖ * ‖A‖ := by ring

theorem norm_lie_le_dev {T : Torus} {X Y : FockSpace T →L[ℂ] FockSpace T} {c : ℝ} (hX : ‖X‖ ≤ c) (hY : ‖Y‖ ≤ 1) :
    ‖⁅X, Y⁆‖ ≤ 2 * c := by
  have hc : 0 ≤ c := (norm_nonneg _).trans hX
  rw [Ring.lie_def]
  calc ‖X * Y - Y * X‖ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ c * 1 + 1 * c := add_le_add (mul_le_mul hX hY (norm_nonneg _) hc) (mul_le_mul hY hX (norm_nonneg _) zero_le_one)
    _ = 2 * c := by ring

theorem one_le_Mb_dev (D : ArgData η δ₀) {N : ℕ} (hN : N ∈ D.Ts.idx) : 1 ≤ D.Mb N := by
  have hCh : 0 ≤ D.d.Ch := (norm_nonneg _).trans (D.d.norm_h_le N hN 0)
  have hM : 0 ≤ moment (Wfilt D.ϑ D.γ) 0 :=
    integral_nonneg fun t => mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
  have hN1 : (1 : ℝ) ≤ N := by
    have h1 := (D.T N).N_pos
    rw [D.Ts.T_N N hN] at h1
    exact_mod_cast h1
  unfold ArgData.Mb
  exact one_le_mul_of_one_le_of_one_le (by nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 4 * π) hCh) hM])
    (one_le_pow₀ hN1)

end OrbDevices

/-- The obligations hold at every `N ∈ 𝒩` for valid data with (H2). -/
theorem obligations (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    ∀ N ∈ D.Ts.idx, OrbObligations D N := by
  intro N hN
  have hγ : 0 < D.γ := by linarith [hD.gap.Δ_nonneg, hD.gap.two_mul_Δ_lt]
  have hH := D.d.H_isSelfAdjoint N hN
  have hHs := H_isSectorPreserving_dev D.toIxSetting hN
  obtain ⟨j1, j2, j3, j4⟩ := J_isSelfAdjoint D.toIxSetting N hN
  refine
    { H_sa := isSelfAdjoint_toCLM_dev hH
      Psec_H := commute_Psec_toCLM_dev _ hHs
      Θ_H := commute_toCLM_dev (D.d.commute_Θ_of_H2 hH2 N hN)
      Δ_nonneg := hD.gap.Δ_nonneg
      Δ_lt_γ := by linarith [hD.gap.Δ_nonneg, hD.gap.two_mul_Δ_lt]
      width := hD.gap.spread N hN
      gap := fun μ v hv0 hv hHv => gap_of_secEig hH hHs hγ (hD.gap.gap N hN) μ v hv0 hv hHv
      Jminus_sa := isSelfAdjoint_toCLM_dev j1
      Jplus_sa := isSelfAdjoint_toCLM_dev j3
      Psec_Jminus := commute_Psec_toCLM_dev _ j2
      Psec_Jplus := commute_Psec_toCLM_dev _ j4
      current_split := ?_
      W_eq := fun ω hω => What_eq_dev hD.cutoff hγ ω hω
      W_conj := fun ω => What_conj_dev hD.cutoff D.γ ω
      g_zero := fun ω hω => by rw [gClust_eq_zero hD.clust hω, Complex.ofReal_zero]
      g_one := fun ω hω => by
        rw [gClust_eq_one hD.clust (by linarith [hD.gap.Δ_nonneg]), Complex.ofReal_one] }
  rw [← toCLM_add_dev, Jminus_add_Jplus D.toIxSetting N hN, toCLM_smul_dev, toCLM_sub', toCLM_mul', toCLM_mul',
    Ring.lie_def]
  unfold IxSetting.Q Qband
  rw [toCLM_sum']

/-- The core's derived objects on `(orbOf D N hN h).toSetting` are the paper's under `toCLM`: `K_±`, `K^U_±`, the band
charges, `T_±`, `P`, `𝓜_±(φ)`, `e^{2πiQ̄_±}`, and `𝒬` on every operator. -/
theorem orbOf_objects (D : ArgData η δ₀) (hD : D.Valid) {N : ℕ} (hN : N ∈ D.Ts.idx) (h : OrbObligations D N) :
    (orbOf D N hN h).toSetting.Kminus = toCLM (D.T N) (D.Km N) ∧
    (orbOf D N hN h).toSetting.Kplus = toCLM (D.T N) (D.Kp N) ∧
    (orbOf D N hN h).toSetting.KUminus = toCLM (D.T N) (D.KUminus N) ∧
    (orbOf D N hN h).toSetting.KUplus = toCLM (D.T N) (D.KUplus N) ∧
    (orbOf D N hN h).toSetting.Qminus = toCLM (D.T N) (D.Qminus N) ∧
    (orbOf D N hN h).toSetting.Qmid = toCLM (D.T N) (D.Qmid N) ∧
    (orbOf D N hN h).toSetting.Qplus = toCLM (D.T N) (D.Qplus N) ∧
    (orbOf D N hN h).toSetting.Tminus = toCLM (D.T N) (D.Tminus N) ∧
    (orbOf D N hN h).toSetting.Tplus = toCLM (D.T N) (D.Tplus N) ∧
    (orbOf D N hN h).toSetting.Qbar = toCLM (D.T N) (D.Qb N) ∧
    (orbOf D N hN h).toSetting.QbarMinus = toCLM (D.T N) (D.QbarMinus N) ∧
    (orbOf D N hN h).toSetting.QbarPlus = toCLM (D.T N) (D.QbarPlus N) ∧
    (orbOf D N hN h).toSetting.QbarUMinus = toCLM (D.T N) (D.QbarUMinus N) ∧
    (orbOf D N hN h).toSetting.QbarUPlus = toCLM (D.T N) (D.QbarUPlus N) ∧
    (orbOf D N hN h).toSetting.Ttilde = toCLM (D.T N) (D.Ttilde N) ∧
    (orbOf D N hN h).toSetting.P = toCLM (D.T N) (D.P N) ∧
    (∀ φ : ℝ, (orbOf D N hN h).toSetting.Mminus φ = toCLM (D.T N) (D.Mminus φ N) ∧
      (orbOf D N hN h).toSetting.Mplus φ = toCLM (D.T N) (D.Mplus φ N)) ∧
    (orbOf D N hN h).toSetting.Ominus = toCLM (D.T N) (D.Ominus N) ∧
    (orbOf D N hN h).toSetting.Oplus = toCLM (D.T N) (D.Oplus N) ∧
    ∀ A : FockOp (D.T N), (orbOf D N hN h).toSetting.Qf (toCLM (D.T N) A) = toCLM (D.T N) (D.Qf N A) := by
  have hKm := orbOf_Kminus_dev D hD hN h
  have hKp := orbOf_Kplus_dev D hD hN h
  have hQm : (orbOf D N hN h).toSetting.Qminus = toCLM (D.T N) (D.Qminus N) :=
    orbOf_Qb_dev D hN h (quarterMinus (D.T N).Nφ N)
  have hQmid : (orbOf D N hN h).toSetting.Qmid = toCLM (D.T N) (D.Qmid N) :=
    orbOf_Qb_dev D hN h (quarterMid (D.T N).Nφ N)
  have hQp : (orbOf D N hN h).toSetting.Qplus = toCLM (D.T N) (D.Qplus N) :=
    orbOf_Qb_dev D hN h (quarterPlus (D.T N).Nφ N)
  have hTm : (orbOf D N hN h).toSetting.Tminus = toCLM (D.T N) (D.Tminus N) := by
    show -toCLM (D.T N) (njs (D.T N) 0 .up) = _
    unfold ArgData.Tminus
    rw [toCLM_neg_dev]
  have hTp : (orbOf D N hN h).toSetting.Tplus = toCLM (D.T N) (D.Tplus N) := rfl
  have hKUm : (orbOf D N hN h).toSetting.KUminus = toCLM (D.T N) (D.KUminus N) := by
    show star (toCLM (D.T N) (Θ (D.T N))) * (orbOf D N hN h).toSetting.Kminus * toCLM (D.T N) (Θ (D.T N)) = _
    rw [hKm]
    unfold ArgData.KUminus
    rw [toCLM_mul', toCLM_mul', ← Matrix.star_eq_conjTranspose, toCLM_star_dev]
  have hKUp : (orbOf D N hN h).toSetting.KUplus = toCLM (D.T N) (D.KUplus N) := by
    show star (toCLM (D.T N) (Θ (D.T N))) * (orbOf D N hN h).toSetting.Kplus * toCLM (D.T N) (Θ (D.T N)) = _
    rw [hKp]
    unfold ArgData.KUplus
    rw [toCLM_mul', toCLM_mul', ← Matrix.star_eq_conjTranspose, toCLM_star_dev]
  have hQb : (orbOf D N hN h).toSetting.Qbar = toCLM (D.T N) (D.Qb N) := by
    show (orbOf D N hN h).toSetting.Qminus + (orbOf D N hN h).toSetting.Qmid + (orbOf D N hN h).toSetting.Qplus -
      (orbOf D N hN h).toSetting.Kminus - (orbOf D N hN h).toSetting.Kplus = _
    rw [hQm, hQmid, hQp, hKm, hKp]
    unfold ArgData.Qb IxSetting.Qbar
    rw [Q_eq_add_dev D.toIxSetting hN, toCLM_sub', toCLM_sub', toCLM_add_dev, toCLM_add_dev]
    rfl
  have hQbm : (orbOf D N hN h).toSetting.QbarMinus = toCLM (D.T N) (D.QbarMinus N) := by
    show (orbOf D N hN h).toSetting.Qminus - (orbOf D N hN h).toSetting.Kminus = _
    rw [hQm, hKm]
    unfold ArgData.QbarMinus
    rw [toCLM_sub']
  have hQbp : (orbOf D N hN h).toSetting.QbarPlus = toCLM (D.T N) (D.QbarPlus N) := by
    show (orbOf D N hN h).toSetting.Qplus - (orbOf D N hN h).toSetting.Kplus = _
    rw [hQp, hKp]
    unfold ArgData.QbarPlus
    rw [toCLM_sub']
  have hQbUm : (orbOf D N hN h).toSetting.QbarUMinus = toCLM (D.T N) (D.QbarUMinus N) := by
    show (orbOf D N hN h).toSetting.Qminus + (orbOf D N hN h).toSetting.Tminus -
      (orbOf D N hN h).toSetting.KUminus = _
    rw [hQm, hTm, hKUm]
    unfold ArgData.QbarUMinus
    rw [toCLM_sub', toCLM_add_dev]
  have hQbUp : (orbOf D N hN h).toSetting.QbarUPlus = toCLM (D.T N) (D.QbarUPlus N) := by
    show (orbOf D N hN h).toSetting.Qplus + (orbOf D N hN h).toSetting.Tplus -
      (orbOf D N hN h).toSetting.KUplus = _
    rw [hQp, hTp, hKUp]
    unfold ArgData.QbarUPlus
    rw [toCLM_sub', toCLM_add_dev]
  have hTt : (orbOf D N hN h).toSetting.Ttilde = toCLM (D.T N) (D.Ttilde N) := by
    show (orbOf D N hN h).toSetting.Tminus - (orbOf D N hN h).toSetting.KUminus +
      (orbOf D N hN h).toSetting.Kminus = _
    rw [hTm, hKUm, hKm]
    unfold ArgData.Ttilde
    rw [toCLM_add_dev, toCLM_sub']
  have hM : ∀ φ : ℝ, (orbOf D N hN h).toSetting.Mminus φ = toCLM (D.T N) (D.Mminus φ N) ∧
      (orbOf D N hN h).toSetting.Mplus φ = toCLM (D.T N) (D.Mplus φ N) := by
    intro φ
    constructor
    · show NormedSpace.exp ((I * φ) • (orbOf D N hN h).toSetting.QbarUMinus) *
        NormedSpace.exp ((-(I * φ)) • (orbOf D N hN h).toSetting.QbarMinus) = _
      rw [hQbUm, hQbm]
      unfold ArgData.Mminus
      rw [toCLM_mul', toCLM_exp_dev, toCLM_exp_dev, toCLM_smul_dev, toCLM_smul_dev]
    · show NormedSpace.exp ((I * φ) • (orbOf D N hN h).toSetting.QbarUPlus) *
        NormedSpace.exp ((-(I * φ)) • (orbOf D N hN h).toSetting.QbarPlus) = _
      rw [hQbUp, hQbp]
      unfold ArgData.Mplus
      rw [toCLM_mul', toCLM_exp_dev, toCLM_exp_dev, toCLM_smul_dev, toCLM_smul_dev]
  have hOm : (orbOf D N hN h).toSetting.Ominus = toCLM (D.T N) (D.Ominus N) := by
    show NormedSpace.exp ((2 * π * I) • (orbOf D N hN h).toSetting.QbarMinus) = _
    rw [hQbm]
    unfold ArgData.Ominus
    rw [toCLM_exp_dev, toCLM_smul_dev]
  have hOp : (orbOf D N hN h).toSetting.Oplus = toCLM (D.T N) (D.Oplus N) := by
    show NormedSpace.exp ((2 * π * I) • (orbOf D N hN h).toSetting.QbarPlus) = _
    rw [hQbp]
    unfold ArgData.Oplus
    rw [toCLM_exp_dev, toCLM_smul_dev]
  exact ⟨hKm, hKp, hKUm, hKUp, hQm, hQmid, hQp, hTm, hTp, hQb, hQbm, hQbp, hQbUm, hQbUp, hTt,
    orbOf_P_dev D hN h, hM, hOm, hOp, orbOf_Qf_dev D hN h⟩

/-- The core's rank `p = rank P` of the orbital structure is Assumption 6.3's `p`. -/
theorem orbOf_p (D : ArgData η δ₀) (hD : D.Valid) {N : ℕ} (hN : N ∈ D.Ts.idx) (h : OrbObligations D N) :
    (orbOf D N hN h).toSetting.p = D.p := by
  show Module.finrank ℂ (LinearMap.range ((orbOf D N hN h).toSetting.P :
    FockSpace (D.T N) →ₗ[ℂ] FockSpace (D.T N))) = D.p
  rw [orbOf_P_dev D hN h, ← ArgData.rank_P D hD.gap N hN,
    Matrix.rank_eq_finrank_range_toLin _ (EuclideanSpace.basisFun (Conf (ZMod (D.T N).Nφ)) ℂ).toBasis
      (EuclideanSpace.basisFun (Conf (ZMod (D.T N).Nφ)) ℂ).toBasis]
  rfl

/-- **The discharge**: at every `N ∈ 𝒩`, the core's inputs hold with `ε = ε(N)` and `M = M(N)`. -/
theorem inputs_orbOf (D : ArgData η δ₀) (hD : D.Valid) {N : ℕ} (hN : N ∈ D.Ts.idx) (h : OrbObligations D N) :
    (orbOf D N hN h).Inputs (D.eps N) (D.Mb N) := by
  obtain ⟨hKm, hKp, hKUm, hKUp, hQm, hQmid, hQp, hTm, hTp, -, -, -, -, -, -, -, hM, hOm, hOp, hQf⟩ :=
    orbOf_objects D hD hN h
  have hγ : 0 < D.γ := by linarith [hD.gap.Δ_nonneg, hD.gap.two_mul_Δ_lt]
  have hsep : ∀ i : Fin 16, ‖toCLM (D.T N) (D.sepComm i N)‖ ≤ D.eps N := fun i =>
    (Finset.le_sup' (fun i : Fin 16 => ‖toCLM (D.T N) (D.sepComm i N)‖) (Finset.mem_univ i)).trans
      (le_max_left _ _)
  have hsep2 : ∀ (i : Fin 16) (X Y : (N : ℕ) → FockOp (D.T N)), D.sepPairs i = (X, Y) →
      ‖toCLM (D.T N) (X N * Y N - Y N * X N)‖ ≤ D.eps N := by
    intro i X Y hXY
    have h1 := hsep i
    unfold ArgData.sepComm at h1
    rw [hXY] at h1
    exact h1
  have hlie : ∀ A B : FockOp (D.T N), ⁅toCLM (D.T N) A, toCLM (D.T N) B⁆ = toCLM (D.T N) (A * B - B * A) := by
    intro A B
    rw [Ring.lie_def, toCLM_sub', toCLM_mul', toCLM_mul']
  obtain ⟨C, hC0, hQfle⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ X, ‖X‖ ≤ 1 → ‖(orbOf D N hN h).toSetting.Qf X‖ ≤ C := by
    refine ⟨_, Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity, fun X hX =>
      (norm_spectralSum_le_dev _ _ _ X).trans (mul_le_of_le_one_right ?_ hX)⟩
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hstar1 : ∀ X : FockOp (D.T N), toCLM (D.T N) Xᴴ = star (toCLM (D.T N) X) := fun X => by
    rw [← Matrix.star_eq_conjTranspose, toCLM_star_dev]
  have hMp1 : ∀ φ : ℝ, ‖(orbOf D N hN h).toSetting.Mplus φ‖ ≤ 1 := fun φ =>
    norm_le_one_of_mem_unitary_dev ((orbOf D N hN h).toSetting.Mplus_mem_unitary φ)
  have hMm1 : ∀ φ : ℝ, ‖(orbOf D N hN h).toSetting.Mminus φ‖ ≤ 1 := fun φ =>
    norm_le_one_of_mem_unitary_dev ((orbOf D N hN h).toSetting.Mminus_mem_unitary φ)
  have hb1 : BddAbove (Set.range fun φ : Set.Icc (0 : ℝ) (2 * π) =>
      ‖toCLM (D.T N) (D.Qf N (D.Mplus φ N) * D.Mminus φ N - D.Mminus φ N * D.Qf N (D.Mplus φ N))‖) := by
    refine ⟨2 * C, ?_⟩
    rintro _ ⟨φ, rfl⟩
    have e : toCLM (D.T N) (D.Qf N (D.Mplus φ N) * D.Mminus φ N - D.Mminus φ N * D.Qf N (D.Mplus φ N)) =
        ⁅(orbOf D N hN h).toSetting.Qf ((orbOf D N hN h).toSetting.Mplus φ),
          (orbOf D N hN h).toSetting.Mminus φ⁆ := by
      rw [(hM φ).2, (hM φ).1, hQf, hlie]
    show ‖toCLM (D.T N) (D.Qf N (D.Mplus φ N) * D.Mminus φ N - D.Mminus φ N * D.Qf N (D.Mplus φ N))‖ ≤ 2 * C
    rw [e]
    exact norm_lie_le_dev (hQfle _ (hMp1 φ)) (hMm1 φ)
  have hb2 : BddAbove (Set.range fun φ : Set.Icc (0 : ℝ) (2 * π) =>
      ‖toCLM (D.T N) (D.Qf N ((D.Mplus φ N)ᴴ) * (D.Mminus φ N)ᴴ -
        (D.Mminus φ N)ᴴ * D.Qf N ((D.Mplus φ N)ᴴ))‖) := by
    refine ⟨2 * C, ?_⟩
    rintro _ ⟨φ, rfl⟩
    have e : toCLM (D.T N) (D.Qf N ((D.Mplus φ N)ᴴ) * (D.Mminus φ N)ᴴ - (D.Mminus φ N)ᴴ * D.Qf N ((D.Mplus φ N)ᴴ)) =
        ⁅(orbOf D N hN h).toSetting.Qf (star ((orbOf D N hN h).toSetting.Mplus φ)),
          star ((orbOf D N hN h).toSetting.Mminus φ)⁆ := by
      rw [(hM φ).2, (hM φ).1, ← hstar1, ← hstar1, hQf, hlie]
    show ‖toCLM (D.T N) (D.Qf N ((D.Mplus φ N)ᴴ) * (D.Mminus φ N)ᴴ -
      (D.Mminus φ N)ᴴ * D.Qf N ((D.Mplus φ N)ᴴ))‖ ≤ 2 * C
    rw [e]
    exact norm_lie_le_dev (hQfle _ ((norm_star _).le.trans (hMp1 φ))) ((norm_star _).le.trans (hMm1 φ))
  have hclu : D.epsClu N ≤ D.eps N := le_max_right _ _
  refine
    { sep_Kminus_Qmid := by
        rw [hKm, hQmid, hlie]; exact hsep2 0 D.Km D.Qmid (by simp [ArgData.sepPairs])
      sep_KUminus_Qmid := by
        rw [hKUm, hQmid, hlie]; exact hsep2 1 D.KUminus D.Qmid (by simp [ArgData.sepPairs])
      sep_Kplus_Qmid := by
        rw [hKp, hQmid, hlie]; exact hsep2 2 D.Kp D.Qmid (by simp [ArgData.sepPairs])
      sep_KUplus_Qmid := by
        rw [hKUp, hQmid, hlie]; exact hsep2 3 D.KUplus D.Qmid (by simp [ArgData.sepPairs])
      sep_Qminus_Kplus := by
        rw [hQm, hKp, hlie]; exact hsep2 4 D.Qminus D.Kp (by simp [ArgData.sepPairs])
      sep_Qminus_KUplus := by
        rw [hQm, hKUp, hlie]; exact hsep2 5 D.Qminus D.KUplus (by simp [ArgData.sepPairs])
      sep_Kminus_Qplus := by
        rw [hKm, hQp, hlie]; exact hsep2 6 D.Km D.Qplus (by simp [ArgData.sepPairs])
      sep_KUminus_Qplus := by
        rw [hKUm, hQp, hlie]; exact hsep2 7 D.KUminus D.Qplus (by simp [ArgData.sepPairs])
      sep_Tminus_Kplus := by
        rw [hTm, hKp, hlie]; exact hsep2 8 D.Tminus D.Kp (by simp [ArgData.sepPairs])
      sep_Tminus_KUplus := by
        rw [hTm, hKUp, hlie]; exact hsep2 9 D.Tminus D.KUplus (by simp [ArgData.sepPairs])
      sep_Kminus_Tplus := by
        rw [hKm, hTp, hlie]; exact hsep2 10 D.Km D.Tplus (by simp [ArgData.sepPairs])
      sep_Kminus_Kplus := by
        rw [hKm, hKp, hlie]; exact hsep2 11 D.Km D.Kp (by simp [ArgData.sepPairs])
      sep_Kminus_KUplus := by
        rw [hKm, hKUp, hlie]; exact hsep2 12 D.Km D.KUplus (by simp [ArgData.sepPairs])
      sep_KUminus_Tplus := by
        rw [hKUm, hTp, hlie]; exact hsep2 13 D.KUminus D.Tplus (by simp [ArgData.sepPairs])
      sep_KUminus_Kplus := by
        rw [hKUm, hKp, hlie]; exact hsep2 14 D.KUminus D.Kp (by simp [ArgData.sepPairs])
      sep_KUminus_KUplus := by
        rw [hKUm, hKUp, hlie]; exact hsep2 15 D.KUminus D.KUplus (by simp [ArgData.sepPairs])
      clu_M := fun φ hφ => by
        rw [(hM φ).2, (hM φ).1, hQf, hlie]
        exact (le_ciSup hb1 ⟨φ, hφ⟩).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hclu))
      clu_M_adj := fun φ hφ => by
        rw [(hM φ).2, (hM φ).1, ← hstar1, ← hstar1, hQf, hlie]
        exact (le_ciSup hb2 ⟨φ, hφ⟩).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hclu))
      clu_O := by
        rw [hOp, hOm, hQf, hlie]
        exact (le_max_left _ _).trans ((le_max_right _ _).trans hclu)
      clu_O_adj := by
        rw [hOp, hOm, ← hstar1, ← hstar1, hQf, hlie]
        exact (le_max_right _ _).trans ((le_max_right _ _).trans hclu)
      norm_n_zero := (norm_toCLM_le_one_of_isStarProjection _ (isStarProjection_njs _ _ _)).trans
        (one_le_Mb_dev D hN)
      norm_Kminus := ?_ }
  have hCh : 0 ≤ D.d.Ch := (norm_nonneg _).trans (D.d.norm_h_le N hN 0)
  have hM0 : 0 ≤ moment (Wfilt D.ϑ D.γ) 0 :=
    integral_nonneg fun t => mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
  rw [hKm]
  have hK := (norm_K_le hD.cutoff hγ D.toIxSetting N hN).1
  have hJ := (norm_J_le D.toIxSetting N hN).1
  unfold ArgData.Mb
  calc ‖toCLM (D.T N) (D.Km N)‖ ≤ moment (Wfilt D.ϑ D.γ) 0 * ‖toCLM (D.T N) (D.Jminus N)‖ := hK
    _ ≤ moment (Wfilt D.ϑ D.γ) 0 * (4 * π * D.d.Ch * (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hJ hM0
    _ ≤ (1 + 4 * π * D.d.Ch * moment (Wfilt D.ϑ D.γ) 0) * (N : ℝ) ^ 2 := by nlinarith [sq_nonneg (N : ℝ)]

/-- **`ε(N)` is `O(N^{−∞})`** (Lemma 6.13(ii) and Corollary 6.15's inputs). -/
theorem eps_isONegInf (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    IsONegInfR D.Ts.idx D.eps := by
  have hS := sep_isONegInf hη hδ₀ D hD hH2
  obtain ⟨h1, h2, h3, h4⟩ := clu_isONegInf hη hδ₀ D hD hH2
  intro k
  choose Cs hCs using fun i : Fin 16 => hS i k
  obtain ⟨C1, hC1⟩ := h1 k
  obtain ⟨C2, hC2⟩ := h2 k
  obtain ⟨C3, hC3⟩ := h3 k
  obtain ⟨C4, hC4⟩ := h4 k
  obtain ⟨Ck, hCk⟩ : ∃ Ck : ℝ, Ck = ∑ i, |Cs i| + |C1| + |C2| + |C3| + |C4| := ⟨_, rfl⟩
  have hsum : ∀ i, |Cs i| ≤ ∑ i, |Cs i| := fun i =>
    Finset.single_le_sum (fun j _ => abs_nonneg (Cs j)) (Finset.mem_univ i)
  have hs0 : 0 ≤ ∑ i, |Cs i| := Finset.sum_nonneg fun j _ => abs_nonneg (Cs j)
  have hA := abs_nonneg C1
  have hB := abs_nonneg C2
  have hC := abs_nonneg C3
  have hD' := abs_nonneg C4
  refine ⟨Ck, fun N hN => ?_⟩
  have hNk : 0 ≤ (N : ℝ) ^ (-(k : ℝ)) := Real.rpow_nonneg (by linarith [one_le_of_mem_idx D.Ts hN]) _
  have hle : ∀ c : ℝ, c ≤ Ck → ∀ x : ℝ, x ≤ c * (N : ℝ) ^ (-(k : ℝ)) → x ≤ Ck * (N : ℝ) ^ (-(k : ℝ)) :=
    fun c hc x hx => hx.trans (mul_le_mul_of_nonneg_right hc hNk)
  have hsep : D.epsSep N ≤ Ck * (N : ℝ) ^ (-(k : ℝ)) := by
    unfold ArgData.epsSep
    refine Finset.sup'_le _ _ fun i _ => hle (Cs i) ?_ _ (hCs i () N hN)
    rw [hCk]
    linarith [le_abs_self (Cs i), hsum i]
  have hne : Nonempty (Set.Icc (0 : ℝ) (2 * π)) := ⟨⟨0, le_rfl, by positivity⟩⟩
  have hclu : D.epsClu N ≤ Ck * (N : ℝ) ^ (-(k : ℝ)) := by
    unfold ArgData.epsClu
    refine max_le (max_le (ciSup_le fun φ => hle C1 ?_ _ (hC1 φ N hN))
      (ciSup_le fun φ => hle C2 ?_ _ (hC2 φ N hN))) (max_le (hle C3 ?_ _ (hC3 () N hN)) (hle C4 ?_ _ (hC4 () N hN)))
    all_goals rw [hCk]
    · linarith [le_abs_self C1]
    · linarith [le_abs_self C2]
    · linarith [le_abs_self C3]
    · linarith [le_abs_self C4]
  have h0 : 0 ≤ D.eps N :=
    le_max_of_le_left ((norm_nonneg _).trans (Finset.le_sup' (fun i : Fin 16 => ‖toCLM (D.T N) (D.sepComm i N)‖)
      (Finset.mem_univ 0)))
  rw [abs_of_nonneg h0]
  exact max_le hsep hclu

/-- **Lemma 6.13(iii)**: "`$\mathcal M(\varphi)\eqN \mathcal M_-(\varphi)\mathcal M_+(\varphi)$`" uniformly in `φ ∈ [0, 2π]`,
and "`$e^{2\pi\iu\Qb}\eqN e^{2\pi\iu\Qb_-}e^{2\pi\iu\Qb_+}$`". -/
theorem factorization_isONegInf (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid)
    (hH2 : D.d.H2) :
    IsONegInf D.Ts (fun (φ : Set.Icc (0 : ℝ) (2 * π)) N => D.Mfull φ N - D.Mminus φ N * D.Mplus φ N) ∧
    IsONegInf D.Ts (fun (_ : Unit) N =>
      NormedSpace.exp ((2 * π * I : ℂ) • D.Qb N) - D.Ominus N * D.Oplus N) := by
  have hE := eps_isONegInf hη hδ₀ D hD hH2
  have key : ∀ N (hN : N ∈ D.Ts.idx),
      (∀ φ : ℝ, ‖toCLM (D.T N) (D.Mfull φ N - D.Mminus φ N * D.Mplus φ N)‖ ≤ 39 / 2 * φ ^ 2 * D.eps N) ∧
        ‖toCLM (D.T N) (NormedSpace.exp ((2 * π * I : ℂ) • D.Qb N) - D.Ominus N * D.Oplus N)‖ ≤
          10 * π ^ 2 * D.eps N := by
    intro N hN
    have h := obligations D hD hH2 N hN
    have hI := inputs_orbOf D hD hN h
    obtain ⟨-, -, -, -, -, -, -, -, -, hQb, -, -, -, -, -, -, hM, hOm, hOp, -⟩ := orbOf_objects D hD hN h
    have hε : 0 ≤ D.eps N := (norm_nonneg _).trans hI.sep_Kminus_Qmid
    have z : ∀ {X Y : FockSpace (D.T N) →L[ℂ] FockSpace (D.T N)}, ⁅X, Y⁆ = 0 → ‖⁅X, Y⁆‖ ≤ D.eps N :=
      fun hXY => by rw [hXY, norm_zero]; exact hε
    have hS : (orbOf D N hN h).toSetting.SepBounds (D.eps N) :=
      ⟨hI.sep_Kminus_Qmid, hI.sep_KUminus_Qmid, hI.sep_Kplus_Qmid, hI.sep_KUplus_Qmid,
        z (orbOf D N hN h).lie_Tminus_Qmid, z (orbOf D N hN h).lie_Tplus_Qmid, hI.sep_Qminus_Kplus,
        hI.sep_Qminus_KUplus, hI.sep_Kminus_Qplus, hI.sep_KUminus_Qplus, z (orbOf D N hN h).lie_Qminus_Tplus,
        z (orbOf D N hN h).lie_Tminus_Qplus, z (orbOf D N hN h).lie_Tminus_Tplus, hI.sep_Tminus_Kplus,
        hI.sep_Tminus_KUplus, hI.sep_Kminus_Tplus, hI.sep_Kminus_Kplus, hI.sep_Kminus_KUplus,
        hI.sep_KUminus_Tplus, hI.sep_KUminus_Kplus, hI.sep_KUminus_KUplus⟩
    have hQbU : (orbOf D N hN h).toSetting.QbarU = toCLM (D.T N) (D.QbarU N) := by
      show star (orbOf D N hN h).toSetting.U * (orbOf D N hN h).toSetting.Qbar * (orbOf D N hN h).toSetting.U = _
      rw [hQb]
      unfold ArgData.QbarU
      rw [toCLM_mul', toCLM_mul', ← Matrix.star_eq_conjTranspose, toCLM_star_dev]
      rfl
    have hMf : ∀ φ : ℝ, (orbOf D N hN h).toSetting.M φ = toCLM (D.T N) (D.Mfull φ N) := by
      intro φ
      rw [(orbOf D N hN h).toSetting.M_eq, ← IndexCore.exp_I_mul_smul, ← IndexCore.exp_neg_I_mul_smul, hQbU, hQb]
      unfold ArgData.Mfull
      rw [toCLM_mul', toCLM_exp_dev, toCLM_exp_dev, toCLM_smul_dev, toCLM_smul_dev]
    refine ⟨fun φ => ?_, ?_⟩
    · rw [toCLM_sub', toCLM_mul', ← hMf, ← (hM φ).1, ← (hM φ).2]
      exact hS.norm_M_sub_le φ
    · rw [toCLM_sub', toCLM_mul', ← hOm, ← hOp, toCLM_exp_dev, toCLM_smul_dev, ← hQb, IndexCore.exp_two_pi_I_smul]
      exact hS.norm_expI_Qbar_sub_le
  have he0 : ∀ N, 0 ≤ D.eps N := fun N =>
    le_max_of_le_left ((norm_nonneg _).trans (Finset.le_sup' (fun i : Fin 16 => ‖toCLM (D.T N) (D.sepComm i N)‖)
      (Finset.mem_univ 0)))
  have hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ N ∈ D.Ts.idx, D.eps N ≤ |C| * (N : ℝ) ^ (-(k : ℝ)) := fun k => by
    obtain ⟨C, hC⟩ := hE k
    refine ⟨C, fun N hN => ?_⟩
    have hNk : 0 ≤ (N : ℝ) ^ (-(k : ℝ)) := Real.rpow_nonneg (by linarith [one_le_of_mem_idx D.Ts hN]) _
    exact (le_abs_self _).trans ((hC N hN).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hNk))
  refine ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨C, hC⟩ := hbd k
    refine ⟨39 / 2 * (2 * π) ^ 2 * |C|, fun φ N hN => ?_⟩
    have hφ : (φ : ℝ) ^ 2 ≤ (2 * π) ^ 2 := pow_le_pow_left₀ φ.2.1 φ.2.2 2
    calc _ ≤ 39 / 2 * (φ : ℝ) ^ 2 * D.eps N := (key N hN).1 φ
      _ ≤ 39 / 2 * (2 * π) ^ 2 * (|C| * (N : ℝ) ^ (-(k : ℝ))) := by
          have := he0 N
          gcongr
          exact hC N hN
      _ = _ := by ring
  · obtain ⟨C, hC⟩ := hbd k
    refine ⟨10 * π ^ 2 * |C|, fun _ N hN => ?_⟩
    calc _ ≤ 10 * π ^ 2 * D.eps N := (key N hN).2
      _ ≤ 10 * π ^ 2 * (|C| * (N : ℝ) ^ (-(k : ℝ))) := by
          gcongr
          exact hC N hN
      _ = _ := by ring

/-! #### Proof device for the limit step (phase (b), round two; not a statement of the paper)

`400 p (c₀ N² + 1) √e ≤ 400 p (|c₀| + 1) √|C₁| N^{−k}` when `|e| ≤ C₁ N^{−(2k+4)}` and `N ≥ 1`: the core's bound
`400 p (M + 1) √ε` with `M = c₀ N²` and `ε = O(N^{−∞})` is `O(N^{−∞})`. -/

section LimitDevices

theorem limit_bound_dev {N : ℕ} (hN : (1 : ℝ) ≤ N) {c₀ C₁ e : ℝ} (k p : ℕ)
    (he : |e| ≤ C₁ * (N : ℝ) ^ (-(((2 * k + 4 : ℕ) : ℝ)))) :
    400 * (p : ℝ) * (c₀ * (N : ℝ) ^ 2 + 1) * Real.sqrt e ≤
      400 * (p : ℝ) * (|c₀| + 1) * Real.sqrt |C₁| * (N : ℝ) ^ (-(k : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  set x : ℝ := (N : ℝ) ^ (-((k : ℝ) + 2)) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx2 : (N : ℝ) ^ (-(((2 * k + 4 : ℕ) : ℝ))) = x ^ 2 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hNx : (N : ℝ) ^ 2 * x = (N : ℝ) ^ (-(k : ℝ)) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  have hs : Real.sqrt e ≤ Real.sqrt |C₁| * x := by
    have h1 : e ≤ |C₁| * x ^ 2 := by
      rw [hx2] at he
      have h2 := le_abs_self e
      have h3 : C₁ * x ^ 2 ≤ |C₁| * x ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      linarith
    calc Real.sqrt e ≤ Real.sqrt (|C₁| * x ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt |C₁| * x := by rw [Real.sqrt_mul (abs_nonneg _), Real.sqrt_sq hx0]
  have hm : c₀ * (N : ℝ) ^ 2 + 1 ≤ (|c₀| + 1) * (N : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : c₀ * (N : ℝ) ^ 2 ≤ |c₀| * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    nlinarith
  calc 400 * (p : ℝ) * (c₀ * (N : ℝ) ^ 2 + 1) * Real.sqrt e
      ≤ 400 * (p : ℝ) * ((|c₀| + 1) * (N : ℝ) ^ 2) * Real.sqrt e := by gcongr
    _ ≤ 400 * (p : ℝ) * ((|c₀| + 1) * (N : ℝ) ^ 2) * (Real.sqrt |C₁| * x) := by gcongr
    _ = 400 * (p : ℝ) * (|c₀| + 1) * Real.sqrt |C₁| * ((N : ℝ) ^ 2 * x) := by ring
    _ = 400 * (p : ℝ) * (|c₀| + 1) * Real.sqrt |C₁| * (N : ℝ) ^ (-(k : ℝ)) := by rw [hNx]

end LimitDevices

/-- **The limit step**: since `p` does not depend on `N`, "`$\dist(p/4,\Z)\le\abs{p/4-n_N}\le CN^{-1}$`" becomes, for the
quantitative core, `400 p (M(N) + 1) √ε(N) < 1/4` for all large `N ∈ 𝒩`. -/
theorem eventually_small (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    ∃ N₀ : ℕ, ∀ N ∈ D.Ts.idx, N₀ ≤ N → 400 * (D.p : ℝ) * (D.Mb N + 1) * Real.sqrt (D.eps N) < 1 / 4 := by
  obtain ⟨C₁, hC₁⟩ := eps_isONegInf hη hδ₀ D hD hH2 (2 * 1 + 4)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 400 * (D.p : ℝ) * (|1 + 4 * π * D.d.Ch * moment (Wfilt D.ϑ D.γ) 0| + 1) *
      Real.sqrt |C₁| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨⌈4 * K⌉₊ + 1, fun N hN hN₀ => ?_⟩
  have hN1 := one_le_of_mem_idx D.Ts hN
  have hb := limit_bound_dev hN1 (c₀ := 1 + 4 * π * D.d.Ch * moment (Wfilt D.ϑ D.γ) 0) 1 D.p (hC₁ N hN)
  rw [← hK, Nat.cast_one, Real.rpow_neg_one] at hb
  refine lt_of_le_of_lt hb ?_
  have hNK : 4 * K < N := by
    have h1 : 4 * K ≤ ⌈4 * K⌉₊ := Nat.le_ceil _
    have h2 : ((⌈4 * K⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN₀
    push_cast at h2
    linarith
  rw [← div_eq_mul_inv, div_lt_iff₀ (by linarith)]
  linarith

/-! ### Theorem 6.18 for `U = Θ` -/

/-- **Theorem 6.18** for `U = Θ` (with Lemma 7.1(b)'s `T_-`): "`Then there are integers $n_N$ such that for every $k$ there is $C_k$ with`"
"`\bigl\lvert\Tr(P_NT_{-,N})-n_N\bigr\rvert\le C_kN^{-k}\qquad\text{for all }N\in\mathcal N .`" -/
theorem index_theorem_Θ (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    ∃ n : ℕ → ℤ, ∀ k : ℕ, ∃ C : ℝ, ∀ N ∈ D.Ts.idx,
      ‖Matrix.trace (D.P N * D.Tminus N) - (n N : ℂ)‖ ≤ C * (N : ℝ) ^ (-(k : ℝ)) := by
  classical
  have key : ∀ N ∈ D.Ts.idx, ∃ m : ℤ, ‖Matrix.trace (D.P N * D.Tminus N) - (m : ℂ)‖ ≤
      400 * (D.p : ℝ) * (D.Mb N + 1) * Real.sqrt (D.eps N) := by
    intro N hN
    have h := obligations D hD hH2 N hN
    obtain ⟨-, -, -, -, -, -, -, hTm, -, -, -, -, -, -, -, hP, -, -, -, -⟩ := orbOf_objects D hD hN h
    obtain ⟨m, hm⟩ := IndexCore.Orbital.translation_corollary (inputs_orbOf D hD hN h)
    rw [orbOf_p D hD hN h] at hm
    have e1 : Matrix.trace (D.P N * D.Tminus N) =
        -(((D.p : ℝ) * (orbOf D N hN h).nup / (orbOf D N hN h).Nφ : ℝ) : ℂ) := by
      rw [← trc_toCLM (T := D.T N), toCLM_mul', ← hP, ← hTm, (orbOf D N hN h).trc_P_Tminus, orbOf_p D hD hN h]
      push_cast
      ring
    refine ⟨-m, ?_⟩
    have e2 : -(((D.p : ℝ) * (orbOf D N hN h).nup / (orbOf D N hN h).Nφ : ℝ) : ℂ) - ((-m : ℤ) : ℂ) =
        ((-((D.p : ℝ) * (orbOf D N hN h).nup / (orbOf D N hN h).Nφ - m) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e1, e2, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    exact hm
  choose! n hn using key
  refine ⟨n, fun k => ?_⟩
  obtain ⟨C₁, hC₁⟩ := eps_isONegInf hη hδ₀ D hD hH2 (2 * k + 4)
  exact ⟨400 * (D.p : ℝ) * (|1 + 4 * π * D.d.Ch * moment (Wfilt D.ϑ D.γ) 0| + 1) * Real.sqrt |C₁|,
    fun N hN => (hn N hN).trans (limit_bound_dev (one_le_of_mem_idx D.Ts hN)
      (c₀ := 1 + 4 * π * D.d.Ch * moment (Wfilt D.ϑ D.γ) 0) k D.p (hC₁ N hN))⟩

end HRTorus.Assembly

end -- noncomputable section
