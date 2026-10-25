import HRTorus.Locality.Filters
import HRTorus.Hamiltonian.LocalForm
import HRTorus.IndexCore.Translation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The setting of the index theorem (T-0056 block E, `Assembly.Setting`)

Written by Claude Opus 5.5 (an AI model; recruit L11), 2026-10-25. **The definitions and statements were written first
and reviewed against the paper (the statement phase, with the review's three additions: `countLE` and
`secEig_eq_sInf_countLE`, and the corrected docstring of `one_le_p_lt_finrank`); proof phase rounds one and two added
the proofs and the proof devices, each section of which is marked as such. No theorem of this module is `sorry`.**
The paper: the HR paper, `papers/hr/sections/06-index-theorem.tex` — Setting 6.1 `set:index`, Lemma 6.2
`lem:separations`, Assumption 6.3 `ass:gap` (with the ordered eigenvalues of §2.5's (2.8) `eq:E11`: "`E_j(N)`" in the
notation table, "eigenvalues in the relevant sector, increasing, with multiplicity"), Definition 6.5 `def:dressing`,
Lemma 6.6 `lem:split`, Lemma 6.7 `lem:KP`, Lemma 6.8 `lem:Klocal`; and the fixed choices of Definition 5.8
`def:filters` (the cutoff `ϑ`, the width `δ` and the mollifier `ζ`) and of the proof of Lemma 6.8 (the light-cone
exponent `α = 4`).

## The model

* **Setting 6.1** is the structure `IxSetting η δ₀`: block B's `TorusSeq δ₀` (the index set `𝒩` and the admissible
  tori), the constant `c_*` with `L_x ≥ c_*√N`, and a sequence `H` with block C's (H1) data `H1Data`. Theorems that the
  paper states "In Setting 6.1" take an `S : IxSetting η δ₀` (with `IsProfile η` and `0 < δ₀` where ι enters).
* **The bands** are the core's `bandΓ`, `quarterMinus`, `quarterMid`, `quarterPlus` at `N_φ = 2N` and the index `N`;
  the charges are block C's `Qband`; the cuts are block B's columns `col δ₀ T 0` and `col δ₀ T N`.
* **The half-tori** are periodic subsets of `ℝ²` (block C's `IsTorusSet` convention): `𝕋⁻_N` is the set of `R` whose
  `R_x` lies in `(−L_x/4, L_x/4]` modulo `L_x` (block B's `circImage`), `𝕋⁺_N` its complement; the translate by `κj₀e_x`
  is `shiftX`. `H_𝒟` for the local terms of general (H1) data is `HDd` (block C's `HD` is the hollow-core case).
* **Definition 6.5**: the currents `J_± = i[H_{𝕋^±}, Q]` are `Jminus`, `Jplus`; the dressing `∫ W_γ(t) τ_t(A) dt` is
  `dress ϑ γ H A` (block D's `opIntegralOn`, `Wfilt`, `dyn` — `τ_t` on `𝓗_N` is `dyn (H N) t`); `K`, `K_±`, `Q̄` are
  `Kfull`, `Kminus`, `Kplus`, `Qbar`, functions of the cutoff `ϑ` and the gap `γ`.
* **The ordered eigenvalues** `E_k` of `H|_{𝓗^𝐧}` with multiplicity (`secEig T H 𝐧 k`, `k = 1, 2, …`): Mathlib's
  spectral theorem (`LinearMap.IsSymmetric.eigenvalues`, sorted decreasingly) applied to the compression `ΠHΠ` of `H` to
  the sector `𝓗^𝐧` (block A's `sector`), read in increasing order: `E_k` is entry `d − k` of the decreasing list,
  `d = dim 𝓗^𝐧`, for `1 ≤ k ≤ d`. Outside `1 ≤ k ≤ d` the index is clamped (`E_0 := E_1`, `E_k := E_d` for `k > d`),
  so that a hypothesis `E_{p+1} − E_p ≥ γ > 0` forces `1 ≤ p < d`, as the paper's "`E_{p+1}`" presupposes; if `H` is not
  self-adjoint, or `d = 0`, every `E_k` is `0` (never used).
* **Assumption 6.3** is `GapAssumption S 𝐧 p Δ γ`, a property of given data (the sectors, `p`, `Δ`, `γ`), and `P = P_N`
  is `ArgData.P` (block A's `cfc` of an indicator times `Π^𝐧`, the form of `specProj_sector`). `ArgData` bundles the
  setting with Assumption 6.3's data and the filters' `ϑ`, `δ`, `ζ`; `ArgData.Valid` is Assumption 6.3 with
  `IsCutoff ϑ` and `ClusterParams Δ γ δ ζ`.
* **The fixed choices**: `cutoff` (a Mathlib `ContDiffBump` with radii `1/4`, `1/2`), `δClust Δ γ = (γ − 2Δ)/4`,
  `ζClust Δ γ` (the normed bump of radii `δ/4`, `δ/2`), `alphaLC = 4`.
-/

open scoped InnerProductSpace Matrix ENNReal Real ComplexConjugate
open Complex (I)
open MeasureTheory Filter

noncomputable section

namespace HRTorus.Assembly

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian HRTorus.Locality
open HRTorus.IndexCore (bandΓ quarterMinus quarterMid quarterPlus)
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op IsEven CAR Alg)

/-! ## Setting 6.1 -/

/-- **Setting 6.1**: "`$\mathcal N\subset\N$ is infinite, $(\Tor_N)_{N\in\mathcal N}$ are admissible tori (Definition~\ref{def:frame}) with $L_x\ge c_*\sqrt N$ for a constant $c_*>0$, and $H=(H_N)_{N\in\mathcal N}$ satisfies (H1).`"
— block B's `TorusSeq` (`𝒩` and the tori), `c_*` with its bound, and `H` with (H1) data. -/
structure IxSetting (η : ℝ → ℝ) (δ₀ : ℝ) where
  /-- the index set `𝒩` and the admissible tori `𝕋_N` -/
  Ts : TorusSeq δ₀
  /-- the constant `c_*` -/
  cstar : ℝ
  cstar_pos : 0 < cstar
  /-- `L_x ≥ c_*√N` -/
  Lx_ge : ∀ N ∈ Ts.idx, cstar * Real.sqrt N ≤ (Ts.T N).Lx
  /-- the Hamiltonians `H_N` -/
  H : (N : ℕ) → FockOp (Ts.T N)
  /-- their (H1) data -/
  d : H1Data η δ₀ Ts H

variable {η : ℝ → ℝ} {δ₀ : ℝ}

namespace IxSetting

variable (S : IxSetting η δ₀)

/-- The torus `𝕋_N`. -/
abbrev T (N : ℕ) : Torus := S.Ts.T N

/-- Setting 6.1: "`Q:=Q_\Gam`" with "`\Gam:=\{0,1,\dots,N-1\}\subset\Z_{\Nphi}`" (the core's `bandΓ`). -/
def Q (N : ℕ) : FockOp (S.T N) := Qband (S.T N) (bandΓ (S.T N).Nφ N)

/-- Setting 6.1: "`Q_\pm:=Q_{\Gamma_\pm}`" — `Q_-` with "`\Gm:=\{0,\dots,\lfloor N/4\rfloor-1\}`". -/
def Qminus (N : ℕ) : FockOp (S.T N) := Qband (S.T N) (quarterMinus (S.T N).Nφ N)

/-- Setting 6.1: "`Q_m:=Q_{\Gmid}`" with "`\Gmid:=\Gam\setminus(\Gm\cup\Gp)`". -/
def Qmid (N : ℕ) : FockOp (S.T N) := Qband (S.T N) (quarterMid (S.T N).Nφ N)

/-- Setting 6.1: `Q_+` with "`\Gp:=\{\lceil3N/4\rceil,\dots,N-1\}`". -/
def Qplus (N : ℕ) : FockOp (S.T N) := Qband (S.T N) (quarterPlus (S.T N).Nφ N)

/-- Setting 6.1: "`\cutm:=\Col(0)`". -/
def cutMinus (N : ℕ) : Finset (Slot δ₀ (S.T N)) := col δ₀ (S.T N) 0

/-- Setting 6.1: "`\cutp:=\Col(N)`". -/
def cutPlus (N : ℕ) : Finset (Slot δ₀ (S.T N)) := col δ₀ (S.T N) N

end IxSetting

/-! ### The half-tori and `H_𝒟` -/

/-- Setting 6.1: "`$\Tor_N^-:=\{R\in\Tor_N:R_x\in(-L_x/4,L_x/4]\bmod L_x\}$`" — as a periodic subset of `ℝ²`. -/
def halfMinus (T : Torus) : Set (ℝ × ℝ) :=
  {R | R.1 ∈ circImage T.Lx (Set.Ioc (-(T.Lx / 4)) (T.Lx / 4))}

/-- Setting 6.1: "`$\Tor_N^+:=\Tor_N\setminus\Tor_N^-$`". -/
def halfPlus (T : Torus) : Set (ℝ × ℝ) :=
  (halfMinus T)ᶜ

/-- Lemma 6.6(iii): the translate "`$\Tor_N^\pm+\kappa j_0\ex$`" of a periodic set `D` by `κj₀e_x`. -/
def shiftX (T : Torus) (j₀ : ℤ) (D : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {R | R - (T.κ * j₀, 0) ∈ D}

/-- Lemma 6.6(iii): "`the band $\Gam+j_0$`". -/
def bandShift (Nφ N : ℕ) (j₀ : ℤ) : Finset (ZMod Nφ) :=
  (bandΓ Nφ N).image fun j => j + (j₀ : ZMod Nφ)

namespace IxSetting

variable (S : IxSetting η δ₀)

/-- Setting 6.1: "`For a Borel set $\mathcal D\subset\Tor_N$ write $H_{\mathcal D}:=\int_{\mathcal D}h_R\,\dd R$.`" — with the
local terms of the (H1) data, over the part of the periodic set in the fundamental domain (block C's `HD` for the
hollow-core `h_R`). -/
def HDd (N : ℕ) (D : Set (ℝ × ℝ)) : FockOp (S.T N) :=
  opIntegral (D ∩ fundDom (S.T N)) (S.d.h N)

/-- The current `i[H_𝒟, Q_B]` of a periodic set `𝒟` and a band `B`. -/
def curr (N : ℕ) (D : Set (ℝ × ℝ)) (B : Finset (ZMod (S.T N).Nφ)) : FockOp (S.T N) :=
  (I : ℂ) • (S.HDd N D * Qband (S.T N) B - Qband (S.T N) B * S.HDd N D)

/-- **Definition 6.5**: "`J_\pm:=\iu\bigl[H_{\Tor_N^\pm},Q\bigr]`" — `J_-`. -/
def Jminus (N : ℕ) : FockOp (S.T N) :=
  S.curr N (halfMinus (S.T N)) (bandΓ (S.T N).Nφ N)

/-- **Definition 6.5**: `J_+`. -/
def Jplus (N : ℕ) : FockOp (S.T N) :=
  S.curr N (halfPlus (S.T N)) (bandΓ (S.T N).Nφ N)

/-- Lemma 6.6(iii): the translated current `J_-` "`for the band $\Gam+j_0$, the half-tori $\Tor_N^\pm+\kappa j_0\ex$`". -/
def JminusShift (j₀ : ℤ) (N : ℕ) : FockOp (S.T N) :=
  S.curr N (shiftX (S.T N) j₀ (halfMinus (S.T N))) (bandShift (S.T N).Nφ N j₀)

/-- Lemma 6.6(iii): the translated current `J_+`. -/
def JplusShift (j₀ : ℤ) (N : ℕ) : FockOp (S.T N) :=
  S.curr N (shiftX (S.T N) j₀ (halfPlus (S.T N))) (bandShift (S.T N).Nφ N j₀)

end IxSetting

/-- The dressing `∫ W_γ(t) τ_t(A) dt` on `𝓗_N` (Definition 6.5's integrals; block D's entrywise `opIntegralOn` over `ℝ`,
`W_γ = Wfilt ϑ γ`, `τ_t = dyn H t`). -/
def dress {T : Torus} (ϑ : ℝ → ℝ) (γ : ℝ) (H A : FockOp T) : FockOp T :=
  opIntegralOn Set.univ fun t => Wfilt ϑ γ t • dyn H t A

namespace IxSetting

variable (S : IxSetting η δ₀)

/-- **Definition 6.5**: "`K:=\int\Wg(t)\,\tau_t\bigl(\iu[H_N,Q]\bigr)\,\dd t`". -/
def Kfull (ϑ : ℝ → ℝ) (γ : ℝ) (N : ℕ) : FockOp (S.T N) :=
  dress ϑ γ (S.H N) ((I : ℂ) • (S.H N * S.Q N - S.Q N * S.H N))

/-- **Definition 6.5**: "`K_\pm:=\int\Wg(t)\,\tau_t(J_\pm)\,\dd t`" — `K_-`. -/
def Kminus (ϑ : ℝ → ℝ) (γ : ℝ) (N : ℕ) : FockOp (S.T N) :=
  dress ϑ γ (S.H N) (S.Jminus N)

/-- **Definition 6.5**: `K_+`. -/
def Kplus (ϑ : ℝ → ℝ) (γ : ℝ) (N : ℕ) : FockOp (S.T N) :=
  dress ϑ γ (S.H N) (S.Jplus N)

/-- **Definition 6.5**: "`\Qb:=Q-K_--K_+`". -/
def Qbar (ϑ : ℝ → ℝ) (γ : ℝ) (N : ℕ) : FockOp (S.T N) :=
  S.Q N - S.Kminus ϑ γ N - S.Kplus ϑ γ N

end IxSetting

/-! ## The ordered eigenvalues of a sector, and Assumption 6.3 -/

/-- The compression `ΠHΠ` of an operator `H` on `𝓗_N` to the sector `𝓗^𝐧`, as a linear map of the sector to itself
(Mathlib's orthogonal projection onto the subspace). For a sector-preserving `H` it is the restriction
"`$H_N|_{\sect{\nn_N}}$`". -/
def secCompr (T : Torus) (H : FockOp T) (nn : SectorLabel T) : sector T nn →ₗ[ℂ] sector T nn :=
  (((sector T nn).orthogonalProjectionOnto ∘L toCLM T H ∘L (sector T nn).subtypeL :
    sector T nn →L[ℂ] sector T nn) : sector T nn →ₗ[ℂ] sector T nn)

open Classical in
/-- The eigenvalues of the compression with multiplicity, in Mathlib's decreasing order
(`LinearMap.IsSymmetric.eigenvalues`); `0` if the compression is not symmetric (never used). -/
def secEigDesc (T : Torus) (H : FockOp T) (nn : SectorLabel T) : Fin (Module.finrank ℂ (sector T nn)) → ℝ :=
  if h : (secCompr T H nn).IsSymmetric then
    LinearMap.IsSymmetric.eigenvalues (𝕜 := ℂ) (E := sector T nn) h rfl
  else fun _ => 0

/-- **The ordered eigenvalues** "`$E_1\le E_2\le\cdots$ of $H_N|_{\sect{\nn_N}}$, repeated according to multiplicity`"
(Assumption 6.3): `E_k` is entry `d − k` of the decreasing list, `d = dim 𝓗^𝐧`, for `1 ≤ k ≤ d`; the index is clamped
outside `[1, d]` (the module docstring). -/
def secEig (T : Torus) (H : FockOp T) (nn : SectorLabel T) (k : ℕ) : ℝ :=
  if hd : 0 < Module.finrank ℂ (sector T nn) then
    secEigDesc T H nn ⟨Module.finrank ℂ (sector T nn) - min (max k 1) (Module.finrank ℂ (sector T nn)),
      by omega⟩
  else 0

/-- The counting function of the eigenvalues (added at the statement review, round one; the fresh reader's `countLE`, in
recruit L12's `Blind.lean`, the blind derivation of Theorem 8.1's statement): the dimension of the span of the eigenvectors
of `H` lying in the sector `𝓗^𝐧` with eigenvalue `≤ E` — the range of the spectral projection of `H|_{𝓗^𝐧}` onto `(−∞, E]`,
extended by zero, in the form of block A's `specProj_sector`. -/
def countLE (T : Torus) (H : FockOp T) (nn : SectorLabel T) (E : ℝ) : ℕ :=
  Module.finrank ℂ ↥(⨆ μ ∈ Set.Iic E,
    Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) H)
      (μ : ℂ) ⊓ sector T nn)

/-- **Assumption 6.3** (gap in a sector), for given data: "`There are sectors $\nn_N=(n_{\up,N},n_{\dn,N})$, $N\in\mathcal N$, and $p\in\N$, $\Delta\ge0$ and $\gamma>2\Delta$, independent of $N$, such that the eigenvalues $E_1\le E_2\le\cdots$ of $H_N|_{\sect{\nn_N}}$, repeated according to multiplicity, satisfy`"
"`E_p-E_1\le\Delta\qquad\text{and}\qquad E_{p+1}-E_p\ge\gamma\qquad\text{for every }N\in\mathcal N .`" -/
structure GapAssumption (S : IxSetting η δ₀) (nn : (N : ℕ) → SectorLabel (S.T N)) (p : ℕ) (Δ γ : ℝ) :
    Prop where
  Δ_nonneg : 0 ≤ Δ
  two_mul_Δ_lt : 2 * Δ < γ
  spread : ∀ N ∈ S.Ts.idx, secEig (S.T N) (S.H N) (nn N) p - secEig (S.T N) (S.H N) (nn N) 1 ≤ Δ
  gap : ∀ N ∈ S.Ts.idx, γ ≤ secEig (S.T N) (S.H N) (nn N) (p + 1) - secEig (S.T N) (S.H N) (nn N) p

/-- The data of §6's argument on top of Setting 6.1: Assumption 6.3's sectors `𝐧_N`, rank `p`, spread `Δ` and gap
`γ`, and the filters' cutoff `ϑ`, width `δ` and mollifier `ζ` (Definition 5.8). -/
structure ArgData (η : ℝ → ℝ) (δ₀ : ℝ) extends IxSetting η δ₀ where
  /-- the sectors `𝐧_N` -/
  nn : (N : ℕ) → SectorLabel (Ts.T N)
  /-- the rank `p` -/
  p : ℕ
  /-- the spread `Δ` -/
  Δ : ℝ
  /-- the gap `γ` -/
  γ : ℝ
  /-- the cutoff `ϑ` of `Ŵ_γ` -/
  ϑ : ℝ → ℝ
  /-- the width `δ` of the mollifier -/
  δ : ℝ
  /-- the mollifier `ζ` of the clustering step `g` -/
  ζ : ℝ → ℝ

namespace ArgData

variable (D : ArgData η δ₀)

/-- `E_k(N)`: the ordered eigenvalues of `H_N|_{𝓗^{𝐧_N}}`. -/
abbrev E (N k : ℕ) : ℝ := secEig (D.T N) (D.H N) (D.nn N) k

/-- Assumption 6.3: "`$P=P_N$ denotes the spectral projection of $H_N|_{\sect{\nn_N}}$ onto $[E_1,E_p]$, extended by zero to $\Fock$`"
— `1_{[E_1, E_p]}(H_N) Π^{𝐧_N}` (block A's `specProj_sector` form). -/
def P (N : ℕ) : FockOp (D.T N) :=
  cfc ((Set.Icc (D.E N 1) (D.E N D.p)).indicator (1 : ℝ → ℝ)) (D.H N) * Psec (D.T N) (D.nn N)

/-- The validity of the data: Assumption 6.3 for `(𝐧_N, p, Δ, γ)`, Definition 5.8's conditions on the cutoff `ϑ` and
on `(Δ, γ, δ, ζ)`. -/
structure Valid : Prop where
  gap : GapAssumption D.toIxSetting D.nn D.p D.Δ D.γ
  cutoff : IsCutoff D.ϑ
  clust : ClusterParams D.Δ D.γ D.δ D.ζ

end ArgData

/-! ## The fixed choices of Definition 5.8 and of the proof of Lemma 6.8 -/

/-- Definition 5.8: "`Fix an even $\vartheta\in C_c^\infty((-1,1))$ with $0\le\vartheta\le1$ and $\vartheta=1$ near $0$.`"
— the choice: Mathlib's smooth bump `ContDiffBump` at `0` with inner radius `1/4` and outer radius `1/2`. -/
def cutoff : ℝ → ℝ :=
  ⇑(⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ))

/-- Definition 5.8: "`fix $\delta\in(0,\gamma/2-\Delta)$`" — the choice `δ = (γ − 2Δ)/4`. -/
def δClust (Δ γ : ℝ) : ℝ :=
  (γ - 2 * Δ) / 4

open Classical in
/-- Definition 5.8: "`$\zeta\in C_c^\infty((-\delta,\delta))$ with $\zeta\ge0$ and $\int\zeta=1$`" — the choice: Mathlib's
normed bump (`ContDiffBump.normed`) at `0` with radii `δ/4` and `δ/2`, `δ = δClust Δ γ` (`0` if `δ ≤ 0`, never used). -/
def ζClust (Δ γ : ℝ) : ℝ → ℝ :=
  if h : 0 < δClust Δ γ then
    (⟨δClust Δ γ / 4, δClust Δ γ / 2, by positivity, by linarith⟩ : ContDiffBump (0 : ℝ)).normed volume
  else fun _ => 0

/-- The proof of Lemma 6.8: "`for the light-cone exponent $\alpha=4$`". -/
def alphaLC : ℝ := 4

/-- Definition 3.1: "`and $\delta_0=\sqrt\pi$`" — the target slot width of the proof (with the profile `SlotFrame.etaStd`,
"`for definiteness $\eta(u)=e^{-1/(1-u^2)}$`"). -/
def δstd : ℝ := Real.sqrt π

/-- The standard data on top of a setting: Assumption 6.3's `(𝐧_N, p, Δ, γ)` with the fixed choices `cutoff`,
`δClust Δ γ`, `ζClust Δ γ`. -/
abbrev ArgData.std (S : IxSetting η δ₀) (nn : (N : ℕ) → SectorLabel (S.T N)) (p : ℕ) (Δ γ : ℝ) : ArgData η δ₀ :=
  { toIxSetting := S, nn := nn, p := p, Δ := Δ, γ := γ, ϑ := cutoff, δ := δClust Δ γ, ζ := ζClust Δ γ }

/-! ## Statements -/

/-! ### The fixed choices -/

/-- The choice `cutoff` satisfies Definition 5.8's conditions. -/
theorem isCutoff_cutoff : IsCutoff cutoff := by
  set f : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ with hf
  have hc : cutoff = ⇑f := rfl
  rw [hc]
  refine ⟨f.contDiff, ?_, fun w => f.neg w, fun w => f.nonneg, fun w => f.le_one, ?_⟩
  · rw [f.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx
    have h2 : f.rOut = 1 / 2 := rfl
    rw [h2] at hx
    obtain ⟨h1, h3⟩ := abs_le.mp hx
    exact ⟨by linarith, by linarith⟩
  · exact f.eventuallyEq_one.mono fun w hw => hw

/-- The choices `δClust`, `ζClust` satisfy Definition 5.8's conditions for every `Δ ≥ 0` and `γ > 2Δ`. -/
theorem clusterParams_std {Δ γ : ℝ} (hΔ : 0 ≤ Δ) (hγ : 2 * Δ < γ) :
    ClusterParams Δ γ (δClust Δ γ) (ζClust Δ γ) := by
  have hδ : 0 < δClust Δ γ := by unfold δClust; linarith
  set g : ContDiffBump (0 : ℝ) := ⟨δClust Δ γ / 4, δClust Δ γ / 2, by positivity, by linarith⟩ with hg
  have hζ : ζClust Δ γ = g.normed volume := by
    unfold ζClust
    rw [dif_pos hδ]
  rw [hζ]
  refine ⟨hΔ, hγ, hδ, ?_, g.contDiff_normed, ?_, g.nonneg_normed, g.integral_normed⟩
  · unfold δClust
    linarith
  · rw [g.tsupport_normed_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx
    have h2 : g.rOut = δClust Δ γ / 2 := rfl
    rw [h2] at hx
    obtain ⟨h1, h3⟩ := abs_le.mp hx
    exact ⟨by linarith, by linarith⟩

/-- The standard data are valid under Assumption 6.3. -/
theorem ArgData.valid_std {S : IxSetting η δ₀} {nn : (N : ℕ) → SectorLabel (S.T N)} {p : ℕ} {Δ γ : ℝ}
    (h : GapAssumption S nn p Δ γ) : (ArgData.std S nn p Δ γ).Valid :=
  ⟨h, isCutoff_cutoff, clusterParams_std h.Δ_nonneg h.two_mul_Δ_lt⟩

/-! ### Proof devices for the ordered eigenvalues (phase (b), round one; not statements of the paper)

The sector projection is the orthogonal projection onto the sector; a sector-preserving `H` maps the sector into itself,
so its compression acts on sector vectors as `H` and is symmetric when `H` is self-adjoint; `cfc f H` acts on an
eigenvector by `f` of its eigenvalue (block A's polynomial interpolation, as in the proof of `specProj_sector`); the index
translation `k ↦ d − k` between the increasing and Mathlib's decreasing order. -/

section EigDevices

theorem toCLM_Psec_dev (T : Torus) (nn : SectorLabel T) : toCLM T (Psec T nn) = (sector T nn).starProjection :=
  (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)).apply_symm_apply _

theorem toEuclideanLin_apply_dev {T : Torus} (M : FockOp T) (w : FockSpace T) :
    Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) M w = toCLM T M w := by
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  rfl

theorem mem_sector_iff_Psec_dev {T : Torus} (nn : SectorLabel T) (v : FockSpace T) :
    v ∈ sector T nn ↔ toCLM T (Psec T nn) v = v := by
  rw [toCLM_Psec_dev]
  exact Submodule.starProjection_eq_self_iff.symm

theorem toCLM_mem_sector_dev {T : Torus} {H : FockOp T} (hHs : IsSectorPreserving T H) (nn : SectorLabel T)
    {v : FockSpace T} (hv : v ∈ sector T nn) : toCLM T H v ∈ sector T nn := by
  have hc : Commute H (Psec T nn) := (isSectorPreserving_iff_commute T H).mp hHs nn
  rw [mem_sector_iff_Psec_dev] at hv ⊢
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← hc.eq, map_mul, ContinuousLinearMap.mul_apply, hv]

theorem secCompr_coe_dev {T : Torus} {H : FockOp T} (hHs : IsSectorPreserving T H) (nn : SectorLabel T)
    (v : sector T nn) : ((secCompr T H nn v : sector T nn) : FockSpace T) = toCLM T H v := by
  have hm := toCLM_mem_sector_dev hHs nn v.2
  have h1 : secCompr T H nn v = (sector T nn).orthogonalProjectionOnto (toCLM T H v) := rfl
  rw [h1, show (sector T nn).orthogonalProjectionOnto (toCLM T H v) = ⟨toCLM T H v, hm⟩ from
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, hm⟩]

theorem secCompr_isSymmetric_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (nn : SectorLabel T) : LinearMap.IsSymmetric (𝕜 := ℂ) (E := sector T nn) (secCompr T H nn) := by
  intro v w
  rw [Submodule.coe_inner, Submodule.coe_inner, secCompr_coe_dev hHs, secCompr_coe_dev hHs]
  have h := (hH.map (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ))).isSymmetric (v : FockSpace T)
    (w : FockSpace T)
  simpa using h

theorem secEigDesc_eq_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (nn : SectorLabel T) :
    secEigDesc T H nn =
      LinearMap.IsSymmetric.eigenvalues (𝕜 := ℂ) (E := sector T nn) (secCompr_isSymmetric_dev hH hHs nn) rfl := by
  unfold secEigDesc
  rw [dif_pos (secCompr_isSymmetric_dev hH hHs nn)]

theorem secEigDesc_antitone_dev (T : Torus) (H : FockOp T) (nn : SectorLabel T) : Antitone (secEigDesc T H nn) := by
  unfold secEigDesc
  split_ifs with h
  · exact LinearMap.IsSymmetric.eigenvalues_antitone (𝕜 := ℂ) (E := sector T nn) h rfl
  · exact fun _ _ _ => le_rfl

theorem secEig_eq_dev {T : Torus} {H : FockOp T} {nn : SectorLabel T} (hd : 0 < Module.finrank ℂ (sector T nn))
    {k : ℕ} (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℂ (sector T nn)) :
    secEig T H nn k = secEigDesc T H nn ⟨Module.finrank ℂ (sector T nn) - k, by omega⟩ := by
  unfold secEig
  rw [dif_pos hd]
  congr 2
  omega

theorem secEig_congr_dev {T : Torus} {H : FockOp T} {nn : SectorLabel T} {a b : ℕ}
    (h : min (max a 1) (Module.finrank ℂ (sector T nn)) = min (max b 1) (Module.finrank ℂ (sector T nn))) :
    secEig T H nn a = secEig T H nn b := by
  unfold secEig
  split_ifs with hd
  · congr 2
    omega
  · rfl

theorem secEig_of_finrank_eq_zero_dev {T : Torus} {H : FockOp T} {nn : SectorLabel T}
    (hd : Module.finrank ℂ (sector T nn) = 0) (k : ℕ) : secEig T H nn k = 0 := by
  unfold secEig
  rw [dif_neg (by omega)]

/-- `cfc f H` acts on an eigenvector of a self-adjoint `H` by `f` of its eigenvalue. -/
theorem toCLM_cfc_eigen_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (f : ℝ → ℝ) {μ : ℝ}
    {w : FockSpace T} (hw : toCLM T H w = (μ : ℂ) • w) : toCLM T (cfc f H) w = ((f μ : ℝ) : ℂ) • w := by
  by_cases hw0 : w = 0
  · subst hw0
    simp
  have hspec : μ ∈ spectrum ℝ H := by
    rw [spectrum.mem_iff]
    intro hu
    apply hw0
    obtain ⟨M, hM⟩ := hu.exists_left_inv
    have h0 : toCLM T (algebraMap ℝ (FockOp T) μ - H) w = 0 := by
      show Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (algebraMap ℝ (FockOp T) μ - H) w = 0
      rw [map_sub, ContinuousLinearMap.sub_apply, hw, Algebra.algebraMap_eq_smul_one (A := FockOp T) μ,
        ← Complex.coe_smul, map_smul, map_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        sub_self]
    have e1 : toCLM T (1 : FockOp T) = 1 := map_one (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ))
    calc w = toCLM T (M * (algebraMap ℝ (FockOp T) μ - H)) w := by rw [hM, e1]; rfl
      _ = 0 := by rw [toCLM_mul', ContinuousLinearMap.mul_apply, h0, map_zero]
  obtain ⟨q, hq⟩ := exists_poly_interp (Matrix.finite_real_spectrum (A := H)).toFinset f
  have hPq : cfc f H = Polynomial.aeval H q := by
    rw [cfc_congr (g := fun x => q.eval x) ?_, cfc_polynomial q H hH]
    intro x hx
    exact (hq x ((Set.Finite.mem_toFinset _).mpr hx)).symm
  rw [hPq, toCLM_aeval_eigen T H (μ : ℂ) w hw q]
  congr 1
  rw [← hq μ ((Set.Finite.mem_toFinset _).mpr hspec)]
  rw [show ((μ : ℝ) : ℂ) = algebraMap ℝ ℂ μ from rfl, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  rfl

/-- The eigenvectors of the compression, as vectors of `𝓗_N`, are eigenvectors of `H`. -/
theorem apply_eigenvector_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (nn : SectorLabel T) (i : Fin (Module.finrank ℂ (sector T nn))) :
    toCLM T H ((secCompr_isSymmetric_dev hH hHs nn).eigenvectorBasis rfl i : FockSpace T) =
      ((secEigDesc T H nn i : ℝ) : ℂ) • ((secCompr_isSymmetric_dev hH hHs nn).eigenvectorBasis rfl i : FockSpace T) := by
  rw [← secCompr_coe_dev hHs nn, (secCompr_isSymmetric_dev hH hHs nn).apply_eigenvectorBasis rfl i,
    secEigDesc_eq_dev hH hHs nn]
  simp

/-- The bijection `k ↦ d − k` between the indices `1 … d` of the increasing order and Mathlib's decreasing order. -/
theorem card_filter_secEig_dev {T : Torus} (H : FockOp T) (nn : SectorLabel T) (P : ℝ → Prop) [DecidablePred P] :
    ((Finset.Icc 1 (Module.finrank ℂ (sector T nn))).filter fun k => P (secEig T H nn k)).card =
      (Finset.univ.filter fun i : Fin (Module.finrank ℂ (sector T nn)) => P (secEigDesc T H nn i)).card := by
  refine Finset.card_bij' (fun k hk => (⟨Module.finrank ℂ (sector T nn) - k, by
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk; omega⟩ : Fin _))
    (fun i _ => Module.finrank ℂ (sector T nn) - i.val) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← secEig_eq_dev (by omega) hk.1.1 hk.1.2]
    exact hk.2
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hi2 := i.2
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [secEig_eq_dev (by omega) (by omega) (by omega)]
    convert hi using 2
    ext
    simp only
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    simp only
    omega
  · intro i hi
    ext
    simp only
    have := i.2
    omega

end EigDevices

/-! ### The ordered eigenvalues -/

/-- "`$E_1\le E_2\le\cdots$`": the ordered eigenvalues are increasing. -/
theorem secEig_mono (T : Torus) (H : FockOp T) (nn : SectorLabel T) : Monotone (secEig T H nn) := by
  intro a b hab
  unfold secEig
  split_ifs with hd
  · exact secEigDesc_antitone_dev T H nn (by simp only [Fin.mk_le_mk]; omega)
  · exact le_rfl

/-- For self-adjoint sector-preserving `H` and `1 ≤ k ≤ dim 𝓗^𝐧`, `E_k` is an eigenvalue of `H` on a nonzero vector of
the sector. -/
theorem secEig_hasEigenvector {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (nn : SectorLabel T) {k : ℕ} (hk : 1 ≤ k) (hkd : k ≤ Module.finrank ℂ (sector T nn)) :
    ∃ v ∈ sector T nn, v ≠ 0 ∧ toCLM T H v = (secEig T H nn k : ℂ) • v := by
  have hd : 0 < Module.finrank ℂ (sector T nn) := by omega
  set b := (secCompr_isSymmetric_dev hH hHs nn).eigenvectorBasis rfl with hb
  have hlt : Module.finrank ℂ (sector T nn) - k < Module.finrank ℂ (sector T nn) := by omega
  refine ⟨(b ⟨Module.finrank ℂ (sector T nn) - k, hlt⟩ : FockSpace T), Submodule.coe_mem _, ?_, ?_⟩
  · intro h0
    have h1 := b.orthonormal.1 ⟨Module.finrank ℂ (sector T nn) - k, hlt⟩
    rw [← Submodule.norm_coe, h0, norm_zero] at h1
    exact zero_ne_one h1
  · rw [hb, apply_eigenvector_dev hH hHs nn, secEig_eq_dev hd hk hkd]

/-- Every eigenvalue of a self-adjoint sector-preserving `H` on a nonzero vector of the sector is some `E_k`,
`1 ≤ k ≤ dim 𝓗^𝐧`. -/
theorem exists_secEig_eq {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    {nn : SectorLabel T} {μ : ℝ} {v : FockSpace T} (hv : v ∈ sector T nn) (hv0 : v ≠ 0)
    (hHv : toCLM T H v = (μ : ℂ) • v) :
    ∃ k, 1 ≤ k ∧ k ≤ Module.finrank ℂ (sector T nn) ∧ secEig T H nn k = μ := by
  have hT := secCompr_isSymmetric_dev hH hHs nn
  have hev : Module.End.HasEigenvalue (secCompr T H nn) (μ : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hv⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      apply Subtype.ext
      rw [secCompr_coe_dev hHs]
      simpa using hHv
    · intro h
      apply hv0
      simpa using congrArg Subtype.val h
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq rfl hev
  have hd : 0 < Module.finrank ℂ (sector T nn) := Fin.pos i
  have hi2 := i.2
  refine ⟨Module.finrank ℂ (sector T nn) - i.val, by omega, by omega, ?_⟩
  rw [secEig_eq_dev hd (by omega) (by omega), secEigDesc_eq_dev hH hHs]
  have he : (⟨Module.finrank ℂ (sector T nn) - (Module.finrank ℂ (sector T nn) - i.val), by omega⟩ :
      Fin (Module.finrank ℂ (sector T nn))) = i := Fin.ext (by simp only; omega)
  rw [he]
  have hi' : ((hT.eigenvalues rfl i : ℝ) : ℂ) = (μ : ℂ) := hi
  exact Complex.ofReal_injective hi'

/-- "`repeated according to multiplicity`": the number of `k ∈ [1, dim 𝓗^𝐧]` with `E_k = μ` is the dimension of the
`μ`-eigenspace of `H` in the sector. -/
theorem card_secEig_eq {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (nn : SectorLabel T) (μ : ℝ) :
    ((Finset.Icc 1 (Module.finrank ℂ (sector T nn))).filter fun k => secEig T H nn k = μ).card =
      Module.finrank ℂ ↥(Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) H) (μ : ℂ) ⊓ sector T nn) := by
  classical
  have hT := secCompr_isSymmetric_dev hH hHs nn
  rw [card_filter_secEig_dev H nn (fun x => x = μ), secEigDesc_eq_dev hH hHs nn]
  have h1 := hT.card_filter_eigenvalues_eq rfl (μ : ℂ)
  have hle : Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) H) (μ : ℂ) ⊓ sector T nn ≤ sector T nn := inf_le_right
  have heq : Module.End.eigenspace (secCompr T H nn) (μ : ℂ) =
      (Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) H) (μ : ℂ) ⊓ sector T nn).comap (sector T nn).subtype := by
    ext v
    simp only [Module.End.mem_eigenspace_iff, Submodule.mem_comap, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · intro h
      refine ⟨?_, v.2⟩
      rw [toEuclideanLin_apply_dev, ← secCompr_coe_dev hHs, h]
      simp
    · rintro ⟨h, -⟩
      ext
      rw [secCompr_coe_dev hHs, ← toEuclideanLin_apply_dev, h]
      simp
  rw [← (Submodule.comapSubtypeEquivOfLe hle).finrank_eq, ← heq, ← h1]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact congrArg Complex.ofReal h
  · intro h
    have h' : ((hT.eigenvalues rfl i : ℝ) : ℂ) = (μ : ℂ) := h
    exact Complex.ofReal_injective h'

open Classical in
/-- The spectral-projection characterization: for every set `B ⊆ ℝ`, the number of `k ∈ [1, dim 𝓗^𝐧]` with `E_k ∈ B` is
the rank of `1_B(H) Π^𝐧` (block A's `specProj_sector`: the spectral projection of `H|_{𝓗^𝐧}` onto `B`, extended by zero). -/
theorem card_secEig_mem {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (nn : SectorLabel T) (B : Set ℝ) :
    ((Finset.Icc 1 (Module.finrank ℂ (sector T nn))).filter fun k => secEig T H nn k ∈ B).card =
      (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn).rank := by
  have hT := secCompr_isSymmetric_dev hH hHs nn
  set b := hT.eigenvectorBasis rfl with hb
  have hrank : (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn).rank =
      Module.finrank ℂ (LinearMap.range ((toCLM T (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn)) :
        FockSpace T →ₗ[ℂ] FockSpace T)) := by
    rw [Matrix.rank_eq_finrank_range_toLin _ (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis
      (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis]
    rfl
  have hrange : LinearMap.range ((toCLM T (cfc (B.indicator (1 : ℝ → ℝ)) H * Psec T nn)) :
      FockSpace T →ₗ[ℂ] FockSpace T) =
      Submodule.span ℂ (Set.range fun i : {i : Fin (Module.finrank ℂ (sector T nn)) // secEigDesc T H nn i ∈ B} =>
        (b i.1 : FockSpace T)) := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      have hPw : toCLM T (Psec T nn) w = ∑ i, ⟪b i, (sector T nn).orthogonalProjectionOnto w⟫_ℂ • (b i : FockSpace T) := by
        rw [toCLM_Psec_dev, Submodule.starProjection_apply]
        conv_lhs => rw [← b.sum_repr' ((sector T nn).orthogonalProjectionOnto w)]
        simp only [Submodule.coe_sum, Submodule.coe_smul]
      simp only [ContinuousLinearMap.coe_coe, map_mul, ContinuousLinearMap.mul_apply, hPw, map_sum, map_smul]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hb, toCLM_cfc_eigen_dev hH _ (apply_eigenvector_dev hH hHs nn i)]
      by_cases hi : secEigDesc T H nn i ∈ B
      · rw [Set.indicator_of_mem hi]
        refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩))
      · rw [Set.indicator_of_notMem hi]
        simp
    · rw [Submodule.span_le]
      rintro _ ⟨⟨i, hi⟩, rfl⟩
      refine ⟨(b i : FockSpace T), ?_⟩
      simp only [ContinuousLinearMap.coe_coe, map_mul, ContinuousLinearMap.mul_apply]
      rw [(mem_sector_iff_Psec_dev nn _).mp (b i).2, hb,
        toCLM_cfc_eigen_dev hH _ (apply_eigenvector_dev hH hHs nn i), Set.indicator_of_mem hi]
      simp
  have hli : LinearIndependent ℂ (fun i : {i : Fin (Module.finrank ℂ (sector T nn)) // secEigDesc T H nn i ∈ B} =>
      (b i.1 : FockSpace T)) := by
    have ho := b.orthonormal.comp_linearIsometry (sector T nn).subtypeₗᵢ
    exact (ho.comp Subtype.val Subtype.val_injective).linearIndependent
  rw [hrank, hrange, finrank_span_eq_card hli, card_filter_secEig_dev H nn (· ∈ B), Fintype.card_subtype]

/-- **The counting form of the ordered eigenvalues** (added at the statement review, round one: the fresh reader's
`eigAsc`, in recruit L12's `Blind.lean`): for self-adjoint sector-preserving `H`, `E_k` is the least `E` at which at least
`k` eigenvalues of `H|_{𝓗^𝐧}` are `≤ E` (`countLE`), the index clamped to `1, …, d` as in `secEig`. -/
theorem secEig_eq_sInf_countLE {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    (nn : SectorLabel T) (k : ℕ) :
    secEig T H nn k = sInf {E : ℝ | min (max k 1) (Module.finrank ℂ (sector T nn)) ≤ countLE T H nn E} := by
  classical
  have hcount : ∀ E, countLE T H nn E =
      ((Finset.Icc 1 (Module.finrank ℂ (sector T nn))).filter fun j => secEig T H nn j ≤ E).card := by
    intro E
    have h := card_secEig_mem hH hHs nn (Set.Iic E)
    simp only [Set.mem_Iic] at h
    rw [h, Matrix.rank_eq_finrank_range_toLin _ (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis
      (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis]
    have hsp := specProj_sector T hH hHs nn (Set.Iic E) measurableSet_Iic
    have h2 : Matrix.toLin (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis
        (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis (cfc ((Set.Iic E).indicator (1 : ℝ → ℝ)) H * Psec T nn) =
        ((toCLM T (cfc ((Set.Iic E).indicator (1 : ℝ → ℝ)) H * Psec T nn)) : FockSpace T →ₗ[ℂ] FockSpace T) := rfl
    rw [h2, hsp, Submodule.range_starProjection]
    rfl
  by_cases hd : Module.finrank ℂ (sector T nn) = 0
  · rw [secEig_of_finrank_eq_zero_dev hd]
    have hs : {E : ℝ | min (max k 1) (Module.finrank ℂ (sector T nn)) ≤ countLE T H nn E} = Set.univ := by
      ext E
      simp [hd]
    rw [hs, Real.sInf_univ]
  · have hm1 : 1 ≤ min (max k 1) (Module.finrank ℂ (sector T nn)) := by omega
    have hmd : min (max k 1) (Module.finrank ℂ (sector T nn)) ≤ Module.finrank ℂ (sector T nn) := min_le_right _ _
    rw [secEig_congr_dev (b := min (max k 1) (Module.finrank ℂ (sector T nn))) (by omega)]
    symm
    apply IsLeast.csInf_eq
    constructor
    · show min (max k 1) (Module.finrank ℂ (sector T nn)) ≤
        countLE T H nn (secEig T H nn (min (max k 1) (Module.finrank ℂ (sector T nn))))
      rw [hcount]
      calc min (max k 1) (Module.finrank ℂ (sector T nn))
          = (Finset.Icc 1 (min (max k 1) (Module.finrank ℂ (sector T nn)))).card := by simp
        _ ≤ _ := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_Icc] at hj
          simp only [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hj.1, le_trans hj.2 hmd⟩, secEig_mono T H nn hj.2⟩
    · intro E hE
      by_contra hlt
      push_neg at hlt
      rw [Set.mem_setOf_eq, hcount] at hE
      have hsub : ((Finset.Icc 1 (Module.finrank ℂ (sector T nn))).filter fun j => secEig T H nn j ≤ E) ⊆
          Finset.Icc 1 (min (max k 1) (Module.finrank ℂ (sector T nn)) - 1) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        simp only [Finset.mem_Icc]
        refine ⟨hj.1.1, ?_⟩
        by_contra hj2
        push_neg at hj2
        have := secEig_mono T H nn (show min (max k 1) (Module.finrank ℂ (sector T nn)) ≤ j by omega)
        linarith [hj.2]
      have := Finset.card_le_card hsub
      simp only [Nat.card_Icc] at this
      omega

/-! ### Proof devices for the dimension of a sector (phase (b), round one; not statements of the paper) -/

section SectorDevices

theorem card_boolFun_dev (α : Type*) [Fintype α] [DecidableEq α] (a : ℕ) :
    Fintype.card {u : α → Bool // (Finset.univ.filter fun j => u j = true).card = a} =
      (Fintype.card α).choose a := by
  rw [← Fintype.card_finset_len]
  refine Fintype.card_congr
    { toFun := fun u => ⟨Finset.univ.filter fun j => u.1 j = true, u.2⟩
      invFun := fun s => ⟨fun j => decide (j ∈ s.1), by simpa using s.2⟩
      left_inv := fun u => ?_
      right_inv := fun s => ?_ }
  · apply Subtype.ext
    funext j
    simp
  · apply Subtype.ext
    ext j
    simp

theorem card_conf_sector_dev (T : Torus) (a b : ℕ) :
    Fintype.card {m : Conf (ZMod T.Nφ) // ctσ T .up m = a ∧ ctσ T .dn m = b} =
      T.Nφ.choose a * T.Nφ.choose b := by
  have e : {m : Conf (ZMod T.Nφ) // ctσ T .up m = a ∧ ctσ T .dn m = b} ≃
      {u : ZMod T.Nφ → Bool // (Finset.univ.filter fun j => u j = true).card = a} ×
        {d : ZMod T.Nφ → Bool // (Finset.univ.filter fun j => d j = true).card = b} :=
    { toFun := fun m => (⟨fun j => m.1 (j, .up), m.2.1⟩, ⟨fun j => m.1 (j, .dn), m.2.2⟩)
      invFun := fun p => ⟨fun μ => match μ.2 with
          | .up => p.1.1 μ.1
          | .dn => p.2.1 μ.1, p.1.2, p.2.2⟩
      left_inv := fun m => by
        apply Subtype.ext
        funext μ
        rcases μ with ⟨j, σ⟩
        cases σ <;> rfl
      right_inv := fun p => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, card_boolFun_dev, card_boolFun_dev, ZMod.card]

end SectorDevices

/-- The dimension of the sector `𝓗^{(n_↑, n_↓)}`: `binom(N_φ, n_↑) · binom(N_φ, n_↓)`. -/
theorem finrank_sector (T : Torus) (nn : SectorLabel T) :
    Module.finrank ℂ (sector T nn) = T.Nφ.choose nn.1 * T.Nφ.choose nn.2 := by
  classical
  have h1 : (Psec T nn).rank = Module.finrank ℂ (sector T nn) := by
    rw [Matrix.rank_eq_finrank_range_toLin _ (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis
      (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis]
    have h2 : Matrix.toLin (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis
        (EuclideanSpace.basisFun (Conf (ZMod T.Nφ)) ℂ).toBasis (Psec T nn) =
        ((toCLM T (Psec T nn)) : FockSpace T →ₗ[ℂ] FockSpace T) := rfl
    rw [h2, toCLM_Psec_dev, Submodule.range_starProjection]
  rw [← h1, Psec_eq_diag, Matrix.rank_diagonal,
    Fintype.card_congr (Equiv.subtypeEquivRight fun m => show secInd T nn m ≠ 0 ↔
      (ctσ T .up m = nn.1 ∧ ctσ T .dn m = nn.2) by simp [secInd, secOf_eq_iff])]
  exact card_conf_sector_dev T nn.1 nn.2

/-- For the hollow-core Hamiltonian, `E_k ≥ 0` (`H_N ≥ 0`, block C's `HN_posSemidef`). -/
theorem secEig_HN_nonneg (T : Torus) (nn : SectorLabel T) (k : ℕ) : 0 ≤ secEig T (HN T) nn k := by
  by_cases hd : Module.finrank ℂ (sector T nn) = 0
  · rw [secEig_of_finrank_eq_zero_dev hd]
  have hH := HN_isSelfAdjoint T
  have hHs := HN_isSectorPreserving T
  rw [secEig_congr_dev (b := min (max k 1) (Module.finrank ℂ (sector T nn))) (by omega)]
  obtain ⟨v, -, hv0, hHv⟩ := secEig_hasEigenvector hH hHs nn
    (k := min (max k 1) (Module.finrank ℂ (sector T nn))) (by omega) (min_le_right _ _)
  set μ := secEig T (HN T) nn (min (max k 1) (Module.finrank ℂ (sector T nn)))
  have hP : 0 ≤ (star (WithLp.ofLp v) ⬝ᵥ (HN T *ᵥ WithLp.ofLp v)).re := by
    open scoped ComplexOrder in
      simpa using (Complex.le_def.mp
        ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (HN_posSemidef T)).2 (WithLp.ofLp v))).1
  have e : star (WithLp.ofLp v) ⬝ᵥ (HN T *ᵥ WithLp.ofLp v) = ⟪v, toCLM T (HN T) v⟫_ℂ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM, dotProduct_comm]
  rw [e, hHv, inner_smul_right, Complex.re_ofReal_mul] at hP
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hvv : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  have h2 : (0 : ℝ) ≤ μ * ‖v‖ ^ 2 := by
    rw [hvv] at hP
    exact hP
  by_contra hneg
  push_neg at hneg
  nlinarith [mul_neg_of_neg_of_pos hneg (pow_pos hv 2)]

/-! ### Assumption 6.3, and its bridge to the core's gap form -/

/-- Assumption 6.3's gap forces `1 ≤ p < dim 𝓗^𝐧` ("`E_{p+1}`" exists): for any `H`, `γ > 0` and
`E_{p+1} − E_p ≥ γ` (the clamped indices make `E_{p+1} − E_p` zero at `p = 0` and at `p ≥ dim 𝓗^𝐧`; the implicit `Δ`
is not used, and a caller names it). -/
theorem one_le_p_lt_finrank {T : Torus} {H : FockOp T} {nn : SectorLabel T} {p : ℕ} {Δ γ : ℝ} (hγ : 0 < γ)
    (hgap : γ ≤ secEig T H nn (p + 1) - secEig T H nn p) :
    1 ≤ p ∧ p < Module.finrank ℂ (sector T nn) := by
  constructor
  · by_contra hp
    have hp0 : p = 0 := by omega
    subst hp0
    have : secEig T H nn (0 + 1) = secEig T H nn 0 := secEig_congr_dev (by omega)
    linarith
  · by_contra hp
    have : secEig T H nn (p + 1) = secEig T H nn p := secEig_congr_dev (by omega)
    linarith

/-- **The bridge to the core's `gap` field**: under `E_{p+1} − E_p ≥ γ`, every eigenvalue of `H` on a nonzero vector of
the sector lies in `[E_1, E_p]` or is at least `E_p + γ` (with `a = E_1`, `b = E_p`). -/
theorem gap_of_secEig {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H)
    {nn : SectorLabel T} {p : ℕ} {γ : ℝ} (hγ : 0 < γ) (hgap : γ ≤ secEig T H nn (p + 1) - secEig T H nn p)
    (μ : ℝ) (v : FockSpace T) (hv0 : v ≠ 0) (hv : toCLM T (Psec T nn) v = v)
    (hHv : toCLM T H v = (μ : ℂ) • v) :
    μ ∈ Set.Icc (secEig T H nn 1) (secEig T H nn p) ∨ secEig T H nn p + γ ≤ μ := by
  have hvS : v ∈ sector T nn := (mem_sector_iff_Psec_dev nn v).mpr hv
  obtain ⟨k, hk1, hkd, hk⟩ := exists_secEig_eq hH hHs hvS hv0 hHv
  rw [← hk]
  by_cases hkp : k ≤ p
  · exact Or.inl ⟨secEig_mono T H nn hk1, secEig_mono T H nn hkp⟩
  · right
    have := secEig_mono T H nn (show p + 1 ≤ k by omega)
    linarith

/-- The spectral projections of block A (`cfc` of an indicator) are the core's (`IndexCore.specProj`, the sum of the
eigenprojections of an orthonormal eigenbasis) under `toCLM`. -/
theorem toCLM_cfc_indicator {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hH' : IsSelfAdjoint (toCLM T H))
    (B : Set ℝ) :
    toCLM T (cfc (B.indicator (1 : ℝ → ℝ)) H) = IndexCore.specProj (toCLM T H) hH' B := by
  classical
  apply ContinuousLinearMap.coe_injective
  refine (IndexCore.eigBasis (toCLM T H) hH').toBasis.ext fun j => ?_
  simp only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis]
  rw [toCLM_cfc_eigen_dev hH _ (IndexCore.apply_eigBasis (toCLM T H) hH' j), IndexCore.specProj_def,
    ContinuousLinearMap.sum_apply]
  simp only [IndexCore.eigProj_apply_eigBasis]
  rw [Finset.sum_ite_eq]
  by_cases hB : IndexCore.eigVal (toCLM T H) hH' j ∈ B
  · rw [if_pos (Finset.mem_filter.mpr ⟨IndexCore.eigVal_mem_spec _ _ j, hB⟩), Set.indicator_of_mem hB]
    simp
  · rw [if_neg (fun h => hB (Finset.mem_filter.mp h).2), Set.indicator_of_notMem hB]
    simp

/-! ### Proof devices: block D's spectral sums are the core's (phase (b), round one; not statements of the paper)

The proofs of `Assembly.Inputs`' bridges `specFinset_eq_spec`, `toCLM_specProj`, `toCLM_spectralSum`, placed here so that
Lemma 6.7 below can use them. -/

section BridgeDevices

theorem toCLM_smul_dev {T : Torus} (c : ℂ) (A : FockOp T) : toCLM T (c • A) = c • toCLM T A :=
  map_smul (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) c A

theorem toCLM_zero_dev (T : Torus) : toCLM T (0 : FockOp T) = 0 :=
  map_zero (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ))

theorem toCLM_one_dev (T : Torus) : toCLM T (1 : FockOp T) = 1 :=
  map_one (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ))

theorem toCLM_add_dev {T : Torus} (A B : FockOp T) : toCLM T (A + B) = toCLM T A + toCLM T B :=
  map_add (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) A B

theorem toCLM_neg_dev {T : Torus} (A : FockOp T) : toCLM T (-A) = -toCLM T A :=
  map_neg (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) A

theorem toCLM_star_dev {T : Torus} (A : FockOp T) : toCLM T (star A) = star (toCLM T A) :=
  map_star (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)) A

theorem toCLM_injective_dev (T : Torus) : Function.Injective (toCLM T) :=
  (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)).injective

theorem toCLM_exp_dev {T : Torus} (A : FockOp T) : toCLM T (NormedSpace.exp A) = NormedSpace.exp (toCLM T A) :=
  opCLM_exp A

theorem commute_toCLM_dev {T : Torus} {A B : FockOp T} (h : Commute A B) : Commute (toCLM T A) (toCLM T B) :=
  h.map (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ))

theorem commute_of_toCLM_dev {T : Torus} {A B : FockOp T} (h : Commute (toCLM T A) (toCLM T B)) : Commute A B := by
  apply toCLM_injective_dev T
  rw [toCLM_mul', toCLM_mul']
  exact h.eq

theorem isSelfAdjoint_toCLM_dev {T : Torus} {A : FockOp T} (h : IsSelfAdjoint A) : IsSelfAdjoint (toCLM T A) :=
  h.map (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ))

/-- An eigenvalue of `H` on a nonzero vector lies in the real spectrum of the matrix `H`. -/
theorem mem_spectrum_of_eigen_dev {T : Torus} {H : FockOp T} {μ : ℝ} {w : FockSpace T} (hw0 : w ≠ 0)
    (hw : toCLM T H w = (μ : ℂ) • w) : μ ∈ spectrum ℝ H := by
  rw [spectrum.mem_iff]
  intro hu
  apply hw0
  obtain ⟨M, hM⟩ := hu.exists_left_inv
  have h0 : toCLM T (algebraMap ℝ (FockOp T) μ - H) w = 0 := by
    show Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ) (algebraMap ℝ (FockOp T) μ - H) w = 0
    rw [map_sub, ContinuousLinearMap.sub_apply, hw, Algebra.algebraMap_eq_smul_one (A := FockOp T) μ,
      ← Complex.coe_smul, map_smul, map_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      sub_self]
  calc w = toCLM T (M * (algebraMap ℝ (FockOp T) μ - H)) w := by rw [hM, toCLM_one_dev]; rfl
    _ = 0 := by rw [toCLM_mul', ContinuousLinearMap.mul_apply, h0, map_zero]

theorem specFinset_eq_spec_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hH' : IsSelfAdjoint (toCLM T H)) :
    specFinset H = IndexCore.spec (toCLM T H) hH' := by
  classical
  ext μ
  rw [mem_specFinset, IndexCore.mem_spec_iff]
  constructor
  · intro hμ
    by_contra hne
    push_neg at hne
    have h0 : toCLM T (cfc (({μ} : Set ℝ).indicator (1 : ℝ → ℝ)) H) = 0 := by
      rw [toCLM_cfc_indicator hH hH' {μ}, IndexCore.specProj_def]
      refine Finset.sum_eq_zero fun ν hν => ?_
      simp only [Finset.mem_filter, Set.mem_singleton_iff] at hν
      obtain ⟨hν1, rfl⟩ := hν
      obtain ⟨i, hi⟩ := (IndexCore.mem_spec_iff _ _ _).mp hν1
      exact absurd hi (hne i)
    have h0' : cfc (({μ} : Set ℝ).indicator (1 : ℝ → ℝ)) H = 0 :=
      toCLM_injective_dev T (h0.trans (toCLM_zero_dev T).symm)
    have hsp := cfc_map_spectrum (({μ} : Set ℝ).indicator (1 : ℝ → ℝ)) H hH
      ((Matrix.finite_real_spectrum (A := H)).continuousOn _)
    rw [h0'] at hsp
    have h1 : (1 : ℝ) ∈ spectrum ℝ (0 : FockOp T) := by
      rw [hsp]
      exact ⟨μ, hμ, by simp⟩
    rw [spectrum.zero_eq] at h1
    simp at h1
  · rintro ⟨i, rfl⟩
    have hw := IndexCore.apply_eigBasis (toCLM T H) hH' i
    exact mem_spectrum_of_eigen_dev ((IndexCore.eigBasis (toCLM T H) hH').orthonormal.ne_zero i) hw

theorem toCLM_specProj_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hH' : IsSelfAdjoint (toCLM T H))
    (E : ℝ) : toCLM T (Locality.specProj H E) = IndexCore.eigProj (toCLM T H) hH' E := by
  classical
  rw [show Locality.specProj H E = cfc (({E} : Set ℝ).indicator (1 : ℝ → ℝ)) H from rfl,
    toCLM_cfc_indicator hH hH' {E}, IndexCore.specProj_def]
  by_cases hE : E ∈ IndexCore.spec (toCLM T H) hH'
  · refine Finset.sum_eq_single_of_mem E ?_ ?_
    · simp only [Finset.mem_filter, Set.mem_singleton_iff]
      exact ⟨hE, trivial⟩
    intro x hx hxE
    simp only [Finset.mem_filter, Set.mem_singleton_iff] at hx
    exact absurd hx.2 hxE
  · rw [IndexCore.eigProj_eq_zero_of_not_mem _ _ hE]
    refine Finset.sum_eq_zero fun x hx => ?_
    simp only [Finset.mem_filter, Set.mem_singleton_iff] at hx
    obtain ⟨hx1, rfl⟩ := hx
    exact absurd hx1 hE

theorem toCLM_spectralSum_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (hH' : IsSelfAdjoint (toCLM T H))
    (f : ℝ → ℝ → ℂ) (A : FockOp T) :
    toCLM T (∑ E ∈ specFinset H, ∑ E' ∈ specFinset H, f E E' • (Locality.specProj H E * A * Locality.specProj H E')) =
      IndexCore.spectralSum (toCLM T H) hH' f (toCLM T A) := by
  rw [IndexCore.spectralSum_def, ← specFinset_eq_spec_dev hH hH', toCLM_sum']
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [toCLM_sum']
  refine Finset.sum_congr rfl fun E' _ => ?_
  rw [toCLM_smul_dev, toCLM_mul', toCLM_mul', toCLM_specProj_dev hH hH' E, toCLM_specProj_dev hH hH' E']

end BridgeDevices

/-! ### Proof devices for `P` and the sector preservation of `H_N` (phase (b), round one; not statements of the paper) -/

section PDevices

theorem opIntegral_commute_dev {S : Type*} [Fintype S] [DecidableEq S] {D : Set (ℝ × ℝ)} {h : ℝ × ℝ → Op S}
    (X : Op S) (hint : ∀ m m' : Conf S, MeasureTheory.IntegrableOn (fun R => h R m m') D)
    (hc : ∀ R, Commute X (h R)) : Commute X (opIntegral D h) := by
  show X * opIntegral D h = opIntegral D h * X
  have h1 := opIntegral_map (LinearMap.mulLeft ℂ X) D h hint
  have h2 := opIntegral_map (LinearMap.mulRight ℂ X) D h hint
  simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply] at h1 h2
  rw [h1, h2]
  congr 1
  funext R
  exact (hc R).eq

theorem H_isSectorPreserving_dev (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx) :
    IsSectorPreserving (S.T N) (S.H N) := by
  rw [S.d.eq_opIntegral N hN]
  exact ⟨(opIntegral_commute_dev _ (integrableOn_h S.d hN)
      fun R => (S.d.h_isSectorPreserving N hN R).1.symm).symm,
    (opIntegral_commute_dev _ (integrableOn_h S.d hN) fun R => (S.d.h_isSectorPreserving N hN R).2.symm).symm⟩

theorem isStarProjection_of_toCLM_dev {T : Torus} {A : FockOp T} (h : IsStarProjection (toCLM T A)) :
    IsStarProjection A := by
  have e : (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)).symm (toCLM T A) = A :=
    (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)).symm_apply_apply A
  refine ⟨?_, ?_⟩
  · have := h.isIdempotentElem.map (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)).symm
    rwa [e] at this
  · have := h.isSelfAdjoint.map (Matrix.toEuclideanCLM (n := Conf (ZMod T.Nφ)) (𝕜 := ℂ)).symm
    rwa [e] at this

theorem isStarProjection_Psec_dev (T : Torus) (nn : SectorLabel T) : IsStarProjection (Psec T nn) := by
  apply isStarProjection_of_toCLM_dev
  rw [toCLM_Psec_dev]
  exact isStarProjection_starProjection

theorem isStarProjection_cfc_indicator_dev {T : Torus} {H : FockOp T} (hH : IsSelfAdjoint H) (B : Set ℝ) :
    IsStarProjection (cfc (B.indicator (1 : ℝ → ℝ)) H) := by
  apply isStarProjection_of_toCLM_dev
  rw [toCLM_cfc_indicator hH (hH.map _) B]
  exact IndexCore.isStarProjection_specProj _ _ _

theorem isStarProjection_mul_dev {R : Type*} [Ring R] [StarRing R] {A B : R} (hA : IsStarProjection A)
    (hB : IsStarProjection B) (hc : Commute A B) : IsStarProjection (A * B) := by
  refine ⟨?_, ?_⟩
  · show A * B * (A * B) = A * B
    calc A * B * (A * B) = A * (B * A) * B := by noncomm_ring
      _ = A * (A * B) * B := by rw [hc.eq]
      _ = (A * A) * (B * B) := by noncomm_ring
      _ = A * B := by rw [hA.isIdempotentElem.eq, hB.isIdempotentElem.eq]
  · show star (A * B) = A * B
    rw [star_mul, hA.isSelfAdjoint.star_eq, hB.isSelfAdjoint.star_eq, hc.eq]

end PDevices

/-- **Assumption 6.3**: "`it has rank $p$`" — the rank of `P_N` is `p`, for every `N ∈ 𝒩`, under (H1). -/
theorem ArgData.rank_P (D : ArgData η δ₀) (hA : GapAssumption D.toIxSetting D.nn D.p D.Δ D.γ) :
    ∀ N ∈ D.Ts.idx, (D.P N).rank = D.p := by
  classical
  intro N hN
  have hH := D.d.H_isSelfAdjoint N hN
  have hHs := H_isSectorPreserving_dev D.toIxSetting hN
  have hγ : 0 < D.γ := by linarith [hA.Δ_nonneg, hA.two_mul_Δ_lt]
  have hg := hA.gap N hN
  obtain ⟨hp1, hpd⟩ := one_le_p_lt_finrank (Δ := 0) hγ hg
  unfold ArgData.P
  rw [← card_secEig_mem hH hHs (D.nn N)]
  have hfil : ((Finset.Icc 1 (Module.finrank ℂ (sector (D.T N) (D.nn N)))).filter fun k =>
      secEig (D.T N) (D.H N) (D.nn N) k ∈ Set.Icc (D.E N 1) (D.E N D.p)) = Finset.Icc 1 D.p := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hkd⟩, -, hkp⟩
      refine ⟨hk1, ?_⟩
      by_contra hk
      push_neg at hk
      have := secEig_mono (D.T N) (D.H N) (D.nn N) (show D.p + 1 ≤ k by omega)
      simp only [ArgData.E] at hkp hg
      linarith
    · rintro ⟨hk1, hkp⟩
      exact ⟨⟨hk1, by omega⟩, secEig_mono _ _ _ hk1, secEig_mono _ _ _ hkp⟩
  have hc := congrArg Finset.card hfil
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hc
  convert hc using 3

/-- **Assumption 6.3**: "`and $P=P\Psec{\nn_N}=\Psec{\nn_N}P$`" (with `P` a self-adjoint idempotent). -/
theorem ArgData.P_props (D : ArgData η δ₀) (hA : GapAssumption D.toIxSetting D.nn D.p D.Δ D.γ) :
    ∀ N ∈ D.Ts.idx, IsStarProjection (D.P N) ∧ D.P N * Psec (D.T N) (D.nn N) = D.P N ∧
      Psec (D.T N) (D.nn N) * D.P N = D.P N := by
  intro N hN
  have hH := D.d.H_isSelfAdjoint N hN
  have hHs := H_isSectorPreserving_dev D.toIxSetting hN
  have hA' := isStarProjection_cfc_indicator_dev hH (Set.Icc (D.E N 1) (D.E N D.p))
  have hQ := isStarProjection_Psec_dev (D.T N) (D.nn N)
  have hc : Commute (cfc ((Set.Icc (D.E N 1) (D.E N D.p)).indicator (1 : ℝ → ℝ)) (D.H N)) (Psec (D.T N) (D.nn N)) :=
    (isSectorPreserving_iff_commute _ _).mp (IsSectorPreserving.cfc _ hH hHs _) (D.nn N)
  unfold ArgData.P
  refine ⟨isStarProjection_mul_dev hA' hQ hc, ?_, ?_⟩
  · rw [mul_assoc, hQ.isIdempotentElem.eq]
  · rw [← mul_assoc, ← hc.eq, mul_assoc, hQ.isIdempotentElem.eq]

/-- Under (H1), `H_N` is sector-preserving (its local terms are, Definition 4.6). -/
theorem IxSetting.H_isSectorPreserving (S : IxSetting η δ₀) :
    ∀ N ∈ S.Ts.idx, IsSectorPreserving (S.T N) (S.H N) :=
  fun N hN => H_isSectorPreserving_dev S hN

/-! ### Proof devices for Lemma 6.2 (phase (b), round one; not statements of the paper)

`d(s, s') ≥ |x_s − x_{s'}|_{L_x}` (block B's `pdist_le_slotDist`); a slot of `Col(j)` lies within `δ_x` of `κj`, so
`d(s, s') ≥ |κj' − κj|_{L_x} − 2δ_x` for `s ∈ Col(j)`, `s' ∈ Col(j')`; on the circle `|v|_{L} ≥ min(v, L − v)` for
`0 ≤ v ≤ L`; `κN = L_x/2`; and the representatives of the quarters' orbitals. -/

section SepDevices

theorem slotSetDist_ge_dev {T : Torus} {X Y : Finset (Slot δ₀ T)} {c : ℝ}
    (h : ∀ s ∈ X, ∀ s' ∈ Y, c ≤ slotDist δ₀ T s s') : ENNReal.ofReal c ≤ slotSetDist X Y := by
  unfold slotSetDist
  apply Finset.le_inf
  rintro ⟨s, s'⟩ hp
  rw [Finset.mem_product] at hp
  exact ENNReal.ofReal_le_ofReal (h s hp.1 s' hp.2)

theorem col_sep_dev {T : Torus} {j j' : ℤ} {s s' : Slot δ₀ T} (hs : s ∈ col δ₀ T j) (hs' : s' ∈ col δ₀ T j') :
    pdist T.Lx (T.κ * j' - T.κ * j) - 2 * δx δ₀ T ≤ slotDist δ₀ T s s' := by
  rw [mem_col] at hs hs'
  have h1 := pdist_le_slotDist s s'
  have h2 : pdist T.Lx (T.κ * j' - T.κ * j) ≤ pdist T.Lx (T.κ * j' - xs δ₀ T s') +
      pdist T.Lx (xs δ₀ T s' - xs δ₀ T s) + pdist T.Lx (xs δ₀ T s - T.κ * j) := by
    have e : T.κ * j' - T.κ * j =
        (T.κ * j' - xs δ₀ T s') + (xs δ₀ T s' - xs δ₀ T s) + (xs δ₀ T s - T.κ * j) := by ring
    rw [e]
    exact (pdist_add_le _ _ _).trans (add_le_add_left (pdist_add_le _ _ _) _)
  have h3 : pdist T.Lx (T.κ * j' - xs δ₀ T s') = pdist T.Lx (xs δ₀ T s' - T.κ * j') := by
    rw [← pdist_neg, neg_sub]
  have h4 : pdist T.Lx (xs δ₀ T s' - xs δ₀ T s) = pdist T.Lx (xs δ₀ T s - xs δ₀ T s') := by
    rw [← pdist_neg, neg_sub]
  linarith

theorem le_pdist_dev {P v : ℝ} (hP : 0 < P) (hv0 : 0 ≤ v) (hvP : v ≤ P) : min v (P - v) ≤ pdist P v := by
  by_contra h
  push_neg at h
  obtain ⟨m, hm⟩ := (pdist_lt_iff P v _).mp h
  obtain ⟨hm1, hm2⟩ := abs_lt.mp hm
  have hmin1 := min_le_left v (P - v)
  have hmin2 := min_le_right v (P - v)
  rcases le_or_gt 0 m with hm0 | hm0
  · have : 0 ≤ (m : ℝ) * P := mul_nonneg (by exact_mod_cast hm0) hP.le
    linarith
  · have hm1' : (m : ℝ) ≤ -1 := by
      have : m ≤ -1 := by omega
      exact_mod_cast this
    have : (m : ℝ) * P ≤ -1 * P := mul_le_mul_of_nonneg_right hm1' hP.le
    linarith

theorem pdist_ge_dev {P v c : ℝ} (hP : 0 < P) (hv0 : 0 ≤ v) (hvP : v ≤ P) (hc1 : c ≤ v) (hc2 : c ≤ P - v) :
    c ≤ pdist P v :=
  (le_min hc1 hc2).trans (le_pdist_dev hP hv0 hvP)

theorem val_mem_of_mem_image_dev {n : ℕ} [NeZero n] {S : Finset ℕ} (hS : ∀ k ∈ S, k < n) {j : ZMod n}
    (hj : j ∈ S.image (fun k : ℕ => (k : ZMod n))) : j.val ∈ S := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hS k hk)]
  exact hk

theorem Lx_eq_two_κN_dev (T : Torus) : T.Lx = 2 * (T.κ * T.N) := by
  rw [T.Lx_eq]
  unfold Torus.Nφ
  push_cast
  ring

/-- A slot of `Col(B)` lies in `Col(k)` for the representative `k = j.val` of an orbital `j ∈ B`. -/
theorem mem_colBand_dev {T : Torus} {B : Finset (ZMod T.Nφ)} {s : Slot δ₀ T} (hs : s ∈ colBand δ₀ T B) :
    ∃ j ∈ B, s ∈ col δ₀ T (j.val : ℤ) := by
  unfold colBand at hs
  exact Finset.mem_biUnion.mp hs

theorem quarterMinus_val_dev {T : Torus} {j : ZMod T.Nφ} (hj : j ∈ quarterMinus T.Nφ T.N) :
    4 * j.val + 4 ≤ T.N := by
  have h := val_mem_of_mem_image_dev (S := Finset.range (T.N / 4))
    (fun k hk => by rw [Finset.mem_range] at hk; unfold Torus.Nφ; omega) hj
  rw [Finset.mem_range] at h
  omega

theorem quarterPlus_val_dev {T : Torus} {j : ZMod T.Nφ} (hj : j ∈ quarterPlus T.Nφ T.N) :
    (3 * T.N : ℝ) / 4 ≤ j.val ∧ j.val + 1 ≤ T.N := by
  have h := val_mem_of_mem_image_dev (S := Finset.Ico ⌈(3 * T.N : ℝ) / 4⌉₊ T.N)
    (fun k hk => by rw [Finset.mem_Ico] at hk; unfold Torus.Nφ; omega) hj
  rw [Finset.mem_Ico] at h
  exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast h.1), h.2⟩

theorem quarterMid_val_dev {T : Torus} {j : ZMod T.Nφ} (hj : j ∈ quarterMid T.Nφ T.N) :
    T.N ≤ 4 * j.val + 3 ∧ (j.val : ℝ) < (3 * T.N : ℝ) / 4 := by
  unfold quarterMid at hj
  rw [Finset.mem_sdiff, Finset.mem_union] at hj
  obtain ⟨hΓ, hnot⟩ := hj
  push_neg at hnot
  have hk := val_mem_of_mem_image_dev (S := Finset.range T.N)
    (fun k hk => by rw [Finset.mem_range] at hk; unfold Torus.Nφ; omega) hΓ
  rw [Finset.mem_range] at hk
  have hjk : ((j.val : ℕ) : ZMod T.Nφ) = j := ZMod.natCast_zmod_val j
  constructor
  · by_contra h1
    apply hnot.1
    rw [← hjk]
    exact Finset.mem_image.mpr ⟨j.val, Finset.mem_range.mpr (by omega), rfl⟩
  · by_contra h2
    push_neg at h2
    apply hnot.2
    rw [← hjk]
    refine Finset.mem_image.mpr ⟨j.val, Finset.mem_Ico.mpr ⟨?_, hk⟩, rfl⟩
    exact Nat.ceil_le.mpr h2

end SepDevices

/-! ### Lemma 6.2 (separations), on every admissible torus -/

/-- **Lemma 6.2**: "`d(\cutm,\cutp)\ge\tfrac12L_x-2\delta_x`". -/
theorem sep_cuts (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) :
    ENNReal.ofReal (T.Lx / 2 - 2 * δx δ₀ T) ≤ slotSetDist (col δ₀ T 0) (col δ₀ T T.N) := by
  apply slotSetDist_ge_dev
  intro s hs s' hs'
  have h := col_sep_dev hs hs'
  simp only [Int.cast_zero, mul_zero, sub_zero, Int.cast_natCast] at h
  have hL := Lx_eq_two_κN_dev T
  have hκ := T.κ_pos
  have hp : T.Lx / 2 ≤ pdist T.Lx (T.κ * (T.N : ℝ)) :=
    pdist_ge_dev T.Lx_pos (by positivity) (by linarith [mul_nonneg hκ.le (Nat.cast_nonneg (α := ℝ) T.N)])
      (by linarith) (by linarith)
  linarith

/-- **Lemma 6.2**: "`d(\Col\Gm,\Col\Gp)\ge\tfrac14L_x-2\delta_x`". -/
theorem sep_quarters (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) :
    ENNReal.ofReal (T.Lx / 4 - 2 * δx δ₀ T) ≤
      slotSetDist (colBand δ₀ T (quarterMinus T.Nφ T.N)) (colBand δ₀ T (quarterPlus T.Nφ T.N)) := by
  apply slotSetDist_ge_dev
  intro s hs s' hs'
  obtain ⟨j, hj, hsj⟩ := mem_colBand_dev hs
  obtain ⟨j', hj', hsj'⟩ := mem_colBand_dev hs'
  have h := col_sep_dev hsj hsj'
  have hL := Lx_eq_two_κN_dev T
  have hκ := T.κ_pos
  have h1 := quarterMinus_val_dev hj
  obtain ⟨h2, h3⟩ := quarterPlus_val_dev hj'
  have h1' : 4 * (j.val : ℝ) + 4 ≤ T.N := by exact_mod_cast h1
  have h3' : (j'.val : ℝ) + 1 ≤ T.N := by exact_mod_cast h3
  have hp : T.Lx / 4 ≤ pdist T.Lx (T.κ * ((j'.val : ℕ) : ℤ) - T.κ * ((j.val : ℕ) : ℤ)) := by
    push_cast
    rw [show T.κ * (j'.val : ℝ) - T.κ * (j.val : ℝ) = T.κ * ((j'.val : ℝ) - j.val) by ring]
    have hd1 : (T.N : ℝ) / 2 + 1 ≤ (j'.val : ℝ) - j.val := by linarith
    have hd2 : (j'.val : ℝ) - j.val ≤ T.N := by linarith [Nat.cast_nonneg (α := ℝ) j.val]
    have hd0 : 0 ≤ (j'.val : ℝ) - j.val := by linarith [Nat.cast_nonneg (α := ℝ) T.N]
    refine pdist_ge_dev T.Lx_pos (mul_nonneg hκ.le hd0) ?_ ?_ ?_
    · rw [hL]; nlinarith
    · rw [hL]; nlinarith
    · rw [hL]; nlinarith
  linarith

/-- **Lemma 6.2**: "`d(\partial_\pm,\Col\Gmid)\ge\tfrac18L_x-\kappa-2\delta_x`". -/
theorem sep_cut_mid (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) :
    ENNReal.ofReal (T.Lx / 8 - T.κ - 2 * δx δ₀ T) ≤ slotSetDist (col δ₀ T 0) (colBand δ₀ T (quarterMid T.Nφ T.N)) ∧
      ENNReal.ofReal (T.Lx / 8 - T.κ - 2 * δx δ₀ T) ≤
        slotSetDist (col δ₀ T T.N) (colBand δ₀ T (quarterMid T.Nφ T.N)) := by
  have hL := Lx_eq_two_κN_dev T
  have hκ := T.κ_pos
  constructor
  · apply slotSetDist_ge_dev
    intro s hs s' hs'
    obtain ⟨j', hj', hsj'⟩ := mem_colBand_dev hs'
    have h := col_sep_dev hs hsj'
    simp only [Int.cast_zero, mul_zero, sub_zero, Int.cast_natCast] at h
    obtain ⟨h1, h2⟩ := quarterMid_val_dev hj'
    have h1' : (T.N : ℝ) ≤ 4 * (j'.val : ℝ) + 3 := by exact_mod_cast h1
    have hp : T.Lx / 8 - T.κ ≤ pdist T.Lx (T.κ * (j'.val : ℝ)) := by
      refine pdist_ge_dev T.Lx_pos (mul_nonneg hκ.le (Nat.cast_nonneg _)) ?_ ?_ ?_
      · rw [hL]; nlinarith
      · rw [hL]; nlinarith
      · rw [hL]; nlinarith
    linarith
  · apply slotSetDist_ge_dev
    intro s hs s' hs'
    obtain ⟨j', hj', hsj'⟩ := mem_colBand_dev hs'
    have h := col_sep_dev hs hsj'
    obtain ⟨h1, h2⟩ := quarterMid_val_dev hj'
    have h1' : (T.N : ℝ) ≤ 4 * (j'.val : ℝ) + 3 := by exact_mod_cast h1
    have hp : T.Lx / 8 - T.κ ≤ pdist T.Lx (T.κ * ((j'.val : ℕ) : ℤ) - T.κ * ((T.N : ℤ) : ℝ)) := by
      push_cast
      rw [← pdist_neg, show -(T.κ * (j'.val : ℝ) - T.κ * (T.N : ℝ)) = T.κ * ((T.N : ℝ) - j'.val) by ring]
      have hd0 : 0 ≤ (T.N : ℝ) - j'.val := by linarith
      refine pdist_ge_dev T.Lx_pos (mul_nonneg hκ.le hd0) ?_ ?_ ?_
      · rw [hL]; nlinarith [Nat.cast_nonneg (α := ℝ) j'.val]
      · rw [hL]; nlinarith
      · rw [hL]; nlinarith
    linarith

/-- **Lemma 6.2**: "`d(\partial_\mp,\Col\Gamma_\pm)\ge\tfrac38L_x-2\delta_x`". -/
theorem sep_cut_opposite (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) :
    ENNReal.ofReal (3 * T.Lx / 8 - 2 * δx δ₀ T) ≤
        slotSetDist (col δ₀ T 0) (colBand δ₀ T (quarterPlus T.Nφ T.N)) ∧
      ENNReal.ofReal (3 * T.Lx / 8 - 2 * δx δ₀ T) ≤
        slotSetDist (col δ₀ T T.N) (colBand δ₀ T (quarterMinus T.Nφ T.N)) := by
  have hL := Lx_eq_two_κN_dev T
  have hκ := T.κ_pos
  constructor
  · apply slotSetDist_ge_dev
    intro s hs s' hs'
    obtain ⟨j', hj', hsj'⟩ := mem_colBand_dev hs'
    have h := col_sep_dev hs hsj'
    simp only [Int.cast_zero, mul_zero, sub_zero, Int.cast_natCast] at h
    obtain ⟨h2, h3⟩ := quarterPlus_val_dev hj'
    have h3' : (j'.val : ℝ) + 1 ≤ T.N := by exact_mod_cast h3
    have hp : 3 * T.Lx / 8 ≤ pdist T.Lx (T.κ * (j'.val : ℝ)) := by
      refine pdist_ge_dev T.Lx_pos (mul_nonneg hκ.le (Nat.cast_nonneg _)) ?_ ?_ ?_
      · rw [hL]; nlinarith
      · rw [hL]; nlinarith
      · rw [hL]; nlinarith
    linarith
  · apply slotSetDist_ge_dev
    intro s hs s' hs'
    obtain ⟨j', hj', hsj'⟩ := mem_colBand_dev hs'
    have h := col_sep_dev hs hsj'
    have h1 := quarterMinus_val_dev hj'
    have h1' : 4 * (j'.val : ℝ) + 4 ≤ T.N := by exact_mod_cast h1
    have hp : 3 * T.Lx / 8 ≤ pdist T.Lx (T.κ * ((j'.val : ℕ) : ℤ) - T.κ * ((T.N : ℤ) : ℝ)) := by
      push_cast
      rw [← pdist_neg, show -(T.κ * (j'.val : ℝ) - T.κ * (T.N : ℝ)) = T.κ * ((T.N : ℝ) - j'.val) by ring]
      have hd0 : 0 ≤ (T.N : ℝ) - j'.val := by linarith [Nat.cast_nonneg (α := ℝ) j'.val]
      refine pdist_ge_dev T.Lx_pos (mul_nonneg hκ.le hd0) ?_ ?_ ?_
      · rw [hL]; nlinarith [Nat.cast_nonneg (α := ℝ) j'.val]
      · rw [hL]; nlinarith [Nat.cast_nonneg (α := ℝ) j'.val]
      · rw [hL]; nlinarith [Nat.cast_nonneg (α := ℝ) j'.val]
    linarith

/-- **Lemma 6.2**: "`All four right-hand sides are at least $\frac{c_*}{16}\sqrt N$ for $N\ge N_*$, with $N_*$ depending only on $c_*$ and $\delta_0$.`"
— with the proof's "`N\ge N_*:=\lceil(96\delta_0/c_*)^2\rceil`". -/
theorem sep_ge (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) {cstar : ℝ} (hc : 0 < cstar)
    (hLx : cstar * Real.sqrt T.N ≤ T.Lx) (hN : ⌈(96 * δ₀ / cstar) ^ 2⌉₊ ≤ T.N) :
    cstar / 16 * Real.sqrt T.N ≤ T.Lx / 2 - 2 * δx δ₀ T ∧
      cstar / 16 * Real.sqrt T.N ≤ T.Lx / 4 - 2 * δx δ₀ T ∧
      cstar / 16 * Real.sqrt T.N ≤ T.Lx / 8 - T.κ - 2 * δx δ₀ T ∧
      cstar / 16 * Real.sqrt T.N ≤ 3 * T.Lx / 8 - 2 * δx δ₀ T := by
  have hδx := (consistency_ii hδ₀ hT).2.2.1
  have hκ := κ_le hδ₀ hT
  unfold δplus at hδx
  have hsq : 96 * δ₀ / cstar ≤ Real.sqrt T.N := by
    have h1 : (96 * δ₀ / cstar) ^ 2 ≤ (T.N : ℝ) := by
      have h0 := Nat.le_ceil ((96 * δ₀ / cstar) ^ 2)
      have h2 : ((⌈(96 * δ₀ / cstar) ^ 2⌉₊ : ℕ) : ℝ) ≤ T.N := by exact_mod_cast hN
      linarith
    calc 96 * δ₀ / cstar = Real.sqrt ((96 * δ₀ / cstar) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt T.N := Real.sqrt_le_sqrt h1
  have h96 : 96 * δ₀ ≤ cstar * Real.sqrt T.N := by
    rw [div_le_iff₀ hc] at hsq
    linarith
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Lemma 6.2**: "`Moreover $\abs{\partial_\pm}\le2\ny\le CL_y\le C'\sqrt N$.`" — with the proof's
"`$C:=4\delta_0/\pi+\frac12$`" and "`$L_y=4\pi N/L_x\le(4\pi/c_*)\sqrt N$`". -/
theorem card_cut_le (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) {cstar : ℝ} (hc : 0 < cstar)
    (hLx : cstar * Real.sqrt T.N ≤ T.Lx) :
    (col δ₀ T 0).card ≤ 2 * ny δ₀ T ∧ (col δ₀ T T.N).card ≤ 2 * ny δ₀ T ∧
      (2 * ny δ₀ T : ℝ) ≤ (4 * δ₀ / π + 1 / 2) * T.Ly ∧ T.Ly ≤ 4 * π / cstar * Real.sqrt T.N := by
  have hcol : ∀ j : ℤ, (col δ₀ T j).card ≤ 2 * ny δ₀ T := by
    intro j
    obtain ⟨W, hW, hcolW⟩ := col_windows hδ₀ hT j
    rw [hcolW, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ hW
  have hπ := Real.pi_pos
  refine ⟨hcol 0, hcol T.N, ?_, ?_⟩
  · have hny := ny_lt δ₀ T
    have hδx := (consistency_ii hδ₀ hT).2.2.1
    unfold δplus at hδx
    have hLy4 : 4 ≤ T.Ly := le_trans (le_max_left _ _) hT.1
    have h1 : 2 * δx δ₀ T / T.κ = δx δ₀ T * T.Ly / π := by
      unfold Torus.κ
      field_simp
    have h2 : δx δ₀ T * T.Ly / π ≤ 2 * δ₀ * T.Ly / π := by
      apply div_le_div_of_nonneg_right _ hπ.le
      nlinarith [T.Ly_pos]
    have h3 : 2 * (2 * δ₀ * T.Ly / π + 1) ≤ (4 * δ₀ / π + 1 / 2) * T.Ly := by
      have e : 2 * (2 * δ₀ * T.Ly / π + 1) = 4 * δ₀ / π * T.Ly + 2 := by ring
      rw [e]
      nlinarith
    rw [h1] at hny
    linarith
  · have harea : T.Lx * T.Ly = 4 * π * T.N := by
      have := T.area
      push_cast at this
      linarith
    have hsqN : Real.sqrt T.N * Real.sqrt T.N = T.N := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hsN : 0 < Real.sqrt T.N := Real.sqrt_pos.2 (by exact_mod_cast T.N_pos)
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [T.Ly_pos]

/-! ### Proof devices for the half-tori (phase (b), round one; not statements of the paper)

Every half-torus and translate is `{R | R_x ∈ A}` for an `L_x`-periodic Borel `A ⊆ ℝ` of the form
`circImage L_x (a, a + L_x/2]` or its complement; the measure of `A ∩ [0, L_x)` is `L_x/2` by Mathlib's
`Function.Periodic.intervalIntegral_add_eq` (the integral of the periodic indicator over a period does not depend on
where the period starts) and the computation over `(a, a + L_x]`. -/

section HalfDevices

theorem measurableSet_circImage_dev (L : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) : MeasurableSet (circImage L J) := by
  have e : circImage L J = ⋃ m : ℤ, (fun x : ℝ => x + m * L) ⁻¹' J := by
    ext x
    simp [circImage]
  rw [e]
  exact MeasurableSet.iUnion fun m => measurable_add_const _ hJ

theorem circImage_add_dev (L : ℝ) (J : Set ℝ) (x : ℝ) : x + L ∈ circImage L J ↔ x ∈ circImage L J := by
  simp only [circImage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m + 1, by push_cast; convert hm using 1; ring⟩
  · rintro ⟨m, hm⟩
    exact ⟨m - 1, by push_cast; convert hm using 1; ring⟩

theorem preimage_sub_circImage_dev (L c a b : ℝ) :
    (fun x : ℝ => x - c) ⁻¹' circImage L (Set.Ioc a b) = circImage L (Set.Ioc (a + c) (b + c)) := by
  ext x
  simp only [circImage, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioc]
  constructor
  · rintro ⟨m, h1, h2⟩
    exact ⟨m, by linarith, by linarith⟩
  · rintro ⟨m, h1, h2⟩
    exact ⟨m, by linarith, by linarith⟩

theorem shiftX_fst_dev (T : Torus) (j₀ : ℤ) (A : Set ℝ) :
    shiftX T j₀ {R : ℝ × ℝ | R.1 ∈ A} = {R : ℝ × ℝ | R.1 ∈ (fun x : ℝ => x - T.κ * j₀) ⁻¹' A} := by
  ext R
  simp [shiftX]

theorem isTorusSet_fst_dev (T : Torus) {A : Set ℝ} (hA : MeasurableSet A) (hper : ∀ x, x + T.Lx ∈ A ↔ x ∈ A) :
    IsTorusSet T {R : ℝ × ℝ | R.1 ∈ A} := by
  refine ⟨measurable_fst hA, fun R => ?_, fun R => ?_⟩
  · simp only [Set.mem_setOf_eq, Prod.fst_add]
    exact hper R.1
  · simp only [Set.mem_setOf_eq, Prod.fst_add, add_zero]

theorem volume_fst_inter_fundDom_dev (T : Torus) (A : Set ℝ) :
    volume ({R : ℝ × ℝ | R.1 ∈ A} ∩ fundDom T) = volume (A ∩ Set.Ico 0 T.Lx) * ENNReal.ofReal T.Ly := by
  have e : {R : ℝ × ℝ | R.1 ∈ A} ∩ fundDom T = (A ∩ Set.Ico 0 T.Lx) ×ˢ Set.Ico 0 T.Ly := by
    ext R
    simp only [fundDom, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_prod]
    tauto
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, sub_zero]

theorem volume_circImage_Ioc_dev {L : ℝ} (hL : 0 < L) (a : ℝ) :
    volume (circImage L (Set.Ioc a (a + L / 2)) ∩ Set.Ico 0 L) = ENNReal.ofReal (L / 2) := by
  set A := circImage L (Set.Ioc a (a + L / 2)) with hA
  have hAm : MeasurableSet A := measurableSet_circImage_dev L measurableSet_Ioc
  have hper : Function.Periodic (A.indicator (1 : ℝ → ℝ)) L := by
    intro x
    have h := circImage_add_dev L (Set.Ioc a (a + L / 2)) x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h.mpr hx)]
      rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (h.mp h'))]
  have hint : ∀ t : ℝ, ∫ x in t..t + L, A.indicator (1 : ℝ → ℝ) x = volume.real (A ∩ Set.Ioc t (t + L)) := by
    intro t
    rw [intervalIntegral.integral_of_le (by linarith), integral_indicator_one hAm, measureReal_restrict_apply hAm]
  have hseg : A ∩ Set.Ioc a (a + L) = Set.Ioc a (a + L / 2) := by
    ext x
    simp only [hA, circImage, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨m, hm1, hm2⟩, hx1, hx2⟩
      have h3 : (m : ℝ) < 1 := lt_of_mul_lt_mul_right (by linarith : (m : ℝ) * L < 1 * L) hL.le
      have h4 : (-1 : ℝ) < m := lt_of_mul_lt_mul_right (by linarith : (-1 : ℝ) * L < m * L) hL.le
      have h5 : m < 1 := by exact_mod_cast h3
      have h6 : -1 < m := by exact_mod_cast h4
      have hm0 : m = 0 := by omega
      subst hm0
      simp only [Int.cast_zero, zero_mul, add_zero] at hm1 hm2
      exact ⟨hm1, hm2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨0, by simpa using hx1, by simpa using hx2⟩, hx1, by linarith⟩
  have hreal : volume.real (A ∩ Set.Ioc 0 L) = L / 2 := by
    have h := hper.intervalIntegral_add_eq 0 a
    have h0 := hint 0
    rw [zero_add] at h h0
    rw [h0, hint a, hseg, Real.volume_real_Ioc_of_le (by linarith)] at h
    linarith
  rw [measure_congr (Filter.EventuallyEqSet.rfl.inter (Ico_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := L))),
    ← ofReal_measureReal (ne_top_of_le_ne_top (measure_Ioc_lt_top (μ := volume) (a := (0 : ℝ)) (b := L)).ne
      (measure_mono Set.inter_subset_right)), hreal]

theorem volume_compl_circImage_Ioc_dev {L : ℝ} (hL : 0 < L) (a : ℝ) :
    volume ((circImage L (Set.Ioc a (a + L / 2)))ᶜ ∩ Set.Ico 0 L) = ENNReal.ofReal (L / 2) := by
  set A := circImage L (Set.Ioc a (a + L / 2)) with hA
  have hAm : MeasurableSet A := measurableSet_circImage_dev L measurableSet_Ioc
  have e : Aᶜ ∩ Set.Ico 0 L = Set.Ico 0 L \ (A ∩ Set.Ico 0 L) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
    tauto
  rw [e, measure_diff Set.inter_subset_right (hAm.inter measurableSet_Ico).nullMeasurableSet
    (ne_top_of_le_ne_top (measure_Ico_lt_top (μ := volume) (a := (0 : ℝ)) (b := L)).ne
      (measure_mono Set.inter_subset_right)), volume_circImage_Ioc_dev hL a, Real.volume_Ico, sub_zero,
    ← ENNReal.ofReal_sub L (show (0 : ℝ) ≤ L / 2 by positivity)]
  congr 1
  ring

/-- The two measures of a half-torus-shaped set `{R | R_x ∈ A}` with `A = circImage L_x (a, a + L_x/2]` or its
complement. -/
theorem volume_half_dev (T : Torus) (a b : ℝ) (hb : b = a + T.Lx / 2) :
    volume ({R : ℝ × ℝ | R.1 ∈ circImage T.Lx (Set.Ioc a b)} ∩ fundDom T) = ENNReal.ofReal (2 * π * T.N) ∧
      volume ({R : ℝ × ℝ | R.1 ∈ (circImage T.Lx (Set.Ioc a b))ᶜ} ∩ fundDom T) = ENNReal.ofReal (2 * π * T.N) := by
  subst hb
  have hL := T.Lx_pos
  have harea : T.Lx / 2 * T.Ly = 2 * π * T.N := by
    have := T.area
    push_cast at this
    linarith
  rw [volume_fst_inter_fundDom_dev, volume_fst_inter_fundDom_dev, volume_circImage_Ioc_dev hL a,
    volume_compl_circImage_Ioc_dev hL a, ← ENNReal.ofReal_mul (by positivity), harea]
  exact ⟨rfl, rfl⟩

end HalfDevices

/-! ### The half-tori -/

/-- The half-tori are Borel sets of the torus (block C's `IsTorusSet`), and so are their translates. -/
theorem isTorusSet_half (T : Torus) (j₀ : ℤ) :
    IsTorusSet T (halfMinus T) ∧ IsTorusSet T (halfPlus T) ∧ IsTorusSet T (shiftX T j₀ (halfMinus T)) ∧
      IsTorusSet T (shiftX T j₀ (halfPlus T)) := by
  set A₀ := circImage T.Lx (Set.Ioc (-(T.Lx / 4)) (T.Lx / 4)) with hA₀
  have hm : MeasurableSet A₀ := measurableSet_circImage_dev _ measurableSet_Ioc
  have hp : ∀ x, x + T.Lx ∈ A₀ ↔ x ∈ A₀ := circImage_add_dev _ _
  have hs : (fun x : ℝ => x - T.κ * j₀) ⁻¹' A₀ =
      circImage T.Lx (Set.Ioc (-(T.Lx / 4) + T.κ * j₀) (T.Lx / 4 + T.κ * j₀)) :=
    preimage_sub_circImage_dev _ _ _ _
  have hm' : MeasurableSet ((fun x : ℝ => x - T.κ * j₀) ⁻¹' A₀) := by
    rw [hs]
    exact measurableSet_circImage_dev _ measurableSet_Ioc
  have hp' : ∀ x, x + T.Lx ∈ (fun x : ℝ => x - T.κ * j₀) ⁻¹' A₀ ↔ x ∈ (fun x : ℝ => x - T.κ * j₀) ⁻¹' A₀ := by
    rw [hs]
    exact circImage_add_dev _ _
  have e1 : halfMinus T = {R : ℝ × ℝ | R.1 ∈ A₀} := rfl
  have e2 : halfPlus T = {R : ℝ × ℝ | R.1 ∈ A₀ᶜ} := rfl
  have e3 : shiftX T j₀ (halfMinus T) = {R : ℝ × ℝ | R.1 ∈ (fun x : ℝ => x - T.κ * j₀) ⁻¹' A₀} := by
    rw [e1, shiftX_fst_dev]
  have e4 : shiftX T j₀ (halfPlus T) = {R : ℝ × ℝ | R.1 ∈ ((fun x : ℝ => x - T.κ * j₀) ⁻¹' A₀)ᶜ} := by
    rw [e2, shiftX_fst_dev]
    rfl
  rw [e3, e4, e1, e2]
  exact ⟨isTorusSet_fst_dev T hm hp, isTorusSet_fst_dev T hm.compl (fun x => not_congr (hp x)),
    isTorusSet_fst_dev T hm' hp', isTorusSet_fst_dev T hm'.compl (fun x => not_congr (hp' x))⟩

/-- The proof of Lemma 6.6(i): "`$\abs{\Tor_N^\pm}=\frac12\abs{\Tor_N}=2\pi N$`" — the measure of the part of each half-torus
(and of each translate) in the fundamental domain. -/
theorem volume_half (T : Torus) (j₀ : ℤ) :
    volume (halfMinus T ∩ fundDom T) = ENNReal.ofReal (2 * π * T.N) ∧
      volume (halfPlus T ∩ fundDom T) = ENNReal.ofReal (2 * π * T.N) ∧
      volume (shiftX T j₀ (halfMinus T) ∩ fundDom T) = ENNReal.ofReal (2 * π * T.N) ∧
      volume (shiftX T j₀ (halfPlus T) ∩ fundDom T) = ENNReal.ofReal (2 * π * T.N) := by
  set A₀ := circImage T.Lx (Set.Ioc (-(T.Lx / 4)) (T.Lx / 4)) with hA₀
  have hs : (fun x : ℝ => x - T.κ * j₀) ⁻¹' A₀ =
      circImage T.Lx (Set.Ioc (-(T.Lx / 4) + T.κ * j₀) (T.Lx / 4 + T.κ * j₀)) :=
    preimage_sub_circImage_dev _ _ _ _
  have e1 : halfMinus T = {R : ℝ × ℝ | R.1 ∈ A₀} := rfl
  have e2 : halfPlus T = {R : ℝ × ℝ | R.1 ∈ A₀ᶜ} := rfl
  have e3 : shiftX T j₀ (halfMinus T) = {R : ℝ × ℝ | R.1 ∈ (fun x : ℝ => x - T.κ * j₀) ⁻¹' A₀} := by
    rw [e1, shiftX_fst_dev]
  have e4 : shiftX T j₀ (halfPlus T) = {R : ℝ × ℝ | R.1 ∈ ((fun x : ℝ => x - T.κ * j₀) ⁻¹' A₀)ᶜ} := by
    rw [e2, shiftX_fst_dev]
    rfl
  have h0 := volume_half_dev T (-(T.Lx / 4)) (T.Lx / 4) (by ring)
  have h1 := volume_half_dev T (-(T.Lx / 4) + T.κ * j₀) (T.Lx / 4 + T.κ * j₀) (by ring)
  rw [e3, e4, e1, e2, hs]
  exact ⟨h0.1, h0.2, h1.1, h1.2⟩

/-! ### Lemma 6.6 (the split of the current) -/

/-! #### Proof devices for Lemma 6.6(i) (phase (b), round one; not statements of the paper) -/

section CurrentDevices

theorem measurableSet_halfMinus_dev (T : Torus) : MeasurableSet (halfMinus T) :=
  measurable_fst (measurableSet_circImage_dev T.Lx measurableSet_Ioc)

theorem measurableSet_shiftX_halfMinus_dev (T : Torus) (j₀ : ℤ) : MeasurableSet (shiftX T j₀ (halfMinus T)) :=
  (isTorusSet_half T j₀).2.2.1.1

theorem shiftX_halfPlus_dev (T : Torus) (j₀ : ℤ) : shiftX T j₀ (halfPlus T) = (shiftX T j₀ (halfMinus T))ᶜ := rfl

/-- `H_N = H_𝒟 + H_{𝒟ᶜ}` for a Borel `𝒟`. -/
theorem HDd_add_compl_dev (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx) {D : Set (ℝ × ℝ)} (hD : MeasurableSet D) :
    S.HDd N D + S.HDd N Dᶜ = S.H N := by
  rw [S.d.eq_opIntegral N hN, opIntegral_split _ D hD _ (integrableOn_h S.d hN)]
  unfold IxSetting.HDd
  congr 2
  · exact Set.inter_comm _ _
  · rw [Set.diff_eq, Set.inter_comm]

theorem HDd_isSelfAdjoint_dev (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx) (D : Set (ℝ × ℝ)) :
    IsSelfAdjoint (S.HDd N D) :=
  ms_isSelfAdjoint_opIntegral _ (S.d.h_isSelfAdjoint N hN)

theorem HDd_isSectorPreserving_dev (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx) (D : Set (ℝ × ℝ)) :
    IsSectorPreserving (S.T N) (S.HDd N D) := by
  have hint : ∀ m m' : Conf (ZMod (S.T N).Nφ),
      MeasureTheory.IntegrableOn (fun R => S.d.h N R m m') (D ∩ fundDom (S.T N)) :=
    fun m m' => (integrableOn_h S.d hN m m').mono_set Set.inter_subset_right
  exact ⟨(opIntegral_commute_dev _ hint fun R => (S.d.h_isSectorPreserving N hN R).1.symm).symm,
    (opIntegral_commute_dev _ hint fun R => (S.d.h_isSectorPreserving N hN R).2.symm).symm⟩

theorem isSelfAdjoint_curr_dev {S : Type*} [Fintype S] [DecidableEq S] {A B : Op S} (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B) : IsSelfAdjoint ((I : ℂ) • (A * B - B * A)) := by
  show star ((I : ℂ) • (A * B - B * A)) = (I : ℂ) • (A * B - B * A)
  rw [star_smul, star_sub, star_mul, star_mul, hA.star_eq, hB.star_eq, Complex.star_def, Complex.conj_I, neg_smul,
    ← smul_neg, neg_sub]

theorem isSectorPreserving_curr_dev {T : Torus} {A B : FockOp T} (hA : IsSectorPreserving T A)
    (hB : IsSectorPreserving T B) : IsSectorPreserving T ((I : ℂ) • (A * B - B * A)) :=
  ⟨((hA.1.mul_left hB.1).sub_left (hB.1.mul_left hA.1)).smul_left _,
    ((hA.2.mul_left hB.2).sub_left (hB.2.mul_left hA.2)).smul_left _⟩

theorem curr_isSelfAdjoint_dev (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx) (D : Set (ℝ × ℝ))
    (B : Finset (ZMod (S.T N).Nφ)) :
    IsSelfAdjoint (S.curr N D B) ∧ IsSectorPreserving (S.T N) (S.curr N D B) :=
  ⟨isSelfAdjoint_curr_dev (HDd_isSelfAdjoint_dev S hN D) (Qband_isSelfAdjoint _ B),
    isSectorPreserving_curr_dev (HDd_isSectorPreserving_dev S hN D) (Qband_isSectorPreserving _ B)⟩

/-- `i[H_𝒟, Q_B] + i[H_{𝒟ᶜ}, Q_B] = i[H_N, Q_B]`. -/
theorem curr_add_compl_dev (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx) {D : Set (ℝ × ℝ)} (hD : MeasurableSet D)
    (B : Finset (ZMod (S.T N).Nφ)) :
    S.curr N D B + S.curr N Dᶜ B =
      (I : ℂ) • (S.H N * Qband (S.T N) B - Qband (S.T N) B * S.H N) := by
  rw [← HDd_add_compl_dev S hN hD]
  unfold IxSetting.curr
  rw [← smul_add]
  congr 1
  noncomm_ring

theorem norm_curr_le_dev (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx) (D : Set (ℝ × ℝ))
    (hvol : volume (D ∩ fundDom (S.T N)) = ENNReal.ofReal (2 * π * N)) (B : Finset (ZMod (S.T N).Nφ))
    (hB : B.card ≤ N) :
    ‖toCLM (S.T N) (S.curr N D B)‖ ≤ 4 * π * S.d.Ch * (N : ℝ) ^ 2 := by
  have hCh : 0 ≤ S.d.Ch := (norm_nonneg _).trans (S.d.norm_h_le N hN 0)
  have hvr : volume.real (D ∩ fundDom (S.T N)) = 2 * π * N := by
    rw [measureReal_def, hvol, ENNReal.toReal_ofReal (by positivity)]
  have hfin : volume (D ∩ fundDom (S.T N)) < ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_lt_top
  have hA : ‖toCLM (S.T N) (S.HDd N D)‖ ≤ S.d.Ch * (2 * π * N) := by
    rw [← hvr]
    exact norm_opIntegral_le_const _ hfin _
      (fun m m' => (integrableOn_h S.d hN m m').mono_set Set.inter_subset_right)
      fun R _ => S.d.norm_h_le N hN R
  have hQ : ‖toCLM (S.T N) (Qband (S.T N) B)‖ ≤ N := (norm_Qband_le _ B).trans (by exact_mod_cast hB)
  have hA0 : 0 ≤ ‖toCLM (S.T N) (S.HDd N D)‖ := norm_nonneg _
  have hQ0 : 0 ≤ ‖toCLM (S.T N) (Qband (S.T N) B)‖ := norm_nonneg _
  have hc0 : 0 ≤ S.d.Ch * (2 * π * N) := mul_nonneg hCh (by positivity)
  unfold IxSetting.curr
  rw [toCLM_smul_dev, norm_smul, Complex.norm_I, one_mul, toCLM_sub', toCLM_mul', toCLM_mul']
  calc ‖toCLM (S.T N) (S.HDd N D) * toCLM (S.T N) (Qband (S.T N) B) -
        toCLM (S.T N) (Qband (S.T N) B) * toCLM (S.T N) (S.HDd N D)‖
      ≤ ‖toCLM (S.T N) (S.HDd N D)‖ * ‖toCLM (S.T N) (Qband (S.T N) B)‖ +
          ‖toCLM (S.T N) (Qband (S.T N) B)‖ * ‖toCLM (S.T N) (S.HDd N D)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ S.d.Ch * (2 * π * N) * N + N * (S.d.Ch * (2 * π * N)) :=
        add_le_add (mul_le_mul hA hQ hQ0 hc0) (mul_le_mul hQ hA hA0 (Nat.cast_nonneg _))
    _ = 4 * π * S.d.Ch * (N : ℝ) ^ 2 := by ring

theorem card_bandΓ_le_dev (Nφ N : ℕ) : (bandΓ Nφ N).card ≤ N :=
  Finset.card_image_le.trans (Finset.card_range N).le

theorem card_bandShift_le_dev (Nφ N : ℕ) (j₀ : ℤ) : (bandShift Nφ N j₀).card ≤ N :=
  Finset.card_image_le.trans (card_bandΓ_le_dev Nφ N)

theorem volume_half_N_dev (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx) (j₀ : ℤ) :
    volume (halfMinus (S.T N) ∩ fundDom (S.T N)) = ENNReal.ofReal (2 * π * N) ∧
      volume (halfPlus (S.T N) ∩ fundDom (S.T N)) = ENNReal.ofReal (2 * π * N) ∧
      volume (shiftX (S.T N) j₀ (halfMinus (S.T N)) ∩ fundDom (S.T N)) = ENNReal.ofReal (2 * π * N) ∧
      volume (shiftX (S.T N) j₀ (halfPlus (S.T N)) ∩ fundDom (S.T N)) = ENNReal.ofReal (2 * π * N) := by
  have h := volume_half (S.T N) j₀
  have hTN : ((S.T N).N : ℝ) = N := by exact_mod_cast S.Ts.T_N N hN
  rw [hTN] at h
  exact h

/-- The dressing in Lemma 5.9's spectral form (block D's `opIntegral_Wfilt_dyn`). -/
theorem dress_eq_dev {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) {γ : ℝ} (hγ : 0 < γ) {T : Torus} {H : FockOp T}
    (hH : IsSelfAdjoint H) (A : FockOp T) :
    dress ϑ γ H A =
      ∑ E ∈ specFinset H, ∑ E' ∈ specFinset H, What ϑ γ (E' - E) • (specProj H E * A * specProj H E') :=
  opIntegral_Wfilt_dyn hϑ hγ hH A

theorem dress_add_dev {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) {γ : ℝ} (hγ : 0 < γ) {T : Torus} {H : FockOp T}
    (hH : IsSelfAdjoint H) (A B : FockOp T) : dress ϑ γ H (A + B) = dress ϑ γ H A + dress ϑ γ H B := by
  rw [dress_eq_dev hϑ hγ hH, dress_eq_dev hϑ hγ hH, dress_eq_dev hϑ hγ hH, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun E' _ => ?_
  rw [mul_add, add_mul, smul_add]

theorem star_What_dev (ϑ : ℝ → ℝ) (γ w : ℝ) : star (What ϑ γ w) = -What ϑ γ w := by
  unfold What
  rw [Complex.star_def, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  ring

theorem isSelfAdjoint_specProj_dev {T : Torus} (H : FockOp T) (E : ℝ) : IsSelfAdjoint (specProj H E) :=
  cfc_predicate _ H

/-- A double spectral sum `∑ c(E, E') 1_{E}(H) A 1_{E'}(H)` with `c(E, E')^* = c(E', E)` of a self-adjoint `A` is
self-adjoint. -/
theorem isSelfAdjoint_specSum_dev {T : Torus} {H J : FockOp T} (hJ : IsSelfAdjoint J) (c : ℝ → ℝ → ℂ)
    (hc : ∀ E E', star (c E E') = c E' E) :
    IsSelfAdjoint (∑ E ∈ specFinset H, ∑ E' ∈ specFinset H, c E E' • (specProj H E * J * specProj H E')) := by
  show star _ = _
  simp only [star_sum, star_smul, star_mul, (isSelfAdjoint_specProj_dev H _).star_eq, hJ.star_eq, hc, mul_assoc]
  rw [Finset.sum_comm]

theorem isSectorPreserving_specSum_dev {T : Torus} {H J : FockOp T} (hH : IsSelfAdjoint H)
    (hHs : IsSectorPreserving T H) (hJ : IsSectorPreserving T J) (c : ℝ → ℝ → ℂ) :
    IsSectorPreserving T
      (∑ E ∈ specFinset H, ∑ E' ∈ specFinset H, c E E' • (specProj H E * J * specProj H E')) := by
  have hP : ∀ E, IsSectorPreserving T (specProj H E) := fun E => IsSectorPreserving.cfc T hH hHs _
  refine ⟨Commute.sum_left _ _ _ fun E _ => Commute.sum_left _ _ _ fun E' _ => ?_,
    Commute.sum_left _ _ _ fun E _ => Commute.sum_left _ _ _ fun E' _ => ?_⟩
  · exact (((hP E).1.mul_left hJ.1).mul_left (hP E').1).smul_left _
  · exact (((hP E).2.mul_left hJ.2).mul_left (hP E').2).smul_left _

theorem dress_props_dev {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) {γ : ℝ} (hγ : 0 < γ) {T : Torus} {H J : FockOp T}
    (hH : IsSelfAdjoint H) (hHs : IsSectorPreserving T H) (hJ : IsSelfAdjoint J) (hJs : IsSectorPreserving T J) :
    IsSelfAdjoint (dress ϑ γ H J) ∧ IsSectorPreserving T (dress ϑ γ H J) := by
  rw [dress_eq_dev hϑ hγ hH]
  refine ⟨isSelfAdjoint_specSum_dev hJ _ fun E E' => ?_, isSectorPreserving_specSum_dev hH hHs hJs _⟩
  rw [star_What_dev, ← What_neg hϑ, neg_sub]

end CurrentDevices

/-- **Lemma 6.6(i)**: "`$J_-+J_+=\iu[H_N,Q]$`". -/
theorem Jminus_add_Jplus (S : IxSetting η δ₀) :
    ∀ N ∈ S.Ts.idx, S.Jminus N + S.Jplus N = (I : ℂ) • (S.H N * S.Q N - S.Q N * S.H N) :=
  fun N hN => curr_add_compl_dev S hN (measurableSet_halfMinus_dev _) _

/-- **Lemma 6.6(i)**: "`hence $K=K_-+K_+$ and $\Qb=Q-K$`". -/
theorem Kfull_eq_add {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) {γ : ℝ} (hγ : 0 < γ) (S : IxSetting η δ₀) :
    ∀ N ∈ S.Ts.idx, S.Kfull ϑ γ N = S.Kminus ϑ γ N + S.Kplus ϑ γ N ∧ S.Qbar ϑ γ N = S.Q N - S.Kfull ϑ γ N := by
  intro N hN
  have hK : S.Kfull ϑ γ N = S.Kminus ϑ γ N + S.Kplus ϑ γ N := by
    unfold IxSetting.Kfull IxSetting.Kminus IxSetting.Kplus
    rw [← dress_add_dev hϑ hγ (S.d.H_isSelfAdjoint N hN), Jminus_add_Jplus S N hN]
  refine ⟨hK, ?_⟩
  unfold IxSetting.Qbar
  rw [hK, sub_sub]

/-- **Lemma 6.6(i)**: "`$J_\pm$ and $K_\pm$ are self-adjoint and sector-preserving`" — `J_±`. -/
theorem J_isSelfAdjoint (S : IxSetting η δ₀) :
    ∀ N ∈ S.Ts.idx, IsSelfAdjoint (S.Jminus N) ∧ IsSectorPreserving (S.T N) (S.Jminus N) ∧
      IsSelfAdjoint (S.Jplus N) ∧ IsSectorPreserving (S.T N) (S.Jplus N) := by
  intro N hN
  obtain ⟨h1, h2⟩ := curr_isSelfAdjoint_dev S hN (halfMinus (S.T N)) (bandΓ (S.T N).Nφ N)
  obtain ⟨h3, h4⟩ := curr_isSelfAdjoint_dev S hN (halfPlus (S.T N)) (bandΓ (S.T N).Nφ N)
  exact ⟨h1, h2, h3, h4⟩

/-- **Lemma 6.6(i)**: `K_±` are self-adjoint and sector-preserving (the proof: "`because $\Wg$ is real`"). -/
theorem K_isSelfAdjoint {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) {γ : ℝ} (hγ : 0 < γ) (S : IxSetting η δ₀) :
    ∀ N ∈ S.Ts.idx, IsSelfAdjoint (S.Kminus ϑ γ N) ∧ IsSectorPreserving (S.T N) (S.Kminus ϑ γ N) ∧
      IsSelfAdjoint (S.Kplus ϑ γ N) ∧ IsSectorPreserving (S.T N) (S.Kplus ϑ γ N) := by
  intro N hN
  obtain ⟨h1, h2, h3, h4⟩ := J_isSelfAdjoint S N hN
  have hH := S.d.H_isSelfAdjoint N hN
  have hHs := H_isSectorPreserving_dev S hN
  obtain ⟨k1, k2⟩ := dress_props_dev hϑ hγ hH hHs h1 h2
  obtain ⟨k3, k4⟩ := dress_props_dev hϑ hγ hH hHs h3 h4
  exact ⟨k1, k2, k3, k4⟩

/-- **Lemma 6.6(i)**: "`$\norm{J_\pm}\le4\pi C_hN^2$`". -/
theorem norm_J_le (S : IxSetting η δ₀) :
    ∀ N ∈ S.Ts.idx, ‖toCLM (S.T N) (S.Jminus N)‖ ≤ 4 * π * S.d.Ch * (N : ℝ) ^ 2 ∧
      ‖toCLM (S.T N) (S.Jplus N)‖ ≤ 4 * π * S.d.Ch * (N : ℝ) ^ 2 := by
  intro N hN
  obtain ⟨hv1, hv2, -, -⟩ := volume_half_N_dev S hN 0
  exact ⟨norm_curr_le_dev S hN _ hv1 _ (card_bandΓ_le_dev _ _),
    norm_curr_le_dev S hN _ hv2 _ (card_bandΓ_le_dev _ _)⟩

/-! #### Proof devices for Lemma 6.6(ii)–(iii) (phase (b), round two; not statements of the paper)

The paper's proof at one torus (`curr_approx_dev`), with three changes. (1) The far region `{ξ > ρ}` is bounded by
the supremum of the integrand times the volume `2πN` of the half-torus, instead of by the integral
`∫_ρ^∞ (1 + u)^{−k} du` over the transverse distance: the error is `O(N²(1 + ρ)^{−k})` rather than
`O(N²(1 + ρ)^{1−k})`, and no shift `k → k + 1` is needed. (2) Step 2 is taken orbital by orbital: an orbital whose
column meets `Ball(ρ, R)` contributes an element of `Alg(Ball(ρ, R) ∪ Col(j))`, the others commute with `h̃_{R,ρ}`
(`near_mem_dev`). (3) For the far band `𝓑_R ∈ {𝓑, 𝓑ᶜ}` the bound `‖Q_{𝓑_R}‖ ≤ N_φ = 2N` is used (`far_comm_le_dev`).
The geometry enters through the two hypotheses `hfar` (Step 1's band `𝓑_R`) and `hnear` (Step 3's inclusion), which
`far_band_dev`, `xi_half_dev` and `near_col_dev` discharge for the four currents. -/

section CurrentASDevices

/-- The constant of Lemma 6.6(ii)–(iii) in this proof. -/
def Jc_dev (δ₀ Ch : ℝ) (CH : ℕ → ℝ) (k : ℕ) : ℝ :=
  4 * π * |Ch| * (1 + 4 * δ₀) ^ k +
    2 * π * (4 * |CH k| + (4 * |CH k| + 2 * |Ch|) * (1 + 2 * δ₀) ^ k) * (2 + 4 * δ₀) ^ k

theorem rpow_neg_le_dev {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≤ c * b) (k : ℕ) :
    b ^ (-(k : ℝ)) ≤ c ^ k * a ^ (-(k : ℝ)) := by
  rw [Real.rpow_neg hb.le, Real.rpow_neg ha.le, Real.rpow_natCast, Real.rpow_natCast, ← div_eq_mul_inv,
    inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
  exact pow_le_pow_left₀ ha.le hab k

/-- `[X, ι(Q_{𝓑ᶜ})] = −[X, ι(Q_𝓑)]` for `X = ι(h)` with `[h, N_↑] = 0` (`Q_𝓑 + Q_{𝓑ᶜ} = N_↑`). -/
theorem comm_compl_dev (hη : IsProfile η) (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) {h : FockOp T}
    (hh : Commute h (Nsig T .up)) (B : Finset (ZMod T.Nφ)) :
    iota η δ₀ T h * iota η δ₀ T (Qband T Bᶜ) - iota η δ₀ T (Qband T Bᶜ) * iota η δ₀ T h =
      -(iota η δ₀ T h * iota η δ₀ T (Qband T B) - iota η δ₀ T (Qband T B) * iota η δ₀ T h) := by
  have e : Qband T Bᶜ = Nsig T .up - Qband T B := by
    rw [← Qband_univ, ← Finset.union_compl B, ← Qband_add _ disjoint_compl_right]
    abel
  have hc : Commute (iota η δ₀ T h) (iota η δ₀ T (Nsig T .up)) := by
    unfold Commute SemiconjBy
    rw [← iota_mul hη hδ₀ hT, ← iota_mul hη hδ₀ hT, hh.eq]
  rw [e, iota_sub' hη hδ₀ hT, mul_sub, sub_mul, hc.eq]
  abel

/-- Step 1 at one point `R` of the far region: `‖[ι(h_R), ι(Q_𝓑)]‖ ≤ (4|C^H_k| + 2|C_h|) N (1 + 2δ₀)^k (1 + ρ)^{−k}`
when `ξ > ρ` and every slot of `Col(𝓑_R)` is farther than `ξ − δ_x` from `R`. -/
theorem far_comm_le_dev (hη : IsProfile η) (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx)
    {B B' : Finset (ZMod (S.T N).Nφ)} (hB : B.card ≤ N) (hB' : B' = B ∨ B' = Bᶜ) (R : ℝ × ℝ) {ξ ρ : ℝ}
    (hρ : 0 ≤ ρ) (hξρ : ρ < ξ)
    (hfar : ∀ s ∈ colBand δ₀ (S.T N) B', ξ - δx δ₀ (S.T N) < flatDist (S.T N) (centre δ₀ (S.T N) s) R) (k : ℕ) :
    ‖opCLM (iota η δ₀ (S.T N) (S.d.h N R) * iota η δ₀ (S.T N) (Qband (S.T N) B) -
        iota η δ₀ (S.T N) (Qband (S.T N) B) * iota η δ₀ (S.T N) (S.d.h N R))‖ ≤
      (4 * |S.d.CH k| + 2 * |S.d.Ch|) * N * (1 + 2 * δ₀) ^ k * (1 + ρ) ^ (-(k : ℝ)) := by
  have hT := S.Ts.admissible N hN
  have hδx := δx_pos hδ₀ hT
  have hδx2 : δx δ₀ (S.T N) ≤ 2 * δ₀ := (consistency_ii hδ₀ hT).2.2.1
  have hρk : 0 ≤ (1 + ρ) ^ (-(k : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpow : (1 + δx δ₀ (S.T N)) ^ k ≤ (1 + 2 * δ₀) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
  have hsame : ‖opCLM (iota η δ₀ (S.T N) (S.d.h N R) * iota η δ₀ (S.T N) (Qband (S.T N) B) -
        iota η δ₀ (S.T N) (Qband (S.T N) B) * iota η δ₀ (S.T N) (S.d.h N R))‖ =
      ‖opCLM (iota η δ₀ (S.T N) (S.d.h N R) * iota η δ₀ (S.T N) (Qband (S.T N) B') -
        iota η δ₀ (S.T N) (Qband (S.T N) B') * iota η δ₀ (S.T N) (S.d.h N R))‖ := by
    rcases hB' with h | h
    · rw [h]
    · rw [h, comm_compl_dev hη hδ₀ hT (S.d.h_isSectorPreserving N hN R).1 B, opCLM_neg', norm_neg]
  rcases le_or_gt (δx δ₀ (S.T N)) ξ with hξ | hξ
  · obtain ⟨A, hA, hAb⟩ := S.d.approx k N hN R (ξ - δx δ₀ (S.T N)) (by linarith)
    have hdisj : Disjoint (slotBall δ₀ (S.T N) R (ξ - δx δ₀ (S.T N))) (colBand δ₀ (S.T N) B') := by
      rw [Finset.disjoint_left]
      intro s hs hs'
      simp only [slotBall, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      linarith [hfar s hs']
    have hc := commute_of_mem_Alg_of_mem_Alg hdisj hA (iota_Qband_mem_Alg hη hδ₀ hT B')
    have e : iota η δ₀ (S.T N) (S.d.h N R) * iota η δ₀ (S.T N) (Qband (S.T N) B') -
        iota η δ₀ (S.T N) (Qband (S.T N) B') * iota η δ₀ (S.T N) (S.d.h N R) =
        (iota η δ₀ (S.T N) (S.d.h N R) - A) * iota η δ₀ (S.T N) (Qband (S.T N) B') -
          iota η δ₀ (S.T N) (Qband (S.T N) B') * (iota η δ₀ (S.T N) (S.d.h N R) - A) := by
      rw [sub_mul, mul_sub, hc.eq]
      abel
    have hQ' : ‖opCLM (iota η δ₀ (S.T N) (Qband (S.T N) B'))‖ ≤ 2 * N := by
      rw [norm_iota hη hδ₀ hT]
      refine (norm_Qband_le _ B').trans ?_
      have h1 : B'.card ≤ 2 * N := by
        have h2 := Finset.card_le_univ B'
        rw [ZMod.card] at h2
        have h3 : (S.T N).Nφ = 2 * N := by
          show 2 * (S.Ts.T N).N = 2 * N
          rw [S.Ts.T_N N hN]
        omega
      exact_mod_cast h1
    have hk1 := rpow_neg_le_dev (a := 1 + ξ) (b := 1 + (ξ - δx δ₀ (S.T N))) (c := 1 + δx δ₀ (S.T N))
      (by linarith) (by linarith) (by linarith) (by nlinarith [mul_nonneg hδx.le (sub_nonneg.mpr hξ)]) k
    have hk2 := rpow_neg_le_dev (a := 1 + ρ) (b := 1 + ξ) (c := 1) (by linarith) (by linarith) one_pos
      (by linarith) k
    rw [one_pow, one_mul] at hk2
    have hXA : ‖opCLM (iota η δ₀ (S.T N) (S.d.h N R) - A)‖ ≤
        |S.d.CH k| * ((1 + δx δ₀ (S.T N)) ^ k * (1 + ρ) ^ (-(k : ℝ))) := by
      refine hAb.trans ?_
      refine (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)).trans ?_
      exact mul_le_mul_of_nonneg_left (hk1.trans (mul_le_mul_of_nonneg_left hk2 (by positivity))) (abs_nonneg _)
    rw [hsame, e]
    calc _ ≤ 2 * ‖opCLM (iota η δ₀ (S.T N) (S.d.h N R) - A)‖ *
          ‖opCLM (iota η δ₀ (S.T N) (Qband (S.T N) B'))‖ := norm_comm_le _ _
      _ ≤ 2 * (|S.d.CH k| * ((1 + δx δ₀ (S.T N)) ^ k * (1 + ρ) ^ (-(k : ℝ)))) * (2 * N) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hXA (by norm_num)) hQ' (norm_nonneg _) (by positivity)
      _ = 4 * |S.d.CH k| * N * (1 + δx δ₀ (S.T N)) ^ k * (1 + ρ) ^ (-(k : ℝ)) := by ring
      _ ≤ 4 * |S.d.CH k| * N * (1 + 2 * δ₀) ^ k * (1 + ρ) ^ (-(k : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hρk
      _ ≤ (4 * |S.d.CH k| + 2 * |S.d.Ch|) * N * (1 + 2 * δ₀) ^ k * (1 + ρ) ^ (-(k : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by linarith [abs_nonneg S.d.Ch]) hN0) (by positivity)) hρk
  · have hQ : ‖opCLM (iota η δ₀ (S.T N) (Qband (S.T N) B))‖ ≤ N := by
      rw [norm_iota hη hδ₀ hT]
      exact (norm_Qband_le _ B).trans (by exact_mod_cast hB)
    have hXn : ‖opCLM (iota η δ₀ (S.T N) (S.d.h N R))‖ ≤ |S.d.Ch| := by
      rw [norm_iota hη hδ₀ hT]
      exact (S.d.norm_h_le N hN R).trans (le_abs_self _)
    have hk3 := rpow_neg_le_dev (a := 1 + ρ) (b := 1) (c := 1 + δx δ₀ (S.T N)) (by linarith) one_pos
      (by linarith) (by linarith) k
    rw [Real.one_rpow] at hk3
    calc _ ≤ 2 * ‖opCLM (iota η δ₀ (S.T N) (S.d.h N R))‖ * ‖opCLM (iota η δ₀ (S.T N) (Qband (S.T N) B))‖ :=
          norm_comm_le _ _
      _ ≤ 2 * |S.d.Ch| * N :=
          mul_le_mul (mul_le_mul_of_nonneg_left hXn (by norm_num)) hQ (norm_nonneg _) (by positivity)
      _ ≤ 2 * |S.d.Ch| * N * ((1 + δx δ₀ (S.T N)) ^ k * (1 + ρ) ^ (-(k : ℝ))) :=
          le_mul_of_one_le_right (by positivity) hk3
      _ = 2 * |S.d.Ch| * N * (1 + δx δ₀ (S.T N)) ^ k * (1 + ρ) ^ (-(k : ℝ)) := by ring
      _ ≤ 2 * |S.d.Ch| * N * (1 + 2 * δ₀) ^ k * (1 + ρ) ^ (-(k : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hρk
      _ ≤ (4 * |S.d.CH k| + 2 * |S.d.Ch|) * N * (1 + 2 * δ₀) ^ k * (1 + ρ) ^ (-(k : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by linarith [abs_nonneg (S.d.CH k)]) hN0) (by positivity)) hρk

/-- Step 2 at one point `R` of the near region: `[h̃_{R,ρ}, ι(Q_𝓑)] ∈ Alg(Y)` for any `Y` containing every slot at
transverse distance `< ρ + 2δ_x` from `R`. -/
theorem near_mem_dev (hη : IsProfile η) (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx)
    (B : Finset (ZMod (S.T N).Nφ)) {Y : Finset (Slot δ₀ (S.T N))} (R : ℝ × ℝ) {ρ : ℝ}
    (hY : ∀ s : Slot δ₀ (S.T N), pdist (S.T N).Lx (xs δ₀ (S.T N) s - R.1) < ρ + 2 * δx δ₀ (S.T N) → s ∈ Y) :
    hTilde S.d N R ρ * iota η δ₀ (S.T N) (Qband (S.T N) B) -
      iota η δ₀ (S.T N) (Qband (S.T N) B) * hTilde S.d N R ρ ∈ Alg Y := by
  have hT := S.Ts.admissible N hN
  have hδx := δx_pos hδ₀ hT
  have hh := hTilde_mem_Alg hη hδ₀ S.d N hN R ρ
  have hball : ∀ s ∈ slotBall δ₀ (S.T N) R ρ, pdist (S.T N).Lx (xs δ₀ (S.T N) s - R.1) ≤ ρ := by
    intro s hs
    simp only [slotBall, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact (pdist_le_flatDist_fst (S.T N) (centre δ₀ (S.T N) s) R).trans hs
  have hhY : hTilde S.d N R ρ ∈ Alg Y := Alg_mono (fun s hs => hY s (by linarith [hball s hs])) hh
  have hQ : iota η δ₀ (S.T N) (Qband (S.T N) B) = ∑ j ∈ B, iota η δ₀ (S.T N) (njs (S.T N) j .up) := by
    unfold Qband
    rw [← iotaHom_apply hη hδ₀ hT, map_sum]
    simp only [iotaHom_apply]
  rw [hQ, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Alg_sum_mem _ _ fun j _ => ?_
  have hn := iota_njs_mem_Alg hη hδ₀ hT j
  by_cases hmeet : ∃ s' ∈ col δ₀ (S.T N) (j.val : ℤ), s' ∈ slotBall δ₀ (S.T N) R ρ
  · obtain ⟨s', hs'c, hs'b⟩ := hmeet
    have hcolY : col δ₀ (S.T N) (j.val : ℤ) ⊆ Y := by
      intro s hs
      apply hY
      rw [mem_col] at hs hs'c
      have h1 := hball s' hs'b
      have e : xs δ₀ (S.T N) s - R.1 = (xs δ₀ (S.T N) s - (S.T N).κ * ((j.val : ℤ) : ℝ)) +
          (-(xs δ₀ (S.T N) s' - (S.T N).κ * ((j.val : ℤ) : ℝ)) + (xs δ₀ (S.T N) s' - R.1)) := by ring
      rw [e]
      have t1 := pdist_add_le (S.T N).Lx (xs δ₀ (S.T N) s - (S.T N).κ * ((j.val : ℤ) : ℝ))
        (-(xs δ₀ (S.T N) s' - (S.T N).κ * ((j.val : ℤ) : ℝ)) + (xs δ₀ (S.T N) s' - R.1))
      have t2 := pdist_add_le (S.T N).Lx (-(xs δ₀ (S.T N) s' - (S.T N).κ * ((j.val : ℤ) : ℝ)))
        (xs δ₀ (S.T N) s' - R.1)
      rw [pdist_neg] at t2
      linarith
    have hnY : iota η δ₀ (S.T N) (njs (S.T N) j .up) ∈ Alg Y := Alg_mono hcolY hn
    exact ⟨sub_mem (mul_mem hhY.1 hnY.1) (mul_mem hnY.1 hhY.1),
      (hhY.2.mul_left hnY.2).sub_left (hnY.2.mul_left hhY.2)⟩
  · have hdisj : Disjoint (slotBall δ₀ (S.T N) R ρ) (col δ₀ (S.T N) (j.val : ℤ)) := by
      rw [Finset.disjoint_left]
      intro s hs hs'
      exact hmeet ⟨s, hs', hs⟩
    rw [(commute_of_mem_Alg_of_mem_Alg hdisj hh hn).eq, sub_self]
    exact Alg_zero_mem _

/-- Step 3's inclusion for a column: if `|R_x − κj|_{L_x} ≤ ρ` and `|x_s − R_x|_{L_x} < ρ + 2δ_x`, then
`s ∈ Col(j)^{(2ρ+2δ_x)}` (the column as a strip, and Lemma 3.10). -/
theorem near_col_dev (hδ₀ : 0 < δ₀) {T : Torus} (hT : T.Admissible δ₀) (j : ℤ) {R : ℝ × ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hR : pdist T.Lx (R.1 - T.κ * j) ≤ ρ) (s : Slot δ₀ T) (hs : pdist T.Lx (xs δ₀ T s - R.1) < ρ + 2 * δx δ₀ T) :
    s ∈ fat (col δ₀ T j) (2 * ρ + 2 * δx δ₀ T) := by
  have hδx := δx_pos hδ₀ hT
  have h1 : pdist T.Lx (xs δ₀ T s - T.κ * j) < 2 * ρ + 2 * δx δ₀ T := by
    have e : xs δ₀ T s - T.κ * j = (xs δ₀ T s - R.1) + (R.1 - T.κ * j) := by ring
    rw [e]
    have := pdist_add_le T.Lx (xs δ₀ T s - R.1) (R.1 - T.κ * j)
    linarith
  obtain ⟨m, hm⟩ := (pdist_lt_iff _ _ _).mp h1
  rw [col_eq_strip hδ₀ hT j]
  have e2 : 2 * ρ + 2 * δx δ₀ T = (2 * ρ + δx δ₀ T) + δx δ₀ T := by ring
  rw [e2]
  refine strip_cthickening_subset hδ₀ hT (by linarith) (by linarith) ?_
  rw [mem_strip, cthickening_circImage_Ioo T.Lx_pos (by linarith) (by linarith), mem_circImage]
  refine ⟨m, ?_⟩
  rw [Set.mem_Icc]
  rw [abs_lt] at hm
  constructor <;> linarith [hm.1, hm.2]

/-- `R_x − κj₀ = u + n L_x` with `u ∈ [0, L_x)` (`n = ⌊(R_x − κj₀)/L_x⌋`). -/
theorem floor_rep_dev {L : ℝ} (hL : 0 < L) (v : ℝ) :
    0 ≤ v - (⌊v / L⌋ : ℝ) * L ∧ v - (⌊v / L⌋ : ℝ) * L < L := by
  have h1 := Int.floor_le (v / L)
  have h2 := Int.lt_floor_add_one (v / L)
  have e : v / L * L = v := div_mul_cancel₀ v hL.ne'
  constructor
  · have := mul_le_mul_of_nonneg_right h1 hL.le
    linarith
  · have := mul_lt_mul_of_pos_right h2 hL
    nlinarith

/-- Step 1's band: for every `R`, one of `Γ + j₀` and its complement has all its orbitals at transverse distance at
least `min{ξ_-(R), ξ_+(R)}` from `R`, where `ξ_∓` are the distances to the lines `x = κj₀` and `x = κj₀ + L_x/2`
("`\abs{\kappa j-R_x}_{L_x}\ge\min\{\xi_-(R),\xi_+(R)\}`"); so every slot of its columns is farther than
`min{ξ_-, ξ_+} − δ_x` from `R`. -/
theorem far_band_dev (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx) (j₀ : ℤ) (R : ℝ × ℝ) :
    ∃ B' : Finset (ZMod (S.T N).Nφ), (B' = bandShift (S.T N).Nφ N j₀ ∨ B' = (bandShift (S.T N).Nφ N j₀)ᶜ) ∧
      ∀ s ∈ colBand δ₀ (S.T N) B',
        min (pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀)) (pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2)) -
          δx δ₀ (S.T N) < flatDist (S.T N) (centre δ₀ (S.T N) s) R := by
  have hT := S.Ts.admissible N hN
  have hTN : (S.T N).N = N := S.Ts.T_N N hN
  have hL : (S.T N).Lx = 2 * ((S.T N).κ * N) := by rw [Lx_eq_two_κN_dev, hTN]
  have hκ := (S.T N).κ_pos
  have hLpos := (S.T N).Lx_pos
  have hNφ : (S.T N).Nφ = 2 * N := by
    show 2 * (S.Ts.T N).N = 2 * N
    rw [S.Ts.T_N N hN]
  obtain ⟨hu0, huL⟩ := floor_rep_dev hLpos (R.1 - (S.T N).κ * j₀)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ⌊(R.1 - (S.T N).κ * j₀) / (S.T N).Lx⌋ := ⟨_, rfl⟩
  rw [← hn] at hu0 huL
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = R.1 - (S.T N).κ * j₀ - n * (S.T N).Lx := ⟨_, rfl⟩
  rw [← hu] at hu0 huL
  have hξm : pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀) ≤ min u ((S.T N).Lx - u) := by
    have e : R.1 - (S.T N).κ * j₀ = u + n * (S.T N).Lx := by rw [hu]; ring
    rw [e, pdist_add_int_mul]
    refine le_min ?_ ?_
    · have h := pdist_le_abs (S.T N).Lx u 0
      simp only [Int.cast_zero, zero_mul, add_zero] at h
      rwa [abs_of_nonneg hu0] at h
    · have h := pdist_le_abs (S.T N).Lx u (-1)
      have e2 : u + ((-1 : ℤ) : ℝ) * (S.T N).Lx = -((S.T N).Lx - u) := by push_cast; ring
      rwa [e2, abs_neg, abs_of_nonneg (by linarith)] at h
  have hξp : pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2) ≤ |u - (S.T N).Lx / 2| := by
    have e : R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2 = (u - (S.T N).Lx / 2) + n * (S.T N).Lx := by rw [hu]; ring
    rw [e, pdist_add_int_mul]
    have h := pdist_le_abs (S.T N).Lx (u - (S.T N).Lx / 2) 0
    simpa using h
  -- the triangle inequality through the orbital `j₀ + t`
  have htri : ∀ (s : Slot δ₀ (S.T N)) (t : ℕ),
      pdist (S.T N).Lx ((S.T N).κ * ((j₀ + t : ℤ) : ℝ) - R.1) ≤
        pdist (S.T N).Lx (xs δ₀ (S.T N) s - (S.T N).κ * ((j₀ + t : ℤ) : ℝ)) +
          flatDist (S.T N) (centre δ₀ (S.T N) s) R := by
    intro s t
    have e : (S.T N).κ * ((j₀ + t : ℤ) : ℝ) - R.1 =
        -(xs δ₀ (S.T N) s - (S.T N).κ * ((j₀ + t : ℤ) : ℝ)) + (xs δ₀ (S.T N) s - R.1) := by ring
    rw [e]
    have h1 := pdist_add_le (S.T N).Lx (-(xs δ₀ (S.T N) s - (S.T N).κ * ((j₀ + t : ℤ) : ℝ))) (xs δ₀ (S.T N) s - R.1)
    rw [pdist_neg] at h1
    have h2 : pdist (S.T N).Lx (xs δ₀ (S.T N) s - R.1) ≤ flatDist (S.T N) (centre δ₀ (S.T N) s) R :=
      pdist_le_flatDist_fst (S.T N) _ R
    linarith
  rcases lt_or_ge u ((S.T N).Lx / 2) with hu2 | hu2
  · refine ⟨_, Or.inr rfl, fun s hs => ?_⟩
    obtain ⟨j, hj, hsj⟩ := mem_colBand_dev hs
    obtain ⟨t, ht⟩ : ∃ t : ℕ, t = (j - (j₀ : ZMod (S.T N).Nφ)).val := ⟨_, rfl⟩
    have htlt : t < 2 * N := by rw [ht, ← hNφ]; exact ZMod.val_lt _
    have hjt : j = ((t : ℕ) : ZMod (S.T N).Nφ) + (j₀ : ZMod (S.T N).Nφ) := by
      rw [ht, ZMod.natCast_zmod_val]
      ring
    have htN : N ≤ t := by
      by_contra hlt
      push_neg at hlt
      apply Finset.mem_compl.mp hj
      exact Finset.mem_image.mpr ⟨(t : ZMod (S.T N).Nφ),
        Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr hlt, rfl⟩, hjt.symm⟩
    have hj' : j = ((j₀ + t : ℤ) : ZMod (S.T N).Nφ) := by
      rw [hjt]
      push_cast
      ring
    have hcol : col δ₀ (S.T N) (j.val : ℤ) = col δ₀ (S.T N) (j₀ + t) := by rw [hj', col_intCast_val]
    rw [hcol, mem_col] at hsj
    have ht1 : (N : ℝ) ≤ t := by exact_mod_cast htN
    have ht2 : (t : ℝ) + 1 ≤ 2 * N := by exact_mod_cast htlt
    have hκt1 : (S.T N).κ * N ≤ (S.T N).κ * t := mul_le_mul_of_nonneg_left ht1 hκ.le
    have hκt2 : (S.T N).κ * (t + 1) ≤ (S.T N).κ * (2 * N) := mul_le_mul_of_nonneg_left ht2 hκ.le
    have hw : pdist (S.T N).Lx ((S.T N).κ * ((j₀ + t : ℤ) : ℝ) - R.1) = pdist (S.T N).Lx ((S.T N).κ * t - u) := by
      have e : (S.T N).κ * ((j₀ + t : ℤ) : ℝ) - R.1 = ((S.T N).κ * t - u) + ((-n : ℤ) : ℝ) * (S.T N).Lx := by
        rw [hu]
        push_cast
        ring
      rw [e, pdist_add_int_mul]
    have hw0 : 0 ≤ (S.T N).κ * t - u := by linarith
    have hwL : (S.T N).κ * t - u ≤ (S.T N).Lx := by linarith
    have hwlow : min ((S.T N).Lx / 2 - u) u ≤ pdist (S.T N).Lx ((S.T N).κ * t - u) := by
      refine le_trans ?_ (le_pdist_dev hLpos hw0 hwL)
      exact le_min ((min_le_left _ _).trans (by linarith)) ((min_le_right _ _).trans (by linarith))
    have hmin : min (pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀))
        (pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2)) ≤ min ((S.T N).Lx / 2 - u) u := by
      have h1 : pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀) ≤ u := hξm.trans (min_le_left _ _)
      have h2 : pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2) ≤ (S.T N).Lx / 2 - u := by
        refine hξp.trans (le_of_eq ?_)
        rw [abs_of_neg (by linarith)]
        ring
      exact le_min ((min_le_right _ _).trans h2) ((min_le_left _ _).trans h1)
    have h3 := htri s t
    rw [hw] at h3
    linarith
  · refine ⟨_, Or.inl rfl, fun s hs => ?_⟩
    obtain ⟨j, hj, hsj⟩ := mem_colBand_dev hs
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj'
    rw [Finset.mem_range] at ht
    have hcol : col δ₀ (S.T N) (((t : ZMod (S.T N).Nφ) + (j₀ : ZMod (S.T N).Nφ)).val : ℤ) =
        col δ₀ (S.T N) (j₀ + t) := by
      have hj'' : (t : ZMod (S.T N).Nφ) + (j₀ : ZMod (S.T N).Nφ) = ((j₀ + t : ℤ) : ZMod (S.T N).Nφ) := by
        push_cast
        ring
      rw [hj'', col_intCast_val]
    rw [hcol, mem_col] at hsj
    have ht1 : (t : ℝ) + 1 ≤ N := by exact_mod_cast ht
    have hκt : (S.T N).κ * (t + 1) ≤ (S.T N).κ * N := mul_le_mul_of_nonneg_left ht1 hκ.le
    have hκt0 : 0 ≤ (S.T N).κ * t := mul_nonneg hκ.le (Nat.cast_nonneg t)
    have hw : pdist (S.T N).Lx ((S.T N).κ * ((j₀ + t : ℤ) : ℝ) - R.1) = pdist (S.T N).Lx (u - (S.T N).κ * t) := by
      have e : (S.T N).κ * ((j₀ + t : ℤ) : ℝ) - R.1 = -((u - (S.T N).κ * t) + ((n : ℤ) : ℝ) * (S.T N).Lx) := by
        rw [hu]
        push_cast
        ring
      rw [e, pdist_neg, pdist_add_int_mul]
    have hw0 : 0 ≤ u - (S.T N).κ * t := by linarith
    have hwL : u - (S.T N).κ * t ≤ (S.T N).Lx := by linarith
    have hwlow : min (u - (S.T N).Lx / 2) ((S.T N).Lx - u) ≤ pdist (S.T N).Lx (u - (S.T N).κ * t) := by
      refine le_trans ?_ (le_pdist_dev hLpos hw0 hwL)
      exact le_min ((min_le_left _ _).trans (by linarith)) ((min_le_right _ _).trans (by linarith))
    have hmin : min (pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀))
        (pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2)) ≤ min (u - (S.T N).Lx / 2) ((S.T N).Lx - u) := by
      have h1 : pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀) ≤ (S.T N).Lx - u := hξm.trans (min_le_right _ _)
      have h2 : pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2) ≤ u - (S.T N).Lx / 2 := by
        refine hξp.trans (le_of_eq ?_)
        rw [abs_of_nonneg (by linarith)]
      exact le_min ((min_le_right _ _).trans h2) ((min_le_left _ _).trans h1)
    have h3 := htri s t
    rw [hw] at h3
    linarith

/-- On each half-torus the nearer centre line is its own: "`$\xi_\pm(R)\le\xi_\mp(R)$ for $R\in\Tor_N^\pm$`" (for the
translates by `κj₀e_x`; `ξ_+` is the distance to `x = κj₀ + L_x/2`). -/
theorem xi_half_dev (S : IxSetting η δ₀) {N : ℕ} (j₀ : ℤ) (R : ℝ × ℝ) :
    (R ∈ shiftX (S.T N) j₀ (halfMinus (S.T N)) →
      pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀) ≤ pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2)) ∧
    (R ∈ shiftX (S.T N) j₀ (halfPlus (S.T N)) →
      pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2) ≤ pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀)) := by
  have hLpos := (S.T N).Lx_pos
  obtain ⟨hu0, huL⟩ := floor_rep_dev hLpos (R.1 - (S.T N).κ * j₀)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ⌊(R.1 - (S.T N).κ * j₀) / (S.T N).Lx⌋ := ⟨_, rfl⟩
  rw [← hn] at hu0 huL
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = R.1 - (S.T N).κ * j₀ - n * (S.T N).Lx := ⟨_, rfl⟩
  rw [← hu] at hu0 huL
  have ev : R.1 - (S.T N).κ * j₀ = u + n * (S.T N).Lx := by rw [hu]; ring
  have ev2 : R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2 = (u - (S.T N).Lx / 2) + n * (S.T N).Lx := by rw [hu]; ring
  have hmem : R ∈ shiftX (S.T N) j₀ (halfMinus (S.T N)) ↔
      ∃ m : ℤ, (R.1 - (S.T N).κ * j₀) + m * (S.T N).Lx ∈ Set.Ioc (-((S.T N).Lx / 4)) ((S.T N).Lx / 4) := Iff.rfl
  rw [ev2, ev, pdist_add_int_mul, pdist_add_int_mul]
  -- `|u|_L ≤ min{u, L − u}` and `|u − L/2|_L ≤ |u − L/2|`; lower bounds from `le_pdist_dev`
  have hup : pdist (S.T N).Lx u ≤ min u ((S.T N).Lx - u) := by
    refine le_min ?_ ?_
    · have h := pdist_le_abs (S.T N).Lx u 0
      simp only [Int.cast_zero, zero_mul, add_zero] at h
      rwa [abs_of_nonneg hu0] at h
    · have h := pdist_le_abs (S.T N).Lx u (-1)
      have e2 : u + ((-1 : ℤ) : ℝ) * (S.T N).Lx = -((S.T N).Lx - u) := by push_cast; ring
      rwa [e2, abs_neg, abs_of_nonneg (by linarith)] at h
  have hdp : pdist (S.T N).Lx (u - (S.T N).Lx / 2) ≤ |u - (S.T N).Lx / 2| := by
    have h := pdist_le_abs (S.T N).Lx (u - (S.T N).Lx / 2) 0
    simpa using h
  have hlo : min u ((S.T N).Lx - u) ≤ pdist (S.T N).Lx u := le_pdist_dev hLpos hu0 huL.le
  have hdlo : |u - (S.T N).Lx / 2| ≤ pdist (S.T N).Lx (u - (S.T N).Lx / 2) := by
    rcases le_or_gt ((S.T N).Lx / 2) u with h | h
    · rw [abs_of_nonneg (by linarith)]
      refine le_trans (le_min le_rfl (by linarith)) (le_pdist_dev hLpos (by linarith) (by linarith))
    · rw [abs_of_neg (by linarith), ← pdist_neg]
      refine le_trans (le_min (by linarith) (by linarith)) (le_pdist_dev hLpos (by linarith) (by linarith))
  constructor
  · intro hR
    obtain ⟨m, hm⟩ := hmem.mp hR
    rw [ev, Set.mem_Ioc] at hm
    have e3 : u + n * (S.T N).Lx + m * (S.T N).Lx = u + ((n + m : ℤ) : ℝ) * (S.T N).Lx := by push_cast; ring
    rw [e3] at hm
    have hk1 : -2 < n + m := by
      by_contra h
      push_neg at h
      have h' : ((n + m : ℤ) : ℝ) ≤ -2 := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_right h' hLpos.le]
    have hk2 : n + m < 1 := by
      by_contra h
      push_neg at h
      have h' : (1 : ℝ) ≤ ((n + m : ℤ) : ℝ) := by exact_mod_cast h
      nlinarith [mul_le_mul_of_nonneg_right h' hLpos.le]
    rcases (by omega : n + m = -1 ∨ n + m = 0) with h | h
    · rw [h] at hm
      push_cast at hm
      -- `u > 3L/4`
      have h1 : 3 * (S.T N).Lx / 4 < u := by linarith [hm.1]
      calc pdist (S.T N).Lx u ≤ (S.T N).Lx - u := hup.trans (min_le_right _ _)
        _ ≤ |u - (S.T N).Lx / 2| := by rw [abs_of_nonneg (by linarith)]; linarith
        _ ≤ _ := hdlo
    · rw [h] at hm
      push_cast at hm
      have h1 : u ≤ (S.T N).Lx / 4 := by linarith [hm.2]
      calc pdist (S.T N).Lx u ≤ u := hup.trans (min_le_left _ _)
        _ ≤ |u - (S.T N).Lx / 2| := by rw [abs_of_neg (by linarith)]; linarith
        _ ≤ _ := hdlo
  · intro hR
    have hR' : ¬ R ∈ shiftX (S.T N) j₀ (halfMinus (S.T N)) := hR
    rw [hmem] at hR'
    push_neg at hR'
    have h1 := hR' (-n)
    have h2 := hR' (-n - 1)
    rw [ev, Set.mem_Ioc] at h1 h2
    have e4 : u + n * (S.T N).Lx + ((-n : ℤ) : ℝ) * (S.T N).Lx = u := by push_cast; ring
    have e5 : u + n * (S.T N).Lx + ((-n - 1 : ℤ) : ℝ) * (S.T N).Lx = u - (S.T N).Lx := by push_cast; ring
    rw [e4] at h1
    rw [e5] at h2
    have hu1 : (S.T N).Lx / 4 < u := by
      by_contra h
      push_neg at h
      exact h1 ⟨by linarith, h⟩
    have hu2 : u ≤ 3 * (S.T N).Lx / 4 := by
      by_contra h
      push_neg at h
      exact h2 ⟨by linarith, by linarith⟩
    calc pdist (S.T N).Lx (u - (S.T N).Lx / 2) ≤ |u - (S.T N).Lx / 2| := hdp
      _ ≤ min u ((S.T N).Lx - u) := by
          have h3 : |u - (S.T N).Lx / 2| ≤ (S.T N).Lx / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
          exact le_min (by linarith) (by linarith)
      _ ≤ pdist (S.T N).Lx u := hlo

/-- **Lemma 6.6(ii)–(iii) at one torus**: for a set `D` of volume `2πN` in the fundamental domain, a band `𝓑` with
`|𝓑| ≤ N`, a set `Z` of slots and a transverse distance `ξ` with Step 1's far band (`hfar`) and Step 3's inclusion
(`hnear`), the current `i[H_D, Q_𝓑]` has an approximant in `Alg(Z^{(r)})` with error `C_k N² (1 + r)^{−k}`. -/
theorem curr_approx_dev (hη : IsProfile η) (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx)
    {D : Set (ℝ × ℝ)} (hDm : MeasurableSet D) (hvol : volume (D ∩ fundDom (S.T N)) = ENNReal.ofReal (2 * π * N))
    {B : Finset (ZMod (S.T N).Nφ)} (hB : B.card ≤ N) {Z : Finset (Slot δ₀ (S.T N))} {ξ : ℝ × ℝ → ℝ}
    (hξ : Measurable ξ)
    (hfar : ∀ R ∈ D, ∃ B' : Finset (ZMod (S.T N).Nφ), (B' = B ∨ B' = Bᶜ) ∧
      ∀ s ∈ colBand δ₀ (S.T N) B', ξ R - δx δ₀ (S.T N) < flatDist (S.T N) (centre δ₀ (S.T N) s) R)
    (hnear : ∀ R ∈ D, ∀ ρ : ℝ, 0 ≤ ρ → ξ R ≤ ρ → ∀ s : Slot δ₀ (S.T N),
      pdist (S.T N).Lx (xs δ₀ (S.T N) s - R.1) < ρ + 2 * δx δ₀ (S.T N) → s ∈ fat Z (2 * ρ + 2 * δx δ₀ (S.T N)))
    (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ A' ∈ Alg (fat Z r), ‖opCLM (iota η δ₀ (S.T N) (S.curr N D B) - A')‖ ≤
      Jc_dev δ₀ S.d.Ch S.d.CH k * (N : ℝ) ^ 2 * (1 + r) ^ (-(k : ℝ)) := by
  have hT := S.Ts.admissible N hN
  have hδx := δx_pos hδ₀ hT
  have hδx2 : δx δ₀ (S.T N) ≤ 2 * δ₀ := (consistency_ii hδ₀ hT).2.2.1
  have hN1 : (1 : ℝ) ≤ N := one_le_of_mem_idx S.Ts hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hCh0 : 0 ≤ |S.d.Ch| := abs_nonneg _
  have hCH0 : 0 ≤ |S.d.CH k| := abs_nonneg _
  have hr1 : 0 ≤ (1 + r) ^ (-(k : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hX0 : 0 ≤ 2 * π * (4 * |S.d.CH k| + (4 * |S.d.CH k| + 2 * |S.d.Ch|) * (1 + 2 * δ₀) ^ k) *
      (2 + 4 * δ₀) ^ k := by positivity
  have hY0 : 0 ≤ 4 * π * |S.d.Ch| * (1 + 4 * δ₀) ^ k := by positivity
  rcases lt_or_ge r (2 * δx δ₀ (S.T N)) with hr2 | hr2
  · refine ⟨0, Alg_zero_mem _, ?_⟩
    rw [sub_zero, norm_iota hη hδ₀ hT]
    have h1 := norm_curr_le_dev S hN D hvol B hB
    have hk := rpow_neg_le_dev (a := 1 + r) (b := 1) (c := 1 + 4 * δ₀) (by linarith) one_pos (by linarith)
      (by linarith) k
    rw [Real.one_rpow] at hk
    calc ‖toCLM (S.T N) (S.curr N D B)‖ ≤ 4 * π * S.d.Ch * (N : ℝ) ^ 2 := h1
      _ ≤ 4 * π * |S.d.Ch| * (N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)) (by positivity)
      _ ≤ 4 * π * |S.d.Ch| * (N : ℝ) ^ 2 * ((1 + 4 * δ₀) ^ k * (1 + r) ^ (-(k : ℝ))) :=
          le_mul_of_one_le_right (by positivity) hk
      _ = 4 * π * |S.d.Ch| * (1 + 4 * δ₀) ^ k * (N : ℝ) ^ 2 * (1 + r) ^ (-(k : ℝ)) := by ring
      _ ≤ Jc_dev δ₀ S.d.Ch S.d.CH k * (N : ℝ) ^ 2 * (1 + r) ^ (-(k : ℝ)) := by
          unfold Jc_dev
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hX0)
            (by positivity)) hr1
  · obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (r - 2 * δx δ₀ (S.T N)) / 2 := ⟨_, rfl⟩
    have hρ0 : 0 ≤ ρ := by rw [hρdef]; linarith
    have hrρ : 2 * ρ + 2 * δx δ₀ (S.T N) = r := by rw [hρdef]; ring
    have hρk : 0 ≤ (1 + ρ) ^ (-(k : ℝ)) := Real.rpow_nonneg (by linarith) _
    obtain ⟨E, hE⟩ : ∃ E : Set (ℝ × ℝ), E = D ∩ fundDom (S.T N) := ⟨_, rfl⟩
    have hfdm : MeasurableSet (fundDom (S.T N)) := measurableSet_Ico.prod measurableSet_Ico
    have hEv : volume E ≠ ⊤ := by rw [hE, hvol]; exact ENNReal.ofReal_ne_top
    have hEvr : volume.real E = 2 * π * N := by
      rw [measureReal_def, hE, hvol, ENNReal.toReal_ofReal (by positivity)]
    obtain ⟨Dle, hDle⟩ : ∃ F : Set (ℝ × ℝ), F = {R | ξ R ≤ ρ} := ⟨_, rfl⟩
    have hDlem : MeasurableSet Dle := by rw [hDle]; exact measurableSet_le hξ measurable_const
    have hEm : MeasurableSet E := by rw [hE]; exact hDm.inter hfdm
    have hv1 : volume (E ∩ Dle) ≠ ⊤ := ne_top_of_le_ne_top hEv (measure_mono Set.inter_subset_left)
    have hv2 : volume (E \ Dle) ≠ ⊤ := ne_top_of_le_ne_top hEv (measure_mono Set.diff_subset)
    have hvr1 : volume.real (E ∩ Dle) ≤ 2 * π * N := (measureReal_mono Set.inter_subset_left hEv).trans hEvr.le
    have hvr2 : volume.real (E \ Dle) ≤ 2 * π * N := (measureReal_mono Set.diff_subset hEv).trans hEvr.le
    obtain ⟨Q', hQ'⟩ : ∃ Q' : Op (Slot δ₀ (S.T N)), Q' = iota η δ₀ (S.T N) (Qband (S.T N) B) := ⟨_, rfl⟩
    have hQn : ‖opCLM Q'‖ ≤ N := by
      rw [hQ', norm_iota hη hδ₀ hT]
      exact (norm_Qband_le _ B).trans (by exact_mod_cast hB)
    have hm1 : ∀ m₁ m₂, Measurable fun R => iota η δ₀ (S.T N) (S.d.h N R) m₁ m₂ :=
      measurable_iota_entry hT hη hδ₀ (S.d.h_measurable N hN)
    have hm2 : ∀ m₁ m₂, Measurable fun R => hTilde S.d N R ρ m₁ m₂ := hTilde_measurable hη hδ₀ S.d N hN ρ
    have hb1 : ∀ R, ‖opCLM (iota η δ₀ (S.T N) (S.d.h N R))‖ ≤ S.d.Ch := fun R => by
      rw [norm_iota hη hδ₀ hT]
      exact S.d.norm_h_le N hN R
    have hb2 : ∀ R, ‖opCLM (hTilde S.d N R ρ)‖ ≤ S.d.Ch := fun R =>
      (norm_hTilde_le hη hδ₀ S.d N hN R ρ).1.trans (norm_hTilde_le hη hδ₀ S.d N hN R ρ).2
    have hi1 : ∀ F : Set (ℝ × ℝ), volume F ≠ ⊤ → ∀ m₁ m₂, IntegrableOn
        (fun R => (iota η δ₀ (S.T N) (S.d.h N R) * Q' - Q' * iota η δ₀ (S.T N) (S.d.h N R)) m₁ m₂) F :=
      fun F hF => integrableOn_entry_of_bounded hF (measurable_entry_comm hm1 Q') (M := 2 * S.d.Ch * ‖opCLM Q'‖)
        fun R => (norm_comm_le _ _).trans (by gcongr; exact hb1 R)
    have hi2 : ∀ F : Set (ℝ × ℝ), volume F ≠ ⊤ → ∀ m₁ m₂, IntegrableOn
        (fun R => (hTilde S.d N R ρ * Q' - Q' * hTilde S.d N R ρ) m₁ m₂) F :=
      fun F hF => integrableOn_entry_of_bounded hF (measurable_entry_comm hm2 Q') (M := 2 * S.d.Ch * ‖opCLM Q'‖)
        fun R => (norm_comm_le _ _).trans (by gcongr; exact hb2 R)
    have hm12 : ∀ m₁ m₂, Measurable fun R => (iota η δ₀ (S.T N) (S.d.h N R) - hTilde S.d N R ρ) m₁ m₂ :=
      fun m₁ m₂ => by simp only [Matrix.sub_apply]; exact (hm1 m₁ m₂).sub (hm2 m₁ m₂)
    have hi12 : ∀ F : Set (ℝ × ℝ), volume F ≠ ⊤ → ∀ m₁ m₂, IntegrableOn
        (fun R => ((iota η δ₀ (S.T N) (S.d.h N R) - hTilde S.d N R ρ) * Q' -
          Q' * (iota η δ₀ (S.T N) (S.d.h N R) - hTilde S.d N R ρ)) m₁ m₂) F := fun F hF =>
      integrableOn_entry_of_bounded hF (measurable_entry_comm hm12 Q') (M := 2 * (S.d.Ch + S.d.Ch) * ‖opCLM Q'‖)
        fun R => (norm_comm_le _ _).trans (by
          gcongr
          rw [opCLM_sub']
          exact (norm_sub_le _ _).trans (add_le_add (hb1 R) (hb2 R)))
    -- `ι(J) = i ∫_E [ι(h_R), ι(Q)]`
    have hint0 : ∀ m₁ m₂ : Conf (ZMod (S.T N).Nφ), IntegrableOn (fun R => S.d.h N R m₁ m₂) E := fun m₁ m₂ => by
      rw [hE]
      exact (integrableOn_h S.d hN m₁ m₂).mono_set Set.inter_subset_right
    have hιH : iota η δ₀ (S.T N) (S.HDd N D) = opIntegral E fun R => iota η δ₀ (S.T N) (S.d.h N R) := by
      unfold IxSetting.HDd
      rw [← hE]
      exact iota_opIntegral hη hδ₀ hT E (S.d.h N) hint0
    have hιJ : iota η δ₀ (S.T N) (S.curr N D B) = (I : ℂ) • opIntegral E
        (fun R => iota η δ₀ (S.T N) (S.d.h N R) * Q' - Q' * iota η δ₀ (S.T N) (S.d.h N R)) := by
      unfold IxSetting.curr
      rw [iota_smul hη hδ₀ hT, iota_sub' hη hδ₀ hT, iota_mul hη hδ₀ hT, iota_mul hη hδ₀ hT, hιH, ← hQ',
        opIntegral_comm _ _ _ (fun m₁ m₂ => integrableOn_entry_of_bounded hEv hm1 hb1 m₁ m₂)]
    -- the approximant
    obtain ⟨Jρ, hJρ⟩ : ∃ Jρ : Op (Slot δ₀ (S.T N)), Jρ = (I : ℂ) • opIntegral (E ∩ Dle)
        (fun R => hTilde S.d N R ρ * Q' - Q' * hTilde S.d N R ρ) := ⟨_, rfl⟩
    have hJmem : Jρ ∈ Alg (fat Z r) := by
      rw [hJρ]
      refine Alg_smul_mem _ (opIntegral_mem_Alg _ (hEm.inter hDlem) _ (hi2 _ hv1) fun R hR => ?_)
      have hRD : R ∈ D := by
        rw [hE] at hR
        exact hR.1.1
      have hRρ : ξ R ≤ ρ := by
        have h := hR.2
        rw [hDle] at h
        exact h
      rw [hQ']
      refine near_mem_dev hη hδ₀ S hN B R fun s hs => ?_
      rw [← hrρ]
      exact hnear R hRD ρ hρ0 hRρ s hs
    refine ⟨Jρ, hJmem, ?_⟩
    -- the decomposition
    have hsplit := opIntegral_split E Dle hDlem
      (fun R => iota η δ₀ (S.T N) (S.d.h N R) * Q' - Q' * iota η δ₀ (S.T N) (S.d.h N R)) (hi1 E hEv)
    have hadd := opIntegral_add' (E ∩ Dle) (fun R => hTilde S.d N R ρ * Q' - Q' * hTilde S.d N R ρ)
      (fun R => (iota η δ₀ (S.T N) (S.d.h N R) - hTilde S.d N R ρ) * Q' -
        Q' * (iota η δ₀ (S.T N) (S.d.h N R) - hTilde S.d N R ρ)) (hi2 _ hv1) (hi12 _ hv1)
    have hpt : (fun R => hTilde S.d N R ρ * Q' - Q' * hTilde S.d N R ρ +
        ((iota η δ₀ (S.T N) (S.d.h N R) - hTilde S.d N R ρ) * Q' -
          Q' * (iota η δ₀ (S.T N) (S.d.h N R) - hTilde S.d N R ρ))) =
        fun R => iota η δ₀ (S.T N) (S.d.h N R) * Q' - Q' * iota η δ₀ (S.T N) (S.d.h N R) := by
      funext R
      noncomm_ring
    rw [hpt] at hadd
    have hdec : iota η δ₀ (S.T N) (S.curr N D B) - Jρ = (I : ℂ) • (opIntegral (E ∩ Dle)
        (fun R => (iota η δ₀ (S.T N) (S.d.h N R) - hTilde S.d N R ρ) * Q' -
          Q' * (iota η δ₀ (S.T N) (S.d.h N R) - hTilde S.d N R ρ)) +
        opIntegral (E \ Dle)
          (fun R => iota η δ₀ (S.T N) (S.d.h N R) * Q' - Q' * iota η δ₀ (S.T N) (S.d.h N R))) := by
      rw [hιJ, hJρ, ← smul_sub, hsplit, hadd]
      congr 1
      abel
    rw [hdec, opCLM_smul', norm_smul, Complex.norm_I, one_mul, opCLM_add']
    -- the two bounds
    have hT1 : ‖opCLM (opIntegral (E ∩ Dle) (fun R => (iota η δ₀ (S.T N) (S.d.h N R) - hTilde S.d N R ρ) * Q' -
          Q' * (iota η δ₀ (S.T N) (S.d.h N R) - hTilde S.d N R ρ)))‖ ≤
        (2 * (2 * |S.d.CH k| * (1 + ρ) ^ (-(k : ℝ))) * N) * (2 * π * N) := by
      refine (norm_opIntegral_le_const _ hv1.lt_top _ (hi12 _ hv1)
        (M := 2 * (2 * |S.d.CH k| * (1 + ρ) ^ (-(k : ℝ))) * N) fun R _ => ?_).trans
        (mul_le_mul_of_nonneg_left hvr1 (by positivity))
      refine (norm_comm_le _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hQn
        (norm_nonneg _) (by positivity))
      refine (norm_iota_sub_hTilde_le hη hδ₀ S.d N hN R ρ hρ0 k).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)) hρk
    have hT2 : ‖opCLM (opIntegral (E \ Dle)
        (fun R => iota η δ₀ (S.T N) (S.d.h N R) * Q' - Q' * iota η δ₀ (S.T N) (S.d.h N R)))‖ ≤
        ((4 * |S.d.CH k| + 2 * |S.d.Ch|) * N * (1 + 2 * δ₀) ^ k * (1 + ρ) ^ (-(k : ℝ))) * (2 * π * N) := by
      refine (norm_opIntegral_le_const _ hv2.lt_top _ (hi1 _ hv2)
        (M := (4 * |S.d.CH k| + 2 * |S.d.Ch|) * N * (1 + 2 * δ₀) ^ k * (1 + ρ) ^ (-(k : ℝ)))
        fun R hR => ?_).trans (mul_le_mul_of_nonneg_left hvr2 (by positivity))
      have hRD : R ∈ D := by
        rw [hE] at hR
        exact hR.1.1
      have hRρ : ρ < ξ R := by
        have h := hR.2
        rw [hDle] at h
        simp only [Set.mem_setOf_eq, not_le] at h
        exact h
      obtain ⟨B', hB', hfarR⟩ := hfar R hRD
      rw [hQ']
      exact far_comm_le_dev hη hδ₀ S hN hB hB' R hρ0 hRρ hfarR k
    -- `(1 + ρ)^{−k} ≤ (2 + 4δ₀)^k (1 + r)^{−k}`
    have hk := rpow_neg_le_dev (a := 1 + r) (b := 1 + ρ) (c := 2 * (1 + δx δ₀ (S.T N))) (by linarith)
      (by linarith) (by positivity) (by nlinarith [mul_nonneg hδx.le hρ0]) k
    have hpow : (2 * (1 + δx δ₀ (S.T N))) ^ k ≤ (2 + 4 * δ₀) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    have hk' : (1 + ρ) ^ (-(k : ℝ)) ≤ (2 + 4 * δ₀) ^ k * (1 + r) ^ (-(k : ℝ)) :=
      hk.trans (mul_le_mul_of_nonneg_right hpow hr1)
    calc _ ≤ (2 * (2 * |S.d.CH k| * (1 + ρ) ^ (-(k : ℝ))) * N) * (2 * π * N) +
          ((4 * |S.d.CH k| + 2 * |S.d.Ch|) * N * (1 + 2 * δ₀) ^ k * (1 + ρ) ^ (-(k : ℝ))) * (2 * π * N) :=
          (norm_add_le _ _).trans (add_le_add hT1 hT2)
      _ = 2 * π * (4 * |S.d.CH k| + (4 * |S.d.CH k| + 2 * |S.d.Ch|) * (1 + 2 * δ₀) ^ k) * (N : ℝ) ^ 2 *
          (1 + ρ) ^ (-(k : ℝ)) := by ring
      _ ≤ 2 * π * (4 * |S.d.CH k| + (4 * |S.d.CH k| + 2 * |S.d.Ch|) * (1 + 2 * δ₀) ^ k) * (N : ℝ) ^ 2 *
          ((2 + 4 * δ₀) ^ k * (1 + r) ^ (-(k : ℝ))) := mul_le_mul_of_nonneg_left hk' (by positivity)
      _ = 2 * π * (4 * |S.d.CH k| + (4 * |S.d.CH k| + 2 * |S.d.Ch|) * (1 + 2 * δ₀) ^ k) * (2 + 4 * δ₀) ^ k *
          (N : ℝ) ^ 2 * (1 + r) ^ (-(k : ℝ)) := by ring
      _ ≤ Jc_dev δ₀ S.d.Ch S.d.CH k * (N : ℝ) ^ 2 * (1 + r) ^ (-(k : ℝ)) := by
          unfold Jc_dev
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hY0)
            (by positivity)) hr1

end CurrentASDevices

/-- **Lemma 6.6(ii)** and the almost support of **(iii)**: "`$J_\pm\in\AS_{\partial_\pm}$ with prefactor exponent $2$.`" and
"`For $j_0\in\Z$, the same holds, with the same constants, for the band $\Gam+j_0$, the half-tori $\Tor_N^\pm+\kappa j_0\ex$ and the columns $\Col(j_0)$, $\Col(j_0+N)$ in place of $\Gam$, $\Tor_N^\pm$ and $\partial_\pm$.`"
— one set of constants for `J_±` and for every `j₀`, chosen after `δ₀`, `C_h` and the sequence `C^H` and before the
profile, the setting and `N` (the proof: "`with constants depending only on $k$, $C_h$, $C^H_{k+1}$ and $\delta_0$`"; blocks
C–D's quantifier order). -/
theorem J_almostSupported {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (Ch : ℝ) (CH : ℕ → ℝ) :
    ∃ C : ℕ → ℝ, ∀ (η : ℝ → ℝ), IsProfile η → ∀ S : IxSetting η δ₀, S.d.Ch = Ch → S.d.CH = CH →
      ASBound η δ₀ S.Ts S.cutMinus S.Jminus 2 C ∧ ASBound η δ₀ S.Ts S.cutPlus S.Jplus 2 C ∧
      ∀ j₀ : ℤ, ASBound η δ₀ S.Ts (fun N => col δ₀ (S.T N) j₀) (S.JminusShift j₀) 2 C ∧
        ASBound η δ₀ S.Ts (fun N => col δ₀ (S.T N) (j₀ + N)) (S.JplusShift j₀) 2 C := by
  refine ⟨Jc_dev δ₀ Ch CH, fun η hη S hCh hCH => ?_⟩
  have hcont : ∀ (L c : ℝ), Measurable fun R : ℝ × ℝ => pdist L (R.1 - c) := fun L c =>
    ((Metric.continuous_infDist_pt _).comp (continuous_fst.sub continuous_const)).measurable
  have key : ∀ j₀ : ℤ, ASBound η δ₀ S.Ts (fun N => col δ₀ (S.T N) j₀) (S.JminusShift j₀) 2 (Jc_dev δ₀ Ch CH) ∧
      ASBound η δ₀ S.Ts (fun N => col δ₀ (S.T N) (j₀ + N)) (S.JplusShift j₀) 2 (Jc_dev δ₀ Ch CH) := by
    intro j₀
    refine ⟨⟨by norm_num, fun k N hN r hr => ?_⟩, ⟨by norm_num, fun k N hN r hr => ?_⟩⟩
    · have h := curr_approx_dev hη hδ₀ S hN (measurableSet_shiftX_halfMinus_dev _ j₀)
        (volume_half_N_dev S hN j₀).2.2.1 (card_bandShift_le_dev _ N j₀) (Z := col δ₀ (S.T N) j₀)
        (ξ := fun R => pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀)) (hcont _ _)
        (fun R hR => by
          obtain ⟨B', hB', h⟩ := far_band_dev hδ₀ S hN j₀ R
          refine ⟨B', hB', fun s hs => ?_⟩
          have h2 := h s hs
          rwa [min_eq_left ((xi_half_dev S j₀ R).1 hR)] at h2)
        (fun R _ ρ hρ hRρ s hs => near_col_dev hδ₀ (S.Ts.admissible N hN) j₀ hρ hRρ s hs) k hr
      rw [hCh, hCH] at h
      rw [Real.rpow_two]
      exact h
    · have hTN : (S.T N).N = N := S.Ts.T_N N hN
      have h := curr_approx_dev hη hδ₀ S hN (show MeasurableSet (shiftX (S.T N) j₀ (halfPlus (S.T N))) from
          (measurableSet_shiftX_halfMinus_dev _ j₀).compl)
        (volume_half_N_dev S hN j₀).2.2.2 (card_bandShift_le_dev _ N j₀) (Z := col δ₀ (S.T N) (j₀ + N))
        (ξ := fun R => pdist (S.T N).Lx (R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2))
        (((Metric.continuous_infDist_pt _).comp ((continuous_fst.sub continuous_const).sub continuous_const)).measurable)
        (fun R hR => by
          obtain ⟨B', hB', h⟩ := far_band_dev hδ₀ S hN j₀ R
          refine ⟨B', hB', fun s hs => ?_⟩
          have h2 := h s hs
          rwa [min_eq_right ((xi_half_dev S j₀ R).2 hR)] at h2)
        (fun R _ ρ hρ hRρ s hs => by
          have e : R.1 - (S.T N).κ * ((j₀ + N : ℤ) : ℝ) = R.1 - (S.T N).κ * j₀ - (S.T N).Lx / 2 := by
            rw [Lx_eq_two_κN_dev, hTN]
            push_cast
            ring
          have hR' : pdist (S.T N).Lx (R.1 - (S.T N).κ * ((j₀ + N : ℤ) : ℝ)) ≤ ρ := by
            rw [e]
            exact hRρ
          exact near_col_dev hδ₀ (S.Ts.admissible N hN) (j₀ + N) hρ hR' s hs) k hr
      rw [hCh, hCH] at h
      rw [Real.rpow_two]
      exact h
  have hsh : ∀ (T : Torus) (D : Set (ℝ × ℝ)), shiftX T 0 D = D := fun T D => by
    ext R
    simp [shiftX, Prod.mk_zero_zero]
  have hb0 : ∀ Nφ N : ℕ, bandShift Nφ N 0 = bandΓ Nφ N := fun Nφ N => by
    simp [bandShift]
  obtain ⟨h0m, h0p⟩ := key 0
  have hJm : ∀ N ∈ S.Ts.idx, S.JminusShift 0 N = S.Jminus N := fun N _ => by
    unfold IxSetting.JminusShift IxSetting.Jminus
    rw [hsh, hb0]
  have hJp : ∀ N ∈ S.Ts.idx, S.JplusShift 0 N = S.Jplus N := fun N _ => by
    unfold IxSetting.JplusShift IxSetting.Jplus
    rw [hsh, hb0]
  refine ⟨asBound_congr h0m hJm, ?_, key⟩
  have h := asBound_congr h0p hJp
  simp only [zero_add] at h
  exact h

/-- **Lemma 6.6(iii)**, the clauses of (i) for the translated currents: the split, self-adjointness, sector preservation
and the norm bound "`$\norm{J_\pm}\le4\pi C_hN^2$`". -/
theorem JShift_props (S : IxSetting η δ₀) :
    ∀ j₀ : ℤ, ∀ N ∈ S.Ts.idx,
      S.JminusShift j₀ N + S.JplusShift j₀ N =
          (I : ℂ) • (S.H N * Qband (S.T N) (bandShift (S.T N).Nφ N j₀) -
            Qband (S.T N) (bandShift (S.T N).Nφ N j₀) * S.H N) ∧
        IsSelfAdjoint (S.JminusShift j₀ N) ∧ IsSectorPreserving (S.T N) (S.JminusShift j₀ N) ∧
        IsSelfAdjoint (S.JplusShift j₀ N) ∧ IsSectorPreserving (S.T N) (S.JplusShift j₀ N) ∧
        ‖toCLM (S.T N) (S.JminusShift j₀ N)‖ ≤ 4 * π * S.d.Ch * (N : ℝ) ^ 2 ∧
        ‖toCLM (S.T N) (S.JplusShift j₀ N)‖ ≤ 4 * π * S.d.Ch * (N : ℝ) ^ 2 := by
  intro j₀ N hN
  obtain ⟨-, -, hv3, hv4⟩ := volume_half_N_dev S hN j₀
  obtain ⟨h1, h2⟩ := curr_isSelfAdjoint_dev S hN (shiftX (S.T N) j₀ (halfMinus (S.T N)))
    (bandShift (S.T N).Nφ N j₀)
  obtain ⟨h3, h4⟩ := curr_isSelfAdjoint_dev S hN (shiftX (S.T N) j₀ (halfPlus (S.T N)))
    (bandShift (S.T N).Nφ N j₀)
  refine ⟨?_, h1, h2, h3, h4, norm_curr_le_dev S hN _ hv3 _ (card_bandShift_le_dev _ _ _),
    norm_curr_le_dev S hN _ hv4 _ (card_bandShift_le_dev _ _ _)⟩
  unfold IxSetting.JminusShift IxSetting.JplusShift
  rw [shiftX_halfPlus_dev]
  exact curr_add_compl_dev S hN (measurableSet_shiftX_halfMinus_dev _ _) _

/-! ### Lemma 6.7 (the in-sector identity) -/

/-! #### Proof device for Lemma 6.7 (phase (b), round one; not a statement of the paper)

The core's `Setting` of the data at `N ∈ 𝒩` with the transport unitary `U = 1`, `T_± = 0` (Lemma 6.7 and the core's
`lie_K_P` do not use the transport) and `g` the step `1_{(−∞, −γ]}` (the core's two properties of `g`), so that the core's
`lie_K_P` and `commute_Qbar_P` apply without (H2) and without Definition 5.8's `ζ`. -/

section CoreDevices

theorem What_eq_dev {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) {γ : ℝ} (hγ : 0 < γ) (ω : ℝ) (hω : γ ≤ |ω|) :
    What ϑ γ ω = I / ω :=
  (integral_Wfilt_mul_exp_of_le hϑ hγ hω).2

theorem What_conj_dev {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) (γ ω : ℝ) : What ϑ γ (-ω) = conj (What ϑ γ ω) := by
  rw [What_neg hϑ, ← star_What_dev]
  exact (starRingEnd_apply _).symm

theorem Q_eq_add_dev (S : IxSetting η δ₀) {N : ℕ} (hN : N ∈ S.Ts.idx) :
    S.Q N = S.Qminus N + S.Qmid N + S.Qplus N := by
  have hle : N ≤ (S.T N).Nφ := by
    show N ≤ 2 * (S.Ts.T N).N
    rw [S.Ts.T_N N hN]
    omega
  obtain ⟨h1, h2, h3, h4⟩ := IndexCore.quarters_partition hle
  unfold IxSetting.Q IxSetting.Qminus IxSetting.Qmid IxSetting.Qplus
  rw [← h4, ← Qband_add _ (Finset.disjoint_union_left.mpr ⟨h2, h3⟩), ← Qband_add _ h1]

theorem exp_toCLM_Qband_dev (T : Torus) (B : Finset (ZMod T.Nφ)) :
    NormedSpace.exp ((2 * π * I : ℂ) • toCLM T (Qband T B)) = 1 := by
  rw [← toCLM_smul_dev, ← toCLM_exp_dev, exp_Qband, toCLM_one_dev]

theorem commute_Psec_toCLM_dev {T : Torus} (nn : SectorLabel T) {A : FockOp T} (hA : IsSectorPreserving T A) :
    Commute (toCLM T (Psec T nn)) (toCLM T A) :=
  commute_toCLM_dev ((isSectorPreserving_iff_commute T A).mp hA nn).symm

/-- The core's `Setting` of the data at `N` (the section docstring). -/
def coreSetting_dev (D : ArgData η δ₀) (hA : GapAssumption D.toIxSetting D.nn D.p D.Δ D.γ) (hϑ : IsCutoff D.ϑ)
    {N : ℕ} (hN : N ∈ D.Ts.idx) : IndexCore.Setting (FockSpace (D.T N)) where
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
  Δ_nonneg := hA.Δ_nonneg
  Δ_lt_γ := by linarith [hA.Δ_nonneg, hA.two_mul_Δ_lt]
  width := hA.spread N hN
  gap := fun μ v hv0 hv hHv => gap_of_secEig (D.d.H_isSelfAdjoint N hN) (H_isSectorPreserving_dev D.toIxSetting hN)
    (by linarith [hA.Δ_nonneg, hA.two_mul_Δ_lt]) (hA.gap N hN) μ v hv0 hv hHv
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
  W_eq := fun ω hω => What_eq_dev hϑ (by linarith [hA.Δ_nonneg, hA.two_mul_Δ_lt]) ω hω
  W_conj := fun ω => What_conj_dev hϑ D.γ ω
  g := fun ω => if ω ≤ -D.γ then 1 else 0
  g_zero := fun ω hω => if_neg (by linarith [hA.Δ_nonneg, hA.two_mul_Δ_lt])
  g_one := fun ω hω => if_pos hω

end CoreDevices

/-- **Lemma 6.7**: "`In Setting~\ref{set:index}, under Assumption~\ref{ass:gap}, $[K,P]=[Q,P]$. Hence $[\Qb,P]=0$ exactly.`"
— with `K`, `Q̄` for the cutoff `ϑ` and the gap `γ` of the assumption. -/
theorem K_comm_P (D : ArgData η δ₀) (hA : GapAssumption D.toIxSetting D.nn D.p D.Δ D.γ) (hϑ : IsCutoff D.ϑ) :
    ∀ N ∈ D.Ts.idx,
      D.Kfull D.ϑ D.γ N * D.P N - D.P N * D.Kfull D.ϑ D.γ N = D.Q N * D.P N - D.P N * D.Q N ∧
        Commute (D.Qbar D.ϑ D.γ N) (D.P N) := by
  intro N hN
  let CS := coreSetting_dev D hA hϑ hN
  have hγ : 0 < D.γ := by linarith [hA.Δ_nonneg, hA.two_mul_Δ_lt]
  have hH := D.d.H_isSelfAdjoint N hN
  have hKm : CS.Kminus = toCLM (D.T N) (D.Kminus D.ϑ D.γ N) := by
    unfold IxSetting.Kminus
    rw [dress_eq_dev hϑ hγ hH, toCLM_spectralSum_dev hH (isSelfAdjoint_toCLM_dev hH)]
    rfl
  have hKp : CS.Kplus = toCLM (D.T N) (D.Kplus D.ϑ D.γ N) := by
    unfold IxSetting.Kplus
    rw [dress_eq_dev hϑ hγ hH, toCLM_spectralSum_dev hH (isSelfAdjoint_toCLM_dev hH)]
    rfl
  have hP : CS.P = toCLM (D.T N) (D.P N) := by
    unfold ArgData.P
    rw [toCLM_mul', toCLM_cfc_indicator hH (isSelfAdjoint_toCLM_dev hH)]
    rfl
  have hQ : CS.Q = toCLM (D.T N) (D.Q N) := by
    rw [Q_eq_add_dev D.toIxSetting hN, toCLM_add_dev, toCLM_add_dev]
    rfl
  have hKf := Kfull_eq_add hϑ hγ D.toIxSetting N hN
  have hlie := CS.lie_K_P
  rw [hKm, hKp, hP, hQ, ← toCLM_add_dev, ← hKf.1, Ring.lie_def, Ring.lie_def] at hlie
  simp only [← toCLM_mul', ← toCLM_sub'] at hlie
  refine ⟨toCLM_injective_dev _ hlie, ?_⟩
  have hQb : CS.Qbar = toCLM (D.T N) (D.Qbar D.ϑ D.γ N) := by
    show CS.Q - CS.Kminus - CS.Kplus = _
    rw [hQ, hKm, hKp]
    unfold IxSetting.Qbar
    rw [toCLM_sub', toCLM_sub']
  have hc := CS.commute_Qbar_P
  rw [hQb, hP] at hc
  exact commute_of_toCLM_dev hc

/-! ### Lemma 6.8 (strip localization of the dressing) -/

/-! #### Proof device for Lemma 6.8's norm bound (phase (b), round two; not a statement of the paper)

`‖∫ W_γ(t) τ_t(J) dt‖ ≤ ∫ |W_γ(t)| ‖τ_t(J)‖ dt = M_0(W_γ) ‖J‖` (block D's `norm_opIntegralOn_le`, `norm_dyn`). -/

theorem norm_dress_le_dev {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) {γ : ℝ} (hγ : 0 < γ) {T : Torus} {H : FockOp T}
    (hH : IsSelfAdjoint H) (J : FockOp T) :
    ‖toCLM T (dress ϑ γ H J)‖ ≤ moment (Wfilt ϑ γ) 0 * ‖toCLM T J‖ := by
  have hWi := (hasFiniteMoments_Wfilt hϑ hγ).1
  have hτc : Continuous fun t => opCLM (dyn H t J) := continuous_opCLM_dyn _ _
  have hτn : ∀ t, ‖opCLM (dyn H t J)‖ ≤ ‖opCLM J‖ := fun t => le_of_eq (norm_dyn hH t J)
  have hint : ∀ m m', MeasureTheory.IntegrableOn (fun t => (Wfilt ϑ γ t • dyn H t J) m m') Set.univ :=
    fun m m' => integrable_entry_smul hWi hτc hτn _ m m'
  have e : ∀ t, ‖opCLM (Wfilt ϑ γ t • dyn H t J)‖ = ‖Wfilt ϑ γ t‖ * ‖opCLM J‖ := by
    intro t
    rw [opCLM_smul', norm_smul, norm_dyn hH]
  unfold dress
  rw [toCLM_eq_opCLM]
  refine (norm_opIntegralOn_le _ _ hint).trans (le_of_eq ?_)
  simp_rw [e]
  rw [MeasureTheory.Measure.restrict_univ, MeasureTheory.integral_mul_const]
  unfold moment
  simp only [Real.rpow_zero, one_mul]

/-- **Lemma 6.8**: "`$\norm{K_\pm}\le\norm{\Wg}_1\norm{J_\pm}$`" (`‖W_γ‖₁ = M_0(W_γ)`, block D's `moment`). -/
theorem norm_K_le {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) {γ : ℝ} (hγ : 0 < γ) (S : IxSetting η δ₀) :
    ∀ N ∈ S.Ts.idx,
      ‖toCLM (S.T N) (S.Kminus ϑ γ N)‖ ≤ moment (Wfilt ϑ γ) 0 * ‖toCLM (S.T N) (S.Jminus N)‖ ∧
        ‖toCLM (S.T N) (S.Kplus ϑ γ N)‖ ≤ moment (Wfilt ϑ γ) 0 * ‖toCLM (S.T N) (S.Jplus N)‖ :=
  fun N hN => ⟨norm_dress_le_dev hϑ hγ (S.d.H_isSelfAdjoint N hN) _,
    norm_dress_le_dev hϑ hγ (S.d.H_isSelfAdjoint N hN) _⟩

/-- **Lemma 6.8**: "`In Setting~\ref{set:index}, $K_\pm\in\AS_{\partial_\pm}$ with prefactor exponent $5/2$`" and "`The same holds for the dressings of the translated currents of Lemma~\ref{lem:split}(iii), with $\Col(j_0)$, $\Col(j_0+N)$ in place of $\partial_\pm$.`"
— one set of constants for `K_±` and for every `j₀`, chosen after `δ₀`, the cutoff `ϑ`, `γ`, `C_h`, `C^H` and `c_*` and
before the profile, the setting and `N` (the proof: "`with constants depending only on $k$, on $\gamma$ (through $\Wg$), on $C_h$ and the constants of $J_-$, on the constants $C_{\rm lc}$, $C_{k+1}$ of Theorem~\ref{thm:propagation}(c), on $\delta_0$ and on $c_*$`"). -/
theorem K_almostSupported {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) {γ : ℝ} (hγ : 0 < γ) (Ch : ℝ)
    (CH : ℕ → ℝ) (cstar : ℝ) :
    ∃ C : ℕ → ℝ, ∀ (η : ℝ → ℝ), IsProfile η → ∀ S : IxSetting η δ₀, S.d.Ch = Ch → S.d.CH = CH →
      S.cstar = cstar →
      ASBound η δ₀ S.Ts S.cutMinus (S.Kminus ϑ γ) (5 / 2) C ∧ ASBound η δ₀ S.Ts S.cutPlus (S.Kplus ϑ γ) (5 / 2) C ∧
      ∀ j₀ : ℤ,
        ASBound η δ₀ S.Ts (fun N => col δ₀ (S.T N) j₀) (fun N => dress ϑ γ (S.H N) (S.JminusShift j₀ N)) (5 / 2) C ∧
          ASBound η δ₀ S.Ts (fun N => col δ₀ (S.T N) (j₀ + N))
            (fun N => dress ϑ γ (S.H N) (S.JplusShift j₀ N)) (5 / 2) C := by
  obtain ⟨CJ, hCJ⟩ := J_almostSupported hδ₀ Ch CH
  obtain ⟨C', hC'⟩ := almostSupported_timeFilter hδ₀ (hasFiniteMoments_Wfilt hϑ hγ)
    (4 * π * |Ch| + (4 * δ₀ / π + 1 / 2) * (4 * π / cstar)) 2 2 (1 / 2) (by norm_num) CJ Ch CH
  refine ⟨C', fun η hη S hCh hCH hcs => ?_⟩
  obtain ⟨hJm, hJp, hJs⟩ := hCJ η hη S hCh hCH
  have hc := S.cstar_pos
  have he : max (2 : ℝ) 2 + 1 / 2 = 5 / 2 := by norm_num
  have hc0 : 0 ≤ (4 * δ₀ / π + 1 / 2) * (4 * π / cstar) := by
    rw [← hcs]
    positivity
  have hnorm : ∀ A : (N : ℕ) → FockOp (S.T N),
      (∀ N ∈ S.Ts.idx, ‖toCLM (S.T N) (A N)‖ ≤ 4 * π * S.d.Ch * (N : ℝ) ^ 2) →
      ∀ N ∈ S.Ts.idx, ‖toCLM (S.Ts.T N) (A N)‖ ≤
        (4 * π * |Ch| + (4 * δ₀ / π + 1 / 2) * (4 * π / cstar)) * (N : ℝ) ^ (2 : ℝ) := by
    intro A hA N hN
    rw [Real.rpow_two]
    refine (hA N hN).trans ?_
    have h2 : 4 * π * S.d.Ch ≤ 4 * π * |Ch| + (4 * δ₀ / π + 1 / 2) * (4 * π / cstar) := by
      rw [hCh]
      have := le_abs_self Ch
      nlinarith [Real.pi_pos]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hcard : ∀ j : ℤ, ∀ N ∈ S.Ts.idx, ((col δ₀ (S.Ts.T N) j).card : ℝ) ≤
      (4 * π * |Ch| + (4 * δ₀ / π + 1 / 2) * (4 * π / cstar)) * (N : ℝ) ^ (1 / 2 : ℝ) := by
    intro j N hN
    have hT := S.Ts.admissible N hN
    have hTN : (S.T N).N = N := S.Ts.T_N N hN
    obtain ⟨-, -, h3, h4⟩ := card_cut_le hδ₀ hT hc (by rw [hTN]; exact S.Lx_ge N hN)
    obtain ⟨W, hW, hcolW⟩ := col_windows hδ₀ hT j
    have h5 : (col δ₀ (S.T N) j).card ≤ 2 * ny δ₀ (S.T N) := by
      rw [hcolW, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      exact Nat.mul_le_mul_right _ hW
    have h6 : ((col δ₀ (S.T N) j).card : ℝ) ≤ 2 * ny δ₀ (S.T N) := by exact_mod_cast h5
    rw [hTN, hcs] at h4
    rw [← Real.sqrt_eq_rpow]
    have h7 : (4 * δ₀ / π + 1 / 2) * (S.T N).Ly ≤ (4 * δ₀ / π + 1 / 2) * (4 * π / cstar * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h8 : 0 ≤ 4 * π * |Ch| * Real.sqrt N := by positivity
    calc ((col δ₀ (S.Ts.T N) j).card : ℝ) ≤ 2 * ny δ₀ (S.T N) := h6
      _ ≤ (4 * δ₀ / π + 1 / 2) * (S.T N).Ly := h3
      _ ≤ (4 * δ₀ / π + 1 / 2) * (4 * π / cstar * Real.sqrt N) := h7
      _ ≤ (4 * π * |Ch| + (4 * δ₀ / π + 1 / 2) * (4 * π / cstar)) * Real.sqrt N := by nlinarith
  have hJn := norm_J_le S
  have hJsn := JShift_props S
  have hJe := J_isSelfAdjoint S
  refine ⟨?_, ?_, fun j₀ => ⟨?_, ?_⟩⟩
  · have h := hC' η hη S.Ts S.H S.d hCh hCH S.cutMinus S.Jminus (fun N hN => (hJe N hN).2.1.isEven) hJm
      (hnorm _ fun N hN => (hJn N hN).1) (hcard 0)
    rw [he] at h
    exact h
  · have h := hC' η hη S.Ts S.H S.d hCh hCH S.cutPlus S.Jplus (fun N hN => (hJe N hN).2.2.2.isEven) hJp
      (hnorm _ fun N hN => (hJn N hN).2) (fun N hN => hcard N N hN)
    rw [he] at h
    exact h
  · have h := hC' η hη S.Ts S.H S.d hCh hCH _ (S.JminusShift j₀)
      (fun N hN => (hJsn j₀ N hN).2.2.1.isEven) (hJs j₀).1
      (hnorm _ fun N hN => (hJsn j₀ N hN).2.2.2.2.2.1) (hcard j₀)
    rw [he] at h
    exact h
  · have h := hC' η hη S.Ts S.H S.d hCh hCH _ (S.JplusShift j₀)
      (fun N hN => (hJsn j₀ N hN).2.2.2.2.1.isEven) (hJs j₀).2
      (hnorm _ fun N hN => (hJsn j₀ N hN).2.2.2.2.2.2) (fun N hN => hcard (j₀ + N) N hN)
    rw [he] at h
    exact h

/-- **Lemma 6.8** for the translated currents: the norm bound "`$\norm{K_\pm}\le\norm{\Wg}_1\norm{J_\pm}$`". -/
theorem norm_KShift_le {ϑ : ℝ → ℝ} (hϑ : IsCutoff ϑ) {γ : ℝ} (hγ : 0 < γ) (S : IxSetting η δ₀) (j₀ : ℤ) :
    ∀ N ∈ S.Ts.idx,
      ‖toCLM (S.T N) (dress ϑ γ (S.H N) (S.JminusShift j₀ N))‖ ≤
          moment (Wfilt ϑ γ) 0 * ‖toCLM (S.T N) (S.JminusShift j₀ N)‖ ∧
        ‖toCLM (S.T N) (dress ϑ γ (S.H N) (S.JplusShift j₀ N))‖ ≤
          moment (Wfilt ϑ γ) 0 * ‖toCLM (S.T N) (S.JplusShift j₀ N)‖ :=
  fun N hN => ⟨norm_dress_le_dev hϑ hγ (S.d.H_isSelfAdjoint N hN) _,
    norm_dress_le_dev hϑ hγ (S.d.H_isSelfAdjoint N hN) _⟩

end HRTorus.Assembly

end -- noncomputable section
