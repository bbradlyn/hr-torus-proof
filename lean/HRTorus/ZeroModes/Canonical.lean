import HRTorus.ZeroModes.Theta
import HRTorus.Hamiltonian.LocalForm
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# The dictionary: canonical components, the pair operators, Lemma C.A3 and Lemma C.A (2) ⇒ (3) (T-0056 stage F, block F1-lower, `ZeroModes.Canonical`)

Written by Claude Opus 5.5 (an AI model; recruit L16), 2026-10-26. **The definitions and statements were written first
and reviewed against the paper (the statement phase). The proof phase is complete: every reviewed statement of this
module is proved (proof phase round one), no theorem of this module is `sorry`, and the proof devices are
marked as such, in their own sections.**
The paper: the HR paper, `papers/hr/appendices/C-kernel.tex` — the first two paragraphs (the coordinates, the
orbitals, the identification of the appendix's `H` with `H_N`), `kz:sec:lll` (the orbitals), `kz:sec:many` (canonical
components), `kz:eq:Bn` (the orbital pair operators), Lemma C.`A3` (`kz:lem:A3`) and Lemma C.`A` (`kz:lem:A`) in the
direction (2) ⇒ (3) only. Not here (not formalized, by the brief): the image-sum `𝒫`, Lemmas C.`A1`, C.`A2`, C.`A4` —
the Lean's `H_N` is Definition 2.7's and block C's `localForm_c` is its orbital form.

## The model

* **The torus** is block A's rectangular `Torus` with "`take $L_1:=L_y$ and $\tau:=\iu L_x/L_y$`" (`tauT T ∈ ℍ`); the
  appendix's `L = N_φ = 2N` is `T.Nφ`, its `κ = 2π/L_1` is `T.κ`. All functions are in the appendix's `u`-units,
  `u = z/L_1`.
* **The orbitals** are obtained from block A's `ψ_j` (`SlotFrame.psi`) by "`The rotation $(x,y)\mapsto(X,Y):=(y,-x)$ maps $\R^2/(L_x\Z\times L_y\Z)$ onto $\C/\Lambda$`"
  and the Gaussian factor: `orbHol T j u := e^{Y²/2} ψ_j(−Y, X)` with `X + iY = L_y u` — "`the function $\psi(X,Y):=f(-Y,X)$`",
  of which "`$e^{Y^2/2}\psi$ is an entire function of $z$ for every $f\in\hN$`". So `orbHol T j` is the holomorphic part
  of the appendix's **normalized** orbital, `(L_y√π)^{−1/2} φ_j` (`orbHol_eq_theta`); the paper's formula for canonical
  components uses the unnormalized `φ_j`, which changes every component of a sector by the same nonzero constant
  `(L_y√π)^{N/2}` (immaterial for every statement here, as is the sign `s_{n,m}`).
* **Spin components.** For a spin assignment `σ : Fin N → Spin` the component `comp T σ Ψ` (the holomorphic part of
  `Ψ(·; σ)`) is the explicit finite sum `Σ_J ⟨c†_{J₀σ₀} ⋯ c†_{J_{N−1}σ_{N−1}} Ω, Ψ⟩ ∏_i orbHol_{J_i}(u_i)` over all orbital
  tuples `J`, with block A's `c_{jσ}` (`cjs`), so that the Jordan–Wigner signs are those of the CAR and no ordering of
  the orbitals is needed; for a basis state it is the product of two Slater determinants (`canon_creVec`), which is the
  paper's formula with `s_{n,m} = 1`. **The canonical component** of a vector of the sector `(n, m)` is `canon T n m`,
  the component for "`up block first`": `σ_i = ↑` for `i < n`, `↓` for `i ≥ n`; its variables are `u = (x, y)` with
  `x_a = u_a` (`a < n`) and `y_k = u_{n+k}`.
* **The pair operators** `B_n^{σσ'}` of `kz:eq:Bn` are `Bpair T σ σ' n` (a `tsum` over `A ∈ ℤ`, `B = n − A`, in the
  topology of the operators, as block C's `bcen`), with `q^{d²} = e^{iπτd²/(2L)}` (`qw`).
* **(C1), (C2)** are conditions on functions in the Osgood class (`IsOsgood`, continuous and separately entire):
  `D_{st} = ∂_s − ∂_t` is the difference of the one-variable derivatives of the slices (`relDeriv`); "vanishes to order
  `≥ 3` along `{u_s − u_t ∈ Λ_u}`" is measured along the transverse coordinate `u_s` (`VanishesAlong`: the slice
  `z ↦ F(u with u_s := z)` and its first two derivatives vanish at every `u_t + λ`, `λ ∈ Λ_u`).
* **Surjectivity of the dictionary.** The brief lists the injectivity of `Ψ ↦ F`; the lower bound also needs the
  converse inclusion — an antisymmetric function in the Osgood class with each variable in the holomorphic class of `𝓛`
  is the canonical component of a vector of the sector (`canon_surj`) — because the explicit states are functions, and
  they must be shown to be canonical components of vectors (the paper uses it silently: a canonical component is
  defined by these properties). It rests on the orbitals paragraph, "`$\phi_0,\dots,\phi_{L-1}$ is an orthogonal basis of the holomorphic parts of $\kzL$`"
  (`span_orbHol`, from Lemma C.theta(a) at `ℓ = L`).
-/

open Complex
open scoped Real UpperHalfPlane InnerProductSpace Matrix

noncomputable section

namespace HRTorus.ZeroModes

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op)

/-! ## The coordinates and the orbitals -/

theorem tauT_im_pos (T : Torus) : 0 < (((T.Lx / T.Ly : ℝ) : ℂ) * I).im := by
  rw [Complex.mul_I_im, Complex.ofReal_re]
  exact div_pos T.Lx_pos T.Ly_pos

/-- The appendix's modular parameter of the torus of Definition 2.1: "`take $L_1:=L_y$ and $\tau:=\iu L_x/L_y$`". -/
def tauT (T : Torus) : ℍ := ⟨((T.Lx / T.Ly : ℝ) : ℂ) * I, tauT_im_pos T⟩

/-- The normalization `(L_y√π)^{−1/2}` of the orbitals (block A's prefactor of `φ_n`). -/
def cT (T : Torus) : ℝ := (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ))

/-- The holomorphic part of the rotated orbital, in `u`-units: "`the function $\psi(X,Y):=f(-Y,X)$`" for `f = ψ_j`, times
`e^{Y²/2}`, at `X + iY = L_y u`. -/
def orbHol (T : Torus) (j : ZMod T.Nφ) (u : ℂ) : ℂ :=
  (Real.exp ((((T.Ly : ℂ) * u).im) ^ 2 / 2) : ℂ) * psi T j (-((T.Ly : ℂ) * u).im, ((T.Ly : ℂ) * u).re)

/-! ### Proof devices for the orbitals (proof phase, round one; not statements of the paper)

`orbHol T j u = c_T Θ_j(i L_y u)` with block A's entire factor `Θ_j = psiTheta` of `ψ_j(x, y) = c_T e^{−x²/2} Θ_j(x + iy)`
(`psi_eq_theta`), and the series of `Θ_j` is the theta series of `ϑ[j/L, 0](Lu | Lτ)` term by term, by `κL_y = 2π` and
`L_xL_y = 2πN_φ`. -/

theorem NtauT_im_pos_dev (T : Torus) : 0 < ((T.Nφ : ℂ) * (tauT T : ℂ)).im := by
  rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  exact mul_pos (by exact_mod_cast T.Nφ_pos) (tauT T).coe_im_pos

theorem orbHol_eq_psiTheta_dev (T : Torus) (j : ZMod T.Nφ) (u : ℂ) :
    orbHol T j u = (cT T : ℂ) * psiTheta T j (I * ((T.Ly : ℂ) * u)) := by
  unfold orbHol
  rw [psi_eq_theta]
  have hz : (((-((T.Ly : ℂ) * u).im : ℝ) : ℂ) + I * ((((T.Ly : ℂ) * u).re : ℝ) : ℂ)) = I * ((T.Ly : ℂ) * u) := by
    apply Complex.ext <;> simp
  have hr : Real.exp ((((T.Ly : ℂ) * u).im) ^ 2 / 2) * Real.exp (-((-((T.Ly : ℂ) * u).im) ^ 2) / 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  rw [hz]
  calc (Real.exp ((((T.Ly : ℂ) * u).im) ^ 2 / 2) : ℂ) *
        ((((T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) * Real.exp (-((-((T.Ly : ℂ) * u).im) ^ 2) / 2) : ℝ) : ℂ) *
          psiTheta T j (I * ((T.Ly : ℂ) * u)))
      = ((Real.exp ((((T.Ly : ℂ) * u).im) ^ 2 / 2) * Real.exp (-((-((T.Ly : ℂ) * u).im) ^ 2) / 2) *
          (T.Ly * Real.sqrt π) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * psiTheta T j (I * ((T.Ly : ℂ) * u)) := by
        push_cast; ring
    _ = (cT T : ℂ) * psiTheta T j (I * ((T.Ly : ℂ) * u)) := by
        rw [hr, one_mul]; rfl

theorem psiTheta_eq_thetaChar_dev (T : Torus) (j : ZMod T.Nφ) (u : ℂ) :
    psiTheta T j (I * ((T.Ly : ℂ) * u)) =
      thetaChar ((j.val : ℝ) / T.Nφ) 0 ((T.Nφ : ℂ) * u) ((T.Nφ : ℂ) * (tauT T : ℂ)) := by
  have hs := hasSum_thetaChar ((j.val : ℝ) / T.Nφ) 0 ((T.Nφ : ℂ) * u) ⟨_, NtauT_im_pos_dev T⟩
  rw [← hs.tsum_eq]
  unfold psiTheta
  refine tsum_congr fun m => ?_
  congr 1
  have hNφ : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
  have hLy : (T.Ly : ℂ) ≠ 0 := by exact_mod_cast T.Ly_pos.ne'
  have harea : (T.Lx : ℂ) = 2 * π * T.Nφ / T.Ly := by
    have h := T.area
    have h2 : ((2 * T.N : ℕ) : ℝ) = (T.Nφ : ℝ) := rfl
    rw [h2] at h
    rw [eq_div_iff hLy]
    exact_mod_cast h
  show ((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) * (I * ((T.Ly : ℂ) * u)) -
      (((T.κ * (((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ)) ^ 2 / 2 : ℝ) : ℂ) =
    π * I * ((T.Nφ : ℂ) * (((T.Lx / T.Ly : ℝ) : ℂ) * I)) * ((m : ℂ) + (((j.val : ℝ) / T.Nφ : ℝ) : ℂ)) ^ 2 +
      2 * π * I * ((m : ℂ) + (((j.val : ℝ) / T.Nφ : ℝ) : ℂ)) * ((T.Nφ : ℂ) * u + ((0 : ℝ) : ℂ))
  simp only [Torus.κ]
  push_cast
  rw [harea]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The first paragraph of Appendix C: "`Moreover the image of the orbital $\psi_j$ of Lemma~\ref{lem:orbitals} is $(L_y\sqrt\pi)^{-1/2}\sum_{k\in\Z}e^{\iu\kappa(j+kL)X}e^{-(Y+\kappa(j+kL))^2/2}$, which is the normalized orbital $\phi_je^{-Y^2/2}/(L_1\sqrt\pi)^{1/2}$ of \eqref{kz:eq:orbital}`"
— in `u`-units `φ_j(L_1u) = ϑ[j/L, 0](Lu | Lτ)` (`kz:eq:orbital`), so `orbHol T j u = (L_y√π)^{−1/2} ϑ[j/L, 0](Lu | Lτ)`. -/
theorem orbHol_eq_theta (T : Torus) (j : ZMod T.Nφ) (u : ℂ) :
    orbHol T j u = (cT T : ℂ) * thetaChar ((j.val : ℝ) / T.Nφ) 0 ((T.Nφ : ℂ) * u) ((T.Nφ : ℂ) * (tauT T : ℂ)) := by
  rw [orbHol_eq_psiTheta_dev, psiTheta_eq_thetaChar_dev]

/-- The rotation inverted: `ψ_j(x, y) = e^{−x²/2} orbHol_j((y − ix)/L_y)` (`(X, Y) = (y, −x)`). -/
theorem psi_eq_orbHol (T : Torus) (j : ZMod T.Nφ) (x y : ℝ) :
    psi T j (x, y) = (Real.exp (-(x ^ 2) / 2) : ℂ) * orbHol T j (((y : ℂ) - (x : ℂ) * I) / T.Ly) := by
  have hLy : (T.Ly : ℂ) ≠ 0 := by exact_mod_cast T.Ly_pos.ne'
  unfold orbHol
  have hz : (T.Ly : ℂ) * (((y : ℂ) - (x : ℂ) * I) / T.Ly) = (y : ℂ) - (x : ℂ) * I := by
    field_simp
  have him : ((y : ℂ) - (x : ℂ) * I).im = -x := by simp
  have hre : ((y : ℂ) - (x : ℂ) * I).re = y := by simp
  rw [hz, him, hre, neg_neg, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    show -(x ^ 2) / 2 + (-x) ^ 2 / 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul]

/-- "`$e^{Y^2/2}\psi$ is an entire function of $z$ for every $f\in\hN$`" — for the orbitals. -/
theorem orbHol_differentiable (T : Torus) (j : ZMod T.Nφ) : Differentiable ℂ (orbHol T j) := by
  have hfun : orbHol T j = fun u => (cT T : ℂ) *
      thetaChar ((j.val : ℝ) / T.Nφ) 0 ((T.Nφ : ℂ) * u) ((T.Nφ : ℂ) * (tauT T : ℂ)) :=
    funext (orbHol_eq_theta T j)
  rw [hfun]
  have hd := thetaChar_differentiable ((j.val : ℝ) / T.Nφ) 0 ⟨_, NtauT_im_pos_dev T⟩
  exact (differentiable_const _).mul (hd.comp (differentiable_const _ |>.mul differentiable_id))

/-- `kz:sec:lll`: "`Each $\phi_j$ satisfies the two boundary conditions`" of the torus LLL, in `u`-units
`f(u + 1) = f(u)`, `f(u + τ) = e^{−iπL(2u+τ)} f(u)` ("`f(z+L_1\tau)=e^{-i\pi L(2z/L_1+\tau)}f(z)`") — the space
`Θ_L[0,0]`. -/
theorem orbHol_mem (T : Torus) (j : ZMod T.Nφ) : orbHol T j ∈ thetaSpace (tauT T) 0 0 T.Nφ := by
  refine ⟨orbHol_differentiable T j, fun U => ?_, fun U => ?_⟩
  · -- `u ↦ u + 1` is `y ↦ y + L_y`: block A's `psi_add_Ly`
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    unfold orbHol
    have h1 : ((T.Ly : ℂ) * (U + 1)).im = ((T.Ly : ℂ) * U).im := by simp
    have h2 : ((T.Ly : ℂ) * (U + 1)).re = ((T.Ly : ℂ) * U).re + T.Ly := by simp; ring
    rw [h1, h2, psi_add_Ly]
  · -- the theta form and (C.eq:theta-basic)
    rw [orbHol_eq_theta, orbHol_eq_theta,
      show (T.Nφ : ℂ) * (U + (tauT T : ℂ)) = (T.Nφ : ℂ) * U + (T.Nφ : ℂ) * (tauT T : ℂ) by ring, thetaChar_add_tau,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, add_zero,
      show -π * I * ((T.Nφ : ℂ) * (tauT T : ℂ)) - 2 * π * I * ((T.Nφ : ℂ) * U) =
        -π * I * (T.Nφ : ℂ) * (2 * U + (tauT T : ℂ)) by ring]
    ring

/-- `kz:sec:lll`: the orbitals are linearly independent ("`$\phi_0,\dots,\phi_{L-1}$ is an orthogonal basis of the holomorphic parts of $\kzL$`";
from block A's orthonormality `l2inner_psi` through `psi_eq_orbHol`). -/
theorem orbHol_linearIndependent (T : Torus) : LinearIndependent ℂ (orbHol T) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hpt : ∀ R : ℝ × ℝ, toFun T (WithLp.toLp 2 g) R = 0 := by
    rintro ⟨x, y⟩
    have h := congrFun hg (((y : ℂ) - (x : ℂ) * I) / T.Ly)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    simp only [toFun, psi_eq_orbHol T _ x y]
    calc ∑ j, g j * ((Real.exp (-(x ^ 2) / 2) : ℂ) * orbHol T j (((y : ℂ) - (x : ℂ) * I) / T.Ly))
        = (Real.exp (-(x ^ 2) / 2) : ℂ) * ∑ j, g j * orbHol T j (((y : ℂ) - (x : ℂ) * I) / T.Ly) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h, mul_zero]
  have h0 : WithLp.toLp 2 g = (0 : Space T) :=
    toFun_injective T (funext fun R => by rw [hpt R]; simp [toFun])
  have := congrArg (fun f : Space T => f i) h0
  simpa using this

/-- `kz:sec:lll`: "`$\phi_0,\dots,\phi_{L-1}$ is an orthogonal basis of the holomorphic parts of $\kzL$`" — the spanning half
(Lemma C.theta(a) at `ℓ = L`: the space has dimension `L`). -/
theorem span_orbHol (T : Torus) : Submodule.span ℂ (Set.range (orbHol T)) = thetaSpace (tauT T) 0 0 T.Nφ := by
  have hle : Submodule.span ℂ (Set.range (orbHol T)) ≤ thetaSpace (tauT T) 0 0 T.Nφ :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact orbHol_mem T j)
  have hfin : Module.finrank ℂ (thetaSpace (tauT T) 0 0 T.Nφ) = T.Nφ :=
    finrank_thetaSpace (tauT T) 0 0 T.Nφ_pos
  have hspan : Module.finrank ℂ (Submodule.span ℂ (Set.range (orbHol T))) = T.Nφ := by
    rw [finrank_span_eq_card (orbHol_linearIndependent T), ZMod.card]
  have : FiniteDimensional ℂ (thetaSpace (tauT T) 0 0 T.Nφ) :=
    Module.finite_of_finrank_pos (by rw [hfin]; exact T.Nφ_pos)
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan, hfin])

/-! ## Canonical components (`kz:sec:many`) -/

/-- The creation word `c†_{J₀σ₀} c†_{J₁σ₁} ⋯ c†_{J_{N−1}σ_{N−1}}` (block A's `c_{jσ}` = `cjs`). -/
def creWord (T : Torus) {N : ℕ} (σ : Fin N → Spin) (J : Fin N → ZMod T.Nφ) : FockOp T :=
  (List.ofFn fun i => (cjs T (J i) (σ i))ᴴ).prod

/-- The state `c†_{J₀σ₀} ⋯ c†_{J_{N−1}σ_{N−1}} Ω` (`Ω` the vacuum). -/
def creVec (T : Torus) {N : ℕ} (σ : Fin N → Spin) (J : Fin N → ZMod T.Nφ) : FockSpace T :=
  toCLM T (creWord T σ J) (EuclideanSpace.single (vac : Conf (ZMod T.Nφ)) 1)

/-- The amplitude `Ψ ↦ ⟨c†_{J₀σ₀} ⋯ Ω, Ψ⟩` — the paper's coefficient `c_{I,I'}` when `J` lists the occupied orbitals. -/
def amp (T : Torus) {N : ℕ} (σ : Fin N → Spin) (J : Fin N → ZMod T.Nφ) : FockSpace T →L[ℂ] ℂ :=
  innerSL ℂ (creVec T σ J)

/-- The product `u ↦ ∏_i orbHol_{J_i}(u_i)` of orbital functions. -/
def orbProd (T : Torus) {N : ℕ} (J : Fin N → ZMod T.Nφ) : (Fin N → ℂ) → ℂ :=
  fun u => ∏ i, orbHol T (J i) (u i)

/-- **`kz:sec:many`**, the spin component of `Ψ` for the spin assignment `σ` (the holomorphic part of `Ψ(·; σ)`), as the
explicit finite sum `Σ_J ⟨c†_{J₀σ₀} ⋯ Ω, Ψ⟩ ∏_i orbHol_{J_i}(u_i)` (a linear map; `comp_apply`). -/
def comp (T : Torus) {N : ℕ} (σ : Fin N → Spin) : FockSpace T →ₗ[ℂ] ((Fin N → ℂ) → ℂ) :=
  ∑ J : Fin N → ZMod T.Nφ, (amp T σ J : FockSpace T →ₗ[ℂ] ℂ).smulRight (orbProd T J)

/-- The spins of the canonical component: "`up block first`" — `↑` at the first `n` places, `↓` at the last `m`. -/
def canonSpins (n m : ℕ) : Fin (n + m) → Spin := fun i => if (i : ℕ) < n then .up else .dn

/-- **`kz:sec:many`**: "`$\Psi$ is determined by its \emph{canonical component} $F(x_1,\dots,x_n;y_1,\dots,y_m)$ (the holomorphic part of $\Psi(\cdot;\uparrow^n\downarrow^m)$), antisymmetric in the $x$'s and in the $y$'s, each variable in the holomorphic class of $\kzL$; every other spin component is $\pm F$ with permuted arguments.`"
— the canonical component, a function of `u = (x, y) : Fin (n + m) → ℂ`. -/
def canon (T : Torus) (n m : ℕ) : FockSpace T →ₗ[ℂ] ((Fin (n + m) → ℂ) → ℂ) :=
  comp T (canonSpins n m)

/-! ### Proof devices for the canonical components (proof phase, round one; not statements of the paper)

The creators are the values `c†(g) = Σ_μ g_μ c†_μ` of a linear map (`cdagLin_dev`) whose every value squares to zero
(block A's `cdag_mul_self`, the CAR), so by the universal property of Mathlib's `ExteriorAlgebra` (its alternating map
`ιMulti`) a product of creators is multiplied by the sign of a permutation of its factors (`prod_cdagLin_perm_dev`);
a creation vector splits off its first factor (`creVec_cons_dev`); the amplitudes of a vector with the spin content of
`σ` determine it (`eq_zero_of_amp_dev`, by induction on the number of particles with block A's `Nsig_mul_c`); and the
products of orbitals are linearly independent (`orbProd_linearIndependent_dev`, by induction from
`orbHol_linearIndependent`). -/

/-- `g ↦ c†(g) = Σ_μ g_μ c†_μ`. -/
def cdagLin_dev (T : Torus) : (Modes T → ℂ) →ₗ[ℂ] FockOp T :=
  Fintype.linearCombination ℂ fun μ => (Fermion.Pilot.JW.c μ)ᴴ

theorem cdagLin_apply_dev (T : Torus) (g : Modes T → ℂ) : cdagLin_dev T g = (cVec g)ᴴ := by
  rw [cdagLin_dev, Fintype.linearCombination_apply, conjTranspose_cVec]

theorem cdagLin_sq_dev (T : Torus) (g : Modes T → ℂ) : cdagLin_dev T g * cdagLin_dev T g = 0 := by
  rw [cdagLin_apply_dev]
  exact cdag_mul_self g

theorem cjs_conjTranspose_dev (T : Torus) (j : ZMod T.Nφ) (σ : Spin) :
    (cjs T j σ)ᴴ = cdagLin_dev T (Pi.single (j, σ) 1) := by
  rw [cdagLin_apply_dev, cjs_eq, ← cVec_single]
  congr 2
  funext ν
  simp [Pi.single_apply]

theorem creWord_eq_dev (T : Torus) {N : ℕ} (σ : Fin N → Spin) (J : Fin N → ZMod T.Nφ) :
    creWord T σ J = (List.ofFn fun i => cdagLin_dev T (Pi.single (J i, σ i) 1)).prod := by
  unfold creWord
  simp only [cjs_conjTranspose_dev]

theorem prod_cdagLin_perm_dev (T : Torus) {N : ℕ} (v : Fin N → (Modes T → ℂ)) (ρ : Equiv.Perm (Fin N)) :
    (List.ofFn fun i => cdagLin_dev T (v (ρ i))).prod =
      ((Equiv.Perm.sign ρ : ℤ) : ℂ) • (List.ofFn fun i => cdagLin_dev T (v i)).prod := by
  set F := ExteriorAlgebra.lift ℂ ⟨cdagLin_dev T, cdagLin_sq_dev T⟩
  have key : ∀ w : Fin N → (Modes T → ℂ), (List.ofFn fun i => cdagLin_dev T (w i)).prod =
      F (ExteriorAlgebra.ιMulti ℂ N w) := by
    intro w
    rw [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [F, Function.comp_apply, ExteriorAlgebra.lift_ι_apply]
  rw [key, key, show (fun i => v (ρ i)) = v ∘ ρ from rfl, AlternatingMap.map_perm, Units.smul_def, map_zsmul,
    Int.cast_smul_eq_zsmul]

theorem creWord_perm_dev (T : Torus) {N : ℕ} (σ : Fin N → Spin) (J : Fin N → ZMod T.Nφ) (ρ : Equiv.Perm (Fin N)) :
    creWord T (σ ∘ ρ) (J ∘ ρ) = ((Equiv.Perm.sign ρ : ℤ) : ℂ) • creWord T σ J := by
  rw [creWord_eq_dev, creWord_eq_dev]
  exact prod_cdagLin_perm_dev T (fun i => Pi.single (J i, σ i) 1) ρ

theorem creVec_perm_dev (T : Torus) {N : ℕ} (σ : Fin N → Spin) (J : Fin N → ZMod T.Nφ) (ρ : Equiv.Perm (Fin N)) :
    creVec T (σ ∘ ρ) (J ∘ ρ) = ((Equiv.Perm.sign ρ : ℤ) : ℂ) • creVec T σ J := by
  unfold creVec
  rw [creWord_perm_dev]
  simp only [toCLM, map_smul, smul_apply]

theorem creVec_cons_dev (T : Torus) {N : ℕ} (s : Spin) (σ : Fin N → Spin) (j : ZMod T.Nφ) (J : Fin N → ZMod T.Nφ) :
    creVec T (Fin.cons s σ) (Fin.cons j J) = toCLM T (cjs T j s)ᴴ (creVec T σ J) := by
  unfold creVec creWord
  rw [List.ofFn_succ, List.prod_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]
  simp only [toCLM, map_mul, mul_apply_eq_comp]

theorem inner_toCLM_dev (T : Torus) (A : FockOp T) (v w : FockSpace T) :
    ⟪toCLM T A v, w⟫_ℂ = ⟪v, toCLM T Aᴴ w⟫_ℂ := by
  show ⟪Matrix.toEuclideanLin A v, w⟫_ℂ = ⟪v, Matrix.toEuclideanLin Aᴴ w⟫_ℂ
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

theorem amp_cons_dev (T : Torus) {N : ℕ} (s : Spin) (σ : Fin N → Spin) (j : ZMod T.Nφ) (J : Fin N → ZMod T.Nφ)
    (Ψ : FockSpace T) :
    ⟪creVec T (Fin.cons s σ) (Fin.cons j J), Ψ⟫_ℂ = ⟪creVec T σ J, toCLM T (cjs T j s) Ψ⟫_ℂ := by
  rw [creVec_cons_dev, inner_toCLM_dev, Matrix.conjTranspose_conjTranspose]

/-- The number of places of `σ` with spin `τ`. -/
def spinCount_dev {N : ℕ} (σ : Fin N → Spin) (τ : Spin) : ℕ :=
  (Finset.univ.filter fun i => σ i = τ).card

theorem spinCount_cons_dev {N : ℕ} (s : Spin) (σ : Fin N → Spin) (τ : Spin) :
    spinCount_dev (Fin.cons s σ : Fin (N + 1) → Spin) τ = (if s = τ then 1 else 0) + spinCount_dev σ τ := by
  unfold spinCount_dev
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem Nsig_cjs_dev (T : Torus) (τ s : Spin) (j : ZMod T.Nφ) (k : ℂ) {Ψ : FockSpace T}
    (hΨ : toCLM T (Nsig T τ) Ψ = k • Ψ) :
    toCLM T (Nsig T τ) (toCLM T (cjs T j s) Ψ) = (k - if s = τ then 1 else 0) • toCLM T (cjs T j s) Ψ := by
  have h := Nsig_mul_c T τ (j, s)
  rw [← cjs_eq] at h
  have e1 : toCLM T (Nsig T τ) (toCLM T (cjs T j s) Ψ) = toCLM T (Nsig T τ * cjs T j s) Ψ := by
    simp only [toCLM, map_mul, mul_apply_eq_comp]
  rw [e1, h]
  simp only [toCLM] at hΨ ⊢
  simp only [map_mul, mul_apply_eq_comp, map_sub, map_smul, map_one, sub_apply, smul_apply, one_apply_eq_self]
  rw [hΨ, map_smul, sub_smul]

theorem eq_zero_of_amp_dev (T : Torus) :
    ∀ (N : ℕ) (σ : Fin N → Spin) (Ψ : FockSpace T),
      (∀ τ : Spin, toCLM T (Nsig T τ) Ψ = ((spinCount_dev σ τ : ℕ) : ℂ) • Ψ) →
      (∀ J : Fin N → ZMod T.Nφ, ⟪creVec T σ J, Ψ⟫_ℂ = 0) → Ψ = 0 := by
  intro N
  induction N with
  | zero =>
    intro σ Ψ hN hJ
    -- no particle: `Ψ` lives on the vacuum, and its vacuum amplitude vanishes
    have hvac : Ψ vac = 0 := by
      have h := hJ (fun i => i.elim0)
      unfold creVec creWord at h
      simpa [EuclideanSpace.inner_single_left] using h
    have hsec : Ψ ∈ sector T (0, 0) := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        show toCLM T (Nsig T .up) Ψ = _
        have := hN .up
        simpa [spinCount_dev] using this
      · rw [Module.End.mem_eigenspace_iff]
        show toCLM T (Nsig T .dn) Ψ = _
        have := hN .dn
        simpa [spinCount_dev] using this
    ext m
    by_contra hm
    have h0 := (mem_sector_iff T (0, 0) Ψ).1 hsec m hm
    rw [secOf_eq_iff] at h0
    have hmv : m = vac := by
      funext μ
      obtain ⟨j, s⟩ := μ
      by_contra hne
      have hne' : m (j, s) = true := by simpa [vac] using hne
      cases s
      · have := h0.1
        rw [Fin.val_zero, ctσ, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
        exact this (Finset.mem_univ j) hne'
      · have := h0.2
        rw [Fin.val_zero, ctσ, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
        exact this (Finset.mem_univ j) hne'
    exact hm (by rw [hmv]; exact hvac)
  | succ N ih =>
    intro σ Ψ hN hJ
    have hσ : σ = Fin.cons (σ 0) (Fin.tail σ) := (Fin.cons_self_tail σ).symm
    -- every `c_{j σ₀} Ψ` vanishes, by induction
    have hc : ∀ j : ZMod T.Nφ, toCLM T (cjs T j (σ 0)) Ψ = 0 := by
      intro j
      refine ih (Fin.tail σ) _ (fun τ => ?_) (fun J => ?_)
      · rw [Nsig_cjs_dev T τ (σ 0) j _ (hN τ)]
        congr 1
        rw [show spinCount_dev σ τ = (if σ 0 = τ then 1 else 0) + spinCount_dev (Fin.tail σ) τ by
          conv_lhs => rw [hσ]
          exact spinCount_cons_dev _ _ _]
        push_cast
        split_ifs <;> ring
      · rw [← amp_cons_dev, ← hσ]
        exact hJ _
    -- `N_{σ₀} Ψ = Σ_j c†c Ψ = 0`, while `N_{σ₀} Ψ = n Ψ` with `n ≥ 1`
    have hzero : toCLM T (Nsig T (σ 0)) Ψ = 0 := by
      have hc' : ∀ j : ZMod T.Nφ, toCLM T (njs T j (σ 0)) Ψ = 0 := by
        intro j
        have e : toCLM T (njs T j (σ 0)) Ψ = toCLM T (cjs T j (σ 0))ᴴ (toCLM T (cjs T j (σ 0)) Ψ) := by
          simp only [njs, toCLM, map_mul, mul_apply_eq_comp]
        rw [e, hc j, map_zero]
      have e : toCLM T (Nsig T (σ 0)) Ψ = ∑ j, toCLM T (njs T j (σ 0)) Ψ := by
        simp only [Nsig, toCLM, map_sum, FunLike.coe_sum, Finset.sum_apply]
      rw [e]
      exact Finset.sum_eq_zero fun j _ => hc' j
    have hpos : 0 < spinCount_dev σ (σ 0) :=
      Finset.card_pos.2 ⟨0, by simp⟩
    rw [hN (σ 0)] at hzero
    exact (smul_eq_zero.1 hzero).resolve_left (by exact_mod_cast hpos.ne')

theorem orbProd_linearIndependent_dev (T : Torus) :
    ∀ N : ℕ, LinearIndependent ℂ (fun J : Fin N → ZMod T.Nφ => orbProd T J) := by
  intro N
  induction N with
  | zero =>
    rw [Fintype.linearIndependent_iff]
    intro g hg J
    have h := congrFun hg (fun i => i.elim0)
    have hJ : ∀ J' : Fin 0 → ZMod T.Nφ, J' = J := fun J' => funext fun i => i.elim0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, orbProd, Finset.univ_eq_empty,
      Finset.prod_empty, mul_one, Pi.zero_apply] at h
    rw [Fintype.sum_eq_single J (fun J' hJ' => absurd (hJ J') hJ')] at h
    exact h
  | succ N ih =>
    rw [Fintype.linearIndependent_iff] at ih ⊢
    intro g hg J
    -- split the first variable off
    have hsplit : ∀ (z : ℂ) (w : Fin N → ℂ), ∑ a, orbHol T a z *
        (∑ J' : Fin N → ZMod T.Nφ, g (Fin.cons a J') * orbProd T J' w) = 0 := by
      intro z w
      have h := congrFun hg (Fin.cons z w)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      rw [← (Fin.consEquiv fun _ => ZMod T.Nφ).sum_comp, Fintype.sum_prod_type] at h
      rw [← h]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun J' _ => ?_
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, orbProd, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring
    have hinner : ∀ a (w : Fin N → ℂ), ∑ J' : Fin N → ZMod T.Nφ, g (Fin.cons a J') * orbProd T J' w = 0 := by
      intro a w
      have hli := (Fintype.linearIndependent_iff.1 (orbHol_linearIndependent T))
        (fun a => ∑ J' : Fin N → ZMod T.Nφ, g (Fin.cons a J') * orbProd T J' w)
        (funext fun z => by simpa [Finset.sum_apply, mul_comm] using hsplit z w)
      exact hli a
    have hJ : J = Fin.cons (J 0) (Fin.tail J) := (Fin.cons_self_tail J).symm
    have := ih (fun J' => g (Fin.cons (J 0) J'))
      (funext fun w => by simpa [Finset.sum_apply] using hinner (J 0) w) (Fin.tail J)
    rw [hJ]
    exact this

theorem spinCount_canonSpins_dev (n m : ℕ) :
    spinCount_dev (canonSpins n m) .up = n ∧ spinCount_dev (canonSpins n m) .dn = m := by
  constructor
  · unfold spinCount_dev canonSpins
    rw [Finset.card_filter, Fin.sum_univ_add]
    simp
  · unfold spinCount_dev canonSpins
    rw [Finset.card_filter, Fin.sum_univ_add]
    simp

theorem sector_counts_dev (T : Torus) (nn : SectorLabel T) {n m : ℕ} (hn : (nn.1 : ℕ) = n) (hm : (nn.2 : ℕ) = m)
    {Ψ : FockSpace T} (hΨ : Ψ ∈ sector T nn) :
    ∀ τ : Spin, toCLM T (Nsig T τ) Ψ = ((spinCount_dev (canonSpins n m) τ : ℕ) : ℂ) • Ψ := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hΨ
  rw [Module.End.mem_eigenspace_iff] at h1 h2
  obtain ⟨c1, c2⟩ := spinCount_canonSpins_dev n m
  intro τ
  cases τ
  · rw [c1, ← hn]
    exact h1
  · rw [c2, ← hm]
    exact h2

/-- The component as the explicit finite sum. -/
theorem comp_apply (T : Torus) {N : ℕ} (σ : Fin N → Spin) (Ψ : FockSpace T) (u : Fin N → ℂ) :
    comp T σ Ψ u = ∑ J : Fin N → ZMod T.Nφ, ⟪creVec T σ J, Ψ⟫_ℂ * ∏ i, orbHol T (J i) (u i) := by
  simp only [comp, amp, orbProd, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smulRight_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, Pi.smul_apply, smul_eq_mul]

/-! ### Proof device for the injectivity (proof phase, round one; not a statement of the paper): a vector with the
spin content of `σ` whose component vanishes is zero (`comp_eq_zero_dev`) -/

theorem comp_eq_zero_dev (T : Torus) {N : ℕ} (σ : Fin N → Spin) {Ψ : FockSpace T}
    (hN : ∀ τ : Spin, toCLM T (Nsig T τ) Ψ = ((spinCount_dev σ τ : ℕ) : ℂ) • Ψ) (h0 : comp T σ Ψ = 0) : Ψ = 0 := by
  refine eq_zero_of_amp_dev T N σ Ψ hN fun J => ?_
  have hli := Fintype.linearIndependent_iff.1 (orbProd_linearIndependent_dev T N)
    (fun J => ⟪creVec T σ J, Ψ⟫_ℂ) (funext fun u => by
      have := comp_apply T σ Ψ u
      rw [h0] at this
      simpa [Finset.sum_apply, orbProd] using this.symm)
  exact hli J

/-! ### Proof devices for the components of the basis states (proof phase, round one; not statements of the paper)

Wick's theorem for the creation vectors: `c_{js}` on `c†_{J₀σ₀} ⋯ c†_{J_Mσ_M} Ω` is the alternating sum over the factors
it contracts (`cjs_creVec_dev`, from block A's CAR `c_anticomm_star` and `c Ω = 0`, the latter from `N_σ ≥ 0`), so the
Gram matrix of the creation vectors is the determinant of the contractions (`gram_dev`, by Laplace's expansion along the
first row, Mathlib's `Matrix.det_succ_row_zero`). For `canonSpins` the contraction matrix is block diagonal
(`det_fromBlocks_zero₂₁`), and summing one block against the orbitals gives the Slater determinant (Leibniz's formula,
`Matrix.det_apply`). -/

/-- A vector on which `N_τ` acts by a negative number is zero: `⟨Φ, N_τ Φ⟩ = Σ_j ‖c_{jτ} Φ‖² ≥ 0`. -/
theorem eq_zero_of_Nsig_neg_dev (T : Torus) (τ : Spin) (r : ℝ) (hr : r < 0) {Φ : FockSpace T}
    (h : toCLM T (Nsig T τ) Φ = (r : ℂ) • Φ) : Φ = 0 := by
  have e1 : toCLM T (Nsig T τ) Φ = ∑ j, toCLM T (cjs T j τ)ᴴ (toCLM T (cjs T j τ) Φ) := by
    simp only [Nsig, njs, toCLM, map_sum, map_mul, FunLike.coe_sum, Finset.sum_apply, mul_apply_eq_comp]
  have e2 : ⟪Φ, toCLM T (Nsig T τ) Φ⟫_ℂ = ∑ j, ⟪toCLM T (cjs T j τ) Φ, toCLM T (cjs T j τ) Φ⟫_ℂ := by
    rw [e1, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← inner_toCLM_dev]
  have hre : ∀ v : FockSpace T, (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := fun v => inner_self_eq_norm_sq (𝕜 := ℂ) v
  have e3 : r * ‖Φ‖ ^ 2 = ∑ j, ‖toCLM T (cjs T j τ) Φ‖ ^ 2 := by
    have := congrArg Complex.re e2
    rw [h, inner_smul_right, Complex.re_sum, Complex.re_ofReal_mul, hre] at this
    simp only [hre] at this
    exact this
  have hnn : 0 ≤ ∑ j, ‖toCLM T (cjs T j τ) Φ‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsq : ‖Φ‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖Φ‖]
  have h0 : ‖Φ‖ ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)

/-- The vacuum has no particles. -/
theorem vac_counts_dev (T : Torus) (τ : Spin) :
    toCLM T (Nsig T τ) (EuclideanSpace.single (vac : Conf (ZMod T.Nφ)) (1 : ℂ)) =
      ((0 : ℕ) : ℂ) • EuclideanSpace.single (vac : Conf (ZMod T.Nφ)) (1 : ℂ) := by
  have hsec : EuclideanSpace.single (vac : Conf (ZMod T.Nφ)) (1 : ℂ) ∈ sector T (0, 0) := by
    rw [mem_sector_iff]
    intro m hm
    have hmv : m = vac := by
      by_contra h
      exact hm (by simp [h])
    subst hmv
    rw [secOf_eq_iff]
    simp [ctσ, vac]
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hsec
  rw [Module.End.mem_eigenspace_iff] at h1 h2
  cases τ
  · rw [show ((0 : ℕ) : ℂ) = (((((0, 0) : SectorLabel T).1 : ℕ) : ℝ) : ℂ) by simp]
    exact h1
  · rw [show ((0 : ℕ) : ℂ) = (((((0, 0) : SectorLabel T).2 : ℕ) : ℝ) : ℂ) by simp]
    exact h2

/-- `c_{js} Ω = 0`. -/
theorem cjs_vac_dev (T : Torus) (j : ZMod T.Nφ) (s : Spin) :
    toCLM T (cjs T j s) (EuclideanSpace.single (vac : Conf (ZMod T.Nφ)) (1 : ℂ)) = 0 := by
  refine eq_zero_of_Nsig_neg_dev T s (-1) (by norm_num) ?_
  rw [Nsig_cjs_dev T s s j _ (vac_counts_dev T s)]
  simp

/-- The CAR for `c_{js}` and `c†_{j's'}`, applied to a vector. -/
theorem cjs_mul_cdag_apply_dev (T : Torus) (j j' : ZMod T.Nφ) (s s' : Spin) (X : FockSpace T) :
    toCLM T (cjs T j s) (toCLM T (cjs T j' s')ᴴ X) =
      (if ((j, s) : Mode (ZMod T.Nφ)) = (j', s') then (1 : ℂ) else 0) • X -
        toCLM T (cjs T j' s')ᴴ (toCLM T (cjs T j s) X) := by
  have h := Fermion.Pilot.JW.c_anticomm_star ((j, s) : Mode (ZMod T.Nφ)) (j', s')
  rw [← cjs_eq, ← cjs_eq] at h
  have h' : cjs T j s * (cjs T j' s')ᴴ =
      (if ((j, s) : Mode (ZMod T.Nφ)) = (j', s') then 1 else 0) - (cjs T j' s')ᴴ * cjs T j s :=
    eq_sub_of_add_eq h
  have e : toCLM T (cjs T j s) (toCLM T (cjs T j' s')ᴴ X) = toCLM T (cjs T j s * (cjs T j' s')ᴴ) X := by
    simp only [toCLM, map_mul, mul_apply_eq_comp]
  rw [e, h']
  split_ifs <;> simp [toCLM, map_sub, mul_apply_eq_comp]

/-- The creation vector with no particle is the vacuum. -/
theorem creVec_zero_dev (T : Torus) (σ : Fin 0 → Spin) (J : Fin 0 → ZMod T.Nφ) :
    creVec T σ J = EuclideanSpace.single (vac : Conf (ZMod T.Nφ)) 1 := by
  unfold creVec creWord
  rw [List.ofFn_zero, List.prod_nil]
  simp only [toCLM, map_one, one_apply_eq_self]

theorem cons_tail_comp_succAbove_dev {α : Type*} {M : ℕ} (f : Fin (M + 2) → α) (b : Fin (M + 1)) :
    (Fin.cons (f 0) (Fin.tail f ∘ b.succAbove) : Fin (M + 1) → α) = f ∘ b.succ.succAbove := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp [Fin.succ_succAbove_succ, Fin.tail]

/-- Wick's theorem, one contraction: `c_{js} c†_{J₀σ₀} ⋯ c†_{J_Mσ_M} Ω = Σ_b (−1)^b δ_{(j,s),(J_b,σ_b)} (the word without
its `b`-th factor) Ω`. -/
theorem cjs_creVec_dev (T : Torus) (j : ZMod T.Nφ) (s : Spin) :
    ∀ (M : ℕ) (σ : Fin (M + 1) → Spin) (J : Fin (M + 1) → ZMod T.Nφ),
      toCLM T (cjs T j s) (creVec T σ J) =
        ∑ b : Fin (M + 1), ((-1 : ℂ) ^ (b : ℕ) * (if ((j, s) : Mode (ZMod T.Nφ)) = (J b, σ b) then 1 else 0)) •
          creVec T (σ ∘ b.succAbove) (J ∘ b.succAbove) := by
  intro M
  induction M with
  | zero =>
    intro σ J
    have hσJ : creVec T σ J = toCLM T (cjs T (J 0) (σ 0))ᴴ (creVec T (Fin.tail σ) (Fin.tail J)) := by
      rw [← creVec_cons_dev, Fin.cons_self_tail, Fin.cons_self_tail]
    rw [hσJ, cjs_mul_cdag_apply_dev, creVec_zero_dev T (Fin.tail σ) (Fin.tail J), cjs_vac_dev, map_zero, sub_zero,
      Fin.sum_univ_one, creVec_zero_dev T (σ ∘ (0 : Fin 1).succAbove) (J ∘ (0 : Fin 1).succAbove)]
    simp
  | succ M ih =>
    intro σ J
    have hσJ : creVec T σ J = toCLM T (cjs T (J 0) (σ 0))ᴴ (creVec T (Fin.tail σ) (Fin.tail J)) := by
      rw [← creVec_cons_dev, Fin.cons_self_tail, Fin.cons_self_tail]
    have hY : ∀ b' : Fin (M + 1), toCLM T (cjs T (J 0) (σ 0))ᴴ
        (creVec T (Fin.tail σ ∘ b'.succAbove) (Fin.tail J ∘ b'.succAbove)) =
          creVec T (σ ∘ b'.succ.succAbove) (J ∘ b'.succ.succAbove) := by
      intro b'
      rw [← creVec_cons_dev, cons_tail_comp_succAbove_dev, cons_tail_comp_succAbove_dev]
    have h0 : creVec T (σ ∘ (0 : Fin (M + 2)).succAbove) (J ∘ (0 : Fin (M + 2)).succAbove) =
        creVec T (Fin.tail σ) (Fin.tail J) := by
      simp only [Fin.succAbove_zero]
      rfl
    rw [hσJ, cjs_mul_cdag_apply_dev, ih (Fin.tail σ) (Fin.tail J), map_sum, Fin.sum_univ_succ (n := M + 1), h0,
      sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simp only [map_smul, hY]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun b' _ => ?_
      rw [← neg_smul]
      congr 1
      simp only [Fin.val_succ, pow_succ, Fin.tail]
      by_cases hc : ((j, s) : Mode (ZMod T.Nφ)) = (J b'.succ, σ b'.succ) <;> simp [hc]

/-- The Gram matrix of the creation vectors: `⟨c†_K Ω, c†_J Ω⟩ = det[δ_{(K_a,σ_a),(J_b,σ'_b)}]`. -/
theorem gram_dev (T : Torus) : ∀ (N : ℕ) (σ σ' : Fin N → Spin) (K J : Fin N → ZMod T.Nφ),
    ⟪creVec T σ K, creVec T σ' J⟫_ℂ =
      (Matrix.of fun a b => if ((K a, σ a) : Mode (ZMod T.Nφ)) = (J b, σ' b) then (1 : ℂ) else 0).det := by
  intro N
  induction N with
  | zero =>
    intro σ σ' K J
    rw [creVec_zero_dev, creVec_zero_dev, Matrix.det_isEmpty]
    simp
  | succ N ih =>
    intro σ σ' K J
    have hK : creVec T σ K = creVec T (Fin.cons (σ 0) (Fin.tail σ)) (Fin.cons (K 0) (Fin.tail K)) := by
      rw [Fin.cons_self_tail, Fin.cons_self_tail]
    rw [hK, amp_cons_dev, cjs_creVec_dev T (K 0) (σ 0) N σ' J, inner_sum, Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [inner_smul_right, ih]
    have hsub : (Matrix.of fun a c => if ((Fin.tail K a, Fin.tail σ a) : Mode (ZMod T.Nφ)) =
          ((J ∘ b.succAbove) c, (σ' ∘ b.succAbove) c) then (1 : ℂ) else 0) =
        (Matrix.of fun a b => if ((K a, σ a) : Mode (ZMod T.Nφ)) = (J b, σ' b) then (1 : ℂ) else 0).submatrix
          Fin.succ b.succAbove := by
      ext a c
      simp [Matrix.submatrix_apply, Fin.tail]
    rw [hsub, Matrix.of_apply]

/-- For `canonSpins` the contraction matrix is block diagonal. -/
theorem det_gram_canon_dev (T : Torus) (n m : ℕ) (Iu : Fin n → ZMod T.Nφ) (Id : Fin m → ZMod T.Nφ)
    (K : Fin (n + m) → ZMod T.Nφ) :
    (Matrix.of fun a b => if ((K a, canonSpins n m a) : Mode (ZMod T.Nφ)) =
        (Fin.append Iu Id b, canonSpins n m b) then (1 : ℂ) else 0).det =
      (Matrix.of fun α β : Fin n => if K (Fin.castAdd m α) = Iu β then (1 : ℂ) else 0).det *
        (Matrix.of fun α β : Fin m => if K (Fin.natAdd n α) = Id β then (1 : ℂ) else 0).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv,
    ← Matrix.det_fromBlocks_zero₂₁ _ (0 : Matrix (Fin n) (Fin m) ℂ)]
  congr 1
  ext (α | α) (β | β) <;> simp [canonSpins]

/-- One species: `Σ_K det[δ_{K_α, I_β}] ∏_α φ_{K_α}(x_α) = det[φ_{I_α}(x_β)]`. -/
theorem sum_det_delta_dev (T : Torus) {n : ℕ} (I : Fin n → ZMod T.Nφ) (x : Fin n → ℂ) :
    ∑ K : Fin n → ZMod T.Nφ, (Matrix.of fun α β : Fin n => if K α = I β then (1 : ℂ) else 0).det *
      ∏ α, orbHol T (K α) (x α) =
      (Matrix.of fun α β : Fin n => orbHol T (I α) (x β)).det := by
  rw [← Matrix.det_transpose]
  simp only [Matrix.det_apply, Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hK : ∀ K : Fin n → ZMod T.Nφ, (Equiv.arrowCongr ρ.symm (Equiv.refl (ZMod T.Nφ))) K = K ∘ ρ := by
    intro K
    funext i
    simp [Equiv.arrowCongr_apply]
  have e1 : ∀ K : Fin n → ZMod T.Nφ,
      (Equiv.Perm.sign ρ • ∏ i, (if K (ρ i) = I i then (1 : ℂ) else 0)) * ∏ α, orbHol T (K α) (x α) =
        Equiv.Perm.sign ρ • ∏ i, ((if K (ρ i) = I i then (1 : ℂ) else 0) * orbHol T (K (ρ i)) (x (ρ i))) := by
    intro K
    rw [smul_mul_assoc, ← Equiv.prod_comp ρ (fun α => orbHol T (K α) (x α)), ← Finset.prod_mul_distrib]
  have e3 : ∑ K : Fin n → ZMod T.Nφ, ∏ i, ((if K (ρ i) = I i then (1 : ℂ) else 0) * orbHol T (K (ρ i)) (x (ρ i))) =
      ∏ i, orbHol T (I i) (x (ρ i)) := by
    have h := (Equiv.arrowCongr ρ.symm (Equiv.refl (ZMod T.Nφ))).sum_comp
      (fun K' : Fin n → ZMod T.Nφ => ∏ i, ((if K' i = I i then (1 : ℂ) else 0) * orbHol T (K' i) (x (ρ i))))
    simp only [hK, Function.comp_apply] at h
    rw [h, ← Fintype.prod_sum (fun i (k : ZMod T.Nφ) => (if k = I i then (1 : ℂ) else 0) * orbHol T k (x (ρ i)))]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  rw [Finset.sum_congr rfl fun K _ => e1 K, ← Finset.smul_sum, e3]

/-- **`kz:sec:many`**: "`$\Psi=\sum_{I,I'}c_{I,I'}\,c^\dagger_{I\uparrow}c^\dagger_{I'\downarrow}|0\rangle$, with $I$ and $I'$ the sets of occupied up and down orbitals (up block first, increasing orbitals), corresponds to $F=s_{n,m}\sum c_{I,I'}\det[\phi_{I_\alpha}(x_\beta)]\det[\phi_{I'_\alpha}(y_\beta)]$ with one sign $s_{n,m}$ per sector.`"
— the basis state of the orbital tuples `Iu` (up) and `Id` (down) has the canonical component
`det[orbHol_{Iu_α}(x_β)] det[orbHol_{Id_α}(y_β)]`: the paper's formula with `s_{n,m} = 1` (for any tuples; both sides
vanish when an orbital repeats). -/
theorem canon_creVec (T : Torus) (n m : ℕ) (Iu : Fin n → ZMod T.Nφ) (Id : Fin m → ZMod T.Nφ) (u : Fin (n + m) → ℂ) :
    canon T n m (creVec T (canonSpins n m) (Fin.append Iu Id)) u =
      (Matrix.of fun α β : Fin n => orbHol T (Iu α) (u (Fin.castAdd m β))).det *
        (Matrix.of fun α β : Fin m => orbHol T (Id α) (u (Fin.natAdd n β))).det := by
  -- `⟨c†_K Ω, c†_J Ω⟩` is the block determinant of the contractions (`gram_dev`, `det_gram_canon_dev`), and each block
  -- summed against the orbitals is a Slater determinant (`sum_det_delta_dev`)
  show comp T (canonSpins n m) (creVec T (canonSpins n m) (Fin.append Iu Id)) u = _
  rw [comp_apply]
  simp only [gram_dev, det_gram_canon_dev]
  rw [← sum_det_delta_dev T Iu (fun β => u (Fin.castAdd m β)), ← sum_det_delta_dev T Id (fun β => u (Fin.natAdd n β)),
    Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  let e : (Fin (n + m) → ZMod T.Nφ) ≃ (Fin n → ZMod T.Nφ) × (Fin m → ZMod T.Nφ) :=
    { toFun := fun K => (fun α => K (Fin.castAdd m α), fun β => K (Fin.natAdd n β))
      invFun := fun p => Fin.append p.1 p.2
      left_inv := fun K => Fin.append_castAdd_natAdd
      right_inv := fun p => by
        ext α
        · simp
        · simp }
  refine Fintype.sum_equiv e _ _ fun K => ?_
  simp only [e, Equiv.coe_fn_mk, Fin.prod_univ_add]
  ring

/-- **`kz:sec:many`**: "`$\Psi$ is determined by its \emph{canonical component} $F(x_1,\dots,x_n;y_1,\dots,y_m)$ (the holomorphic part of $\Psi(\cdot;\uparrow^n\downarrow^m)$), antisymmetric in the $x$'s and in the $y$'s, each variable in the holomorphic class of $\kzL$; every other spin component is $\pm F$ with permuted arguments.`"
— "determined": the map `Ψ ↦ F` is injective on each sector (from the linear independence of the orbitals). -/
theorem canon_injective (T : Torus) (nn : SectorLabel T) {n m : ℕ} (hn : (nn.1 : ℕ) = n) (hm : (nn.2 : ℕ) = m)
    {Ψ : FockSpace T} (hΨ : Ψ ∈ sector T nn) (h0 : canon T n m Ψ = 0) : Ψ = 0 := by
  exact comp_eq_zero_dev T (canonSpins n m) (sector_counts_dev T nn hn hm hΨ) h0

/-- **`kz:sec:many`**: "`every other spin component is $\pm F$ with permuted arguments.`" — permuting the variables and the
spins together multiplies a component by the sign of the permutation (the CAR). -/
theorem comp_perm (T : Torus) {N : ℕ} (σ : Fin N → Spin) (ρ : Equiv.Perm (Fin N)) (Ψ : FockSpace T)
    (u : Fin N → ℂ) :
    comp T (σ ∘ ρ) Ψ (u ∘ ρ) = ((Equiv.Perm.sign ρ : ℤ) : ℂ) * comp T σ Ψ u := by
  rw [comp_apply, comp_apply, Finset.mul_sum, ← (Equiv.arrowCongr ρ.symm (Equiv.refl (ZMod T.Nφ))).sum_comp]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hK : (Equiv.arrowCongr ρ.symm (Equiv.refl (ZMod T.Nφ))) K = K ∘ ρ := by
    funext i
    simp [Equiv.arrowCongr_apply]
  have hprod : ∏ i, orbHol T ((K ∘ ρ) i) ((u ∘ ρ) i) = ∏ i, orbHol T (K i) (u i) :=
    Equiv.prod_comp ρ (fun i => orbHol T (K i) (u i))
  rw [hK, creVec_perm_dev, inner_smul_left, hprod]
  simp only [map_intCast]
  ring

/-- Components are in the Osgood class (finite sums of products of entire functions of one variable). -/
theorem comp_isOsgood (T : Torus) {N : ℕ} (σ : Fin N → Spin) (Ψ : FockSpace T) : IsOsgood (comp T σ Ψ) := by
  have hfun : (comp T σ Ψ : (Fin N → ℂ) → ℂ) =
      fun u => ∑ J : Fin N → ZMod T.Nφ, ⟪creVec T σ J, Ψ⟫_ℂ * ∏ i, orbHol T (J i) (u i) :=
    funext (comp_apply T σ Ψ)
  rw [hfun]
  refine ⟨?_, fun u k => ?_⟩
  · refine continuous_finsetSum _ fun J _ => continuous_const.mul ?_
    exact continuous_finsetProd _ fun i _ => (orbHol_differentiable T (J i)).continuous.comp (continuous_apply i)
  · refine Differentiable.fun_sum fun J _ => (differentiable_const _).mul ?_
    exact Differentiable.fun_finsetProd fun i _ =>
      (orbHol_differentiable T (J i)).comp (differentiable_update_apply_dev u k i)

/-- The proof of Lemma C.A: "`Expand $F$ in its first up and first down variables, $F=\sum_{a,b}\phi_a(x_1)\phi_b(y_1)F_{ab}(x';y')$.`"
"`So $F_{ab}=\pm$ (canonical component of $c_{b\downarrow}c_{a\uparrow}\Psi$), with a sign that depends only on $(n,m)$.`"
— for the first two variables of any spin component, with no sign: the coefficient of `orbHol_a(z₀) orbHol_b(z₁)` is the
component of `c_{bσ₁} c_{aσ₀} Ψ` for the remaining spins (the other pairs are brought to the front by `comp_perm`). -/
theorem comp_cons_cons (T : Torus) {N : ℕ} (σ : Fin (N + 2) → Spin) (Ψ : FockSpace T) (z₀ z₁ : ℂ)
    (w : Fin N → ℂ) :
    comp T σ Ψ (Fin.cons z₀ (Fin.cons z₁ w : Fin (N + 1) → ℂ) : Fin (N + 2) → ℂ) =
      ∑ a : ZMod T.Nφ, ∑ b : ZMod T.Nφ, orbHol T a z₀ * orbHol T b z₁ *
        comp T (fun i : Fin N => σ i.succ.succ) (toCLM T (cjs T b (σ 1) * cjs T a (σ 0)) Ψ) w := by
  have hσ : σ = Fin.cons (σ 0) (Fin.cons (σ 1) (fun i : Fin N => σ i.succ.succ)) := by
    funext i
    refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i
  have hamp : ∀ (a b : ZMod T.Nφ) (J : Fin N → ZMod T.Nφ),
      ⟪creVec T σ (Fin.cons a (Fin.cons b J)), Ψ⟫_ℂ =
        ⟪creVec T (fun i : Fin N => σ i.succ.succ) J, toCLM T (cjs T b (σ 1) * cjs T a (σ 0)) Ψ⟫_ℂ := by
    intro a b J
    conv_lhs => rw [hσ]
    rw [amp_cons_dev, amp_cons_dev]
    simp only [toCLM, map_mul, mul_apply_eq_comp]
  rw [comp_apply, ← (Fin.consEquiv fun _ => ZMod T.Nφ).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (Fin.consEquiv fun _ => ZMod T.Nφ).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [comp_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk]
  rw [hamp, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-! ## The torus LLL in each variable, and the image of the dictionary -/

/-- Two variables of the same species (both up, `< n`, or both down). -/
def SameSpecies (n : ℕ) {N : ℕ} (s t : Fin N) : Prop := ((s : ℕ) < n ↔ (t : ℕ) < n)

/-- **`kz:sec:many`**: the shape of a canonical component of the sector `(n, m)` — in the Osgood class, "`each variable in the holomorphic class of $\kzL$`"
(the space `Θ_L[0,0]` in each variable), and "`antisymmetric in the $x$'s and in the $y$'s`". -/
def IsCanonShape (τ : ℍ) (L n m : ℕ) (f : (Fin (n + m) → ℂ) → ℂ) : Prop :=
  IsOsgood f ∧
    (∀ (u : Fin (n + m) → ℂ) (i : Fin (n + m)), (fun z => f (Function.update u i z)) ∈ thetaSpace τ 0 0 L) ∧
    ∀ s t : Fin (n + m), s ≠ t → SameSpecies n s t → ∀ u, f (u ∘ Equiv.swap s t) = -f u

/-- Every canonical component has the shape. -/
theorem canon_shape (T : Torus) (n m : ℕ) (Ψ : FockSpace T) : IsCanonShape (tauT T) T.Nφ n m (canon T n m Ψ) := by
  refine ⟨comp_isOsgood T _ Ψ, fun u i => ?_, fun s t hst hss u => ?_⟩
  · -- each variable: a finite combination of orbitals
    have hfun : (fun z => canon T n m Ψ (Function.update u i z)) =
        ∑ J : Fin (n + m) → ZMod T.Nφ, (⟪creVec T (canonSpins n m) J, Ψ⟫_ℂ *
          ∏ k ∈ Finset.univ.erase i, orbHol T (J k) (u k)) • orbHol T (J i) := by
      funext z
      rw [show canon T n m Ψ (Function.update u i z) = comp T (canonSpins n m) Ψ (Function.update u i z) from rfl,
        comp_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self,
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]]
      ring
    rw [hfun]
    exact Submodule.sum_mem _ fun J _ => Submodule.smul_mem _ _ (orbHol_mem T (J i))
  · -- antisymmetry within a species, from `comp_perm` with a transposition
    have hss' : ((s : ℕ) < n ↔ (t : ℕ) < n) := hss
    have hspins : canonSpins n m ∘ Equiv.swap s t = canonSpins n m := by
      funext k
      simp only [Function.comp, canonSpins]
      rcases eq_or_ne k s with rfl | hks
      · rw [Equiv.swap_apply_left]
        by_cases h : (k : ℕ) < n
        · rw [ite_eq_left (hss'.1 h), ite_eq_left h]
        · rw [ite_eq_right (fun h' => h (hss'.2 h')), ite_eq_right h]
      · rcases eq_or_ne k t with rfl | hkt
        · rw [Equiv.swap_apply_right]
          by_cases h : (s : ℕ) < n
          · rw [ite_eq_left h, ite_eq_left (hss'.1 h)]
          · rw [ite_eq_right h, ite_eq_right (fun h' => h (hss'.2 h'))]
        · rw [Equiv.swap_apply_of_ne_of_ne hks hkt]
    have h := comp_perm T (canonSpins n m) (Equiv.swap s t) Ψ u
    rw [hspins, Equiv.Perm.sign_swap hst] at h
    show comp T (canonSpins n m) Ψ (u ∘ Equiv.swap s t) = -comp T (canonSpins n m) Ψ u
    rw [h]
    push_cast
    ring

/-! ### Proof devices for the image of the dictionary (proof phase, round one; not statements of the paper)

A function of the shape is expanded in products of orbitals: the orbitals take an invertible matrix of values at some
points (`exists_points_orbHol_dev`, from their linear independence by the cofactor expansion along the first column),
which gives Lagrange interpolation in each variable (`interp1_dev`) and, by induction on the number of variables, in all
of them (`interpN_dev`, `expand_dev`). The antisymmetry under transpositions within a species gives it under every
permutation of each species block (`blk_anti_dev`, by `Equiv.Perm.swap_induction_on`), so averaging over the blocks turns
the products of orbitals into products of two Slater determinants, the canonical components of the creation vectors
(`average_dev`, with `canon_creVec`); the creation vectors of `canonSpins n m` lie in the sector `(n, m)`
(`creVec_mem_sector_dev`). -/

/-- Linearly independent functions take an invertible matrix of values at some points. -/
theorem exists_points_det_ne_zero_dev {X : Type*} :
    ∀ (k : ℕ) (φ : Fin k → X → ℂ), LinearIndependent ℂ φ →
      ∃ x : Fin k → X, (Matrix.of fun a b => φ a (x b)).det ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro φ _
    exact ⟨fun i => i.elim0, by rw [Matrix.det_isEmpty]; exact one_ne_zero⟩
  | succ k ih =>
    intro φ hφ
    obtain ⟨x', hx'⟩ := ih (fun a => φ a.succ) (hφ.comp _ (Fin.succ_injective k))
    by_contra hno
    push Not at hno
    have hsub : ∀ (z : X) (i : Fin (k + 1)), (Matrix.of fun a b => φ a ((Fin.cons z x' : Fin (k + 1) → X) b)).submatrix
        i.succAbove Fin.succ = Matrix.of fun a b => φ (i.succAbove a) (x' b) := by
      intro z i
      ext a b
      simp
    set c : Fin (k + 1) → ℂ := fun i => (-1 : ℂ) ^ (i : ℕ) * (Matrix.of fun a b => φ (i.succAbove a) (x' b)).det
      with hc
    have hsum : ∑ i, c i • φ i = 0 := by
      funext z
      have h := hno (Fin.cons z x')
      rw [Matrix.det_succ_column_zero] at h
      simp only [hsub, Matrix.of_apply, Fin.cons_zero] at h
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]
      ring
    have h0 := Fintype.linearIndependent_iff.1 hφ c hsum 0
    apply hx'
    simpa [hc] using h0

/-- The orbitals take an invertible matrix of values at some points. -/
theorem exists_points_orbHol_dev (T : Torus) :
    ∃ z : ZMod T.Nφ → ℂ, IsUnit (Matrix.of fun a b => orbHol T a (z b)).det := by
  have : NeZero T.Nφ := ⟨T.Nφ_pos.ne'⟩
  let e : Fin T.Nφ ≃ ZMod T.Nφ := (ZMod.finEquiv T.Nφ).toEquiv
  obtain ⟨x, hx⟩ := exists_points_det_ne_zero_dev T.Nφ (fun a => orbHol T (e a))
    ((orbHol_linearIndependent T).comp _ e.injective)
  refine ⟨x ∘ e.symm, ?_⟩
  rw [isUnit_iff_ne_zero, ← Matrix.det_submatrix_equiv_self e]
  convert hx using 2
  ext a b
  simp

/-- Lagrange interpolation in the orbitals: `F(w) = Σ_b F(z_b) Σ_a (M⁻¹)_{ba} φ_a(w)` on `Θ_L[0,0]`. -/
theorem interp1_dev (T : Torus) {z : ZMod T.Nφ → ℂ} (hz : IsUnit (Matrix.of fun a b => orbHol T a (z b)).det)
    {F : ℂ → ℂ} (hF : F ∈ thetaSpace (tauT T) 0 0 T.Nφ) (w : ℂ) :
    F w = ∑ b, F (z b) * ∑ a, (Matrix.of fun a b => orbHol T a (z b))⁻¹ b a * orbHol T a w := by
  set M := Matrix.of fun a b => orbHol T a (z b) with hM
  rw [← span_orbHol, Submodule.mem_span_range_iff_exists_fun] at hF
  obtain ⟨c, rfl⟩ := hF
  have hMW : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hz
  have key : ∀ a' a, ∑ b, M a' b * M⁻¹ b a = if a' = a then 1 else 0 := by
    intro a' a
    have := congrFun (congrFun hMW a') a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc ∑ a, c a * orbHol T a w = ∑ a', ∑ a, c a' * (if a' = a then 1 else 0) * orbHol T a w := by
        refine Finset.sum_congr rfl fun a' _ => ?_
        simp
    _ = ∑ a', ∑ a, c a' * (∑ b, M a' b * M⁻¹ b a) * orbHol T a w := by simp only [key]
    _ = ∑ a', ∑ a, ∑ b, c a' * M a' b * M⁻¹ b a * orbHol T a w := by
        refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ a', ∑ b, ∑ a, c a' * M a' b * M⁻¹ b a * orbHol T a w :=
        Finset.sum_congr rfl fun a' _ => Finset.sum_comm
    _ = ∑ b, ∑ a', ∑ a, c a' * M a' b * M⁻¹ b a * orbHol T a w := Finset.sum_comm
    _ = ∑ b, (∑ a', c a' * orbHol T a' (z b)) * ∑ a, M⁻¹ b a * orbHol T a w := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [hM, Matrix.of_apply]
        ring

/-- Lagrange interpolation in every variable of a function whose one-variable slices lie in `Θ_L[0,0]`. -/
theorem interpN_dev (T : Torus) {z : ZMod T.Nφ → ℂ} (hz : IsUnit (Matrix.of fun a b => orbHol T a (z b)).det) :
    ∀ (N : ℕ) (g : (Fin N → ℂ) → ℂ),
      (∀ (u : Fin N → ℂ) (i : Fin N), (fun w => g (Function.update u i w)) ∈ thetaSpace (tauT T) 0 0 T.Nφ) →
      ∀ u : Fin N → ℂ, g u = ∑ B : Fin N → ZMod T.Nφ, g (z ∘ B) *
        ∏ i, ∑ a, (Matrix.of fun a b => orbHol T a (z b))⁻¹ (B i) a * orbHol T a (u i) := by
  intro N
  induction N with
  | zero =>
    intro g _ u
    rw [Fintype.sum_unique, Fin.prod_univ_zero, mul_one]
    congr 1
    funext i
    exact i.elim0
  | succ N ih =>
    intro g hg u
    have e0 : ∀ w, Function.update u 0 w = Fin.cons w (Fin.tail u) := fun w => by
      conv_lhs => rw [← Fin.cons_self_tail u]
      rw [Fin.update_cons_zero]
    have h1 : (fun w => g (Fin.cons w (Fin.tail u))) ∈ thetaSpace (tauT T) 0 0 T.Nφ := by
      simpa only [e0] using hg u 0
    have h2 : ∀ (b0 : ZMod T.Nφ) (v : Fin N → ℂ) (i : Fin N),
        (fun w' => g (Fin.cons (z b0) (Function.update v i w'))) ∈ thetaSpace (tauT T) 0 0 T.Nφ := by
      intro b0 v i
      simpa only [Fin.cons_update] using hg (Fin.cons (z b0) v) i.succ
    conv_lhs => rw [← Fin.cons_self_tail u]
    rw [interp1_dev T hz h1 (u 0), ← (Fin.consEquiv fun _ => ZMod T.Nφ).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hih := ih (fun v => g (Fin.cons (z b) v)) (h2 b) (Fin.tail u)
    beta_reduce at hih
    rw [hih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun B' _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.comp_cons,
      Fin.tail]
    ring

/-- The expansion of a function of the shape in products of orbitals. -/
theorem expand_dev (T : Torus) {z : ZMod T.Nφ → ℂ} (hz : IsUnit (Matrix.of fun a b => orbHol T a (z b)).det)
    (N : ℕ) (g : (Fin N → ℂ) → ℂ)
    (hg : ∀ (u : Fin N → ℂ) (i : Fin N), (fun w => g (Function.update u i w)) ∈ thetaSpace (tauT T) 0 0 T.Nφ) :
    ∃ c : (Fin N → ZMod T.Nφ) → ℂ, ∀ v, g v = ∑ K, c K * ∏ i, orbHol T (K i) (v i) := by
  set W := (Matrix.of fun a b => orbHol T a (z b))⁻¹ with hW
  refine ⟨fun K => ∑ B : Fin N → ZMod T.Nφ, g (z ∘ B) * ∏ i, W (B i) (K i), fun v => ?_⟩
  rw [interpN_dev T hz N g hg v]
  simp only [Fintype.prod_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun B _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-- The action of a permutation of each species block on the variables. -/
def blkAct_dev {n m : ℕ} (ρ : Equiv.Perm (Fin n)) (ρ' : Equiv.Perm (Fin m)) (u : Fin (n + m) → ℂ) :
    Fin (n + m) → ℂ :=
  Fin.append (fun α => u (Fin.castAdd m (ρ α))) (fun β => u (Fin.natAdd n (ρ' β)))

theorem castAdd_ne_natAdd_dev {n m : ℕ} (α : Fin n) (β : Fin m) : Fin.castAdd m α ≠ Fin.natAdd n β := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem blkAct_one_dev {n m : ℕ} (u : Fin (n + m) → ℂ) : blkAct_dev 1 1 u = u := by
  unfold blkAct_dev
  exact Fin.append_castAdd_natAdd

theorem blkAct_swap_right_dev {n m : ℕ} (ρ : Equiv.Perm (Fin n)) (ρ₀ : Equiv.Perm (Fin m)) (x y : Fin m)
    (u : Fin (n + m) → ℂ) :
    blkAct_dev ρ (Equiv.swap x y * ρ₀) u = blkAct_dev ρ ρ₀ (u ∘ Equiv.swap (Fin.natAdd n x) (Fin.natAdd n y)) := by
  unfold blkAct_dev
  congr 1
  · funext α
    simp only [Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (castAdd_ne_natAdd_dev _ _) (castAdd_ne_natAdd_dev _ _)]
  · funext β
    simp only [Function.comp_apply, Equiv.Perm.mul_apply]
    rw [(Fin.natAdd_injective m n).swap_apply]

theorem blkAct_swap_left_dev {n m : ℕ} (ρ₀ : Equiv.Perm (Fin n)) (ρ' : Equiv.Perm (Fin m)) (x y : Fin n)
    (u : Fin (n + m) → ℂ) :
    blkAct_dev (Equiv.swap x y * ρ₀) ρ' u = blkAct_dev ρ₀ ρ' (u ∘ Equiv.swap (Fin.castAdd m x) (Fin.castAdd m y)) := by
  unfold blkAct_dev
  congr 1
  · funext α
    simp only [Function.comp_apply, Equiv.Perm.mul_apply]
    rw [(Fin.castAdd_injective n m).swap_apply]
  · funext β
    simp only [Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (castAdd_ne_natAdd_dev _ _).symm (castAdd_ne_natAdd_dev _ _).symm]

/-- The antisymmetry within each species, for every permutation of the blocks. -/
theorem blk_anti_dev {n m : ℕ} {f : (Fin (n + m) → ℂ) → ℂ}
    (hanti : ∀ s t : Fin (n + m), s ≠ t → SameSpecies n s t → ∀ u, f (u ∘ Equiv.swap s t) = -f u)
    (ρ : Equiv.Perm (Fin n)) (ρ' : Equiv.Perm (Fin m)) (u : Fin (n + m) → ℂ) :
    f (blkAct_dev ρ ρ' u) = ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ' : ℤ) : ℂ) * f u := by
  have hR : ∀ (ρ' : Equiv.Perm (Fin m)) (u : Fin (n + m) → ℂ),
      f (blkAct_dev 1 ρ' u) = ((Equiv.Perm.sign ρ' : ℤ) : ℂ) * f u := by
    intro ρ'
    induction ρ' using Equiv.Perm.swap_induction_on with
    | one =>
      intro u
      rw [blkAct_one_dev]
      simp
    | swap_mul ρ₀ x y hxy ih =>
      intro u
      rw [blkAct_swap_right_dev, ih, hanti _ _ ((Fin.natAdd_injective m n).ne hxy)
        (show ((Fin.natAdd n x : ℕ) < n ↔ (Fin.natAdd n y : ℕ) < n) by simp)]
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]
      push_cast
      ring
  induction ρ using Equiv.Perm.swap_induction_on generalizing u with
  | one =>
    rw [hR]
    simp
  | swap_mul ρ₀ x y hxy ih =>
    rw [blkAct_swap_left_dev, ih, hanti _ _ ((Fin.castAdd_injective n m).ne hxy)
      (show ((Fin.castAdd m x : ℕ) < n ↔ (Fin.castAdd m y : ℕ) < n) by simp)]
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]
    push_cast
    ring

/-- Leibniz's formula, in the form used for the averaging. -/
theorem leibniz_dev (T : Torus) {n : ℕ} (K : Fin n → ZMod T.Nφ) (x : Fin n → ℂ) :
    (Matrix.of fun α β : Fin n => orbHol T (K α) (x β)).det =
      ∑ ρ : Equiv.Perm (Fin n), ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ α, orbHol T (K α) (x (ρ α)) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  simp only [Matrix.transpose_apply, Matrix.of_apply]

/-- Averaging over the blocks: `n! m! f(u) = Σ_K c_K F_K(u)` with `F_K` the canonical component of `c†_K Ω`. -/
theorem average_dev (T : Torus) {n m : ℕ} {f : (Fin (n + m) → ℂ) → ℂ}
    (hanti : ∀ s t : Fin (n + m), s ≠ t → SameSpecies n s t → ∀ u, f (u ∘ Equiv.swap s t) = -f u)
    {c : (Fin (n + m) → ZMod T.Nφ) → ℂ} (hc : ∀ v, f v = ∑ K, c K * ∏ i, orbHol T (K i) (v i))
    (u : Fin (n + m) → ℂ) :
    ((Nat.factorial n * Nat.factorial m : ℕ) : ℂ) * f u =
      ∑ K, c K * canon T n m (creVec T (canonSpins n m) K) u := by
  have h1 : ((Nat.factorial n * Nat.factorial m : ℕ) : ℂ) * f u =
      ∑ ρ : Equiv.Perm (Fin n), ∑ ρ' : Equiv.Perm (Fin m),
        ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ' : ℤ) : ℂ) * f (blkAct_dev ρ ρ' u) := by
    have hs : ∀ (ρ : Equiv.Perm (Fin n)) (ρ' : Equiv.Perm (Fin m)),
        ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ' : ℤ) : ℂ) * f (blkAct_dev ρ ρ' u) = f u := by
      intro ρ ρ'
      rw [blk_anti_dev hanti]
      have e1 : ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ : ℤ) : ℂ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
      have e2 : ((Equiv.Perm.sign ρ' : ℤ) : ℂ) * ((Equiv.Perm.sign ρ' : ℤ) : ℂ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
      linear_combination (((Equiv.Perm.sign ρ' : ℤ) : ℂ) * ((Equiv.Perm.sign ρ' : ℤ) : ℂ) * f u) * e1 + f u * e2
    simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hK : ∀ K : Fin (n + m) → ZMod T.Nφ, c K * canon T n m (creVec T (canonSpins n m) K) u =
      ∑ ρ : Equiv.Perm (Fin n), ∑ ρ' : Equiv.Perm (Fin m),
        ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ' : ℤ) : ℂ) *
          (c K * ∏ i, orbHol T (K i) (blkAct_dev ρ ρ' u i)) := by
    intro K
    have hKa : K = Fin.append (fun α => K (Fin.castAdd m α)) (fun β => K (Fin.natAdd n β)) :=
      Fin.append_castAdd_natAdd.symm
    rw [hKa, canon_creVec, leibniz_dev, leibniz_dev, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ' _ => ?_
    simp only [blkAct_dev, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
    ring
  rw [h1]
  calc ∑ ρ : Equiv.Perm (Fin n), ∑ ρ' : Equiv.Perm (Fin m),
        ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ' : ℤ) : ℂ) * f (blkAct_dev ρ ρ' u)
      = ∑ ρ : Equiv.Perm (Fin n), ∑ ρ' : Equiv.Perm (Fin m), ∑ K : Fin (n + m) → ZMod T.Nφ,
          ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ' : ℤ) : ℂ) *
            (c K * ∏ i, orbHol T (K i) (blkAct_dev ρ ρ' u i)) := by
        simp only [hc, Finset.mul_sum]
    _ = ∑ ρ : Equiv.Perm (Fin n), ∑ K : Fin (n + m) → ZMod T.Nφ, ∑ ρ' : Equiv.Perm (Fin m),
          ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ' : ℤ) : ℂ) *
            (c K * ∏ i, orbHol T (K i) (blkAct_dev ρ ρ' u i)) :=
        Finset.sum_congr rfl fun ρ _ => Finset.sum_comm
    _ = ∑ K : Fin (n + m) → ZMod T.Nφ, ∑ ρ : Equiv.Perm (Fin n), ∑ ρ' : Equiv.Perm (Fin m),
          ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ' : ℤ) : ℂ) *
            (c K * ∏ i, orbHol T (K i) (blkAct_dev ρ ρ' u i)) := Finset.sum_comm
    _ = ∑ K, c K * canon T n m (creVec T (canonSpins n m) K) u :=
        Finset.sum_congr rfl fun K _ => (hK K).symm

/-- `c†_{js}` raises the number of `τ`-particles by `[s = τ]`. -/
theorem Nsig_cdag_dev (T : Torus) (τ s : Spin) (j : ZMod T.Nφ) (k : ℂ) {Ψ : FockSpace T}
    (hΨ : toCLM T (Nsig T τ) Ψ = k • Ψ) :
    toCLM T (Nsig T τ) (toCLM T (cjs T j s)ᴴ Ψ) = (k + if s = τ then 1 else 0) • toCLM T (cjs T j s)ᴴ Ψ := by
  have h := Nsig_mul_cdag T τ (j, s)
  rw [← cjs_eq] at h
  have e1 : toCLM T (Nsig T τ) (toCLM T (cjs T j s)ᴴ Ψ) = toCLM T (Nsig T τ * (cjs T j s)ᴴ) Ψ := by
    simp only [toCLM, map_mul, mul_apply_eq_comp]
  rw [e1, h]
  simp only [toCLM] at hΨ ⊢
  simp only [map_mul, mul_apply_eq_comp, map_add, map_smul, map_one, add_apply, smul_apply, one_apply_eq_self]
  rw [hΨ, map_smul, add_smul]

/-- The creation vectors have the spin content of their spins. -/
theorem creVec_counts_dev (T : Torus) : ∀ (N : ℕ) (σ : Fin N → Spin) (K : Fin N → ZMod T.Nφ) (τ : Spin),
    toCLM T (Nsig T τ) (creVec T σ K) = ((spinCount_dev σ τ : ℕ) : ℂ) • creVec T σ K := by
  intro N
  induction N with
  | zero =>
    intro σ K τ
    rw [creVec_zero_dev, vac_counts_dev]
    congr 1
  | succ N ih =>
    intro σ K τ
    have hσK : creVec T σ K = toCLM T (cjs T (K 0) (σ 0))ᴴ (creVec T (Fin.tail σ) (Fin.tail K)) := by
      rw [← creVec_cons_dev, Fin.cons_self_tail, Fin.cons_self_tail]
    rw [hσK, Nsig_cdag_dev T τ (σ 0) (K 0) _ (ih (Fin.tail σ) (Fin.tail K) τ)]
    congr 1
    have hc : spinCount_dev σ τ = (if σ 0 = τ then 1 else 0) + spinCount_dev (Fin.tail σ) τ := by
      conv_lhs => rw [← Fin.cons_self_tail σ]
      exact spinCount_cons_dev _ _ _
    rw [hc]
    push_cast
    ring

/-- The creation vectors of `canonSpins n m` lie in the sector `(n, m)`. -/
theorem creVec_mem_sector_dev (T : Torus) (nn : SectorLabel T) {n m : ℕ} (hn : (nn.1 : ℕ) = n)
    (hm : (nn.2 : ℕ) = m) (K : Fin (n + m) → ZMod T.Nφ) : creVec T (canonSpins n m) K ∈ sector T nn := by
  obtain ⟨cu, cd⟩ := spinCount_canonSpins_dev n m
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    show toCLM T (Nsig T .up) _ = _
    rw [creVec_counts_dev, cu, hn]
    norm_cast
  · rw [Module.End.mem_eigenspace_iff]
    show toCLM T (Nsig T .dn) _ = _
    rw [creVec_counts_dev, cd, hm]
    norm_cast

/-- The image of the dictionary (needed for the lower bound; not in the brief's list — the module docstring): a function
of the shape is the canonical component of a vector of the sector. -/
theorem canon_surj (T : Torus) (nn : SectorLabel T) {n m : ℕ} (hn : (nn.1 : ℕ) = n) (hm : (nn.2 : ℕ) = m)
    {f : (Fin (n + m) → ℂ) → ℂ} (hf : IsCanonShape (tauT T) T.Nφ n m f) :
    ∃ Ψ ∈ sector T nn, canon T n m Ψ = f := by
  -- expand in products of orbitals, average over the species blocks, and read off the creation vectors
  obtain ⟨_, hslice, hanti⟩ := hf
  obtain ⟨z, hz⟩ := exists_points_orbHol_dev T
  obtain ⟨c, hc⟩ := expand_dev T hz (n + m) f hslice
  refine ⟨((Nat.factorial n * Nat.factorial m : ℕ) : ℂ)⁻¹ • ∑ K, c K • creVec T (canonSpins n m) K, ?_, ?_⟩
  · exact Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun K _ => Submodule.smul_mem _ _ (creVec_mem_sector_dev T nn hn hm K))
  · funext u
    have hfact : ((Nat.factorial n * Nat.factorial m : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero m))
    have hav := average_dev T hanti hc u
    rw [map_smul, map_sum]
    simp only [map_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [← hav, ← mul_assoc, inv_mul_cancel₀ hfact, one_mul]

/-! ## The orbital pair operators (`kz:eq:Bn`) and the identification with Definition 4.1 -/

/-- `kz:sec:ham`: "`Put $\kzq^{d^2}:=e^{i\pi\tau d^2/(2L)}$ (for rectangular $\tau=i\tau_2$ this is $e^{-\kappa^2d^2/4}$, by \eqref{kz:eq:flux}).`" -/
def qw (T : Torus) (d : ℤ) : ℂ := cexp (π * I * (tauT T : ℂ) * (d : ℂ) ^ 2 / (2 * (T.Nφ : ℂ)))

/-- **(C.eq:Bn)**: "`B_n^{\sigma\sigma'}:=\sum_{A+B=n,\ A,B\in\Z}(A-B)\,\kzq^{(A-B)^2}\,c_{[B]\sigma'}c_{[A]\sigma}`" — the sum over
`A ∈ ℤ`, `B = n − A` (a `tsum` of operators). -/
def Bpair (T : Torus) (σ σ' : Spin) (n : ℤ) : FockOp T :=
  ∑' A : ℤ, (((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n)) •
    (cjs T ((n - A : ℤ) : ZMod T.Nφ) σ' * cjs T (A : ZMod T.Nφ) σ)

/-- `kz:sec:ham`: "`Put $\kzq^{d^2}:=e^{i\pi\tau d^2/(2L)}$ (for rectangular $\tau=i\tau_2$ this is $e^{-\kappa^2d^2/4}$, by \eqref{kz:eq:flux}).`" -/
theorem qw_eq (T : Torus) (d : ℤ) : qw T d = ((Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) : ℝ) : ℂ) := by
  have hNφ : (T.Nφ : ℂ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
  have hLy : (T.Ly : ℂ) ≠ 0 := by exact_mod_cast T.Ly_pos.ne'
  have harea : (T.Lx : ℂ) = 2 * π * T.Nφ / T.Ly := by
    have h := T.area
    have h2 : ((2 * T.N : ℕ) : ℝ) = (T.Nφ : ℝ) := rfl
    rw [h2] at h
    rw [eq_div_iff hLy]
    exact_mod_cast h
  unfold qw
  rw [Complex.ofReal_exp]
  congr 1
  show π * I * (((T.Lx / T.Ly : ℝ) : ℂ) * I) * (d : ℂ) ^ 2 / (2 * (T.Nφ : ℂ)) =
    ((-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4 : ℝ) : ℂ)
  simp only [Torus.κ]
  push_cast
  rw [harea]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### Proof devices for the identification of the pair operators (proof phase, round one; not statements of the paper)

The terms of `B_n^{σσ'}` indexed by `d = A − B = 2A − n` (`BpairTerm_dev`, zero unless `d ≡ n mod 2`), their
summability over `ℤ` by the Gaussian weight (as block C's `summable_bcenTerm`), and the paper's pairing of the terms
`(A, B)` and `(B, A)`, i.e. of `d` with `−d` (`pairTerm_*_dev`), against block C's terms of `b_ν(n)`. -/

/-- The term of `B_n^{σσ'}` with `A − B = d`. -/
def BpairTerm_dev (T : Torus) (σ σ' : Spin) (n d : ℤ) : FockOp T :=
  if d ≡ n [ZMOD 2] then
    ((d : ℂ) * qw T d) • (cjs T (((n - d) / 2 : ℤ) : ZMod T.Nφ) σ' * cjs T (((n + d) / 2 : ℤ) : ZMod T.Nφ) σ)
  else 0

theorem Bpair_eq_tsum_dev (T : Torus) (σ σ' : Spin) (n : ℤ) :
    Bpair T σ σ' n = ∑' d : ℤ, BpairTerm_dev T σ σ' n d := by
  unfold Bpair
  have hinj : Function.Injective fun A : ℤ => 2 * A - n := fun A B h => by simp only at h; omega
  rw [← hinj.tsum_eq (f := BpairTerm_dev T σ σ' n)]
  · refine tsum_congr fun A => ?_
    have hmod : (2 * A - n) ≡ n [ZMOD 2] := by
      rw [Int.ModEq]
      omega
    have h1 : (n - (2 * A - n)) / 2 = n - A := by omega
    have h2 : (n + (2 * A - n)) / 2 = A := by omega
    simp only [BpairTerm_dev, hmod, ite_true, h1, h2]
  · intro d hd
    rw [Function.mem_support] at hd
    unfold BpairTerm_dev at hd
    split_ifs at hd with h
    · refine ⟨(n + d) / 2, ?_⟩
      rw [Int.ModEq] at h
      simp only
      omega
    · exact absurd rfl hd

theorem norm_BpairTerm_le_dev (T : Torus) (σ σ' : Spin) (n d : ℤ) :
    ‖toCLM T (BpairTerm_dev T σ σ' n d)‖ ≤ |(d : ℝ)| * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) := by
  unfold BpairTerm_dev
  split_ifs
  · rw [toCLM_eq_opCLM, opCLM_smul, norm_smul, qw_eq]
    have hc := norm_chatVec_mul_le (spinTensor (orb T (((n - d) / 2 : ℤ) : ZMod T.Nφ)) σ')
      (spinTensor (orb T (((n + d) / 2 : ℤ) : ZMod T.Nφ)) σ)
    simp only [norm_spinTensor, orb, PiLp.norm_single, norm_one, mul_one] at hc
    have hw : ‖(d : ℂ) * ((Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) : ℝ) : ℂ)‖ =
        |(d : ℝ)| * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      congr 1
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    rw [hw]
    calc |(d : ℝ)| * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) *
          ‖opCLM (cjs T (((n - d) / 2 : ℤ) : ZMod T.Nφ) σ' * cjs T (((n + d) / 2 : ℤ) : ZMod T.Nφ) σ)‖
        ≤ |(d : ℝ)| * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) * 1 :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := mul_one _
  · rw [toCLM_eq_opCLM, opCLM_zero, norm_zero]
    positivity

theorem exp_gauss_le_dev (T : Torus) (k : ℕ) :
    Real.exp (-(T.κ ^ 2 * (k : ℝ) ^ 2) / 4) ≤ Real.exp (-(T.κ ^ 2 / 4) * k) := by
  -- block C's estimate (`summable_bcenTerm`)
  apply Real.exp_le_exp.mpr
  have hd : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ k := by exact_mod_cast h
      nlinarith
  have hk : 0 ≤ T.κ ^ 2 := sq_nonneg _
  nlinarith

theorem summable_BpairTerm_dev (T : Torus) (σ σ' : Spin) (n : ℤ) : Summable (BpairTerm_dev T σ σ' n) := by
  have hκ : 0 < T.κ ^ 2 / 4 := by have := T.κ_pos; positivity
  have hs : Summable fun k : ℕ => (k : ℝ) ^ 1 * Real.exp (-(T.κ ^ 2 / 4) * k) :=
    Real.summable_pow_mul_exp_neg_nat_mul 1 hκ
  refine Summable.of_nat_of_neg ?_ ?_
  · refine summable_of_summable_norm_opCLM (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hs)
    have h := norm_BpairTerm_le_dev T σ σ' n k
    rw [toCLM_eq_opCLM] at h
    refine h.trans ?_
    rw [pow_one, show ((k : ℤ) : ℝ) = (k : ℝ) by push_cast; rfl, abs_of_nonneg (Nat.cast_nonneg k)]
    exact mul_le_mul_of_nonneg_left (exp_gauss_le_dev T k) (Nat.cast_nonneg k)
  · refine summable_of_summable_norm_opCLM (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hs)
    have h := norm_BpairTerm_le_dev T σ σ' n (-(k : ℤ))
    rw [toCLM_eq_opCLM] at h
    refine h.trans ?_
    rw [pow_one, show ((-(k : ℤ) : ℤ) : ℝ) = -(k : ℝ) by push_cast; rfl, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg k), neg_sq]
    exact mul_le_mul_of_nonneg_left (exp_gauss_le_dev T k) (Nat.cast_nonneg k)

theorem BpairTerm_zero_dev (T : Torus) (σ σ' : Spin) (n : ℤ) : BpairTerm_dev T σ σ' n 0 = 0 := by
  unfold BpairTerm_dev
  split_ifs <;> simp

theorem Bpair_eq_tsum_nat_dev (T : Torus) (σ σ' : Spin) (n : ℤ) :
    Bpair T σ σ' n = ∑' k : ℕ, (BpairTerm_dev T σ σ' n k + BpairTerm_dev T σ σ' n (-(k : ℤ))) := by
  rw [tsum_nat_add_neg (summable_BpairTerm_dev T σ σ' n), BpairTerm_zero_dev, add_zero, Bpair_eq_tsum_dev]

theorem sum_spin_dev {M : Type*} [AddCommMonoid M] (f : Spin → M) : ∑ s, f s = f .up + f .dn := by
  rw [show (Finset.univ : Finset Spin) = {Spin.up, Spin.dn} from rfl, Finset.sum_pair (by decide)]

theorem cpair_plus_dev (T : Torus) (f g : Space T) :
    cpair T .plus f g = cf T (spinTensor f .up) * cf T (spinTensor g .up) := by
  simp [cpair, sum_spin_dev, chi]

theorem cpair_minus_dev (T : Torus) (f g : Space T) :
    cpair T .minus f g = cf T (spinTensor f .dn) * cf T (spinTensor g .dn) := by
  simp [cpair, sum_spin_dev, chi]

theorem cpair_zero_dev (T : Torus) (f g : Space T) :
    cpair T .zero f g = (((2 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      (cf T (spinTensor f .dn) * cf T (spinTensor g .up) + cf T (spinTensor f .up) * cf T (spinTensor g .dn)) := by
  simp [cpair, sum_spin_dev, chi, smul_add]

theorem neg_modEq_two_dev (d n : ℤ) : (-d ≡ n [ZMOD 2]) ↔ (d ≡ n [ZMOD 2]) := by
  simp only [Int.ModEq]
  omega

theorem qw_neg_dev (T : Torus) (d : ℤ) : qw T (-d) = qw T d := by
  rw [qw_eq, qw_eq]
  push_cast
  ring_nf

theorem cjs_anticomm_dev (T : Torus) (a b : ZMod T.Nφ) (t t' : Spin) :
    cjs T a t * cjs T b t' = -(cjs T b t' * cjs T a t) := by
  have h := cf_anticomm T (spinTensor (orb T a) t) (spinTensor (orb T b) t')
  exact eq_neg_of_add_eq_zero_left h

theorem qw_neg_mul_dev (T : Torus) (k : ℕ) :
    ((-(k : ℤ) : ℤ) : ℂ) * qw T (k : ℤ) = -(((k : ℤ) : ℂ) * qw T (k : ℤ)) := by
  push_cast
  ring

/-- The pairing of `d` and `−d` for equal spins. -/
theorem pairTerm_same_dev (T : Torus) (s : Spin) (n : ℤ) (k : ℕ) :
    BpairTerm_dev T s s n k + BpairTerm_dev T s s n (-(k : ℤ)) =
      if (k : ℤ) ≡ n [ZMOD 2] then
        ((2 * (k : ℝ) * Real.exp (-(T.κ ^ 2 * (k : ℝ) ^ 2) / 4) : ℝ) : ℂ) •
          (cjs T (((n - (k : ℤ)) / 2 : ℤ) : ZMod T.Nφ) s * cjs T (((n + (k : ℤ)) / 2 : ℤ) : ZMod T.Nφ) s)
      else 0 := by
  unfold BpairTerm_dev
  simp only [neg_modEq_two_dev]
  split_ifs with h
  · rw [qw_neg_dev, show n - -(k : ℤ) = n + k by ring, show n + -(k : ℤ) = n - k by ring,
      cjs_anticomm_dev T (((n + (k : ℤ)) / 2 : ℤ) : ZMod T.Nφ) (((n - (k : ℤ)) / 2 : ℤ) : ZMod T.Nφ) s s,
      qw_neg_mul_dev, neg_smul, smul_neg, neg_neg, ← add_smul, qw_eq]
    congr 1
    push_cast
    ring
  · simp

/-- The pairing of `d` and `−d` for the spins `(σ, σ') = (↑, ↓)` and `(↓, ↑)`. -/
theorem pairTerm_mixed_dev (T : Torus) (s s' : Spin) (hss : s ≠ s') (n : ℤ) (k : ℕ) :
    BpairTerm_dev T s s' n k + BpairTerm_dev T s s' n (-(k : ℤ)) =
      if (k : ℤ) ≡ n [ZMOD 2] then
        (((k : ℝ) * Real.exp (-(T.κ ^ 2 * (k : ℝ) ^ 2) / 4) : ℝ) : ℂ) •
          (cjs T (((n - (k : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .dn * cjs T (((n + (k : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .up +
            cjs T (((n - (k : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .up * cjs T (((n + (k : ℤ)) / 2 : ℤ) : ZMod T.Nφ) .dn)
      else 0 := by
  unfold BpairTerm_dev
  simp only [neg_modEq_two_dev]
  split_ifs with h
  · rw [qw_neg_dev, show n - -(k : ℤ) = n + k by ring, show n + -(k : ℤ) = n - k by ring,
      cjs_anticomm_dev T (((n + (k : ℤ)) / 2 : ℤ) : ZMod T.Nφ) (((n - (k : ℤ)) / 2 : ℤ) : ZMod T.Nφ) s' s,
      qw_neg_mul_dev, neg_smul, smul_neg, neg_neg, ← smul_add, qw_eq]
    have hscal : ((k : ℤ) : ℂ) * ((Real.exp (-(T.κ ^ 2 * ((k : ℤ) : ℝ) ^ 2) / 4) : ℝ) : ℂ) =
        (((k : ℝ) * Real.exp (-(T.κ ^ 2 * (k : ℝ) ^ 2) / 4) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hscal]
    congr 1
    cases s <;> cases s'
    · exact absurd rfl hss
    · rfl
    · rw [add_comm]
    · exact absurd rfl hss
  · simp

/-- The identification paragraph: "`pairing the terms $(A,B)$ and $(B,A)$ of \eqref{kz:eq:Bn} gives $B_n^{\up\up}=\bcen+n$, $B_n^{\dn\dn}=\bcen-n$ and $B_n^{\up\dn}=B_n^{\dn\up}=\bcen0n/\sqrt2$`"
— `B_n^{↑↑} = b_+(n)`. -/
theorem Bpair_up_up (T : Torus) (n : ℤ) : Bpair T .up .up n = bcen T .plus n := by
  rw [Bpair_eq_tsum_nat_dev]
  unfold bcen
  refine tsum_congr fun k => ?_
  rw [pairTerm_same_dev]
  unfold bcenTerm
  rw [cpair_plus_dev]
  rfl

/-- The identification paragraph: `B_n^{↓↓} = b_−(n)`. -/
theorem Bpair_dn_dn (T : Torus) (n : ℤ) : Bpair T .dn .dn n = bcen T .minus n := by
  rw [Bpair_eq_tsum_nat_dev]
  unfold bcen
  refine tsum_congr fun k => ?_
  rw [pairTerm_same_dev]
  unfold bcenTerm
  rw [cpair_minus_dev]
  rfl

/-- The identification paragraph: `B_n^{↑↓} = b_0(n)/√2`. -/
theorem Bpair_up_dn (T : Torus) (n : ℤ) : Bpair T .up .dn n = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • bcen T .zero n := by
  rw [Bpair_eq_tsum_nat_dev]
  unfold bcen
  rw [← (summable_bcenTerm T .zero n).2.tsum_const_smul]
  refine tsum_congr fun k => ?_
  rw [pairTerm_mixed_dev T .up .dn (by decide)]
  unfold bcenTerm
  split_ifs
  · rw [cpair_zero_dev, smul_smul, smul_smul]
    congr 1
    have h2 : (2 : ℝ) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt 2 := two_mul_rpow_neg_half
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc (k : ℝ) * Real.exp (-(T.κ ^ 2 * (k : ℝ) ^ 2) / 4)
        = (Real.sqrt 2)⁻¹ * (Real.sqrt 2 * ((k : ℝ) * Real.exp (-(T.κ ^ 2 * (k : ℝ) ^ 2) / 4))) := by
          field_simp
      _ = _ := by rw [← h2]; ring
  · rw [smul_zero]

/-- The identification paragraph and `kz:eq:Bn`: `B_n^{↓↑} = B_n^{↑↓}`. -/
theorem Bpair_dn_up (T : Torus) (n : ℤ) : Bpair T .dn .up n = Bpair T .up .dn n := by
  rw [Bpair_eq_tsum_nat_dev, Bpair_eq_tsum_nat_dev]
  refine tsum_congr fun k => ?_
  rw [pairTerm_mixed_dev T .dn .up (by decide), pairTerm_mixed_dev T .up .dn (by decide)]

/-- The action of the pair operators on components (the proof of Lemma C.A, "(2) ⇔ (3)", with `comp_cons_cons`): the
component of `B_n^{σ₀σ₁} Ψ` is the combination `Σ_{A+B=n} (A − B) q^{(A−B)²} F_{[A][B]}` of the pair coefficients of the
first two variables. -/
theorem comp_Bpair (T : Torus) {N : ℕ} (σ : Fin (N + 2) → Spin) (n : ℤ) (Ψ : FockSpace T) (w : Fin N → ℂ) :
    comp T (fun i : Fin N => σ i.succ.succ) (toCLM T (Bpair T (σ 0) (σ 1) n) Ψ) w =
      ∑' A : ℤ, ((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n) *
        comp T (fun i : Fin N => σ i.succ.succ)
          (toCLM T (cjs T ((n - A : ℤ) : ZMod T.Nφ) (σ 1) * cjs T (A : ZMod T.Nφ) (σ 0)) Ψ) w := by
  -- the linear functional `M ↦ comp σ'' (M Ψ) w` is continuous (finite dimension) and commutes with the sum
  let φ : FockOp T →ₗ[ℂ] ℂ :=
    { toFun := fun M => comp T (fun i : Fin N => σ i.succ.succ) (toCLM T M Ψ) w
      map_add' := fun M M' => by
        simp only [toCLM, map_add, add_apply, Pi.add_apply]
      map_smul' := fun c M => by
        simp only [toCLM, map_smul, smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hφ : Continuous φ := φ.continuous_of_finiteDimensional
  have hinj : Function.Injective fun A : ℤ => 2 * A - n := fun A B h => by simp only at h; omega
  have hterm : ∀ A : ℤ, BpairTerm_dev T (σ 0) (σ 1) n (2 * A - n) =
      (((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n)) •
        (cjs T ((n - A : ℤ) : ZMod T.Nφ) (σ 1) * cjs T (A : ZMod T.Nφ) (σ 0)) := by
    intro A
    have hmod : (2 * A - n) ≡ n [ZMOD 2] := by
      rw [Int.ModEq]
      omega
    have h1 : (n - (2 * A - n)) / 2 = n - A := by omega
    have h2 : (n + (2 * A - n)) / 2 = A := by omega
    simp only [BpairTerm_dev, hmod, ite_true, h1, h2]
  have hsum : Summable fun A : ℤ => (((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n)) •
      (cjs T ((n - A : ℤ) : ZMod T.Nφ) (σ 1) * cjs T (A : ZMod T.Nφ) (σ 0)) := by
    have hs := summable_BpairTerm_dev T (σ 0) (σ 1) n
    have hsupp : ∀ x ∉ Set.range (fun A : ℤ => 2 * A - n), BpairTerm_dev T (σ 0) (σ 1) n x = 0 := by
      intro x hx
      unfold BpairTerm_dev
      rw [ite_eq_right]
      intro h
      apply hx
      rw [Int.ModEq] at h
      exact ⟨(n + x) / 2, by simp only; omega⟩
    have := (hinj.summable_iff hsupp).2 hs
    simpa only [Function.comp_def, hterm] using this
  have h := (hsum.hasSum.map φ hφ).tsum_eq
  show φ (Bpair T (σ 0) (σ 1) n) = _
  unfold Bpair
  rw [← h]
  refine tsum_congr fun A => ?_
  simp only [Function.comp_apply, φ, LinearMap.coe_mk, AddHom.coe_mk, toCLM, map_smul, smul_apply,
    Pi.smul_apply, smul_eq_mul]

/-! ## Lemma C.A3: the `m = 1` relative amplitude of a pair on the diagonal -/

/-- A two-body holomorphic part `f(z₁, z₂) = Σ_{a,b} ψ_{ab} φ_a(z₁) φ_b(z₂)` (Lemma C.A3: "`Let $\psi=\sum_{a,b\in\Z_L}\psi_{ab}\,\phi_a(z_1)\phi_b(z_2)e^{-(Y_1^2+Y_2^2)/2}\in\kzH_2$ and`"),
in `u`-units with the normalized orbitals. -/
def pairFun (T : Torus) (ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ) (z₁ z₂ : ℂ) : ℂ :=
  ∑ a, ∑ b, ψ a b * orbHol T a z₁ * orbHol T b z₂

/-- **Lemma C.A3**: "`\beta_n(\psi):=\sum_{A+B=n,\ A,B\in\Z}(A-B)\,\kzq^{(A-B)^2}\,\psi_{[A][B]}`" (`A ∈ ℤ`, `B = n − A`). -/
def betaC (T : Torus) (ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ) (n : ℤ) : ℂ :=
  ∑' A : ℤ, ((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n) * ψ (A : ZMod T.Nφ) ((n - A : ℤ) : ZMod T.Nφ)

/-- **Lemma C.A3**: "`Then $\beta_{n+2L}=\beta_n$`". -/
theorem betaC_add_period (T : Torus) (ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ) (n : ℤ) :
    betaC T ψ (n + 2 * (T.Nφ : ℤ)) = betaC T ψ n := by
  -- the paper's proof: "`$(A,B)\mapsto(A+L,B+L)$`"
  unfold betaC
  rw [← (Equiv.addRight (T.Nφ : ℤ)).tsum_eq]
  refine tsum_congr fun A => ?_
  simp only [Equiv.coe_addRight]
  have h1 : 2 * (A + (T.Nφ : ℤ)) - (n + 2 * (T.Nφ : ℤ)) = 2 * A - n := by ring
  have h2 : ((A + (T.Nφ : ℤ) : ℤ) : ZMod T.Nφ) = (A : ZMod T.Nφ) := by
    push_cast
    simp
  have h3 : ((n + 2 * (T.Nφ : ℤ) - (A + (T.Nφ : ℤ)) : ℤ) : ZMod T.Nφ) = ((n - A : ℤ) : ZMod T.Nφ) := by
    push_cast
    simp only [ZMod.natCast_self, mul_zero, add_zero]
  rw [h1, h2, h3]

/-! ### Proof devices for Lemma C.A3 (proof phase, round one; not statements of the paper)

The orbitals as series over `A ≡ j mod L` of `e_A(u) = e^{2πiAu} e^{−κ²A²/2}` (block A's `psiTheta`, with `κL_y = 2π`),
their derivatives termwise (block A's `psiTheta_hasDerivAt`), the Gaussian bounds from Mathlib's
`summable_pow_mul_jacobiTheta₂_term_bound`, and the regrouping of `Σ_{a,b} c_{ab} (Σ_m f(a + mL)) (Σ_m g(b + mL))` into
one sum over `(A, B) ∈ ℤ²` (block A's `hasSum_regroup_dev` in two variables). The paper's computation is then the
change of variables `(A, B) = (A, n − A)` with `A² + B² = (n² + (A − B)²)/2`. -/

/-- The term `e_A(u) = e^{2πiAu} e^{−κ²A²/2}` of the orbital series. -/
def ee_dev (T : Torus) (A : ℤ) (u : ℂ) : ℂ :=
  cexp (2 * π * I * (A : ℂ) * u) * ((Real.exp (-(T.κ ^ 2 * (A : ℝ) ^ 2) / 2) : ℝ) : ℂ)

theorem psiTheta_term_dev (T : Torus) (A : ℤ) (u : ℂ) :
    cexp (((T.κ * (A : ℝ) : ℝ) : ℂ) * (I * ((T.Ly : ℂ) * u)) - (((T.κ * (A : ℝ)) ^ 2 / 2 : ℝ) : ℂ)) =
      ee_dev T A u := by
  have hLy : (T.Ly : ℂ) ≠ 0 := by exact_mod_cast T.Ly_pos.ne'
  unfold ee_dev
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [Torus.κ]
  push_cast
  field_simp
  ring

theorem orbHol_eq_tsum_dev (T : Torus) (j : ZMod T.Nφ) (u : ℂ) :
    orbHol T j u = (cT T : ℂ) * ∑' m : ℤ, ee_dev T ((j.val : ℤ) + m * T.Nφ) u := by
  rw [orbHol_eq_psiTheta_dev]
  unfold psiTheta
  congr 1
  exact tsum_congr fun m => psiTheta_term_dev T _ u

/-- The derivative of the orbital, as a series. -/
def dOrb_dev (T : Torus) (j : ZMod T.Nφ) (u : ℂ) : ℂ :=
  (cT T : ℂ) * ∑' m : ℤ, (2 * π * I * (((j.val : ℤ) + m * T.Nφ : ℤ) : ℂ)) * ee_dev T ((j.val : ℤ) + m * T.Nφ) u

theorem orbHol_hasDerivAt_dev (T : Torus) (j : ZMod T.Nφ) (u : ℂ) : HasDerivAt (orbHol T j) (dOrb_dev T j u) u := by
  have hfun : orbHol T j = fun u => (cT T : ℂ) * psiTheta T j (I * ((T.Ly : ℂ) * u)) :=
    funext (orbHol_eq_psiTheta_dev T j)
  have hg : HasDerivAt (fun u : ℂ => I * ((T.Ly : ℂ) * u)) (I * (T.Ly : ℂ)) u := by
    simpa using ((hasDerivAt_id u).const_mul (T.Ly : ℂ)).const_mul I
  have h := ((psiTheta_hasDerivAt T j (I * ((T.Ly : ℂ) * u))).comp u hg).const_mul (cT T : ℂ)
  rw [hfun]
  refine h.congr_deriv ?_
  unfold dOrb_dev
  congr 1
  rw [← tsum_mul_right]
  refine tsum_congr fun m => ?_
  rw [← psiTheta_term_dev]
  have hk : ((T.κ * ((((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) * (I * (T.Ly : ℂ)) =
      2 * π * I * ((((j.val : ℤ) + m * (T.Nφ : ℤ) : ℤ)) : ℂ) := by
    have hLy : (T.Ly : ℂ) ≠ 0 := by exact_mod_cast T.Ly_pos.ne'
    simp only [Torus.κ]
    push_cast
    field_simp
  rw [mul_right_comm, hk]

theorem norm_ee_le_dev (T : Torus) (A : ℤ) (u : ℂ) :
    ‖ee_dev T A u‖ ≤ Real.exp (-π * ((T.κ ^ 2 / (2 * π)) * (A : ℝ) ^ 2 - 2 * |u.im| * |(A : ℝ)|)) := by
  unfold ee_dev
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hre : (2 * π * I * (A : ℂ) * u).re = -(2 * π * (A : ℝ) * u.im) := by
    rw [show (2 * π * I * (A : ℂ) * u) = I * (((2 * π * (A : ℝ) : ℝ) : ℂ) * u) by push_cast; ring,
      Complex.I_mul_re, Complex.im_ofReal_mul]
  rw [hre]
  have e : |2 * π * (A : ℝ) * u.im| = 2 * π * |u.im| * |(A : ℝ)| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h2 : -π * ((T.κ ^ 2 / (2 * π)) * (A : ℝ) ^ 2 - 2 * |u.im| * |(A : ℝ)|) =
      -(T.κ ^ 2 * (A : ℝ) ^ 2) / 2 + 2 * π * |u.im| * |(A : ℝ)| := by
    field_simp
    ring
  rw [h2]
  linarith [neg_le_abs (2 * π * (A : ℝ) * u.im)]

theorem kappa_pos_dev (T : Torus) : 0 < T.κ := by
  unfold Torus.κ
  exact div_pos (by positivity) T.Ly_pos

theorem summable_ee_dev (T : Torus) (u : ℂ) (k : ℕ) :
    Summable fun A : ℤ => |(A : ℝ)| ^ k * ‖ee_dev T A u‖ := by
  have hT : 0 < T.κ ^ 2 / (2 * π) := by
    have := kappa_pos_dev T
    positivity
  refine Summable.of_nonneg_of_le (fun A => by positivity) (fun A => ?_)
    (summable_pow_mul_jacobiTheta₂_term_bound |u.im| hT k)
  rw [Int.cast_abs]
  exact mul_le_mul_of_nonneg_left (norm_ee_le_dev T A u) (pow_nonneg (abs_nonneg _) k)

theorem summable_norm_ee_dev (T : Torus) (u : ℂ) : Summable fun A : ℤ => ‖ee_dev T A u‖ := by
  simpa using summable_ee_dev T u 0

theorem summable_norm_dee_dev (T : Torus) (u : ℂ) :
    Summable fun A : ℤ => ‖(2 * π * I * (A : ℂ)) * ee_dev T A u‖ := by
  have h := (summable_ee_dev T u 1).mul_left (2 * π)
  refine Summable.of_nonneg_of_le (fun A => norm_nonneg _) (fun A => ?_) h
  have e : ‖(2 * π * I * (A : ℂ))‖ = 2 * π * |(A : ℝ)| := by
    rw [show (2 * π * I * (A : ℂ)) = I * (((2 * π * (A : ℝ) : ℝ)) : ℂ) by push_cast; ring, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  rw [norm_mul, e, pow_one]
  exact le_of_eq (by ring)

/-- A combination `c_{[A][B]} f(A) g(B)` of two norm-summable sequences is summable on `ℤ²`. -/
theorem summable_cmul_dev (T : Torus) (c : ZMod T.Nφ → ZMod T.Nφ → ℂ) {f g : ℤ → ℂ}
    (hf : Summable fun A => ‖f A‖) (hg : Summable fun B => ‖g B‖) :
    Summable fun p : ℤ × ℤ => c (p.1 : ZMod T.Nφ) (p.2 : ZMod T.Nφ) * (f p.1 * g p.2) := by
  have hC : ∀ a b, ‖c a b‖ ≤ ∑ a', ∑ b', ‖c a' b'‖ := fun a b =>
    (Finset.single_le_sum (f := fun b' => ‖c a b'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a' => ∑ b', ‖c a' b'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))
  have hfg : Summable fun p : ℤ × ℤ => ‖f p.1‖ * ‖g p.2‖ :=
    summable_mul_of_summable_norm (f := fun A => ‖f A‖) (g := fun B => ‖g B‖) (by simpa using hf)
      (by simpa using hg)
  refine Summable.of_norm_bounded (hfg.mul_left (∑ a', ∑ b', ‖c a' b'‖)) fun p => ?_
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC _ _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- `Σ_{a,b} c_{ab} (Σ_m f(a + mL)) (Σ_m g(b + mL)) = Σ_{(A,B) ∈ ℤ²} c_{[A][B]} f(A) g(B)`. -/
theorem regroup2_dev (T : Torus) (c : ZMod T.Nφ → ZMod T.Nφ → ℂ) {f g : ℤ → ℂ}
    (hf : Summable fun A => ‖f A‖) (hg : Summable fun B => ‖g B‖) :
    ∑ a, ∑ b, c a b * ((∑' m : ℤ, f ((a.val : ℤ) + m * T.Nφ)) * ∑' m : ℤ, g ((b.val : ℤ) + m * T.Nφ)) =
      ∑' p : ℤ × ℤ, c (p.1 : ZMod T.Nφ) (p.2 : ZMod T.Nφ) * (f p.1 * g p.2) := by
  have hK := summable_cmul_dev T c hf hg
  set K : ℤ × ℤ → ℂ := fun p => c (p.1 : ZMod T.Nφ) (p.2 : ZMod T.Nφ) * (f p.1 * g p.2) with hKdef
  let E : (ZMod T.Nφ × ZMod T.Nφ) × (ℤ × ℤ) ≃ ℤ × ℤ :=
    (Equiv.prodProdProdComm (ZMod T.Nφ) (ZMod T.Nφ) ℤ ℤ).trans ((idxEquiv_dev T).prodCongr (idxEquiv_dev T))
  have h1 : HasSum (K ∘ E) (∑' p, K p) := (E.hasSum_iff).2 hK.hasSum
  have hcast : ∀ (a : ZMod T.Nφ) (m : ℤ), (((a.val : ℤ) + m * T.Nφ : ℤ) : ZMod T.Nφ) = a := by
    intro a m
    push_cast
    simp
  have hinj : ∀ a : ZMod T.Nφ, Function.Injective fun m : ℤ => (a.val : ℤ) + m * T.Nφ := by
    intro a m m' h
    have hN : (T.Nφ : ℤ) ≠ 0 := by exact_mod_cast T.Nφ_pos.ne'
    simp only [add_right_inj] at h
    exact mul_right_cancel₀ hN h
  have hKE : ∀ (ab : ZMod T.Nφ × ZMod T.Nφ) (mm : ℤ × ℤ), (K ∘ E) (ab, mm) =
      c ab.1 ab.2 * (f ((ab.1.val : ℤ) + mm.1 * T.Nφ) * g ((ab.2.val : ℤ) + mm.2 * T.Nφ)) := by
    rintro ⟨a, b⟩ ⟨m, m'⟩
    show c (((a.val : ℤ) + m * T.Nφ : ℤ) : ZMod T.Nφ) (((b.val : ℤ) + m' * T.Nφ : ℤ) : ZMod T.Nφ) *
      (f ((a.val : ℤ) + m * T.Nφ) * g ((b.val : ℤ) + m' * T.Nφ)) = _
    rw [hcast, hcast]
  have h2 : ∀ ab : ZMod T.Nφ × ZMod T.Nφ, HasSum (fun mm : ℤ × ℤ => (K ∘ E) (ab, mm))
      (c ab.1 ab.2 * ((∑' m : ℤ, f ((ab.1.val : ℤ) + m * T.Nφ)) * ∑' m : ℤ, g ((ab.2.val : ℤ) + m * T.Nφ))) := by
    intro ab
    have hf' : Summable fun m : ℤ => ‖f ((ab.1.val : ℤ) + m * T.Nφ)‖ := hf.comp_injective (hinj ab.1)
    have hg' : Summable fun m : ℤ => ‖g ((ab.2.val : ℤ) + m * T.Nφ)‖ := hg.comp_injective (hinj ab.2)
    have hprod := (summable_mul_of_summable_norm hf' hg').hasSum
    rw [← tsum_mul_tsum_of_summable_norm hf' hg'] at hprod
    have := hprod.mul_left (c ab.1 ab.2)
    simpa only [hKE] using this
  have h3 := h1.prod_fiberwise h2
  rw [← h3.tsum_eq, tsum_fintype, Fintype.sum_prod_type]

/-- The derivative of a two-body function in its first variable on the diagonal. -/
theorem pairFun_deriv_left_dev (T : Torus) (ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ) (W : ℂ) :
    deriv (fun z => pairFun T ψ z W) W = ∑ a, ∑ b, ψ a b * dOrb_dev T a W * orbHol T b W := by
  refine HasDerivAt.deriv ?_
  unfold pairFun
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
  exact ((orbHol_hasDerivAt_dev T a W).const_mul (ψ a b)).mul_const (orbHol T b W)

/-- The derivative of a two-body function in its second variable on the diagonal. -/
theorem pairFun_deriv_right_dev (T : Torus) (ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ) (W : ℂ) :
    deriv (fun z => pairFun T ψ W z) W = ∑ a, ∑ b, ψ a b * orbHol T a W * dOrb_dev T b W := by
  refine HasDerivAt.deriv ?_
  unfold pairFun
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
  exact (orbHol_hasDerivAt_dev T b W).const_mul (ψ a b * orbHol T a W)

/-- `e_A(W) e_{n−A}(W) = e^{2πinW} q^{n²} q^{(2A−n)²}` (`A² + (n − A)² = (n² + (2A − n)²)/2`). -/
theorem ee_mul_ee_dev (T : Torus) (A n : ℤ) (W : ℂ) :
    ee_dev T A W * ee_dev T (n - A) W = cexp (2 * π * I * (n : ℂ) * W) * qw T n * qw T (2 * A - n) := by
  unfold ee_dev
  rw [qw_eq, qw_eq]
  simp only [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The sum over `A` of the term of the series of `D f(W, W)` for fixed `n = A + B`. -/
theorem lemA3_term_dev (T : Torus) (ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ) (W : ℂ) (n A : ℤ) :
    ψ (A : ZMod T.Nφ) ((n - A : ℤ) : ZMod T.Nφ) * ((2 * π * I * (A : ℂ)) * ee_dev T A W * ee_dev T (n - A) W) -
      ψ (A : ZMod T.Nφ) ((n - A : ℤ) : ZMod T.Nφ) * (ee_dev T A W * ((2 * π * I * ((n - A : ℤ) : ℂ)) * ee_dev T (n - A) W)) =
      (2 * π * I * (cexp (2 * π * I * (n : ℂ) * W) * qw T n)) *
        (((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n) * ψ (A : ZMod T.Nφ) ((n - A : ℤ) : ZMod T.Nφ)) := by
  have h := ee_mul_ee_dev T A n W
  calc _ = ψ (A : ZMod T.Nφ) ((n - A : ℤ) : ZMod T.Nφ) * (2 * π * I * ((A : ℂ) - ((n - A : ℤ) : ℂ))) *
        (ee_dev T A W * ee_dev T (n - A) W) := by ring
    _ = _ := by
        rw [h]
        push_cast
        ring

/-- The Gaussian `e^{−κ²k²/4}` is summable over `ℤ`, with the weight `|k|` too. -/
theorem summable_gauss_dev (T : Torus) (k : ℕ) :
    Summable fun d : ℤ => |(d : ℝ)| ^ k * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4) := by
  have hT : 0 < T.κ ^ 2 / (4 * π) := by
    have := kappa_pos_dev T
    positivity
  refine (summable_pow_mul_jacobiTheta₂_term_bound 0 hT k).congr fun d => ?_
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [Int.cast_abs]
  congr 2
  field_simp
  ring

/-- The uniform bound `|β_n(ψ)| ≤ (Σ_{ab} |ψ_ab|) Σ_d |d| e^{−κ²d²/4}`. -/
def betaBound_dev (T : Torus) (ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ) : ℝ :=
  (∑ a, ∑ b, ‖ψ a b‖) * ∑' d : ℤ, |(d : ℝ)| ^ 1 * Real.exp (-(T.κ ^ 2 * (d : ℝ) ^ 2) / 4)

theorem betaBound_nonneg_dev (T : Torus) (ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ) : 0 ≤ betaBound_dev T ψ := by
  unfold betaBound_dev
  refine mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_
  exact tsum_nonneg fun d => by positivity

theorem norm_betaC_le_dev (T : Torus) (ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ) (n : ℤ) :
    ‖betaC T ψ n‖ ≤ betaBound_dev T ψ := by
  have hgs := summable_gauss_dev T 1
  have hψ : ∀ a b, ‖ψ a b‖ ≤ ∑ a', ∑ b', ‖ψ a' b'‖ := fun a b =>
    (Finset.single_le_sum (f := fun b' => ‖ψ a b'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a' => ∑ b', ‖ψ a' b'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))
  have hM : 0 ≤ ∑ a', ∑ b', ‖ψ a' b'‖ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hterm : ∀ A : ℤ, ‖((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n) * ψ (A : ZMod T.Nφ) ((n - A : ℤ) : ZMod T.Nφ)‖ ≤
      (∑ a', ∑ b', ‖ψ a' b'‖) *
        (|((2 * A - n : ℤ) : ℝ)| ^ 1 * Real.exp (-(T.κ ^ 2 * ((2 * A - n : ℤ) : ℝ) ^ 2) / 4)) := by
    intro A
    rw [norm_mul, norm_mul, qw_eq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_intCast,
      pow_one]
    have := hψ (A : ZMod T.Nφ) ((n - A : ℤ) : ZMod T.Nφ)
    have hpos : 0 ≤ |((2 * A - n : ℤ) : ℝ)| * Real.exp (-(T.κ ^ 2 * ((2 * A - n : ℤ) : ℝ) ^ 2) / 4) := by
      positivity
    nlinarith
  have hinj : Function.Injective fun A : ℤ => 2 * A - n := fun A B h => by simp only at h; omega
  have hs2 : Summable fun A : ℤ => (∑ a', ∑ b', ‖ψ a' b'‖) *
      (|((2 * A - n : ℤ) : ℝ)| ^ 1 * Real.exp (-(T.κ ^ 2 * ((2 * A - n : ℤ) : ℝ) ^ 2) / 4)) :=
    (hgs.comp_injective hinj).mul_left _
  have hs1 : Summable fun A : ℤ =>
      ‖((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n) * ψ (A : ZMod T.Nφ) ((n - A : ℤ) : ZMod T.Nφ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hs2
  unfold betaC betaBound_dev
  calc _ ≤ _ := norm_tsum_le_tsum_norm hs1
    _ ≤ _ := hs1.tsum_le_tsum hterm hs2
    _ = (∑ a', ∑ b', ‖ψ a' b'‖) *
          ∑' A : ℤ, |((2 * A - n : ℤ) : ℝ)| ^ 1 * Real.exp (-(T.κ ^ 2 * ((2 * A - n : ℤ) : ℝ) ^ 2) / 4) :=
        tsum_mul_left
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        exact (hgs.comp_injective hinj).tsum_le_tsum_of_inj (fun A : ℤ => 2 * A - n) hinj
          (fun d _ => by positivity) (fun A => le_refl _) hgs

/-- **Lemma C.A3**: "`(\kzD f)(Z,Z)=i\kappa\sum_{n\in\Z}e^{i\kappa nZ+i\pi\tau n^2/(2L)}\,\beta_n(\psi)`" — in `u`-units
(`z = L_1 u`, `κL_1 = 2π`) and with the normalized orbitals (the factor `(L_y√π)^{−1}`):
`(∂₁ − ∂₂)f(W, W) = 2πi (L_y√π)^{−1} Σ_n e^{2πinW} q^{n²} β_n(ψ)`. -/
theorem lemA3 (T : Torus) (ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ) (W : ℂ) :
    deriv (fun z => pairFun T ψ z W) W - deriv (fun z => pairFun T ψ W z) W =
      2 * π * I * (cT T : ℂ) ^ 2 * ∑' n : ℤ, cexp (2 * π * I * (n : ℂ) * W) * qw T n * betaC T ψ n := by
  rw [pairFun_deriv_left_dev, pairFun_deriv_right_dev]
  have hf₀s : Summable fun A : ℤ => ‖ee_dev T A W‖ := summable_norm_ee_dev T W
  have hf₁s : Summable fun A : ℤ => ‖(2 * π * I * (A : ℂ)) * ee_dev T A W‖ := summable_norm_dee_dev T W
  have h₁ := regroup2_dev T ψ hf₁s hf₀s
  have h₂ := regroup2_dev T ψ hf₀s hf₁s
  have hK₁ := summable_cmul_dev T ψ hf₁s hf₀s
  have hK₂ := summable_cmul_dev T ψ hf₀s hf₁s
  -- the two derivatives as combinations of the orbital series
  have hL : (∑ a, ∑ b, ψ a b * dOrb_dev T a W * orbHol T b W) - ∑ a, ∑ b, ψ a b * orbHol T a W * dOrb_dev T b W =
      (cT T : ℂ) ^ 2 * ((∑ a, ∑ b, ψ a b * ((∑' m : ℤ, (2 * π * I * (((a.val : ℤ) + m * T.Nφ : ℤ) : ℂ)) *
          ee_dev T ((a.val : ℤ) + m * T.Nφ) W) * ∑' m : ℤ, ee_dev T ((b.val : ℤ) + m * T.Nφ) W)) -
        ∑ a, ∑ b, ψ a b * ((∑' m : ℤ, ee_dev T ((a.val : ℤ) + m * T.Nφ) W) *
          ∑' m : ℤ, (2 * π * I * (((b.val : ℤ) + m * T.Nφ : ℤ) : ℂ)) * ee_dev T ((b.val : ℤ) + m * T.Nφ) W)) := by
    simp only [dOrb_dev, orbHol_eq_tsum_dev, mul_sub, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_ <;> ring
  rw [hL, h₁, h₂, ← hK₁.tsum_sub hK₂]
  -- the change of variables `(A, B) = (A, n − A)` and the sum over `A` for fixed `n`
  set Kd : ℤ × ℤ → ℂ := fun p =>
    ψ (p.1 : ZMod T.Nφ) (p.2 : ZMod T.Nφ) * ((2 * π * I * (p.1 : ℂ)) * ee_dev T p.1 W * ee_dev T p.2 W) -
      ψ (p.1 : ZMod T.Nφ) (p.2 : ZMod T.Nφ) * (ee_dev T p.1 W * ((2 * π * I * (p.2 : ℂ)) * ee_dev T p.2 W)) with hKd
  have hKs : Summable Kd := hK₁.sub hK₂
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun p => (p.1 + p.2, p.1)
      left_inv := fun q => by simp
      right_inv := fun p => by simp }
  have hiter : ∑' n : ℤ, ∑' A : ℤ, (Kd ∘ e) (n, A) = ∑' p, Kd p :=
    (((e.hasSum_iff).2 hKs.hasSum).prod_fiberwise fun n =>
      (((e.summable_iff).2 hKs).comp_injective (Prod.mk_right_injective n)).hasSum).tsum_eq
  have hfib : ∀ n : ℤ, ∑' A : ℤ, (Kd ∘ e) (n, A) =
      2 * π * I * (cexp (2 * π * I * (n : ℂ) * W) * qw T n * betaC T ψ n) := by
    intro n
    have hA : ∀ A : ℤ, (Kd ∘ e) (n, A) = (2 * π * I * (cexp (2 * π * I * (n : ℂ) * W) * qw T n)) *
        (((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n) * ψ (A : ZMod T.Nφ) ((n - A : ℤ) : ZMod T.Nφ)) := by
      intro A
      exact lemA3_term_dev T ψ W n A
    rw [tsum_congr hA, tsum_mul_left]
    unfold betaC
    ring
  rw [← hiter, tsum_congr hfib, tsum_mul_left]
  ring

/-- **Lemma C.A3**: "`Finally, $(\kzD f)(Z,Z)\equiv0$ forces every $\beta_n=0$`" (a Fourier series in `Re W`). -/
theorem betaC_eq_zero_of_diag (T : Torus) (ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ)
    (h : ∀ W : ℂ, deriv (fun z => pairFun T ψ z W) W - deriv (fun z => pairFun T ψ W z) W = 0) (n : ℤ) :
    betaC T ψ n = 0 := by
  -- the series of Lemma C.A3 vanishes on the real line
  have hc : (2 * π * I * (cT T : ℂ) ^ 2) ≠ 0 := by
    have hcT : (cT T : ℂ) ≠ 0 := by
      have : 0 < cT T := by
        unfold cT
        exact Real.rpow_pos_of_pos (mul_pos T.Ly_pos (Real.sqrt_pos.2 Real.pi_pos)) _
      exact_mod_cast this.ne'
    simp [Complex.I_ne_zero, Real.pi_ne_zero, hcT]
  have hser : ∀ t : ℝ, ∑' k : ℤ, cexp (2 * π * I * (k : ℂ) * (t : ℂ)) * qw T k * betaC T ψ k = 0 := by
    intro t
    have := h (t : ℂ)
    rw [lemA3] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  -- its `n`-th Fourier coefficient on `[0, 1]` (as F0's `coef_thetaBasis`)
  let f : ℤ → C(ℝ, ℂ) := fun k =>
    ⟨fun t => qw T k * betaC T ψ k * cexp ((2 * π * I * ((k - n : ℤ) : ℂ)) * t), by fun_prop⟩
  have hpt : ∀ t : ℝ, (∑' k : ℤ, cexp (2 * π * I * (k : ℂ) * (t : ℂ)) * qw T k * betaC T ψ k) *
      cexp (-(2 * π * I * (n : ℂ)) * t) = ∑' k : ℤ, f k t := by
    intro t
    rw [← tsum_mul_right]
    refine tsum_congr fun k => ?_
    simp only [f, ContinuousMap.coe_mk]
    have hx : cexp (2 * π * I * (k : ℂ) * (t : ℂ)) * cexp (-(2 * π * I * (n : ℂ)) * t) =
        cexp ((2 * π * I * ((k - n : ℤ) : ℂ)) * t) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc _ = qw T k * betaC T ψ k * (cexp (2 * π * I * (k : ℂ) * (t : ℂ)) * cexp (-(2 * π * I * (n : ℂ)) * t)) := by
          ring
      _ = _ := by rw [hx]
  have hbound : ∀ k : ℤ, ‖(f k).restrict (⟨Set.uIcc 0 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ ≤
      betaBound_dev T ψ * (|(k : ℝ)| ^ 0 * Real.exp (-(T.κ ^ 2 * (k : ℝ) ^ 2) / 4)) := by
    intro k
    have hB0 := betaBound_nonneg_dev T ψ
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
    simp only [ContinuousMap.restrict_apply, f, ContinuousMap.coe_mk, norm_mul]
    have h1 : ‖cexp ((2 * π * I * ((k - n : ℤ) : ℂ)) * (x : ℝ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [h1, mul_one, qw_eq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, pow_zero, one_mul]
    have hb := norm_betaC_le_dev T ψ k
    have hE := (Real.exp_pos (-(T.κ ^ 2 * (k : ℝ) ^ 2) / 4)).le
    nlinarith
  have hsum : Summable fun k : ℤ => ‖(f k).restrict
      (⟨Set.uIcc 0 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound ((summable_gauss_dev T 0).mul_left _)
  have hhas := intervalIntegral.hasSum_intervalIntegral_of_summable_norm (a := 0) (b := 1) hsum
  have e : ∫ x in (0:ℝ)..1, ∑' k, f k x = 0 := by
    have hz : ∀ x : ℝ, ∑' k, f k x = 0 := fun x => by rw [← hpt, hser, zero_mul]
    simp [hz]
  rw [e] at hhas
  have hint : ∀ k : ℤ, ∫ x in (0:ℝ)..1, f k x = if k = n then qw T n * betaC T ψ n else 0 := by
    intro k
    simp only [f, ContinuousMap.coe_mk]
    rw [ThetaDev.intervalIntegral_exp_int]
    by_cases hk : k = n
    · subst hk
      simp
    · have hkn : k - n ≠ 0 := sub_ne_zero.2 hk
      simp [hkn, hk]
  have hfun : (fun k : ℤ => ∫ x in (0:ℝ)..1, f k x) =
      fun k => if k = n then qw T n * betaC T ψ n else 0 := funext hint
  rw [hfun] at hhas
  have h0 := hhas.unique (hasSum_ite_eq n _)
  have hq : qw T n ≠ 0 := by
    unfold qw
    exact Complex.exp_ne_zero _
  exact (mul_eq_zero.1 h0.symm).resolve_left hq

/-! ## (C1), (C2) and Lemma C.A, (2) ⇒ (3) -/

/-- "`Write $\kzD_{st}:=\partial_s-\partial_t$ and $[\,\cdot\,]_{s=t}$ for restriction.`" — `(D_{st} f)(u)`, the partial
derivatives being the one-variable derivatives of the slices. -/
def relDeriv {N : ℕ} (f : (Fin N → ℂ) → ℂ) (s t : Fin N) (u : Fin N → ℂ) : ℂ :=
  deriv (fun z => f (Function.update u s z)) (u s) - deriv (fun z => f (Function.update u t z)) (u t)

/-- `f` vanishes to order `≥ k` along the divisor `{u_s − u_t ∈ Λ_u}`, measured along the transverse coordinate `u_s`:
the slice `z ↦ f(u with u_s := z)` and its first `k − 1` derivatives vanish at every `u_t + λ`, `λ ∈ Λ_u`. -/
def VanishesAlong (τ : ℍ) {N : ℕ} (f : (Fin N → ℂ) → ℂ) (s t : Fin N) (k : ℕ) : Prop :=
  ∀ (u : Fin N → ℂ) (l : ℂ), l ∈ Λu τ → ∀ j < k,
    iteratedDeriv j (fun z => f (Function.update u s z)) (u t + l) = 0

/-- **Lemma C.A (2), (C1)**: "`\textup{(C1)} For all $a<b$, $F$ vanishes to order $\ge3$ along the divisor $\{x_a-x_b\in\Lambda\}$, and likewise for the $y$'s.`"
(in `u`-units, `Λ_u`). -/
def C1 (τ : ℍ) (n m : ℕ) (f : (Fin (n + m) → ℂ) → ℂ) : Prop :=
  ∀ s t : Fin (n + m), s < t → SameSpecies n s t → VanishesAlong τ f s t 3

/-- **Lemma C.A (2), (C2)**: "`\textup{(C2)} For all $a,k$, $[\kzD_{x_ay_k}F]_{x_a=y_k}=0$ identically, on the covering diagonal $x_a=y_k$ of $\C^N$.`" -/
def C2 (n m : ℕ) (f : (Fin (n + m) → ℂ) → ℂ) : Prop :=
  ∀ s t : Fin (n + m), (s : ℕ) < n → n ≤ (t : ℕ) → ∀ u : Fin (n + m) → ℂ, u s = u t → relDeriv f s t u = 0

/-! ### Proof devices for Lemma C.A, (2) ⇒ (3) (proof phase, round one; not statements of the paper)

The paper's route: "`Expand $F$ in its first up and first down variables`". For any two variables `s ≠ t` of the
canonical component a permutation brings them to the first two places (`comp_perm`); there the two-body coefficients
`F_{ab}` are the components of `c_{bσ'} c_{aσ} Ψ` (`comp_cons_cons`), the diagonal relative derivative of the pair is
Lemma C.A3's series, so every `β_n` vanishes (`betaC_eq_zero_of_diag`); `β_n` is the component of `B_n^{σσ'} Ψ`
(`comp_Bpair`), which has the spin content of the remaining variables, so `B_n^{σσ'} Ψ = 0` (`comp_eq_zero_dev`).
(C1) gives the diagonal condition for a same-species pair (vanishing to order `≥ 2` along the divisor, and the
antisymmetry), (C2) for a mixed pair. A sector with fewer particles of a spin than the pair removes is annihilated by
the pair operator because `N_τ ≥ 0` (`eq_zero_of_Nsig_neg_dev`). -/

/-- `c_{bσ'} c_{aσ}` lowers the number of `τ`-particles by `[σ = τ] + [σ' = τ]`. -/
theorem Nsig_pair_dev (T : Torus) (τ s s' : Spin) (a b : ZMod T.Nφ) (k : ℂ) {Ψ : FockSpace T}
    (hΨ : toCLM T (Nsig T τ) Ψ = k • Ψ) :
    toCLM T (Nsig T τ) (toCLM T (cjs T b s' * cjs T a s) Ψ) =
      (k - (if s = τ then 1 else 0) - (if s' = τ then 1 else 0)) • toCLM T (cjs T b s' * cjs T a s) Ψ := by
  have e : toCLM T (cjs T b s' * cjs T a s) Ψ = toCLM T (cjs T b s') (toCLM T (cjs T a s) Ψ) := by
    simp only [toCLM, map_mul, mul_apply_eq_comp]
  rw [e]
  exact Nsig_cjs_dev T τ s' b _ (Nsig_cjs_dev T τ s a k hΨ)

/-- The terms of `B_n^{σσ'}`, indexed by `A`, are summable in the operators (as in `comp_Bpair`). -/
theorem summable_BpairA_dev (T : Torus) (σ σ' : Spin) (n : ℤ) :
    Summable fun A : ℤ => (((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n)) •
      (cjs T ((n - A : ℤ) : ZMod T.Nφ) σ' * cjs T (A : ZMod T.Nφ) σ) := by
  have hinj : Function.Injective fun A : ℤ => 2 * A - n := fun A B h => by simp only at h; omega
  have hterm : ∀ A : ℤ, BpairTerm_dev T σ σ' n (2 * A - n) =
      (((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n)) •
        (cjs T ((n - A : ℤ) : ZMod T.Nφ) σ' * cjs T (A : ZMod T.Nφ) σ) := by
    intro A
    have hmod : (2 * A - n) ≡ n [ZMOD 2] := by
      rw [Int.ModEq]
      omega
    have h1 : (n - (2 * A - n)) / 2 = n - A := by omega
    have h2 : (n + (2 * A - n)) / 2 = A := by omega
    simp only [BpairTerm_dev, hmod, ite_true, h1, h2]
  have hs := summable_BpairTerm_dev T σ σ' n
  have hsupp : ∀ x ∉ Set.range (fun A : ℤ => 2 * A - n), BpairTerm_dev T σ σ' n x = 0 := by
    intro x hx
    unfold BpairTerm_dev
    rw [ite_eq_right]
    intro h
    apply hx
    rw [Int.ModEq] at h
    exact ⟨(n + x) / 2, by simp only; omega⟩
  have := (hinj.summable_iff hsupp).2 hs
  simpa only [Function.comp_def, hterm] using this

/-- `B_n^{σσ'} Ψ` as the sum of its terms applied to `Ψ`. -/
theorem Bpair_hasSum_dev (T : Torus) (σ σ' : Spin) (n : ℤ) (Ψ : FockSpace T) :
    HasSum (fun A : ℤ => (((2 * A - n : ℤ) : ℂ) * qw T (2 * A - n)) •
      toCLM T (cjs T ((n - A : ℤ) : ZMod T.Nφ) σ' * cjs T (A : ZMod T.Nφ) σ) Ψ) (toCLM T (Bpair T σ σ' n) Ψ) := by
  let φ : FockOp T →ₗ[ℂ] FockSpace T :=
    { toFun := fun M => toCLM T M Ψ
      map_add' := fun M M' => by
        simp only [toCLM, map_add, add_apply]
      map_smul' := fun c M => by
        simp only [toCLM, map_smul, smul_apply, RingHom.id_apply] }
  have hφ : Continuous φ := φ.continuous_of_finiteDimensional
  have h := (summable_BpairA_dev T σ σ' n).hasSum.map φ hφ
  unfold Bpair
  convert h using 1
  funext A
  simp only [Function.comp_apply, φ, LinearMap.coe_mk, AddHom.coe_mk, toCLM, map_smul, smul_apply]

/-- `B_n^{σσ'}` annihilates a vector with fewer `τ`-particles than the pair removes. -/
theorem Bpair_eq_zero_of_count_dev (T : Torus) (σ σ' : Spin) (k : ℤ) {Ψ : FockSpace T} (τ : Spin) (c : ℕ)
    (hΨ : toCLM T (Nsig T τ) Ψ = (c : ℂ) • Ψ)
    (hc : c < (if σ = τ then 1 else 0) + (if σ' = τ then 1 else 0)) :
    toCLM T (Bpair T σ σ' k) Ψ = 0 := by
  have hc' : (c : ℝ) < (if σ = τ then 1 else 0) + (if σ' = τ then 1 else 0) := by
    have := (Nat.cast_lt (α := ℝ)).2 hc
    push_cast at this
    exact this
  have hterm : ∀ A : ℤ, toCLM T (cjs T ((k - A : ℤ) : ZMod T.Nφ) σ' * cjs T (A : ZMod T.Nφ) σ) Ψ = 0 := by
    intro A
    refine eq_zero_of_Nsig_neg_dev T τ ((c : ℝ) - (if σ = τ then 1 else 0) - (if σ' = τ then 1 else 0))
      (by linarith) ?_
    rw [Nsig_pair_dev T τ σ σ' _ _ _ hΨ]
    congr 1
    split_ifs <;> push_cast <;> ring
  have hs := Bpair_hasSum_dev T σ σ' k Ψ
  simp only [hterm, smul_zero] at hs
  exact hs.unique hasSum_zero

/-- The pair of the first two variables: if the diagonal relative derivative of the component in them vanishes, then
`B_n^{σ₀σ₁} Ψ = 0`. -/
theorem Bpair_eq_zero_core_dev (T : Torus) {N : ℕ} (σ : Fin (N + 2) → Spin) {Ψ : FockSpace T}
    (hN : ∀ τ : Spin, toCLM T (Nsig T τ) Ψ = ((spinCount_dev σ τ : ℕ) : ℂ) • Ψ)
    (hdiag : ∀ (W : ℂ) (w : Fin N → ℂ),
      relDeriv (comp T σ Ψ) 0 1 (Fin.cons W (Fin.cons W w : Fin (N + 1) → ℂ)) = 0)
    (k : ℤ) : toCLM T (Bpair T (σ 0) (σ 1) k) Ψ = 0 := by
  -- the component of `B_k Ψ` for the remaining spins is `β_k` of the pair coefficients, which vanishes
  have hcomp : ∀ w : Fin N → ℂ,
      comp T (fun i : Fin N => σ i.succ.succ) (toCLM T (Bpair T (σ 0) (σ 1) k) Ψ) w = 0 := by
    intro w
    let ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ := fun a b =>
      comp T (fun i : Fin N => σ i.succ.succ) (toCLM T (cjs T b (σ 1) * cjs T a (σ 0)) Ψ) w
    have hpair : ∀ z₀ z₁ : ℂ,
        pairFun T ψ z₀ z₁ = comp T σ Ψ (Fin.cons z₀ (Fin.cons z₁ w : Fin (N + 1) → ℂ)) := by
      intro z₀ z₁
      rw [comp_cons_cons]
      unfold pairFun
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have hd : ∀ W : ℂ, deriv (fun z => pairFun T ψ z W) W - deriv (fun z => pairFun T ψ W z) W = 0 := by
      intro W
      have h := hdiag W w
      unfold relDeriv at h
      have e0 : ∀ z : ℂ, Function.update (Fin.cons W (Fin.cons W w : Fin (N + 1) → ℂ) : Fin (N + 2) → ℂ) 0 z =
          Fin.cons z (Fin.cons W w : Fin (N + 1) → ℂ) := fun z => by
        rw [Fin.update_cons_zero]
      have e1 : ∀ z : ℂ, Function.update (Fin.cons W (Fin.cons W w : Fin (N + 1) → ℂ) : Fin (N + 2) → ℂ) 1 z =
          Fin.cons W (Fin.cons z w : Fin (N + 1) → ℂ) := fun z => by
        rw [← Fin.succ_zero_eq_one', ← Fin.cons_update, Fin.update_cons_zero]
      simp only [e0, e1, Fin.cons_zero, Fin.cons_one] at h
      simp only [hpair]
      exact h
    have hβ := betaC_eq_zero_of_diag T ψ hd k
    rw [comp_Bpair]
    exact hβ
  -- `B_k Ψ` has the spin content of the remaining variables
  have hσ : σ = Fin.cons (σ 0) (Fin.cons (σ 1) (fun i : Fin N => σ i.succ.succ) : Fin (N + 1) → Spin) := by
    funext i
    refine Fin.cases rfl (fun i => Fin.cases rfl (fun j => rfl) i) i
  have hcount : ∀ τ : Spin, ((spinCount_dev σ τ : ℕ) : ℂ) - (if σ 0 = τ then 1 else 0) - (if σ 1 = τ then 1 else 0) =
      ((spinCount_dev (fun i : Fin N => σ i.succ.succ) τ : ℕ) : ℂ) := by
    intro τ
    have hc : spinCount_dev σ τ = (if σ 0 = τ then 1 else 0) +
        ((if σ 1 = τ then 1 else 0) + spinCount_dev (fun i : Fin N => σ i.succ.succ) τ) := by
      conv_lhs => rw [hσ]
      rw [spinCount_cons_dev, spinCount_cons_dev]
    rw [hc]
    push_cast
    ring
  have hrest : ∀ τ : Spin, toCLM T (Nsig T τ) (toCLM T (Bpair T (σ 0) (σ 1) k) Ψ) =
      ((spinCount_dev (fun i : Fin N => σ i.succ.succ) τ : ℕ) : ℂ) • toCLM T (Bpair T (σ 0) (σ 1) k) Ψ := by
    intro τ
    have hs := Bpair_hasSum_dev T (σ 0) (σ 1) k Ψ
    have h1 := hs.map (toCLM T (Nsig T τ)) (toCLM T (Nsig T τ)).continuous
    refine h1.unique ?_
    convert hs.const_smul ((spinCount_dev (fun i : Fin N => σ i.succ.succ) τ : ℕ) : ℂ) using 1
    funext A
    rw [Function.comp_apply, map_smul, Nsig_pair_dev T τ (σ 0) (σ 1) _ _ _ (hN τ), hcount, smul_comm]
  exact comp_eq_zero_dev T (fun i : Fin N => σ i.succ.succ) hrest (funext fun w => hcomp w)

/-- Any pair `s ≠ t` of variables, brought to the first two places by a permutation (`comp_perm`). -/
theorem Bpair_eq_zero_of_relDeriv_dev (T : Torus) {N' : ℕ} (σc : Fin N' → Spin) {Ψ : FockSpace T}
    (hN : ∀ τ : Spin, toCLM T (Nsig T τ) Ψ = ((spinCount_dev σc τ : ℕ) : ℂ) • Ψ)
    (s t : Fin N') (hst : s ≠ t)
    (hdiag : ∀ u : Fin N' → ℂ, u s = u t → relDeriv (comp T σc Ψ) s t u = 0) (k : ℤ) :
    toCLM T (Bpair T (σc s) (σc t) k) Ψ = 0 := by
  obtain ⟨N, rfl⟩ : ∃ N, N' = N + 2 := by
    have h1 := s.2
    have h2 := t.2
    have h3 : (s : ℕ) ≠ t := fun h => hst (Fin.ext h)
    exact ⟨N' - 2, by omega⟩
  -- a permutation with `ρ 0 = s`, `ρ 1 = t`
  set t' := Equiv.swap (0 : Fin (N + 2)) s t with ht'
  have ht'0 : t' ≠ 0 := by
    intro h
    apply hst
    have := congrArg (Equiv.swap (0 : Fin (N + 2)) s) h
    rw [ht', Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact this.symm
  set ρ : Equiv.Perm (Fin (N + 2)) := Equiv.swap 0 s * Equiv.swap 1 t' with hρ
  have hρ0 : ρ 0 = s := by
    rw [hρ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne zero_ne_one (Ne.symm ht'0), Equiv.swap_apply_left]
  have hρ1 : ρ 1 = t := by
    rw [hρ, Equiv.Perm.mul_apply, Equiv.swap_apply_left, ht', Equiv.swap_apply_self]
  have hcount : ∀ τ : Spin, spinCount_dev (σc ∘ ρ) τ = spinCount_dev σc τ := by
    intro τ
    unfold spinCount_dev
    rw [Finset.card_filter, Finset.card_filter]
    exact Equiv.sum_comp ρ (fun i => if σc i = τ then 1 else 0)
  have hN' : ∀ τ : Spin, toCLM T (Nsig T τ) Ψ = ((spinCount_dev (σc ∘ ρ) τ : ℕ) : ℂ) • Ψ := by
    intro τ
    rw [hcount]
    exact hN τ
  have hcompρ : ∀ v : Fin (N + 2) → ℂ,
      comp T (σc ∘ ρ) Ψ v = ((Equiv.Perm.sign ρ : ℤ) : ℂ) * comp T σc Ψ (v ∘ ρ.symm) := by
    intro v
    have h := comp_perm T σc ρ Ψ (v ∘ ρ.symm)
    have hv : (v ∘ ρ.symm) ∘ ρ = v := by
      funext i
      simp
    rw [hv] at h
    exact h
  have hderiv : ∀ (v : Fin (N + 2) → ℂ) (i : Fin (N + 2)) (x : ℂ),
      deriv (fun z => comp T (σc ∘ ρ) Ψ (Function.update v i z)) x =
        ((Equiv.Perm.sign ρ : ℤ) : ℂ) * deriv (fun z => comp T σc Ψ (Function.update (v ∘ ρ.symm) (ρ i) z)) x := by
    intro v i x
    have hslice : (fun z => comp T (σc ∘ ρ) Ψ (Function.update v i z)) =
        fun z => ((Equiv.Perm.sign ρ : ℤ) : ℂ) * comp T σc Ψ (Function.update (v ∘ ρ.symm) (ρ i) z) := by
      funext z
      rw [hcompρ]
      congr 2
      rw [Function.update_comp_equiv, Equiv.symm_symm]
    rw [hslice, deriv_const_mul_field]
  have hdiag' : ∀ (W : ℂ) (w : Fin N → ℂ),
      relDeriv (comp T (σc ∘ ρ) Ψ) 0 1 (Fin.cons W (Fin.cons W w : Fin (N + 1) → ℂ)) = 0 := by
    intro W w
    set v : Fin (N + 2) → ℂ := Fin.cons W (Fin.cons W w : Fin (N + 1) → ℂ) with hv
    have e0 : v 0 = (v ∘ ρ.symm) s := by
      rw [Function.comp_apply, ← hρ0, Equiv.symm_apply_apply]
    have e1 : v 1 = (v ∘ ρ.symm) t := by
      rw [Function.comp_apply, ← hρ1, Equiv.symm_apply_apply]
    have hu : (v ∘ ρ.symm) s = (v ∘ ρ.symm) t := by
      rw [← e0, ← e1]
      simp only [hv, Fin.cons_zero, Fin.cons_one]
    have h := hdiag (v ∘ ρ.symm) hu
    unfold relDeriv at h ⊢
    rw [hderiv v 0, hderiv v 1, ← mul_sub, hρ0, hρ1, e0, e1, h, mul_zero]
  have h := Bpair_eq_zero_core_dev T (σc ∘ ρ) hN' hdiag' k
  simpa only [Function.comp_apply, hρ0, hρ1] using h

/-- (C1) and the antisymmetry give the diagonal condition for a same-species pair: on `u_s = u_t` both one-variable
derivatives vanish. -/
theorem relDeriv_eq_zero_of_C1_dev (τ : ℍ) {n m : ℕ} {f : (Fin (n + m) → ℂ) → ℂ}
    (hanti : ∀ s t : Fin (n + m), s ≠ t → SameSpecies n s t → ∀ u, f (u ∘ Equiv.swap s t) = -f u)
    (h1 : C1 τ n m f) (s t : Fin (n + m)) (hst : s < t) (hss : SameSpecies n s t) (u : Fin (n + m) → ℂ)
    (hu : u s = u t) : relDeriv f s t u = 0 := by
  have h0 : (0 : ℂ) ∈ Λu τ := ⟨0, 0, by simp⟩
  have hv := h1 s t hst hss u 0 h0 1 (by norm_num)
  rw [iteratedDeriv_one, add_zero, ← hu] at hv
  have hslice : (fun z => f (Function.update u t z)) = fun z => -f (Function.update u s z) := by
    funext z
    rw [← hanti s t (ne_of_lt hst) hss (Function.update u s z)]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rcases eq_or_ne i s with rfl | his
    · rw [Equiv.swap_apply_left, Function.update_of_ne (ne_of_lt hst).symm, Function.update_of_ne (ne_of_lt hst), hu]
    · rcases eq_or_ne i t with rfl | hit
      · rw [Equiv.swap_apply_right, Function.update_self, Function.update_self]
      · rw [Equiv.swap_apply_of_ne_of_ne his hit, Function.update_of_ne his, Function.update_of_ne hit]
  unfold relDeriv
  rw [hslice, deriv.fun_neg, ← hu, hv, neg_zero, sub_zero]

/-- **Lemma C.A, (2) ⇒ (3)**: if the canonical component satisfies (C1) and (C2), then
"`$B_n^\mu\Psi=0$ for all $n\in\Z_{2L}$ and $\mu\in\{+1,0,-1\}$.`" — every `b_ν(n)` of Definition 4.1 annihilates `Ψ`
(`Bpair_up_up` etc.). -/
theorem lemA_bcen (T : Torus) (nn : SectorLabel T) {n m : ℕ} (hn : (nn.1 : ℕ) = n) (hm : (nn.2 : ℕ) = m)
    {Ψ : FockSpace T} (hΨ : Ψ ∈ sector T nn)
    (h1 : C1 (tauT T) n m (canon T n m Ψ)) (h2 : C2 n m (canon T n m Ψ))
    (ν : Triplet) (k : ℤ) : toCLM T (bcen T ν k) Ψ = 0 := by
  have hN := sector_counts_dev T nn hn hm hΨ
  obtain ⟨cu, cd⟩ := spinCount_canonSpins_dev n m
  have hanti := (canon_shape T n m Ψ).2.2
  have hB : ∀ s t : Fin (n + m), s ≠ t →
      (∀ u : Fin (n + m) → ℂ, u s = u t → relDeriv (canon T n m Ψ) s t u = 0) →
      toCLM T (Bpair T (canonSpins n m s) (canonSpins n m t) k) Ψ = 0 :=
    fun s t hst hd => Bpair_eq_zero_of_relDeriv_dev T (canonSpins n m) hN s t hst hd k
  have hup : toCLM T (Nsig T .up) Ψ = ((n : ℕ) : ℂ) • Ψ := by
    rw [← cu]
    exact hN .up
  have hdn : toCLM T (Nsig T .dn) Ψ = ((m : ℕ) : ℂ) • Ψ := by
    rw [← cd]
    exact hN .dn
  cases ν with
  | plus =>
    -- `b_+(k) = B_k^{↑↑}`: the first two up variables, by (C1)
    rw [← Bpair_up_up]
    by_cases h2n : 2 ≤ n
    · have h := hB ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
        (relDeriv_eq_zero_of_C1_dev (tauT T) hanti h1 _ _ (Fin.mk_lt_mk.2 (by omega))
          (show ((0 : ℕ) < n ↔ (1 : ℕ) < n) from ⟨fun _ => by omega, fun _ => by omega⟩))
      have e0 : canonSpins n m ⟨0, by omega⟩ = .up := by simp [canonSpins, show 0 < n by omega]
      have e1 : canonSpins n m ⟨1, by omega⟩ = .up := by simp [canonSpins, show 1 < n by omega]
      rw [e0, e1] at h
      exact h
    · exact Bpair_eq_zero_of_count_dev T .up .up k .up n hup (by simp; omega)
  | minus =>
    -- `b_−(k) = B_k^{↓↓}`: the first two down variables, by (C1)
    rw [← Bpair_dn_dn]
    by_cases h2m : 2 ≤ m
    · have h := hB ⟨n, by omega⟩ ⟨n + 1, by omega⟩ (by simp [Fin.ext_iff])
        (relDeriv_eq_zero_of_C1_dev (tauT T) hanti h1 _ _ (Fin.mk_lt_mk.2 (by omega))
          (show ((n : ℕ) < n ↔ (n + 1 : ℕ) < n) from ⟨fun _ => by omega, fun _ => by omega⟩))
      have e0 : canonSpins n m ⟨n, by omega⟩ = .dn := by simp [canonSpins]
      have e1 : canonSpins n m ⟨n + 1, by omega⟩ = .dn := by simp [canonSpins, show ¬(n + 1 < n) by omega]
      rw [e0, e1] at h
      exact h
    · exact Bpair_eq_zero_of_count_dev T .dn .dn k .dn m hdn (by simp; omega)
  | zero =>
    -- `b_0(k) = √2 B_k^{↑↓}`: the first up and the first down variable, by (C2)
    have hz : toCLM T (bcen T .zero k) Ψ = ((Real.sqrt 2 : ℝ) : ℂ) • toCLM T (Bpair T .up .dn k) Ψ := by
      rw [Bpair_up_dn]
      simp only [toCLM, map_smul, smul_apply, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity), Complex.ofReal_one, one_smul]
    rw [hz]
    by_cases h0n : 0 < n
    · by_cases h0m : 0 < m
      · have h := hB ⟨0, by omega⟩ ⟨n, by omega⟩ (by simp [Fin.ext_iff]; omega)
          (fun u hu => h2 _ _ (show 0 < n from h0n) (show n ≤ n from le_refl n) u hu)
        have e0 : canonSpins n m ⟨0, by omega⟩ = .up := by simp [canonSpins, h0n]
        have e1 : canonSpins n m ⟨n, by omega⟩ = .dn := by simp [canonSpins]
        rw [e0, e1] at h
        rw [h, smul_zero]
      · rw [Bpair_eq_zero_of_count_dev T .up .dn k .dn m hdn (by simp; omega), smul_zero]
    · rw [Bpair_eq_zero_of_count_dev T .up .dn k .up n hup (by simp; omega), smul_zero]

/-- **Lemma C.A, (3) ⇒ (1)** for the Lean's `H_N`: (C1) and (C2) give "`$H\Psi=0$.`" — by Theorem 4.2(c) (`localForm_c`,
"`$\sum_{\sigma,\sigma'}(B_n^{\sigma\sigma'})^\dagger B_n^{\sigma\sigma'}=\sum_\nu(\bcen\nu n)^*\bcen\nu n$`"). -/
theorem lemA_HN (T : Torus) (nn : SectorLabel T) {n m : ℕ} (hn : (nn.1 : ℕ) = n) (hm : (nn.2 : ℕ) = m)
    {Ψ : FockSpace T} (hΨ : Ψ ∈ sector T nn)
    (h1 : C1 (tauT T) n m (canon T n m Ψ)) (h2 : C2 n m (canon T n m Ψ)) :
    Ψ ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) := by
  -- (3) ⇒ (1) by Theorem 4.2(c), every b_ν(n) annihilating Ψ
  have hb := lemA_bcen T nn hn hm hΨ h1 h2
  rw [LinearMap.mem_ker]
  show toCLM T (HN T) Ψ = 0
  rw [localForm_c]
  simp only [toCLM] at hb ⊢
  simp only [map_smul, map_sum, map_mul, smul_apply, FunLike.coe_sum, Finset.sum_apply, mul_apply_eq_comp, hb,
    map_zero, Finset.sum_const_zero, smul_zero]

end HRTorus.ZeroModes

end -- noncomputable section
