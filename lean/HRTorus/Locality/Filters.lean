import HRTorus.Locality.Propagation
import HRTorus.Locality.Calculus
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.Fourier.Inversion

/-!
# Time filters, the commutator with the Hamiltonian, and the clustering filter (T-0056 block D, `Locality.Filters`)

Written by Claude Opus 5.5 (an AI model), 2026-10-24. **Proof phase, round two (recruit L10, 2026-10-24/25): every
theorem is proved on the standard axioms; there is no `sorry` in this module. Lemma 5.6 (`setNorm_timeFilter_le`,
`almostSupported_timeFilter`) uses Lemma 5.5 `setNorm_dyn_le` of `Locality.Propagation`, and Proposition 5.11
`almostSupported_clusterFilter` uses Lemma 5.6. The proofs add devices, each marked as a device; the Fourier identity of
Lemma 5.9 uses Mathlib's Fourier inversion (`Mathlib.Analysis.Fourier.Inversion`).**
The paper: the HR paper,
`papers/hr/sections/05-locality.tex` — Lemma 5.6 `lem:filters`, Lemma 5.7 `lem:commutatorH` (with the bound
`‖H_N‖ ≤ C_h|𝕋_N|` of its proof, which Lemma 5.10's use cites), Definition 5.8 `def:filters` with the paragraph after
it, Lemma 5.9 `lem:Wexists` (with the Fourier identity for every `ω` of its proof, which the spectral formula uses),
Lemma 5.10 `lem:timerep` and Proposition 5.11 `prop:Qlocal`.

## The model

* **Operator-valued time integrals are entrywise** (`opIntegralOn D g`: the matrix of the Bochner integrals
  `∫ t in D, g t m m'` over a set `D ⊆ ℝ`; `D = Set.univ` for `∫_ℝ`), block C's `opIntegral` pattern on the line; the
  bridge to Mathlib's Bochner integral of `t ↦ opCLM (g t)` is a stated theorem (`opCLM_opIntegralOn`). For the
  integrands of §5 (an integrable scalar filter times a bounded continuous operator-valued function) every entry is
  integrable, so no integrability hypothesis is needed in the statements.
* **Filters** `F : ℝ → ℂ`; `M_j(F) := ∫ (1 + |t|)^j |F(t)| dt` is `moment F j` (real `j`); "`F ∈ L¹(ℝ)` with `M_j(F) < ∞` for
  every `j`" is `HasFiniteMoments F` (integrability of `F` and of every `(1 + |t|)^j |F|`, `j ∈ ℕ`).
* **Definition 5.8.** The fixed `ϑ` is an explicit argument with the hypothesis structure `IsCutoff ϑ` (as `SlotFrame`'s
  `IsProfile` is for `η`); `C_c^∞((−1, 1))` is smoothness with `tsupport ϑ ⊆ (−1, 1)` (closed and bounded, hence
  compact). **`W_γ` is the paper's improper integral**: `(1/2π) · limUnder atTop (Ω ↦ ∫_{−Ω}^{Ω} Ŵ_γ(ω) e^{iωt} dω)`;
  Mathlib's `limUnder` gives a junk value where the limit fails, and `tendsto_Wfilt` (Lemma 5.9's first sentence:
  "`the limit exists for every $t$`") rules that out. `W_γ` is complex-valued and "real" is a theorem. The parameters
  `Δ`, `γ`, `δ`, `ζ` and their conditions are the hypothesis structure `ClusterParams`; `g` (`gClust`) is real-valued.
* **`𝒬` and the spectral projections.** `1_{{E}}(H) := cfc 1_{{E}} H` (`specProj`, block A's `cfc` of an indicator, the
  form of `specProj_sector` and block B's `specProj_iota`); `σ(H)` is the finite real spectrum as a `Finset`
  (`Matrix.finite_real_spectrum`); `𝒬(A) := Σ_{E,E'∈σ(H)} g(E − E') 1_{E}(H) A 1_{E'}(H)` is `clusterFilter g H A`, for
  any operator `H` on any `Op S` — the paper's `𝒬` on `𝔉` is `clusterFilter g (H N)`, on `𝔉_𝒮` it is
  `clusterFilter g (Ĥ_N)`, so "the same on `𝔉_𝒮`" is the generic statement at `S = Slot δ₀ T`. Lemmas 5.9's spectral
  formula and 5.10 are stated for any self-adjoint `H` on any `Op S`.
* **Principal values** are the limits the paper means: `HasPVIntegral f L` is `∫_{ε<|t|<T} f → L` as `ε → 0⁺` and
  `T → ∞` jointly (the filter `𝓝[>] 0 ×ˢ atTop`), and `c_F := lim_{ε→0⁺} ∫_{ε<|t|<1} F(t) dt/t` is a `limUnder` with its
  existence a theorem. `G` is extended by `0` outside `(−1, 1)` (and at `0`), which is the paper's `G_1` of Proposition
  5.11.
* **Exponents.** As in `Locality.Calculus`, an exponent that becomes a prefactor exponent must be nonnegative
  (Definition 3.11's `m ≥ 0`): Lemma 5.6 and Proposition 5.11 assume `m'' ≥ 0`.
-/

open scoped InnerProductSpace Matrix Real ContDiff Topology
open Complex (I)
open Filter MeasureTheory Asymptotics

noncomputable section

namespace HRTorus.Locality

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op c chat parityOp IsEven CAR Alg condExp)

/-! ## Operator-valued integrals over subsets of `ℝ`, and moments (any finite `S`) -/

section Integrals

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The integral `∫_D g(t) dt` of an operator-valued function over a set `D ⊆ ℝ` for Lebesgue measure, entrywise (a
model definition; the module docstring): the `(m, m')` entry is `∫ t in D, (g t) m m'`. -/
def opIntegralOn (D : Set ℝ) (g : ℝ → Op S) : Op S :=
  Matrix.of fun m m' => ∫ t in D, g t m m'

/-- The entrywise integral is the Bochner integral of `t ↦ opCLM (g t)` (a model statement, for entrywise integrable
`g`). -/
theorem opCLM_opIntegralOn (D : Set ℝ) (g : ℝ → Op S) (hint : ∀ m m' : Conf S, IntegrableOn (fun t => g t m m') D) :
    opCLM (opIntegralOn D g) = ∫ t in D, opCLM (g t) := by
  have hΦ : ∀ A : Op S, opCLM A = ∑ m, ∑ m', A m m' • opCLM (Matrix.single m m' (1 : ℂ)) := by
    intro A
    conv_lhs => rw [matrix_eq_sum_smul_single A]
    simp only [opCLM_sum, opCLM_smul]
  have e : (fun t => opCLM (g t)) = fun t => ∑ m, ∑ m', g t m m' • opCLM (Matrix.single m m' (1 : ℂ)) :=
    funext fun t => hΦ (g t)
  rw [hΦ, e, integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun m' _ => (hint m m').smul_const _))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ (fun m' _ => (hint m m').smul_const _)]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [integral_smul_const]
  rfl

end Integrals

/-- **Lemma 5.6**: "`M_j(F):=\int(1+\abs t)^j\abs{F(t)}\,\dd t`". -/
def moment (F : ℝ → ℂ) (j : ℝ) : ℝ :=
  ∫ t, (1 + |t|) ^ j * ‖F t‖

/-- **Lemma 5.6**: "`Let $F\in L^1(\R)$ with $M_j(F):=\int(1+\abs t)^j\abs{F(t)}\,\dd t<\infty$ for every $j$.`" -/
def HasFiniteMoments (F : ℝ → ℂ) : Prop :=
  Integrable F ∧ ∀ j : ℕ, Integrable fun t => (1 + |t|) ^ j * ‖F t‖

/-! ## Lemma 5.6 (time filters) -/

/-! ### Proof devices for the operator-valued time integrals and Lemma 5.6 (phase (b); not statements of the paper) -/

section IntegralDevices

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem opIntegralOn_map {S' : Type*} [Fintype S'] [DecidableEq S'] (Φ : Op S →ₗ[ℂ] Op S') (D : Set ℝ) (g : ℝ → Op S)
    (hint : ∀ m m' : Conf S, IntegrableOn (fun t => g t m m') D) :
    Φ (opIntegralOn D g) = opIntegralOn D fun t => Φ (g t) := by
  have hΦ : ∀ A : Op S, Φ A = ∑ m, ∑ m', A m m' • Φ (Matrix.single m m' (1 : ℂ)) := by
    intro A
    conv_lhs => rw [matrix_eq_sum_smul_single A]
    simp only [map_sum, map_smul]
  ext k k'
  rw [hΦ]
  simp only [opIntegralOn, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have e : (fun t => (Φ (g t)) k k') =
      fun t => ∑ m, ∑ m', g t m m' * (Φ (Matrix.single m m' (1 : ℂ))) k k' := by
    funext t
    rw [hΦ (g t)]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [e, integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun m' _ => (hint m m').mul_const _))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ (fun m' _ => (hint m m').mul_const _)]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [integral_mul_const]

theorem opCLM_apply_single_apply (A : Op S) (m m' : Conf S) :
    (opCLM A (EuclideanSpace.single m' 1)) m = A m m' := by
  rw [show (opCLM A (EuclideanSpace.single m' 1)) m = (A *ᵥ (EuclideanSpace.single m' (1 : ℂ)).ofLp) m from rfl]
  simp [Matrix.mulVec, dotProduct]

theorem continuous_entry_of_continuous_opCLM {X : ℝ → Op S} (hX : Continuous fun t => opCLM (X t))
    (m m' : Conf S) : Continuous fun t => X t m m' := by
  have e : (fun t => X t m m') = fun t => (EuclideanSpace.proj m) (opCLM (X t) (EuclideanSpace.single m' 1)) :=
    funext fun t => (opCLM_apply_single_apply _ m m').symm
  rw [e]
  exact (EuclideanSpace.proj m).continuous.comp (hX.clm_apply continuous_const)

theorem integrable_entry_smul {F : ℝ → ℂ} (hF : Integrable F) {X : ℝ → Op S}
    (hX : Continuous fun t => opCLM (X t)) {M : ℝ} (hM : ∀ t, ‖opCLM (X t)‖ ≤ M) (D : Set ℝ) (m m' : Conf S) :
    IntegrableOn (fun t => (F t • X t) m m') D := by
  have e : (fun t => (F t • X t) m m') = fun t => F t * X t m m' :=
    funext fun t => by rw [Matrix.smul_apply, smul_eq_mul]
  rw [e]
  refine Integrable.integrableOn (Integrable.mono' (hF.norm.mul_const M)
    (hF.aestronglyMeasurable.mul (continuous_entry_of_continuous_opCLM hX m m').aestronglyMeasurable) ?_)
  refine Filter.Eventually.of_forall fun t => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_entry_le _ m m').trans (hM t)) (norm_nonneg _)

theorem norm_opIntegralOn_le (D : Set ℝ) (g : ℝ → Op S) (hint : ∀ m m' : Conf S, IntegrableOn (fun t => g t m m') D) :
    ‖opCLM (opIntegralOn D g)‖ ≤ ∫ t in D, ‖opCLM (g t)‖ := by
  rw [opCLM_opIntegralOn D g hint]
  exact norm_integral_le_integral_norm _

theorem isEven_opIntegralOn (D : Set ℝ) (g : ℝ → Op S) (hint : ∀ m m' : Conf S, IntegrableOn (fun t => g t m m') D)
    (hg : ∀ t, IsEven (g t)) : IsEven (opIntegralOn D g) := by
  show opIntegralOn D g * parityOp = parityOp * opIntegralOn D g
  have h1 := opIntegralOn_map (LinearMap.mulRight ℂ (parityOp : Op S)) D g hint
  have h2 := opIntegralOn_map (LinearMap.mulLeft ℂ (parityOp : Op S)) D g hint
  simp only [LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at h1 h2
  rw [h1, h2]
  congr 1
  funext t
  exact (hg t).eq

/-- Device: the conditional expectation `𝔼_Y` as a linear map. -/
def condExpLM (Y : Finset S) : Op S →ₗ[ℂ] Op S :=
  IsLinearMap.mk' (condExp Y) (Fermion.Pilot.JW.condExp_isLinearMap Y)

theorem condExpLM_apply (Y : Finset S) (A : Op S) : condExpLM Y A = condExp Y A := rfl

theorem norm_condExp_le' (Y : Finset S) (A : Op S) : ‖opCLM (condExp Y A)‖ ≤ ‖opCLM A‖ := by
  open scoped Matrix.Norms.L2Operator in
  (rw [norm_opCLM_eq_l2, norm_opCLM_eq_l2]; exact Fermion.Pilot.JW.norm_condExp_le Y A)

theorem norm_sub_condExp_le' (Y : Finset S) {A : Op S} (hA : IsEven A) :
    ‖opCLM (A - condExp Y A)‖ ≤ 2 * ⨅ A' : Alg Y, ‖opCLM (A - (A' : Op S))‖ := by
  open scoped Matrix.Norms.L2Operator in
  (rw [norm_opCLM_eq_l2]; exact Fermion.Pilot.JW.norm_sub_condExp_le Y hA)

theorem continuous_opCLM_condExp (Y : Finset S) {X : ℝ → Op S} (hX : Continuous fun t => opCLM (X t)) :
    Continuous fun t => opCLM (condExp Y (X t)) := by
  have hlin : Continuous fun B : Op S => condExp Y B :=
    LinearMap.continuous_of_finiteDimensional (condExpLM Y)
  have hX' : Continuous X := by
    have e : X = fun t => (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)).symm (opCLM (X t)) :=
      funext fun t => ((Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)).symm_apply_apply (X t)).symm
    rw [e]
    exact (LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (n := Conf S) (𝕜 := ℂ)).symm.toAlgEquiv.toLinearEquiv.toLinearMap).comp hX
  exact continuous_opCLM.comp (hlin.comp hX')

end IntegralDevices

theorem integrable_moment_rpow {F : ℝ → ℂ} (hF : HasFiniteMoments F) {j : ℝ} (hj : 0 ≤ j) :
    Integrable fun t => (1 + |t|) ^ j * ‖F t‖ := by
  refine Integrable.mono' (hF.2 ⌈j⌉₊) ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((continuous_const.add continuous_abs).rpow_const fun t => Or.inr hj).aestronglyMeasurable.mul
      hF.1.aestronglyMeasurable.norm
  · have h1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (norm_nonneg _))]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil j)

/-- **Lemma 5.6**: "`For every $k$ there is $C_k$ such that for every even operator $A$ on $\FockS$ and every $X\subset\Slots$ with $\norm A_{X;\max\{k,3\}}<\infty$,`"
"`\Bigl\lVert\int F(t)\tau_t(A)\,\dd t\Bigr\rVert_{X;k}\le C_k\abs X\bigl(\norm A+\norm A_{X;\max\{k,3\}}\bigr)M_{4k}(F).`"
— in block B's set norm; `k` real, `k ≥ 0`; the constant after `F`, `δ₀`, `k`, `C_h`, `C^H` ("`in addition, those of Lemma~\ref{lem:filters} depend on $F$`").
For `A` with `n_A < ∞`, the paper's hypothesis as in Lemma 5.5 (`setNorm_dyn_le`; the proof: "`$n_A:=\norm A+\norm A_{X;\bar k}$, finite by hypothesis`"). -/
theorem setNorm_timeFilter_le {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {F : ℝ → ℂ} (hF : HasFiniteMoments F) {k : ℝ} (hk : 0 ≤ k)
    (Ch : ℝ) (CH : ℕ → ℝ) :
    ∃ Ck : ℝ, ∀ (η : ℝ → ℝ), IsProfile η → ∀ (Ts : TorusSeq δ₀) (H : (N : ℕ) → FockOp (Ts.T N))
      (d : H1Data η δ₀ Ts H), d.Ch = Ch → d.CH = CH →
        ∀ N ∈ Ts.idx, ∀ A : Op (Slot δ₀ (Ts.T N)), IsEven A → ∀ X : Finset (Slot δ₀ (Ts.T N)),
          setNorm A X (max k 3) ≠ ⊤ →
          setNorm (opIntegralOn Set.univ fun t => F t • dyn (Hhat η δ₀ Ts H N) t A) X k ≤
            ENNReal.ofReal (Ck * (X.card : ℝ) * moment F (4 * k)) *
              (ENNReal.ofReal ‖opCLM A‖ + setNorm A X (max k 3)) := by
  obtain ⟨Cs, hCs⟩ := setNorm_dyn_le hδ₀ hk Ch CH
  refine ⟨2 * |Cs|, ?_⟩
  intro η hη Ts H d hCh hCH N hN A hA X hfin
  have hHsa := isSelfAdjoint_Hhat hη hδ₀ d N hN
  have hHe := isEven_Hhat hη hδ₀ d N hN
  have hS0 : 0 ≤ (setNorm A X (max k 3)).toReal := ENNReal.toReal_nonneg
  have hnA0 : 0 ≤ ‖opCLM A‖ + (setNorm A X (max k 3)).toReal := add_nonneg (norm_nonneg _) hS0
  have e1 : ENNReal.ofReal ‖opCLM A‖ + setNorm A X (max k 3) =
      ENNReal.ofReal (‖opCLM A‖ + (setNorm A X (max k 3)).toReal) := by
    rw [ENNReal.ofReal_add (norm_nonneg _) hS0, ENNReal.ofReal_toReal hfin]
  have hX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  have hτ : ∀ t : ℝ, setNorm (dyn (Hhat η δ₀ Ts H N) t A) X k ≤
      ENNReal.ofReal (|Cs| * (1 + |t|) ^ (4 * k) * X.card * (‖opCLM A‖ + (setNorm A X (max k 3)).toReal)) := by
    intro t
    refine (hCs η hη Ts H d hCh hCH N hN A hA X t hfin).trans ?_
    rw [e1, ← ENNReal.ofReal_mul' hnA0]
    apply ENNReal.ofReal_le_ofReal
    have ht0 : 0 ≤ (1 + |t|) ^ (4 * k) := Real.rpow_nonneg (by linarith [abs_nonneg t]) _
    have h1 : Cs * (1 + |t|) ^ (4 * k) * X.card ≤ |Cs| * (1 + |t|) ^ (4 * k) * X.card :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) ht0) hX0
    exact mul_le_mul_of_nonneg_right h1 hnA0
  have hτc : Continuous fun t => opCLM (dyn (Hhat η δ₀ Ts H N) t A) := continuous_opCLM_dyn _ A
  have hτn : ∀ t, ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A)‖ ≤ ‖opCLM A‖ := fun t => le_of_eq (norm_dyn hHsa t A)
  have hint : ∀ m m', IntegrableOn (fun t => (F t • dyn (Hhat η δ₀ Ts H N) t A) m m') Set.univ :=
    fun m m' => integrable_entry_smul hF.1 hτc hτn _ m m'
  have hτe : ∀ t, IsEven (dyn (Hhat η δ₀ Ts H N) t A) := fun t => isEven_dyn hHe hA t
  have hQe : IsEven (opIntegralOn Set.univ fun t => F t • dyn (Hhat η δ₀ Ts H N) t A) :=
    isEven_opIntegralOn _ _ hint fun t => (hτe t).smul_left (F t)
  rw [e1, ← ENNReal.ofReal_mul' hnA0]
  refine iSup₂_le fun r hr => ?_
  have hB := Fermion.Pilot.JW.condExp_mem_Alg (fat X r) hQe
  have hbdd : BddBelow (Set.range fun A' : Alg (fat X r) =>
      ‖opCLM ((opIntegralOn Set.univ fun t => F t • dyn (Hhat η δ₀ Ts H N) t A) - (A' : Op (Slot δ₀ (Ts.T N))))‖) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
  have hinf := ciInf_le hbdd ⟨_, hB⟩
  have hdiff : (opIntegralOn Set.univ fun t => F t • dyn (Hhat η δ₀ Ts H N) t A) -
      condExp (fat X r) (opIntegralOn Set.univ fun t => F t • dyn (Hhat η δ₀ Ts H N) t A) =
      opIntegralOn Set.univ fun t => F t • (dyn (Hhat η δ₀ Ts H N) t A -
        condExp (fat X r) (dyn (Hhat η δ₀ Ts H N) t A)) := by
    have h := opIntegralOn_map (LinearMap.id - condExpLM (fat X r)) Set.univ _ hint
    simp only [LinearMap.sub_apply, LinearMap.id_apply, condExpLM_apply] at h
    rw [h]
    congr 1
    funext t
    rw [← condExpLM_apply, (condExpLM (fat X r)).map_smul, condExpLM_apply, smul_sub]
  have hint2 : ∀ m m', IntegrableOn (fun t => (F t • (dyn (Hhat η δ₀ Ts H N) t A -
      condExp (fat X r) (dyn (Hhat η δ₀ Ts H N) t A))) m m') Set.univ := by
    intro m m'
    refine integrable_entry_smul hF.1 ?_ (M := 2 * ‖opCLM A‖) ?_ _ m m'
    · have hc := continuous_opCLM_condExp (fat X r) hτc
      have e : (fun t => opCLM (dyn (Hhat η δ₀ Ts H N) t A - condExp (fat X r) (dyn (Hhat η δ₀ Ts H N) t A))) =
          fun t => opCLM (dyn (Hhat η δ₀ Ts H N) t A) - opCLM (condExp (fat X r) (dyn (Hhat η δ₀ Ts H N) t A)) :=
        funext fun t => opCLM_sub' _ _
      rw [e]
      exact hτc.sub hc
    · intro t
      rw [opCLM_sub']
      calc _ ≤ ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A)‖ + ‖opCLM (condExp (fat X r) (dyn (Hhat η δ₀ Ts H N) t A))‖ :=
            norm_sub_le _ _
        _ ≤ ‖opCLM A‖ + ‖opCLM A‖ := add_le_add (hτn t) ((norm_condExp_le' _ _).trans (hτn t))
        _ = 2 * ‖opCLM A‖ := by ring
  have hr1 : 0 < 1 + r := by linarith
  have hpos : 0 < (1 + r) ^ k := Real.rpow_pos_of_pos hr1 _
  have hpt : ∀ t, ‖opCLM (F t • (dyn (Hhat η δ₀ Ts H N) t A - condExp (fat X r) (dyn (Hhat η δ₀ Ts H N) t A)))‖ ≤
      2 * (1 + r) ^ (-k) * (|Cs| * X.card * (‖opCLM A‖ + (setNorm A X (max k 3)).toReal)) *
        ((1 + |t|) ^ (4 * k) * ‖F t‖) := by
    intro t
    rw [opCLM_smul', norm_smul]
    have h1 := norm_sub_condExp_le' (fat X r) (hτe t)
    have hle : ENNReal.ofReal ((1 + r) ^ k * ⨅ A' : Alg (fat X r),
        ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - (A' : Op (Slot δ₀ (Ts.T N))))‖) ≤
        setNorm (dyn (Hhat η δ₀ Ts H N) t A) X k := by
      unfold setNorm
      exact le_iSup₂ (f := fun (r : ℝ) (_ : 0 ≤ r) => ENNReal.ofReal ((1 + r) ^ k * ⨅ A' : Alg (fat X r),
        ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - (A' : Op (Slot δ₀ (Ts.T N))))‖)) r hr
    have hle2 := hle.trans (hτ t)
    have ht0 : 0 ≤ (1 + |t|) ^ (4 * k) := Real.rpow_nonneg (by linarith [abs_nonneg t]) _
    rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) ht0) hX0) hnA0)] at hle2
    have hinf2 : ⨅ A' : Alg (fat X r), ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - (A' : Op (Slot δ₀ (Ts.T N))))‖ ≤
        (1 + r) ^ (-k) * (|Cs| * (1 + |t|) ^ (4 * k) * X.card *
          (‖opCLM A‖ + (setNorm A X (max k 3)).toReal)) := by
      rw [Real.rpow_neg hr1.le, ← div_eq_inv_mul, le_div_iff₀ hpos]
      linarith
    calc ‖F t‖ * ‖opCLM (dyn (Hhat η δ₀ Ts H N) t A - condExp (fat X r) (dyn (Hhat η δ₀ Ts H N) t A))‖
        ≤ ‖F t‖ * (2 * ((1 + r) ^ (-k) * (|Cs| * (1 + |t|) ^ (4 * k) * X.card *
            (‖opCLM A‖ + (setNorm A X (max k 3)).toReal)))) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hinf2 (by norm_num))) (norm_nonneg _)
      _ = _ := by ring
  have hmono : ‖opCLM ((opIntegralOn Set.univ fun t => F t • dyn (Hhat η δ₀ Ts H N) t A) -
      condExp (fat X r) (opIntegralOn Set.univ fun t => F t • dyn (Hhat η δ₀ Ts H N) t A))‖ ≤
      2 * (1 + r) ^ (-k) * (|Cs| * X.card * (‖opCLM A‖ + (setNorm A X (max k 3)).toReal)) * moment F (4 * k) := by
    rw [hdiff]
    refine (norm_opIntegralOn_le _ _ hint2).trans ?_
    rw [Measure.restrict_univ]
    have hg := (integrable_moment_rpow hF (by linarith : (0 : ℝ) ≤ 4 * k)).const_mul
      (2 * (1 + r) ^ (-k) * (|Cs| * X.card * (‖opCLM A‖ + (setNorm A X (max k 3)).toReal)))
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _) hg
      (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_const_mul]
    rfl
  apply ENNReal.ofReal_le_ofReal
  have hk1 : (1 + r) ^ k * (1 + r) ^ (-k) = 1 := by
    rw [← Real.rpow_add hr1, add_neg_cancel, Real.rpow_zero]
  calc (1 + r) ^ k * ⨅ A' : Alg (fat X r),
        ‖opCLM ((opIntegralOn Set.univ fun t => F t • dyn (Hhat η δ₀ Ts H N) t A) - (A' : Op (Slot δ₀ (Ts.T N))))‖
      ≤ (1 + r) ^ k * ‖opCLM ((opIntegralOn Set.univ fun t => F t • dyn (Hhat η δ₀ Ts H N) t A) -
          condExp (fat X r) (opIntegralOn Set.univ fun t => F t • dyn (Hhat η δ₀ Ts H N) t A))‖ :=
        mul_le_mul_of_nonneg_left hinf hpos.le
    _ ≤ (1 + r) ^ k * (2 * (1 + r) ^ (-k) * (|Cs| * X.card * (‖opCLM A‖ + (setNorm A X (max k 3)).toReal)) *
          moment F (4 * k)) := mul_le_mul_of_nonneg_left hmono hpos.le
    _ = (2 * |Cs| * X.card * moment F (4 * k) * (‖opCLM A‖ + (setNorm A X (max k 3)).toReal)) *
          ((1 + r) ^ k * (1 + r) ^ (-k)) := by ring
    _ = _ := by rw [hk1, mul_one]

/-- **Lemma 5.6**, the second claim: "`Consequently, if $A=(A_N)\in\AS_Z$ is even, with prefactor exponent $m$ and $\norm{A_N}\le CN^{m'}$, and $\abs{Z_N}\le CN^{m''}$, then $\bigl(\int F(t)\tau_t(A_N)\,\dd t\bigr)_N\in\AS_Z$ with prefactor exponent $\max\{m,m'\}+m''$.`"
— on `𝔉` with `τ_t = dyn (H N) t`; `m'' ≥ 0`; the new constants after `F`, `δ₀`, `C`, the exponents, the constants of
`A`, `C_h` and `C^H`. -/
theorem almostSupported_timeFilter {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {F : ℝ → ℂ} (hF : HasFiniteMoments F)
    (C m m' m'' : ℝ) (hm'' : 0 ≤ m'') (CA : ℕ → ℝ) (Ch : ℝ) (CH : ℕ → ℝ) :
    ∃ C' : ℕ → ℝ, ∀ (η : ℝ → ℝ), IsProfile η → ∀ (Ts : TorusSeq δ₀) (H : (N : ℕ) → FockOp (Ts.T N))
      (d : H1Data η δ₀ Ts H), d.Ch = Ch → d.CH = CH →
      ∀ (Z : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))) (A : (N : ℕ) → FockOp (Ts.T N)),
        (∀ N ∈ Ts.idx, IsEven (A N)) → ASBound η δ₀ Ts Z A m CA →
        (∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (A N)‖ ≤ C * (N : ℝ) ^ m') →
        (∀ N ∈ Ts.idx, ((Z N).card : ℝ) ≤ C * (N : ℝ) ^ m'') →
          ASBound η δ₀ Ts Z (fun N => opIntegralOn Set.univ fun t => F t • dyn (H N) t (A N))
            (max m m' + m'') C' := by
  choose Ck hCk using fun k : ℕ => setNorm_timeFilter_le hδ₀ hF (Nat.cast_nonneg k) Ch CH
  refine ⟨fun k => |Ck k| * |C| * moment F (4 * k) * (|C| + |CA (max k 3)|), ?_⟩
  intro η hη Ts H d hCh hCH Z A hAe hAS hAn hZ
  have hm0 : 0 ≤ m := hAS.1
  refine ⟨by have := le_max_left m m'; linarith, ?_⟩
  intro k N hN r hr
  have hT := Ts.admissible N hN
  have hN1 := one_le_of_mem_idx Ts hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hHsa := d.H_isSelfAdjoint N hN
  have hτc : Continuous fun t => opCLM (dyn (H N) t (A N)) := continuous_opCLM_dyn _ _
  have hτn : ∀ t, ‖opCLM (dyn (H N) t (A N))‖ ≤ ‖opCLM (A N)‖ := fun t => le_of_eq (norm_dyn hHsa t _)
  have hint : ∀ m m', IntegrableOn (fun t => (F t • dyn (H N) t (A N)) m m') Set.univ :=
    fun m m' => integrable_entry_smul hF.1 hτc hτn Set.univ m m'
  have hιQ : iota η δ₀ (Ts.T N) (opIntegralOn Set.univ fun t => F t • dyn (H N) t (A N)) =
      opIntegralOn Set.univ fun t => F t • dyn (Hhat η δ₀ Ts H N) t (iota η δ₀ (Ts.T N) (A N)) := by
    have h := opIntegralOn_map (iotaHom hη hδ₀ hT).toAlgHom.toLinearMap Set.univ _ hint
    rw [AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, iotaHom_apply] at h
    rw [h]
    congr 1
    funext t
    rw [AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, iotaHom_apply, iota_smul hη hδ₀ hT,
      ← dyn_iota hη hδ₀ hT hHsa]
  have hAι : IsEven (iota η δ₀ (Ts.T N) (A N)) := iota_isEven hη hδ₀ hT (hAe N hN)
  have hcast : (((max k 3 : ℕ) : ℝ)) = max (k : ℝ) 3 := by push_cast; rfl
  have hsetA : setNorm (iota η δ₀ (Ts.T N) (A N)) (Z N) (max (k : ℝ) 3) ≤
      ENNReal.ofReal (|CA (max k 3)| * (N : ℝ) ^ m) := by
    have h := hAS.setNorm_le (max k 3) N hN
    rw [hcast] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _)
      (Real.rpow_nonneg hNpos.le _)))
  have hfinA : setNorm (iota η δ₀ (Ts.T N) (A N)) (Z N) (max (k : ℝ) 3) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsetA
  have hQ := hCk k η hη Ts H d hCh hCH N hN (iota η δ₀ (Ts.T N) (A N)) hAι (Z N) hfinA
  rw [← hιQ] at hQ
  have hM0 : 0 ≤ moment F (4 * k) :=
    integral_nonneg fun t => mul_nonneg (Real.rpow_nonneg (by linarith [abs_nonneg t]) _) (norm_nonneg _)
  have hZ0 : (0 : ℝ) ≤ (Z N).card := Nat.cast_nonneg _
  have hnorm : ‖opCLM (iota η δ₀ (Ts.T N) (A N))‖ = ‖toCLM (Ts.T N) (A N)‖ := norm_iota hη hδ₀ hT _
  have hb0 : 0 ≤ ‖opCLM (iota η δ₀ (Ts.T N) (A N))‖ + |CA (max k 3)| * (N : ℝ) ^ m :=
    add_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hNpos.le _))
  have hbound : setNorm (iota η δ₀ (Ts.T N) (opIntegralOn Set.univ fun t => F t • dyn (H N) t (A N))) (Z N) k ≤
      ENNReal.ofReal (|Ck k| * (Z N).card * moment F (4 * k) *
        (‖opCLM (iota η δ₀ (Ts.T N) (A N))‖ + |CA (max k 3)| * (N : ℝ) ^ m)) := by
    refine hQ.trans ?_
    calc ENNReal.ofReal (Ck k * (Z N).card * moment F (4 * k)) *
          (ENNReal.ofReal ‖opCLM (iota η δ₀ (Ts.T N) (A N))‖ +
            setNorm (iota η δ₀ (Ts.T N) (A N)) (Z N) (max (k : ℝ) 3))
        ≤ ENNReal.ofReal (|Ck k| * (Z N).card * moment F (4 * k)) *
          (ENNReal.ofReal ‖opCLM (iota η δ₀ (Ts.T N) (A N))‖ + ENNReal.ofReal (|CA (max k 3)| * (N : ℝ) ^ m)) := by
          gcongr
          exact le_abs_self _
      _ = _ := by
          rw [← ENNReal.ofReal_add (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hNpos.le _)),
            ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (abs_nonneg _) hZ0) hM0)]
  have hfinQ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  obtain ⟨B, hB, hQB⟩ := exists_approx_of_setNorm hfinQ hr
  refine ⟨B, hB, hQB.trans ?_⟩
  have hreal := ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hZ0) hM0) hb0)
    hbound
  have hρ : 0 ≤ (1 + r) ^ (-(k : ℝ)) := Real.rpow_nonneg (by linarith) _
  refine mul_le_mul_of_nonneg_right ?_ hρ
  refine hreal.trans ?_
  -- `|Ck| |Z| M (‖A‖ + |CA| N^m) ≤ |Ck| |C| M (|C| + |CA|) N^{max m m' + m''}`
  have hZb : ((Z N).card : ℝ) ≤ |C| * (N : ℝ) ^ m'' :=
    (hZ N hN).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hNpos.le _))
  have hAb : ‖opCLM (iota η δ₀ (Ts.T N) (A N))‖ ≤ |C| * (N : ℝ) ^ m' := by
    rw [hnorm]
    exact (hAn N hN).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hNpos.le _))
  have hp1 : (N : ℝ) ^ m'' * (N : ℝ) ^ m' ≤ (N : ℝ) ^ (max m m' + m'') :=
    rpow_mul_rpow_le hN1 (by linarith [le_max_right m m'])
  have hp2 : (N : ℝ) ^ m'' * (N : ℝ) ^ m ≤ (N : ℝ) ^ (max m m' + m'') :=
    rpow_mul_rpow_le hN1 (by linarith [le_max_left m m'])
  have hx1 : 0 ≤ (N : ℝ) ^ m'' := Real.rpow_nonneg hNpos.le _
  have hx2 : 0 ≤ (N : ℝ) ^ m' := Real.rpow_nonneg hNpos.le _
  have hx3 : 0 ≤ (N : ℝ) ^ m := Real.rpow_nonneg hNpos.le _
  have hK : 0 ≤ |Ck k| * moment F (4 * k) := mul_nonneg (abs_nonneg _) hM0
  calc |Ck k| * (Z N).card * moment F (4 * k) * (‖opCLM (iota η δ₀ (Ts.T N) (A N))‖ + |CA (max k 3)| * (N : ℝ) ^ m)
      = (|Ck k| * moment F (4 * k)) * ((Z N).card *
          (‖opCLM (iota η δ₀ (Ts.T N) (A N))‖ + |CA (max k 3)| * (N : ℝ) ^ m)) := by ring
    _ ≤ (|Ck k| * moment F (4 * k)) * ((|C| * (N : ℝ) ^ m'') *
          (|C| * (N : ℝ) ^ m' + |CA (max k 3)| * (N : ℝ) ^ m)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hZb (add_le_add hAb le_rfl) hb0
          (mul_nonneg (abs_nonneg _) hx1)) hK
    _ = (|Ck k| * moment F (4 * k)) * |C| * (|C| * ((N : ℝ) ^ m'' * (N : ℝ) ^ m') +
          |CA (max k 3)| * ((N : ℝ) ^ m'' * (N : ℝ) ^ m)) := by ring
    _ ≤ (|Ck k| * moment F (4 * k)) * |C| * (|C| * (N : ℝ) ^ (max m m' + m'') +
          |CA (max k 3)| * (N : ℝ) ^ (max m m' + m'')) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hp1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hp2 (abs_nonneg _))) (mul_nonneg hK (abs_nonneg _))
    _ = _ := by ring

/-! ## Lemma 5.7 (the commutator with the Hamiltonian) -/

section CommutatorH

variable {η : ℝ → ℝ} {δ₀ : ℝ} {Ts : TorusSeq δ₀} {H : (N : ℕ) → FockOp (Ts.T N)}

/-! ### Proof devices for Lemma 5.7 (phase (b); not statements of the paper) -/

theorem norm_H_le (d : H1Data η δ₀ Ts H) {N : ℕ} (hN : N ∈ Ts.idx) :
    ‖toCLM (Ts.T N) (H N)‖ ≤ d.Ch * ((Ts.T N).Lx * (Ts.T N).Ly) := by
  have hint := integrableOn_h d hN
  have h1 : toCLM (Ts.T N) (H N) = ∫ R in fundDom (Ts.T N), opCLM (d.h N R) := by
    rw [d.eq_opIntegral N hN]
    exact opCLM_opIntegral _ _ hint
  rw [h1]
  have hvol : MeasureTheory.volume (fundDom (Ts.T N)) < ⊤ := (volume_fundDom_ne_top (Ts.T N)).lt_top
  refine (norm_setIntegral_le_of_norm_le_const hvol fun R _ => d.norm_h_le N hN R).trans (le_of_eq ?_)
  congr 1
  simp only [fundDom, Measure.real, Real.volume_Ico, Measure.volume_eq_prod, Measure.prod_prod]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [(Ts.T N).Lx_pos]),
    ENNReal.toReal_ofReal (by linarith [(Ts.T N).Ly_pos])]
  ring

/-- The proof of Lemma 5.7: "`By (H1), $\norm{H_N}\le\int\norm{h_R}\,\dd R\le C_h\abs{\Tor_N}=4\pi C_hN$`" (`|𝕋_N| = L_xL_y`). -/
theorem norm_HN_le_of_H1 (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (H N)‖ ≤ d.Ch * ((Ts.T N).Lx * (Ts.T N).Ly) ∧
      d.Ch * ((Ts.T N).Lx * (Ts.T N).Ly) = 4 * π * d.Ch * N := by
  intro N hN
  refine ⟨norm_H_le d hN, ?_⟩
  have harea := (Ts.T N).area
  rw [Ts.T_N N hN] at harea
  rw [harea]
  push_cast
  ring

/-- **Lemma 5.7**: "`and $\norm{[H_N,A_N]}\le2C_h\abs{\Tor_N}\norm{A_N}=8\pi C_hN\norm{A_N}$.`" — for every operator on `𝔉`
(the bound uses no locality). -/
theorem norm_comm_HN_le (d : H1Data η δ₀ Ts H) :
    ∀ N ∈ Ts.idx, ∀ A : FockOp (Ts.T N),
      ‖toCLM (Ts.T N) (H N * A - A * H N)‖ ≤ 2 * d.Ch * ((Ts.T N).Lx * (Ts.T N).Ly) * ‖toCLM (Ts.T N) A‖ ∧
        2 * d.Ch * ((Ts.T N).Lx * (Ts.T N).Ly) * ‖toCLM (Ts.T N) A‖ = 8 * π * d.Ch * N * ‖toCLM (Ts.T N) A‖ := by
  intro N hN A
  have h1 := (norm_HN_le_of_H1 d N hN).1
  refine ⟨?_, ?_⟩
  · calc ‖toCLM (Ts.T N) (H N * A - A * H N)‖ ≤ 2 * ‖toCLM (Ts.T N) (H N)‖ * ‖toCLM (Ts.T N) A‖ := norm_comm_le _ _
      _ ≤ 2 * (d.Ch * ((Ts.T N).Lx * (Ts.T N).Ly)) * ‖toCLM (Ts.T N) A‖ := by
          gcongr
      _ = _ := by ring
  · rw [mul_assoc 2, (norm_HN_le_of_H1 d N hN).2]
    ring

end CommutatorH

/-! ### Proof devices for Lemma 5.7 (phase (b); not statements of the paper)

The paper's proof with one change: for `R` with `d_R > r` the (H1) approximant is taken at radius `r/2` (not `d_R/2`),
which already lies in a ball disjoint from `X^{(r)}`; the operator integrals over the parts of the torus are block C's
entrywise `opIntegral` over `fundDom ∩ 𝒟_≤` and `fundDom \ 𝒟_≤`. -/

section OpIntegralDevices

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem opIntegral_add' (D : Set (ℝ × ℝ)) (f g : ℝ × ℝ → Op S)
    (hf : ∀ m m' : Conf S, IntegrableOn (fun R => f R m m') D) (hg : ∀ m m' : Conf S, IntegrableOn (fun R => g R m m') D) :
    opIntegral D (fun R => f R + g R) = opIntegral D f + opIntegral D g := by
  ext m m'
  simp only [opIntegral, Matrix.of_apply, Matrix.add_apply]
  exact integral_add (hf m m') (hg m m')

theorem opIntegral_split (D E : Set (ℝ × ℝ)) (hE : MeasurableSet E) (f : ℝ × ℝ → Op S)
    (hf : ∀ m m' : Conf S, IntegrableOn (fun R => f R m m') D) :
    opIntegral D f = opIntegral (D ∩ E) f + opIntegral (D \ E) f := by
  ext m m'
  simp only [opIntegral, Matrix.of_apply, Matrix.add_apply]
  exact (integral_inter_add_sdiff hE (hf m m')).symm

theorem opIntegral_comm (D : Set (ℝ × ℝ)) (f : ℝ × ℝ → Op S) (X : Op S)
    (hf : ∀ m m' : Conf S, IntegrableOn (fun R => f R m m') D) :
    opIntegral D (fun R => f R * X - X * f R) = opIntegral D f * X - X * opIntegral D f := by
  have h := opIntegral_map (LinearMap.mulRight ℂ X - LinearMap.mulLeft ℂ X) D f hf
  simp only [LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at h
  exact h.symm

theorem norm_opIntegral_le_const (D : Set (ℝ × ℝ)) (hD : MeasureTheory.volume D < ⊤) (f : ℝ × ℝ → Op S)
    (hf : ∀ m m' : Conf S, IntegrableOn (fun R => f R m m') D) {M : ℝ} (hM : ∀ R ∈ D, ‖opCLM (f R)‖ ≤ M) :
    ‖opCLM (opIntegral D f)‖ ≤ M * MeasureTheory.volume.real D := by
  rw [opCLM_opIntegral D f hf]
  exact norm_setIntegral_le_of_norm_le_const hD hM

theorem opIntegral_mem_Alg (D : Set (ℝ × ℝ)) (hDm : MeasurableSet D) (f : ℝ × ℝ → Op S)
    (hf : ∀ m m' : Conf S, IntegrableOn (fun R => f R m m') D) {Y : Finset S} (hY : ∀ R ∈ D, f R ∈ Alg Y) :
    opIntegral D f ∈ Alg Y := by
  have hE : condExp Y (opIntegral D f) = opIntegral D f := by
    have h := opIntegral_map (condExpLM Y) D f hf
    simp only [condExpLM_apply] at h
    rw [h]
    ext m m'
    simp only [opIntegral, Matrix.of_apply]
    refine setIntegral_congr_fun hDm fun R hR => ?_
    rw [Fermion.Pilot.JW.condExp_of_mem (hY R hR).1]
  have hP : opIntegral D f * parityOp = parityOp * opIntegral D f := by
    have h1 := opIntegral_map (LinearMap.mulRight ℂ (parityOp : Op S)) D f hf
    have h2 := opIntegral_map (LinearMap.mulLeft ℂ (parityOp : Op S)) D f hf
    simp only [LinearMap.mulRight_apply, LinearMap.mulLeft_apply] at h1 h2
    rw [h1, h2]
    ext m m'
    simp only [opIntegral, Matrix.of_apply]
    refine setIntegral_congr_fun hDm fun R hR => ?_
    rw [(hY R hR).2.eq]
  refine ⟨?_, hP⟩
  rw [← hE]
  exact Fermion.Pilot.JW.condExp_mem Y _

theorem measurable_entry_comm {f : ℝ × ℝ → Op S} (hf : ∀ m m', Measurable fun R => f R m m') (X : Op S) :
    ∀ m m', Measurable fun R => (f R * X - X * f R) m m' := by
  intro m m'
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  exact (Finset.measurable_sum _ fun j _ => (hf m j).mul_const _).sub
    (Finset.measurable_sum _ fun j _ => (hf j m').const_mul _)

theorem integrableOn_entry_of_bounded {D : Set (ℝ × ℝ)} (hD : MeasureTheory.volume D ≠ ⊤) {f : ℝ × ℝ → Op S}
    (hf : ∀ m m', Measurable fun R => f R m m') {M : ℝ} (hM : ∀ R, ‖opCLM (f R)‖ ≤ M) :
    ∀ m m' : Conf S, IntegrableOn (fun R => f R m m') D := by
  intro m m'
  refine MeasureTheory.Measure.integrableOn_of_bounded hD (hf m m').aestronglyMeasurable (M := M) ?_
  exact Filter.Eventually.of_forall fun R => (norm_entry_le _ m m').trans (hM R)

end OpIntegralDevices

theorem flatDist_comm' (T : Torus) (a b : ℝ × ℝ) : flatDist T a b = flatDist T b a := by
  simp only [flatDist]
  rw [← neg_sub a.1, ← neg_sub a.2, pdist_neg, pdist_neg]

theorem volume_real_fundDom (T : Torus) : MeasureTheory.volume.real (fundDom T) = T.Lx * T.Ly := by
  simp only [fundDom, Measure.real, Real.volume_Ico, Measure.volume_eq_prod, Measure.prod_prod]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [T.Lx_pos]),
    ENNReal.toReal_ofReal (by linarith [T.Ly_pos])]
  ring

theorem one_add_half_rpow_le {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    (1 + r / 2) ^ (-(k : ℝ)) ≤ 2 ^ k * (1 + r) ^ (-(k : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_natCast,
    ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by linarith) k

theorem arith57 {T1 T2 T3 h α β γ a x P N ρ q π' : ℝ} (hh : 0 ≤ h) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hN : 0 ≤ N)
    (hρ : 0 ≤ ρ) (hq : 0 ≤ q) (hπ : 0 ≤ π') (hx : x ≤ P) (ha : a ≤ γ * P)
    (h1 : T1 ≤ 2 * (h * (4 * π' * N)) * (α * x * ρ)) (h2 : T2 ≤ (2 * (2 * β * ρ) * a) * (4 * π' * N))
    (h3 : T3 ≤ (2 * (β * (q * ρ)) * a) * (4 * π' * N)) :
    T1 + T2 + T3 ≤ (8 * π' * h * α + (16 * π' + 8 * q * π') * β * γ) * (N * P) * ρ := by
  have c1 : 0 ≤ 8 * π' * h * α * N * ρ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hπ) hh) hα) hN) hρ
  have c2 : 0 ≤ 16 * π' * β * N * ρ := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hπ) hβ) hN) hρ
  have c3 : 0 ≤ 8 * q * π' * β * N * ρ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hq) hπ) hβ) hN) hρ
  have e1 : 2 * (h * (4 * π' * N)) * (α * x * ρ) ≤ 8 * π' * h * α * (N * P) * ρ := by
    calc 2 * (h * (4 * π' * N)) * (α * x * ρ) = 8 * π' * h * α * N * ρ * x := by ring
      _ ≤ 8 * π' * h * α * N * ρ * P := mul_le_mul_of_nonneg_left hx c1
      _ = _ := by ring
  have e2 : (2 * (2 * β * ρ) * a) * (4 * π' * N) ≤ 16 * π' * β * γ * (N * P) * ρ := by
    calc (2 * (2 * β * ρ) * a) * (4 * π' * N) = 16 * π' * β * N * ρ * a := by ring
      _ ≤ 16 * π' * β * N * ρ * (γ * P) := mul_le_mul_of_nonneg_left ha c2
      _ = _ := by ring
  have e3 : (2 * (β * (q * ρ)) * a) * (4 * π' * N) ≤ 8 * q * π' * β * γ * (N * P) * ρ := by
    calc (2 * (β * (q * ρ)) * a) * (4 * π' * N) = 8 * q * π' * β * N * ρ * a := by ring
      _ ≤ 8 * q * π' * β * N * ρ * (γ * P) := mul_le_mul_of_nonneg_left ha c3
      _ = _ := by ring
  calc T1 + T2 + T3 ≤ 8 * π' * h * α * (N * P) * ρ + 16 * π' * β * γ * (N * P) * ρ +
        8 * q * π' * β * γ * (N * P) * ρ := add_le_add (add_le_add (h1.trans e1) (h2.trans e2)) (h3.trans e3)
    _ = _ := by ring

/-- **Lemma 5.7**: "`If $A=(A_N)\in\AS_X$ is even, with prefactor exponent $m$ and $\norm{A_N}\le CN^{m'}$, then $(\iu[H_N,A_N])_N\in\AS_X$ with prefactor exponent $1+\max\{m,m'\}$`"
— the new constants after `δ₀`, `C`, the exponents, the constants of `A`, `C_h`, `C^H` ("`with $C'_k$ depending only on $C$, $C_h$, $C^H_k$ and the constants of $A$`"). -/
theorem almostSupported_comm_HN {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (C m m' : ℝ) (CA : ℕ → ℝ) (Ch : ℝ) (CH : ℕ → ℝ) :
    ∃ C' : ℕ → ℝ, ∀ (η : ℝ → ℝ), IsProfile η → ∀ (Ts : TorusSeq δ₀) (H : (N : ℕ) → FockOp (Ts.T N))
      (d : H1Data η δ₀ Ts H), d.Ch = Ch → d.CH = CH →
      ∀ (X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))) (A : (N : ℕ) → FockOp (Ts.T N)),
        (∀ N ∈ Ts.idx, IsEven (A N)) → ASBound η δ₀ Ts X A m CA →
        (∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (A N)‖ ≤ C * (N : ℝ) ^ m') →
          ASBound η δ₀ Ts X (fun N => (I : ℂ) • (H N * A N - A N * H N)) (1 + max m m') C' := by
  refine ⟨fun k => 3 ^ k * (8 * π * |Ch| * |CA k| + (16 * π + 2 ^ (k + 3) * π) * |CH k| * (|C| + |CA 0|)), ?_⟩
  intro η hη Ts H d hCh hCH X A hAe hAS hAn
  have hm0 : 0 ≤ m := hAS.1
  refine ⟨by have := le_max_left m m'; linarith, ?_⟩
  intro k N hN r hr
  have hT := Ts.admissible N hN
  have hN1 := one_le_of_mem_idx Ts hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hρ0 : 0 ≤ r / 3 := div_nonneg hr (by norm_num)
  -- the best approximant of `ι(A_N)` in `Alg(X^{(r/3)})`
  obtain ⟨Aρ, hAρ, hAρinf⟩ := exists_nearest_le_iInf (fat (X N) (r / 3)) (iota η δ₀ (Ts.T N) (A N))
  have hbddA : BddBelow (Set.range fun A' : Alg (fat (X N) (r / 3)) =>
      ‖opCLM (iota η δ₀ (Ts.T N) (A N) - (A' : Op (Slot δ₀ (Ts.T N))))‖) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
  have hNm : 0 ≤ (N : ℝ) ^ m := Real.rpow_nonneg hNpos.le _
  have hρk : ∀ j : ℕ, 0 ≤ (1 + r / 3) ^ (-(j : ℝ)) := fun j => Real.rpow_nonneg (by linarith) _
  have hAρk : ∀ j : ℕ, ‖opCLM (iota η δ₀ (Ts.T N) (A N) - Aρ)‖ ≤ |CA j| * (N : ℝ) ^ m * (1 + r / 3) ^ (-(j : ℝ)) := by
    intro j
    obtain ⟨A', hA'm, hA'⟩ := hAS.2 j N hN (r / 3) hρ0
    exact hAρinf.trans ((ciInf_le hbddA ⟨A', hA'm⟩).trans (hA'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) hNm) (hρk j))))
  have haN : ‖opCLM Aρ‖ ≤ |C| * (N : ℝ) ^ m' + |CA 0| * (N : ℝ) ^ m := by
    have h := norm_approx_le hη hδ₀ hT (A N) Aρ
    have h0 := hAρk 0
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at h0
    have hAn' : ‖toCLM (Ts.T N) (A N)‖ ≤ |C| * (N : ℝ) ^ m' :=
      (hAn N hN).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hNpos.le _))
    linarith
  -- the parts of the torus
  have hfd : MeasureTheory.volume (fundDom (Ts.T N)) ≠ ⊤ := volume_fundDom_ne_top _
  have hfdm : MeasurableSet (fundDom (Ts.T N)) := measurableSet_Ico.prod measurableSet_Ico
  have hDle : MeasurableSet (⋃ s ∈ fat (X N) (r / 3),
      {R : ℝ × ℝ | flatDist (Ts.T N) (centre δ₀ (Ts.T N) s) R ≤ r / 3}) :=
    Finset.measurableSet_biUnion _ fun s _ =>
      measurableSet_le (continuous_flatDist_right _ _).measurable measurable_const
  set Dle : Set (ℝ × ℝ) := ⋃ s ∈ fat (X N) (r / 3),
    {R : ℝ × ℝ | flatDist (Ts.T N) (centre δ₀ (Ts.T N) s) R ≤ r / 3} with hDledef
  have hvle : ∀ E : Set (ℝ × ℝ), E ⊆ fundDom (Ts.T N) →
      MeasureTheory.volume.real E ≤ (Ts.T N).Lx * (Ts.T N).Ly := fun E hE =>
    (measureReal_mono hE hfd).trans (le_of_eq (volume_real_fundDom _))
  have harea : (Ts.T N).Lx * (Ts.T N).Ly = 4 * π * N := by
    have h := (Ts.T N).area
    rw [Ts.T_N N hN] at h
    rw [h]; push_cast; ring
  -- the integrands, their measurability and bounds
  have hm1 : ∀ m₁ m₂, Measurable fun R => iota η δ₀ (Ts.T N) (d.h N R) m₁ m₂ :=
    measurable_iota_entry hT hη hδ₀ (d.h_measurable N hN)
  have hm2 : ∀ m₁ m₂, Measurable fun R => hTilde d N R (r / 3) m₁ m₂ := hTilde_measurable hη hδ₀ d N hN (r / 3)
  have hb1 : ∀ R, ‖opCLM (iota η δ₀ (Ts.T N) (d.h N R))‖ ≤ d.Ch := fun R => by
    rw [norm_iota hη hδ₀ hT]; exact d.norm_h_le N hN R
  have hb2 : ∀ R, ‖opCLM (hTilde d N R (r / 3))‖ ≤ d.Ch := fun R => (norm_hTilde_le hη hδ₀ d N hN R (r / 3)).1.trans
    (norm_hTilde_le hη hδ₀ d N hN R (r / 3)).2
  have hcomm_bound : ∀ (P : Op (Slot δ₀ (Ts.T N))), ‖opCLM (P * Aρ - Aρ * P)‖ ≤ 2 * ‖opCLM P‖ * ‖opCLM Aρ‖ :=
    fun P => norm_comm_le _ _
  have hi1 : ∀ D : Set (ℝ × ℝ), MeasureTheory.volume D ≠ ⊤ → ∀ m₁ m₂, IntegrableOn
      (fun R => (iota η δ₀ (Ts.T N) (d.h N R) * Aρ - Aρ * iota η δ₀ (Ts.T N) (d.h N R)) m₁ m₂) D := fun D hD =>
    integrableOn_entry_of_bounded hD (measurable_entry_comm hm1 Aρ) (M := 2 * d.Ch * ‖opCLM Aρ‖)
      fun R => (hcomm_bound _).trans (by gcongr; exact hb1 R)
  have hi2 : ∀ D : Set (ℝ × ℝ), MeasureTheory.volume D ≠ ⊤ → ∀ m₁ m₂, IntegrableOn
      (fun R => (hTilde d N R (r / 3) * Aρ - Aρ * hTilde d N R (r / 3)) m₁ m₂) D := fun D hD =>
    integrableOn_entry_of_bounded hD (measurable_entry_comm hm2 Aρ) (M := 2 * d.Ch * ‖opCLM Aρ‖)
      fun R => (hcomm_bound _).trans (by gcongr; exact hb2 R)
  have hm12 : ∀ m₁ m₂, Measurable fun R => (iota η δ₀ (Ts.T N) (d.h N R) - hTilde d N R (r / 3)) m₁ m₂ :=
    fun m₁ m₂ => by simp only [Matrix.sub_apply]; exact (hm1 m₁ m₂).sub (hm2 m₁ m₂)
  have hi12 : ∀ D : Set (ℝ × ℝ), MeasureTheory.volume D ≠ ⊤ → ∀ m₁ m₂, IntegrableOn
      (fun R => ((iota η δ₀ (Ts.T N) (d.h N R) - hTilde d N R (r / 3)) * Aρ -
        Aρ * (iota η δ₀ (Ts.T N) (d.h N R) - hTilde d N R (r / 3))) m₁ m₂) D := fun D hD =>
    integrableOn_entry_of_bounded hD (measurable_entry_comm hm12 Aρ) (M := 2 * (d.Ch + d.Ch) * ‖opCLM Aρ‖)
      fun R => (hcomm_bound _).trans (by
        gcongr
        rw [opCLM_sub']
        exact (norm_sub_le _ _).trans (add_le_add (hb1 R) (hb2 R)))
  have hvfd1 : MeasureTheory.volume (fundDom (Ts.T N) ∩ Dle) ≠ ⊤ :=
    ne_top_of_le_ne_top hfd (MeasureTheory.measure_mono Set.inter_subset_left)
  have hvfd2 : MeasureTheory.volume (fundDom (Ts.T N) \ Dle) ≠ ⊤ :=
    ne_top_of_le_ne_top hfd (MeasureTheory.measure_mono Set.sdiff_subset)
  -- the decomposition
  set B : Op (Slot δ₀ (Ts.T N)) := (I : ℂ) • opIntegral (fundDom (Ts.T N) ∩ Dle)
    (fun R => hTilde d N R (r / 3) * Aρ - Aρ * hTilde d N R (r / 3)) with hBdef
  have hHhat := Hhat_eq_opIntegral hη hδ₀ d N hN
  have hdec : iota η δ₀ (Ts.T N) ((I : ℂ) • (H N * A N - A N * H N)) - B =
      (I : ℂ) • ((Hhat η δ₀ Ts H N * (iota η δ₀ (Ts.T N) (A N) - Aρ) -
          (iota η δ₀ (Ts.T N) (A N) - Aρ) * Hhat η δ₀ Ts H N) +
        opIntegral (fundDom (Ts.T N) ∩ Dle) (fun R => (iota η δ₀ (Ts.T N) (d.h N R) - hTilde d N R (r / 3)) * Aρ -
          Aρ * (iota η δ₀ (Ts.T N) (d.h N R) - hTilde d N R (r / 3))) +
        opIntegral (fundDom (Ts.T N) \ Dle)
          (fun R => iota η δ₀ (Ts.T N) (d.h N R) * Aρ - Aρ * iota η δ₀ (Ts.T N) (d.h N R))) := by
    have hcommH : Hhat η δ₀ Ts H N * Aρ - Aρ * Hhat η δ₀ Ts H N =
        opIntegral (fundDom (Ts.T N))
          (fun R => iota η δ₀ (Ts.T N) (d.h N R) * Aρ - Aρ * iota η δ₀ (Ts.T N) (d.h N R)) := by
      rw [hHhat, opIntegral_comm _ _ _ (fun m₁ m₂ => integrableOn_entry_of_bounded hfd hm1 hb1 m₁ m₂)]
    have hsplit := opIntegral_split (fundDom (Ts.T N)) Dle hDle
      (fun R => iota η δ₀ (Ts.T N) (d.h N R) * Aρ - Aρ * iota η δ₀ (Ts.T N) (d.h N R)) (hi1 _ hfd)
    have hadd := opIntegral_add' (fundDom (Ts.T N) ∩ Dle)
      (fun R => hTilde d N R (r / 3) * Aρ - Aρ * hTilde d N R (r / 3))
      (fun R => (iota η δ₀ (Ts.T N) (d.h N R) - hTilde d N R (r / 3)) * Aρ -
          Aρ * (iota η δ₀ (Ts.T N) (d.h N R) - hTilde d N R (r / 3))) (hi2 _ hvfd1) (hi12 _ hvfd1)
    have hpt : (fun R => hTilde d N R (r / 3) * Aρ - Aρ * hTilde d N R (r / 3) +
        ((iota η δ₀ (Ts.T N) (d.h N R) - hTilde d N R (r / 3)) * Aρ -
          Aρ * (iota η δ₀ (Ts.T N) (d.h N R) - hTilde d N R (r / 3)))) =
        fun R => iota η δ₀ (Ts.T N) (d.h N R) * Aρ - Aρ * iota η δ₀ (Ts.T N) (d.h N R) := by
      funext R; noncomm_ring
    rw [hpt] at hadd
    have hι : iota η δ₀ (Ts.T N) ((I : ℂ) • (H N * A N - A N * H N)) =
        (I : ℂ) • (Hhat η δ₀ Ts H N * iota η δ₀ (Ts.T N) (A N) - iota η δ₀ (Ts.T N) (A N) * Hhat η δ₀ Ts H N) := by
      rw [iota_smul hη hδ₀ hT, iota_sub' hη hδ₀ hT, iota_mul hη hδ₀ hT, iota_mul hη hδ₀ hT]
    rw [hι, hBdef, ← smul_sub]
    congr 1
    have e : Hhat η δ₀ Ts H N * iota η δ₀ (Ts.T N) (A N) - iota η δ₀ (Ts.T N) (A N) * Hhat η δ₀ Ts H N =
        (Hhat η δ₀ Ts H N * (iota η δ₀ (Ts.T N) (A N) - Aρ) - (iota η δ₀ (Ts.T N) (A N) - Aρ) * Hhat η δ₀ Ts H N) +
          (Hhat η δ₀ Ts H N * Aρ - Aρ * Hhat η δ₀ Ts H N) := by noncomm_ring
    rw [e, hcommH, hsplit, hadd]
    abel
  -- `B ∈ Alg(X^{(r)})`
  have hBmem : B ∈ Alg (fat (X N) r) := by
    have h3 : r / 3 + r / 3 + r / 3 = r := by ring
    refine Alg_smul_mem _ (opIntegral_mem_Alg _ (hfdm.inter hDle) _ (hi2 _ hvfd1) fun R hR => ?_)
    obtain ⟨s', hs', hs'R⟩ := Set.mem_iUnion₂.mp hR.2
    have hball : slotBall δ₀ (Ts.T N) R (r / 3) ⊆ fat (X N) r := by
      intro s hs
      simp only [slotBall, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      obtain ⟨x, hx, hdx⟩ := mem_fat.mp hs'
      rw [mem_fat]
      refine ⟨x, hx, ?_⟩
      have t1 := flatDist_triangle (T := Ts.T N) (centre δ₀ (Ts.T N) s) R (centre δ₀ (Ts.T N) s')
      have t2 := flatDist_triangle (T := Ts.T N) (centre δ₀ (Ts.T N) s) (centre δ₀ (Ts.T N) s')
        (centre δ₀ (Ts.T N) x)
      rw [flatDist_comm' (Ts.T N) R] at t1
      simp only [Set.mem_ofPred_eq] at hs'R
      show flatDist (Ts.T N) (centre δ₀ (Ts.T N) s) (centre δ₀ (Ts.T N) x) ≤ r
      have hdx' : flatDist (Ts.T N) (centre δ₀ (Ts.T N) s') (centre δ₀ (Ts.T N) x) ≤ r / 3 := hdx
      linarith
    have hA2 : Aρ ∈ Alg (fat (X N) r) := Alg_mono (fat_mono_right _ (by linarith)) hAρ
    have hh2 : hTilde d N R (r / 3) ∈ Alg (fat (X N) r) :=
      Alg_mono hball (hTilde_mem_Alg hη hδ₀ d N hN R (r / 3))
    exact ⟨sub_mem (mul_mem hh2.1 hA2.1) (mul_mem hA2.1 hh2.1),
      ((hh2.2.mul_left hA2.2).sub_left (hA2.2.mul_left hh2.2))⟩
  refine ⟨B, hBmem, ?_⟩
  rw [hdec, opCLM_smul', norm_smul, Complex.norm_I, one_mul, opCLM_add', opCLM_add']
  -- the three bounds
  have hCH' : ∀ j, d.CH j ≤ |CH j| := fun j => by rw [hCH]; exact le_abs_self _
  have hCh' : d.Ch ≤ |Ch| := by rw [hCh]; exact le_abs_self _
  have hHn : ‖opCLM (Hhat η δ₀ Ts H N)‖ ≤ |Ch| * (4 * π * N) := by
    rw [norm_iota hη hδ₀ hT, ← harea]
    exact (norm_HN_le_of_H1 d N hN).1.trans (mul_le_mul_of_nonneg_right hCh'
      (mul_pos (Ts.T N).Lx_pos (Ts.T N).Ly_pos).le)
  have hT1 : ‖opCLM (Hhat η δ₀ Ts H N * (iota η δ₀ (Ts.T N) (A N) - Aρ) -
      (iota η δ₀ (Ts.T N) (A N) - Aρ) * Hhat η δ₀ Ts H N)‖ ≤
      2 * (|Ch| * (4 * π * N)) * (|CA k| * (N : ℝ) ^ m * (1 + r / 3) ^ (-(k : ℝ))) :=
    (norm_comm_le _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hHn (by norm_num)) (hAρk k) (norm_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) (by positivity))))
  have haN0 : 0 ≤ |C| * (N : ℝ) ^ m' + |CA 0| * (N : ℝ) ^ m := (norm_nonneg _).trans haN
  have hT2 : ‖opCLM (opIntegral (fundDom (Ts.T N) ∩ Dle) (fun R => (iota η δ₀ (Ts.T N) (d.h N R) -
      hTilde d N R (r / 3)) * Aρ - Aρ * (iota η δ₀ (Ts.T N) (d.h N R) - hTilde d N R (r / 3))))‖ ≤
      (2 * (2 * |CH k| * (1 + r / 3) ^ (-(k : ℝ))) * (|C| * (N : ℝ) ^ m' + |CA 0| * (N : ℝ) ^ m)) *
        (4 * π * N) := by
    refine (norm_opIntegral_le_const _ hvfd1.lt_top _ (hi12 _ hvfd1)
      (M := 2 * (2 * |CH k| * (1 + r / 3) ^ (-(k : ℝ))) * (|C| * (N : ℝ) ^ m' + |CA 0| * (N : ℝ) ^ m))
      fun R _ => ?_).trans ?_
    · refine (norm_comm_le _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by norm_num)) haN (norm_nonneg _)
        (by positivity))
      refine (norm_iota_sub_hTilde_le hη hδ₀ d N hN R (r / 3) hρ0 k).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hCH' k) (by norm_num)) (hρk k)
    · rw [← harea]
      exact mul_le_mul_of_nonneg_left (hvle _ Set.inter_subset_left) (by positivity)
  have hT3 : ‖opCLM (opIntegral (fundDom (Ts.T N) \ Dle)
      (fun R => iota η δ₀ (Ts.T N) (d.h N R) * Aρ - Aρ * iota η δ₀ (Ts.T N) (d.h N R)))‖ ≤
      (2 * (|CH k| * (2 ^ k * (1 + r / 3) ^ (-(k : ℝ)))) * (|C| * (N : ℝ) ^ m' + |CA 0| * (N : ℝ) ^ m)) *
        (4 * π * N) := by
    refine (norm_opIntegral_le_const _ hvfd2.lt_top _ (hi1 _ hvfd2)
      (M := 2 * (|CH k| * (2 ^ k * (1 + r / 3) ^ (-(k : ℝ)))) * (|C| * (N : ℝ) ^ m' + |CA 0| * (N : ℝ) ^ m))
      fun R hR => ?_).trans ?_
    · have hRn : R ∉ Dle := hR.2
      obtain ⟨h', hh'm, hh'⟩ := d.approx k N hN R (r / 3 / 2) (by positivity)
      have hdisj : Disjoint (slotBall δ₀ (Ts.T N) R (r / 3 / 2)) (fat (X N) (r / 3)) := by
        rw [Finset.disjoint_left]
        intro s hs hsX
        apply hRn
        simp only [slotBall, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        exact Set.mem_iUnion₂.mpr ⟨s, hsX, by simp only [Set.mem_ofPred_eq]; linarith⟩
      have hc : h' * Aρ = Aρ * h' := (commute_of_mem_Alg_of_mem_Alg hdisj hh'm hAρ).eq
      have e : iota η δ₀ (Ts.T N) (d.h N R) * Aρ - Aρ * iota η δ₀ (Ts.T N) (d.h N R) =
          (iota η δ₀ (Ts.T N) (d.h N R) - h') * Aρ - Aρ * (iota η δ₀ (Ts.T N) (d.h N R) - h') := by
        rw [Matrix.sub_mul, Matrix.mul_sub, hc]; abel
      rw [e]
      refine (norm_comm_le _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by norm_num)) haN (norm_nonneg _)
        (by positivity))
      refine hh'.trans ?_
      have hhalf := one_add_half_rpow_le hρ0 k
      exact mul_le_mul (hCH' k) hhalf (Real.rpow_nonneg (by positivity) _) (abs_nonneg _)
    · rw [← harea]
      exact mul_le_mul_of_nonneg_left (hvle _ Set.sdiff_subset) (by positivity)
  -- assembling
  have hNmax : (N : ℝ) ^ m ≤ (N : ℝ) ^ (max m m') := rpow_le_rpow_of_one_le hN1 (le_max_left _ _)
  have hNmax' : (N : ℝ) ^ m' ≤ (N : ℝ) ^ (max m m') := rpow_le_rpow_of_one_le hN1 (le_max_right _ _)
  have hNe : (N : ℝ) ^ (1 + max m m') = N * (N : ℝ) ^ (max m m') := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  have hNmx0 : 0 ≤ (N : ℝ) ^ (max m m') := Real.rpow_nonneg hNpos.le _
  have haN' : |C| * (N : ℝ) ^ m' + |CA 0| * (N : ℝ) ^ m ≤ (|C| + |CA 0|) * (N : ℝ) ^ (max m m') := by
    nlinarith [abs_nonneg C, abs_nonneg (CA 0)]
  have hρ3 := one_add_div_three_rpow_le hr k
  have hk0 : 0 ≤ (1 + r / 3) ^ (-(k : ℝ)) := hρk k
  have hpi := Real.pi_pos
  have hX1 : 0 ≤ |CH k| := abs_nonneg _
  have hX2 : 0 ≤ |Ch| := abs_nonneg _
  have hX3 : 0 ≤ |CA k| := abs_nonneg _
  have hX4 : 0 ≤ |C| + |CA 0| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have h2k : (0 : ℝ) ≤ 2 ^ k := by positivity
  have h8 : (2 : ℝ) ^ (k + 3) = 8 * 2 ^ k := by rw [pow_add]; norm_num; ring
  have hfin := arith57 (abs_nonneg Ch) (abs_nonneg (CA k)) (abs_nonneg (CH k)) hNpos.le hk0 h2k hpi.le hNmax
    haN' hT1 hT2 hT3
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (hfin.trans ?_))
  beta_reduce
  rw [h8]
  calc (8 * π * |Ch| * |CA k| + (16 * π + 8 * 2 ^ k * π) * |CH k| * (|C| + |CA 0|)) * (N * (N : ℝ) ^ (max m m')) *
        (1 + r / 3) ^ (-(k : ℝ))
      ≤ (8 * π * |Ch| * |CA k| + (16 * π + 8 * 2 ^ k * π) * |CH k| * (|C| + |CA 0|)) *
          (N * (N : ℝ) ^ (max m m')) * (3 ^ k * (1 + r) ^ (-(k : ℝ))) := by
        refine mul_le_mul_of_nonneg_left hρ3 ?_
        refine mul_nonneg (add_nonneg ?_ ?_) (mul_nonneg hNpos.le hNmx0)
        · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpi.le) hX2) hX3
        · exact mul_nonneg (mul_nonneg (add_nonneg (by positivity) (by positivity)) hX1) hX4
    _ = _ := by rw [hNe]; ring

/-! ## Definition 5.8 (the filters) -/

/-- **Definition 5.8**: "`Fix an even $\vartheta\in C_c^\infty((-1,1))$ with $0\le\vartheta\le1$ and $\vartheta=1$ near $0$.`" -/
structure IsCutoff (ϑ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ ϑ
  tsupport_subset : tsupport ϑ ⊆ Set.Ioo (-1) 1
  even : ∀ w : ℝ, ϑ (-w) = ϑ w
  nonneg : ∀ w : ℝ, 0 ≤ ϑ w
  le_one : ∀ w : ℝ, ϑ w ≤ 1
  eventually_eq_one : ∀ᶠ w in 𝓝 (0 : ℝ), ϑ w = 1

/-- **Definition 5.8**: "`For $\gamma>0$ let`" "`\widehat W_\gamma(\omega):=\frac{\iu\,(1-\vartheta(\omega/\gamma))}{\omega},`"
(at `ω = 0` Lean's `x/0 = 0`, which is the continuous extension since `1 − ϑ(ω/γ) = 0` near `0`). -/
def What (ϑ : ℝ → ℝ) (γ w : ℝ) : ℂ :=
  I * ((1 - ϑ (w / γ) : ℝ) : ℂ) / (w : ℂ)

/-- **Definition 5.8**: "`\Wg(t):=\frac1{2\pi}\lim_{\Omega\to\infty}\int_{-\Omega}^{\Omega}\widehat W_\gamma(\omega)e^{\iu\omega t}\,\dd\omega ,`"
"`an improper integral, since $\widehat W_\gamma$ is not integrable`" — `limUnder` (the module docstring). -/
def Wfilt (ϑ : ℝ → ℝ) (γ t : ℝ) : ℂ :=
  (((2 * π)⁻¹ : ℝ) : ℂ) *
    limUnder atTop fun Ω : ℝ => ∫ w in (-Ω)..Ω, What ϑ γ w * Complex.exp (I * (w : ℂ) * (t : ℂ))

/-- **Definition 5.8**: "`For $\Delta\ge0$ and $\gamma>2\Delta$ fix $\delta\in(0,\gamma/2-\Delta)$ and $\zeta\in C_c^\infty((-\delta,\delta))$ with $\zeta\ge0$ and $\int\zeta=1$`". -/
structure ClusterParams (Δ γ δ : ℝ) (ζ : ℝ → ℝ) : Prop where
  Δ_nonneg : 0 ≤ Δ
  two_mul_Δ_lt : 2 * Δ < γ
  δ_pos : 0 < δ
  δ_lt : δ < γ / 2 - Δ
  contDiff : ContDiff ℝ ∞ ζ
  tsupport_subset : tsupport ζ ⊆ Set.Ioo (-δ) δ
  nonneg : ∀ w : ℝ, 0 ≤ ζ w
  integral_eq_one : ∫ w, ζ w = 1

/-- **Definition 5.8**: "`g(\omega):=\int_\R\zeta(\omega-\omega')\,\one_{\{\omega'<-\gamma/2\}}\,\dd\omega' .`" -/
def gClust (γ : ℝ) (ζ : ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ w', ζ (w - w') * (Set.Iio (-γ / 2)).indicator (fun _ => (1 : ℝ)) w'

section ClusterFilter

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The spectral projection `1_{{E}}(H)` (block A's form: `cfc` of the indicator). -/
def specProj (H : Op S) (E : ℝ) : Op S :=
  cfc (({E} : Set ℝ).indicator (1 : ℝ → ℝ)) H

/-- The spectrum `σ(H) ⊆ ℝ` as a finite set (the real spectrum of a matrix is finite). -/
def specFinset (H : Op S) : Finset ℝ :=
  (Matrix.finite_real_spectrum (A := H)).toFinset

/-- **Definition 5.8**: "`\Qf(A):=g(\ad_{H_N})(A):=\sum_{E,E'\in\sigma(H_N)}g(E-E')\,\one_{\{E\}}(H_N)\,A\,\one_{\{E'\}}(H_N),`"
"`and define $\Qf$ on operators on $\FockS$ in the same way, with $\Hhat_N$ in place of $H_N$.`" — for any operator `H`
(the module docstring). -/
def clusterFilter (g : ℝ → ℝ) (H A : Op S) : Op S :=
  ∑ E ∈ specFinset H, ∑ E' ∈ specFinset H, ((g (E - E') : ℝ) : ℂ) • (specProj H E * A * specProj H E')

end ClusterFilter

/-! ### The paragraph after Definition 5.8 -/

/-! ### Proof devices for the clustering filter `g` (phase (b); not statements of the paper) -/

theorem gClust_eq_one_sub {Δ γ δ : ℝ} {ζ : ℝ → ℝ} (hζ : ClusterParams Δ γ δ ζ) (w : ℝ) :
    gClust γ ζ w = 1 - ∫ v in (-δ)..(w + γ / 2), ζ v := by
  have hζc : Continuous ζ := hζ.contDiff.continuous
  have hζ0 : ∀ v, v ∉ Set.Ioo (-δ) δ → ζ v = 0 := fun v hv =>
    image_eq_zero_of_notMem_tsupport fun h => hv (hζ.tsupport_subset h)
  have hζi : Integrable ζ := by
    have hcs : HasCompactSupport ζ := by
      rw [HasCompactSupport]
      exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport ζ)
        (hζ.tsupport_subset.trans Set.Ioo_subset_Icc_self)
    exact hζc.integrable_of_hasCompactSupport hcs
  -- `g(w) = ∫_{v > w + γ/2} ζ(v) dv`
  have e1 : gClust γ ζ w = ∫ v, (Set.Ioi (w + γ / 2)).indicator ζ v := by
    unfold gClust
    have : (fun w' : ℝ => ζ (w - w') * (Set.Iio (-γ / 2)).indicator (fun _ => (1 : ℝ)) w') =
        fun w' => (Set.Ioi (w + γ / 2)).indicator ζ (w - w') := by
      funext w'
      by_cases h : w' < -γ / 2
      · rw [Set.indicator_of_mem (by simpa using h), mul_one, Set.indicator_of_mem (by simp; linarith)]
      · rw [Set.indicator_of_notMem (by simpa using h), mul_zero, Set.indicator_of_notMem (by simp; linarith)]
    rw [this, integral_sub_left_eq_self (fun v => (Set.Ioi (w + γ / 2)).indicator ζ v) volume w]
  -- `∫_{v > a} ζ = 1 − ∫_{−δ}^{a} ζ`
  have hsplit : ∫ v, (Set.Ioi (w + γ / 2)).indicator ζ v = 1 - ∫ v in Set.Iic (w + γ / 2), ζ v := by
    rw [integral_indicator measurableSet_Ioi, ← hζ.integral_eq_one,
      ← integral_add_compl measurableSet_Iic hζi, Set.compl_Iic]
    ring
  have hIic : ∫ v in Set.Iic (w + γ / 2), ζ v = ∫ v in (-δ)..(w + γ / 2), ζ v := by
    rcases le_or_gt (-δ) (w + γ / 2) with hle | hlt
    · have hzero : ∫ v in Set.Iic (-δ), ζ v = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => hζ0 v ?_
        rw [Set.mem_Ioo, not_and_or]
        left
        simp only [Set.mem_Iic] at hv
        linarith
      have hset : Set.Ioc (-δ) (w + γ / 2) = Set.Iic (w + γ / 2) \ Set.Iic (-δ) := by
        ext v
        simp only [Set.mem_Ioc, Set.mem_sdiff, Set.mem_Iic, not_le]
        exact and_comm
      rw [intervalIntegral.integral_of_le hle, hset, setIntegral_sdiff measurableSet_Iic
        (hζi.integrableOn) (Set.Iic_subset_Iic.mpr hle), hzero, sub_zero]
    · have h1 : ∫ v in Set.Iic (w + γ / 2), ζ v = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => hζ0 v ?_
        rw [Set.mem_Ioo, not_and_or]
        left
        simp only [Set.mem_Iic] at hv
        linarith
      have h2 : ∫ v in Set.Ioc (w + γ / 2) (-δ), ζ v = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => hζ0 v ?_
        rw [Set.mem_Ioo, not_and_or]
        left
        simp only [Set.mem_Ioc] at hv
        linarith [hv.2]
      rw [h1, intervalIntegral.integral_symm, intervalIntegral.integral_of_le hlt.le, h2, neg_zero]
  rw [e1, hsplit, hIic]

/-- "`The function $g$ is smooth and real`" (real by definition). -/
theorem contDiff_gClust {Δ γ δ : ℝ} {ζ : ℝ → ℝ} (hζ : ClusterParams Δ γ δ ζ) : ContDiff ℝ ∞ (gClust γ ζ) := by
  have hζc : Continuous ζ := hζ.contDiff.continuous
  have hrep : gClust γ ζ = fun w => 1 - ∫ v in (-δ)..(w + γ / 2), ζ v := by
    funext w
    exact gClust_eq_one_sub hζ w
  rw [hrep]
  refine contDiff_const.sub ?_
  have hprim : ContDiff ℝ ∞ fun a : ℝ => ∫ v in (-δ)..a, ζ v := by
    rw [contDiff_infty_iff_deriv]
    have hd : ∀ a : ℝ, HasDerivAt (fun a : ℝ => ∫ v in (-δ)..a, ζ v) (ζ a) a := fun a =>
      intervalIntegral.integral_hasDerivAt_right (hζc.intervalIntegrable _ _)
        hζc.aestronglyMeasurable.stronglyMeasurableAtFilter hζc.continuousAt
    refine ⟨fun a => (hd a).differentiableAt, ?_⟩
    have : deriv (fun a : ℝ => ∫ v in (-δ)..a, ζ v) = ζ := funext fun a => (hd a).deriv
    rw [this]
    exact hζ.contDiff
  exact hprim.comp (contDiff_id.add contDiff_const)

/-- "`with $g(\omega)=0$ for $\omega\ge-\Delta$`". -/
theorem gClust_eq_zero {Δ γ δ : ℝ} {ζ : ℝ → ℝ} (hζ : ClusterParams Δ γ δ ζ) {w : ℝ} (hw : -Δ ≤ w) :
    gClust γ ζ w = 0 := by
  unfold gClust
  have h0 : (fun w' : ℝ => ζ (w - w') * (Set.Iio (-γ / 2)).indicator (fun _ => (1 : ℝ)) w') = fun _ => 0 := by
    funext w'
    by_cases hw' : w' < -γ / 2
    · have hout : ζ (w - w') = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h := hζ.tsupport_subset hmem
        have := hζ.δ_lt
        rw [Set.mem_Ioo] at h
        linarith [h.2]
      rw [hout, zero_mul]
    · rw [Set.indicator_of_notMem (by simpa using hw'), mul_zero]
  rw [h0, integral_zero]

/-- "`and $g(\omega)=1$ for $\omega\le-\gamma+\Delta$, in particular for $\omega\le-\gamma$.`" -/
theorem gClust_eq_one {Δ γ δ : ℝ} {ζ : ℝ → ℝ} (hζ : ClusterParams Δ γ δ ζ) {w : ℝ} (hw : w ≤ -γ + Δ) :
    gClust γ ζ w = 1 := by
  unfold gClust
  have h1 : (fun w' : ℝ => ζ (w - w') * (Set.Iio (-γ / 2)).indicator (fun _ => (1 : ℝ)) w') = fun w' => ζ (w - w') := by
    funext w'
    by_cases hw' : w' < -γ / 2
    · rw [Set.indicator_of_mem (by simpa using hw'), mul_one]
    · have hout : ζ (w - w') = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h := hζ.tsupport_subset hmem
        have := hζ.δ_lt
        rw [Set.mem_Ioo] at h
        push Not at hw'
        linarith [h.1]
      rw [hout, zero_mul]
  rw [h1, integral_sub_left_eq_self (fun v => ζ v) volume w, hζ.integral_eq_one]

/-- "`By Lemma~\ref{lem:embedding}(ii), $\Qf(\iota(A))=\iota(\Qf(A))$.`" (for self-adjoint `H`). -/
theorem clusterFilter_iota {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {T : Torus}
    (hT : T.Admissible δ₀) {H : FockOp T} (hH : IsSelfAdjoint H) (g : ℝ → ℝ) (A : FockOp T) :
    clusterFilter g (iota η δ₀ T H) (iota η δ₀ T A) = iota η δ₀ T (clusterFilter g H A) := by
  have hH' : IsSelfAdjoint (iota η δ₀ T H) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ← iota_conjTranspose hη hδ₀ hT, ← Matrix.star_eq_conjTranspose,
      hH.star_eq]
  have hspec : specFinset (iota η δ₀ T H) = specFinset H := by
    ext E
    simp only [specFinset, Set.Finite.mem_toFinset]
    rw [← spectrum.preimage_algebraMap ℂ, ← spectrum.preimage_algebraMap ℂ (a := H), spectrum_iota hη hδ₀ hT]
  have hproj : ∀ E, specProj (iota η δ₀ T H) E = iota η δ₀ T (specProj H E) := fun E => cfc_iota hη hδ₀ hT hH _
  have key : ∀ X : FockOp T, iota η δ₀ T X = iotaHom hη hδ₀ hT X := fun X => (iotaHom_apply hη hδ₀ hT X).symm
  simp only [clusterFilter, hspec, hproj]
  simp only [key, map_sum, map_smul, map_mul]

/-! ## Lemma 5.9 (the generator filter) -/

section GeneratorFilter

variable {ϑ : ℝ → ℝ} {γ : ℝ}

/-! ### Proof devices for Lemma 5.9 (phase (b); not statements of the paper)

The Dirichlet integral `∫_0^A sin x/x dx → π/2` (by Fubini with `1/x = ∫_0^∞ e^{−sx} ds` and dominated convergence);
the truncated integral `∫_{−Ω}^{Ω} Ŵ_γ(ω)e^{iωt} dω = −2∫_0^Ω (1 − ϑ(ω/γ)) sin(ωt)/ω dω` (`Ŵ_γ` odd); for `Ω ≥ γ` it is
`−2(∫_0^Ω sin(ωt)/ω dω − K(t))` with `K(t) := ∫_0^∞ ϑ(ω/γ) sin(ωt)/ω dω`, whose limit is `−π sign t + 2K(t)`; hence
`W_γ(t) = −½ sign t + K(t)/π`, the paper's formula, and `|K(t)| ≤ γ|t|`. -/

section W59Devices

open Real Set

theorem integral_Ioi_inv_one_add_sq' : ∫ s in Ioi (0 : ℝ), (1 + s ^ 2)⁻¹ = π / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (f := arctan) (f' := fun s => (1 + s ^ 2)⁻¹) (a := 0)
    (fun x _ => by simpa [one_div] using hasDerivAt_arctan x) integrable_inv_one_add_sq.integrableOn
    (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds)
  rw [h, arctan_zero, sub_zero]

theorem hasDerivAt_sin_exp_prim (s x : ℝ) :
    HasDerivAt (fun x => -(exp (-(s * x)) * (s * sin x + cos x)) / (1 + s ^ 2)) (sin x * exp (-(s * x))) x := by
  have h1 : HasDerivAt (fun x => exp (-(s * x))) (exp (-(s * x)) * (-s)) x := by
    have := ((hasDerivAt_id x).const_mul s).neg.exp
    simpa [mul_comm] using this
  have h2 : HasDerivAt (fun x => s * sin x + cos x) (s * cos x + -sin x) x :=
    ((hasDerivAt_sin x).const_mul s).add (hasDerivAt_cos x)
  have h3 := ((h1.mul h2).neg).div_const (1 + s ^ 2)
  refine h3.congr_deriv ?_
  have hpos : (0 : ℝ) < 1 + s ^ 2 := by positivity
  field_simp
  ring

theorem integral_sin_mul_exp (A s : ℝ) :
    ∫ x in (0 : ℝ)..A, sin x * exp (-(s * x)) = (1 - exp (-(s * A)) * (s * sin A + cos A)) / (1 + s ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_sin_exp_prim s x)
    ((continuous_sin.mul (continuous_exp.comp (continuous_const.mul continuous_id).neg)).intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, exp_zero, sin_zero, cos_zero, one_mul, zero_add]
  have hpos : (0 : ℝ) < 1 + s ^ 2 := by positivity
  field_simp
  ring

theorem integral_exp_neg_mul_Ioi {x : ℝ} (hx : 0 < x) : ∫ s in Ioi (0 : ℝ), exp (-(s * x)) = x⁻¹ := by
  have h := integral_exp_mul_Ioi (a := -x) (by linarith) 0
  have e : (fun s : ℝ => exp (-(s * x))) = fun s => exp (-x * s) := funext fun s => by ring_nf
  rw [e, h]
  simp [neg_div, div_neg]

theorem integral_sin_div_eq {A : ℝ} (hA : 0 ≤ A) :
    ∫ x in (0 : ℝ)..A, sin x / x =
      ∫ s in Ioi (0 : ℝ), (1 - exp (-(s * A)) * (s * sin A + cos A)) / (1 + s ^ 2) := by
  -- `sin x / x = ∫_0^∞ sin x e^{−sx} ds` for `x > 0`
  have h1 : ∫ x in (0 : ℝ)..A, sin x / x = ∫ x in Ioc (0 : ℝ) A, ∫ s in Ioi (0 : ℝ), sin x * exp (-(s * x)) := by
    rw [intervalIntegral.integral_of_le hA]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [integral_const_mul, integral_exp_neg_mul_Ioi hx.1, div_eq_mul_inv]
  -- Fubini
  have hint : Integrable (Function.uncurry fun (x s : ℝ) => sin x * exp (-(s * x)))
      ((volume.restrict (Ioc (0 : ℝ) A)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry fun (x s : ℝ) => sin x * exp (-(s * x)))
        ((volume.restrict (Ioc (0 : ℝ) A)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
      refine Continuous.aestronglyMeasurable ?_
      exact (continuous_sin.comp continuous_fst).mul
        (continuous_exp.comp ((continuous_snd.mul continuous_fst).neg))
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
      have hi : IntegrableOn (fun s : ℝ => exp (-(s * x))) (Ioi 0) := by
        have := (exp_neg_integrableOn_Ioi 0 hx.1)
        refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
        ring_nf
      exact hi.const_mul (sin x)
    · have hb : ∀ x ∈ Ioc (0 : ℝ) A, ∫ s in Ioi (0 : ℝ), ‖sin x * exp (-(s * x))‖ ≤ 1 := by
        intro x hx
        have e : (fun s : ℝ => ‖sin x * exp (-(s * x))‖) = fun s => |sin x| * exp (-(s * x)) := by
          funext s; rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        rw [e, integral_const_mul, integral_exp_neg_mul_Ioi hx.1]
        rw [← div_eq_mul_inv, div_le_one hx.1]
        exact (abs_sin_le_abs).trans (le_of_eq (abs_of_pos hx.1))
      refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.norm.integral_prod_right' ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun s => norm_nonneg _)]
      exact hb x hx
  rw [h1, integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [← intervalIntegral.integral_of_le hA, integral_sin_mul_exp]

theorem tendsto_integral_sin_div : Tendsto (fun A => ∫ x in (0 : ℝ)..A, sin x / x) atTop (𝓝 (π / 2)) := by
  have h1 : (fun A => ∫ s in Ioi (0 : ℝ), (1 - exp (-(s * A)) * (s * sin A + cos A)) / (1 + s ^ 2)) =ᶠ[atTop]
      fun A => ∫ x in (0 : ℝ)..A, sin x / x :=
    (eventually_ge_atTop 0).mono fun A hA => (integral_sin_div_eq hA).symm
  refine Tendsto.congr' h1 ?_
  rw [← integral_Ioi_inv_one_add_sq']
  refine tendsto_integral_filter_of_dominated_convergence (fun s => (1 + s ^ 2)⁻¹ + 2 * exp (-s)) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun A => Continuous.aestronglyMeasurable ?_
    refine Continuous.div ?_ (by fun_prop) fun s => by positivity
    fun_prop
  · refine (eventually_ge_atTop 1).mono fun A hA => ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs
    have hpos : (0 : ℝ) < 1 + s ^ 2 := by positivity
    have he : exp (-(s * A)) ≤ exp (-s) := exp_le_exp.mpr (by nlinarith)
    have hsc : |s * sin A + cos A| ≤ s + 1 := by
      calc |s * sin A + cos A| ≤ |s * sin A| + |cos A| := abs_add_le _ _
        _ ≤ s * 1 + 1 := by
            rw [abs_mul, abs_of_pos hs0]
            exact add_le_add (mul_le_mul_of_nonneg_left (abs_sin_le_one A) hs0.le) (abs_cos_le_one A)
        _ = s + 1 := by ring
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have h2 : |1 - exp (-(s * A)) * (s * sin A + cos A)| ≤ 1 + exp (-s) * (s + 1) := by
      calc |1 - exp (-(s * A)) * (s * sin A + cos A)| ≤ |1| + |exp (-(s * A)) * (s * sin A + cos A)| :=
            abs_sub _ _
        _ ≤ 1 + exp (-s) * (s + 1) := by
            rw [abs_one, abs_mul, abs_of_pos (exp_pos _)]
            exact add_le_add le_rfl (mul_le_mul he hsc (abs_nonneg _) (exp_pos _).le)
    have h3 : exp (-s) * (s + 1) ≤ 2 * exp (-s) * (1 + s ^ 2) := by
      have := exp_pos (-s)
      nlinarith [sq_nonneg (s - 1)]
    calc |1 - exp (-(s * A)) * (s * sin A + cos A)| ≤ 1 + exp (-s) * (s + 1) := h2
      _ ≤ 1 + 2 * exp (-s) * (1 + s ^ 2) := by linarith
      _ = ((1 + s ^ 2)⁻¹ + 2 * exp (-s)) * (1 + s ^ 2) := by field_simp
  · exact integrable_inv_one_add_sq.integrableOn.add ((exp_neg_integrableOn_Ioi 0 one_pos).congr_fun
      (fun s _ => by ring_nf) measurableSet_Ioi |>.const_mul 2)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs
    have hexp : Tendsto (fun A => exp (-(s * A))) atTop (𝓝 0) := by
      have := tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hs0))
      exact this
    have hbdd : IsBoundedUnder (· ≤ ·) atTop fun A => ‖s * sin A + cos A‖ :=
      Filter.isBoundedUnder_of ⟨s + 1, fun A => by
        rw [Real.norm_eq_abs]
        calc |s * sin A + cos A| ≤ |s * sin A| + |cos A| := abs_add_le _ _
          _ ≤ s * 1 + 1 := by
              rw [abs_mul, abs_of_pos hs0]
              exact add_le_add (mul_le_mul_of_nonneg_left (abs_sin_le_one A) hs0.le) (abs_cos_le_one A)
          _ = s + 1 := by ring⟩
    have h0 := hexp.zero_mul_isBoundedUnder_le hbdd
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    rw [sub_zero] at h2
    have h3 := h2.div_const (1 + s ^ 2)
    simpa [one_div] using h3

theorem cutoff_eq_zero_of_le (hϑ : IsCutoff ϑ) {x : ℝ} (hx : 1 ≤ |x|) : ϑ x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have := hϑ.tsupport_subset h
  rw [Set.mem_Ioo] at this
  have := abs_lt.mpr this
  linarith

theorem What_neg (hϑ : IsCutoff ϑ) (w : ℝ) : What ϑ γ (-w) = -What ϑ γ w := by
  simp only [What]
  rw [neg_div, hϑ.even, Complex.ofReal_neg, div_neg]

theorem continuous_What (hϑ : IsCutoff ϑ) : Continuous (What ϑ γ) := by
  have hc : Continuous ϑ := hϑ.contDiff.continuous
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    have hev : ∀ᶠ v in 𝓝 (0 : ℝ), What ϑ γ v = 0 := by
      have h1 : ∀ᶠ v in 𝓝 (0 : ℝ), ϑ (v / γ) = 1 := by
        have hcont : Tendsto (fun v : ℝ => v / γ) (𝓝 0) (𝓝 0) := by
          have := (continuous_id.div_const γ).tendsto (0 : ℝ)
          simpa using this
        exact hcont.eventually hϑ.eventually_eq_one
      exact h1.mono fun v hv => by simp [What, hv]
    have h0 : What ϑ γ 0 = 0 := by simp [What]
    exact (continuousAt_const.congr (hev.mono fun v hv => (hv.trans h0.symm).symm))
  · refine ContinuousAt.div ?_ (Complex.continuous_ofReal.continuousAt) (by exact_mod_cast hw)
    exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_const.sub ((hc.comp (continuous_id.div_const γ)).continuousAt)))

theorem cexp_I_mul (y : ℝ) : Complex.exp (I * (y : ℂ)) = (Real.cos y : ℂ) + (Real.sin y : ℂ) * I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem What_mul_exp_add_neg (hϑ : IsCutoff ϑ) (w t : ℝ) :
    What ϑ γ (-w) * Complex.exp (I * ((-w : ℝ) : ℂ) * (t : ℂ)) + What ϑ γ w * Complex.exp (I * (w : ℂ) * (t : ℂ)) =
      ((-2 * ((1 - ϑ (w / γ)) / w * Real.sin (w * t)) : ℝ) : ℂ) := by
  rw [What_neg hϑ, mul_assoc I, mul_assoc I, ← Complex.ofReal_mul, ← Complex.ofReal_mul, cexp_I_mul, cexp_I_mul]
  simp only [What, neg_mul, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  by_cases hw : w = 0
  · subst hw; simp
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem trunc_eq (hϑ : IsCutoff ϑ) {Ω : ℝ} (t : ℝ) :
    ∫ w in (-Ω)..Ω, What ϑ γ w * Complex.exp (I * (w : ℂ) * (t : ℂ)) =
      ((-2 * ∫ w in (0 : ℝ)..Ω, (1 - ϑ (w / γ)) / w * Real.sin (w * t) : ℝ) : ℂ) := by
  have hg : Continuous fun w : ℝ => What ϑ γ w * Complex.exp (I * (w : ℂ) * (t : ℂ)) :=
    (continuous_What hϑ).mul (Complex.continuous_exp.comp (by fun_prop))
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)]
  have h1 : ∫ w in (-Ω)..0, What ϑ γ w * Complex.exp (I * (w : ℂ) * (t : ℂ)) =
      ∫ w in (0 : ℝ)..Ω, What ϑ γ (-w) * Complex.exp (I * ((-w : ℝ) : ℂ) * (t : ℂ)) := by
    rw [intervalIntegral.integral_comp_neg (fun w : ℝ => What ϑ γ w * Complex.exp (I * (w : ℂ) * (t : ℂ))),
      neg_zero]
  have hA : IntervalIntegrable (fun w : ℝ => What ϑ γ (-w) * Complex.exp (I * ((-w : ℝ) : ℂ) * (t : ℂ))) volume 0 Ω :=
    (hg.comp continuous_neg).intervalIntegrable _ _
  rw [h1, ← intervalIntegral.integral_add hA (hg.intervalIntegrable _ _)]
  simp only [What_mul_exp_add_neg hϑ]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]

theorem abs_sin_mul_div_le (w t : ℝ) : |Real.sin (w * t) / w| ≤ |t| := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hw)]
  calc |Real.sin (w * t)| ≤ |w * t| := Real.abs_sin_le_abs
    _ = |t| * |w| := by rw [abs_mul, mul_comm]

theorem abs_cut_sin_div_le (hϑ : IsCutoff ϑ) (w t : ℝ) : |ϑ (w / γ) * Real.sin (w * t) / w| ≤ |t| := by
  rw [mul_div_assoc, abs_mul]
  calc |ϑ (w / γ)| * |Real.sin (w * t) / w| ≤ 1 * |t| :=
        mul_le_mul (by rw [abs_of_nonneg (hϑ.nonneg _)]; exact hϑ.le_one _) (abs_sin_mul_div_le w t)
          (abs_nonneg _) zero_le_one
    _ = |t| := one_mul _

theorem intervalIntegrable_of_abs_le {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  refine intervalIntegrable_iff.mpr ?_
  refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne hf.aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x

theorem measurable_sin_mul_div (t : ℝ) : Measurable fun w : ℝ => Real.sin (w * t) / w := by
  fun_prop

theorem measurable_cut_sin_div (hϑ : IsCutoff ϑ) (t : ℝ) :
    Measurable fun w : ℝ => ϑ (w / γ) * Real.sin (w * t) / w := by
  have hm : Measurable ϑ := hϑ.contDiff.continuous.measurable
  fun_prop

theorem integral_sin_mul_div_eq {t : ℝ} (ht : 0 < t) (Ω : ℝ) :
    ∫ w in (0 : ℝ)..Ω, Real.sin (w * t) / w = ∫ u in (0 : ℝ)..Ω * t, Real.sin u / u := by
  have ht0 : t ≠ 0 := ht.ne'
  have e : ∀ w : ℝ, Real.sin (w * t) / w = t * (Real.sin (w * t) / (w * t)) := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · rw [mul_div_assoc', mul_comm t, mul_div_mul_right _ _ ht0]
  have h := intervalIntegral.integral_comp_mul_right (a := 0) (b := Ω) (fun u : ℝ => Real.sin u / u) ht0
  beta_reduce at h
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, h, zero_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht0, one_mul]

theorem tendsto_integral_sin_mul_div (t : ℝ) :
    Tendsto (fun Ω => ∫ w in (0 : ℝ)..Ω, Real.sin (w * t) / w) atTop (𝓝 (π / 2 * Real.sign t)) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h1 : ∀ Ω, ∫ w in (0 : ℝ)..Ω, Real.sin (w * t) / w = -∫ u in (0 : ℝ)..Ω * (-t), Real.sin u / u := by
      intro Ω
      rw [← integral_sin_mul_div_eq (neg_pos.mpr ht), ← intervalIntegral.integral_neg]
      congr 1
      funext w
      rw [mul_neg, Real.sin_neg, neg_div, neg_neg]
    simp_rw [h1]
    rw [Real.sign_of_neg ht, show π / 2 * -1 = -(π / 2) by ring]
    exact (tendsto_integral_sin_div.comp (Tendsto.atTop_mul_const (neg_pos.mpr ht) tendsto_id)).neg
  · simp only [mul_zero, Real.sin_zero, zero_div, intervalIntegral.integral_zero, Real.sign_zero]
    exact tendsto_const_nhds
  · simp_rw [integral_sin_mul_div_eq ht]
    rw [Real.sign_of_pos ht, mul_one]
    exact tendsto_integral_sin_div.comp (Tendsto.atTop_mul_const ht tendsto_id)

theorem integral_cut_eq (hϑ : IsCutoff ϑ) (hγ : 0 < γ) {Ω : ℝ} (hΩ : γ ≤ Ω) (t : ℝ) :
    ∫ w in (0 : ℝ)..Ω, ϑ (w / γ) * Real.sin (w * t) / w =
      ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w := by
  rw [intervalIntegral.integral_of_le (hγ.le.trans hΩ)]
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self ?_
  intro w hw
  obtain ⟨h1, h2⟩ := hw
  have h1' : 0 < w := h1
  have hw' : Ω < w := by
    simp only [Set.mem_Ioc, not_and, not_le] at h2
    exact h2 h1
  rw [cutoff_eq_zero_of_le hϑ, zero_mul, zero_div]
  rw [abs_of_pos (div_pos h1' hγ), le_div_iff₀ hγ, one_mul]
  linarith

theorem tendsto_trunc (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (t : ℝ) :
    Tendsto (fun Ω : ℝ => ∫ w in (-Ω)..Ω, What ϑ γ w * Complex.exp (I * (w : ℂ) * (t : ℂ))) atTop
      (𝓝 (((-π * Real.sign t + 2 * ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w : ℝ) : ℂ))) := by
  set K := ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w with hK
  have hev : ∀ᶠ Ω in atTop, ∫ w in (-Ω)..Ω, What ϑ γ w * Complex.exp (I * (w : ℂ) * (t : ℂ)) =
      ((-2 * ((∫ w in (0 : ℝ)..Ω, Real.sin (w * t) / w) - K) : ℝ) : ℂ) := by
    filter_upwards [eventually_ge_atTop γ] with Ω hΩ
    have hint : ∫ w in (0 : ℝ)..Ω, (1 - ϑ (w / γ)) / w * Real.sin (w * t) =
        (∫ w in (0 : ℝ)..Ω, Real.sin (w * t) / w) - ∫ w in (0 : ℝ)..Ω, ϑ (w / γ) * Real.sin (w * t) / w := by
      rw [← intervalIntegral.integral_sub
        (intervalIntegrable_of_abs_le (measurable_sin_mul_div t) (fun w => abs_sin_mul_div_le w t) _ _)
        (intervalIntegrable_of_abs_le (measurable_cut_sin_div hϑ t) (fun w => abs_cut_sin_div_le hϑ w t) _ _)]
      congr 1
      funext w
      ring
    rw [trunc_eq hϑ t, hint, integral_cut_eq hϑ hγ hΩ t]
  refine (tendsto_congr' hev).mpr ?_
  have hlim : Tendsto (fun Ω => -2 * ((∫ w in (0 : ℝ)..Ω, Real.sin (w * t) / w) - K)) atTop
      (𝓝 (-2 * (π / 2 * Real.sign t - K))) :=
    ((tendsto_integral_sin_mul_div t).sub_const K).const_mul (-2)
  have h2 := (Complex.continuous_ofReal.tendsto _).comp hlim
  have e : -2 * (π / 2 * Real.sign t - K) = -π * Real.sign t + 2 * K := by ring
  rw [e] at h2
  exact h2

theorem Wfilt_eq' (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (t : ℝ) :
    Wfilt ϑ γ t = (((2 * π)⁻¹ : ℝ) : ℂ) *
      ((-π * Real.sign t + 2 * ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w : ℝ) : ℂ) := by
  rw [Wfilt, (tendsto_trunc hϑ hγ t).limUnder_eq]

theorem Wfilt_eq_real (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (t : ℝ) :
    Wfilt ϑ γ t = ((-(1 / 2) * Real.sign t +
      π⁻¹ * ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w : ℝ) : ℂ) := by
  rw [Wfilt_eq' hϑ hγ t, ← Complex.ofReal_mul]
  congr 1
  generalize (∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w) = K
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp

theorem abs_K_le (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (t : ℝ) :
    |∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w| ≤ γ * |t| := by
  rw [← integral_cut_eq hϑ hγ le_rfl t, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := γ) (C := |t|)
    (f := fun w => ϑ (w / γ) * Real.sin (w * t) / w)
    (fun w _ => by rw [Real.norm_eq_abs]; exact abs_cut_sin_div_le hϑ w t)
  rw [sub_zero, abs_of_pos hγ] at this
  linarith

theorem tendsto_K_zero (hϑ : IsCutoff ϑ) (hγ : 0 < γ) :
    Tendsto (fun t => ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w) (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => γ * |t|) (𝓝 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => γ * |t|) (𝓝 0) (𝓝 (γ * |(0 : ℝ)|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    rwa [abs_zero, mul_zero] at h0
  exact squeeze_zero_norm (fun t => by rw [Real.norm_eq_abs]; exact abs_K_le hϑ hγ t) h

end W59Devices

/-- **Definition 5.8**/**Lemma 5.9**: "`the limit exists for every $t$`" — the truncated integrals converge to `W_γ(t)`. -/
theorem tendsto_Wfilt (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (t : ℝ) :
    Tendsto (fun Ω : ℝ => (((2 * π)⁻¹ : ℝ) : ℂ) *
        ∫ w in (-Ω)..Ω, What ϑ γ w * Complex.exp (I * (w : ℂ) * (t : ℂ))) atTop (𝓝 (Wfilt ϑ γ t)) := by
  rw [Wfilt_eq' hϑ hγ t]
  exact (tendsto_trunc hϑ hγ t).const_mul _

/-- **Lemma 5.9**: "`$\Wg$ is real`". -/
theorem Wfilt_im (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (t : ℝ) : (Wfilt ϑ γ t).im = 0 := by
  rw [Wfilt_eq_real hϑ hγ t, Complex.ofReal_im]

/-! ### Proof devices for Lemma 5.9, continued (phase (b); not statements of the paper)

Cosine transforms `cosInt g a b α s := ∫_a^b g(w) cos(ws + α) dw` (a device definition): smooth in `s` for continuous
`g` (each derivative is again one: `∂_s` multiplies by `w` and shifts `α` by `π/2`), and for smooth `φ` supported in
`(−R, R)` integration by parts gives `|s|^k |∫_{−R}^{R} φ(w) cos(ws + α) dw| ≤ ∫_{−R}^{R} |φ^{(k)}|`. With
`K(t) = ∫_0^γ ϑ(ω/γ) sin(ωt)/ω dω` (the paper's integral, its integrand zero beyond `γ`): `K' = c` with
`c(s) := ∫_0^γ ϑ(ω/γ) cos(ωs) dω = ½ ∫_{−γ}^{γ} ϑ(ω/γ) cos(ωs) dω`, so `K` is smooth and `|K(t)| ≤ γ + B₂`
(`|K| ≤ γ|t|` near `0`, `|c(s)| ≤ B₂ s^{−2}` beyond `1`, `K` odd). -/

section W59Devices2

open Real Set

/-- (device) the cosine transform `s ↦ ∫_a^b g(w) cos(ws + α) dw`. -/
noncomputable def cosInt (g : ℝ → ℝ) (a b α s : ℝ) : ℝ := ∫ w in a..b, g w * Real.cos (w * s + α)

theorem hasDerivAt_cosInt {g : ℝ → ℝ} (hg : Continuous g) (a b α s : ℝ) :
    HasDerivAt (cosInt g a b α) (cosInt (fun w => w * g w) a b (α + π / 2) s) s := by
  have hcos : ∀ s' : ℝ, Continuous fun w : ℝ => Real.cos (w * s' + α) := fun s' => by fun_prop
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := a) (b := b)
    (F := fun s w => g w * Real.cos (w * s + α))
    (F' := fun s w => w * g w * Real.cos (w * s + (α + π / 2)))
    (x₀ := s) (s := Set.univ) (bound := fun w => |w * g w|) Filter.univ_mem
    (Eventually.of_forall fun s' => (hg.mul (hcos s')).aestronglyMeasurable)
    ((hg.mul (hcos s)).intervalIntegrable _ _)
    (((continuous_id.mul hg).mul
      (by fun_prop : Continuous fun w : ℝ => Real.cos (w * s + (α + π / 2)))).aestronglyMeasurable)
    (Eventually.of_forall fun w _ x _ => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |w * g w| * |Real.cos (w * x + (α + π / 2))| ≤ |w * g w| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |w * g w| := mul_one _)
    ((continuous_id.mul hg).abs.intervalIntegrable _ _)
    (Eventually.of_forall fun w _ x _ => by
      have h1 : HasDerivAt (fun x => w * x + α) w x := by
        simpa using ((hasDerivAt_id x).const_mul w).add_const α
      have h3 := (Real.hasDerivAt_cos (w * x + α)).comp x h1
      have h2 : HasDerivAt (fun x => g w * Real.cos (w * x + α)) (g w * (-Real.sin (w * x + α) * w)) x :=
        h3.const_mul (g w)
      refine h2.congr_deriv ?_
      rw [← add_assoc, Real.cos_add_pi_div_two]
      ring)
  exact h.2

theorem iteratedDeriv_cosInt {g : ℝ → ℝ} (hg : Continuous g) (a b α : ℝ) (n : ℕ) :
    iteratedDeriv n (cosInt g a b α) = cosInt (fun w => w ^ n * g w) a b (α + n * (π / 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [(hasDerivAt_cosInt (g := fun w => w ^ n * g w) ((continuous_pow n).mul hg) a b _ s).deriv]
    simp only [cosInt]
    congr 1
    funext w
    rw [show α + (n : ℝ) * (π / 2) + π / 2 = α + ((n + 1 : ℕ) : ℝ) * (π / 2) by push_cast; ring, pow_succ]
    ring

theorem contDiff_cosInt {g : ℝ → ℝ} (hg : Continuous g) (a b α : ℝ) : ContDiff ℝ ∞ (cosInt g a b α) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [iteratedDeriv_cosInt hg]
  exact fun s => (hasDerivAt_cosInt (g := fun w => w ^ m * g w) ((continuous_pow m).mul hg) a b _ s).differentiableAt

theorem cosInt_decay {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {R : ℝ} (hR0 : 0 ≤ R) (hR : tsupport φ ⊆ Set.Ioo (-R) R)
    (k : ℕ) (α s : ℝ) : |s| ^ k * |cosInt φ (-R) R α s| ≤ ∫ w in (-R)..R, |iteratedDeriv k φ w| := by
  have hle : -R ≤ R := by linarith
  induction k generalizing φ α with
  | zero =>
    simp only [pow_zero, one_mul, iteratedDeriv_zero, cosInt]
    refine (intervalIntegral.abs_integral_le_integral_abs hle).trans ?_
    refine intervalIntegral.integral_mono_on hle ?_ ?_ fun w _ => ?_
    · exact (hφ.continuous.mul (by fun_prop : Continuous fun w : ℝ => Real.cos (w * s + α))).abs.intervalIntegrable _ _
    · exact hφ.continuous.abs.intervalIntegrable _ _
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  | succ k ih =>
    have hd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    have hdR : tsupport (deriv φ) ⊆ Set.Ioo (-R) R := tsupport_deriv_subset.trans hR
    rcases eq_or_ne s 0 with rfl | hs
    · rw [abs_zero, zero_pow (Nat.succ_ne_zero k), zero_mul]
      exact intervalIntegral.integral_nonneg hle fun w _ => abs_nonneg _
    have h0 : ∀ x, x ∉ Set.Ioo (-R) R → φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hR h)
    have hφR : φ R = 0 := h0 R fun h => lt_irrefl _ h.2
    have hφR' : φ (-R) = 0 := h0 (-R) fun h => lt_irrefl _ h.1
    have hdiff : Differentiable ℝ φ := (contDiff_infty_iff_deriv.mp hφ).1
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -R) (b := R) (u := φ) (u' := deriv φ)
      (v := fun w => Real.sin (w * s + α) / s) (v' := fun w => Real.cos (w * s + α))
      (fun x _ => (hdiff x).hasDerivAt)
      (fun x _ => by
        have h1 : HasDerivAt (fun x => x * s + α) s x := by
          simpa using ((hasDerivAt_id x).mul_const s).add_const α
        have h3 := (Real.hasDerivAt_sin (x * s + α)).comp x h1
        have h2 : HasDerivAt (fun x => Real.sin (x * s + α) / s) (Real.cos (x * s + α) * s / s) x :=
          h3.div_const s
        refine h2.congr_deriv ?_
        field_simp)
      (hd.continuous.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun w : ℝ => Real.cos (w * s + α)).intervalIntegrable _ _)
    beta_reduce at hibp
    have heq : cosInt φ (-R) R α s = -s⁻¹ * cosInt (deriv φ) (-R) R (α - π / 2) s := by
      simp only [cosInt]
      rw [hibp, hφR, hφR', zero_mul, zero_mul, sub_zero, zero_sub, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_neg]
      congr 1
      funext w
      rw [show w * s + (α - π / 2) = (w * s + α) - π / 2 by ring, Real.cos_sub_pi_div_two]
      ring
    have hs'' : |s| ≠ 0 := (abs_pos.mpr hs).ne'
    rw [heq, abs_mul, abs_neg, abs_inv, pow_succ, iteratedDeriv_succ']
    calc |s| ^ k * |s| * (|s|⁻¹ * |cosInt (deriv φ) (-R) R (α - π / 2) s|) =
          |s| ^ k * |cosInt (deriv φ) (-R) R (α - π / 2) s| := by
          rw [mul_assoc, mul_inv_cancel_left₀ hs'']
      _ ≤ _ := ih hd hdR (α - π / 2)

theorem contDiff_cut (hϑ : IsCutoff ϑ) : ContDiff ℝ ∞ fun w : ℝ => ϑ (w / γ) :=
  hϑ.contDiff.comp (contDiff_id.div_const γ)

theorem tsupport_cut (hϑ : IsCutoff ϑ) (hγ : 0 < γ) : tsupport (fun w : ℝ => ϑ (w / γ)) ⊆ Set.Ioo (-γ) γ := by
  intro w hw
  have h := tsupport_comp_subset_preimage ϑ (continuous_id.div_const γ) hw
  have h2 := hϑ.tsupport_subset h
  simp only [Set.mem_Ioo, id] at h2
  constructor
  · have := h2.1
    rw [lt_div_iff₀ hγ] at this
    linarith
  · have := h2.2
    rw [div_lt_iff₀ hγ] at this
    linarith

theorem cosInt_cut_eq (hϑ : IsCutoff ϑ) (s : ℝ) :
    cosInt (fun w => ϑ (w / γ)) (-γ) γ 0 s = 2 * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s) := by
  have hc0 : Continuous ϑ := hϑ.contDiff.continuous
  have hc : Continuous fun w : ℝ => ϑ (w / γ) * Real.cos (w * s) := by fun_prop
  simp only [cosInt, add_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h1 : ∫ w in (-γ)..0, ϑ (w / γ) * Real.cos (w * s) = ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := γ) (fun w => ϑ (w / γ) * Real.cos (w * s))
    rw [neg_zero] at h
    rw [← h]
    congr 1
    funext w
    simp only [neg_div, hϑ.even, neg_mul, Real.cos_neg]
  rw [h1, two_mul]

theorem hasDerivAt_Kint (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (t : ℝ) :
    HasDerivAt (fun t => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w)
      (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * t)) t := by
  have hc : Continuous ϑ := hϑ.contDiff.continuous
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0) (b := γ)
    (F := fun t w => ϑ (w / γ) * Real.sin (w * t) / w) (F' := fun t w => ϑ (w / γ) * Real.cos (w * t))
    (x₀ := t) (s := Set.univ) (bound := fun _ => 1) Filter.univ_mem
    (Eventually.of_forall fun t' => (measurable_cut_sin_div hϑ t').aestronglyMeasurable)
    (intervalIntegrable_of_abs_le (measurable_cut_sin_div hϑ t) (fun w => abs_cut_sin_div_le hϑ w t) _ _)
    ((by fun_prop : Continuous fun w : ℝ => ϑ (w / γ) * Real.cos (w * t)).aestronglyMeasurable)
    (Eventually.of_forall fun w _ x _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hϑ.nonneg _)]
      calc ϑ (w / γ) * |Real.cos (w * x)| ≤ 1 * 1 :=
            mul_le_mul (hϑ.le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1)
    intervalIntegrable_const
    (Eventually.of_forall fun w hw x _ => by
      rw [Set.uIoc_of_le hγ.le] at hw
      have hw0 : w ≠ 0 := hw.1.ne'
      have h1 : HasDerivAt (fun x => w * x) w x := by simpa using (hasDerivAt_id x).const_mul w
      have h2 : HasDerivAt (fun x => ϑ (w / γ) * Real.sin (w * x) / w) (ϑ (w / γ) * (Real.cos (w * x) * w) / w) x :=
        (((Real.hasDerivAt_sin (w * x)).comp x h1).const_mul (ϑ (w / γ))).div_const w
      refine h2.congr_deriv ?_
      field_simp)
  exact h.2

theorem contDiff_Kint (hϑ : IsCutoff ϑ) (hγ : 0 < γ) :
    ContDiff ℝ ∞ (fun t => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w) := by
  have hc : Continuous ϑ := hϑ.contDiff.continuous
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (hasDerivAt_Kint hϑ hγ t).differentiableAt, ?_⟩
  have e : deriv (fun t => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w) =
      cosInt (fun w => ϑ (w / γ)) 0 γ 0 := by
    funext t
    rw [(hasDerivAt_Kint hϑ hγ t).deriv]
    simp only [cosInt, add_zero]
  rw [e]
  exact contDiff_cosInt (by fun_prop) 0 γ 0

theorem Kderiv_decay (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (k : ℕ) (s : ℝ) :
    |s| ^ k * |∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)| ≤
      (1 / 2) * ∫ w in (-γ)..γ, |iteratedDeriv k (fun w => ϑ (w / γ)) w| := by
  have h := cosInt_decay (contDiff_cut hϑ) hγ.le (tsupport_cut hϑ hγ) k 0 s
  rw [cosInt_cut_eq hϑ s, abs_mul, abs_two] at h
  linarith

theorem Kint_eq (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (t : ℝ) :
    ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w = ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w :=
  (integral_cut_eq hϑ hγ le_rfl t).symm

theorem Kint_neg (t : ℝ) :
    ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * -t) / w = -∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w := by
  rw [← intervalIntegral.integral_neg]
  congr 1
  funext w
  rw [mul_neg, Real.sin_neg]
  ring

theorem integral_inv_sq_le {T : ℝ} (hT : 1 ≤ T) : ∫ s in (1 : ℝ)..T, (s ^ 2)⁻¹ ≤ 1 := by
  have hd : ∀ x ∈ Set.uIcc (1 : ℝ) T, HasDerivAt (fun s : ℝ => -s⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h : HasDerivAt (fun s : ℝ => -s⁻¹) (-(-(x ^ 2)⁻¹)) x := (hasDerivAt_inv hx0).neg
    rwa [neg_neg] at h
  have hc : ContinuousOn (fun s : ℝ => (s ^ 2)⁻¹) (Set.uIcc 1 T) := by
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    have hx0 : x ^ 2 ≠ 0 := by have : x ≠ 0 := by linarith [hx.1]
                               positivity
    exact ((continuous_pow 2).continuousAt.inv₀ hx0).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  have : 0 < T⁻¹ := inv_pos.mpr (by linarith)
  simp only [inv_one]
  linarith

theorem abs_Kint_le (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (t : ℝ) :
    |∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w| ≤
      γ + (1 / 2) * ∫ w in (-γ)..γ, |iteratedDeriv 2 (fun w => ϑ (w / γ)) w| := by
  set B := (1 / 2) * ∫ w in (-γ)..γ, |iteratedDeriv 2 (fun w => ϑ (w / γ)) w| with hB
  have hB0 : 0 ≤ B := by
    have := Kderiv_decay hϑ hγ 2 0
    have h2 : 0 ≤ |(0 : ℝ)| ^ 2 * |∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * 0)| := by positivity
    linarith
  -- the case `0 ≤ t`
  have hpos : ∀ t : ℝ, 0 ≤ t → |∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w| ≤ γ + B := by
    intro t ht
    rcases le_or_gt t 1 with ht1 | ht1
    · have h := abs_K_le hϑ hγ t
      rw [Kint_eq hϑ hγ t, abs_of_nonneg ht] at h
      have : γ * t ≤ γ * 1 := mul_le_mul_of_nonneg_left ht1 hγ.le
      linarith
    · have hc : Continuous fun s : ℝ => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s) := by
        have e : (fun s : ℝ => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)) =
            cosInt (fun w => ϑ (w / γ)) 0 γ 0 := by
          funext s; simp only [cosInt, add_zero]
        rw [e]
        exact (contDiff_cosInt (hϑ.contDiff.continuous.comp (continuous_id.div_const γ)) 0 γ 0).continuous
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 1) (b := t)
        (fun x _ => hasDerivAt_Kint hϑ hγ x) (hc.intervalIntegrable _ _)
      have h1 : |∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * 1) / w| ≤ γ := by
        have h := abs_K_le hϑ hγ 1
        rw [Kint_eq hϑ hγ 1, abs_one, mul_one] at h
        exact h
      have h2 : |∫ s in (1 : ℝ)..t, ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)| ≤ B := by
        rw [← Real.norm_eq_abs]
        refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun s => B * (s ^ 2)⁻¹) ht1.le ?_ ?_).trans ?_
        · refine Eventually.of_forall fun s hs => ?_
          have hs0 : 0 < s := by linarith [hs.1]
          have h := Kderiv_decay hϑ hγ 2 s
          rw [← hB, abs_of_pos hs0] at h
          rw [Real.norm_eq_abs, le_mul_inv_iff₀ (by positivity), mul_comm]
          exact h
        · refine ContinuousOn.intervalIntegrable ?_
          intro x hx
          rw [Set.uIcc_of_le ht1.le] at hx
          have hx0 : x ^ 2 ≠ 0 := by have : x ≠ 0 := by linarith [hx.1]
                                     positivity
          exact (continuousAt_const.mul ((continuous_pow 2).continuousAt.inv₀ hx0)).continuousWithinAt
        · rw [intervalIntegral.integral_const_mul]
          calc B * ∫ s in (1 : ℝ)..t, (s ^ 2)⁻¹ ≤ B * 1 :=
                mul_le_mul_of_nonneg_left (integral_inv_sq_le ht1.le) hB0
            _ = B := mul_one B
      rw [hftc] at h2
      have := abs_sub_abs_le_abs_sub (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w)
        (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * 1) / w)
      linarith
  rcases le_or_gt 0 t with ht | ht
  · exact hpos t ht
  · have h := hpos (-t) (by linarith)
    rw [Kint_neg, abs_neg] at h
    exact h

end W59Devices2

/-- **Lemma 5.9**: "`and bounded`". -/
theorem Wfilt_bounded (hϑ : IsCutoff ϑ) (hγ : 0 < γ) : ∃ C : ℝ, ∀ t : ℝ, ‖Wfilt ϑ γ t‖ ≤ C := by
  refine ⟨1 / 2 + π⁻¹ * (γ + (1 / 2) * ∫ w in (-γ)..γ, |iteratedDeriv 2 (fun w => ϑ (w / γ)) w|), fun t => ?_⟩
  rw [Wfilt_eq_real hϑ hγ t, Complex.norm_real, Real.norm_eq_abs, Kint_eq hϑ hγ t]
  have hK := abs_Kint_le hϑ hγ t
  have hs : |Real.sign t| ≤ 1 := by
    rcases lt_trichotomy t 0 with h | rfl | h
    · rw [Real.sign_of_neg h]; norm_num
    · rw [Real.sign_zero]; norm_num
    · rw [Real.sign_of_pos h]; norm_num
  have hpi : 0 < π⁻¹ := inv_pos.mpr Real.pi_pos
  calc |-(1 / 2) * Real.sign t + π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w|
      ≤ |-(1 / 2) * Real.sign t| + |π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w| := abs_add_le _ _
    _ = 1 / 2 * |Real.sign t| + π⁻¹ * |∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos hpi]
    _ ≤ 1 / 2 * 1 + π⁻¹ * (γ + (1 / 2) * ∫ w in (-γ)..γ, |iteratedDeriv 2 (fun w => ϑ (w / γ)) w|) := by
        gcongr
    _ = _ := by ring

/-- **Lemma 5.9**: "`smooth on $\R\setminus\{0\}$`". -/
theorem contDiffOn_Wfilt (hϑ : IsCutoff ϑ) (hγ : 0 < γ) : ContDiffOn ℝ ∞ (Wfilt ϑ γ) {0}ᶜ := by
  have hK : ContDiff ℝ ∞ (fun t => ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w) := by
    have e : (fun t => ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w) =
        fun t => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w := funext fun t => Kint_eq hϑ hγ t
    rw [e]
    exact contDiff_Kint hϑ hγ
  refine (isOpen_compl_singleton).contDiffOn_iff.mpr fun t ht => ?_
  have hev : Wfilt ϑ γ =ᶠ[𝓝 t] fun s => (((-(1 / 2) * Real.sign t +
      π⁻¹ * ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * s) / w) : ℝ) : ℂ) := by
    rcases lt_or_gt_of_ne (show t ≠ 0 from ht) with h | h
    · filter_upwards [Iio_mem_nhds h] with s hs
      rw [Wfilt_eq_real hϑ hγ s, Real.sign_of_neg (show s < 0 from hs), Real.sign_of_neg h]
    · filter_upwards [Ioi_mem_nhds h] with s hs
      rw [Wfilt_eq_real hϑ hγ s, Real.sign_of_pos (show 0 < s from hs), Real.sign_of_pos h]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hF : ContDiff ℝ ∞ (fun s => -(1 / 2) * Real.sign t +
      π⁻¹ * ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * s) / w) :=
    contDiff_const.add (contDiff_const.mul hK)
  have h3 : ContDiff ℝ ∞ (fun s => (((-(1 / 2) * Real.sign t +
      π⁻¹ * ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * s) / w) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hF
  exact h3.contDiffAt

/-- **Lemma 5.9**: "`with a jump of $-1$ at $t=0$`" — the proof's "`$\Wg(0\pm)=\mp\frac12$, a jump of $-1$`". -/
theorem tendsto_Wfilt_zero (hϑ : IsCutoff ϑ) (hγ : 0 < γ) :
    Tendsto (Wfilt ϑ γ) (𝓝[>] 0) (𝓝 (-(1 / 2 : ℂ))) ∧ Tendsto (Wfilt ϑ γ) (𝓝[<] 0) (𝓝 (1 / 2 : ℂ)) := by
  have hK := tendsto_K_zero hϑ hγ
  have hc : Continuous fun x : ℝ => (x : ℂ) := Complex.continuous_ofReal
  constructor
  · have h1 : Tendsto (fun t => ((-(1 / 2) * 1 + π⁻¹ * ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 (((-(1 / 2) * 1 + π⁻¹ * 0 : ℝ) : ℂ))) :=
      (hc.tendsto _).comp ((tendsto_const_nhds.add (hK.const_mul π⁻¹)).mono_left nhdsWithin_le_nhds)
    have h2 : (((-(1 / 2) * 1 + π⁻¹ * 0 : ℝ) : ℂ)) = -(1 / 2 : ℂ) := by push_cast; ring
    rw [h2] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Wfilt_eq_real hϑ hγ t, Real.sign_of_pos ht]
  · have h1 : Tendsto (fun t => ((-(1 / 2) * (-1) + π⁻¹ * ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w : ℝ) : ℂ))
        (𝓝[<] 0) (𝓝 (((-(1 / 2) * (-1) + π⁻¹ * 0 : ℝ) : ℂ))) :=
      (hc.tendsto _).comp ((tendsto_const_nhds.add (hK.const_mul π⁻¹)).mono_left nhdsWithin_le_nhds)
    have h2 : (((-(1 / 2) * (-1) + π⁻¹ * 0 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by push_cast; ring
    rw [h2] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < 0)
    rw [Wfilt_eq_real hϑ hγ t, Real.sign_of_neg ht]

/-- **Lemma 5.9**: "`\Wg(t)=-\tfrac12\operatorname{sign}(t)+\frac1\pi\int_0^\infty\vartheta(\omega/\gamma)\frac{\sin(\omega t)}{\omega}\,\dd\omega,`"
(`sign 0 = 0`; the integrand vanishes for `ω ≥ γ`). -/
theorem Wfilt_eq (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (t : ℝ) :
    Wfilt ϑ γ t = ((-(1 / 2) * Real.sign t +
      π⁻¹ * ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w : ℝ) : ℂ) := by
  exact Wfilt_eq_real hϑ hγ t

/-- **Lemma 5.9**: "`\qquad\Wg(t)=W_1(\gamma t).`" -/
theorem Wfilt_eq_Wfilt_one (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (t : ℝ) : Wfilt ϑ γ t = Wfilt ϑ 1 (γ * t) := by
  rw [Wfilt_eq_real hϑ hγ t, Wfilt_eq_real hϑ one_pos (γ * t)]
  have hs : Real.sign (γ * t) = Real.sign t := by
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · rw [Real.sign_of_neg ht, Real.sign_of_neg (mul_neg_of_pos_of_neg hγ ht)]
    · rw [mul_zero]
    · rw [Real.sign_of_pos ht, Real.sign_of_pos (mul_pos hγ ht)]
  have hK : ∫ w in Set.Ioi (0 : ℝ), ϑ (w / 1) * Real.sin (w * (γ * t)) / w =
      ∫ w in Set.Ioi (0 : ℝ), ϑ (w / γ) * Real.sin (w * t) / w := by
    have h := integral_comp_mul_left_Ioi (fun u : ℝ => ϑ (u / γ) * Real.sin (u * t) / u) 0 hγ
    simp only [mul_zero, smul_eq_mul] at h
    have e : ∀ x : ℝ, ϑ (x / 1) * Real.sin (x * (γ * t)) / x =
        γ * (ϑ (γ * x / γ) * Real.sin (γ * x * t) / (γ * x)) := by
      intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · rw [div_one, mul_div_cancel_left₀ _ hγ.ne', show γ * x * t = x * (γ * t) by ring, mul_div_assoc' γ,
          mul_div_mul_left _ _ hγ.ne']
    simp_rw [e]
    rw [integral_const_mul, h, ← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul]
  rw [hs, hK]

/-! ### Proof devices for Lemma 5.9, continued: decay (phase (b); not statements of the paper)

`K(T) → π/2` as `T → ∞`: `K(T) = ∫_0^γ sin(ωT)/ω dω − ∫_0^γ f(ω) sin(ωT) dω` with `f(ω) := (1 − ϑ(ω/γ))/ω`, smooth
(zero near `0`); the first is the Dirichlet integral at `γT`, the second is `O(1/T)` by one integration by parts. Then
`K(t) − π/2 = −∫_t^∞ c` and `|c(s)| ≤ B_{n+2} s^{−n−2}` give `|W_γ(t)| ≤ π^{−1} B_{n+2} |t|^{−n}` for `|t| ≥ 1` (the
paper integrates by parts in `W_1(t) = −(πt)^{−1} ∫_0^∞ f'(ω) cos(ωt) dω` instead; this route uses the tail of the cosine
transform `c`); with `|W_γ| ≤ C` this gives `(1 + |t|)^j |W_γ(t)| ≤ C_j (1 + t²)^{−1}`, hence the moments and the tails. -/

section W59Devices3

open Real Set

theorem contDiff_chiDiv (hϑ : IsCutoff ϑ) : ContDiff ℝ ∞ (fun w : ℝ => (1 - ϑ (w / γ)) / w) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  rcases eq_or_ne w 0 with rfl | hw
  · have h1 : ∀ᶠ v in 𝓝 (0 : ℝ), ϑ (v / γ) = 1 := by
      have hcont : Tendsto (fun v : ℝ => v / γ) (𝓝 0) (𝓝 0) := by
        have := (continuous_id.div_const γ).tendsto (0 : ℝ)
        simpa using this
      exact hcont.eventually hϑ.eventually_eq_one
    have hev : (fun w : ℝ => (1 - ϑ (w / γ)) / w) =ᶠ[𝓝 0] fun _ => (0 : ℝ) :=
      h1.mono fun v hv => by simp [hv]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact ((contDiff_const.sub (hϑ.contDiff.comp (contDiff_id.div_const γ))).contDiffAt).div contDiffAt_id hw

theorem abs_integral_mul_sin_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {a b : ℝ} (hab : a ≤ b) {T : ℝ} (hT : T ≠ 0) :
    |∫ w in a..b, f w * Real.sin (w * T)| ≤ (|f a| + |f b| + ∫ w in a..b, |deriv f w|) / |T| := by
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hcd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b) (u := f) (u' := deriv f)
    (v := fun w => -Real.cos (w * T) / T) (v' := fun w => Real.sin (w * T))
    (fun x _ => (hdiff x).hasDerivAt)
    (fun x _ => by
      have h1 : HasDerivAt (fun x => x * T) T x := by simpa using (hasDerivAt_id x).mul_const T
      have h3 := (Real.hasDerivAt_cos (x * T)).comp x h1
      have h2 : HasDerivAt (fun x => -Real.cos (x * T) / T) (-(-Real.sin (x * T) * T) / T) x :=
        h3.neg.div_const T
      refine h2.congr_deriv ?_
      field_simp)
    (hcd.intervalIntegrable _ _) ((by fun_prop : Continuous fun w : ℝ => Real.sin (w * T)).intervalIntegrable _ _)
  beta_reduce at hibp
  rw [hibp]
  have hT' : 0 < |T| := abs_pos.mpr hT
  have e1 : |f b * (-Real.cos (b * T) / T)| ≤ |f b| / |T| := by
    rw [abs_mul, abs_div, abs_neg]
    calc |f b| * (|Real.cos (b * T)| / |T|) ≤ |f b| * (1 / |T|) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hT'.le) (abs_nonneg _)
      _ = |f b| / |T| := by ring
  have e2 : |f a * (-Real.cos (a * T) / T)| ≤ |f a| / |T| := by
    rw [abs_mul, abs_div, abs_neg]
    calc |f a| * (|Real.cos (a * T)| / |T|) ≤ |f a| * (1 / |T|) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hT'.le) (abs_nonneg _)
      _ = |f a| / |T| := by ring
  have e3 : |∫ x in a..b, deriv f x * (-Real.cos (x * T) / T)| ≤ (∫ w in a..b, |deriv f w|) / |T| := by
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun w => |deriv f w| / |T|) hab
      (Eventually.of_forall fun w _ => ?_) ((hcd.abs.div_const _).intervalIntegrable _ _)).trans ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg]
      calc |deriv f w| * (|Real.cos (w * T)| / |T|) ≤ |deriv f w| * (1 / |T|) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hT'.le) (abs_nonneg _)
        _ = |deriv f w| / |T| := by ring
    · rw [intervalIntegral.integral_div]
  calc |f b * (-Real.cos (b * T) / T) - f a * (-Real.cos (a * T) / T) - ∫ x in a..b, deriv f x * (-Real.cos (x * T) / T)|
      ≤ |f b * (-Real.cos (b * T) / T)| + |f a * (-Real.cos (a * T) / T)| +
          |∫ x in a..b, deriv f x * (-Real.cos (x * T) / T)| := by
        have := abs_sub (f b * (-Real.cos (b * T) / T) - f a * (-Real.cos (a * T) / T))
          (∫ x in a..b, deriv f x * (-Real.cos (x * T) / T))
        have := abs_sub (f b * (-Real.cos (b * T) / T)) (f a * (-Real.cos (a * T) / T))
        linarith
    _ ≤ |f b| / |T| + |f a| / |T| + (∫ w in a..b, |deriv f w|) / |T| := by linarith
    _ = _ := by ring

theorem tendsto_Kint_atTop (hϑ : IsCutoff ϑ) (hγ : 0 < γ) :
    Tendsto (fun T => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * T) / w) atTop (𝓝 (π / 2)) := by
  set f : ℝ → ℝ := fun w => (1 - ϑ (w / γ)) / w with hf
  have hfc : ContDiff ℝ ∞ f := contDiff_chiDiv hϑ
  set A := |f 0| + |f γ| + ∫ w in (0 : ℝ)..γ, |deriv f w| with hA
  -- the difference tends to `0`
  have hD : Tendsto (fun T => ∫ w in (0 : ℝ)..γ, f w * Real.sin (w * T)) atTop (𝓝 0) := by
    have hb : Tendsto (fun T : ℝ => A / |T|) atTop (𝓝 0) := by
      have := (tendsto_abs_atTop_atTop.comp tendsto_id).inv_tendsto_atTop.const_mul A
      simpa [div_eq_mul_inv] using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [Real.norm_eq_abs]
    exact abs_integral_mul_sin_le (hfc.of_le (by simp)) hγ.le hT.ne'
  -- the Dirichlet part
  have hS : Tendsto (fun T => ∫ w in (0 : ℝ)..γ, Real.sin (w * T) / w) atTop (𝓝 (π / 2)) := by
    have h1 : (fun T => ∫ u in (0 : ℝ)..γ * T, Real.sin u / u) =ᶠ[atTop]
        fun T => ∫ w in (0 : ℝ)..γ, Real.sin (w * T) / w :=
      (eventually_gt_atTop 0).mono fun T hT => (integral_sin_mul_div_eq hT γ).symm
    refine Tendsto.congr' h1 ?_
    exact tendsto_integral_sin_div.comp (Tendsto.const_mul_atTop hγ tendsto_id)
  have heq : ∀ T, ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * T) / w =
      (∫ w in (0 : ℝ)..γ, Real.sin (w * T) / w) - ∫ w in (0 : ℝ)..γ, f w * Real.sin (w * T) := by
    intro T
    have i1 : IntervalIntegrable (fun w : ℝ => Real.sin (w * T) / w) volume 0 γ :=
      intervalIntegrable_of_abs_le (measurable_sin_mul_div T) (fun w => abs_sin_mul_div_le w T) _ _
    have i2 : IntervalIntegrable (fun w : ℝ => f w * Real.sin (w * T)) volume 0 γ :=
      (hfc.continuous.mul (by fun_prop : Continuous fun w : ℝ => Real.sin (w * T))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub i1 i2]
    congr 1
    funext w
    simp only [hf]
    ring
  simp_rw [heq]
  simpa using hS.sub hD

theorem integral_inv_sq_le' {t T : ℝ} (ht : 1 ≤ t) (hT : t ≤ T) : ∫ s in t..T, (s ^ 2)⁻¹ ≤ 1 := by
  have hd : ∀ x ∈ Set.uIcc t T, HasDerivAt (fun s : ℝ => -s⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h : HasDerivAt (fun s : ℝ => -s⁻¹) (-(-(x ^ 2)⁻¹)) x := (hasDerivAt_inv hx0).neg
    rwa [neg_neg] at h
  have hc : ContinuousOn (fun s : ℝ => (s ^ 2)⁻¹) (Set.uIcc t T) := by
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    have hx0 : x ^ 2 ≠ 0 := by
      have : x ≠ 0 := by linarith [hx.1]
      positivity
    exact ((continuous_pow 2).continuousAt.inv₀ hx0).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  have h1 : 0 < T⁻¹ := inv_pos.mpr (by linarith)
  have h2 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  linarith

/-- `|K(t) − π/2| ≤ B_{n+2} t^{−n}` for `t ≥ 1`. -/
theorem abs_Kint_sub_le (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    |(∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w) - π / 2| ≤
      (1 / 2) * (∫ w in (-γ)..γ, |iteratedDeriv (n + 2) (fun w => ϑ (w / γ)) w|) * (t ^ n)⁻¹ := by
  set B := (1 / 2) * ∫ w in (-γ)..γ, |iteratedDeriv (n + 2) (fun w => ϑ (w / γ)) w| with hB
  have ht0 : 0 < t := by linarith
  have hB0 : 0 ≤ B := by
    have := Kderiv_decay hϑ hγ (n + 2) 0
    have h2 : 0 ≤ |(0 : ℝ)| ^ (n + 2) * |∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * 0)| := by positivity
    linarith
  have hc : Continuous fun s : ℝ => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s) := by
    have e : (fun s : ℝ => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)) = cosInt (fun w => ϑ (w / γ)) 0 γ 0 := by
      funext s; simp only [cosInt, add_zero]
    rw [e]
    exact (contDiff_cosInt (hϑ.contDiff.continuous.comp (continuous_id.div_const γ)) 0 γ 0).continuous
  have hbound : ∀ T, t ≤ T → |(∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * T) / w) -
      ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w| ≤ B * (t ^ n)⁻¹ := by
    intro T hT
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_Kint hϑ hγ x)
      (hc.intervalIntegrable _ _), ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun s => B * (t ^ n)⁻¹ * (s ^ 2)⁻¹) hT ?_ ?_).trans ?_
    · refine Eventually.of_forall fun s hs => ?_
      have hs0 : 0 < s := by linarith [hs.1]
      have hts : t ≤ s := hs.1.le
      have h := Kderiv_decay hϑ hγ (n + 2) s
      rw [← hB, abs_of_pos hs0] at h
      rw [Real.norm_eq_abs]
      have hsn : 0 < s ^ (n + 2) := by positivity
      have h1 : |∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)| ≤ B / s ^ (n + 2) := by
        rw [le_div_iff₀ hsn, mul_comm]; exact h
      have h2 : B / s ^ (n + 2) ≤ B * (t ^ n)⁻¹ * (s ^ 2)⁻¹ := by
        rw [pow_add, div_eq_mul_inv, mul_inv, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hB0) (by positivity)
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ ht0.le hts n)
      exact h1.trans h2
    · refine ContinuousOn.intervalIntegrable ?_
      intro x hx
      rw [Set.uIcc_of_le hT] at hx
      have hx0 : x ^ 2 ≠ 0 := by
        have : x ≠ 0 := by linarith [hx.1]
        positivity
      exact (continuousAt_const.mul ((continuous_pow 2).continuousAt.inv₀ hx0)).continuousWithinAt
    · rw [intervalIntegral.integral_const_mul]
      calc B * (t ^ n)⁻¹ * ∫ s in t..T, (s ^ 2)⁻¹ ≤ B * (t ^ n)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (integral_inv_sq_le' ht hT) (by positivity)
        _ = B * (t ^ n)⁻¹ := mul_one _
  have hlim := ((tendsto_Kint_atTop hϑ hγ).sub_const (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w)).abs
  have := le_of_tendsto hlim ((eventually_ge_atTop t).mono fun T hT => hbound T hT)
  rw [abs_sub_comm]
  exact this

theorem norm_Wfilt_le_of_one_le (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (n : ℕ) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖Wfilt ϑ γ t‖ ≤ π⁻¹ * ((1 / 2) * (∫ w in (-γ)..γ, |iteratedDeriv (n + 2) (fun w => ϑ (w / γ)) w|)) *
      (|t| ^ n)⁻¹ := by
  have hpi : 0 < π := Real.pi_pos
  rw [Wfilt_eq_real hϑ hγ t, Complex.norm_real, Real.norm_eq_abs, Kint_eq hϑ hγ t]
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht ⊢
    rw [Real.sign_of_pos (by linarith)]
    have h := abs_Kint_sub_le hϑ hγ n ht
    have e : -(1 / 2) * 1 + π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w =
        π⁻¹ * ((∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w) - π / 2) := by
      generalize (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w) = K
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (inv_pos.mpr hpi), mul_assoc]
    exact mul_le_mul_of_nonneg_left h (inv_pos.mpr hpi).le
  · rw [abs_of_neg h0] at ht ⊢
    rw [Real.sign_of_neg h0]
    have h := abs_Kint_sub_le hϑ hγ n ht
    have hneg := Kint_neg (ϑ := ϑ) (γ := γ) (-t)
    rw [neg_neg] at hneg
    have e : -(1 / 2) * (-1) + π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w =
        -(π⁻¹ * ((∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * -t) / w) - π / 2)) := by
      rw [hneg]
      generalize (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * -t) / w) = K
      field_simp
      ring
    rw [e, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hpi), mul_assoc]
    exact mul_le_mul_of_nonneg_left h (inv_pos.mpr hpi).le

theorem measurable_sign' : Measurable Real.sign := by
  have e : Real.sign = fun r : ℝ => if r < 0 then -1 else if 0 < r then 1 else 0 := by
    funext r; rfl
  rw [e]
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

theorem measurable_Wfilt (hϑ : IsCutoff ϑ) (hγ : 0 < γ) : Measurable (Wfilt ϑ γ) := by
  have e : Wfilt ϑ γ = fun t => (((-(1 / 2) * Real.sign t +
      π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w) : ℝ) : ℂ) := by
    funext t
    rw [Wfilt_eq_real hϑ hγ t, Kint_eq hϑ hγ t]
  rw [e]
  have hK := (contDiff_Kint hϑ hγ).continuous.measurable
  exact Complex.measurable_ofReal.comp ((measurable_const.mul measurable_sign').add (measurable_const.mul hK))

/-- The bound `(1 + |t|)^j ‖W_γ(t)‖ ≤ C_j (1 + t²)^{−1}`. -/
theorem moment_bound_Wfilt (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (j : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, (1 + |t|) ^ j * ‖Wfilt ϑ γ t‖ ≤ C * (1 + t ^ 2)⁻¹ := by
  obtain ⟨M, hM⟩ := Wfilt_bounded hϑ hγ
  set A := π⁻¹ * ((1 / 2) * (∫ w in (-γ)..γ, |iteratedDeriv (j + 2 + 2) (fun w => ϑ (w / γ)) w|)) with hA
  refine ⟨2 ^ (j + 1) * (|M| + |A|), fun t => ?_⟩
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hpos]
  rcases le_or_gt |t| 1 with ht | ht
  · have h1 : (1 + |t|) ^ j ≤ 2 ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j
    have h2 : 1 + t ^ 2 ≤ 2 := by
      have : t ^ 2 ≤ 1 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg t]
      linarith
    have h3 : ‖Wfilt ϑ γ t‖ ≤ |M| := (hM t).trans (le_abs_self M)
    calc (1 + |t|) ^ j * ‖Wfilt ϑ γ t‖ * (1 + t ^ 2) ≤ 2 ^ j * |M| * 2 := by
          gcongr
      _ = 2 ^ (j + 1) * |M| := by ring
      _ ≤ 2 ^ (j + 1) * (|M| + |A|) := by gcongr; linarith [abs_nonneg A]
  · have h1 : (1 + |t|) ^ j ≤ 2 ^ j * |t| ^ j := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) j
    have h2 : 1 + t ^ 2 ≤ 2 * |t| ^ 2 := by
      rw [sq_abs]; nlinarith [sq_abs t, abs_nonneg t]
    have h3 := norm_Wfilt_le_of_one_le hϑ hγ (j + 2) ht.le
    rw [← hA] at h3
    have htj : 0 < |t| ^ (j + 2) := by positivity
    have h4 : ‖Wfilt ϑ γ t‖ * |t| ^ (j + 2) ≤ |A| := by
      rw [← le_div_iff₀ htj, div_eq_mul_inv]
      exact h3.trans (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
    calc (1 + |t|) ^ j * ‖Wfilt ϑ γ t‖ * (1 + t ^ 2) ≤ (2 ^ j * |t| ^ j) * ‖Wfilt ϑ γ t‖ * (2 * |t| ^ 2) := by
          gcongr
      _ = 2 ^ (j + 1) * (‖Wfilt ϑ γ t‖ * |t| ^ (j + 2)) := by ring
      _ ≤ 2 ^ (j + 1) * |A| := by gcongr
      _ ≤ 2 ^ (j + 1) * (|M| + |A|) := by gcongr; linarith [abs_nonneg M]

end W59Devices3

/-- **Lemma 5.9**: "`Moreover $\Wg(t)=O(\abs t^{-\infty})$ as $\abs t\to\infty$`" — `O(|t|^{−n})` along the cocompact
filter, for every `n`. -/
theorem Wfilt_isBigO (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (n : ℕ) :
    Wfilt ϑ γ =O[cocompact ℝ] fun t => ((|t| ^ (-(n : ℝ)) : ℝ) : ℂ) := by
  refine IsBigO.of_bound (π⁻¹ * ((1 / 2) * (∫ w in (-γ)..γ, |iteratedDeriv (n + 2) (fun w => ϑ (w / γ)) w|))) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with t ht
  rw [Real.norm_eq_abs] at ht
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    Real.rpow_neg (abs_nonneg _), Real.rpow_natCast]
  exact norm_Wfilt_le_of_one_le hϑ hγ n ht

/-- **Lemma 5.9**: "`so $M_j(\Wg)<\infty$ for every $j$`". -/
theorem hasFiniteMoments_Wfilt (hϑ : IsCutoff ϑ) (hγ : 0 < γ) : HasFiniteMoments (Wfilt ϑ γ) := by
  have hm : AEStronglyMeasurable (Wfilt ϑ γ) volume := (measurable_Wfilt hϑ hγ).aestronglyMeasurable
  have hint : ∀ j : ℕ, Integrable fun t => (1 + |t|) ^ j * ‖Wfilt ϑ γ t‖ := by
    intro j
    obtain ⟨C, hC⟩ := moment_bound_Wfilt hϑ hγ j
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) ?_ (Eventually.of_forall fun t => ?_)
    · exact ((continuous_const.add continuous_abs).pow j).aestronglyMeasurable.mul hm.norm
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hC t
  refine ⟨?_, hint⟩
  obtain ⟨C, hC⟩ := moment_bound_Wfilt hϑ hγ 0
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) hm (Eventually.of_forall fun t => ?_)
  simpa using hC t

/-- **Lemma 5.9**: "`for every $n$ there is $C_n$ with $\int_{\abs t>T}\abs{\Wg(t)}\,\dd t\le C_n\gamma^{-1}(\gamma T)^{-n}$`"
(for `T > 0`; `C_n` after `γ`, as the convention on constants allows). -/
theorem tail_Wfilt_le (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (n : ℕ) :
    ∃ C : ℝ, ∀ T : ℝ, 0 < T → ∫ t in {t : ℝ | T < |t|}, ‖Wfilt ϑ γ t‖ ≤ C * γ⁻¹ * (γ * T) ^ (-(n : ℝ)) := by
  have hfm := hasFiniteMoments_Wfilt hϑ hγ
  obtain ⟨C₂, hC₂⟩ := moment_bound_Wfilt hϑ hγ n
  have hC₂0 : 0 ≤ C₂ := by
    have h := hC₂ 0
    simp only [abs_zero, add_zero, one_pow, one_mul] at h
    norm_num at h
    exact (norm_nonneg _).trans h
  set I₂ := ∫ t : ℝ, (1 + t ^ 2)⁻¹ with hI₂
  refine ⟨C₂ * I₂ * γ ^ (n + 1), fun T hT => ?_⟩
  have hγ0 : γ ≠ 0 := hγ.ne'
  have hT0 : T ≠ 0 := hT.ne'
  have hS : MeasurableSet {t : ℝ | T < |t|} := measurableSet_lt measurable_const continuous_abs.measurable
  have hTn : 0 < T ^ n := pow_pos hT n
  have hb : ∀ t ∈ {t : ℝ | T < |t|}, ‖Wfilt ϑ γ t‖ ≤ C₂ * (T ^ n)⁻¹ * (1 + t ^ 2)⁻¹ := by
    intro t ht
    have ht' : T < |t| := ht
    have h1 := hC₂ t
    have hpos : 0 < (1 + |t|) ^ n := by positivity
    have h2 : T ^ n ≤ (1 + |t|) ^ n := pow_le_pow_left₀ hT.le (by linarith [abs_nonneg t]) n
    calc ‖Wfilt ϑ γ t‖ ≤ C₂ * (1 + t ^ 2)⁻¹ / (1 + |t|) ^ n := by
          rw [le_div_iff₀ hpos, mul_comm]; exact h1
      _ ≤ C₂ * (1 + t ^ 2)⁻¹ / T ^ n :=
          div_le_div_of_nonneg_left (mul_nonneg hC₂0 (inv_nonneg.mpr (by positivity))) hTn h2
      _ = C₂ * (T ^ n)⁻¹ * (1 + t ^ 2)⁻¹ := by ring
  have hint2 : Integrable fun t : ℝ => C₂ * (T ^ n)⁻¹ * (1 + t ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul _
  calc ∫ t in {t : ℝ | T < |t|}, ‖Wfilt ϑ γ t‖ ≤ ∫ t in {t : ℝ | T < |t|}, C₂ * (T ^ n)⁻¹ * (1 + t ^ 2)⁻¹ :=
        setIntegral_mono_on hfm.1.norm.integrableOn hint2.integrableOn hS hb
    _ ≤ ∫ t, C₂ * (T ^ n)⁻¹ * (1 + t ^ 2)⁻¹ :=
        setIntegral_le_integral hint2 (Eventually.of_forall fun t =>
          mul_nonneg (mul_nonneg hC₂0 (inv_nonneg.mpr hTn.le)) (inv_nonneg.mpr (by positivity)))
    _ = C₂ * I₂ * (T ^ n)⁻¹ := by rw [integral_const_mul]; ring
    _ = C₂ * I₂ * γ ^ (n + 1) * γ⁻¹ * (γ * T) ^ (-(n : ℝ)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_natCast, mul_pow]
        field_simp
        ring

/-! ### Proof devices for Lemma 5.9, continued: the Fourier identity (phase (b); not statements of the paper)

The cosine inversion `∫_0^∞ c(s) cos(sω) ds = (π/2) ϑ(ω/γ)` from Mathlib's Fourier inversion
(`Continuous.fourierInv_fourier_eq`) for `ϑ(·/γ)`, whose Fourier transform in Mathlib's normalization is `2c(2πξ)`; then,
with the real form `W_γ = −½ sign + K/π` (`Wre`, a device definition; odd), `∫ W_γ(t) e^{−iωt} dt = −2i ∫_0^∞ W_γ(t)
sin(ωt) dt`, and one integration by parts on `(0, ∞)` (`W_γ(0+) = −½`, `W_γ' = c/π`, `W_γ(∞) = 0`) gives
`∫_0^∞ W_γ(t) sin(ωt) dt = −1/(2ω) + (πω)^{−1} ∫_0^∞ c(t) cos(tω) dt = −(1 − ϑ(ω/γ))/(2ω)`. -/

section W59Devices4

open Real Set
open scoped FourierTransform

theorem integral_interval_odd {h : ℝ → ℝ} (hodd : ∀ x, h (-x) = -h x) (a : ℝ) : ∫ x in (-a)..a, h x = 0 := by
  have h1 := intervalIntegral.integral_comp_neg (a := -a) (b := a) h
  rw [neg_neg] at h1
  simp only [hodd, intervalIntegral.integral_neg] at h1
  linarith

theorem integral_real_odd {h : ℝ → ℝ} (hodd : ∀ x, h (-x) = -h x) : ∫ x, h x = 0 := by
  have h1 : ∫ x, h (-x) = ∫ x, h x := integral_neg_eq_self h volume
  simp only [hodd, integral_neg] at h1
  linarith

theorem integral_real_even {h : ℝ → ℝ} (heven : ∀ x, h (-x) = h x) : ∫ x, h x = 2 * ∫ x in Set.Ioi (0 : ℝ), h x := by
  rw [← integral_comp_abs]
  congr 1; funext x
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, heven]

theorem cK_neg (s : ℝ) :
    ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * -s) = ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s) := by
  congr 1; funext w; rw [mul_neg, Real.cos_neg]

theorem continuous_cK (hϑ : IsCutoff ϑ) :
    Continuous fun s : ℝ => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s) := by
  have e : (fun s : ℝ => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)) = cosInt (fun w => ϑ (w / γ)) 0 γ 0 := by
    funext s; simp only [cosInt, add_zero]
  rw [e]
  exact (contDiff_cosInt (hϑ.contDiff.continuous.comp (continuous_id.div_const γ)) 0 γ 0).continuous

theorem cK_bound (hϑ : IsCutoff ϑ) (hγ : 0 < γ) :
    ∃ M : ℝ, ∀ s : ℝ, |∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)| ≤ M * (1 + s ^ 2)⁻¹ := by
  set B₀ := (1 / 2) * ∫ w in (-γ)..γ, |iteratedDeriv 0 (fun w => ϑ (w / γ)) w| with hB₀
  set B₂ := (1 / 2) * ∫ w in (-γ)..γ, |iteratedDeriv 2 (fun w => ϑ (w / γ)) w| with hB₂
  refine ⟨B₀ + B₂, fun s => ?_⟩
  have h0 := Kderiv_decay hϑ hγ 0 s
  have h2 := Kderiv_decay hϑ hγ 2 s
  rw [← hB₀] at h0
  rw [← hB₂] at h2
  simp only [pow_zero, one_mul] at h0
  rw [sq_abs] at h2
  have hpos : 0 < 1 + s ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hpos]
  nlinarith [abs_nonneg (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s))]

theorem integrable_cK (hϑ : IsCutoff ϑ) (hγ : 0 < γ) :
    Integrable fun s : ℝ => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s) := by
  obtain ⟨M, hM⟩ := cK_bound hϑ hγ
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul M) (continuous_cK hϑ).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs]; exact hM s

/-- The Fourier transform (Mathlib's normalization) of `ϑ(·/γ)`: `𝓕(ϑ(·/γ))(ξ) = 2 c(2πξ)`. -/
theorem fourier_cut_eq (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((ϑ (x / γ) : ℝ) : ℂ)) ξ =
      ((2 * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * (2 * π * ξ)) : ℝ) : ℂ) := by
  have hc : Continuous ϑ := hϑ.contDiff.continuous
  rw [fourier_real_eq_integral_exp_smul]
  have h1 : ∀ v : ℝ, Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * I) • ((ϑ (v / γ) : ℝ) : ℂ) =
      ((ϑ (v / γ) * Real.cos (v * (2 * π * ξ) + 0) : ℝ) : ℂ) -
        ((ϑ (v / γ) * Real.sin (v * (2 * π * ξ)) : ℝ) : ℂ) * I := by
    intro v
    rw [smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show -2 * π * v * ξ = -(v * (2 * π * ξ)) by ring, Real.cos_neg, Real.sin_neg, add_zero]
    push_cast
    ring
  simp_rw [h1]
  have hzero : ∀ v : ℝ, v ∉ Set.Ioc (-γ) γ → ((ϑ (v / γ) * Real.cos (v * (2 * π * ξ) + 0) : ℝ) : ℂ) -
      ((ϑ (v / γ) * Real.sin (v * (2 * π * ξ)) : ℝ) : ℂ) * I = 0 := by
    intro v hv
    have : ϑ (v / γ) = 0 := image_eq_zero_of_notMem_tsupport (f := fun w : ℝ => ϑ (w / γ))
      fun h => hv (Set.Ioo_subset_Ioc_self (tsupport_cut hϑ hγ h))
    rw [this]; simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← intervalIntegral.integral_of_le (by linarith)]
  have i1 : IntervalIntegrable (fun v : ℝ => ((ϑ (v / γ) * Real.cos (v * (2 * π * ξ) + 0) : ℝ) : ℂ)) volume (-γ) γ :=
    (by fun_prop : Continuous fun v : ℝ => ((ϑ (v / γ) * Real.cos (v * (2 * π * ξ) + 0) : ℝ) : ℂ)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun v : ℝ => ((ϑ (v / γ) * Real.sin (v * (2 * π * ξ)) : ℝ) : ℂ) * I) volume (-γ) γ :=
    (by fun_prop : Continuous fun v : ℝ => ((ϑ (v / γ) * Real.sin (v * (2 * π * ξ)) : ℝ) : ℂ) * I).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  have hodd : ∫ v in (-γ)..γ, ϑ (v / γ) * Real.sin (v * (2 * π * ξ)) = 0 := by
    refine integral_interval_odd (fun x => ?_) γ
    rw [neg_div, hϑ.even, neg_mul, Real.sin_neg, mul_neg]
  have hcos := cosInt_cut_eq (γ := γ) hϑ (2 * π * ξ)
  simp only [cosInt] at hcos
  rw [hodd, hcos]
  push_cast
  ring

theorem integral_cK_cos_aux (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (ν : ℝ) (c : ℝ → ℝ)
    (hcdef : ∀ s, c s = ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)) :
    ∫ s, c s * Real.cos (s * ν) = π * ϑ (ν / γ) := by
  set f : ℝ → ℂ := fun x => ((ϑ (x / γ) : ℝ) : ℂ) with hfdef
  have hc0 : Continuous ϑ := hϑ.contDiff.continuous
  have hfc : Continuous f := by fun_prop
  have hfi : Integrable f := by
    refine hfc.integrable_of_hasCompactSupport ?_
    have h1 : HasCompactSupport fun x : ℝ => ϑ (x / γ) :=
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
        ((tsupport_cut hϑ hγ).trans Set.Ioo_subset_Icc_self)
    exact h1.comp_left Complex.ofReal_zero
  have hce : c = fun s => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s) := funext hcdef
  have hF : ∀ ξ, 𝓕 f ξ = ((2 * c (2 * π * ξ) : ℝ) : ℂ) := fun ξ => by rw [hcdef]; exact fourier_cut_eq hϑ hγ ξ
  have hcc : Continuous c := by rw [hce]; exact continuous_cK hϑ
  have hci : Integrable c := by rw [hce]; exact integrable_cK hϑ hγ
  have h2 : Integrable fun ξ : ℝ => c (2 * π * ξ) := hci.comp_mul_left' (by positivity)
  have hFi : Integrable (𝓕 f) := by
    have : 𝓕 f = fun ξ => ((2 * c (2 * π * ξ) : ℝ) : ℂ) := funext hF
    rw [this]
    exact (h2.const_mul 2).ofReal
  have hinv := congrFun (Continuous.fourierInv_fourier_eq hfc hfi hFi) ν
  rw [fourierInv_eq_fourier_neg, fourier_real_eq_integral_exp_smul] at hinv
  simp_rw [hF] at hinv
  have h1 : ∀ ξ : ℝ, Complex.exp (((-2 * π * ξ * -ν : ℝ) : ℂ) * I) • ((2 * c (2 * π * ξ) : ℝ) : ℂ) =
      ((2 * c (2 * π * ξ) * Real.cos (2 * π * ξ * ν) : ℝ) : ℂ) +
        ((2 * c (2 * π * ξ) * Real.sin (2 * π * ξ * ν) : ℝ) : ℂ) * I := by
    intro ξ
    rw [smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show -2 * π * ξ * -ν = 2 * π * ξ * ν by ring]
    push_cast; ring
  simp_rw [h1] at hinv
  have hbd : ∀ ψ : ℝ → ℝ, Continuous ψ → (∀ x, |ψ x| ≤ 1) →
      Integrable fun ξ : ℝ => 2 * c (2 * π * ξ) * ψ ξ := by
    intro ψ hψ hψ1
    refine Integrable.mono' (h2.const_mul 2).norm ?_ (Eventually.of_forall fun ξ => ?_)
    · exact ((continuous_const.mul (hcc.comp (continuous_const.mul continuous_id))).mul hψ).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs (ψ ξ)]
      exact mul_le_of_le_one_right (norm_nonneg _) (hψ1 ξ)
  have i1 : Integrable fun ξ : ℝ => ((2 * c (2 * π * ξ) * Real.cos (2 * π * ξ * ν) : ℝ) : ℂ) :=
    (hbd (fun ξ => Real.cos (2 * π * ξ * ν)) (by fun_prop) fun x => Real.abs_cos_le_one _).ofReal
  have i2 : Integrable fun ξ : ℝ => ((2 * c (2 * π * ξ) * Real.sin (2 * π * ξ * ν) : ℝ) : ℂ) * I :=
    (hbd (fun ξ => Real.sin (2 * π * ξ * ν)) (by fun_prop) fun x => Real.abs_sin_le_one _).ofReal.mul_const I
  rw [integral_add i1 i2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal] at hinv
  have hodd : ∫ ξ, 2 * c (2 * π * ξ) * Real.sin (2 * π * ξ * ν) = 0 := by
    refine integral_real_odd (fun x => ?_)
    have e : c (2 * π * -x) = c (2 * π * x) := by
      rw [hcdef, hcdef, mul_neg]; exact cK_neg _
    rw [e, show 2 * π * -x * ν = -(2 * π * x * ν) by ring, Real.sin_neg]; ring
  rw [hodd, Complex.ofReal_zero, zero_mul, add_zero] at hinv
  have hinv' : ((∫ ξ, 2 * c (2 * π * ξ) * Real.cos (2 * π * ξ * ν) : ℝ) : ℂ) = ((ϑ (ν / γ) : ℝ) : ℂ) := hinv
  have hreal : ∫ ξ, 2 * c (2 * π * ξ) * Real.cos (2 * π * ξ * ν) = ϑ (ν / γ) := by exact_mod_cast hinv'
  have hsub : ∫ ξ, 2 * c (2 * π * ξ) * Real.cos (2 * π * ξ * ν) = (2 * π)⁻¹ * ∫ s, 2 * c s * Real.cos (s * ν) := by
    have := Measure.integral_comp_mul_left (fun s => 2 * c s * Real.cos (s * ν)) (2 * π)
    rw [this, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), smul_eq_mul]
  rw [hsub] at hreal
  have e2 : ∫ s, 2 * c s * Real.cos (s * ν) = 2 * ∫ s, c s * Real.cos (s * ν) := by
    rw [← integral_const_mul]; congr 1; funext s; ring
  rw [e2] at hreal
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp at hreal
  linarith

theorem integral_cK_cos_Ioi (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (ν : ℝ) :
    ∫ s in Set.Ioi (0 : ℝ), (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)) * Real.cos (s * ν) =
      π / 2 * ϑ (ν / γ) := by
  have h := integral_cK_cos_aux hϑ hγ ν (fun s => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)) fun s => rfl
  rw [integral_real_even (fun x => by rw [cK_neg, neg_mul, Real.cos_neg])] at h
  linarith

/-- (device) the real form of `W_γ`: `−½ sign t + K(t)/π`. -/
noncomputable def Wre (ϑ : ℝ → ℝ) (γ t : ℝ) : ℝ :=
  -(1 / 2) * Real.sign t + π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w

theorem Wfilt_eq_Wre (hϑ : IsCutoff ϑ) (hγ : 0 < γ) : Wfilt ϑ γ = fun t => ((Wre ϑ γ t : ℝ) : ℂ) := by
  funext t; rw [Wfilt_eq_real hϑ hγ t, Kint_eq hϑ hγ t]; rfl

theorem Wre_neg (t : ℝ) : Wre ϑ γ (-t) = -Wre ϑ γ t := by
  simp only [Wre, Real.sign_neg, Kint_neg]; ring

theorem measurable_Wre (hϑ : IsCutoff ϑ) (hγ : 0 < γ) : Measurable (Wre ϑ γ) :=
  (measurable_const.mul measurable_sign').add (measurable_const.mul (contDiff_Kint hϑ hγ).continuous.measurable)

theorem integrable_Wre (hϑ : IsCutoff ϑ) (hγ : 0 < γ) : Integrable (Wre ϑ γ) := by
  have h := (hasFiniteMoments_Wfilt hϑ hγ).1
  rw [Wfilt_eq_Wre hϑ hγ] at h
  refine Integrable.mono' h.norm (measurable_Wre hϑ hγ).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  exact (Complex.norm_real _).symm.le

theorem integral_Wre_sin (hϑ : IsCutoff ϑ) (hγ : 0 < γ) {ν : ℝ} (hν : ν ≠ 0) :
    ∫ t in Set.Ioi (0 : ℝ), Wre ϑ γ t * Real.sin (ν * t) =
      -(1 / (2 * ν)) + (π * ν)⁻¹ *
        ∫ s in Set.Ioi (0 : ℝ), (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)) * Real.cos (s * ν) := by
  have hc0 : Continuous ϑ := hϑ.contDiff.continuous
  have hcc := continuous_cK (γ := γ) hϑ
  have hci := integrable_cK hϑ hγ
  have hWi := integrable_Wre hϑ hγ
  have hWm := measurable_Wre hϑ hγ
  have hu : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (Wre ϑ γ)
      (π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun t => -(1 / 2) * 1 + π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w)
        (π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * x)) x :=
      ((hasDerivAt_Kint hϑ hγ x).const_mul π⁻¹).const_add _
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < x from hx)] with t ht
    simp only [Wre, Real.sign_of_pos (show (0 : ℝ) < t from ht)]
  have hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun t => -Real.cos (ν * t) / ν) (Real.sin (ν * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => ν * t) ν x := by simpa using (hasDerivAt_id x).const_mul ν
    have h3 := (Real.hasDerivAt_cos (ν * x)).comp x h1
    have h2 : HasDerivAt (fun t => -Real.cos (ν * t) / ν) (-(-Real.sin (ν * x) * ν) / ν) x := h3.neg.div_const ν
    refine h2.congr_deriv ?_
    field_simp
  have huv' : IntegrableOn (fun t => Wre ϑ γ t * Real.sin (ν * t)) (Set.Ioi 0) := by
    refine (Integrable.mono' hWi.norm (hWm.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun t : ℝ => Real.sin (ν * t)).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)).integrableOn
    show ‖Wre ϑ γ t * Real.sin (ν * t)‖ ≤ ‖Wre ϑ γ t‖
    rw [norm_mul, Real.norm_eq_abs (Real.sin _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sin_le_one _)
  have hu'v : IntegrableOn (fun t => (π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * t)) *
      (-Real.cos (ν * t) / ν)) (Set.Ioi 0) := by
    refine (Integrable.mono' ((hci.const_mul π⁻¹).norm.div_const |ν|) ?_ (Eventually.of_forall fun t => ?_)).integrableOn
    · exact ((continuous_const.mul hcc).mul
        (by fun_prop : Continuous fun t : ℝ => -Real.cos (ν * t) / ν)).aestronglyMeasurable
    · rw [norm_mul, norm_div, norm_neg, Real.norm_eq_abs (Real.cos _), Real.norm_eq_abs ν]
      calc ‖π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * t)‖ * (|Real.cos (ν * t)| / |ν|) ≤
            ‖π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * t)‖ * (1 / |ν|) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _))
              (norm_nonneg _)
        _ = ‖π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * t)‖ / |ν| := by ring
  have hK0 : Tendsto (fun t => ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w) (𝓝 0) (𝓝 0) :=
    (tendsto_K_zero hϑ hγ).congr fun t => Kint_eq hϑ hγ t
  have hW0 : Tendsto (Wre ϑ γ) (𝓝[>] 0) (𝓝 (-(1 / 2))) := by
    have h1 : Tendsto (fun t => -(1 / 2) * 1 + π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.sin (w * t) / w)
        (𝓝[>] 0) (𝓝 (-(1 / 2) * 1 + π⁻¹ * 0)) :=
      (tendsto_const_nhds.add (hK0.const_mul _)).mono_left nhdsWithin_le_nhds
    rw [mul_zero, add_zero, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [Wre, Real.sign_of_pos ht, mul_one]
  have hv0 : Tendsto (fun t => -Real.cos (ν * t) / ν) (𝓝[>] 0) (𝓝 (-1 / ν)) := by
    have h1 : Tendsto (fun t => -Real.cos (ν * t) / ν) (𝓝 0) (𝓝 (-Real.cos (ν * 0) / ν)) :=
      (by fun_prop : Continuous fun t : ℝ => -Real.cos (ν * t) / ν).tendsto 0
    rw [mul_zero, Real.cos_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have h_zero := hW0.mul hv0
  have hWinf : Tendsto (Wre ϑ γ) atTop (𝓝 0) := by
    set A := π⁻¹ * ((1 / 2) * ∫ w in (-γ)..γ, |iteratedDeriv (1 + 2) (fun w => ϑ (w / γ)) w|) with hA
    have hb : ∀ t : ℝ, 1 ≤ t → |Wre ϑ γ t| ≤ A * t⁻¹ := by
      intro t ht
      have h := norm_Wfilt_le_of_one_le hϑ hγ 1 (show 1 ≤ |t| by rw [abs_of_pos (by linarith)]; exact ht)
      simp only [Wfilt_eq_Wre hϑ hγ, Complex.norm_real, Real.norm_eq_abs, pow_one] at h
      rw [abs_of_pos (show (0 : ℝ) < t by linarith)] at h
      exact h
    have h2 : Tendsto (fun t : ℝ => A * t⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul A
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Real.norm_eq_abs]; exact hb t ht
  have hvb : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun t => -Real.cos (ν * t) / ν) :=
    Filter.isBoundedUnder_of ⟨1 / |ν|, fun t => by
      simp only [Function.comp_apply, norm_div, norm_neg, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)⟩
  have h_infty := hWinf.zero_mul_isBoundedUnder_le hvb
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  rw [hibp]
  have e : ∫ t in Set.Ioi (0 : ℝ), (π⁻¹ * ∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * t)) * (-Real.cos (ν * t) / ν) =
      -((π * ν)⁻¹ * ∫ s in Set.Ioi (0 : ℝ), (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)) * Real.cos (s * ν)) := by
    rw [← integral_const_mul, ← integral_neg]
    congr 1; funext t
    rw [mul_comm ν t]
    generalize (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * t)) = C
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [e]
  generalize (∫ s in Set.Ioi (0 : ℝ), (∫ w in (0 : ℝ)..γ, ϑ (w / γ) * Real.cos (w * s)) * Real.cos (s * ν)) = X
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end W59Devices4

/-- The proof of Lemma 5.9: "`Hence $\int\Wg(t)e^{-\iu\omega t}\,\dd t=\widehat W_\gamma(\omega)$ for every $\omega$`". -/
theorem integral_Wfilt_mul_exp (hϑ : IsCutoff ϑ) (hγ : 0 < γ) (w : ℝ) :
    ∫ t, Wfilt ϑ γ t * Complex.exp (-(I * (w : ℂ) * (t : ℂ))) = What ϑ γ w := by
  rw [Wfilt_eq_Wre hϑ hγ]
  have hWi := integrable_Wre hϑ hγ
  have hWm := measurable_Wre hϑ hγ
  have h1 : ∀ t : ℝ, ((Wre ϑ γ t : ℝ) : ℂ) * Complex.exp (-(I * (w : ℂ) * (t : ℂ))) =
      ((Wre ϑ γ t * Real.cos (w * t) : ℝ) : ℂ) - ((Wre ϑ γ t * Real.sin (w * t) : ℝ) : ℂ) * I := by
    intro t
    rw [show -(I * (w : ℂ) * (t : ℂ)) = ((-(w * t) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  simp_rw [h1]
  have hb : ∀ ψ : ℝ → ℝ, Continuous ψ → (∀ x, |ψ x| ≤ 1) → Integrable fun t => Wre ϑ γ t * ψ t := by
    intro ψ hψ hψ1
    refine Integrable.mono' hWi.norm (hWm.aestronglyMeasurable.mul hψ.aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Real.norm_eq_abs (ψ t)]
    exact mul_le_of_le_one_right (norm_nonneg _) (hψ1 t)
  have i1 : Integrable fun t : ℝ => ((Wre ϑ γ t * Real.cos (w * t) : ℝ) : ℂ) :=
    (hb (fun t => Real.cos (w * t)) (by fun_prop) fun x => Real.abs_cos_le_one _).ofReal
  have i2 : Integrable fun t : ℝ => ((Wre ϑ γ t * Real.sin (w * t) : ℝ) : ℂ) * I :=
    ((hb (fun t => Real.sin (w * t)) (by fun_prop) fun x => Real.abs_sin_le_one _).ofReal).mul_const I
  rw [integral_sub i1 i2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]
  have hodd : ∫ t, Wre ϑ γ t * Real.cos (w * t) = 0 :=
    integral_real_odd fun x => by rw [Wre_neg, mul_neg, Real.cos_neg]; ring
  have heven : ∫ t, Wre ϑ γ t * Real.sin (w * t) = 2 * ∫ t in Set.Ioi (0 : ℝ), Wre ϑ γ t * Real.sin (w * t) :=
    integral_real_even fun x => by rw [Wre_neg, mul_neg, Real.sin_neg]; ring
  rw [hodd, heven]
  rcases eq_or_ne w 0 with rfl | hw
  · simp [What]
  · rw [integral_Wre_sin hϑ hγ hw, integral_cK_cos_Ioi hϑ hγ w]
    simp only [What]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw
    push_cast
    field_simp
    ring

/-- **Lemma 5.9**: "`$\int\Wg(t)e^{-\iu\omega t}\,\dd t =\widehat W_\gamma(\omega)=\iu/\omega$ for $\abs\omega\ge\gamma$`". -/
theorem integral_Wfilt_mul_exp_of_le (hϑ : IsCutoff ϑ) (hγ : 0 < γ) {w : ℝ} (hw : γ ≤ |w|) :
    ∫ t, Wfilt ϑ γ t * Complex.exp (-(I * (w : ℂ) * (t : ℂ))) = What ϑ γ w ∧ What ϑ γ w = I / (w : ℂ) := by
  refine ⟨integral_Wfilt_mul_exp hϑ hγ w, ?_⟩
  have h : ϑ (w / γ) = 0 := cutoff_eq_zero_of_le hϑ (by
    rw [abs_div, abs_of_pos hγ, le_div_iff₀ hγ, one_mul]; exact hw)
  simp [What, h]

/-! ### Proof devices for the spectral formula of Lemma 5.9 (phase (b); not statements of the paper)

For self-adjoint `H`: `Σ_{E∈σ(H)} 1_E(H) = 1`, `H 1_E(H) = 1_E(H) H = E 1_E(H)` (the `cfc` calculus), hence
`e^{cH} 1_E(H) = 1_E(H) e^{cH} = e^{cE} 1_E(H)` (the exponential series) and
`τ_t(A) = Σ_{E,E'} e^{it(E−E')} 1_E(H) A 1_{E'}(H)`. -/

section SpecDevices

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem mem_specFinset {H : Op S} {E : ℝ} : E ∈ specFinset H ↔ E ∈ spectrum ℝ H := by
  simp [specFinset]

theorem sum_specProj {H : Op S} (hH : IsSelfAdjoint H) : ∑ E ∈ specFinset H, specProj H E = 1 := by
  simp only [specProj]
  rw [← cfc_sum (fun E => ({E} : Set ℝ).indicator (1 : ℝ → ℝ)) H (specFinset H)
    (fun E _ => (Matrix.finite_real_spectrum (A := H)).continuousOn _), ← cfc_one ℝ H]
  apply cfc_congr
  intro x hx
  rw [Finset.sum_apply, Pi.one_apply, Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    rw [Set.indicator_of_notMem]
    simpa [eq_comm] using hb
  · intro hx'; exact absurd (mem_specFinset.mpr hx) hx'

theorem mul_specProj {H : Op S} (hH : IsSelfAdjoint H) (E : ℝ) :
    H * specProj H E = (E : ℂ) • specProj H E := by
  have hc := Matrix.finite_real_spectrum (A := H)
  simp only [specProj]
  nth_rewrite 1 [← cfc_id ℝ H]
  rw [← cfc_mul (id : ℝ → ℝ) _ H (hc.continuousOn _) (hc.continuousOn _)]
  have e : (fun x => id x * ({E} : Set ℝ).indicator (1 : ℝ → ℝ) x) =
      fun x => E * ({E} : Set ℝ).indicator (1 : ℝ → ℝ) x := by
    funext x
    by_cases hx : x = E
    · subst hx; rfl
    · simp [Set.indicator_of_notMem (show x ∉ ({E} : Set ℝ) from hx)]
  rw [e, cfc_const_mul E _ H (hc.continuousOn _), Complex.coe_smul]

theorem specProj_mul {H : Op S} (hH : IsSelfAdjoint H) (E : ℝ) :
    specProj H E * H = (E : ℂ) • specProj H E := by
  have hc := Matrix.finite_real_spectrum (A := H)
  simp only [specProj]
  nth_rewrite 2 [← cfc_id ℝ H]
  rw [← cfc_mul _ (id : ℝ → ℝ) H (hc.continuousOn _) (hc.continuousOn _)]
  have e : (fun x => ({E} : Set ℝ).indicator (1 : ℝ → ℝ) x * id x) =
      fun x => E * ({E} : Set ℝ).indicator (1 : ℝ → ℝ) x := by
    funext x
    by_cases hx : x = E
    · subst hx; simp
    · simp [Set.indicator_of_notMem (show x ∉ ({E} : Set ℝ) from hx)]
  rw [e, cfc_const_mul E _ H (hc.continuousOn _), Complex.coe_smul]

theorem exp_smul_mul_specProj {H : Op S} (hH : IsSelfAdjoint H) (E : ℝ) (c : ℂ) :
    NormedSpace.exp (c • H) * specProj H E = Complex.exp (c * E) • specProj H E := by
  have hpow : ∀ n : ℕ, (c • H) ^ n * specProj H E = (c * E) ^ n • specProj H E := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, smul_mul_assoc, mul_specProj hH, smul_smul, smul_smul]
      congr 1
      ring
  open scoped Matrix.Norms.L2Operator in
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • H)).mul_right (specProj H E)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c * (E : ℂ))).smul_const (specProj H E)
  have e : (fun n => ((n.factorial : ℂ)⁻¹ • (c • H) ^ n) * specProj H E) =
      fun n => ((n.factorial : ℂ)⁻¹ • (c * (E : ℂ)) ^ n) • specProj H E := by
    funext n; rw [smul_mul_assoc, hpow, smul_smul, smul_eq_mul]
  rw [e] at h1
  rw [h1.unique h2, ← Complex.exp_eq_exp_ℂ]

theorem specProj_mul_exp_smul {H : Op S} (hH : IsSelfAdjoint H) (E : ℝ) (c : ℂ) :
    specProj H E * NormedSpace.exp (c • H) = Complex.exp (c * E) • specProj H E := by
  have hpow : ∀ n : ℕ, specProj H E * (c • H) ^ n = (c * E) ^ n • specProj H E := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_smul_comm, specProj_mul hH, smul_smul, smul_smul]
      congr 1
      ring
  open scoped Matrix.Norms.L2Operator in
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • H)).mul_left (specProj H E)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c * (E : ℂ))).smul_const (specProj H E)
  have e : (fun n => specProj H E * ((n.factorial : ℂ)⁻¹ • (c • H) ^ n)) =
      fun n => ((n.factorial : ℂ)⁻¹ • (c * (E : ℂ)) ^ n) • specProj H E := by
    funext n; rw [mul_smul_comm, hpow, smul_smul, smul_eq_mul]
  rw [e] at h1
  rw [h1.unique h2, ← Complex.exp_eq_exp_ℂ]

theorem dyn_eq_sum {H : Op S} (hH : IsSelfAdjoint H) (t : ℝ) (A : Op S) :
    dyn H t A = ∑ E ∈ specFinset H, ∑ E' ∈ specFinset H,
      Complex.exp (I * (t : ℂ) * ((E - E' : ℝ) : ℂ)) • (specProj H E * A * specProj H E') := by
  have h1 : dyn H t A = (∑ E ∈ specFinset H, specProj H E) * dyn H t A *
      (∑ E' ∈ specFinset H, specProj H E') := by
    rw [sum_specProj hH, one_mul, mul_one]
  rw [h1, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun E' _ => ?_
  simp only [dyn]
  rw [show specProj H E * (NormedSpace.exp ((I * (t : ℂ)) • H) * A * NormedSpace.exp ((-(I * (t : ℂ))) • H)) *
      specProj H E' = (specProj H E * NormedSpace.exp ((I * (t : ℂ)) • H)) * A *
        (NormedSpace.exp ((-(I * (t : ℂ))) • H) * specProj H E') by noncomm_ring]
  rw [specProj_mul_exp_smul hH, exp_smul_mul_specProj hH, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

end SpecDevices

/-- **Lemma 5.9**: "`and for every operator $A$ on $\Fock$,`"
"`\int\Wg(t)\,\tau_t(A)\,\dd t=\sum_{E,E'\in\sigma(H_N)}\widehat W_\gamma(E'-E)\,\one_{\{E\}}(H_N)\,A\,\one_{\{E'\}}(H_N).`"
— for any self-adjoint `H` on any `Op S` (the module docstring). -/
theorem opIntegral_Wfilt_dyn (hϑ : IsCutoff ϑ) (hγ : 0 < γ) {S : Type*} [Fintype S] [DecidableEq S] {H : Op S}
    (hH : IsSelfAdjoint H) (A : Op S) :
    opIntegralOn Set.univ (fun t => Wfilt ϑ γ t • dyn H t A) =
      ∑ E ∈ specFinset H, ∑ E' ∈ specFinset H, What ϑ γ (E' - E) • (specProj H E * A * specProj H E') := by
  have hWi := (hasFiniteMoments_Wfilt hϑ hγ).1
  ext m m'
  simp only [opIntegralOn, Matrix.of_apply, Measure.restrict_univ]
  simp_rw [dyn_eq_sum hH]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  have hint : ∀ E E' : ℝ, Integrable fun t : ℝ => Wfilt ϑ γ t *
      (Complex.exp (I * (t : ℂ) * ((E - E' : ℝ) : ℂ)) * (specProj H E * A * specProj H E') m m') := by
    intro E E'
    refine Integrable.mono' (hWi.norm.mul_const ‖(specProj H E * A * specProj H E') m m'‖) ?_
      (Eventually.of_forall fun t => ?_)
    · exact (hasFiniteMoments_Wfilt hϑ hγ).1.aestronglyMeasurable.mul
        ((by fun_prop : Continuous fun t : ℝ => Complex.exp (I * (t : ℂ) * ((E - E' : ℝ) : ℂ)) *
          (specProj H E * A * specProj H E') m m').aestronglyMeasurable)
    · rw [norm_mul, norm_mul]
      have : ‖Complex.exp (I * (t : ℂ) * ((E - E' : ℝ) : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, one_mul]
  rw [integral_finsetSum _ fun E _ => integrable_finsetSum _ fun E' _ => hint E E']
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [integral_finsetSum _ fun E' _ => hint E E']
  refine Finset.sum_congr rfl fun E' _ => ?_
  simp_rw [← mul_assoc]
  rw [integral_mul_const]
  congr 1
  rw [← integral_Wfilt_mul_exp hϑ hγ (E' - E)]
  congr 1; funext t
  congr 2
  push_cast
  ring

end GeneratorFilter

/-! ## Lemma 5.10 (time representation of the clustering filter) -/

/-- **Lemma 5.10**: "`$\hat\zeta(t):=\int\zeta(u)e^{-\iu ut}\,\dd u$`". -/
def zetaHat (ζ : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ u, (ζ u : ℂ) * Complex.exp (-(I * (u : ℂ) * (t : ℂ)))

/-- **Lemma 5.10**: "`Let $\gamma':=-\gamma/2$, $\hat\zeta(t):=\int\zeta(u)e^{-\iu ut}\,\dd u$ and $F(t):=-e^{-\iu\gamma't}\hat\zeta(t)/(2\pi\iu)$`". -/
def Fclust (γ : ℝ) (ζ : ℝ → ℝ) (t : ℝ) : ℂ :=
  -(Complex.exp (-(I * ((-γ / 2 : ℝ) : ℂ) * (t : ℂ))) * zetaHat ζ t) / (2 * (π : ℂ) * I)

/-- A principal value `PV ∫ f(t) dt := lim_{ε→0⁺, T→∞} ∫_{ε<|t|<T} f(t) dt` exists and equals `L` (the limit the
proof of Lemma 5.10 takes: "`\lim_{\varepsilon\to0,\,T\to\infty}\int\zeta(v)\int_{\varepsilon<\abs t<T}`"). -/
def HasPVIntegral (f : ℝ → ℂ) (L : ℂ) : Prop :=
  Tendsto (fun p : ℝ × ℝ => ∫ t in {t : ℝ | p.1 < |t| ∧ |t| < p.2}, f t) (𝓝[>] (0 : ℝ) ×ˢ atTop) (𝓝 L)

/-- **Lemma 5.10**: "`where $c_F:=\PV_{-1}^{1}F(t)\,\dd t/t$`" — `lim_{ε→0⁺} ∫_{ε<|t|<1} F(t) dt/t` (`limUnder`;
`tendsto_cF`). -/
def cF (F : ℝ → ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ => ∫ t in {t : ℝ | ε < |t| ∧ |t| < 1}, F t / t

/-- **Lemma 5.10**: "`$G(u):=\int_u^1F(t)\,\dd t/t$ for $0<u<1$ and $G(u):=-\int_{-1}^uF(t)\,\dd t/t$ for $-1<u<0$`",
extended by `0` (Proposition 5.11: "`and $G_1$ is $G$ on $(-1,1)$ and $0$ otherwise`"; also `G(0) := 0`). -/
def Gclust (F : ℝ → ℂ) (u : ℝ) : ℂ :=
  if 0 < u ∧ u < 1 then ∫ t in u..1, F t / t
  else if -1 < u ∧ u < 0 then -∫ t in (-1)..u, F t / t else 0

/-- `‖F‖_∞ := sup_t |F(t)|`. -/
def supNorm (F : ℝ → ℂ) : ℝ :=
  ⨆ t : ℝ, ‖F t‖

section TimeRep

variable {Δ γ δ : ℝ} {ζ : ℝ → ℝ}

/-! ### Proof devices for Lemma 5.10: `F` as cosine transforms (phase (b); not statements of the paper)

`e^{iγt/2} ζ̂(t) = ∫ ζ(v + γ/2) e^{−ivt} dv` (translation), so with `R := δ + γ/2` and the shifted bump
`ζ_s(v) := ζ(v + γ/2)` (smooth, supported in `(−R, R)`), `F(t) = (2π)^{−1}(C_1(t) + i C_0(t))`, `C_0`, `C_1` the cosine
transforms `∫_{−R}^{R} ζ_s(v) cos(vt + α) dv` at `α = 0, −π/2`. Every derivative of `C_j` is again such a transform
(of `v^n ζ_s(v)`) and decays faster than any power: this is the Schwartz property. -/

section S510Devices

open Real Set

theorem gamma_pos_cp (hζ : ClusterParams Δ γ δ ζ) : 0 < γ := by
  linarith [hζ.Δ_nonneg, hζ.two_mul_Δ_lt]

theorem contDiff_shift (hζ : ClusterParams Δ γ δ ζ) : ContDiff ℝ ∞ fun v : ℝ => ζ (v + γ / 2) :=
  hζ.contDiff.comp (contDiff_id.add contDiff_const)

theorem tsupport_shift (hζ : ClusterParams Δ γ δ ζ) :
    tsupport (fun v : ℝ => ζ (v + γ / 2)) ⊆ Set.Ioo (-(δ + γ / 2)) (δ + γ / 2) := by
  have hγ := gamma_pos_cp hζ
  intro v hv
  have h := tsupport_comp_subset_preimage ζ
    (continuous_id.add continuous_const : Continuous fun v : ℝ => v + γ / 2) hv
  have h2 := hζ.tsupport_subset h
  simp only [Set.mem_Ioo, Pi.add_apply, id] at h2
  constructor <;> linarith [h2.1, h2.2]

theorem shift_zero_of_notMem (hζ : ClusterParams Δ γ δ ζ) {v : ℝ}
    (hv : v ∉ Set.Ioo (-(δ + γ / 2)) (δ + γ / 2)) : ζ (v + γ / 2) = 0 :=
  image_eq_zero_of_notMem_tsupport (f := fun v : ℝ => ζ (v + γ / 2)) fun h => hv (tsupport_shift hζ h)

theorem exp_mul_zetaHat_eq (hζ : ClusterParams Δ γ δ ζ) (t : ℝ) :
    Complex.exp (-(I * ((-γ / 2 : ℝ) : ℂ) * (t : ℂ))) * zetaHat ζ t =
      ((cosInt (fun v => ζ (v + γ / 2)) (-(δ + γ / 2)) (δ + γ / 2) 0 t : ℝ) : ℂ) -
        ((cosInt (fun v => ζ (v + γ / 2)) (-(δ + γ / 2)) (δ + γ / 2) (-(π / 2)) t : ℝ) : ℂ) * I := by
  have hγ := gamma_pos_cp hζ
  have hR : -(δ + γ / 2) ≤ δ + γ / 2 := by linarith [hζ.δ_pos]
  have hc : Continuous ζ := hζ.contDiff.continuous
  have h1 : Complex.exp (-(I * ((-γ / 2 : ℝ) : ℂ) * (t : ℂ))) * zetaHat ζ t =
      ∫ u, (ζ u : ℂ) * Complex.exp (I * (((γ / 2 - u) * t : ℝ) : ℂ)) := by
    unfold zetaHat
    rw [← integral_const_mul]
    congr 1; funext u
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h2 : ∫ u, (ζ u : ℂ) * Complex.exp (I * (((γ / 2 - u) * t : ℝ) : ℂ)) =
      ∫ v, (ζ (v + γ / 2) : ℂ) * Complex.exp (I * (((-v) * t : ℝ) : ℂ)) := by
    rw [← integral_add_right_eq_self (fun u => (ζ u : ℂ) * Complex.exp (I * (((γ / 2 - u) * t : ℝ) : ℂ))) (γ / 2)]
    congr 1; funext v
    rw [show (γ / 2 - (v + γ / 2)) * t = -v * t by ring]
  have h3 : ∀ v : ℝ, (ζ (v + γ / 2) : ℂ) * Complex.exp (I * (((-v) * t : ℝ) : ℂ)) =
      ((ζ (v + γ / 2) * Real.cos (v * t + 0) : ℝ) : ℂ) -
        ((ζ (v + γ / 2) * Real.cos (v * t + -(π / 2)) : ℝ) : ℂ) * I := by
    intro v
    rw [cexp_I_mul, neg_mul, Real.cos_neg, Real.sin_neg, add_zero,
      show v * t + -(π / 2) = v * t - π / 2 by ring, Real.cos_sub_pi_div_two]
    push_cast
    ring
  have h4 : ∫ v, (ζ (v + γ / 2) : ℂ) * Complex.exp (I * (((-v) * t : ℝ) : ℂ)) =
      ∫ v in (-(δ + γ / 2))..(δ + γ / 2), (ζ (v + γ / 2) : ℂ) * Complex.exp (I * (((-v) * t : ℝ) : ℂ)) := by
    rw [intervalIntegral.integral_of_le hR, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro v hv
    rw [shift_zero_of_notMem hζ (fun h => hv (Set.Ioo_subset_Ioc_self h))]
    simp
  have hcs := (contDiff_shift hζ).continuous
  have hi : ∀ α : ℝ, IntervalIntegrable (fun v : ℝ => ((ζ (v + γ / 2) * Real.cos (v * t + α) : ℝ) : ℂ)) volume
      (-(δ + γ / 2)) (δ + γ / 2) := fun α =>
    (by fun_prop : Continuous fun v : ℝ => ((ζ (v + γ / 2) * Real.cos (v * t + α) : ℝ) : ℂ)).intervalIntegrable _ _
  have hi' : IntervalIntegrable (fun v : ℝ => ((ζ (v + γ / 2) * Real.cos (v * t + -(π / 2)) : ℝ) : ℂ) * I) volume
      (-(δ + γ / 2)) (δ + γ / 2) :=
    (by fun_prop : Continuous fun v : ℝ => ((ζ (v + γ / 2) * Real.cos (v * t + -(π / 2)) : ℝ) : ℂ) * I).intervalIntegrable _ _
  rw [h1, h2, h4]
  simp_rw [h3]
  rw [intervalIntegral.integral_sub (hi 0) hi',
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  simp only [cosInt]

theorem Fclust_eq_cos (hζ : ClusterParams Δ γ δ ζ) (t : ℝ) :
    Fclust γ ζ t = (((2 * π)⁻¹ : ℝ) : ℂ) *
      (((cosInt (fun v => ζ (v + γ / 2)) (-(δ + γ / 2)) (δ + γ / 2) (-(π / 2)) t : ℝ) : ℂ) +
        I * ((cosInt (fun v => ζ (v + γ / 2)) (-(δ + γ / 2)) (δ + γ / 2) 0 t : ℝ) : ℂ)) := by
  have h := exp_mul_zetaHat_eq hζ t
  unfold Fclust
  rw [h]
  generalize ((cosInt (fun v => ζ (v + γ / 2)) (-(δ + γ / 2)) (δ + γ / 2) 0 t : ℝ) : ℂ) = a
  generalize ((cosInt (fun v => ζ (v + γ / 2)) (-(δ + γ / 2)) (δ + γ / 2) (-(π / 2)) t : ℝ) : ℂ) = b
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [div_eq_iff (by simp [hπ, Complex.I_ne_zero])]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end S510Devices

/-- **Lemma 5.10**: "`a Schwartz function`". -/
theorem exists_schwartz_Fclust (hζ : ClusterParams Δ γ δ ζ) : ∃ f : SchwartzMap ℝ ℂ, ⇑f = Fclust γ ζ := by
  set R := δ + γ / 2 with hRdef
  have hγ := gamma_pos_cp hζ
  have hR0 : 0 ≤ R := by have := hζ.δ_pos; positivity
  set ζs : ℝ → ℝ := fun v => ζ (v + γ / 2) with hζs
  have hζsc : ContDiff ℝ ∞ ζs := contDiff_shift hζ
  have hζsR : tsupport ζs ⊆ Set.Ioo (-R) R := tsupport_shift hζ
  set C₀ := cosInt ζs (-R) R 0 with hC₀def
  set C₁ := cosInt ζs (-R) R (-(π / 2)) with hC₁def
  set L₁ : ℝ →L[ℝ] ℂ := (((2 * π)⁻¹ : ℝ) : ℂ) • Complex.ofRealCLM with hL₁
  set L₀ : ℝ →L[ℝ] ℂ := ((((2 * π)⁻¹ : ℝ) : ℂ) * I) • Complex.ofRealCLM with hL₀
  have hF : Fclust γ ζ = (L₁ ∘ C₁) + (L₀ ∘ C₀) := by
    funext t
    rw [Fclust_eq_cos hζ t]
    simp only [Pi.add_apply, Function.comp_apply, hL₁, hL₀, smul_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
    ring
  have hC₀ : ContDiff ℝ ∞ C₀ := contDiff_cosInt hζsc.continuous _ _ _
  have hC₁ : ContDiff ℝ ∞ C₁ := contDiff_cosInt hζsc.continuous _ _ _
  have hs1 : ContDiff ℝ ∞ (L₁ ∘ C₁) := L₁.contDiff.comp hC₁
  have hs0 : ContDiff ℝ ∞ (L₀ ∘ C₀) := L₀.contDiff.comp hC₀
  have hsmooth : ContDiff ℝ ∞ (Fclust γ ζ) := by rw [hF]; exact hs1.add hs0
  refine ⟨⟨Fclust γ ζ, hsmooth, fun k n => ?_⟩, rfl⟩
  set φ : ℝ → ℝ := fun w => w ^ n * ζs w with hφdef
  have hφ : ContDiff ℝ ∞ φ := (contDiff_id.pow n).mul hζsc
  have hφR : tsupport φ ⊆ Set.Ioo (-R) R := tsupport_mul_subset_right.trans hζsR
  set B := ∫ w in (-R)..R, |iteratedDeriv k φ w| with hB
  refine ⟨(‖L₁‖ + ‖L₀‖) * B, fun x => ?_⟩
  have hn : ((n : ℕ) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  rw [hF, iteratedFDeriv_add_apply ((hs1.of_le hn).contDiffAt) ((hs0.of_le hn).contDiffAt)]
  have e1 : ‖iteratedFDeriv ℝ n (L₁ ∘ C₁) x‖ ≤
      ‖L₁‖ * |cosInt (fun w => w ^ n * ζs w) (-R) R (-(π / 2) + n * (π / 2)) x| := by
    have h := L₁.norm_iteratedFDeriv_comp_left (x := x) (n := n) hC₁.contDiffAt hn
    rwa [norm_iteratedFDeriv_eq_norm_iteratedDeriv (f := C₁), Real.norm_eq_abs, hC₁def,
      iteratedDeriv_cosInt hζsc.continuous] at h
  have e0 : ‖iteratedFDeriv ℝ n (L₀ ∘ C₀) x‖ ≤
      ‖L₀‖ * |cosInt (fun w => w ^ n * ζs w) (-R) R (0 + n * (π / 2)) x| := by
    have h := L₀.norm_iteratedFDeriv_comp_left (x := x) (n := n) hC₀.contDiffAt hn
    rwa [norm_iteratedFDeriv_eq_norm_iteratedDeriv (f := C₀), Real.norm_eq_abs, hC₀def,
      iteratedDeriv_cosInt hζsc.continuous] at h
  have d1 := cosInt_decay hφ hR0 hφR k (-(π / 2) + n * (π / 2)) x
  have d0 := cosInt_decay hφ hR0 hφR k (0 + n * (π / 2)) x
  rw [← hB] at d1 d0
  rw [Real.norm_eq_abs]
  have hxk : 0 ≤ |x| ^ k := by positivity
  calc |x| ^ k * ‖iteratedFDeriv ℝ n (L₁ ∘ C₁) x + iteratedFDeriv ℝ n (L₀ ∘ C₀) x‖
      ≤ |x| ^ k * (‖L₁‖ * |cosInt (fun w => w ^ n * ζs w) (-R) R (-(π / 2) + n * (π / 2)) x| +
          ‖L₀‖ * |cosInt (fun w => w ^ n * ζs w) (-R) R (0 + n * (π / 2)) x|) := by
        refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add e1 e0)) hxk
    _ = ‖L₁‖ * (|x| ^ k * |cosInt φ (-R) R (-(π / 2) + n * (π / 2)) x|) +
          ‖L₀‖ * (|x| ^ k * |cosInt φ (-R) R (0 + n * (π / 2)) x|) := by ring
    _ ≤ ‖L₁‖ * B + ‖L₀‖ * B :=
        add_le_add (mul_le_mul_of_nonneg_left d1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left d0 (norm_nonneg _))
    _ = (‖L₁‖ + ‖L₀‖) * B := by ring

/-! ### Proof devices for Lemma 5.10 (phase (b); not statements of the paper)

`ζ` is continuous with compact support, so `ζ̂` is continuous with `|ζ̂| ≤ ∫ζ = 1` and `|F| ≤ 1/2π` (hence `‖F‖_∞` is a
supremum of a bounded set); `e^{iγt/2} ζ̂(t) = ∫ ζ(u) e^{i(γ/2 − u)t} du` and `|e^{ix} − 1| ≤ |x|` give
`|F(t) − F(0)| ≤ (2π)^{−1}(δ + γ/2)|t|`; `∫_{ε<|t|<1} dt/t = 0` (an odd function on a symmetric set). -/

section T510Devices

open Real Set

theorem cp_zero_of_le (hζ : ClusterParams Δ γ δ ζ) {u : ℝ} (hu : δ ≤ |u|) : ζ u = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have := hζ.tsupport_subset h
  rw [Set.mem_Ioo] at this
  have := abs_lt.mpr this
  linarith

theorem hasCompactSupport_cp (hζ : ClusterParams Δ γ δ ζ) : HasCompactSupport ζ :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport ζ)
    (hζ.tsupport_subset.trans Set.Ioo_subset_Icc_self)

theorem integrable_cp (hζ : ClusterParams Δ γ δ ζ) : Integrable ζ :=
  hζ.contDiff.continuous.integrable_of_hasCompactSupport (hasCompactSupport_cp hζ)

theorem integrable_cp_mul (hζ : ClusterParams Δ γ δ ζ) {g : ℝ → ℂ} (hg : Continuous g) :
    Integrable fun u => (ζ u : ℂ) * g u := by
  have hc : Continuous fun u => (ζ u : ℂ) * g u :=
    (Complex.continuous_ofReal.comp hζ.contDiff.continuous).mul hg
  refine hc.integrable_of_hasCompactSupport ?_
  have h1 : HasCompactSupport fun u => (ζ u : ℂ) := (hasCompactSupport_cp hζ).comp_left Complex.ofReal_zero
  exact h1.mul_right

theorem norm_cexp_neg_I_mul (u t : ℝ) : ‖Complex.exp (-(I * (u : ℂ) * (t : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_zetaHat_le (hζ : ClusterParams Δ γ δ ζ) (t : ℝ) : ‖zetaHat ζ t‖ ≤ 1 := by
  unfold zetaHat
  calc ‖∫ u, (ζ u : ℂ) * Complex.exp (-(I * (u : ℂ) * (t : ℂ)))‖
      ≤ ∫ u, ‖(ζ u : ℂ) * Complex.exp (-(I * (u : ℂ) * (t : ℂ)))‖ := norm_integral_le_integral_norm _
    _ = ∫ u, ζ u := by
        congr 1; funext u
        rw [norm_mul, norm_cexp_neg_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hζ.nonneg u)]
    _ = 1 := hζ.integral_eq_one

theorem continuous_zetaHat (hζ : ClusterParams Δ γ δ ζ) : Continuous (zetaHat ζ) := by
  have hc : Continuous ζ := hζ.contDiff.continuous
  unfold zetaHat
  refine continuous_of_dominated (bound := fun u => |ζ u|) (fun t => ?_)
    (fun t => Eventually.of_forall fun u => ?_) (integrable_cp hζ).abs (Eventually.of_forall fun u => ?_)
  · exact (by fun_prop : Continuous fun u : ℝ => (ζ u : ℂ) * Complex.exp (-(I * (u : ℂ) * (t : ℂ)))).aestronglyMeasurable
  · rw [norm_mul, norm_cexp_neg_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
  · fun_prop

theorem continuous_Fclust (hζ : ClusterParams Δ γ δ ζ) : Continuous (Fclust γ ζ) := by
  have := continuous_zetaHat hζ
  unfold Fclust
  fun_prop

theorem norm_two_pi_I : ‖(2 : ℂ) * (π : ℂ) * I‖ = 2 * π := by
  simp [abs_of_pos Real.pi_pos]

theorem norm_Fclust_le (hζ : ClusterParams Δ γ δ ζ) (t : ℝ) : ‖Fclust γ ζ t‖ ≤ (2 * π)⁻¹ := by
  unfold Fclust
  rw [norm_div, norm_neg, norm_mul, norm_cexp_neg_I_mul, one_mul, norm_two_pi_I, div_eq_mul_inv, mul_comm]
  calc (2 * π)⁻¹ * ‖zetaHat ζ t‖ ≤ (2 * π)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (norm_zetaHat_le hζ t) (by positivity)
    _ = (2 * π)⁻¹ := mul_one _

theorem bddAbove_Fclust (hζ : ClusterParams Δ γ δ ζ) : BddAbove (Set.range fun t => ‖Fclust γ ζ t‖) :=
  ⟨(2 * π)⁻¹, by rintro _ ⟨t, rfl⟩; exact norm_Fclust_le hζ t⟩

theorem norm_le_supNorm (hζ : ClusterParams Δ γ δ ζ) (t : ℝ) : ‖Fclust γ ζ t‖ ≤ supNorm (Fclust γ ζ) :=
  le_ciSup (bddAbove_Fclust hζ) t

theorem norm_Fclust_sub_le (hζ : ClusterParams Δ γ δ ζ) (t : ℝ) :
    ‖Fclust γ ζ t - Fclust γ ζ 0‖ ≤ (2 * π)⁻¹ * (δ + γ / 2) * |t| := by
  have hγ : 0 < γ := by linarith [hζ.Δ_nonneg, hζ.two_mul_Δ_lt]
  have hc : ∀ s : ℝ, Fclust γ ζ s = -(2 * (π : ℂ) * I)⁻¹ *
      (Complex.exp (-(I * ((-γ / 2 : ℝ) : ℂ) * (s : ℂ))) * zetaHat ζ s) := by
    intro s; unfold Fclust; ring
  have heζ : ∀ s : ℝ, Complex.exp (-(I * ((-γ / 2 : ℝ) : ℂ) * (s : ℂ))) * zetaHat ζ s =
      ∫ u, (ζ u : ℂ) * Complex.exp (I * (((γ / 2 - u) * s : ℝ) : ℂ)) := by
    intro s
    unfold zetaHat
    rw [← integral_const_mul]
    congr 1; funext u
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hc t, hc 0, ← mul_sub, norm_mul, norm_neg, norm_inv, norm_two_pi_I, heζ t, heζ 0,
    ← integral_sub (integrable_cp_mul hζ (by fun_prop)) (integrable_cp_mul hζ (by fun_prop))]
  have hb : ∀ u, ‖(ζ u : ℂ) * Complex.exp (I * (((γ / 2 - u) * t : ℝ) : ℂ)) -
      (ζ u : ℂ) * Complex.exp (I * (((γ / 2 - u) * 0 : ℝ) : ℂ))‖ ≤ (δ + γ / 2) * |t| * ζ u := by
    intro u
    rw [mul_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hζ.nonneg u)]
    rcases le_or_gt δ |u| with hu | hu
    · rw [cp_zero_of_le hζ hu]; simp
    · have h1 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (γ / 2 - u) * t)
      rw [Real.norm_eq_abs, abs_mul] at h1
      have h2 : |γ / 2 - u| ≤ δ + γ / 2 := by
        have := abs_lt.mp hu
        rw [abs_le]; constructor <;> linarith
      calc ζ u * ‖Complex.exp (I * (((γ / 2 - u) * t : ℝ) : ℂ)) - 1‖ ≤ ζ u * (|γ / 2 - u| * |t|) :=
            mul_le_mul_of_nonneg_left h1 (hζ.nonneg u)
        _ ≤ ζ u * ((δ + γ / 2) * |t|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (abs_nonneg t)) (hζ.nonneg u)
        _ = (δ + γ / 2) * |t| * ζ u := by ring
  have hint3 : Integrable fun u => (δ + γ / 2) * |t| * ζ u := (integrable_cp hζ).const_mul _
  calc (2 * π)⁻¹ * ‖∫ u, ((ζ u : ℂ) * Complex.exp (I * (((γ / 2 - u) * t : ℝ) : ℂ)) -
        (ζ u : ℂ) * Complex.exp (I * (((γ / 2 - u) * 0 : ℝ) : ℂ)))‖
      ≤ (2 * π)⁻¹ * ∫ u, (δ + γ / 2) * |t| * ζ u := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (norm_integral_le_integral_norm _).trans
          (integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) hint3 (Eventually.of_forall hb))
    _ = (2 * π)⁻¹ * (δ + γ / 2) * |t| := by rw [integral_const_mul, hζ.integral_eq_one]; ring

theorem integral_inv_symm_eq_zero {ε : ℝ} :
    ∫ t in {t : ℝ | ε < |t| ∧ |t| < 1}, ((t : ℂ))⁻¹ = 0 := by
  set S := {t : ℝ | ε < |t| ∧ |t| < 1} with hSdef
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  rw [← integral_indicator hSm]
  have h1 : ∫ x, S.indicator (fun t : ℝ => ((t : ℂ))⁻¹) (-x) = ∫ x, S.indicator (fun t : ℝ => ((t : ℂ))⁻¹) x :=
    integral_neg_eq_self _ _
  have h2 : ∀ x, S.indicator (fun t : ℝ => ((t : ℂ))⁻¹) (-x) = -S.indicator (fun t : ℝ => ((t : ℂ))⁻¹) x := by
    intro x
    by_cases hx : x ∈ S
    · have hx' : -x ∈ S := by
        simp only [hSdef, Set.mem_ofPred_eq, abs_neg] at hx ⊢; exact hx
      rw [indicator_of_mem hx', indicator_of_mem hx]
      push_cast
      rw [inv_neg]
    · have hx' : -x ∉ S := by
        simp only [hSdef, Set.mem_ofPred_eq, abs_neg] at hx ⊢; exact hx
      rw [indicator_of_notMem hx', indicator_of_notMem hx, neg_zero]
  simp_rw [h2, integral_neg] at h1
  linear_combination (-1 / 2 : ℂ) * h1

end T510Devices

/-! ### Proof devices for Lemma 5.10: the principal-value formula (phase (b); not statements of the paper)

`F(t)e^{iωt}/t = −(2πi)^{−1} ∫ ζ(u) e^{i a_u t}/t du` with `a_u := ω + γ/2 − u`; on the shell `{ε < |t| < T}` (finite
measure, `|1/t| ≤ 1/ε`) Fubini gives `−(2πi)^{−1} ∫ ζ(u) · 2i ∫_ε^T sin(a_u t)/t dt du`; the inner integral is bounded by
`2(π/2 + 2)` (the Dirichlet integral `∫_0^A sin x/x` is bounded by `π/2 + 2`) and tends to `(π/2) sign a_u` as `ε → 0⁺`,
`T → ∞`; dominated convergence and `∫ ζ(u) sign(a − u) du = 1 − 2∫_a^∞ ζ`, `g(ω) = ∫_{ω+γ/2}^∞ ζ` give `g(ω) − ½`. The
block also carries the earlier Lemma 5.10 devices and `shell_eq`, moved here from below (the statement order). -/

section PVDevices

open Real Set
/-- A symmetric shell is the union of two intervals. -/
theorem shell_eq {f : ℝ → ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hl : IntervalIntegrable f volume (-b) (-a)) (hr : IntervalIntegrable f volume a b) :
    ∫ t in {t : ℝ | a < |t| ∧ |t| < b}, f t = (∫ t in (-b)..(-a), f t) + ∫ t in a..b, f t := by
  have hS : {t : ℝ | a < |t| ∧ |t| < b} = Set.Ioo (-b) (-a) ∪ Set.Ioo a b := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioo]
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inr ⟨h1, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · linarith
        · exact ⟨h1, h2⟩
    · rw [abs_of_neg ht]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inl ⟨by linarith, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨by linarith, by linarith⟩
        · linarith
  have hdis : Disjoint (Set.Ioo (-b) (-a)) (Set.Ioo a b) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    linarith [h1.2, h2.1]
  rw [hS, setIntegral_union hdis measurableSet_Ioo
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mp hl)
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp hr),
    ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le hab.le]

/-- `|∫_0^A sin x/x dx| ≤ π/2 + 2`. -/
theorem abs_Si_le (A : ℝ) : |∫ x in (0 : ℝ)..A, Real.sin x / x| ≤ π / 2 + 2 := by
  have hpos : ∀ A : ℝ, 0 ≤ A → |∫ x in (0 : ℝ)..A, Real.sin x / x| ≤ π / 2 + 2 := by
    intro A hA
    rcases le_or_gt A 1 with h1 | h1
    · have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := A) (C := 1)
        (f := fun x : ℝ => Real.sin x / x) (fun x _ => by
          rw [Real.norm_eq_abs]
          have := abs_sin_mul_div_le x 1
          rwa [mul_one, abs_one] at this)
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hA, one_mul] at h
      have : (0 : ℝ) < π := Real.pi_pos
      linarith
    · rw [integral_sin_div_eq hA]
      have hb : ∀ s ∈ Set.Ioi (0 : ℝ), ‖(1 - Real.exp (-(s * A)) * (s * Real.sin A + Real.cos A)) / (1 + s ^ 2)‖ ≤
          (1 + s ^ 2)⁻¹ + 2 * Real.exp (-s) := by
        intro s hs
        have hs0 : 0 < s := hs
        have hpos : (0 : ℝ) < 1 + s ^ 2 := by positivity
        have he : Real.exp (-(s * A)) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by nlinarith)
        have hsc : |s * Real.sin A + Real.cos A| ≤ s + 1 := by
          calc |s * Real.sin A + Real.cos A| ≤ |s * Real.sin A| + |Real.cos A| := abs_add_le _ _
            _ ≤ s * 1 + 1 := by
                rw [abs_mul, abs_of_pos hs0]
                exact add_le_add (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one A) hs0.le) (Real.abs_cos_le_one A)
            _ = s + 1 := by ring
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
        have h2 : |1 - Real.exp (-(s * A)) * (s * Real.sin A + Real.cos A)| ≤ 1 + Real.exp (-s) * (s + 1) := by
          calc |1 - Real.exp (-(s * A)) * (s * Real.sin A + Real.cos A)| ≤
                |1| + |Real.exp (-(s * A)) * (s * Real.sin A + Real.cos A)| := abs_sub _ _
            _ ≤ 1 + Real.exp (-s) * (s + 1) := by
                rw [abs_one, abs_mul, abs_of_pos (Real.exp_pos _)]
                exact add_le_add le_rfl (mul_le_mul he hsc (abs_nonneg _) (Real.exp_pos _).le)
        have h3 : Real.exp (-s) * (s + 1) ≤ 2 * Real.exp (-s) * (1 + s ^ 2) := by
          have := Real.exp_pos (-s)
          nlinarith [sq_nonneg (s - 1)]
        calc |1 - Real.exp (-(s * A)) * (s * Real.sin A + Real.cos A)| ≤ 1 + Real.exp (-s) * (s + 1) := h2
          _ ≤ 1 + 2 * Real.exp (-s) * (1 + s ^ 2) := by linarith
          _ = ((1 + s ^ 2)⁻¹ + 2 * Real.exp (-s)) * (1 + s ^ 2) := by field_simp
      have hint : IntegrableOn (fun s : ℝ => (1 + s ^ 2)⁻¹ + 2 * Real.exp (-s)) (Set.Ioi 0) :=
        integrable_inv_one_add_sq.integrableOn.add ((exp_neg_integrableOn_Ioi 0 one_pos).congr_fun
          (fun s _ => by ring_nf) measurableSet_Ioi |>.const_mul 2)
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall hb))).trans (le_of_eq ?_)
      rw [integral_add integrable_inv_one_add_sq.integrableOn
        ((exp_neg_integrableOn_Ioi 0 one_pos).congr_fun (fun s _ => by ring_nf) measurableSet_Ioi |>.const_mul 2),
        integral_Ioi_inv_one_add_sq', integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rcases le_or_gt 0 A with hA | hA
  · exact hpos A hA
  · have h := intervalIntegral.integral_comp_neg (a := 0) (b := -A) (fun x : ℝ => Real.sin x / x)
    simp only [neg_neg, neg_zero] at h
    have e : (fun x : ℝ => Real.sin (-x) / -x) = fun x => Real.sin x / x := by
      funext x; rw [Real.sin_neg, neg_div_neg_eq]
    simp only [e] at h
    rw [intervalIntegral.integral_symm 0 A] at h
    have := hpos (-A) (by linarith)
    rw [h, abs_neg] at this
    exact this

/-- `|∫_0^Ω sin(ta)/t dt| ≤ π/2 + 2` for `Ω ≥ 0`. -/
theorem abs_int_sin_mul_div_le (a Ω : ℝ) :
    |∫ t in (0 : ℝ)..Ω, Real.sin (t * a) / t| ≤ π / 2 + 2 := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have h1 : ∫ t in (0 : ℝ)..Ω, Real.sin (t * a) / t = -∫ u in (0 : ℝ)..Ω * (-a), Real.sin u / u := by
      rw [← integral_sin_mul_div_eq (neg_pos.mpr ha), ← intervalIntegral.integral_neg]
      congr 1; funext t; rw [mul_neg, Real.sin_neg, neg_div, neg_neg]
    rw [h1, abs_neg]; exact abs_Si_le _
  · simp only [mul_zero, Real.sin_zero, zero_div, intervalIntegral.integral_zero, abs_zero]
    have := Real.pi_pos; positivity
  · rw [integral_sin_mul_div_eq ha]; exact abs_Si_le _

theorem intervalIntegrable_sin_mul_div (a b c : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.sin (t * a) / t) volume b c :=
  intervalIntegrable_of_abs_le (measurable_sin_mul_div a) (fun t => abs_sin_mul_div_le t a) _ _

theorem tendsto_int_sin_shell (a : ℝ) :
    Tendsto (fun p : ℝ × ℝ => ∫ t in p.1..p.2, Real.sin (t * a) / t) (𝓝[>] (0 : ℝ) ×ˢ atTop)
      (𝓝 (π / 2 * Real.sign a)) := by
  have hT : Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, Real.sin (t * a) / t) atTop (𝓝 (π / 2 * Real.sign a)) :=
    tendsto_integral_sin_mul_div a
  have hε : Tendsto (fun ε : ℝ => ∫ t in (0 : ℝ)..ε, Real.sin (t * a) / t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hb : ∀ ε : ℝ, 0 ≤ ε → ‖∫ t in (0 : ℝ)..ε, Real.sin (t * a) / t‖ ≤ |a| * ε := by
      intro ε hε
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := ε) (C := |a|)
        (f := fun t : ℝ => Real.sin (t * a) / t) (fun t _ => by rw [Real.norm_eq_abs]; exact abs_sin_mul_div_le t a)
      rwa [sub_zero, abs_of_nonneg hε] at h
    have h2 : Tendsto (fun ε : ℝ => |a| * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ => |a| * ε) (𝓝 (0 : ℝ)) (𝓝 (|a| * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact hb ε hε.le
  have hsplit : (fun p : ℝ × ℝ => ∫ t in p.1..p.2, Real.sin (t * a) / t) =
      fun p => (∫ t in (0 : ℝ)..p.2, Real.sin (t * a) / t) - ∫ t in (0 : ℝ)..p.1, Real.sin (t * a) / t := by
    funext p
    rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_sin_mul_div a _ _)
      (intervalIntegrable_sin_mul_div a _ _)]
  rw [hsplit, show π / 2 * Real.sign a = π / 2 * Real.sign a - 0 by ring]
  exact (hT.comp tendsto_snd).sub (hε.comp tendsto_fst)

theorem integral_shell_exp_div (a : ℝ) {ε T : ℝ} (hε : 0 < ε) (hεT : ε < T) :
    ∫ t in {t : ℝ | ε < |t| ∧ |t| < T}, Complex.exp (I * ((a * t : ℝ) : ℂ)) / t =
      2 * I * ((∫ t in ε..T, Real.sin (t * a) / t : ℝ) : ℂ) := by
  have hcont : ∀ s : ℝ, s ≠ 0 → ContinuousAt (fun t : ℝ => Complex.exp (I * ((a * t : ℝ) : ℂ)) / t) s := by
    intro s hs
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    exact ((by fun_prop : Continuous fun t : ℝ => Complex.exp (I * ((a * t : ℝ) : ℂ))).continuousAt).div
      Complex.continuous_ofReal.continuousAt this
  have hl : IntervalIntegrable (fun t : ℝ => Complex.exp (I * ((a * t : ℝ) : ℂ)) / t) volume (-T) (-ε) :=
    ContinuousOn.intervalIntegrable fun s hs => (hcont s (by
      rw [Set.uIcc_of_le (by linarith)] at hs; linarith [hs.2])).continuousWithinAt
  have hr : IntervalIntegrable (fun t : ℝ => Complex.exp (I * ((a * t : ℝ) : ℂ)) / t) volume ε T :=
    ContinuousOn.intervalIntegrable fun s hs => (hcont s (by
      rw [Set.uIcc_of_le hεT.le] at hs; linarith [hs.1])).continuousWithinAt
  rw [shell_eq hε hεT hl hr]
  have h1 : ∫ t in (-T)..(-ε), Complex.exp (I * ((a * t : ℝ) : ℂ)) / t =
      ∫ s in ε..T, Complex.exp (I * ((a * -s : ℝ) : ℂ)) / ((-s : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_comp_neg (fun t : ℝ => Complex.exp (I * ((a * t : ℝ) : ℂ)) / t)]
  have hr' : IntervalIntegrable (fun s : ℝ => Complex.exp (I * ((a * -s : ℝ) : ℂ)) / ((-s : ℝ) : ℂ)) volume ε T := by
    refine ContinuousOn.intervalIntegrable fun s hs => ?_
    rw [Set.uIcc_of_le hεT.le] at hs
    have : ((-s : ℝ) : ℂ) ≠ 0 := by
      have : -s ≠ 0 := by linarith [hs.1]
      exact_mod_cast this
    exact (((by fun_prop : Continuous fun t : ℝ => Complex.exp (I * ((a * -t : ℝ) : ℂ))).continuousAt).div
      (Complex.continuous_ofReal.comp continuous_neg).continuousAt this).continuousWithinAt
  rw [h1, ← intervalIntegral.integral_add hr' hr, ← intervalIntegral.integral_ofReal,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    rw [cexp_I_mul, cexp_I_mul, mul_neg, Real.cos_neg, Real.sin_neg, mul_comm s a]
    push_cast
    field_simp
    ring


theorem exp_mul_zetaHat_integral (hζ : ClusterParams Δ γ δ ζ) (t : ℝ) :
    Complex.exp (-(I * ((-γ / 2 : ℝ) : ℂ) * (t : ℂ))) * zetaHat ζ t =
      ∫ u, (ζ u : ℂ) * Complex.exp (I * (((γ / 2 - u) * t : ℝ) : ℂ)) := by
  unfold zetaHat
  rw [← integral_const_mul]
  congr 1; funext u
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem Fclust_mul_exp_div_eq (hζ : ClusterParams Δ γ δ ζ) (w t : ℝ) :
    Fclust γ ζ t * Complex.exp (I * (w : ℂ) * (t : ℂ)) / t =
      -(2 * (π : ℂ) * I)⁻¹ * ∫ u, (ζ u : ℂ) * (Complex.exp (I * (((w + γ / 2 - u) * t : ℝ) : ℂ)) / t) := by
  have h1 := exp_mul_zetaHat_integral hζ t
  have e : Fclust γ ζ t * Complex.exp (I * (w : ℂ) * (t : ℂ)) / t =
      -(2 * (π : ℂ) * I)⁻¹ * ((Complex.exp (-(I * ((-γ / 2 : ℝ) : ℂ) * (t : ℂ))) * zetaHat ζ t) *
        (Complex.exp (I * (w : ℂ) * (t : ℂ)) / t)) := by
    unfold Fclust; ring
  rw [e, h1, ← integral_mul_const]
  congr 1; congr 1; funext u
  rw [mul_assoc, mul_div_assoc', ← Complex.exp_add]
  congr 3
  push_cast
  ring

theorem pv_rep (hζ : ClusterParams Δ γ δ ζ) (w : ℝ) {ε T : ℝ} (hε : 0 < ε) (hεT : ε < T) :
    ∫ t in {t : ℝ | ε < |t| ∧ |t| < T}, Fclust γ ζ t * Complex.exp (I * (w : ℂ) * (t : ℂ)) / t =
      -(2 * (π : ℂ) * I)⁻¹ *
        ∫ u, (ζ u : ℂ) * (2 * I * ((∫ t in ε..T, Real.sin (t * (w + γ / 2 - u)) / t : ℝ) : ℂ)) := by
  set Sh := {t : ℝ | ε < |t| ∧ |t| < T} with hSh
  have hSm : MeasurableSet Sh :=
    (measurableSet_lt measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hSsub : Sh ⊆ Set.Ioo (-T) T := fun t ht => abs_lt.mp ht.2
  have hfin : MeasureTheory.volume Sh ≠ ⊤ := ((measure_mono hSsub).trans_lt (by simp)).ne
  have : IsFiniteMeasure (volume.restrict Sh) := isFiniteMeasure_restrict.mpr hfin
  have hc : Continuous ζ := hζ.contDiff.continuous
  simp_rw [Fclust_mul_exp_div_eq hζ w]
  rw [integral_const_mul]
  congr 1
  set f : ℝ → ℝ → ℂ := fun t u => (ζ u : ℂ) * (Complex.exp (I * (((w + γ / 2 - u) * t : ℝ) : ℂ)) / t) with hf
  have hmeas : AEStronglyMeasurable (Function.uncurry f) ((volume.restrict Sh).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    have hm : Measurable fun z : ℝ × ℝ => ((ζ z.2 : ℝ) : ℂ) * (Complex.exp (I * (((w + γ / 2 - z.2) * z.1 : ℝ) : ℂ)) /
        ((z.1 : ℝ) : ℂ)) := by
      have hζm : Measurable ζ := hc.measurable
      fun_prop
    exact hm
  have hint : Integrable (Function.uncurry f) ((volume.restrict Sh).prod volume) := by
    refine (integrable_prod_iff hmeas).mpr ⟨Eventually.of_forall fun t => ?_, ?_⟩
    · exact integrable_cp_mul hζ (by fun_prop : Continuous fun u : ℝ =>
        Complex.exp (I * (((w + γ / 2 - u) * t : ℝ) : ℂ)) / (t : ℂ))
    · refine Integrable.mono' (integrable_const (ε⁻¹)) hmeas.norm.integral_prod_right' ?_
      refine (ae_restrict_iff' hSm).mpr (Eventually.of_forall fun t ht => ?_)
      have ht0 : ε < |t| := ht.1
      have e1 : ∫ u, ‖Function.uncurry f (t, u)‖ = ∫ u, |t|⁻¹ * ζ u := by
        congr 1; funext u
        simp only [Function.uncurry_apply_pair, hf]
        rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hζ.nonneg u),
          Complex.norm_real, Real.norm_eq_abs]
        have : ‖Complex.exp (I * (((w + γ / 2 - u) * t : ℝ) : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
        rw [this]; ring
      rw [e1, integral_const_mul, hζ.integral_eq_one, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (abs_nonneg t))]
      exact inv_anti₀ hε ht0.le
  rw [integral_integral_swap hint]
  congr 1; funext u
  simp only [hf]
  rw [integral_const_mul, integral_shell_exp_div (w + γ / 2 - u) hε hεT]

theorem gClust_eq_integral_Ioi (w : ℝ) :
    gClust γ ζ w = ∫ u in Set.Ioi (w + γ / 2), ζ u := by
  unfold gClust
  rw [← integral_sub_left_eq_self _ volume w]
  rw [← integral_indicator measurableSet_Ioi]
  congr 1; funext u
  simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_Ioi, sub_sub_cancel]
  by_cases h : w - u < -γ / 2
  · rw [ite_eq_left h, ite_eq_left (by linarith), mul_one]
  · rw [ite_eq_right h, ite_eq_right (by linarith), mul_zero]

theorem integral_sign_cp (hζ : ClusterParams Δ γ δ ζ) (a : ℝ) :
    ∫ u, ζ u * Real.sign (a - u) = 1 - 2 * ∫ u in Set.Ioi a, ζ u := by
  have hae : (fun u => ζ u * Real.sign (a - u)) =ᵐ[volume] fun u => ζ u - 2 * (Set.Ioi a).indicator ζ u := by
    have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ a := by
      rw [ae_iff]; simp
    filter_upwards [hne] with u hu
    rcases lt_or_gt_of_ne hu with h | h
    · rw [Real.sign_of_pos (by linarith), Set.indicator_of_notMem (by simp; linarith)]; ring
    · rw [Real.sign_of_neg (by linarith), Set.indicator_of_mem (by simpa using h)]; ring
  rw [integral_congr_ae hae, integral_sub (integrable_cp hζ) ((integrable_cp hζ).indicator measurableSet_Ioi |>.const_mul 2),
    integral_const_mul, integral_indicator measurableSet_Ioi, hζ.integral_eq_one]

end PVDevices

/-- **Lemma 5.10**: "`Then $g(\omega)=\tfrac12+\PV F(t)e^{\iu\omega t}\,\dd t/t$ for every $\omega\in\R$`". -/
theorem hasPVIntegral_gClust (hζ : ClusterParams Δ γ δ ζ) (w : ℝ) :
    HasPVIntegral (fun t => Fclust γ ζ t * Complex.exp (I * (w : ℂ) * (t : ℂ)) / t)
      ((gClust γ ζ w : ℂ) - 1 / 2) := by
  unfold HasPVIntegral
  have hc : Continuous ζ := hζ.contDiff.continuous
  set Lim := ∫ u, (ζ u : ℂ) * (2 * I * ((π / 2 * Real.sign (w + γ / 2 - u) : ℝ) : ℂ)) with hLim
  have hlim : Tendsto (fun p : ℝ × ℝ =>
      ∫ u, (ζ u : ℂ) * (2 * I * ((∫ t in p.1..p.2, Real.sin (t * (w + γ / 2 - u)) / t : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ) ×ˢ atTop) (𝓝 Lim) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => ‖(ζ u : ℂ)‖ * (2 * (2 * (π / 2 + 2)))) ?_ ?_ ?_ ?_
    · filter_upwards [prod_mem_prod self_mem_nhdsWithin (eventually_gt_atTop (0 : ℝ))] with p hp
      obtain ⟨hp1, hp2⟩ := hp
      have hp1' : 0 < p.1 := hp1
      have hp2' : 0 < p.2 := hp2
      -- continuity of `u ↦ S(w + γ/2 − u)` by domination
      have hS : Continuous fun u : ℝ => ∫ t in p.1..p.2, Real.sin (t * (w + γ / 2 - u)) / t := by
        refine intervalIntegral.continuous_of_dominated_interval (bound := fun t => |t|⁻¹) ?_ ?_ ?_ ?_
        · exact fun u => ((by fun_prop : Measurable fun t : ℝ =>
            Real.sin (t * (w + γ / 2 - u)) / t)).aestronglyMeasurable
        · intro u
          refine Eventually.of_forall fun t _ => ?_
          rw [Real.norm_eq_abs, abs_div]
          exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _) |>.trans (le_of_eq (one_div _))
        · refine ContinuousOn.intervalIntegrable fun t ht => ?_
          have : 0 < t := by
            rcases le_total p.1 p.2 with h | h
            · rw [Set.uIcc_of_le h] at ht; linarith [ht.1]
            · rw [Set.uIcc_of_ge h] at ht; linarith [ht.1, hp2']
          exact (continuous_abs.continuousAt.inv₀ (abs_pos.mpr this.ne').ne').continuousWithinAt
        · exact Eventually.of_forall fun t _ => by fun_prop
      exact (Complex.continuous_ofReal.comp hc |>.mul (continuous_const.mul
        (Complex.continuous_ofReal.comp hS))).aestronglyMeasurable
    · filter_upwards [prod_mem_prod self_mem_nhdsWithin (eventually_gt_atTop (0 : ℝ))] with p hp
      obtain ⟨hp1, hp2⟩ := hp
      have hp1' : 0 < p.1 := hp1
      refine Eventually.of_forall fun u => ?_
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hsplit : ∫ t in p.1..p.2, Real.sin (t * (w + γ / 2 - u)) / t =
          (∫ t in (0 : ℝ)..p.2, Real.sin (t * (w + γ / 2 - u)) / t) -
            ∫ t in (0 : ℝ)..p.1, Real.sin (t * (w + γ / 2 - u)) / t := by
        rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_sin_mul_div _ _ _)
          (intervalIntegrable_sin_mul_div _ _ _)]
      have hb : |∫ t in p.1..p.2, Real.sin (t * (w + γ / 2 - u)) / t| ≤ 2 * (π / 2 + 2) := by
        rw [hsplit]
        have h1 := abs_int_sin_mul_div_le (w + γ / 2 - u) p.2
        have h2 := abs_int_sin_mul_div_le (w + γ / 2 - u) p.1
        have := abs_sub _ _ |>.trans (add_le_add h1 h2)
        linarith
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [norm_mul, norm_mul, h2, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      linarith [hb]
    · exact ((integrable_cp hζ).ofReal.norm).mul_const _
    · refine Eventually.of_forall fun u => ?_
      have h := tendsto_int_sin_shell (w + γ / 2 - u)
      exact ((Complex.continuous_ofReal.tendsto _).comp h |>.const_mul (2 * I)).const_mul (ζ u : ℂ)
  have hval : -(2 * (π : ℂ) * I)⁻¹ * Lim = (gClust γ ζ w : ℂ) - 1 / 2 := by
    have e : Lim = ((π : ℂ) * I) * ((∫ u, ζ u * Real.sign (w + γ / 2 - u) : ℝ) : ℂ) := by
      rw [hLim, ← integral_complex_ofReal, ← integral_const_mul]
      congr 1; funext u
      push_cast; ring
    rw [e, integral_sign_cp hζ, gClust_eq_integral_Ioi w]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    ring
  rw [← hval]
  refine (hlim.const_mul _).congr' ?_
  filter_upwards [prod_mem_prod (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)) (eventually_gt_atTop (1 : ℝ))]
    with p hp
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
  have hp3' : 1 < p.2 := hp3
  exact (pv_rep hζ w hp1 (by linarith)).symm

/-- The principal value `c_F` exists, and the proof's "`where $c_F=\int_{-1}^1(F(t)-F(0))\,\dd t/t$ is finite because $F$ is smooth`". -/
theorem tendsto_cF (hζ : ClusterParams Δ γ δ ζ) :
    Tendsto (fun ε : ℝ => ∫ t in {t : ℝ | ε < |t| ∧ |t| < 1}, Fclust γ ζ t / t) (𝓝[>] (0 : ℝ))
        (𝓝 (cF (Fclust γ ζ))) ∧
      cF (Fclust γ ζ) = ∫ t in (-1 : ℝ)..1, (Fclust γ ζ t - Fclust γ ζ 0) / t := by
  set F := Fclust γ ζ with hF
  set L := (2 * π)⁻¹ * (δ + γ / 2) with hL
  have hγ : 0 < γ := by linarith [hζ.Δ_nonneg, hζ.two_mul_Δ_lt]
  have hL0 : 0 ≤ L := by have := hζ.δ_pos; positivity
  set J := ∫ t in (-1 : ℝ)..1, (F t - F 0) / t with hJ
  have hFc : Continuous F := continuous_Fclust hζ
  have hhb : ∀ t : ℝ, ‖(F t - F 0) / t‖ ≤ L := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · simp only [Complex.ofReal_zero, div_zero, norm_zero]; exact hL0
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (abs_pos.mpr ht)]
      exact norm_Fclust_sub_le hζ t
  have hhm : Measurable fun t : ℝ => (F t - F 0) / t :=
    (hFc.measurable.sub measurable_const).div Complex.measurable_ofReal
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖(∫ t in {t : ℝ | ε < |t| ∧ |t| < 1}, F t / t) - J‖ ≤ L * (2 * ε) := by
    intro ε hε0 hε1
    set S := {t : ℝ | ε < |t| ∧ |t| < 1} with hSdef
    have hSm : MeasurableSet S :=
      (measurableSet_lt measurable_const continuous_abs.measurable).inter
        (measurableSet_lt continuous_abs.measurable measurable_const)
    have hSsub : S ⊆ Set.Ioo (-1) 1 := fun t ht => abs_lt.mp ht.2
    have hint_h : IntegrableOn (fun t : ℝ => (F t - F 0) / t) (Set.Ioo (-1) 1) :=
      Measure.integrableOn_of_bounded (M := L) (by simp) hhm.aestronglyMeasurable
        (Eventually.of_forall fun t => hhb t)
    have hint_inv : IntegrableOn (fun t : ℝ => F 0 * ((t : ℂ))⁻¹) S := by
      refine Measure.integrableOn_of_bounded (M := ‖F 0‖ * ε⁻¹) ?_ ?_ ?_
      · exact ((measure_mono hSsub).trans_lt (by simp)).ne
      · exact (measurable_const.mul Complex.measurable_ofReal.inv).aestronglyMeasurable
      · refine (ae_restrict_iff' hSm).mpr (Eventually.of_forall fun t ht => ?_)
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hε0 ht.1.le) (norm_nonneg _)
    -- `F t / t = (F t − F 0)/t + F 0 · t⁻¹`
    have hsplit : ∫ t in S, F t / t = (∫ t in S, (F t - F 0) / t) + ∫ t in S, F 0 * ((t : ℂ))⁻¹ := by
      rw [← integral_add (hint_h.mono_set hSsub) hint_inv]
      refine setIntegral_congr_fun hSm fun t ht => ?_
      have ht0 : (t : ℂ) ≠ 0 := by
        have : t ≠ 0 := by
          have ht' : ε < |t| := ht.1
          intro h0; rw [h0, abs_zero] at ht'; linarith
        exact_mod_cast this
      field_simp
      ring
    rw [hsplit, integral_const_mul, integral_inv_symm_eq_zero, mul_zero, add_zero]
    -- `J = ∫_{(−1,1)} h`, and the difference is the integral over `(−1,1) \ S ⊆ [−ε, ε]`
    have hJ' : J = ∫ t in Set.Ioo (-1) 1, (F t - F 0) / t := by
      rw [hJ, intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    rw [hJ', ← norm_neg, neg_sub, ← setIntegral_sdiff hSm hint_h hSsub]
    have hdiff : Set.Ioo (-1) 1 \ S ⊆ Set.Icc (-ε) ε := by
      intro t ht
      have h1 := abs_lt.mpr ht.1
      have h2 : ¬ (ε < |t| ∧ |t| < 1) := ht.2
      have h3 : |t| ≤ ε := by
        by_contra h4
        exact h2 ⟨lt_of_not_ge h4, abs_lt.mpr ht.1⟩
      exact abs_le.mp h3
    have hvol : MeasureTheory.volume (Set.Ioo (-1) 1 \ S) < ⊤ :=
      (measure_mono hdiff).trans_lt (by simp)
    refine (norm_setIntegral_le_of_norm_le_const hvol fun t _ => hhb t).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hL0
    calc MeasureTheory.volume.real (Set.Ioo (-1) 1 \ S) ≤ MeasureTheory.volume.real (Set.Icc (-ε) ε) :=
          measureReal_mono hdiff (by simp)
      _ = 2 * ε := by
          rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
          ring
  have hlim : Tendsto (fun ε : ℝ => ∫ t in {t : ℝ | ε < |t| ∧ |t| < 1}, F t / t) (𝓝[>] (0 : ℝ)) (𝓝 J) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h2 : Tendsto (fun ε : ℝ => L * (2 * ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ => L * (2 * ε)) (𝓝 (0 : ℝ)) (𝓝 (L * (2 * 0))) :=
        (continuous_const.mul (continuous_const.mul continuous_id)).tendsto 0
      rw [mul_zero, mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    rw [norm_norm]
    exact key ε hε.1 hε.2
  have hcF : cF F = J := hlim.limUnder_eq
  exact ⟨by rw [hcF]; exact hlim, hcF⟩

/-! ### Proof devices for Lemma 5.10: the time representation (phase (b); not statements of the paper)

The scalar identity `g(x) = ½ + c_F + ∫_{|t|≥1} F(t)e^{itx}/t dt + ix ∫_{−1}^{1} G(u)e^{iux} du` from the principal-value
formula `hasPVIntegral_gClust`: split the shell `{ε < |t| < T}` at `|t| = 1`; on `(ε, 1)` and `(−1, −ε)` integrate by parts
against `G` (`G' = −F/t`, `G(±1) = 0`), the boundary terms `G(ε)e^{iεx} − G(−ε)e^{−iεx}` tend to `c_F` (`|G(±ε)| ≤
‖F‖_∞ log(1/ε)` and `|e^{±iεx} − 1| ≤ ε|x|`); on `1 ≤ |t| < T` the improper integrals. The operator form follows from
`τ_t(A) = Σ e^{it(E−E')} 1_E A 1_{E'}` and `1_E [H, A] 1_{E'} = (E − E') 1_E A 1_{E'}`. The block also carries a device copy
`norm_Gclust_le'` of `norm_Gclust_le` and the moment devices (moved here from before `hasFiniteMoments_timeRep`, since
the statements come later in the file). -/
theorem norm_Gclust_le' (hζ : ClusterParams Δ γ δ ζ) {u : ℝ} (hu : 0 < |u|) (hu1 : |u| < 1) :
    ‖Gclust (Fclust γ ζ) u‖ ≤ supNorm (Fclust γ ζ) * Real.log (1 / |u|) := by
  set S := supNorm (Fclust γ ζ) with hS
  rcases lt_or_gt_of_ne (abs_pos.mp hu) with h | h
  · have hu' : -1 < u ∧ u < 0 := ⟨by rw [abs_of_neg h] at hu1; linarith, h⟩
    have hn : ¬ (0 < u ∧ u < 1) := fun h' => absurd h'.1 (not_lt.mpr h.le)
    rw [Gclust, ite_eq_right hn, ite_eq_left hu', norm_neg, abs_of_neg h]
    have hle : (-1 : ℝ) ≤ u := hu'.1.le
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun t => S * (-t)⁻¹) hle ?_ ?_).trans ?_
    · refine Eventually.of_forall fun t ht => ?_
      have ht0 : t < 0 := lt_of_le_of_lt ht.2 h
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (norm_le_supNorm hζ t) (inv_nonneg.mpr (by linarith))
    · refine ContinuousOn.intervalIntegrable ?_
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      have hx0 : -x ≠ 0 := by linarith [hx.2]
      exact (continuousAt_const.mul (continuous_neg.continuousAt.inv₀ hx0)).continuousWithinAt
    · rw [intervalIntegral.integral_const_mul]
      have e : (fun t : ℝ => (-t)⁻¹) = fun t => -t⁻¹ := funext fun t => by rw [inv_neg]
      rw [e, intervalIntegral.integral_neg, integral_inv_of_neg (by norm_num) h, div_neg, div_one, one_div,
        Real.log_inv]
  · have hu' : 0 < u ∧ u < 1 := ⟨h, by rw [abs_of_pos h] at hu1; exact hu1⟩
    rw [Gclust, ite_eq_left hu', abs_of_pos h]
    have hle : u ≤ 1 := hu'.2.le
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun t => S * t⁻¹) hle ?_ ?_).trans ?_
    · refine Eventually.of_forall fun t ht => ?_
      have ht0 : 0 < t := lt_trans h ht.1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (norm_le_supNorm hζ t) (inv_nonneg.mpr ht0.le)
    · refine ContinuousOn.intervalIntegrable ?_
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      exact (continuousAt_const.mul (continuousAt_id.inv₀ hx0)).continuousWithinAt
    · rw [intervalIntegral.integral_const_mul, integral_inv_of_pos h one_pos]

/-! ### Proof devices for Lemma 5.10: the moments of the two filters (phase (b); not statements of the paper)

`|t|^k |F(t)| ≤ π^{−1} ∫_{−R}^{R} |ζ_s^{(k)}|`, so `F(t)/t` on `|t| ≥ 1` has `(1 + |t|)^j |F(t)/t| ≤ C_j (1 + t²)^{−1}`;
`G` is continuous on `(0, 1)` and on `(−1, 0)` (derivative `−F(u)/u`), zero outside, and `|G(u)| ≤ ‖F‖_∞ |log u|`, which
is integrable on `(−1, 1)`. -/

section S510bDevices

open Real Set

theorem norm_Fclust_decay (hζ : ClusterParams Δ γ δ ζ) (k : ℕ) (t : ℝ) :
    |t| ^ k * ‖Fclust γ ζ t‖ ≤
      π⁻¹ * ∫ w in (-(δ + γ / 2))..(δ + γ / 2), |iteratedDeriv k (fun v => ζ (v + γ / 2)) w| := by
  have hR0 : 0 ≤ δ + γ / 2 := by have := hζ.δ_pos; have := gamma_pos_cp hζ; positivity
  set B := ∫ w in (-(δ + γ / 2))..(δ + γ / 2), |iteratedDeriv k (fun v => ζ (v + γ / 2)) w| with hB
  rw [Fclust_eq_cos hζ t]
  set a := cosInt (fun v => ζ (v + γ / 2)) (-(δ + γ / 2)) (δ + γ / 2) 0 t with ha
  set b := cosInt (fun v => ζ (v + γ / 2)) (-(δ + γ / 2)) (δ + γ / 2) (-(π / 2)) t with hb
  have da := cosInt_decay (contDiff_shift hζ) hR0 (tsupport_shift hζ) k 0 t
  have db := cosInt_decay (contDiff_shift hζ) hR0 (tsupport_shift hζ) k (-(π / 2)) t
  rw [← ha] at da
  rw [← hb] at db
  rw [← hB] at da db
  have hn : ‖(((2 * π)⁻¹ : ℝ) : ℂ) * ((b : ℂ) + I * (a : ℂ))‖ ≤ (2 * π)⁻¹ * (|b| + |a|) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (by positivity)
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hpi : 0 < π := Real.pi_pos
  calc |t| ^ k * ‖(((2 * π)⁻¹ : ℝ) : ℂ) * ((b : ℂ) + I * (a : ℂ))‖ ≤ |t| ^ k * ((2 * π)⁻¹ * (|b| + |a|)) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (2 * π)⁻¹ * (|t| ^ k * |b| + |t| ^ k * |a|) := by ring
    _ ≤ (2 * π)⁻¹ * (B + B) := mul_le_mul_of_nonneg_left (add_le_add db da) (by positivity)
    _ = π⁻¹ * B := by field_simp; ring

theorem moment_bound_F1 (hζ : ClusterParams Δ γ δ ζ) (j : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, (1 + |t|) ^ j * ‖(if 1 ≤ |t| then Fclust γ ζ t / t else 0)‖ ≤ C * (1 + t ^ 2)⁻¹ := by
  have hR0 : 0 ≤ δ + γ / 2 := by have := hζ.δ_pos; have := gamma_pos_cp hζ; positivity
  set B := ∫ w in (-(δ + γ / 2))..(δ + γ / 2), |iteratedDeriv (j + 2) (fun v => ζ (v + γ / 2)) w| with hB
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg (by linarith) fun w _ => abs_nonneg _
  refine ⟨2 ^ (j + 1) * (π⁻¹ * B), fun t => ?_⟩
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hpos]
  split_ifs with ht
  · have h1 : (1 + |t|) ^ j ≤ 2 ^ j * |t| ^ j := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) j
    have h2 : 1 + t ^ 2 ≤ 2 * |t| ^ 2 := by rw [sq_abs]; nlinarith [sq_abs t, abs_nonneg t]
    have h3 : ‖Fclust γ ζ t / (t : ℂ)‖ ≤ ‖Fclust γ ζ t‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_self (norm_nonneg _) ht
    have h4 := norm_Fclust_decay hζ (j + 2) t
    rw [← hB] at h4
    calc (1 + |t|) ^ j * ‖Fclust γ ζ t / (t : ℂ)‖ * (1 + t ^ 2) ≤
          (2 ^ j * |t| ^ j) * ‖Fclust γ ζ t‖ * (2 * |t| ^ 2) := by gcongr
      _ = 2 ^ (j + 1) * (|t| ^ (j + 2) * ‖Fclust γ ζ t‖) := by ring
      _ ≤ 2 ^ (j + 1) * (π⁻¹ * B) := by gcongr
  · simp only [norm_zero, mul_zero, zero_mul]
    have : 0 < π⁻¹ := inv_pos.mpr Real.pi_pos
    positivity

theorem hasFiniteMoments_F1 (hζ : ClusterParams Δ γ δ ζ) :
    HasFiniteMoments (fun t => if 1 ≤ |t| then Fclust γ ζ t / t else 0) := by
  have hm : Measurable (fun t : ℝ => if 1 ≤ |t| then Fclust γ ζ t / t else 0) :=
    Measurable.ite (measurableSet_le measurable_const continuous_abs.measurable)
      ((continuous_Fclust hζ).measurable.div Complex.measurable_ofReal) measurable_const
  refine ⟨?_, fun j => ?_⟩
  · obtain ⟨C, hC⟩ := moment_bound_F1 hζ 0
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) hm.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    simpa using hC t
  · obtain ⟨C, hC⟩ := moment_bound_F1 hζ j
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) ?_ (Eventually.of_forall fun t => ?_)
    · exact ((continuous_const.add continuous_abs).pow j).aestronglyMeasurable.mul hm.aestronglyMeasurable.norm
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hC t

theorem Gclust_eq_indicator (F : ℝ → ℂ) :
    Gclust F = (Set.Ioo (0 : ℝ) 1).indicator (fun u => ∫ t in u..1, F t / t) +
      (Set.Ioo (-1 : ℝ) 0).indicator (fun u => -∫ t in (-1)..u, F t / t) := by
  funext u
  simp only [Gclust, Pi.add_apply, Set.indicator_apply, Set.mem_Ioo]
  by_cases h1 : 0 < u ∧ u < 1 <;> by_cases h2 : -1 < u ∧ u < 0
  · exact absurd h1.1 (not_lt.mpr h2.2.le)
  · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right h2, add_zero]
  · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, zero_add]
  · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, add_zero]

theorem continuousOn_Gpos (hζ : ClusterParams Δ γ δ ζ) :
    ContinuousOn (fun u => ∫ t in u..1, Fclust γ ζ t / t) (Set.Ioo 0 1) := by
  intro u hu
  have hf : ContinuousOn (fun t : ℝ => Fclust γ ζ t / t) (Set.Ioi 0) := by
    intro t ht
    have : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    exact ((continuous_Fclust hζ).continuousAt.div Complex.continuous_ofReal.continuousAt this).continuousWithinAt
  have hu0 : 0 < u := hu.1
  have hd : HasDerivAt (fun u => ∫ t in (1 : ℝ)..u, Fclust γ ζ t / t) (Fclust γ ζ u / u) u := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      exact hf.mono (fun x hx => by rw [Set.uIcc_of_ge hu.2.le] at hx; exact lt_of_lt_of_le hu0 hx.1)
    · exact hf.stronglyMeasurableAtFilter isOpen_Ioi u hu0
    · exact hf.continuousAt (Ioi_mem_nhds hu0)
  have e : (fun u => ∫ t in u..1, Fclust γ ζ t / t) = fun u => -∫ t in (1 : ℝ)..u, Fclust γ ζ t / t := by
    funext v; rw [intervalIntegral.integral_symm]
  rw [e]
  exact hd.continuousAt.neg.continuousWithinAt

theorem continuousOn_Gneg (hζ : ClusterParams Δ γ δ ζ) :
    ContinuousOn (fun u => -∫ t in (-1)..u, Fclust γ ζ t / t) (Set.Ioo (-1) 0) := by
  intro u hu
  have hf : ContinuousOn (fun t : ℝ => Fclust γ ζ t / t) (Set.Iio 0) := by
    intro t ht
    have : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_lt ht)
    exact ((continuous_Fclust hζ).continuousAt.div Complex.continuous_ofReal.continuousAt this).continuousWithinAt
  have hu0 : u < 0 := hu.2
  have hd : HasDerivAt (fun u => ∫ t in (-1 : ℝ)..u, Fclust γ ζ t / t) (Fclust γ ζ u / u) u := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      exact hf.mono (fun x hx => by rw [Set.uIcc_of_le hu.1.le] at hx; exact lt_of_le_of_lt hx.2 hu0)
    · exact hf.stronglyMeasurableAtFilter isOpen_Iio u hu0
    · exact hf.continuousAt (Iio_mem_nhds hu0)
  exact hd.continuousAt.neg.continuousWithinAt

theorem hasFiniteMoments_G (hζ : ClusterParams Δ γ δ ζ) : HasFiniteMoments (Gclust (Fclust γ ζ)) := by
  set S := supNorm (Fclust γ ζ) with hS
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (norm_le_supNorm hζ 0)
  have hmeas : AEStronglyMeasurable (Gclust (Fclust γ ζ)) volume := by
    rw [Gclust_eq_indicator]
    exact ((aestronglyMeasurable_indicator_iff measurableSet_Ioo).mpr
      ((continuousOn_Gpos hζ).aestronglyMeasurable measurableSet_Ioo)).add
      ((aestronglyMeasurable_indicator_iff measurableSet_Ioo).mpr
        ((continuousOn_Gneg hζ).aestronglyMeasurable measurableSet_Ioo))
  have hzero : ∀ u, u ∉ Set.Ioo (-1 : ℝ) 1 → Gclust (Fclust γ ζ) u = 0 := by
    intro u hu
    have h1 : ¬ (0 < u ∧ u < 1) := fun h => hu ⟨by linarith [h.1], h.2⟩
    have h2 : ¬ (-1 < u ∧ u < 0) := fun h => hu ⟨h.1, by linarith [h.2]⟩
    rw [Gclust, ite_eq_right h1, ite_eq_right h2]
  have hbound : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ‖Gclust (Fclust γ ζ) u‖ ≤ S * |Real.log u| := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hu0
    · have h0 : Gclust (Fclust γ ζ) 0 = 0 := by simp [Gclust]
      rw [h0, norm_zero]
      exact mul_nonneg hS0 (abs_nonneg _)
    · have hu' : 0 < |u| := abs_pos.mpr hu0
      have hu1 : |u| < 1 := abs_lt.mpr hu
      have h := norm_Gclust_le' hζ hu' hu1
      have hl : Real.log (1 / |u|) = |Real.log u| := by
        have hneg : Real.log u < 0 := by rw [← Real.log_abs]; exact Real.log_neg hu' hu1
        rw [one_div, Real.log_inv, Real.log_abs, abs_of_neg hneg]
      rw [hl] at h
      exact h
  have hlog : IntegrableOn (fun u => |Real.log u|) (Set.Ioo (-1 : ℝ) 1) :=
    IntegrableOn.mono_set (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).1.norm Set.Ioo_subset_Ioc_self
  have hint_j : ∀ j : ℕ, Integrable fun u => (1 + |u|) ^ j * ‖Gclust (Fclust γ ζ) u‖ := by
    intro j
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Set.Ioo (-1) 1) ?_ ?_
    · refine Integrable.mono' (hlog.const_mul (2 ^ j * S)) ?_ ?_
      · exact (((continuous_const.add continuous_abs).pow j).aestronglyMeasurable.mul hmeas.norm).restrict
      · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun u hu => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h1 : (1 + |u|) ^ j ≤ 2 ^ j := pow_le_pow_left₀ (by positivity) (by linarith [abs_lt.mpr hu]) j
        calc (1 + |u|) ^ j * ‖Gclust (Fclust γ ζ) u‖ ≤ 2 ^ j * (S * |Real.log u|) :=
              mul_le_mul h1 (hbound u hu) (norm_nonneg _) (by positivity)
          _ = 2 ^ j * S * |Real.log u| := by ring
    · intro u hu
      rw [hzero u hu, norm_zero, mul_zero]
  refine ⟨?_, hint_j⟩
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Set.Ioo (-1) 1) ?_ hzero
  exact Integrable.mono' (hlog.const_mul S) hmeas.restrict
    ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun u hu => hbound u hu))

end S510bDevices

section TimeRepDevices

open Real Set

theorem continuousOn_Fdiv_pos (hζ : ClusterParams Δ γ δ ζ) :
    ContinuousOn (fun t : ℝ => Fclust γ ζ t / t) (Set.Ioi 0) := by
  intro t ht
  have : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  exact ((continuous_Fclust hζ).continuousAt.div Complex.continuous_ofReal.continuousAt this).continuousWithinAt

theorem continuousOn_Fdiv_neg (hζ : ClusterParams Δ γ δ ζ) :
    ContinuousOn (fun t : ℝ => Fclust γ ζ t / t) (Set.Iio 0) := by
  intro t ht
  have : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_lt ht)
  exact ((continuous_Fclust hζ).continuousAt.div Complex.continuous_ofReal.continuousAt this).continuousWithinAt

theorem hasDerivAt_Gpos (hζ : ClusterParams Δ γ δ ζ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => ∫ s in u..1, Fclust γ ζ s / s) (-(Fclust γ ζ t / t)) t := by
  have hf := continuousOn_Fdiv_pos hζ
  have hd : HasDerivAt (fun u => ∫ s in (1 : ℝ)..u, Fclust γ ζ s / s) (Fclust γ ζ t / t) t := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      exact hf.mono fun y hy => by
        rcases le_total t 1 with h | h
        · rw [Set.uIcc_of_ge h] at hy; exact lt_of_lt_of_le ht hy.1
        · rw [Set.uIcc_of_le h] at hy; exact lt_of_lt_of_le one_pos hy.1
    · exact hf.stronglyMeasurableAtFilter isOpen_Ioi t ht
    · exact hf.continuousAt (Ioi_mem_nhds ht)
  have e : (fun u => ∫ s in u..1, Fclust γ ζ s / s) = fun u => -∫ s in (1 : ℝ)..u, Fclust γ ζ s / s := by
    funext v; rw [intervalIntegral.integral_symm]
  rw [e]
  exact hd.neg

theorem hasDerivAt_Gneg (hζ : ClusterParams Δ γ δ ζ) {t : ℝ} (ht : t < 0) :
    HasDerivAt (fun u => -∫ s in (-1)..u, Fclust γ ζ s / s) (-(Fclust γ ζ t / t)) t := by
  have hf := continuousOn_Fdiv_neg hζ
  have hd : HasDerivAt (fun u => ∫ s in (-1 : ℝ)..u, Fclust γ ζ s / s) (Fclust γ ζ t / t) t := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      exact hf.mono fun y hy => by
        rcases le_total t (-1) with h | h
        · rw [Set.uIcc_of_ge h] at hy; exact lt_of_le_of_lt hy.2 (by norm_num)
        · rw [Set.uIcc_of_le h] at hy; exact lt_of_le_of_lt hy.2 ht
    · exact hf.stronglyMeasurableAtFilter isOpen_Iio t ht
    · exact hf.continuousAt (Iio_mem_nhds ht)
  exact hd.neg

theorem hasDerivAt_cexp_I_mul (x t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (I * (t : ℂ) * (x : ℂ))) (Complex.exp (I * (t : ℂ) * (x : ℂ)) * (I * x)) t := by
  have h1 : HasDerivAt (fun y : ℝ => I * (y : ℂ) * (x : ℂ)) (I * 1 * x) t :=
    (((hasDerivAt_id t).ofReal_comp).const_mul I).mul_const (x : ℂ)
  have h2 := h1.cexp
  rw [mul_one] at h2
  exact h2

/-- Integration by parts on `(ε, 1)` against `G(u) = ∫_u^1 F(s) ds/s`. -/
theorem ibp_pos (hζ : ClusterParams Δ γ δ ζ) (x : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ t in ε..1, Fclust γ ζ t / t * Complex.exp (I * t * x) =
      (∫ s in ε..1, Fclust γ ζ s / s) * Complex.exp (I * ε * x) +
        I * x * ∫ t in ε..1, (∫ s in t..1, Fclust γ ζ s / s) * Complex.exp (I * t * x) := by
  have hpos : ∀ t ∈ Set.uIcc ε 1, 0 < t := fun t ht => by
    rw [Set.uIcc_of_le hε1] at ht; exact lt_of_lt_of_le hε ht.1
  have hd : ∀ t ∈ Set.uIcc ε 1, HasDerivAt (fun u => (∫ s in u..1, Fclust γ ζ s / s) * Complex.exp (I * u * x))
      (-(Fclust γ ζ t / t) * Complex.exp (I * t * x) +
        (∫ s in t..1, Fclust γ ζ s / s) * (Complex.exp (I * t * x) * (I * x))) t := fun t ht =>
    (hasDerivAt_Gpos hζ (hpos t ht)).mul (hasDerivAt_cexp_I_mul x t)
  have hPc : ContinuousOn (fun u => ∫ s in u..1, Fclust γ ζ s / s) (Set.uIcc ε 1) := fun t ht =>
    (hasDerivAt_Gpos hζ (hpos t ht)).continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun t : ℝ => Fclust γ ζ t / t) (Set.uIcc ε 1) :=
    (continuousOn_Fdiv_pos hζ).mono fun t ht => hpos t ht
  have hec : Continuous fun t : ℝ => Complex.exp (I * (t : ℂ) * (x : ℂ)) := by fun_prop
  have i1 : IntervalIntegrable (fun t : ℝ => -(Fclust γ ζ t / t) * Complex.exp (I * t * x)) volume ε 1 :=
    (hfc.neg.mul hec.continuousOn).intervalIntegrable
  have i2 : IntervalIntegrable (fun t : ℝ => (∫ s in t..1, Fclust γ ζ s / s) * (Complex.exp (I * t * x) * (I * x)))
      volume ε 1 := (hPc.mul (hec.continuousOn.mul continuousOn_const)).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (i1.add i2)
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_same, zero_mul, zero_sub] at h
  have e1 : ∫ t in ε..1, -(Fclust γ ζ t / t) * Complex.exp (I * t * x) =
      -∫ t in ε..1, Fclust γ ζ t / t * Complex.exp (I * t * x) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext t; ring
  have e2 : ∫ t in ε..1, (∫ s in t..1, Fclust γ ζ s / s) * (Complex.exp (I * t * x) * (I * x)) =
      I * x * ∫ t in ε..1, (∫ s in t..1, Fclust γ ζ s / s) * Complex.exp (I * t * x) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
  rw [e1, e2] at h
  linear_combination -h

/-- Integration by parts on `(−1, −ε)` against `G(u) = −∫_{−1}^u F(s) ds/s`. -/
theorem ibp_neg (hζ : ClusterParams Δ γ δ ζ) (x : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ t in (-1)..(-ε), Fclust γ ζ t / t * Complex.exp (I * t * x) =
      -((-∫ s in (-1)..(-ε), Fclust γ ζ s / s) * Complex.exp (I * ((-ε : ℝ) : ℂ) * x)) +
        I * x * ∫ t in (-1)..(-ε), (-∫ s in (-1)..t, Fclust γ ζ s / s) * Complex.exp (I * t * x) := by
  have hle : (-1 : ℝ) ≤ -ε := by linarith
  have hneg : ∀ t ∈ Set.uIcc (-1) (-ε), t < 0 := fun t ht => by
    rw [Set.uIcc_of_le hle] at ht; exact lt_of_le_of_lt ht.2 (by linarith)
  have hd : ∀ t ∈ Set.uIcc (-1) (-ε), HasDerivAt (fun u => (-∫ s in (-1)..u, Fclust γ ζ s / s) * Complex.exp (I * u * x))
      (-(Fclust γ ζ t / t) * Complex.exp (I * t * x) +
        (-∫ s in (-1)..t, Fclust γ ζ s / s) * (Complex.exp (I * t * x) * (I * x))) t := fun t ht =>
    (hasDerivAt_Gneg hζ (hneg t ht)).mul (hasDerivAt_cexp_I_mul x t)
  have hNc : ContinuousOn (fun u => -∫ s in (-1)..u, Fclust γ ζ s / s) (Set.uIcc (-1) (-ε)) := fun t ht =>
    (hasDerivAt_Gneg hζ (hneg t ht)).continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun t : ℝ => Fclust γ ζ t / t) (Set.uIcc (-1) (-ε)) :=
    (continuousOn_Fdiv_neg hζ).mono fun t ht => hneg t ht
  have hec : Continuous fun t : ℝ => Complex.exp (I * (t : ℂ) * (x : ℂ)) := by fun_prop
  have i1 : IntervalIntegrable (fun t : ℝ => -(Fclust γ ζ t / t) * Complex.exp (I * t * x)) volume (-1) (-ε) :=
    (hfc.neg.mul hec.continuousOn).intervalIntegrable
  have i2 : IntervalIntegrable (fun t : ℝ => (-∫ s in (-1)..t, Fclust γ ζ s / s) * (Complex.exp (I * t * x) * (I * x)))
      volume (-1) (-ε) := (hNc.mul (hec.continuousOn.mul continuousOn_const)).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (i1.add i2)
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_same, neg_zero, zero_mul, sub_zero] at h
  have e1 : ∫ t in (-1)..(-ε), -(Fclust γ ζ t / t) * Complex.exp (I * t * x) =
      -∫ t in (-1)..(-ε), Fclust γ ζ t / t * Complex.exp (I * t * x) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext t; ring
  have e2 : ∫ t in (-1)..(-ε), (-∫ s in (-1)..t, Fclust γ ζ s / s) * (Complex.exp (I * t * x) * (I * x)) =
      I * x * ∫ t in (-1)..(-ε), (-∫ s in (-1)..t, Fclust γ ζ s / s) * Complex.exp (I * t * x) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
  rw [e1, e2] at h
  linear_combination -h

theorem norm_cexp_I_mul_sub_one_le (t x : ℝ) : ‖Complex.exp (I * (t : ℂ) * (x : ℂ)) - 1‖ ≤ |t| * |x| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * x)
  rw [Real.norm_eq_abs, abs_mul] at h
  rw [show I * (t : ℂ) * (x : ℂ) = I * ((t * x : ℝ) : ℂ) by push_cast; ring]
  exact h

theorem integrable_Gclust_mul_exp (hζ : ClusterParams Δ γ δ ζ) (x : ℝ) :
    Integrable fun u : ℝ => Gclust (Fclust γ ζ) u * Complex.exp (I * u * x) := by
  have hG := (hasFiniteMoments_G hζ).1
  refine Integrable.mono' hG.norm (hG.aestronglyMeasurable.mul
    (by fun_prop : Continuous fun u : ℝ => Complex.exp (I * u * x)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  have : ‖Complex.exp (I * (u : ℂ) * (x : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
  rw [this, mul_one]

theorem integrableOn_F1_mul_exp (hζ : ClusterParams Δ γ δ ζ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => Fclust γ ζ t / t * Complex.exp (I * t * x)) {t : ℝ | 1 ≤ |t|} := by
  have hF1 := (hasFiniteMoments_F1 hζ).1
  have hS : MeasurableSet {t : ℝ | 1 ≤ |t|} := measurableSet_le measurable_const continuous_abs.measurable
  have hm : AEStronglyMeasurable (fun t : ℝ => Fclust γ ζ t / t * Complex.exp (I * t * x)) volume :=
    (((continuous_Fclust hζ).measurable.div Complex.measurable_ofReal).mul
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (I * t * x)).measurable).aestronglyMeasurable
  refine Integrable.mono' hF1.norm.integrableOn hm.restrict ((ae_restrict_iff' hS).mpr
    (Eventually.of_forall fun t ht => ?_))
  have ht' : 1 ≤ |t| := ht
  rw [ite_eq_left ht', norm_mul]
  have : ‖Complex.exp (I * (t : ℂ) * (x : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
  rw [this, mul_one]

theorem gClust_timeRep_scalar (hζ : ClusterParams Δ γ δ ζ) (x : ℝ) :
    ((gClust γ ζ x : ℝ) : ℂ) = (1 / 2 : ℂ) + cF (Fclust γ ζ) +
      (∫ t in {t : ℝ | 1 ≤ |t|}, Fclust γ ζ t / t * Complex.exp (I * t * x)) +
      I * x * ∫ u in Set.Ioo (-1) 1, Gclust (Fclust γ ζ) u * Complex.exp (I * u * x) := by
  set F := Fclust γ ζ with hFdef
  set G := Gclust F with hGdef
  set S := supNorm F with hSdef
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (norm_le_supNorm hζ 0)
  have hFc : Continuous F := continuous_Fclust hζ
  have hec : Continuous fun t : ℝ => Complex.exp (I * (t : ℂ) * (x : ℂ)) := by fun_prop
  -- the principal value
  have hPV := hasPVIntegral_gClust hζ x
  have hfun : (fun t : ℝ => Fclust γ ζ t * Complex.exp (I * (x : ℂ) * (t : ℂ)) / t) =
      fun t : ℝ => F t / t * Complex.exp (I * t * x) := by
    funext t; rw [show I * (x : ℂ) * (t : ℂ) = I * (t : ℂ) * (x : ℂ) by ring]; ring
  unfold HasPVIntegral at hPV
  rw [hfun] at hPV
  -- the pieces near `0`
  have hGe := integrable_Gclust_mul_exp hζ x
  have hGeI : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => G u * Complex.exp (I * u * x)) volume a b :=
    fun a b => hGe.intervalIntegrable
  set Alim := cF F + I * x * ∫ u in Set.Ioo (-1) 1, G u * Complex.exp (I * u * x) with hAlim
  have hA : Tendsto (fun ε : ℝ => (∫ t in (-1)..(-ε), F t / t * Complex.exp (I * t * x)) +
      ∫ t in ε..1, F t / t * Complex.exp (I * t * x)) (𝓝[>] 0) (𝓝 Alim) := by
    -- the exact identity for `0 < ε < 1`
    have hid : ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∫ t in (-1)..(-ε), F t / t * Complex.exp (I * t * x)) + ∫ t in ε..1, F t / t * Complex.exp (I * t * x) =
          (∫ t in {t : ℝ | ε < |t| ∧ |t| < 1}, F t / t) +
            G ε * (Complex.exp (I * ε * x) - 1) - G (-ε) * (Complex.exp (I * ((-ε : ℝ) : ℂ) * x) - 1) +
            I * x * ((∫ u in (-1)..(-ε), G u * Complex.exp (I * u * x)) + ∫ u in ε..1, G u * Complex.exp (I * u * x)) := by
      intro ε hε hε1
      rw [ibp_pos hζ x hε hε1.le, ibp_neg hζ x hε hε1.le]
      have hGε : G ε = ∫ s in ε..1, F s / s := by
        simp only [hGdef, Gclust, ite_eq_left (show 0 < ε ∧ ε < 1 from ⟨hε, hε1⟩)]
      have hGmε : G (-ε) = -∫ s in (-1)..(-ε), F s / s := by
        have h1 : ¬ (0 < -ε ∧ -ε < 1) := fun h => by linarith [h.1]
        simp only [hGdef, Gclust, ite_eq_right h1, ite_eq_left (show -1 < -ε ∧ -ε < 0 from ⟨by linarith, by linarith⟩)]
      have hP : ∫ t in ε..1, (∫ s in t..1, F s / s) * Complex.exp (I * t * x) =
          ∫ u in ε..1, G u * Complex.exp (I * u * x) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hε1.le] at ht
        rcases eq_or_lt_of_le ht.2 with h | h
        · simp only [h, intervalIntegral.integral_same, hGdef, Gclust]
          simp
        · simp only [hGdef, Gclust, ite_eq_left (show 0 < t ∧ t < 1 from ⟨lt_of_lt_of_le hε ht.1, h⟩)]
      have hN : ∫ t in (-1)..(-ε), (-∫ s in (-1)..t, F s / s) * Complex.exp (I * t * x) =
          ∫ u in (-1)..(-ε), G u * Complex.exp (I * u * x) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤ -ε)] at ht
        rcases eq_or_lt_of_le ht.1 with h | h
        · subst h
          simp only [intervalIntegral.integral_same, neg_zero, zero_mul, hGdef, Gclust]
          simp
        · have h1 : ¬ (0 < t ∧ t < 1) := fun h' => by linarith [h'.1, ht.2]
          simp only [hGdef, Gclust, ite_eq_right h1,
            ite_eq_left (show -1 < t ∧ t < 0 from ⟨h, by linarith [ht.2]⟩)]
      have hshell := shell_eq (f := fun t => F t / t) hε hε1
        ((continuousOn_Fdiv_neg hζ).mono (fun t ht => by
          rw [Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤ -ε)] at ht; exact lt_of_le_of_lt ht.2 (by linarith))
          |>.intervalIntegrable)
        ((continuousOn_Fdiv_pos hζ).mono (fun t ht => by
          rw [Set.uIcc_of_le hε1.le] at ht; exact lt_of_lt_of_le hε ht.1) |>.intervalIntegrable)
      rw [hP, hN, hshell, hGε, hGmε]
      ring
    -- the limits of the pieces
    have h1 : Tendsto (fun ε : ℝ => ∫ t in {t : ℝ | ε < |t| ∧ |t| < 1}, F t / t) (𝓝[>] 0) (𝓝 (cF F)) :=
      (tendsto_cF hζ).1
    have hlog : Tendsto (fun ε : ℝ => ε * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have h2 : Tendsto (fun ε : ℝ => G ε * (Complex.exp (I * ε * x) - 1)) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ ((hlog.neg.const_mul (S * |x|)).trans (by simp))
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      rw [norm_mul]
      have hg := norm_Gclust_le' hζ (show 0 < |ε| from abs_pos.mpr hε.1.ne') (by rw [abs_of_pos hε.1]; exact hε.2)
      rw [abs_of_pos hε.1, one_div, Real.log_inv] at hg
      have he := norm_cexp_I_mul_sub_one_le ε x
      rw [abs_of_pos hε.1] at he
      calc ‖G ε‖ * ‖Complex.exp (I * (ε : ℂ) * (x : ℂ)) - 1‖ ≤ (S * -Real.log ε) * (ε * |x|) :=
            mul_le_mul hg he (norm_nonneg _) (mul_nonneg hS0 (by
              have := Real.log_nonpos hε.1.le hε.2.le; linarith))
        _ = S * |x| * -(ε * Real.log ε) := by ring
    have h3 : Tendsto (fun ε : ℝ => G (-ε) * (Complex.exp (I * ((-ε : ℝ) : ℂ) * x) - 1)) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ ((hlog.neg.const_mul (S * |x|)).trans (by simp))
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      rw [norm_mul]
      have hg := norm_Gclust_le' hζ (show 0 < |-ε| by rw [abs_neg]; exact abs_pos.mpr hε.1.ne')
        (by rw [abs_neg, abs_of_pos hε.1]; exact hε.2)
      rw [abs_neg, abs_of_pos hε.1, one_div, Real.log_inv] at hg
      have he := norm_cexp_I_mul_sub_one_le (-ε) x
      rw [abs_neg, abs_of_pos hε.1] at he
      calc ‖G (-ε)‖ * ‖Complex.exp (I * ((-ε : ℝ) : ℂ) * (x : ℂ)) - 1‖ ≤ (S * -Real.log ε) * (ε * |x|) :=
            mul_le_mul hg he (norm_nonneg _) (mul_nonneg hS0 (by
              have := Real.log_nonpos hε.1.le hε.2.le; linarith))
        _ = S * |x| * -(ε * Real.log ε) := by ring
    have h4 : Tendsto (fun ε : ℝ => (∫ u in (-1)..(-ε), G u * Complex.exp (I * u * x)) +
        ∫ u in ε..1, G u * Complex.exp (I * u * x)) (𝓝[>] 0)
        (𝓝 ((∫ u in (-1)..0, G u * Complex.exp (I * u * x)) + ∫ u in (0 : ℝ)..1, G u * Complex.exp (I * u * x))) := by
      have hc1 : Continuous fun b : ℝ => ∫ u in (-1)..b, G u * Complex.exp (I * u * x) :=
        intervalIntegral.continuous_primitive hGeI (-1)
      have hc2 : Continuous fun a : ℝ => ∫ u in a..1, G u * Complex.exp (I * u * x) := by
        have e : (fun a : ℝ => ∫ u in a..1, G u * Complex.exp (I * u * x)) =
            fun a => -∫ u in (1 : ℝ)..a, G u * Complex.exp (I * u * x) := by
          funext a; rw [intervalIntegral.integral_symm]
        rw [e]
        exact (intervalIntegral.continuous_primitive hGeI 1).neg
      have t1 : Tendsto (fun ε : ℝ => ∫ u in (-1)..(-ε), G u * Complex.exp (I * u * x)) (𝓝[>] 0)
          (𝓝 (∫ u in (-1)..0, G u * Complex.exp (I * u * x))) := by
        have := (hc1.comp continuous_neg).tendsto 0
        simp only [Function.comp_def, neg_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have t2 : Tendsto (fun ε : ℝ => ∫ u in ε..1, G u * Complex.exp (I * u * x)) (𝓝[>] 0)
          (𝓝 (∫ u in (0 : ℝ)..1, G u * Complex.exp (I * u * x))) :=
        (hc2.tendsto 0).mono_left nhdsWithin_le_nhds
      exact t1.add t2
    have hIoo : ∫ u in Set.Ioo (-1) 1, G u * Complex.exp (I * u * x) =
        (∫ u in (-1)..0, G u * Complex.exp (I * u * x)) + ∫ u in (0 : ℝ)..1, G u * Complex.exp (I * u * x) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hGeI _ _) (hGeI _ _),
        intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    have hlim := ((h1.add h2).sub h3).add (h4.const_mul (I * x))
    rw [add_zero, sub_zero, ← hIoo] at hlim
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (hid ε hε.1 hε.2).symm
  -- the pieces near `∞`
  have hIF := integrableOn_F1_mul_exp hζ x
  have hIic : IntegrableOn (fun t : ℝ => F t / t * Complex.exp (I * t * x)) (Set.Iic (-1)) :=
    hIF.mono_set fun t ht => by
      have ht' : t ≤ -1 := ht
      show 1 ≤ |t|
      rw [abs_of_neg (by linarith)]; linarith
  have hIoi : IntegrableOn (fun t : ℝ => F t / t * Complex.exp (I * t * x)) (Set.Ioi 1) :=
    hIF.mono_set fun t ht => by
      have ht' : 1 < t := ht
      show 1 ≤ |t|
      rw [abs_of_pos (by linarith)]; linarith
  set Blim := ∫ t in {t : ℝ | 1 ≤ |t|}, F t / t * Complex.exp (I * t * x) with hBlim
  have hB : Tendsto (fun T : ℝ => (∫ t in (-T)..(-1), F t / t * Complex.exp (I * t * x)) +
      ∫ t in (1 : ℝ)..T, F t / t * Complex.exp (I * t * x)) atTop (𝓝 Blim) := by
    have t1 := intervalIntegral_tendsto_integral_Iic (-1) hIic (tendsto_neg_atTop_atBot)
    have t2 := intervalIntegral_tendsto_integral_Ioi 1 hIoi tendsto_id
    have hsplit : Blim = (∫ t in Set.Iic (-1), F t / t * Complex.exp (I * t * x)) +
        ∫ t in Set.Ioi 1, F t / t * Complex.exp (I * t * x) := by
      have hset : {t : ℝ | 1 ≤ |t|} = Set.Iic (-1) ∪ Set.Ici 1 := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
        constructor
        · intro h
          rcases le_or_gt 0 t with h0 | h0
          · rw [abs_of_nonneg h0] at h; exact Or.inr h
          · rw [abs_of_neg h0] at h; exact Or.inl (by linarith)
        · rintro (h | h)
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; exact h
      have hdis : Disjoint (Set.Iic (-1 : ℝ)) (Set.Ici 1) := by
        rw [Set.disjoint_left]; intro t h1 h2
        have : t ≤ -1 := h1
        have : 1 ≤ t := h2
        linarith
      rw [hBlim, hset, setIntegral_union hdis measurableSet_Ici hIic
        (hIF.mono_set fun t ht => by
          have ht' : 1 ≤ t := ht
          show 1 ≤ |t|
          rw [abs_of_pos (by linarith)]; exact ht'),
        integral_Ici_eq_integral_Ioi]
    rw [hsplit]
    exact t1.add t2
  -- combine along the product filter
  have hcomb : Tendsto (fun p : ℝ × ℝ => ((∫ t in (-1)..(-p.1), F t / t * Complex.exp (I * t * x)) +
      ∫ t in p.1..1, F t / t * Complex.exp (I * t * x)) +
      ((∫ t in (-p.2)..(-1), F t / t * Complex.exp (I * t * x)) +
      ∫ t in (1 : ℝ)..p.2, F t / t * Complex.exp (I * t * x))) (𝓝[>] (0 : ℝ) ×ˢ atTop) (𝓝 (Alim + Blim)) :=
    (hA.comp tendsto_fst).add (hB.comp tendsto_snd)
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ atTop,
      ((∫ t in (-1)..(-p.1), F t / t * Complex.exp (I * t * x)) + ∫ t in p.1..1, F t / t * Complex.exp (I * t * x)) +
        ((∫ t in (-p.2)..(-1), F t / t * Complex.exp (I * t * x)) +
          ∫ t in (1 : ℝ)..p.2, F t / t * Complex.exp (I * t * x)) =
      ∫ t in {t : ℝ | p.1 < |t| ∧ |t| < p.2}, F t / t * Complex.exp (I * t * x) := by
    filter_upwards [prod_mem_prod (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)) (eventually_gt_atTop 1)]
      with p hp
    obtain ⟨⟨hε0, hε1⟩, hT0⟩ := hp
    have hT : 1 < p.2 := hT0
    have hfneg : ∀ a b : ℝ, a ≤ b → b < 0 →
        IntervalIntegrable (fun t : ℝ => F t / t * Complex.exp (I * t * x)) volume a b := fun a b hab hb =>
      ((continuousOn_Fdiv_neg hζ).mul hec.continuousOn).mono (fun t ht => by
        rw [Set.uIcc_of_le hab] at ht; exact lt_of_le_of_lt ht.2 hb) |>.intervalIntegrable
    have hfpos : ∀ a b : ℝ, 0 < a → a ≤ b →
        IntervalIntegrable (fun t : ℝ => F t / t * Complex.exp (I * t * x)) volume a b := fun a b ha hab =>
      ((continuousOn_Fdiv_pos hζ).mul hec.continuousOn).mono (fun t ht => by
        rw [Set.uIcc_of_le hab] at ht; exact lt_of_lt_of_le ha ht.1) |>.intervalIntegrable
    have e1 := intervalIntegral.integral_add_adjacent_intervals (hfneg (-p.2) (-1) (by linarith) (by linarith))
      (hfneg (-1) (-p.1) (by linarith) (by linarith))
    have e2 := intervalIntegral.integral_add_adjacent_intervals (hfpos p.1 1 hε0 hε1.le)
      (hfpos 1 p.2 one_pos hT.le)
    rw [shell_eq hε0 (by linarith) (hfneg _ _ (by linarith) (by linarith)) (hfpos _ _ hε0 (by linarith)),
      ← e1, ← e2]
    abel
  have hfinal := tendsto_nhds_unique (hcomb.congr' hev) hPV
  rw [hAlim, hBlim] at hfinal
  linear_combination -hfinal

theorem eq_sum_specProj {S : Type*} [Fintype S] [DecidableEq S] {H : Op S} (hH : IsSelfAdjoint H) (A : Op S) :
    A = ∑ E ∈ specFinset H, ∑ E' ∈ specFinset H, specProj H E * A * specProj H E' := by
  calc A = (∑ E ∈ specFinset H, specProj H E) * A * (∑ E' ∈ specFinset H, specProj H E') := by
        rw [sum_specProj hH, one_mul, mul_one]
    _ = _ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun E _ => ?_
        rw [Finset.mul_sum]

theorem specProj_comm_mul {S : Type*} [Fintype S] [DecidableEq S] {H : Op S} (hH : IsSelfAdjoint H) (A : Op S)
    (E E' : ℝ) : specProj H E * ((I : ℂ) • (H * A - A * H)) * specProj H E' =
      (I * ((E - E' : ℝ) : ℂ)) • (specProj H E * A * specProj H E') := by
  have e1 : specProj H E * ((I : ℂ) • (H * A - A * H)) * specProj H E' =
      (I : ℂ) • ((specProj H E * H) * A * specProj H E' - specProj H E * A * (H * specProj H E')) := by
    rw [mul_smul_comm, smul_mul_assoc]; congr 1; noncomm_ring
  rw [e1, specProj_mul hH, mul_specProj hH, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, ← sub_smul, smul_smul]
  push_cast
  ring_nf

theorem dyn_comm_eq_sum {S : Type*} [Fintype S] [DecidableEq S] {H : Op S} (hH : IsSelfAdjoint H) (u : ℝ) (A : Op S) :
    dyn H u ((I : ℂ) • (H * A - A * H)) = ∑ E ∈ specFinset H, ∑ E' ∈ specFinset H,
      Complex.exp (I * (u : ℂ) * ((E - E' : ℝ) : ℂ)) • ((I * ((E - E' : ℝ) : ℂ)) • (specProj H E * A * specProj H E')) := by
  rw [dyn_eq_sum hH]
  refine Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun E' _ => ?_
  rw [specProj_comm_mul hH]

end TimeRepDevices

/-- **Lemma 5.10**: "`and for every operator $A$ on $\Fock$`"
"`\Qf(A)=\bigl(\tfrac12+c_F\bigr)A+\int_{\abs t\ge1}\frac{F(t)}t\,\tau_t(A)\,\dd t+\int_{-1}^1G(u)\,\tau_u\bigl(\iu[H_N,A]\bigr)\,\dd u,`"
— for any self-adjoint `H` on any `Op S`; "`The same holds on $\FockS$ with $\Hhat_N$.`" is the case `S = Slot δ₀ T`. -/
theorem clusterFilter_eq_timeRep (hζ : ClusterParams Δ γ δ ζ) {S : Type*} [Fintype S] [DecidableEq S] {H : Op S}
    (hH : IsSelfAdjoint H) (A : Op S) :
    clusterFilter (gClust γ ζ) H A =
      ((1 / 2 : ℂ) + cF (Fclust γ ζ)) • A +
        opIntegralOn {t : ℝ | 1 ≤ |t|} (fun t => (Fclust γ ζ t / t) • dyn H t A) +
        opIntegralOn (Set.Ioo (-1) 1) (fun u => Gclust (Fclust γ ζ) u • dyn H u ((I : ℂ) • (H * A - A * H))) := by
  ext m m'
  have hAmm : A m m' = ∑ E ∈ specFinset H, ∑ E' ∈ specFinset H, (specProj H E * A * specProj H E') m m' := by
    conv_lhs => rw [eq_sum_specProj hH A]
    simp only [Matrix.sum_apply]
  simp only [clusterFilter, opIntegralOn, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.sum_apply,
    smul_eq_mul]
  rw [hAmm]
  simp_rw [dyn_comm_eq_sum hH, dyn_eq_sum hH]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  have i1 : ∀ E E' : ℝ, Integrable (fun t : ℝ => Fclust γ ζ t / t *
      (Complex.exp (I * (t : ℂ) * ((E - E' : ℝ) : ℂ)) * (specProj H E * A * specProj H E') m m'))
      (volume.restrict {t : ℝ | 1 ≤ |t|}) := by
    intro E E'
    have h := (integrableOn_F1_mul_exp hζ (E - E')).mul_const ((specProj H E * A * specProj H E') m m')
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only
    ring
  have i2 : ∀ E E' : ℝ, Integrable (fun u : ℝ => Gclust (Fclust γ ζ) u *
      (Complex.exp (I * (u : ℂ) * ((E - E' : ℝ) : ℂ)) *
        ((I * ((E - E' : ℝ) : ℂ)) * (specProj H E * A * specProj H E') m m')))
      (volume.restrict (Set.Ioo (-1) 1)) := by
    intro E E'
    have h := ((integrable_Gclust_mul_exp hζ (E - E')).mul_const
      ((I * ((E - E' : ℝ) : ℂ)) * (specProj H E * A * specProj H E') m m')).integrableOn (s := Set.Ioo (-1) 1)
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only
    ring
  rw [integral_finsetSum _ fun E _ => integrable_finsetSum _ fun E' _ => i1 E E',
    integral_finsetSum _ fun E _ => integrable_finsetSum _ fun E' _ => i2 E E', ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [integral_finsetSum _ fun E' _ => i1 E E', integral_finsetSum _ fun E' _ => i2 E E',
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun E' _ => ?_
  have hs := gClust_timeRep_scalar hζ (E - E')
  have e1 : ∫ t in {t : ℝ | 1 ≤ |t|}, Fclust γ ζ t / t *
      (Complex.exp (I * (t : ℂ) * ((E - E' : ℝ) : ℂ)) * (specProj H E * A * specProj H E') m m') =
      (∫ t in {t : ℝ | 1 ≤ |t|}, Fclust γ ζ t / t * Complex.exp (I * t * ((E - E' : ℝ) : ℂ))) *
        (specProj H E * A * specProj H E') m m' := by
    rw [← integral_mul_const]; congr 1; funext t; ring
  have e2 : ∫ u in Set.Ioo (-1) 1, Gclust (Fclust γ ζ) u *
      (Complex.exp (I * (u : ℂ) * ((E - E' : ℝ) : ℂ)) *
        ((I * ((E - E' : ℝ) : ℂ)) * (specProj H E * A * specProj H E') m m')) =
      (∫ u in Set.Ioo (-1) 1, Gclust (Fclust γ ζ) u * Complex.exp (I * u * ((E - E' : ℝ) : ℂ))) *
        ((I * ((E - E' : ℝ) : ℂ)) * (specProj H E * A * specProj H E') m m') := by
    rw [← integral_mul_const]; congr 1; funext u; ring
  rw [e1, e2, hs]
  ring

/-- **Lemma 5.10**: "`Here $\abs{G(u)}\le\norm F_\infty\log(1/\abs u)$`". -/
theorem norm_Gclust_le (hζ : ClusterParams Δ γ δ ζ) {u : ℝ} (hu : 0 < |u|) (hu1 : |u| < 1) :
    ‖Gclust (Fclust γ ζ) u‖ ≤ supNorm (Fclust γ ζ) * Real.log (1 / |u|) := by
  set S := supNorm (Fclust γ ζ) with hS
  rcases lt_or_gt_of_ne (abs_pos.mp hu) with h | h
  · have hu' : -1 < u ∧ u < 0 := ⟨by rw [abs_of_neg h] at hu1; linarith, h⟩
    have hn : ¬ (0 < u ∧ u < 1) := fun h' => absurd h'.1 (not_lt.mpr h.le)
    rw [Gclust, ite_eq_right hn, ite_eq_left hu', norm_neg, abs_of_neg h]
    have hle : (-1 : ℝ) ≤ u := hu'.1.le
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun t => S * (-t)⁻¹) hle ?_ ?_).trans ?_
    · refine Eventually.of_forall fun t ht => ?_
      have ht0 : t < 0 := lt_of_le_of_lt ht.2 h
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (norm_le_supNorm hζ t) (inv_nonneg.mpr (by linarith))
    · refine ContinuousOn.intervalIntegrable ?_
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      have hx0 : -x ≠ 0 := by linarith [hx.2]
      exact (continuousAt_const.mul (continuous_neg.continuousAt.inv₀ hx0)).continuousWithinAt
    · rw [intervalIntegral.integral_const_mul]
      have e : (fun t : ℝ => (-t)⁻¹) = fun t => -t⁻¹ := funext fun t => by rw [inv_neg]
      rw [e, intervalIntegral.integral_neg, integral_inv_of_neg (by norm_num) h, div_neg, div_one, one_div,
        Real.log_inv]
  · have hu' : 0 < u ∧ u < 1 := ⟨h, by rw [abs_of_pos h] at hu1; exact hu1⟩
    rw [Gclust, ite_eq_left hu', abs_of_pos h]
    have hle : u ≤ 1 := hu'.2.le
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun t => S * t⁻¹) hle ?_ ?_).trans ?_
    · refine Eventually.of_forall fun t ht => ?_
      have ht0 : 0 < t := lt_trans h ht.1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (norm_le_supNorm hζ t) (inv_nonneg.mpr ht0.le)
    · refine ContinuousOn.intervalIntegrable ?_
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      exact (continuousAt_const.mul (continuousAt_id.inv₀ hx0)).continuousWithinAt
    · rw [intervalIntegral.integral_const_mul, integral_inv_of_pos h one_pos]

/-- **Lemma 5.10**: "`so both filters on the right have finite moments of all orders`" — `F(t)/t` on `|t| ≥ 1` (`0`
otherwise; Proposition 5.11's `F_1`) and `G` (extended by `0`; `G_1`). -/
theorem hasFiniteMoments_timeRep (hζ : ClusterParams Δ γ δ ζ) :
    HasFiniteMoments (fun t => if 1 ≤ |t| then Fclust γ ζ t / t else 0) ∧
      HasFiniteMoments (Gclust (Fclust γ ζ)) := by
  exact ⟨hasFiniteMoments_F1 hζ, hasFiniteMoments_G hζ⟩

/-- **Lemma 5.10**: "`and $\norm{\Qf(A)}\le C(1+\norm{H_N})\norm A$ with $C$ depending only on $\zeta$ and $\gamma$`" — `C`
after `γ`, `ζ` and before the space, `H` and `A`. -/
theorem norm_clusterFilter_le (hζ : ClusterParams Δ γ δ ζ) :
    ∃ C : ℝ, ∀ (S : Type) [Fintype S] [DecidableEq S] (H : Op S), IsSelfAdjoint H → ∀ A : Op S,
      ‖opCLM (clusterFilter (gClust γ ζ) H A)‖ ≤ C * (1 + ‖opCLM H‖) * ‖opCLM A‖ := by
  have hF1 := (hasFiniteMoments_timeRep hζ).1.1
  have hG := (hasFiniteMoments_timeRep hζ).2.1
  have hD1 : MeasurableSet {t : ℝ | 1 ≤ |t|} := measurableSet_le measurable_const continuous_abs.measurable
  set M1 := ∫ t in {t : ℝ | 1 ≤ |t|}, ‖Fclust γ ζ t / t‖ with hM1def
  set MG := ∫ u in Set.Ioo (-1 : ℝ) 1, ‖Gclust (Fclust γ ζ) u‖ with hMGdef
  set c0 := ‖(1 / 2 : ℂ) + cF (Fclust γ ζ)‖ with hc0def
  have hM1 : 0 ≤ M1 := setIntegral_nonneg hD1 fun t _ => norm_nonneg _
  have hMG : 0 ≤ MG := setIntegral_nonneg measurableSet_Ioo fun t _ => norm_nonneg _
  have hc0 : 0 ≤ c0 := norm_nonneg _
  refine ⟨c0 + M1 + 2 * MG, fun S _ _ H hH A => ?_⟩
  rw [clusterFilter_eq_timeRep hζ hH A, opCLM_add', opCLM_add', opCLM_smul']
  have b1 : ‖opCLM (opIntegralOn {t : ℝ | 1 ≤ |t|} (fun t => (Fclust γ ζ t / t) • dyn H t A))‖ ≤
      M1 * ‖opCLM A‖ := by
    have hint : ∀ m m', IntegrableOn (fun t => ((Fclust γ ζ t / t) • dyn H t A) m m') {t : ℝ | 1 ≤ |t|} := by
      intro m m'
      have h := integrable_entry_smul hF1 (continuous_opCLM_dyn H A) (fun t => (norm_dyn hH t A).le)
        {t : ℝ | 1 ≤ |t|} m m'
      refine h.congr_fun (fun t ht => ?_) hD1
      have ht' : 1 ≤ |t| := ht
      simp only [ite_eq_left ht']
    refine (norm_opIntegralOn_le _ _ hint).trans (le_of_eq ?_)
    rw [hM1def, ← integral_mul_const]
    refine setIntegral_congr_fun hD1 fun t _ => ?_
    rw [opCLM_smul', norm_smul, norm_dyn hH]
  have b2 : ‖opCLM (opIntegralOn (Set.Ioo (-1) 1)
      (fun u => Gclust (Fclust γ ζ) u • dyn H u ((I : ℂ) • (H * A - A * H))))‖ ≤
      MG * (2 * ‖opCLM H‖ * ‖opCLM A‖) := by
    have hint : ∀ m m', IntegrableOn (fun u => (Gclust (Fclust γ ζ) u • dyn H u ((I : ℂ) • (H * A - A * H))) m m')
        (Set.Ioo (-1) 1) :=
      fun m m' => integrable_entry_smul hG (continuous_opCLM_dyn H _) (fun t => (norm_dyn hH t _).le) _ m m'
    refine (norm_opIntegralOn_le _ _ hint).trans ?_
    have hc : ‖opCLM ((I : ℂ) • (H * A - A * H))‖ ≤ 2 * ‖opCLM H‖ * ‖opCLM A‖ := by
      rw [opCLM_smul', norm_smul, Complex.norm_I, one_mul]; exact norm_comm_le H A
    calc ∫ u in Set.Ioo (-1 : ℝ) 1, ‖opCLM (Gclust (Fclust γ ζ) u • dyn H u ((I : ℂ) • (H * A - A * H)))‖
        = ∫ u in Set.Ioo (-1 : ℝ) 1, ‖Gclust (Fclust γ ζ) u‖ * ‖opCLM ((I : ℂ) • (H * A - A * H))‖ := by
          refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
          rw [opCLM_smul', norm_smul, norm_dyn hH]
      _ = MG * ‖opCLM ((I : ℂ) • (H * A - A * H))‖ := integral_mul_const _ _
      _ ≤ MG * (2 * ‖opCLM H‖ * ‖opCLM A‖) := mul_le_mul_of_nonneg_left hc hMG
  have hA0 := norm_nonneg (opCLM A)
  have hH0 := norm_nonneg (opCLM H)
  calc ‖((1 / 2 : ℂ) + cF (Fclust γ ζ)) • opCLM A +
        opCLM (opIntegralOn {t : ℝ | 1 ≤ |t|} (fun t => (Fclust γ ζ t / t) • dyn H t A)) +
        opCLM (opIntegralOn (Set.Ioo (-1) 1)
          (fun u => Gclust (Fclust γ ζ) u • dyn H u ((I : ℂ) • (H * A - A * H))))‖
      ≤ ‖((1 / 2 : ℂ) + cF (Fclust γ ζ)) • opCLM A‖ +
          ‖opCLM (opIntegralOn {t : ℝ | 1 ≤ |t|} (fun t => (Fclust γ ζ t / t) • dyn H t A))‖ +
          ‖opCLM (opIntegralOn (Set.Ioo (-1) 1)
            (fun u => Gclust (Fclust γ ζ) u • dyn H u ((I : ℂ) • (H * A - A * H))))‖ := norm_add₃_le
    _ ≤ c0 * ‖opCLM A‖ + M1 * ‖opCLM A‖ + MG * (2 * ‖opCLM H‖ * ‖opCLM A‖) :=
        add_le_add (add_le_add (le_of_eq (norm_smul _ _)) b1) b2
    _ ≤ (c0 + M1 + 2 * MG) * (1 + ‖opCLM H‖) * ‖opCLM A‖ := by
        have e : (c0 + M1 + 2 * MG) * (1 + ‖opCLM H‖) * ‖opCLM A‖ -
            (c0 * ‖opCLM A‖ + M1 * ‖opCLM A‖ + MG * (2 * ‖opCLM H‖ * ‖opCLM A‖)) =
            2 * MG * ‖opCLM A‖ + c0 * ‖opCLM H‖ * ‖opCLM A‖ + M1 * ‖opCLM H‖ * ‖opCLM A‖ := by ring
        have : 0 ≤ 2 * MG * ‖opCLM A‖ + c0 * ‖opCLM H‖ * ‖opCLM A‖ + M1 * ‖opCLM H‖ * ‖opCLM A‖ :=
          add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hMG) hA0) (mul_nonneg (mul_nonneg hc0 hH0) hA0))
            (mul_nonneg (mul_nonneg hM1 hH0) hA0)
        linarith

end TimeRep

/-! ## Proposition 5.11 (locality of the clustering filter) -/

/-! ### Proof devices for Proposition 5.11 (phase (b); not statements of the paper)

`𝒜𝒮` bounds are invariant under changing the sequence off `𝒩` (`asBound_congr`) and scale under `a •` (`asBound_smul`);
the operator integrals over `{|t| ≥ 1}` and `(−1, 1)` of Lemma 5.10 are integrals over `ℝ` of the filters `F_1`
(`F(t)/t` on `|t| ≥ 1`, `0` otherwise) and `G_1 = G` (zero off `(−1, 1)`), the form Lemma 5.6 takes. -/

theorem asBound_congr {η : ℝ → ℝ} {δ₀ : ℝ} {Ts : TorusSeq δ₀} {X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))}
    {A B : (N : ℕ) → FockOp (Ts.T N)} {e : ℝ} {C : ℕ → ℝ} (h : ASBound η δ₀ Ts X A e C)
    (hAB : ∀ N ∈ Ts.idx, A N = B N) : ASBound η δ₀ Ts X B e C := by
  refine ⟨h.1, fun k N hN r hr => ?_⟩
  rw [← hAB N hN]
  exact h.2 k N hN r hr

theorem asBound_smul {η : ℝ → ℝ} (hη : IsProfile η) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {Ts : TorusSeq δ₀}
    {X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))} {A : (N : ℕ) → FockOp (Ts.T N)} {e : ℝ} {C : ℕ → ℝ}
    (h : ASBound η δ₀ Ts X A e C) (a : ℂ) :
    ASBound η δ₀ Ts X (fun N => a • A N) e (fun k => ‖a‖ * C k) := by
  refine ⟨h.1, fun k N hN r hr => ?_⟩
  obtain ⟨A', hA', hb⟩ := h.2 k N hN r hr
  have hT := Ts.admissible N hN
  refine ⟨a • A', ⟨(CAR _).smul_mem hA'.1 a, hA'.2.smul_left a⟩, ?_⟩
  rw [iota_smul hη hδ₀ hT, ← smul_sub, opCLM_smul', norm_smul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by rw [← mul_assoc]; exact hb) (norm_nonneg _)

section OpInt

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem opIntegralOn_eq_univ_indicator {D : Set ℝ} (hD : MeasurableSet D) (f : ℝ → ℂ) (X : ℝ → Op S) :
    opIntegralOn D (fun t => f t • X t) = opIntegralOn Set.univ (fun t => D.indicator f t • X t) := by
  ext m m'
  simp only [opIntegralOn, Matrix.of_apply, Measure.restrict_univ]
  rw [← integral_indicator hD]
  congr 1; funext t
  by_cases ht : t ∈ D
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_smul, Matrix.zero_apply]

theorem opIntegralOn_eq_univ_of_zero {D : Set ℝ} (f : ℝ → ℂ) (hf : ∀ t, t ∉ D → f t = 0) (X : ℝ → Op S) :
    opIntegralOn D (fun t => f t • X t) = opIntegralOn Set.univ (fun t => f t • X t) := by
  ext m m'
  simp only [opIntegralOn, Matrix.of_apply, Measure.restrict_univ]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
  rw [hf t ht, zero_smul, Matrix.zero_apply]

end OpInt

/-- **Proposition 5.11**: "`If $A=(A_N)\in\AS_X$ is even, with prefactor exponent $m$ and $\norm{A_N}\le CN^{m'}$, and $\abs{X_N}\le CN^{m''}$, then $(\Qf(A_N))_N\in\AS_X$ with prefactor exponent $1+\max\{m,m'\}+m''$, and $\norm{\Qf(A_N)}\le CN^{1+m'}$.`"
— `𝒬` on `𝔉` with `H_N`; `m'' ≥ 0`; the new constants after `δ₀`, the filter data, `C`, the exponents, the constants
of `A`, `C_h`, `C^H`. "`No spectral assumption on $H$ is used.`" is a remark: there is no hypothesis on the spectrum. -/
theorem almostSupported_clusterFilter {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {Δ γ δ : ℝ} {ζ : ℝ → ℝ}
    (hζ : ClusterParams Δ γ δ ζ) (C m m' m'' : ℝ) (hm'' : 0 ≤ m'') (CA : ℕ → ℝ) (Ch : ℝ) (CH : ℕ → ℝ) :
    ∃ (C'k : ℕ → ℝ) (C' : ℝ), ∀ (η : ℝ → ℝ), IsProfile η → ∀ (Ts : TorusSeq δ₀)
      (H : (N : ℕ) → FockOp (Ts.T N)) (d : H1Data η δ₀ Ts H), d.Ch = Ch → d.CH = CH →
      ∀ (X : (N : ℕ) → Finset (Slot δ₀ (Ts.T N))) (A : (N : ℕ) → FockOp (Ts.T N)),
        (∀ N ∈ Ts.idx, IsEven (A N)) → ASBound η δ₀ Ts X A m CA →
        (∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (A N)‖ ≤ C * (N : ℝ) ^ m') →
        (∀ N ∈ Ts.idx, ((X N).card : ℝ) ≤ C * (N : ℝ) ^ m'') →
          ASBound η δ₀ Ts X (fun N => clusterFilter (gClust γ ζ) (H N) (A N)) (1 + max m m' + m'') C'k ∧
            ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) (clusterFilter (gClust γ ζ) (H N) (A N))‖ ≤ C' * (N : ℝ) ^ (1 + m') := by
  set F1 : ℝ → ℂ := fun t => if 1 ≤ |t| then Fclust γ ζ t / t else 0 with hF1
  set G1 : ℝ → ℂ := Gclust (Fclust γ ζ) with hG1
  have hmom := hasFiniteMoments_timeRep hζ
  set cc : ℂ := (1 / 2 : ℂ) + cF (Fclust γ ζ) with hcc
  -- Lemma 5.6 for `F_1`
  obtain ⟨C1, hC1⟩ := almostSupported_timeFilter hδ₀ hmom.1 C m m' m'' hm'' CA Ch CH
  -- Lemma 5.7 for `i[H, A]`
  obtain ⟨C7, hC7⟩ := almostSupported_comm_HN hδ₀ C m m' CA Ch CH
  -- Lemma 5.6 for `G_1` applied to `i[H, A]`
  set CB : ℝ := 8 * π * |Ch| * |C| + |C| with hCB
  obtain ⟨C2, hC2⟩ := almostSupported_timeFilter hδ₀ hmom.2 CB (1 + max m m') (1 + m') m'' hm'' C7 Ch CH
  -- the norm bound
  obtain ⟨CQ, hCQ⟩ := norm_clusterFilter_le hζ
  refine ⟨fun k => |(|‖cc‖ * CA k| + |C1 k|)| + |C2 k|, |CQ| * (1 + 4 * π * |Ch|) * |C|, ?_⟩
  intro η hη Ts H d hCh hCH X A hAe hAS hAn hXc
  have hm0 : 0 ≤ m := hAS.1
  have hHsa := d.H_isSelfAdjoint
  -- the three pieces
  have h0 := asBound_smul hη hδ₀ hAS cc
  have h1 := hC1 η hη Ts H d hCh hCH X A hAe hAS hAn hXc
  have h7 := hC7 η hη Ts H d hCh hCH X A hAe hAS hAn
  have hBe : ∀ N ∈ Ts.idx, IsEven ((I : ℂ) • (H N * A N - A N * H N)) := fun N hN =>
    (((isEven_H d hN).mul_left (hAe N hN)).sub_left ((hAe N hN).mul_left (isEven_H d hN))).smul_left I
  have hBn : ∀ N ∈ Ts.idx, ‖toCLM (Ts.T N) ((I : ℂ) • (H N * A N - A N * H N))‖ ≤ CB * (N : ℝ) ^ (1 + m') := by
    intro N hN
    have hN1 := one_le_of_mem_idx Ts hN
    have hNpos : (0 : ℝ) < N := by linarith
    have hHn := (norm_HN_le_of_H1 d N hN)
    rw [hHn.2, hCh] at hHn
    have hHn' : ‖toCLM (Ts.T N) (H N)‖ ≤ 4 * π * |Ch| * N := by
      have := hHn.1
      have h2 : 4 * π * Ch * N ≤ 4 * π * |Ch| * N := by
        have : (0 : ℝ) ≤ 4 * π * N := by positivity
        nlinarith [le_abs_self Ch]
      linarith
    have hAn' : ‖toCLM (Ts.T N) (A N)‖ ≤ |C| * (N : ℝ) ^ m' :=
      (hAn N hN).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    show ‖opCLM ((I : ℂ) • (H N * A N - A N * H N))‖ ≤ CB * (N : ℝ) ^ (1 + m')
    rw [opCLM_smul', norm_smul, Complex.norm_I, one_mul]
    have hc := norm_comm_le (H N) (A N)
    have hpow : (N : ℝ) ^ (1 + m') = N * N ^ m' := by
      rw [Real.rpow_add hNpos, Real.rpow_one]
    calc ‖opCLM (H N * A N - A N * H N)‖ ≤ 2 * ‖opCLM (H N)‖ * ‖opCLM (A N)‖ := hc
      _ ≤ 2 * (4 * π * |Ch| * N) * (|C| * (N : ℝ) ^ m') := by
          have h1 : ‖opCLM (H N)‖ ≤ 4 * π * |Ch| * N := hHn'
          have h2 : ‖opCLM (A N)‖ ≤ |C| * (N : ℝ) ^ m' := hAn'
          gcongr
      _ = 8 * π * |Ch| * |C| * (N * N ^ m') := by ring
      _ ≤ CB * (N : ℝ) ^ (1 + m') := by
          rw [hpow, hCB]
          have : 0 ≤ |C| * (N * N ^ m') := by positivity
          nlinarith
  have hXc' : ∀ N ∈ Ts.idx, ((X N).card : ℝ) ≤ CB * (N : ℝ) ^ m'' := by
    intro N hN
    have hN1 := one_le_of_mem_idx Ts hN
    refine (hXc N hN).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have : 0 ≤ 8 * π * |Ch| * |C| := by positivity
    rw [hCB]; linarith [le_abs_self C]
  have h2 := hC2 η hη Ts H d hCh hCH X (fun N => (I : ℂ) • (H N * A N - A N * H N)) hBe h7 hBn hXc'
  have hmax : max (1 + max m m') (1 + m') = 1 + max m m' := max_eq_left (by linarith [le_max_right m m'])
  rw [hmax] at h2
  -- combine
  have h01 := asBound_add hη hδ₀ h0 h1
  have h012 := asBound_add hη hδ₀ h01 h2
  have he : max (max m (max m m' + m'')) (1 + max m m' + m'') = 1 + max m m' + m'' := by
    refine max_eq_right (max_le ?_ ?_)
    · linarith [le_max_left m m']
    · linarith
  rw [he] at h012
  refine ⟨asBound_congr h012 fun N hN => ?_, fun N hN => ?_⟩
  · rw [clusterFilter_eq_timeRep hζ (hHsa N hN) (A N),
      opIntegralOn_eq_univ_indicator (measurableSet_le measurable_const continuous_abs.measurable),
      opIntegralOn_eq_univ_of_zero (D := Set.Ioo (-1) 1) _ (fun t ht => by
        simp only [Gclust]
        have h1 : ¬ (0 < t ∧ t < 1) := fun h => ht ⟨by linarith [h.1], h.2⟩
        have h2 : ¬ (-1 < t ∧ t < 0) := fun h => ht ⟨h.1, by linarith [h.2]⟩
        rw [ite_eq_right h1, ite_eq_right h2])]
    have hind : ({t : ℝ | 1 ≤ |t|}.indicator fun t => Fclust γ ζ t / t) = F1 := by
      funext t
      simp only [hF1, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hind]
  · have hN1 := one_le_of_mem_idx Ts hN
    have hNpos : (0 : ℝ) < N := by linarith
    have hq := hCQ _ (H N) (hHsa N hN) (A N)
    have hHn := norm_HN_le_of_H1 d N hN
    rw [hHn.2, hCh] at hHn
    have hHn' : ‖opCLM (H N)‖ ≤ 4 * π * |Ch| * N := by
      have := hHn.1
      have h2 : 4 * π * Ch * N ≤ 4 * π * |Ch| * N := by
        have : (0 : ℝ) ≤ 4 * π * N := by positivity
        nlinarith [le_abs_self Ch]
      exact this.trans h2
    have hAn' : ‖opCLM (A N)‖ ≤ |C| * (N : ℝ) ^ m' :=
      (hAn N hN).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    show ‖opCLM (clusterFilter (gClust γ ζ) (H N) (A N))‖ ≤ |CQ| * (1 + 4 * π * |Ch|) * |C| * (N : ℝ) ^ (1 + m')
    have hpow : (N : ℝ) ^ (1 + m') = N * N ^ m' := by rw [Real.rpow_add hNpos, Real.rpow_one]
    calc ‖opCLM (clusterFilter (gClust γ ζ) (H N) (A N))‖ ≤ CQ * (1 + ‖opCLM (H N)‖) * ‖opCLM (A N)‖ := hq
      _ ≤ |CQ| * (1 + ‖opCLM (H N)‖) * ‖opCLM (A N)‖ := by
          gcongr
          exact le_abs_self CQ
      _ ≤ |CQ| * ((1 + 4 * π * |Ch|) * N) * (|C| * (N : ℝ) ^ m') := by
          have h3 : 1 + ‖opCLM (H N)‖ ≤ (1 + 4 * π * |Ch|) * N := by
            have : (0 : ℝ) ≤ 4 * π * |Ch| := by positivity
            nlinarith
          gcongr
      _ = |CQ| * (1 + 4 * π * |Ch|) * |C| * (N * N ^ m') := by ring
      _ = _ := by rw [hpow]

end HRTorus.Locality
