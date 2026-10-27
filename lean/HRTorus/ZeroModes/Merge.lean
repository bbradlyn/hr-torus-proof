import HRTorus.ZeroModes.Spaces

/-!
# The merge and the induction: Lemmas C.C and C.D, Propositions C.induct and C.base, Corollary C.bounds (T-0056 stage F, block F1-upper, `ZeroModes.Merge`)

Written by Claude Opus 5.5 (an AI model; recruit L18), 2026-10-26. **Statement phase and proof phase (2026-10-26): the
definitions and statements were written first, every theorem that carries content `sorry`, and reviewed against the
paper before any proof; the proof phase (round two) then proved every statement, the reviewed text unchanged. The
proof devices — the declarations named `_dev`, in marked sections — are not statements of the paper. The linearity
of the merge (part of the definition of `muL`) and one conjunction are written out.**
The paper: the HR paper, `papers/hr/appendices/C-kernel.tex` — Lemma C.`C` (`kz:lem:C`) (a)–(d), Lemma C.`D`
(`kz:lem:D`), Propositions C.`induct` (`kz:prop:induct`) and C.`base` (`kz:prop:base`), Corollary C.`bounds`
(`kz:cor:bounds`). Not here: Lemma C.C(e), the budget remark (it rests on Lemma C.theta(b), the general zero count,
out of the block's scope by the stage-F scouting pilot's finding).

## The model

* **Indices.** The merge goes from the sector `(n + 1, m + 1)` to `(n, m)` (the paper's `n, m ≥ 1` to `n − 1, m − 1`);
  it merges the first up and the first down variable, `x_1 = y_1 = w`. The other variables, the paper's `rest`, are
  `r : Fin (n + m) → ℂ`, up block first; `mergePt w r` is the point of `M = {x_1 = y_1}` with those coordinates.
* **The merged numerator** (`kz:eq:merge`, `𝖺|_M = ϑ₁'(0)² E J'² 𝒜`): for `a ∈ Gnum τ (n+1) (m+1) ε` and an admissible
  centre `w ∉ rest + Λ_u` (where `E(w; rest) = ∏_{z ∈ rest} ϑ₁(w − z)⁴ ≠ 0`), `mergeAt τ a w r := 𝖺|_M/(ϑ₁'(0)² E)`,
  which is `J'² 𝒜` — the numerator of the paper's `μ(g) = 𝒜`. `μ(a)(r) := mergeAt τ a (admW τ r) r`, with
  `admW τ r` an admissible centre chosen by Hilbert's ε-operator (`admW_spec_dev`); by (c) any admissible centre gives
  the same value, at every `rest`, generic or not (generic `rest` by Liouville, the others by continuity: the admissible
  pairs `(w, rest)` form an open set and generic `rest` are dense).
* **(a) in numerator form** is the statement that `w ↦ mergeAt τ a w r` extends from the admissible centres to an entire
  function, for `rest` off its up–down divisors; at same-spin coincidences of `rest`, `𝖺|_M ≡ 0` in `w`.
* **(c)** is split into the independence of the admissible centre (`lemC_c_indep`) and the vanishing for `ε² ≠ 1`
  (`lemC_c_zero`); **(d)** is the membership `mu τ a ∈ Gnum τ n m ε`, and `muL` is `μ` as a linear map.
* **Lemma C.D(b)** in numerator form: "`g` is constant" is `a = c J²`.
* **Dimensions** (Trap 1 of the brief): every dimension statement about `Gnum` carries its `FiniteDimensional`, proved
  along the induction from the base cases through the injective merges; equalities to spans are stated where the paper
  names the spanning functions, with the numerators of `℘(x_1 − y_1)` and `℘_ε(x_1 − y_1)` as F1-lower's `dEps … 1`
  (`dEps_one`) and the constant `g = 1` as `J²`.
* **Multipliers** `ε ∈ ℂ × ℂ` as in `ZeroModes.Spaces`; the paper's `ε² = 1` is `ε₁² = 1 ∧ ε₂² = 1`, which with `ε ∈ ℂ × ℂ` means
  `ε ∈ {±1}²`, i.e. `ε = Eps.pair e` for one of the four `e : Eps`.
-/

open Complex
open scoped Real UpperHalfPlane

noncomputable section

namespace HRTorus.ZeroModes

/-! ## The merge -/

/-- The point of `M` with common value `w` of `x_1, y_1` and the other variables `rest = r`: "`$\mathrm{rest}:=(x_2,\dots,x_n;y_2,\dots,y_m)$`",
"`$M:=\{x_1=y_1\}\cong\C^{N-1}$ with coordinate $w$ for the common value`". -/
def mergePt {n m : ℕ} (w : ℂ) (r : Fin (n + m) → ℂ) : Fin ((n + 1) + (m + 1)) → ℂ :=
  Fin.append (Fin.cons w (fun a : Fin n => r (Fin.castAdd m a)) : Fin (n + 1) → ℂ)
    (Fin.cons w (fun k : Fin m => r (Fin.natAdd n k)) : Fin (m + 1) → ℂ)

/-- `kz:eq:merge`: "`E(w;\mathrm{rest}):=\prod_{z\in\mathrm{rest}}\kzvth_1(w-z)^4`". -/
def Emerge (τ : ℂ) {K : ℕ} (w : ℂ) (r : Fin K → ℂ) : ℂ :=
  ∏ i, theta1 (w - r i) τ ^ 4

/-- The merged numerator at a centre `w`: `kz:eq:merge`, "`\mathsf a|_M=\kzvth_1'(0)^2\,E\,J'^2\,\mathcal A,`", solved for
`J'² 𝒜` — meaningful at the admissible centres `w ∉ rest + Λ_u`, where `E(w; rest) ≠ 0`. -/
def mergeAt (τ : ℍ) {n m : ℕ} (a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ) (w : ℂ) (r : Fin (n + m) → ℂ) : ℂ :=
  a (mergePt w r) / (deriv (fun z => theta1 z τ) 0 ^ 2 * Emerge τ w r)

/-- An admissible centre for `rest`, chosen by Hilbert's ε-operator: some `w` with `w − z ∉ Λ_u` for every `z` of `rest`
(the proof of Lemma C.C(d): "`Given a point of $\mathrm{rest}$-space, choose $w\notin\mathrm{rest}+\Lambda_u$; then $E\ne0$ there.`"). -/
def admW (τ : ℍ) {K : ℕ} (r : Fin K → ℂ) : ℂ :=
  Classical.epsilon fun w : ℂ => ∀ i, w - r i ∉ Λu τ

/-! ### Proof device for the merge (statement phase; not a statement of the paper): admissible centres exist
(`Λ_u` is countable, `rest + Λ_u` a countable union of countable sets) -/

theorem admW_spec_dev (τ : ℍ) {K : ℕ} (r : Fin K → ℂ) : ∀ i, admW τ r - r i ∉ Λu τ := by
  have hex : ∃ w : ℂ, ∀ i, w - r i ∉ Λu τ := by
    have hS : (⋃ i, (fun l => r i + l) '' Λu τ).Countable :=
      Set.countable_iUnion fun i => (Λu_countable_dev τ).image _
    obtain ⟨w, hw⟩ := (hS.dense_compl ℂ).nonempty
    exact ⟨w, fun i hi => hw (Set.mem_iUnion.2 ⟨i, ⟨w - r i, hi, add_sub_cancel (r i) w⟩⟩)⟩
  exact Classical.epsilon_spec hex

/-- **Lemma C.C(d)**: "`$\mu(g):=\mathcal A\in\kzG(n-1,m-1;\varepsilon)$`" — the merge in numerator form,
`μ(a)(rest) := J'²(rest) 𝒜(rest)`, the merged numerator at the admissible centre `admW τ rest` (Lemma C.C(c): any
admissible centre gives the same value). -/
def mu (τ : ℍ) {n m : ℕ} (a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ) : (Fin (n + m) → ℂ) → ℂ :=
  fun r => mergeAt τ a (admW τ r) r

/-! ### The several-variables toolkit (statement phase; proof devices, not statements of the paper)

What the proofs of Lemmas C.C and C.D need beyond F1-lower's devices, with no Hartogs, no joint analyticity and no
argument principle: (T1) the slice derivatives of a function of the Osgood class are jointly continuous (Cauchy's
formula on a circle in the `u_s`-plane, a parametric integral — the pattern of `D1_continuous_dev`); (T2) vanishing
along a divisor at the points of a dense set extends to the whole divisor (by (T1)); (T3) division by
`ϑ₁(u_s − u_t)^k` in the Osgood class (one-variable removable singularities in each slice; the converse of
`vanishes3_core_dev` — the statement phase planned F0's `divq2_isOsgood` pattern with a Cauchy estimate, and round two
proved it instead by the mean value on a circle kept off the divisor and by locally uniform limits, see the (T3) devices); (T4) the restriction to `M` of a function of the Osgood class is in the class in `rest` and
entire in `w` (the `w`-half is the pattern of `differentiable_osgood_merge_dev`); (T5) Liouville on `ℂ^N`, one variable
at a time (Mathlib's `Differentiable.apply_eq_apply_of_bounded`); (T7) the generic set — the complement of finitely
many families of translated coincidence divisors — is dense. ((T6), affine substitutions of a jointly differentiable
function, is composition — `differentiable_mergePt_dev` through F1-lower's two-variable `isOsgood2_differentiable_dev`;
`differentiable_of_isCanonShape_dev` is not used in this module.) -/

/-! ### Proof devices for (T1) (proof phase, round two; not statements of the paper)

Cauchy's formula for the `j`-th derivative on the unit circle about `u_s`
(`DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`) writes the slice derivative as a parametric interval
integral of a jointly continuous integrand — the pattern of F1-lower's `D1int_dev`, `D1int_continuous_dev`,
`D1_eq_integral_dev`, `D1_continuous_dev` (`ZeroModes.Explicit`, copied there from F0's `work/l15/lean/Osgood.lean`,
recruit L15), generalized from `j = 1` on `ℂ × ℂ` to every `j` on `Fin N → ℂ`. -/

/-- The integrand of Cauchy's formula for the `j`-th slice derivative along `u_s`, on the unit circle about `u_s`. -/
def sliceInt_dev {N : ℕ} (f : (Fin N → ℂ) → ℂ) (s : Fin N) (j : ℕ) (u : Fin N → ℂ) (θ : ℝ) : ℂ :=
  (circleMap 0 1 θ * I) * ((1 / (circleMap 0 1 θ) ^ (j + 1)) * f (Function.update u s (u s + circleMap 0 1 θ)))

theorem sliceInt_continuous_dev {N : ℕ} {f : (Fin N → ℂ) → ℂ} (hf : Continuous f) (s : Fin N) (j : ℕ) :
    Continuous (Function.uncurry (sliceInt_dev f s j)) := by
  have hc : Continuous fun θ : ℝ => circleMap 0 1 θ := continuous_circleMap 0 1
  have hne : ∀ θ : ℝ, circleMap 0 1 θ ^ (j + 1) ≠ 0 := fun θ => pow_ne_zero _ (circleMap_ne_center one_ne_zero)
  have hinv : Continuous fun θ : ℝ => 1 / circleMap 0 1 θ ^ (j + 1) := continuous_const.div (hc.pow _) hne
  have hf' : Continuous fun q : (Fin N → ℂ) × ℝ => f (Function.update q.1 s (q.1 s + circleMap 0 1 q.2)) :=
    hf.comp (continuous_fst.update s (((continuous_apply s).comp continuous_fst).add (hc.comp continuous_snd)))
  exact ((hc.comp continuous_snd).mul continuous_const).mul ((hinv.comp continuous_snd).mul hf')

theorem iteratedDeriv_slice_eq_integral_dev {N : ℕ} {f : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) (s : Fin N) (j : ℕ)
    (u : Fin N → ℂ) :
    (2 * π * I / (j.factorial : ℂ)) * iteratedDeriv j (fun z => f (Function.update u s z)) (u s) =
      ∫ θ in (0 : ℝ)..2 * π, sliceInt_dev f s j u θ := by
  have h := ((hf.2 u s).differentiableOn).circleIntegral_one_div_sub_center_pow_smul (c := u s) one_pos j
  unfold circleIntegral at h
  rw [← smul_eq_mul, ← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [sliceInt_dev, smul_eq_mul, deriv_circleMap, circleMap_sub_center]
  congr 3
  simp [circleMap]

theorem continuous_iteratedDeriv_slice_dev {N : ℕ} {f : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) (s : Fin N) (j : ℕ) :
    Continuous fun u : Fin N → ℂ => iteratedDeriv j (fun z => f (Function.update u s z)) (u s) := by
  have hI : Continuous fun u : Fin N → ℂ => ∫ θ in (0 : ℝ)..2 * π, sliceInt_dev f s j u θ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (sliceInt_continuous_dev hf.1 s j) _ _
  have hc : (2 * π * I / (j.factorial : ℂ)) ≠ 0 :=
    div_ne_zero two_pi_I_ne_zero (by exact_mod_cast j.factorial_ne_zero)
  have e : (fun u : Fin N → ℂ => iteratedDeriv j (fun z => f (Function.update u s z)) (u s)) =
      fun u => (2 * π * I / (j.factorial : ℂ))⁻¹ * ∫ θ in (0 : ℝ)..2 * π, sliceInt_dev f s j u θ := by
    funext u
    rw [← iteratedDeriv_slice_eq_integral_dev hf s j u, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [e]
  exact continuous_const.mul hI

theorem vanishesAlong_of_dense_dev (τ : ℍ) {N : ℕ} {f : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) (s t : Fin N) (k : ℕ)
    {S : Set (Fin N → ℂ)} (hS : Dense S)
    (h : ∀ u ∈ S, ∀ l ∈ Λu τ, ∀ j < k, iteratedDeriv j (fun z => f (Function.update u s z)) (u t + l) = 0) :
    VanishesAlong τ f s t k := by
  intro u l hl j hj
  have hc : Continuous fun v : Fin N → ℂ => iteratedDeriv j (fun z => f (Function.update v s z)) (v t + l) := by
    have h2 : Continuous fun v : Fin N → ℂ => Function.update v s (v t + l) :=
      continuous_id.update s ((continuous_apply t).add continuous_const)
    have e : (fun v : Fin N → ℂ => iteratedDeriv j (fun z => f (Function.update v s z)) (v t + l)) =
        (fun v => iteratedDeriv j (fun z => f (Function.update v s z)) (v s)) ∘
          fun v => Function.update v s (v t + l) := by
      funext v
      simp only [Function.comp_apply, Function.update_idem, Function.update_self]
    rw [e]
    exact (continuous_iteratedDeriv_slice_dev hf s j).comp h2
  have hzero := Continuous.ext_on hS hc continuous_const fun v hv => h v hv l hl j hj
  exact congrFun hzero u

/-! ### Proof devices for (T3) (proof phase, round two; not statements of the paper)

One variable (`divq_dev`, `divq_spec_dev`): `g/ϑ₁(z − c)^k`, extended at the zeros `c + Λ_u` by its limit, is entire:
at a zero `z₀`, `g = (z − z₀)^k g₁` (Mathlib's `natCast_le_analyticOrderAt` with the vanishing derivatives) and
`ϑ₁(z − c) = (z − z₀) h₁` with `h₁(z₀) ≠ 0` (the zeros of `ϑ₁` are simple, `theta1_deriv_ne_zero_of_mem`), so the
quotient agrees near `z₀` with the analytic `g₁/h₁^k`. Several variables: `Q(u)` is the slice quotient at `u_s`. It is
continuous by the mean value property on a circle about `u_s` that avoids the divisor (the radius chosen off a
countable set of radii, the circle kept off the divisor near `u₀` by the tube lemma); entire in `u_t` since it is
continuous and entire off the countable set `u_s − Λ_u` (`hasFPowerSeriesOnBall_of_differentiable_off_countable`);
entire in any other variable as the locally uniform limit of the off-divisor quotients (`ContinuousMap.curry`,
`ContinuousMap.tendsto_iff_tendstoLocallyUniformly`, `TendstoLocallyUniformlyOn.differentiableOn`). -/

/-- The quotient of `g` by `ϑ₁(z − c)^k`, extended at the zeros of `ϑ₁(z − c)` by its limit. -/
def divq_dev (τ : ℂ) (c : ℂ) (k : ℕ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if theta1 (z - c) τ = 0 then Filter.limUnder (nhdsWithin z {z}ᶜ) (fun w => g w / theta1 (w - c) τ ^ k)
  else g z / theta1 (z - c) τ ^ k

theorem theta1_sub_factor_dev (τ : ℍ) {c z₀ : ℂ} (hz₀ : theta1 (z₀ - c) τ = 0) :
    ∃ h₁ : ℂ → ℂ, AnalyticAt ℂ h₁ z₀ ∧ h₁ z₀ ≠ 0 ∧
      ∀ᶠ z in nhds z₀, theta1 (z - c) τ = (z - z₀) * h₁ z := by
  have hd : Differentiable ℂ fun z => theta1 (z - c) τ :=
    (theta1_differentiable τ).comp (differentiable_id.sub_const c)
  have ha : AnalyticAt ℂ (fun z => theta1 (z - c) τ) z₀ := hd.analyticAt z₀
  have hder : deriv (fun z => theta1 (z - c) τ) z₀ ≠ 0 := by
    rw [((theta1_differentiable τ (z₀ - c)).hasDerivAt.comp_sub_const z₀ c).deriv]
    exact theta1_deriv_ne_zero_of_mem τ ((theta1_eq_zero_iff τ _).1 hz₀)
  have h1 := ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz₀ hder
  obtain ⟨h₁, hh₁, hne, hev⟩ := (ha.analyticOrderAt_eq_natCast (n := 1)).1 (by exact_mod_cast h1)
  exact ⟨h₁, hh₁, hne, hev.mono fun z hz => by simpa [pow_one, smul_eq_mul] using hz⟩

theorem slice_factor_dev {g : ℂ → ℂ} (hg : Differentiable ℂ g) {z₀ : ℂ} {k : ℕ}
    (hv : ∀ j < k, iteratedDeriv j g z₀ = 0) :
    ∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ z₀ ∧ ∀ᶠ z in nhds z₀, g z = (z - z₀) ^ k * g₁ z := by
  have ha := hg.analyticAt z₀
  obtain ⟨g₁, hg₁, hev⟩ :=
    (natCast_le_analyticOrderAt ha).1 ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).2 hv)
  exact ⟨g₁, hg₁, hev.mono fun z hz => by rw [hz, smul_eq_mul]⟩

theorem divq_local_dev (τ : ℍ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) {c z₀ : ℂ} {k : ℕ}
    (hz₀ : theta1 (z₀ - c) τ = 0) (hv : ∀ j < k, iteratedDeriv j g z₀ = 0) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ z₀ ∧ (∀ᶠ z in nhds z₀, g z = theta1 (z - c) τ ^ k * φ z) ∧
      ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, theta1 (z - c) τ ≠ 0 := by
  obtain ⟨h₁, hh₁, hne, hevh⟩ := theta1_sub_factor_dev τ hz₀
  obtain ⟨g₁, hg₁, hevg⟩ := slice_factor_dev hg hv
  have hne' : ∀ᶠ z in nhds z₀, h₁ z ≠ 0 := hh₁.continuousAt.eventually_ne hne
  refine ⟨fun z => g₁ z / h₁ z ^ k, hg₁.div (hh₁.pow k) (pow_ne_zero k hne), ?_, ?_⟩
  · filter_upwards [hevh, hevg, hne'] with z h1 h2 h3
    rw [h2, h1, mul_pow, mul_assoc, mul_div_cancel₀ _ (pow_ne_zero k h3)]
  · filter_upwards [hevh.filter_mono nhdsWithin_le_nhds, hne'.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z h1 h3 h4
    rw [h1]
    exact mul_ne_zero (sub_ne_zero.2 h4) h3

theorem divq_spec_dev (τ : ℍ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) (c : ℂ) (k : ℕ)
    (hv : ∀ l ∈ Λu τ, ∀ j < k, iteratedDeriv j g (c + l) = 0) :
    Differentiable ℂ (divq_dev τ c k g) ∧ ∀ z, g z = theta1 (z - c) τ ^ k * divq_dev τ c k g z := by
  have hθd : Differentiable ℂ fun z => theta1 (z - c) τ :=
    (theta1_differentiable τ).comp (differentiable_id.sub_const c)
  have hpt : ∀ z₀, DifferentiableAt ℂ (divq_dev τ c k g) z₀ ∧
      g z₀ = theta1 (z₀ - c) τ ^ k * divq_dev τ c k g z₀ := by
    intro z₀
    by_cases h0 : theta1 (z₀ - c) τ = 0
    · have hl : z₀ - c ∈ Λu τ := (theta1_eq_zero_iff τ _).1 h0
      have hv' : ∀ j < k, iteratedDeriv j g z₀ = 0 := by
        intro j hj
        have h := hv _ hl j hj
        rwa [add_sub_cancel] at h
      obtain ⟨φ, hφ, hgφ, hne⟩ := divq_local_dev τ hg h0 hv'
      have hpunct : ∀ᶠ w in nhdsWithin z₀ {z₀}ᶜ, g w / theta1 (w - c) τ ^ k = φ w := by
        filter_upwards [hgφ.filter_mono nhdsWithin_le_nhds, hne] with w h1 h2
        rw [h1, mul_div_cancel_left₀ _ (pow_ne_zero k h2)]
      have hlim : Filter.Tendsto (fun w => g w / theta1 (w - c) τ ^ k) (nhdsWithin z₀ {z₀}ᶜ) (nhds (φ z₀)) :=
        (hφ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hpunct.mono fun w hw => hw.symm)
      have hz : divq_dev τ c k g z₀ = φ z₀ := by
        rw [divq_dev, ite_eq_left h0]
        exact hlim.limUnder_eq
      have hpunct' : ∀ᶠ w in nhdsWithin z₀ {z₀}ᶜ, divq_dev τ c k g w = φ w := by
        filter_upwards [hpunct, hne] with w h1 h2
        rw [divq_dev, ite_eq_right h2, h1]
      have hev : divq_dev τ c k g =ᶠ[nhds z₀] φ := by
        have h := Filter.eventually_sup.2 ⟨hpunct', Filter.eventually_pure.2 hz⟩
        rwa [nhdsNE_sup_pure] at h
      refine ⟨hφ.differentiableAt.congr_of_eventuallyEq hev, ?_⟩
      rw [hz]
      exact hgφ.self_of_nhds
    · have hne : ∀ᶠ w in nhds z₀, theta1 (w - c) τ ≠ 0 := hθd.continuous.continuousAt.eventually_ne h0
      have hev : divq_dev τ c k g =ᶠ[nhds z₀] fun w => g w / theta1 (w - c) τ ^ k := by
        filter_upwards [hne] with w hw
        rw [divq_dev, ite_eq_right hw]
      refine ⟨((hg z₀).div ((hθd z₀).pow k) (pow_ne_zero k h0)).congr_of_eventuallyEq hev, ?_⟩
      rw [hev.self_of_nhds, mul_div_cancel₀ _ (pow_ne_zero k h0)]
  exact ⟨fun z => (hpt z).1, fun z => (hpt z).2⟩

/-- The integrand of the mean value of the slice quotient over the circle `u_s + ρ e^{iθ}`. -/
def meanInt_dev (τ : ℂ) {N : ℕ} (f : (Fin N → ℂ) → ℂ) (s t : Fin N) (k : ℕ) (ρ : ℝ) (u : Fin N → ℂ) (θ : ℝ) : ℂ :=
  I * (f (Function.update u s (u s + circleMap 0 ρ θ)) / theta1 (u s + circleMap 0 ρ θ - u t) τ ^ k)

theorem div_theta1_pow_dev (τ : ℍ) {N : ℕ} {f : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) {s t : Fin N} (hst : s ≠ t)
    (k : ℕ) (hv : VanishesAlong τ f s t k) :
    ∃ Q : (Fin N → ℂ) → ℂ, IsOsgood Q ∧ ∀ u, f u = theta1 (u s - u t) τ ^ k * Q u := by
  have hθd : Differentiable ℂ fun z => theta1 z τ := theta1_differentiable τ
  have hslice : ∀ u : Fin N → ℂ, Differentiable ℂ (divq_dev τ (u t) k fun z => f (Function.update u s z)) ∧
      ∀ z, f (Function.update u s z) =
        theta1 (z - u t) τ ^ k * divq_dev τ (u t) k (fun z => f (Function.update u s z)) z :=
    fun u => divq_spec_dev τ (hf.2 u s) (u t) k fun l hl j hj => hv u l hl j hj
  obtain ⟨Q, hQ⟩ : ∃ Q : (Fin N → ℂ) → ℂ,
      ∀ u, Q u = divq_dev τ (u t) k (fun z => f (Function.update u s z)) (u s) := ⟨_, fun _ => rfl⟩
  have hfac : ∀ u, f u = theta1 (u s - u t) τ ^ k * Q u := by
    intro u
    have h := (hslice u).2 (u s)
    rwa [Function.update_eq_self, ← hQ] at h
  have hoff : ∀ u, theta1 (u s - u t) τ ≠ 0 → Q u = f u / theta1 (u s - u t) τ ^ k := by
    intro u hu
    rw [hfac u, mul_div_cancel_left₀ _ (pow_ne_zero k hu)]
  have hQs : ∀ (u : Fin N → ℂ) (z : ℂ),
      Q (Function.update u s z) = divq_dev τ (u t) k (fun z => f (Function.update u s z)) z := by
    intro u z
    rw [hQ]
    simp only [Function.update_self, Function.update_of_ne hst.symm, Function.update_idem]
  -- continuity
  have hQcont : Continuous Q := by
    rw [continuous_iff_continuousAt]
    intro u₀
    have hB : ((fun l => ‖u₀ t + l - u₀ s‖) '' Λu τ).Countable := (Λu_countable_dev τ).image _
    obtain ⟨ρ, hρB, hρ⟩ := (hB.dense_compl ℝ).exists_between (zero_lt_one : (0 : ℝ) < 1)
    have hρ0 : 0 < ρ := hρ.1
    have hcirc : ∀ e ∈ Metric.sphere (0 : ℂ) 1, theta1 (u₀ s + ρ * e - u₀ t) τ ≠ 0 := by
      intro e he h0
      apply hρB
      refine ⟨u₀ s + ρ * e - u₀ t, (theta1_eq_zero_iff τ _).1 h0, ?_⟩
      have he1 : ‖e‖ = 1 := by simpa using he
      show ‖u₀ t + (u₀ s + ρ * e - u₀ t) - u₀ s‖ = ρ
      rw [show u₀ t + (u₀ s + ρ * e - u₀ t) - u₀ s = (ρ : ℂ) * e by ring, norm_mul, he1, mul_one,
        Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    have hcθ : Continuous fun p : (Fin N → ℂ) × ℂ => theta1 (p.1 s + ρ * p.2 - p.1 t) τ :=
      hθd.continuous.comp (by fun_prop)
    have hV : ∀ᶠ u in nhds u₀, ∀ e ∈ Metric.sphere (0 : ℂ) 1, theta1 (u s + ρ * e - u t) τ ≠ 0 :=
      (isCompact_sphere (0 : ℂ) 1).eventually_forall_of_forall_eventually fun e he =>
        hcθ.continuousAt.eventually_ne (hcirc e he)
    obtain ⟨W, hWV, hWo, hu₀W⟩ := mem_nhds_iff.1 hV
    have hcm : ∀ θ : ℝ, circleMap 0 ρ θ = ρ * cexp (θ * I) := fun θ => by simp [circleMap]
    have hsph : ∀ θ : ℝ, cexp (θ * I) ∈ Metric.sphere (0 : ℂ) 1 := fun θ => by
      simp [Complex.norm_exp_ofReal_mul_I]
    have hFne : ∀ (x : W) (θ : ℝ), theta1 (x.1 s + circleMap 0 ρ θ - x.1 t) τ ≠ 0 := by
      intro x θ
      rw [hcm]
      exact hWV x.2 _ (hsph θ)
    have hFc : Continuous fun p : W × ℝ => meanInt_dev τ f s t k ρ p.1.1 p.2 := by
      show Continuous fun p : W × ℝ => I * (f (Function.update p.1.1 s (p.1.1 s + circleMap 0 ρ p.2)) /
        theta1 (p.1.1 s + circleMap 0 ρ p.2 - p.1.1 t) τ ^ k)
      refine continuous_const.mul (Continuous.div ?_ ?_ fun p => pow_ne_zero k (hFne p.1 p.2))
      · exact hf.1.comp ((continuous_subtype_val.comp continuous_fst).update s
          (((continuous_apply s).comp (continuous_subtype_val.comp continuous_fst)).add
            ((continuous_circleMap 0 ρ).comp continuous_snd)))
      · exact (hθd.continuous.comp ((((continuous_apply s).comp (continuous_subtype_val.comp continuous_fst)).add
            ((continuous_circleMap 0 ρ).comp continuous_snd)).sub
            ((continuous_apply t).comp (continuous_subtype_val.comp continuous_fst)))).pow k
    have hrep : ∀ x : W, Q x.1 = (2 * π * I)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, meanInt_dev τ f s t k ρ x.1 θ := by
      intro x
      have hCauchy := ((hslice x.1).1.differentiableOn).circleIntegral_sub_inv_smul
        (Metric.mem_ball_self (x := x.1 s) hρ0)
      unfold circleIntegral at hCauchy
      have hint : (∫ θ in (0 : ℝ)..2 * π, deriv (circleMap (x.1 s) ρ) θ •
          (circleMap (x.1 s) ρ θ - x.1 s)⁻¹ •
            divq_dev τ (x.1 t) k (fun z => f (Function.update x.1 s z)) (circleMap (x.1 s) ρ θ)) =
          ∫ θ in (0 : ℝ)..2 * π, meanInt_dev τ f s t k ρ x.1 θ := by
        refine intervalIntegral.integral_congr fun θ _ => ?_
        have hne0 : circleMap 0 ρ θ ≠ 0 := circleMap_ne_center hρ0.ne'
        have hqv : divq_dev τ (x.1 t) k (fun z => f (Function.update x.1 s z)) (x.1 s + circleMap 0 ρ θ) =
            f (Function.update x.1 s (x.1 s + circleMap 0 ρ θ)) /
              theta1 (x.1 s + circleMap 0 ρ θ - x.1 t) τ ^ k := by
          rw [(hslice x.1).2, mul_div_cancel_left₀ _ (pow_ne_zero k (hFne x θ))]
        simp only [smul_eq_mul, deriv_circleMap, circleMap_sub_center, meanInt_dev]
        rw [show circleMap (x.1 s) ρ θ = x.1 s + circleMap 0 ρ θ by simp [circleMap], hqv]
        calc circleMap 0 ρ θ * I * ((circleMap 0 ρ θ)⁻¹ * (f (Function.update x.1 s (x.1 s + circleMap 0 ρ θ)) /
              theta1 (x.1 s + circleMap 0 ρ θ - x.1 t) τ ^ k))
            = I * (circleMap 0 ρ θ * (circleMap 0 ρ θ)⁻¹) * (f (Function.update x.1 s (x.1 s + circleMap 0 ρ θ)) /
              theta1 (x.1 s + circleMap 0 ρ θ - x.1 t) τ ^ k) := by ring
          _ = I * (f (Function.update x.1 s (x.1 s + circleMap 0 ρ θ)) /
              theta1 (x.1 s + circleMap 0 ρ θ - x.1 t) τ ^ k) := by rw [mul_inv_cancel₀ hne0, mul_one]
      rw [hint] at hCauchy
      rw [hQ, hCauchy, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
    have hcontW : ContinuousOn Q W := by
      rw [continuousOn_iff_continuous_domRestrict]
      have e : Set.domRestrict W Q =
          fun x : W => (2 * π * I)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, meanInt_dev τ f s t k ρ x.1 θ := funext hrep
      rw [e]
      exact continuous_const.mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun (x : W) θ =>
          meanInt_dev τ f s t k ρ x.1 θ) hFc _ _)
    exact hcontW.continuousAt (hWo.mem_nhds hu₀W)
  -- separate holomorphy
  have hQd : ∀ (u : Fin N → ℂ) (i : Fin N), Differentiable ℂ fun z => Q (Function.update u i z) := by
    intro u i
    by_cases his : i = s
    · rw [his]
      have e : (fun z => Q (Function.update u s z)) = divq_dev τ (u t) k (fun z => f (Function.update u s z)) :=
        funext (hQs u)
      rw [e]
      exact (hslice u).1
    by_cases hit : i = t
    · rw [hit]
      have hcont : Continuous fun z => Q (Function.update u t z) :=
        hQcont.comp (continuous_const.update t continuous_id)
      have hS : ((fun l => u s - l) '' Λu τ).Countable := (Λu_countable_dev τ).image _
      have key : ∀ z', theta1 (u s - z') τ ≠ 0 →
          Q (Function.update u t z') = f (Function.update u t z') / theta1 (u s - z') τ ^ k := by
        intro z' hz'
        have h := hoff (Function.update u t z')
        simp only [Function.update_self, Function.update_of_ne hst] at h
        exact h hz'
      have hθc : Continuous fun z' : ℂ => theta1 (u s - z') τ :=
        hθd.continuous.comp (continuous_const.sub continuous_id)
      have hdiff : ∀ z ∉ (fun l => u s - l) '' Λu τ,
          DifferentiableAt ℂ (fun z => Q (Function.update u t z)) z := by
        intro z hz
        have hne : theta1 (u s - z) τ ≠ 0 := fun h0 => hz ⟨u s - z, (theta1_eq_zero_iff τ _).1 h0, by ring⟩
        have hev : (fun z' => Q (Function.update u t z')) =ᶠ[nhds z]
            fun z' => f (Function.update u t z') / theta1 (u s - z') τ ^ k := by
          filter_upwards [hθc.continuousAt.eventually_ne hne] with z' hz'
          exact key z' hz'
        refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
        exact ((hf.2 u t) z).div (((hθd.comp ((differentiable_const _).sub differentiable_id)) z).pow k)
          (pow_ne_zero k hne)
      intro z
      have hps := hasFPowerSeriesOnBall_of_differentiable_off_countable (R := 1) (c := z) hS
        hcont.continuousOn (fun z' hz' => hdiff z' hz'.2) one_pos
      exact hps.analyticAt.differentiableAt
    by_cases h0 : theta1 (u s - u t) τ = 0
    · have hHc : Continuous fun p : ℂ × ℂ => Q (Function.update (Function.update u i p.2) s p.1) :=
        hQcont.comp (((continuous_const : Continuous fun _ : ℂ × ℂ => u).update i continuous_snd).update s continuous_fst)
      let Hc : C(ℂ × ℂ, ℂ) := ⟨fun p => Q (Function.update (Function.update u i p.2) s p.1), hHc⟩
      have hT := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 (Hc.curry.continuous.tendsto (u s))
      have hS'dense : Dense {ζ : ℂ | theta1 (ζ - u t) τ ≠ 0} := by
        have hc : ((fun l => u t + l) '' Λu τ).Countable := (Λu_countable_dev τ).image _
        refine Dense.mono ?_ (hc.dense_compl ℂ)
        intro ζ hζ h0'
        exact hζ ⟨ζ - u t, (theta1_eq_zero_iff τ _).1 h0', by ring⟩
      have : (nhdsWithin (u s) {ζ : ℂ | theta1 (ζ - u t) τ ≠ 0}).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.1 (hS'dense (u s))
      have hT' : TendstoLocallyUniformlyOn (fun ζ z => Hc.curry ζ z) (Hc.curry (u s))
          (nhdsWithin (u s) {ζ : ℂ | theta1 (ζ - u t) τ ≠ 0}) Set.univ := by
        rw [tendstoLocallyUniformlyOn_univ]
        intro v hv x
        obtain ⟨w, hw, h⟩ := hT v hv x
        exact ⟨w, hw, h.filter_mono nhdsWithin_le_nhds⟩
      have hgood : ∀ ζ : ℂ, theta1 (ζ - u t) τ ≠ 0 → DifferentiableOn ℂ (Hc.curry ζ) Set.univ := by
        intro ζ hζ
        have e : (Hc.curry ζ : ℂ → ℂ) = fun z => f (Function.update (Function.update u s ζ) i z) /
            theta1 (ζ - u t) τ ^ k := by
          funext z
          show Q (Function.update (Function.update u i z) s ζ) = _
          have h := hoff (Function.update (Function.update u i z) s ζ)
          simp only [Function.update_self, Function.update_of_ne hst.symm, Function.update_of_ne (Ne.symm hit)]
            at h
          rw [h hζ, Function.update_comm his]
        rw [e]
        exact ((hf.2 _ i).div_const _).differentiableOn
      have hD := hT'.differentiableOn (Filter.eventually_of_mem self_mem_nhdsWithin hgood) isOpen_univ
      have e : (fun z => Q (Function.update u i z)) = (Hc.curry (u s) : ℂ → ℂ) := by
        funext z
        show Q (Function.update u i z) = Q (Function.update (Function.update u i z) s (u s))
        congr 1
        rw [show u s = (Function.update u i z) s from (Function.update_of_ne (Ne.symm his) z u).symm,
          Function.update_eq_self]
      rw [e]
      exact fun z => (hD z (Set.mem_univ z)).differentiableAt Filter.univ_mem
    · have e : (fun z => Q (Function.update u i z)) =
          fun z => f (Function.update u i z) / theta1 (u s - u t) τ ^ k := by
        funext z
        have h := hoff (Function.update u i z)
        simp only [Function.update_of_ne (Ne.symm his), Function.update_of_ne (Ne.symm hit)] at h
        exact h h0
      rw [e]
      exact (hf.2 u i).div_const _
  exact ⟨Q, ⟨hQcont, hQd⟩, hfac⟩

/-! ### Proof devices for (T4) (proof phase, round two; not statements of the paper): the coordinates of `mergePt`

The variable `i` of `rest` sits at `mIdx_dev i` in `mergePt` (`mergePt_update_dev`), and `mergePt w r` is a base point
with its two merged coordinates updated to `w` (`mergePt_eq_update_dev`); the two-variable step is F1-lower's
`isOsgood2_differentiable_dev` along `w ↦ (w, w)`, the pattern of `differentiable_osgood_merge_dev`. -/

/-- The position in `Fin ((n + 1) + (m + 1))` of the variable `i` of `rest`. -/
def mIdx_dev {n m : ℕ} (i : Fin (n + m)) : Fin ((n + 1) + (m + 1)) :=
  Fin.addCases (fun a : Fin n => Fin.castAdd (m + 1) a.succ) (fun k : Fin m => Fin.natAdd (n + 1) k.succ) i

theorem mergePt_update_dev {n m : ℕ} (w : ℂ) (r : Fin (n + m) → ℂ) (i : Fin (n + m)) (z : ℂ) :
    mergePt w (Function.update r i z) = Function.update (mergePt w r) (mIdx_dev i) z := by
  funext j
  induction i using Fin.addCases with
  | left a₀ =>
    induction j using Fin.addCases with
    | left a' =>
      induction a' using Fin.cases with
      | zero => simp [mergePt, mIdx_dev, Function.update_apply]; intro h; exact absurd h.symm (Fin.succ_ne_zero _)
      | succ a => simp [mergePt, mIdx_dev, Function.update_apply]
    | right b' =>
      induction b' using Fin.cases with
      | zero => simp [mergePt, mIdx_dev, Function.update_apply, (castAdd_ne_natAdd_dev _ _).symm]
      | succ k =>
        simp [mergePt, mIdx_dev, Function.update_apply, (castAdd_ne_natAdd_dev _ _).symm]
  | right k₀ =>
    induction j using Fin.addCases with
    | left a' =>
      induction a' using Fin.cases with
      | zero => simp [mergePt, mIdx_dev, Function.update_apply, castAdd_ne_natAdd_dev]
      | succ a => simp [mergePt, mIdx_dev, Function.update_apply, castAdd_ne_natAdd_dev]
    | right b' =>
      induction b' using Fin.cases with
      | zero => simp [mergePt, mIdx_dev, Function.update_apply]; intro h; exact absurd h.symm (Fin.succ_ne_zero _)
      | succ k => simp [mergePt, mIdx_dev, Function.update_apply]

theorem continuous_mergePt_dev {n m : ℕ} (w : ℂ) : Continuous fun r : Fin (n + m) → ℂ => mergePt w r := by
  refine continuous_pi fun j => ?_
  induction j using Fin.addCases with
  | left a' =>
    induction a' using Fin.cases with
    | zero => simpa [mergePt] using continuous_const
    | succ a => simpa [mergePt] using continuous_apply (Fin.castAdd m a)
  | right b' =>
    induction b' using Fin.cases with
    | zero => simpa [mergePt] using continuous_const
    | succ k => simpa [mergePt] using continuous_apply (Fin.natAdd n k)

theorem mergePt_eq_update_dev {n m : ℕ} (w : ℂ) (r : Fin (n + m) → ℂ) :
    mergePt w r = Function.update (Function.update (mergePt 0 r) (Fin.castAdd (m + 1) 0) w)
      (Fin.natAdd (n + 1) 0) w := by
  funext j
  induction j using Fin.addCases with
  | left a' =>
    induction a' using Fin.cases with
    | zero => simp [mergePt, castAdd_ne_natAdd_dev]
    | succ a => simp [mergePt, castAdd_ne_natAdd_dev, Fin.succ_ne_zero]
  | right b' =>
    induction b' using Fin.cases with
    | zero => simp [mergePt]
    | succ k => simp [mergePt, (castAdd_ne_natAdd_dev _ _).symm, Fin.succ_ne_zero]

theorem isOsgood_mergePt_dev {n m : ℕ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ} (ha : IsOsgood a) (w : ℂ) :
    IsOsgood fun r : Fin (n + m) → ℂ => a (mergePt w r) := by
  refine ⟨ha.1.comp (continuous_mergePt_dev w), fun r i => ?_⟩
  have e : (fun z => a (mergePt w (Function.update r i z))) =
      fun z => a (Function.update (mergePt w r) (mIdx_dev i) z) := by
    funext z
    rw [mergePt_update_dev]
  rw [e]
  exact ha.2 _ _

theorem differentiable_mergePt_dev {n m : ℕ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ} (ha : IsOsgood a)
    (r : Fin (n + m) → ℂ) : Differentiable ℂ fun w => a (mergePt w r) := by
  set s : Fin ((n + 1) + (m + 1)) := Fin.castAdd (m + 1) 0 with hs
  set t : Fin ((n + 1) + (m + 1)) := Fin.natAdd (n + 1) 0 with ht
  have hst : s ≠ t := castAdd_ne_natAdd_dev _ _
  set u := mergePt 0 r with hu
  set G : ℂ × ℂ → ℂ := fun p => a (Function.update (Function.update u s p.1) t p.2) with hG
  have hGos : IsOsgood2_dev G := by
    refine ⟨?_, fun b => ?_, fun x => ?_⟩
    · refine ha.1.comp (continuous_pi fun i => ?_)
      by_cases hit : i = t
      · subst hit
        simp only [Function.update_self]
        exact continuous_snd
      · by_cases his : i = s
        · subst his
          simp only [Function.update_of_ne hit, Function.update_self]
          exact continuous_fst
        · simp only [Function.update_of_ne hit, Function.update_of_ne his]
          exact continuous_const
    · have e : (fun x => G (x, b)) = fun x => a (Function.update (Function.update u t b) s x) :=
        funext fun x => by simp only [hG]; rw [Function.update_comm hst]
      rw [e]
      exact ha.2 _ s
    · exact ha.2 (Function.update u s x) t
  have e : (fun w => a (mergePt w r)) = G ∘ fun w => (w, w) := by
    funext w
    simp only [Function.comp_apply, hG, hu, hs, ht]
    rw [mergePt_eq_update_dev]
  rw [e]
  exact (isOsgood2_differentiable_dev hGos).comp (differentiable_id.prodMk differentiable_id)

/-! ### Proof devices for (T5) and (T7) (proof phase, round two; not statements of the paper)

(T5): a bounded slice is constant (`Differentiable.apply_eq_apply_of_bounded`), and `u` is joined to `v` by changing
one coordinate at a time (`Finset.piecewise`). (T7): Baire's theorem for the countable family of open dense sets
`{u_i − u_j ≠ λ}` (`dense_iInter_of_isOpen`); each is dense since `u + t e_i` leaves the hyperplane for `t ≠ 0`. -/

theorem dense_ne_dev {N : ℕ} {i j : Fin N} (hij : i ≠ j) (l : ℂ) : Dense {u : Fin N → ℂ | u i - u j ≠ l} := by
  intro u
  by_cases hu : u i - u j = l
  · have hcont : Continuous fun t : ℂ => Function.update u i (u i + t) :=
      continuous_const.update i (continuous_const.add continuous_id)
    have ht : Filter.Tendsto (fun t : ℂ => Function.update u i (u i + t)) (nhdsWithin 0 {0}ᶜ) (nhds u) := by
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
      simpa using this
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with t htne
    simp only [Function.update_self, Function.update_of_ne hij.symm]
    intro h
    exact htne (show t = 0 by linear_combination h - hu)
  · exact subset_closure hu

theorem isOsgood_eq_of_bounded_dev {N : ℕ} {f : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) {C : ℝ}
    (hb : ∀ u, ‖f u‖ ≤ C) (u v : Fin N → ℂ) : f u = f v := by
  have hslice : ∀ (w : Fin N → ℂ) (i : Fin N) (z : ℂ), f (Function.update w i z) = f w := by
    intro w i z
    have hb' : Bornology.IsBounded (Set.range fun z => f (Function.update w i z)) := by
      rw [isBounded_iff_forall_norm_le]
      exact ⟨C, by rintro _ ⟨z, rfl⟩; exact hb _⟩
    rw [(hf.2 w i).apply_eq_apply_of_bounded hb' z (w i), Function.update_eq_self]
  have key : ∀ S : Finset (Fin N), f u = f (S.piecewise v u) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · rw [Finset.piecewise_empty]
    · intro a S _ ih
      rw [Finset.piecewise_insert, hslice, ih]
  rw [key Finset.univ, Finset.piecewise_univ]

theorem dense_generic_dev (τ : ℍ) {N : ℕ} (P : Finset (Fin N × Fin N)) (hP : ∀ p ∈ P, p.1 ≠ p.2) :
    Dense {u : Fin N → ℂ | ∀ p ∈ P, u p.1 - u p.2 ∉ Λu τ} := by
  have hset : {u : Fin N → ℂ | ∀ p ∈ P, u p.1 - u p.2 ∉ Λu τ} =
      ⋂ q : P × Λu τ, {u : Fin N → ℂ | u q.1.1.1 - u q.1.1.2 ≠ q.2} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · rintro h ⟨⟨p, hp⟩, ⟨l, hl⟩⟩ heq
      exact h p hp (heq ▸ hl)
    · intro h p hp hl
      exact h ⟨⟨p, hp⟩, ⟨_, hl⟩⟩ rfl
  rw [hset]
  have : Countable (Λu τ) := (Λu_countable_dev τ).to_subtype
  refine dense_iInter_of_isOpen (fun q => ?_) (fun q => ?_)
  · exact isOpen_ne_fun (by fun_prop) continuous_const
  · exact dense_ne_dev (hP q.1.1 q.1.2) q.2

/-! ### Proof devices for the merge (proof phase, round two; not statements of the paper): the merged coordinates,
the shift of the centre (both merged coordinates move, so (ii) applies twice), the sum of the coordinates, and the
multipliers of `E` (`theta1_add_one`, `theta1_add_tau` in each factor) -/

theorem mergePt_s0_dev {n m : ℕ} (w : ℂ) (r : Fin (n + m) → ℂ) : mergePt w r (Fin.castAdd (m + 1) 0) = w := by
  simp [mergePt]

theorem mergePt_t0_dev {n m : ℕ} (w : ℂ) (r : Fin (n + m) → ℂ) : mergePt w r (Fin.natAdd (n + 1) 0) = w := by
  simp [mergePt]

theorem mergePt_shift_dev {n m : ℕ} (w c : ℂ) (r : Fin (n + m) → ℂ) :
    mergePt (w + c) r = Function.update (Function.update (mergePt w r) (Fin.castAdd (m + 1) 0) (w + c))
      (Fin.natAdd (n + 1) 0) (w + c) := by
  funext j
  induction j using Fin.addCases with
  | left a' =>
    induction a' using Fin.cases with
    | zero => simp [mergePt, castAdd_ne_natAdd_dev]
    | succ a => simp [mergePt, castAdd_ne_natAdd_dev, Fin.succ_ne_zero]
  | right b' =>
    induction b' using Fin.cases with
    | zero => simp [mergePt]
    | succ k => simp [mergePt, (castAdd_ne_natAdd_dev _ _).symm, Fin.succ_ne_zero]

theorem sum_mergePt_dev {n m : ℕ} (w : ℂ) (r : Fin (n + m) → ℂ) :
    ∑ i, mergePt w r i = 2 * w + ∑ i, r i := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add (f := r)]
  simp only [mergePt, Fin.append_left, Fin.append_right, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem Emerge_add_one_dev (τ : ℂ) {K : ℕ} (w : ℂ) (r : Fin K → ℂ) : Emerge τ (w + 1) r = Emerge τ w r := by
  unfold Emerge
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show w + 1 - r i = (w - r i) + 1 by ring, theta1_add_one]
  ring

theorem Emerge_add_tau_dev (τ : ℂ) {K : ℕ} (w : ℂ) (r : Fin K → ℂ) :
    Emerge τ (w + τ) r = cexp (-4 * π * I * τ * K - 8 * π * I * (K * w - ∑ i, r i)) * Emerge τ w r := by
  have hsum : ∑ i, (-4 * π * I * τ - 8 * π * I * (w - r i)) = -4 * π * I * τ * K - 8 * π * I * (K * w - ∑ i, r i) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  unfold Emerge
  rw [← hsum, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 : ∀ A : ℂ, cexp A ^ 4 = cexp (4 * A) := fun A => by rw [← Complex.exp_nat_mul]; norm_num
  rw [show w + τ - r i = (w - r i) + τ by ring, theta1_add_tau,
    show (-cexp (-π * I * τ - 2 * π * I * (w - r i)) * theta1 (w - r i) τ) ^ 4 =
      cexp (-π * I * τ - 2 * π * I * (w - r i)) ^ 4 * theta1 (w - r i) τ ^ 4 by ring, h4]
  congr 2
  ring

theorem mergePt_add_tau_dev (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (haτ : ∀ (u : Fin ((n + 1) + (m + 1)) → ℂ) (k : Fin ((n + 1) + (m + 1))), a (Function.update u k (u k + τ)) =
      ε.2 * cexp (-2 * π * I * ((((n + 1) + (m + 1) : ℕ) : ℂ) - 1) * τ -
        4 * π * I * ((((n + 1) + (m + 1) : ℕ) : ℂ) * u k - ∑ i, u i)) * a u)
    (w : ℂ) (r : Fin (n + m) → ℂ) :
    a (mergePt (w + τ) r) =
      ε.2 ^ 2 * cexp (-4 * π * I * τ * ((n + m : ℕ) : ℂ) - 8 * π * I * (((n + m : ℕ) : ℂ) * w - ∑ i, r i)) *
        a (mergePt w r) := by
  have hst : Fin.castAdd (m + 1) (0 : Fin (n + 1)) ≠ Fin.natAdd (n + 1) (0 : Fin (m + 1)) := castAdd_ne_natAdd_dev _ _
  have e : mergePt (w + τ) r =
      Function.update (Function.update (mergePt w r) (Fin.castAdd (m + 1) 0)
        (mergePt w r (Fin.castAdd (m + 1) 0) + τ)) (Fin.natAdd (n + 1) 0)
        (Function.update (mergePt w r) (Fin.castAdd (m + 1) 0) (mergePt w r (Fin.castAdd (m + 1) 0) + τ)
          (Fin.natAdd (n + 1) 0) + τ) := by
    rw [Function.update_of_ne hst.symm, mergePt_s0_dev, mergePt_t0_dev]
    exact mergePt_shift_dev w τ r
  have key : ∀ x y A : ℂ, ε.2 * cexp x * (ε.2 * cexp y * A) = ε.2 ^ 2 * cexp (x + y) * A := fun x y A => by
    rw [Complex.exp_add]
    ring
  rw [e, haτ, haτ, key]
  simp only [Function.update_of_ne hst.symm, mergePt_s0_dev, mergePt_t0_dev, sum_update_dev,
    sum_mergePt_dev]
  congr 3
  push_cast
  ring

/-! ## Lemma C.C -/

/-! ### Proof devices for Lemma C.C(a) (proof phase, round two; not statements of the paper)

Steps 1 and 2 (`order4_dev`): (T3) gives `𝖺 = ϑ₁(u_p − u_q)³ Q` for the pair `(x₁, x_a)` (resp. `(y₁, y_k)`); (C2) for the
pair `(x_a, y₁)` (resp. `(x₁, y_k)`), through `relDeriv_theta_cube_dev`, reads `∓3ϑ₁'Q + ϑ₁ D Q = 0` off the divisor,
and its limit at the triple coincidence gives `Q = 0` there (`triple_zero_dev`, with (T1) for the continuity of `D Q`);
so `w ↦ 𝖺|_M` vanishes to order `≥ 4` at `w = x_a` (resp. `y_k`). The order passes to `x_a + Λ_u` through the
multipliers of `𝖺|_M` in `w` (`lattice_closed_dev`), and Step 4 is the division by `E` in `w` alone
(`divqg_spec_dev`, the pattern of `divq_spec_dev` with a general divisor). A coincidence of two variables of one
species in `rest` makes `𝖺|_M ≡ 0` by (C1) (`zero_of_coincide_dev`). -/

theorem mergePt_add_one_dev {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha1 : ∀ (u : Fin ((n + 1) + (m + 1)) → ℂ) (k : Fin ((n + 1) + (m + 1))),
      a (Function.update u k (u k + 1)) = ε.1 * a u)
    (w : ℂ) (r : Fin (n + m) → ℂ) : a (mergePt (w + 1) r) = ε.1 ^ 2 * a (mergePt w r) := by
  have hst : Fin.castAdd (m + 1) (0 : Fin (n + 1)) ≠ Fin.natAdd (n + 1) (0 : Fin (m + 1)) := castAdd_ne_natAdd_dev _ _
  have e : mergePt (w + 1) r =
      Function.update (Function.update (mergePt w r) (Fin.castAdd (m + 1) 0)
        (mergePt w r (Fin.castAdd (m + 1) 0) + 1)) (Fin.natAdd (n + 1) 0)
        (Function.update (mergePt w r) (Fin.castAdd (m + 1) 0) (mergePt w r (Fin.castAdd (m + 1) 0) + 1)
          (Fin.natAdd (n + 1) 0) + 1) := by
    rw [Function.update_of_ne hst.symm, mergePt_s0_dev, mergePt_t0_dev]
    exact mergePt_shift_dev w 1 r
  rw [e, ha1, ha1]
  ring

theorem mergePt_mIdx_dev {n m : ℕ} (w : ℂ) (r : Fin (n + m) → ℂ) (i : Fin (n + m)) :
    mergePt w r (mIdx_dev i) = r i := by
  induction i using Fin.addCases with
  | left b => simp [mergePt, mIdx_dev]
  | right k => simp [mergePt, mIdx_dev]

theorem zero_of_coincide_dev (τ : ℍ) {n m : ℕ} {a : (Fin (n + m) → ℂ) → ℂ} (hC1 : C1 τ n m a) {s t : Fin (n + m)}
    (hst : s ≠ t) (hss : SameSpecies n s t) (u : Fin (n + m) → ℂ) (hl : u s - u t ∈ Λu τ) : a u = 0 := by
  rcases lt_or_gt_of_ne hst with h | h
  · have hv := hC1 s t h hss u (u s - u t) hl 0 (by norm_num)
    rw [iteratedDeriv_zero, show u t + (u s - u t) = u s by ring, Function.update_eq_self] at hv
    exact hv
  · have hss' : SameSpecies n t s := hss.symm
    have hl' : u t - u s ∈ Λu τ := by
      rw [show u t - u s = -(u s - u t) by ring]
      exact neg_mem_Λu_dev τ hl
    have hv := hC1 t s h hss' u (u t - u s) hl' 0 (by norm_num)
    rw [iteratedDeriv_zero, show u s + (u t - u s) = u t by ring, Function.update_eq_self] at hv
    exact hv

theorem lattice_closed_dev (τ : ℍ) {P : ℂ → Prop} (h1 : ∀ z, P z → P (z + 1)) (h1' : ∀ z, P (z + 1) → P z)
    (hτ : ∀ z, P z → P (z + τ)) (hτ' : ∀ z, P (z + τ) → P z) {z₀ : ℂ} (h0 : P z₀) :
    ∀ l ∈ Λu τ, P (z₀ + l) := by
  rintro l ⟨p, q, rfl⟩
  have hp : ∀ p : ℤ, ∀ z, P z → P (z + p) := by
    intro p
    refine Int.induction_on p ?_ ?_ ?_
    · intro z hz
      simpa using hz
    · intro k ih z hz
      have := h1 _ (ih z hz)
      rwa [show z + ((k : ℤ) : ℂ) + 1 = z + (((k : ℤ) + 1 : ℤ) : ℂ) by push_cast; ring] at this
    · intro k ih z hz
      apply h1'
      rw [show z + ((-(k : ℤ) - 1 : ℤ) : ℂ) + 1 = z + ((-(k : ℤ) : ℤ) : ℂ) by push_cast; ring]
      exact ih z hz
  have hq : ∀ q : ℤ, ∀ z, P z → P (z + q * τ) := by
    intro q
    refine Int.induction_on q ?_ ?_ ?_
    · intro z hz
      simpa using hz
    · intro k ih z hz
      have := hτ _ (ih z hz)
      rwa [show z + ((k : ℤ) : ℂ) * τ + τ = z + (((k : ℤ) + 1 : ℤ) : ℂ) * τ by push_cast; ring] at this
    · intro k ih z hz
      apply hτ'
      rw [show z + ((-(k : ℤ) - 1 : ℤ) : ℂ) * τ + τ = z + ((-(k : ℤ) : ℤ) : ℂ) * τ by push_cast; ring]
      exact ih z hz
  have := hq q _ (hp p z₀ h0)
  rwa [show z₀ + (p : ℂ) + (q : ℂ) * τ = z₀ + ((p : ℂ) + (q : ℂ) * τ) by ring] at this

theorem relDeriv_theta_cube_dev (τ : ℍ) {N : ℕ} {Q : (Fin N → ℂ) → ℂ} (hQ : IsOsgood Q) {p q x : Fin N}
    (hpq : p ≠ q) (hpx : p ≠ x) (hqx : q ≠ x) (u : Fin N → ℂ) :
    relDeriv (fun v => theta1 (v p - v q) τ ^ 3 * Q v) q x u =
      -1 * 3 * theta1 (u p - u q) τ ^ 2 * deriv (fun z => theta1 z τ) (u p - u q) * Q u +
        theta1 (u p - u q) τ ^ 3 * relDeriv Q q x u := by
  unfold relDeriv
  have eq : (fun z => (fun v => theta1 (v p - v q) τ ^ 3 * Q v) (Function.update u q z)) =
      fun z => theta1 (u p - z) τ ^ 3 * Q (Function.update u q z) := by
    funext z
    simp only [Function.update_of_ne hpq, Function.update_self]
  have ex : (fun z => (fun v => theta1 (v p - v q) τ ^ 3 * Q v) (Function.update u x z)) =
      fun z => theta1 (u p - u q) τ ^ 3 * Q (Function.update u x z) := by
    funext z
    simp only [Function.update_of_ne hpx, Function.update_of_ne hqx]
  have hθ : HasDerivAt (fun z => theta1 (u p - z) τ ^ 3)
      (-3 * theta1 (u p - u q) τ ^ 2 * deriv (fun z => theta1 z τ) (u p - u q)) (u q) :=
    (((theta1_differentiable τ (u p - u q)).hasDerivAt.comp_const_sub (u p) (u q)).fun_pow 3).congr_deriv
      (by rw [show (3 : ℕ) - 1 = 2 from rfl]; push_cast; ring)
  have hd1 : HasDerivAt (fun z => theta1 (u p - z) τ ^ 3 * Q (Function.update u q z))
      (-3 * theta1 (u p - u q) τ ^ 2 * deriv (fun z => theta1 z τ) (u p - u q) * Q (Function.update u q (u q)) +
        theta1 (u p - u q) τ ^ 3 * deriv (fun z => Q (Function.update u q z)) (u q)) (u q) :=
    hθ.mul ((hQ.2 u q (u q)).hasDerivAt)
  have hd2 : HasDerivAt (fun z => theta1 (u p - u q) τ ^ 3 * Q (Function.update u x z))
      (theta1 (u p - u q) τ ^ 3 * deriv (fun z => Q (Function.update u x z)) (u x)) (u x) :=
    ((hQ.2 u x (u x)).hasDerivAt).const_mul (theta1 (u p - u q) τ ^ 3)
  rw [eq, ex, hd1.deriv, hd2.deriv, Function.update_eq_self]
  ring

theorem triple_zero_dev (τ : ℍ) {N : ℕ} {Q R : (Fin N → ℂ) → ℂ} (hQ : Continuous Q) (hR : Continuous R)
    {p q x : Fin N} (hpq : p ≠ q) (hpx : p ≠ x) (c : ℂ) (hc : c ≠ 0)
    (hrel : ∀ u : Fin N → ℂ, u q = u x → theta1 (u p - u q) τ ≠ 0 →
      c * 3 * deriv (fun z => theta1 z τ) (u p - u q) * Q u + theta1 (u p - u q) τ * R u = 0)
    (u : Fin N → ℂ) (h1 : u p = u q) (h2 : u q = u x) : Q u = 0 := by
  have hθ'c : Continuous (deriv fun z => theta1 z τ) := (theta1_differentiable τ).deriv.continuous
  have hu : Continuous fun ζ : ℂ => Function.update u p ζ := continuous_const.update p continuous_id
  have hsub : Continuous fun ζ : ℂ => ζ - u q := continuous_sub_right (u q)
  have hθ1 : Continuous fun ζ : ℂ => theta1 (ζ - u q) τ := (theta1_differentiable τ).continuous.comp hsub
  have hθ2 : Continuous fun ζ : ℂ => deriv (fun z => theta1 z τ) (ζ - u q) := hθ'c.comp hsub
  have hQu : Continuous fun ζ : ℂ => Q (Function.update u p ζ) := hQ.comp hu
  have hRu : Continuous fun ζ : ℂ => R (Function.update u p ζ) := hR.comp hu
  have hφc : Continuous fun ζ : ℂ => c * 3 * deriv (fun z => theta1 z τ) (ζ - u q) * Q (Function.update u p ζ) +
      theta1 (ζ - u q) τ * R (Function.update u p ζ) :=
    ((continuous_const.mul hθ2).mul hQu).add (hθ1.mul hRu)
  have hT : Filter.Tendsto (fun ζ : ℂ => ζ - u q) (nhdsWithin (u q) {u q}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    have hmaps : Set.MapsTo (fun ζ : ℂ => ζ - u q) ({u q}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) := fun ζ hζ => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hζ ⊢
      exact sub_ne_zero.2 hζ
    have h := (hsub.continuousWithinAt (s := {u q}ᶜ) (x := u q)).tendsto_nhdsWithin hmaps
    simpa using h
  have hev : ∀ᶠ ζ in nhdsWithin (u q) {u q}ᶜ, c * 3 * deriv (fun z => theta1 z τ) (ζ - u q) *
      Q (Function.update u p ζ) + theta1 (ζ - u q) τ * R (Function.update u p ζ) = 0 := by
    filter_upwards [hT.eventually (not_mem_Λu_punctured_dev τ (zero_mem_Λu_dev τ))] with ζ hζ
    have h := hrel (Function.update u p ζ)
      (by rw [Function.update_of_ne hpq.symm, Function.update_of_ne hpx.symm, h2]) (by
        rw [Function.update_self, Function.update_of_ne hpq.symm, Ne, theta1_eq_zero_iff]
        exact hζ)
    rwa [Function.update_self, Function.update_of_ne hpq.symm] at h
  have hlim := (hφc.continuousAt (x := u q)).tendsto.mono_left (nhdsWithin_le_nhds (s := ({u q}ᶜ : Set ℂ)))
  have h0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun ζ hζ => hζ.symm))
  have hupd : Function.update u p (u q) = u := by
    rw [← h1]
    exact Function.update_eq_self p u
  simp only [sub_self, hupd, (theta1_eq_zero_iff τ 0).2 (zero_mem_Λu_dev τ), zero_mul, add_zero] at h0
  have hne : c * 3 * deriv (fun z => theta1 z τ) 0 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc three_ne_zero) (theta1_deriv_zero_ne_zero τ)
  exact (mul_eq_zero.1 h0).resolve_left hne

theorem order4_dev (τ : ℍ) {n m : ℕ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ} (hao : IsOsgood a)
    (r : Fin (n + m) → ℂ) {p q x : Fin ((n + 1) + (m + 1))} (hpq : p ≠ q) (hpx : p ≠ x) (hqx : q ≠ x)
    (i : Fin (n + m)) (hp : ∀ w, mergePt w r p = w) (hx : ∀ w, mergePt w r x = w)
    (hq : ∀ w, mergePt w r q = r i) (hvan : VanishesAlong τ a p q 3)
    (hC2 : ∀ u : Fin ((n + 1) + (m + 1)) → ℂ, u q = u x → relDeriv a q x u = 0) :
    ∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ (r i) ∧ ∀ᶠ w in nhds (r i), a (mergePt w r) = (w - r i) ^ 4 * g₁ w := by
  obtain ⟨Q, hQ, hfac⟩ := div_theta1_pow_dev τ hao hpq 3 hvan
  have hrelQ : ∀ u : Fin ((n + 1) + (m + 1)) → ℂ, u q = u x → theta1 (u p - u q) τ ≠ 0 →
      -1 * 3 * deriv (fun z => theta1 z τ) (u p - u q) * Q u + theta1 (u p - u q) τ * relDeriv Q q x u = 0 := by
    intro u h1 h2
    have h := hC2 u h1
    rw [show a = fun v => theta1 (v p - v q) τ ^ 3 * Q v from funext hfac,
      relDeriv_theta_cube_dev τ hQ hpq hpx hqx u] at h
    have hm : theta1 (u p - u q) τ ^ 2 * (-1 * 3 * deriv (fun z => theta1 z τ) (u p - u q) * Q u +
        theta1 (u p - u q) τ * relDeriv Q q x u) = 0 := by linear_combination h
    exact (mul_eq_zero.1 hm).resolve_left (pow_ne_zero 2 h2)
  have hR : Continuous fun u => relDeriv Q q x u := by
    have h1 := continuous_iteratedDeriv_slice_dev hQ q 1
    have h2 := continuous_iteratedDeriv_slice_dev hQ x 1
    simp only [iteratedDeriv_one] at h1 h2
    exact h1.sub h2
  have hQ0 : Q (mergePt (r i) r) = 0 :=
    triple_zero_dev τ hQ.1 hR hpq hpx (-1) (by norm_num) hrelQ (mergePt (r i) r) (by rw [hp, hq]) (by rw [hq, hx])
  obtain ⟨h₁, hh₁, _, hevh⟩ := theta1_sub_factor_dev τ (c := r i) (z₀ := r i)
    (by rw [sub_self]; exact (theta1_eq_zero_iff τ 0).2 (zero_mem_Λu_dev τ))
  obtain ⟨q₁, hq₁, hevq⟩ := slice_factor_dev (differentiable_mergePt_dev hQ r) (z₀ := r i) (k := 1)
    (fun j hj => by
      have : j = 0 := by omega
      subst this
      simpa using hQ0)
  refine ⟨fun w => h₁ w ^ 3 * q₁ w, (hh₁.pow 3).mul hq₁, ?_⟩
  filter_upwards [hevh, hevq] with w h1 h2
  rw [hfac, hp, hq, h1, h2]
  ring

theorem const_of_root_mult_dev (τ : ℍ) {A : ℂ → ℂ} (hA : Differentiable ℂ A) {N : ℕ} (hN : N ≠ 0) {α β : ℂ}
    (hα : α ^ N = 1) (hβ : β ^ N = 1) (h1 : ∀ z, A (z + 1) = α * A z) (hτ : ∀ z, A (z + τ) = β * A z)
    (z z' : ℂ) : A z = A z' := by
  have hk1 : ∀ k : ℕ, ∀ z, A (z + k) = α ^ k * A z := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [show z + ((k + 1 : ℕ) : ℂ) = (z + k) + 1 by push_cast; ring, h1, ih, pow_succ]
      ring
  have hkτ : ∀ k : ℕ, ∀ z, A (z + k * τ) = β ^ k * A z := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [show z + ((k + 1 : ℕ) : ℂ) * τ = (z + k * τ) + τ by push_cast; ring, hτ, ih, pow_succ]
      ring
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hB : (fun z => A (N * z)) ∈ thetaSpace τ 0 0 0 := by
    refine ⟨hA.comp ((differentiable_const _).mul differentiable_id), fun U => ?_, fun U => ?_⟩
    · show A (N * (U + 1)) = cexp (2 * π * I * ((0 : ℝ) : ℂ)) * A (N * U)
      rw [show (N : ℂ) * (U + 1) = N * U + N by ring, hk1, hα]
      simp
    · show A (N * (U + τ)) = cexp (-2 * π * I * ((0 : ℝ) : ℂ)) * cexp (-π * I * ((0 : ℕ) : ℂ) * (2 * U + τ)) *
        A (N * U)
      rw [show (N : ℂ) * (U + τ) = N * U + N * τ by ring, hkτ, hβ]
      simp
  have h := thetaSpace_zero_const_dev τ hB (z / N) (z' / N)
  simp only [mul_div_cancel₀ _ hNc] at h
  exact h

theorem order4_shift_dev {G β : ℂ → ℂ} (hβ : Differentiable ℂ β) (hβ0 : ∀ w, β w ≠ 0) {c : ℂ}
    (hG : ∀ w, G (w + c) = β w * G w) (z : ℂ) :
    (∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ z ∧ ∀ᶠ w in nhds z, G w = (w - z) ^ 4 * g₁ w) ↔
      (∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ (z + c) ∧ ∀ᶠ w in nhds (z + c), G w = (w - (z + c)) ^ 4 * g₁ w) := by
  constructor
  · rintro ⟨g₁, hg₁, hev⟩
    have hsub : AnalyticAt ℂ (fun w : ℂ => w - c) (z + c) := by fun_prop
    have hg₁' : AnalyticAt ℂ g₁ ((fun w : ℂ => w - c) (z + c)) := by simpa using hg₁
    refine ⟨fun w => β (w - c) * g₁ (w - c), ((hβ.analyticAt _).comp hsub).mul (AnalyticAt.comp (f := fun w : ℂ => w - c) (x := z + c) hg₁' hsub), ?_⟩
    have hT : Filter.Tendsto (fun w : ℂ => w - c) (nhds (z + c)) (nhds z) :=
      (continuous_sub_right c).tendsto' (z + c) z (by ring)
    filter_upwards [hT.eventually hev] with w hw
    have h := hG (w - c)
    rw [sub_add_cancel] at h
    rw [h, hw]
    ring
  · rintro ⟨g₁, hg₁, hev⟩
    have hadd : AnalyticAt ℂ (fun w : ℂ => w + c) z := by fun_prop
    refine ⟨fun w => (β w)⁻¹ * g₁ (w + c), ((hβ.analyticAt z).inv (hβ0 z)).mul (AnalyticAt.comp (f := fun w : ℂ => w + c) (x := z) hg₁ hadd), ?_⟩
    have hT : Filter.Tendsto (fun w : ℂ => w + c) (nhds z) (nhds (z + c)) :=
      (by fun_prop : Continuous fun w : ℂ => w + c).tendsto z
    filter_upwards [hT.eventually hev] with w hw
    have h := hG w
    rw [hw] at h
    have hb := hβ0 w
    field_simp
    linear_combination -h

/-- The quotient of `g` by `h`, extended at the zeros of `h` by its limit. -/
def divqg_dev (g h : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h z = 0 then Filter.limUnder (nhdsWithin z {z}ᶜ) (fun w => g w / h w) else g z / h z

theorem divqg_spec_dev {g h : ℂ → ℂ} (hg : Differentiable ℂ g) (hh : Differentiable ℂ h)
    (hloc : ∀ z₀, h z₀ = 0 → ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ z₀ ∧ (∀ᶠ z in nhds z₀, g z = h z * φ z) ∧
      ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, h z ≠ 0) :
    Differentiable ℂ (divqg_dev g h) ∧ ∀ z, g z = h z * divqg_dev g h z := by
  have hpt : ∀ z₀, DifferentiableAt ℂ (divqg_dev g h) z₀ ∧ g z₀ = h z₀ * divqg_dev g h z₀ := by
    intro z₀
    by_cases h0 : h z₀ = 0
    · obtain ⟨φ, hφ, hgφ, hne⟩ := hloc z₀ h0
      have hpunct : ∀ᶠ w in nhdsWithin z₀ {z₀}ᶜ, g w / h w = φ w := by
        filter_upwards [hgφ.filter_mono nhdsWithin_le_nhds, hne] with w h1 h2
        rw [h1, mul_div_cancel_left₀ _ h2]
      have hlim : Filter.Tendsto (fun w => g w / h w) (nhdsWithin z₀ {z₀}ᶜ) (nhds (φ z₀)) :=
        (hφ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hpunct.mono fun w hw => hw.symm)
      have hz : divqg_dev g h z₀ = φ z₀ := by
        rw [divqg_dev, ite_eq_left h0]
        exact hlim.limUnder_eq
      have hpunct' : ∀ᶠ w in nhdsWithin z₀ {z₀}ᶜ, divqg_dev g h w = φ w := by
        filter_upwards [hpunct, hne] with w h1 h2
        rw [divqg_dev, ite_eq_right h2, h1]
      have hev : divqg_dev g h =ᶠ[nhds z₀] φ := by
        have h' := Filter.eventually_sup.2 ⟨hpunct', Filter.eventually_pure.2 hz⟩
        rwa [nhdsNE_sup_pure] at h'
      refine ⟨hφ.differentiableAt.congr_of_eventuallyEq hev, ?_⟩
      rw [hz]
      exact hgφ.self_of_nhds
    · have hne : ∀ᶠ w in nhds z₀, h w ≠ 0 := hh.continuous.continuousAt.eventually_ne h0
      have hev : divqg_dev g h =ᶠ[nhds z₀] fun w => g w / h w := by
        filter_upwards [hne] with w hw
        rw [divqg_dev, ite_eq_right hw]
      refine ⟨((hg z₀).div (hh z₀) h0).congr_of_eventuallyEq hev, ?_⟩
      rw [hev.self_of_nhds, mul_div_cancel₀ _ h0]
  exact ⟨fun z => (hpt z).1, fun z => (hpt z).2⟩

/-- **Lemma C.C(a)**: "`for $\mathrm{rest}$ outside the divisors $\{x_a-y_k\in\Lambda_u\}$ ($a,k\ge2$), $w\mapsto\mathcal A(w;\mathrm{rest})$ is entire`"
— in numerator form: off the up–down divisors of `rest`, `w ↦ 𝖺|_M/(ϑ₁'(0)² E)` extends from the admissible centres
to an entire function (Steps 1, 2 and 4: `𝖺|_M` vanishes to order `≥ 4` at `w = x_a` and at `w = y_k`, "`Then $\mathsf a|_M=\kzvth_1(w-x_a)^3Q_M=-\kzvth_1(w-x_a)^4\widetilde Q_M$, which has order $\ge4$.`"). -/
theorem lemC_a (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) (r : Fin (n + m) → ℂ)
    (hr : ∀ (b : Fin n) (k : Fin m), r (Fin.castAdd m b) - r (Fin.natAdd n k) ∉ Λu τ) :
    ∃ A : ℂ → ℂ, Differentiable ℂ A ∧ ∀ w, (∀ i, w - r i ∉ Λu τ) → A w = mergeAt τ a w r := by
  have hao : IsOsgood a := ha.1
  obtain ⟨_, _, ha1, haτ, _, hC1, hC2⟩ := ha
  have hGd : Differentiable ℂ fun w => a (mergePt w r) := differentiable_mergePt_dev hao r
  have hc0 : deriv (fun z => theta1 z τ) 0 ^ 2 ≠ 0 := pow_ne_zero 2 (theta1_deriv_zero_ne_zero τ)
  suffices hq : ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ w, a (mergePt w r) = Emerge τ w r * q w by
    obtain ⟨q, hqd, hq⟩ := hq
    refine ⟨fun w => q w / deriv (fun z => theta1 z τ) 0 ^ 2, hqd.div_const _, fun w hw => ?_⟩
    have hE : Emerge (τ : ℂ) w r ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ =>
      pow_ne_zero 4 fun h0 => hw i ((theta1_eq_zero_iff τ _).1 h0)
    unfold mergeAt
    rw [hq w]
    field_simp
  by_cases hG0 : ∀ w, a (mergePt w r) = 0
  · exact ⟨fun _ => 0, differentiable_const 0, fun w => by rw [hG0 w, mul_zero]⟩
  push Not at hG0
  obtain ⟨w₁, hw₁⟩ := hG0
  -- the variables of `rest` are distinct modulo `Λ_u`
  have hdist : ∀ i j : Fin (n + m), i ≠ j → r i - r j ∉ Λu τ := by
    intro i j hij hl
    apply hw₁
    induction i using Fin.addCases with
    | left b =>
      induction j using Fin.addCases with
      | left b' =>
        have hbb : b ≠ b' := fun h => hij (by rw [h])
        have hb1 := b.isLt
        have hb2 := b'.isLt
        refine zero_of_coincide_dev τ hC1 (s := Fin.castAdd (m + 1) b.succ) (t := Fin.castAdd (m + 1) b'.succ)
          ?_ ?_ _ ?_
        · intro h
          exact hbb (Fin.succ_injective _ (Fin.castAdd_injective _ _ h))
        · simp only [SameSpecies, Fin.val_castAdd, Fin.val_succ]
          constructor <;> intro _ <;> omega
        · simpa [mergePt] using hl
      | right k => exact absurd hl (hr b k)
    | right k =>
      induction j using Fin.addCases with
      | left b =>
        refine absurd ?_ (hr b k)
        rw [show r (Fin.castAdd m b) - r (Fin.natAdd n k) = -(r (Fin.natAdd n k) - r (Fin.castAdd m b)) by ring]
        exact neg_mem_Λu_dev τ hl
      | right k' =>
        have hkk : k ≠ k' := fun h => hij (by rw [h])
        refine zero_of_coincide_dev τ hC1 (s := Fin.natAdd (n + 1) k.succ) (t := Fin.natAdd (n + 1) k'.succ)
          ?_ ?_ _ ?_
        · intro h
          exact hkk (Fin.succ_injective _ (Fin.natAdd_injective _ _ h))
        · simp only [SameSpecies, Fin.val_natAdd, Fin.val_succ]
          constructor <;> intro _ <;> omega
        · simpa [mergePt] using hl
  -- the multipliers of `𝖺|_M` in `w`
  have hG1 : ∀ w, a (mergePt (w + 1) r) = ε.1 ^ 2 * a (mergePt w r) := fun w => mergePt_add_one_dev ha1 w r
  have hGτ := fun w => mergePt_add_tau_dev τ haτ w r
  have hε1 : ε.1 ≠ 0 := fun h => hw₁ (by
    have := hG1 (w₁ - 1)
    rwa [sub_add_cancel, h, zero_pow two_ne_zero, zero_mul] at this)
  have hε2 : ε.2 ≠ 0 := fun h => hw₁ (by
    have := hGτ (w₁ - τ)
    rwa [sub_add_cancel, h, zero_pow two_ne_zero, zero_mul, zero_mul] at this)
  -- the order `≥ 4` along `rest + Λ_u`
  have hP1 := order4_shift_dev (G := fun w => a (mergePt w r)) (differentiable_const (ε.1 ^ 2))
    (fun _ => pow_ne_zero 2 hε1) (c := 1) hG1
  have hPτ := order4_shift_dev (G := fun w => a (mergePt w r))
    (β := fun w => ε.2 ^ 2 * cexp (-4 * π * I * τ * ((n + m : ℕ) : ℂ) - 8 * π * I * (((n + m : ℕ) : ℂ) * w - ∑ i, r i)))
    (by fun_prop) (fun _ => mul_ne_zero (pow_ne_zero 2 hε2) (Complex.exp_ne_zero _)) (c := τ) hGτ
  have hPi : ∀ i : Fin (n + m), ∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ (r i) ∧
      ∀ᶠ w in nhds (r i), a (mergePt w r) = (w - r i) ^ 4 * g₁ w := by
    intro i
    induction i using Fin.addCases with
    | left b =>
      have hb := b.isLt
      refine order4_dev τ hao r (p := Fin.castAdd (m + 1) 0) (q := Fin.castAdd (m + 1) b.succ)
        (x := Fin.natAdd (n + 1) 0) ?_ ?_ ?_ (Fin.castAdd m b) (fun w => mergePt_s0_dev w r)
        (fun w => mergePt_t0_dev w r) (fun w => by simp [mergePt]) (hC1 _ _ ?_ ?_) (fun u hu => hC2 _ _ ?_ ?_ u hu)
      · intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_zero, Fin.val_succ] at this
        omega
      · exact castAdd_ne_natAdd_dev _ _
      · exact castAdd_ne_natAdd_dev _ _
      · rw [Fin.lt_def]
        simp only [Fin.val_castAdd, Fin.val_zero, Fin.val_succ]
        omega
      · simp only [SameSpecies, Fin.val_castAdd, Fin.val_zero, Fin.val_succ]
        constructor <;> intro _ <;> omega
      · simp only [Fin.val_castAdd, Fin.val_succ]
        omega
      · simp only [Fin.val_natAdd, Fin.val_zero]
        omega
    | right k =>
      have hk := k.isLt
      refine order4_dev τ hao r (p := Fin.natAdd (n + 1) 0) (q := Fin.natAdd (n + 1) k.succ)
        (x := Fin.castAdd (m + 1) 0) ?_ ?_ ?_ (Fin.natAdd n k) (fun w => mergePt_t0_dev w r)
        (fun w => mergePt_s0_dev w r) (fun w => by simp [mergePt]) (hC1 _ _ ?_ ?_) (fun u hu => ?_)
      · intro h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_zero, Fin.val_succ] at this
        omega
      · exact (castAdd_ne_natAdd_dev _ _).symm
      · exact (castAdd_ne_natAdd_dev _ _).symm
      · rw [Fin.lt_def]
        simp only [Fin.val_natAdd, Fin.val_zero, Fin.val_succ]
        omega
      · simp only [SameSpecies, Fin.val_natAdd, Fin.val_zero, Fin.val_succ]
        constructor <;> intro _ <;> omega
      · have h := hC2 (Fin.castAdd (m + 1) 0) (Fin.natAdd (n + 1) k.succ)
          (by simp only [Fin.val_castAdd, Fin.val_zero]; omega)
          (by simp only [Fin.val_natAdd, Fin.val_succ]; omega) u hu.symm
        unfold relDeriv at h ⊢
        linear_combination -h
  have hPall : ∀ i : Fin (n + m), ∀ l ∈ Λu τ, ∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ (r i + l) ∧
      ∀ᶠ w in nhds (r i + l), a (mergePt w r) = (w - (r i + l)) ^ 4 * g₁ w := fun i =>
    lattice_closed_dev τ (P := fun z => ∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ z ∧
      ∀ᶠ w in nhds z, a (mergePt w r) = (w - z) ^ 4 * g₁ w)
      (fun z => (hP1 z).1) (fun z => (hP1 z).2) (fun z => (hPτ z).1) (fun z => (hPτ z).2) (hPi i)
  -- the division by `E` in `w`
  have hEd : Differentiable ℂ fun w => Emerge (τ : ℂ) w r :=
    differentiable_finsetProd_dev _ fun j _ => ((theta1_differentiable τ).comp (differentiable_id.sub_const _)).pow 4
  have hloc : ∀ z₀, Emerge (τ : ℂ) z₀ r = 0 → ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ z₀ ∧
      (∀ᶠ z in nhds z₀, a (mergePt z r) = Emerge (τ : ℂ) z r * φ z) ∧
      ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, Emerge (τ : ℂ) z r ≠ 0 := by
    intro z₀ hz₀
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hz₀
    have hθ0 : theta1 (z₀ - r i) τ = 0 := pow_eq_zero_iff (n := 4) (by norm_num) |>.1 hi
    have hl : z₀ - r i ∈ Λu τ := (theta1_eq_zero_iff τ _).1 hθ0
    obtain ⟨g₁, hg₁, hevg⟩ := hPall i _ hl
    rw [add_sub_cancel] at hg₁ hevg
    obtain ⟨h₁, hh₁, hne₁, hevh⟩ := theta1_sub_factor_dev τ (c := r i) hθ0
    have hPrd : Differentiable ℂ fun w => ∏ j ∈ Finset.univ.erase i, theta1 (w - r j) τ ^ 4 :=
      differentiable_finsetProd_dev _ fun j _ => ((theta1_differentiable τ).comp (differentiable_id.sub_const _)).pow 4
    have hPr0 : ∏ j ∈ Finset.univ.erase i, theta1 (z₀ - r j) τ ^ 4 ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero 4 fun h0 => ?_
      have hlj := (theta1_eq_zero_iff τ _).1 h0
      refine hdist i j (Ne.symm (Finset.ne_of_mem_erase hj)) (mem_Λu_of_add_dev τ hl ?_)
      rwa [show r i - r j + (z₀ - r i) = z₀ - r j by ring]
    have hE : ∀ w, Emerge (τ : ℂ) w r = theta1 (w - r i) τ ^ 4 * ∏ j ∈ Finset.univ.erase i, theta1 (w - r j) τ ^ 4 :=
      fun w => (Finset.mul_prod_erase _ (fun j => theta1 (w - r j) τ ^ 4) (Finset.mem_univ i)).symm
    have hH : AnalyticAt ℂ (fun w => h₁ w ^ 4 * ∏ j ∈ Finset.univ.erase i, theta1 (w - r j) τ ^ 4) z₀ :=
      (hh₁.pow 4).mul (hPrd.analyticAt z₀)
    have hH0 : h₁ z₀ ^ 4 * ∏ j ∈ Finset.univ.erase i, theta1 (z₀ - r j) τ ^ 4 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 4 hne₁) hPr0
    have hnh : ∀ᶠ w in nhds z₀, h₁ w ^ 4 * ∏ j ∈ Finset.univ.erase i, theta1 (w - r j) τ ^ 4 ≠ 0 :=
      hH.continuousAt.eventually_ne hH0
    refine ⟨fun w => g₁ w * (h₁ w ^ 4 * ∏ j ∈ Finset.univ.erase i, theta1 (w - r j) τ ^ 4)⁻¹,
      hg₁.mul (hH.inv hH0), ?_, ?_⟩
    · filter_upwards [hevg, hevh, hnh] with w h1 h2 h3
      rw [h1, hE, h2]
      have h4 := mul_inv_cancel₀ h3
      linear_combination (-(w - z₀) ^ 4 * g₁ w) * h4
    · filter_upwards [hevh.filter_mono nhdsWithin_le_nhds, hnh.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with w h2 h3 h5
      rw [hE, h2, mul_pow, mul_assoc]
      exact mul_ne_zero (pow_ne_zero 4 (sub_ne_zero.2 h5)) h3
  obtain ⟨hqd, hq⟩ := divqg_spec_dev hGd hEd hloc
  exact ⟨_, hqd, hq⟩

/-- **Lemma C.C(b)**: "`$\mathcal A(w+1;\cdot)=\varepsilon_1^2\mathcal A(w;\cdot)$ and $\mathcal A(w+\tau;\cdot)=\varepsilon_2^2\mathcal A(w;\cdot)$`"
— for the merged numerator at admissible centres (the factors `E` and `𝖺|_M` change together under `w ↦ w + τ`); in
the Lean the identity holds at every centre, both sides vanishing at a non-admissible one, so the hypothesis `_hw` is
not used by the proof and records the paper's scope. -/
theorem lemC_b (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) (r : Fin (n + m) → ℂ) {w : ℂ} (_hw : ∀ i, w - r i ∉ Λu τ) :
    mergeAt τ a (w + 1) r = ε.1 ^ 2 * mergeAt τ a w r ∧ mergeAt τ a (w + τ) r = ε.2 ^ 2 * mergeAt τ a w r := by
  obtain ⟨_, _, ha1, haτ, _, _, _⟩ := ha
  have hst : Fin.castAdd (m + 1) (0 : Fin (n + 1)) ≠ Fin.natAdd (n + 1) (0 : Fin (m + 1)) := castAdd_ne_natAdd_dev _ _
  constructor
  · have e : mergePt (w + 1) r =
        Function.update (Function.update (mergePt w r) (Fin.castAdd (m + 1) 0)
          (mergePt w r (Fin.castAdd (m + 1) 0) + 1)) (Fin.natAdd (n + 1) 0)
          (Function.update (mergePt w r) (Fin.castAdd (m + 1) 0) (mergePt w r (Fin.castAdd (m + 1) 0) + 1)
            (Fin.natAdd (n + 1) 0) + 1) := by
      rw [Function.update_of_ne hst.symm, mergePt_s0_dev, mergePt_t0_dev]
      exact mergePt_shift_dev w 1 r
    unfold mergeAt
    rw [e, ha1, ha1, Emerge_add_one_dev]
    ring
  · unfold mergeAt
    rw [mergePt_add_tau_dev τ haτ w r, Emerge_add_tau_dev]
    rw [show ε.2 ^ 2 * cexp (-4 * π * I * τ * ((n + m : ℕ) : ℂ) - 8 * π * I * (((n + m : ℕ) : ℂ) * w - ∑ i, r i)) *
        a (mergePt w r) = cexp (-4 * π * I * τ * ((n + m : ℕ) : ℂ) - 8 * π * I * (((n + m : ℕ) : ℂ) * w - ∑ i, r i)) *
          (ε.2 ^ 2 * a (mergePt w r)) by ring,
      show deriv (fun z => theta1 z ↑τ) 0 ^ 2 * (cexp (-4 * π * I * τ * ((n + m : ℕ) : ℂ) -
        8 * π * I * (((n + m : ℕ) : ℂ) * w - ∑ i, r i)) * Emerge (↑τ) w r) =
          cexp (-4 * π * I * τ * ((n + m : ℕ) : ℂ) - 8 * π * I * (((n + m : ℕ) : ℂ) * w - ∑ i, r i)) *
            (deriv (fun z => theta1 z ↑τ) 0 ^ 2 * Emerge (↑τ) w r) by ring,
      mul_div_mul_left _ _ (Complex.exp_ne_zero _)]
    ring

/-- **Lemma C.C(c)**: "`$\mathcal A$ does not depend on $w$, and $\mathcal A\equiv0$ unless $\varepsilon_1^2=\varepsilon_2^2=1$`"
— the independence of the admissible centre, at every `rest` (the proof: "`So it is bounded and therefore constant.`",
then "`These $\mathrm{rest}$ form a dense open set`"). -/
theorem lemC_c_indep (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) (r : Fin (n + m) → ℂ) {w w' : ℂ} (hw : ∀ i, w - r i ∉ Λu τ)
    (hw' : ∀ i, w' - r i ∉ Λu τ) : mergeAt τ a w r = mergeAt τ a w' r := by
  by_cases hroot : ε.1 ^ ((n + 1) + (m + 1)) = 1 ∧ ε.2 ^ ((n + 1) + (m + 1)) = 1
  swap
  · have ha0 : a = 0 := by
      have hb := Gnum_eq_bot_of_not_root τ (n + 1) (m + 1) hroot
      have h0 : a ∈ (⊥ : Submodule ℂ ((Fin ((n + 1) + (m + 1)) → ℂ) → ℂ)) := hb ▸ ha
      exact (Submodule.mem_bot ℂ).1 h0
    subst ha0
    simp [mergeAt]
  have hN : (n + 1) + (m + 1) ≠ 0 := by omega
  have hao : IsOsgood a := ha.1
  have hc0 : deriv (fun z => theta1 z τ) 0 ^ 2 ≠ 0 := pow_ne_zero 2 (theta1_deriv_zero_ne_zero τ)
  -- generic `rest`: the extension of Lemma C.C(a) is constant
  have hgen : ∀ r' : Fin (n + m) → ℂ, (∀ (b : Fin n) (k : Fin m), r' (Fin.castAdd m b) - r' (Fin.natAdd n k) ∉ Λu τ) →
      ∀ z₁ z₂ : ℂ, (∀ i, z₁ - r' i ∉ Λu τ) → (∀ i, z₂ - r' i ∉ Λu τ) →
        mergeAt τ a z₁ r' = mergeAt τ a z₂ r' := by
    intro r' hr' z₁ z₂ hz₁ hz₂
    obtain ⟨A, hAd, hA⟩ := lemC_a τ ha r' hr'
    have hS : (⋃ i, (fun l => r' i + l) '' Λu τ).Countable :=
      Set.countable_iUnion fun i => (Λu_countable_dev τ).image _
    have hadm : ∀ z ∈ (⋃ i, (fun l => r' i + l) '' Λu τ)ᶜ, ∀ i, z - r' i ∉ Λu τ := fun z hz i hl =>
      hz (Set.mem_iUnion.2 ⟨i, ⟨z - r' i, hl, add_sub_cancel _ _⟩⟩)
    have hshift : ∀ c : ℂ, c ∈ Λu τ → ∀ z, (∀ i, z - r' i ∉ Λu τ) → ∀ i, z + c - r' i ∉ Λu τ :=
      fun c hc z hz i hl => hz i (mem_Λu_of_add_dev τ hc (by rwa [show z - r' i + c = z + c - r' i by ring]))
    have hA1 : ∀ z, A (z + 1) = ε.1 ^ 2 * A z := by
      have h := Continuous.ext_on (hS.dense_compl ℂ)
        ((hAd.comp (differentiable_id.add_const 1)).continuous) (continuous_const.mul hAd.continuous)
        fun z hz => by
          have hz' := hadm z hz
          show A (z + 1) = ε.1 ^ 2 * A z
          rw [hA _ (hshift 1 (one_mem_Λu_dev τ) z hz'), hA z hz', (lemC_b τ ha r' hz').1]
      exact fun z => congrFun h z
    have hAτ : ∀ z, A (z + τ) = ε.2 ^ 2 * A z := by
      have h := Continuous.ext_on (hS.dense_compl ℂ)
        ((hAd.comp (differentiable_id.add_const (τ : ℂ))).continuous) (continuous_const.mul hAd.continuous)
        fun z hz => by
          have hz' := hadm z hz
          show A (z + τ) = ε.2 ^ 2 * A z
          rw [hA _ (hshift τ (tau_mem_Λu_dev τ) z hz'), hA z hz', (lemC_b τ ha r' hz').2]
      exact fun z => congrFun h z
    have hc := const_of_root_mult_dev τ hAd hN (α := ε.1 ^ 2) (β := ε.2 ^ 2)
      (by rw [← pow_mul, mul_comm, pow_mul, hroot.1, one_pow])
      (by rw [← pow_mul, mul_comm, pow_mul, hroot.2, one_pow]) hA1 hAτ
    rw [← hA z₁ hz₁, ← hA z₂ hz₂]
    exact hc z₁ z₂
  -- every `rest`, by continuity
  have hPne : ∀ p ∈ Finset.univ.image (fun bk : Fin n × Fin m => (Fin.castAdd m bk.1, Fin.natAdd n bk.2)),
      p.1 ≠ p.2 := by
    intro p hp
    obtain ⟨⟨b, k⟩, -, rfl⟩ := Finset.mem_image.1 hp
    exact castAdd_ne_natAdd_dev b k
  have hdense := dense_generic_dev τ _ hPne
  have hev : ∀ᶠ r'' in nhds r, (∀ i, w - r'' i ∉ Λu τ) ∧ (∀ i, w' - r'' i ∉ Λu τ) := by
    refine (Filter.eventually_all.2 fun i => ?_).and (Filter.eventually_all.2 fun i => ?_)
    · exact ((by fun_prop : Continuous fun r'' : Fin (n + m) → ℂ => w - r'' i).tendsto r).eventually
        (not_mem_Λu_nhds_dev τ (hw i))
    · exact ((by fun_prop : Continuous fun r'' : Fin (n + m) → ℂ => w' - r'' i).tendsto r).eventually
        (not_mem_Λu_nhds_dev τ (hw' i))
  have hcont : ∀ z, (∀ i, z - r i ∉ Λu τ) → ContinuousAt (fun r'' => mergeAt τ a z r'') r := by
    intro z hz
    have hE : Emerge (τ : ℂ) z r ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ =>
      pow_ne_zero 4 fun h0 => hz i ((theta1_eq_zero_iff τ _).1 h0)
    have hEc : Continuous fun r'' : Fin (n + m) → ℂ => Emerge (τ : ℂ) z r'' :=
      continuous_finsetProd _ fun i _ =>
        ((theta1_differentiable τ).continuous.comp (continuous_const.sub (continuous_apply i))).pow 4
    exact ((isOsgood_mergePt_dev hao z).1.continuousAt).div (continuousAt_const.mul hEc.continuousAt)
      (mul_ne_zero hc0 hE)
  have hφ : ContinuousAt (fun r'' => mergeAt τ a w r'' - mergeAt τ a w' r'') r := (hcont w hw).sub (hcont w' hw')
  have hfreq : ∃ᶠ r'' in nhds r, (fun r'' => mergeAt τ a w r'' - mergeAt τ a w' r'') r'' ∈ ({0} : Set ℂ) := by
    have h1 := mem_closure_iff_frequently.1 (hdense r)
    refine (h1.and_eventually hev).mono fun r'' hr'' => ?_
    obtain ⟨hg, hw1, hw2⟩ := hr''
    have hgr : ∀ (b : Fin n) (k : Fin m), r'' (Fin.castAdd m b) - r'' (Fin.natAdd n k) ∉ Λu τ := fun b k =>
      hg _ (Finset.mem_image.2 ⟨(b, k), Finset.mem_univ _, rfl⟩)
    show mergeAt τ a w r'' - mergeAt τ a w' r'' ∈ ({0} : Set ℂ)
    rw [hgen r'' hgr w w' hw1 hw2, sub_self]
    exact Set.mem_singleton 0
  have h0 := isClosed_singleton.mem_of_frequently_of_tendsto hfreq hφ
  exact sub_eq_zero.1 h0

/-- **Lemma C.C(c)**: "`$\mathcal A$ does not depend on $w$, and $\mathcal A\equiv0$ unless $\varepsilon_1^2=\varepsilon_2^2=1$`"
— the vanishing ("`If it is nonzero, $\mathcal A=\varepsilon_1^2\mathcal A=\varepsilon_2^2\mathcal A$ forces $\varepsilon_1^2=\varepsilon_2^2=1$.`"). -/
theorem lemC_c_zero (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) (hε : ¬ (ε.1 ^ 2 = 1 ∧ ε.2 ^ 2 = 1)) : mu τ a = 0 := by
  funext r
  show mergeAt τ a (admW τ r) r = 0
  have hw := admW_spec_dev τ r
  have hw1 : ∀ i, admW τ r + 1 - r i ∉ Λu τ := fun i h => hw i (mem_Λu_of_add_dev τ (one_mem_Λu_dev τ)
    (by rwa [show admW τ r - r i + 1 = admW τ r + 1 - r i by ring]))
  have hwτ : ∀ i, admW τ r + τ - r i ∉ Λu τ := fun i h => hw i (mem_Λu_of_add_dev τ (tau_mem_Λu_dev τ)
    (by rwa [show admW τ r - r i + τ = admW τ r + τ - r i by ring]))
  obtain ⟨hb1, hbτ⟩ := lemC_b τ ha r hw
  have hi1 := lemC_c_indep τ ha r hw1 hw
  have hiτ := lemC_c_indep τ ha r hwτ hw
  by_contra hne
  apply hε
  constructor
  · have h' : (ε.1 ^ 2 - 1) * mergeAt τ a (admW τ r) r = 0 := by linear_combination hi1 - hb1
    rcases mul_eq_zero.1 h' with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hne
  · have h' : (ε.2 ^ 2 - 1) * mergeAt τ a (admW τ r) r = 0 := by linear_combination hiτ - hbτ
    rcases mul_eq_zero.1 h' with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hne

/-! ### Proof devices for Lemma C.C(d) (proof phase, round two; not statements of the paper)

The position `mIdx_dev i` of a variable of `rest` keeps its species and its order (`mIdx_val_dev`); the merge commutes
with the translations, the transpositions and the shifts of one variable of `rest` (`mergePt_add_const_dev`,
`mergePt_swap_dev`, `mergePt_update_dev`), and `E` changes by the multipliers of `ϑ₁⁴` (`Emerge_*_dev`). Near any `rest`,
`μ(a)` is the merged numerator at one fixed admissible centre (`mu_local_dev`, from Lemma C.C(c)); so its regularity,
(C1) and (C2) are those of `𝖺|_M` times the nonvanishing `(ϑ₁'(0)² E)⁻¹`, which is symmetric in the variables of
`rest`. -/

theorem mIdx_val_dev {n m : ℕ} (i : Fin (n + m)) :
    ((mIdx_dev i : Fin ((n + 1) + (m + 1))) : ℕ) = if (i : ℕ) < n then (i : ℕ) + 1 else (i : ℕ) + 2 := by
  induction i using Fin.addCases with
  | left b => simp [mIdx_dev, b.isLt]
  | right k =>
    simp [mIdx_dev]
    omega

theorem mIdx_injective_dev {n m : ℕ} : Function.Injective (mIdx_dev (n := n) (m := m)) := by
  intro i j h
  have h' := congrArg Fin.val h
  rw [mIdx_val_dev, mIdx_val_dev] at h'
  apply Fin.ext
  split_ifs at h' <;> omega

theorem mIdx_lt_dev {n m : ℕ} {i j : Fin (n + m)} (h : i < j) : mIdx_dev i < mIdx_dev j := by
  rw [Fin.lt_def, mIdx_val_dev, mIdx_val_dev]
  have := Fin.lt_def.1 h
  split_ifs <;> omega

theorem mIdx_species_dev {n m : ℕ} (i : Fin (n + m)) :
    ((mIdx_dev i : Fin ((n + 1) + (m + 1))) : ℕ) < n + 1 ↔ (i : ℕ) < n := by
  rw [mIdx_val_dev]
  split_ifs <;> constructor <;> intro <;> omega

theorem swap_eq_update_dev {ι : Type*} [DecidableEq ι] (v : ι → ℂ) {i j : ι} (h : i ≠ j) :
    v ∘ Equiv.swap i j = Function.update (Function.update v i (v j)) j (v i) := by
  funext k
  by_cases hki : k = i
  · subst hki
    simp [Function.update_of_ne h, Equiv.swap_apply_left]
  · by_cases hkj : k = j
    · subst hkj
      simp [Equiv.swap_apply_right]
    · simp [Function.update_of_ne hki, Function.update_of_ne hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem mergePt_swap_dev {n m : ℕ} (w : ℂ) (r : Fin (n + m) → ℂ) {s t : Fin (n + m)} (hst : s ≠ t) :
    mergePt w (r ∘ Equiv.swap s t) = mergePt w r ∘ Equiv.swap (mIdx_dev s) (mIdx_dev t) := by
  rw [swap_eq_update_dev r hst, mergePt_update_dev, mergePt_update_dev,
    swap_eq_update_dev (mergePt w r) (mIdx_injective_dev.ne hst), mergePt_mIdx_dev, mergePt_mIdx_dev]

theorem mergePt_add_const_dev {n m : ℕ} (w c : ℂ) (r : Fin (n + m) → ℂ) :
    mergePt (w + c) (fun i => r i + c) = fun j => mergePt w r j + c := by
  funext j
  induction j using Fin.addCases with
  | left a' =>
    induction a' using Fin.cases with
    | zero => simp [mergePt]
    | succ a => simp [mergePt]
  | right b' =>
    induction b' using Fin.cases with
    | zero => simp [mergePt]
    | succ k => simp [mergePt]

theorem Emerge_ne_zero_dev (τ : ℍ) {K : ℕ} {w : ℂ} {r : Fin K → ℂ} (hw : ∀ i, w - r i ∉ Λu τ) :
    Emerge (τ : ℂ) w r ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero 4 fun h0 => hw i ((theta1_eq_zero_iff τ _).1 h0)

theorem Emerge_add_const_dev (τ : ℂ) {K : ℕ} (w c : ℂ) (r : Fin K → ℂ) :
    Emerge τ (w + c) (fun i => r i + c) = Emerge τ w r := by
  unfold Emerge
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show w + c - (r i + c) = w - r i by ring]

theorem Emerge_swap_dev (τ : ℂ) {K : ℕ} (w : ℂ) (r : Fin K → ℂ) (s t : Fin K) :
    Emerge τ w (r ∘ Equiv.swap s t) = Emerge τ w r := by
  unfold Emerge
  exact Equiv.prod_comp (Equiv.swap s t) (fun i => theta1 (w - r i) τ ^ 4)

theorem Emerge_update_dev (τ : ℂ) {K : ℕ} (w : ℂ) (r : Fin K → ℂ) (k : Fin K) (z : ℂ) :
    Emerge τ w (Function.update r k z) = theta1 (w - z) τ ^ 4 * ∏ j ∈ Finset.univ.erase k, theta1 (w - r j) τ ^ 4 := by
  unfold Emerge
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem Emerge_update_add_one_dev (τ : ℂ) {K : ℕ} (w : ℂ) (r : Fin K → ℂ) (k : Fin K) :
    Emerge τ w (Function.update r k (r k + 1)) = Emerge τ w r := by
  rw [Emerge_update_dev, ← Function.update_eq_self k r, Emerge_update_dev, Function.update_eq_self]
  rw [show w - r k = (w - (r k + 1)) + 1 by ring, theta1_add_one]
  ring

theorem Emerge_update_add_tau_dev (τ : ℂ) {K : ℕ} (w : ℂ) (r : Fin K → ℂ) (k : Fin K) :
    Emerge τ w (Function.update r k (r k + τ)) = cexp (8 * π * I * (w - r k) - 4 * π * I * τ) * Emerge τ w r := by
  rw [Emerge_update_dev, ← Function.update_eq_self k r, Emerge_update_dev, Function.update_eq_self]
  have h4 : ∀ A : ℂ, cexp A ^ 4 = cexp (4 * A) := fun A => by rw [← Complex.exp_nat_mul]; norm_num
  rw [show w - r k = (w - (r k + τ)) + τ by ring, theta1_add_tau,
    show (-cexp (-π * I * τ - 2 * π * I * (w - (r k + τ))) * theta1 (w - (r k + τ)) τ) ^ 4 =
      cexp (-π * I * τ - 2 * π * I * (w - (r k + τ))) ^ 4 * theta1 (w - (r k + τ)) τ ^ 4 by ring, h4,
    show (w - (r k + τ)) + τ = w - r k by ring]
  have he : cexp (8 * π * I * (w - r k) - 4 * π * I * τ) * cexp (4 * (-π * I * τ - 2 * π * I * (w - (r k + τ)))) = 1 := by
    rw [← Complex.exp_add, show 8 * π * I * (w - r k) - 4 * π * I * τ + 4 * (-π * I * τ - 2 * π * I * (w - (r k + τ))) =
      (0 : ℂ) by ring, Complex.exp_zero]
  linear_combination (-(theta1 (w - (r k + τ)) τ ^ 4 * ∏ j ∈ Finset.univ.erase k, theta1 (w - r j) τ ^ 4)) * he

theorem mu_local_dev (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) (r₀ : Fin (n + m) → ℂ) {w₀ : ℂ} (hw₀ : ∀ i, w₀ - r₀ i ∉ Λu τ) :
    (∀ᶠ r in nhds r₀, ∀ i, w₀ - r i ∉ Λu τ) ∧ mu τ a =ᶠ[nhds r₀] fun r => mergeAt τ a w₀ r := by
  have hev : ∀ᶠ r in nhds r₀, ∀ i, w₀ - r i ∉ Λu τ := Filter.eventually_all.2 fun i =>
    ((by fun_prop : Continuous fun r : Fin (n + m) → ℂ => w₀ - r i).tendsto r₀).eventually
      (not_mem_Λu_nhds_dev τ (hw₀ i))
  exact ⟨hev, hev.mono fun r hr => lemC_c_indep τ ha r (admW_spec_dev τ r) hr⟩

/-- **Lemma C.C(d)**: "`$\mu(g):=\mathcal A\in\kzG(n-1,m-1;\varepsilon)$`" — the merged numerator is a numerator of
`𝒢(n − 1, m − 1; ε)` (Step 6, (i)–(v); in numerator form (v) is (C2) of the quotient `𝖺|_M/E`, `E` being symmetric under
`x_a ↔ y_k`). -/
theorem lemC_d (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) : mu τ a ∈ Gnum τ n m ε := by
  have hao : IsOsgood a := ha.1
  obtain ⟨_, ha0, ha1, haτ, has, hC1, hC2⟩ := id ha
  have hc0 : deriv (fun z => theta1 z τ) 0 ^ 2 ≠ 0 := pow_ne_zero 2 (theta1_deriv_zero_ne_zero τ)
  have hEc : ∀ w : ℂ, Continuous fun r : Fin (n + m) → ℂ => Emerge (τ : ℂ) w r := fun w =>
    continuous_finsetProd _ fun i _ =>
      ((theta1_differentiable τ).continuous.comp (continuous_const.sub (continuous_apply i))).pow 4
  have hEd : ∀ (w : ℂ) (r : Fin (n + m) → ℂ) (i : Fin (n + m)),
      Differentiable ℂ fun z => Emerge (τ : ℂ) w (Function.update r i z) := fun w r i =>
    differentiable_finsetProd_dev _ fun j _ =>
      ((theta1_differentiable τ).comp ((differentiable_const _).sub (differentiable_update_apply_dev r i j))).pow 4
  have hspec : ∀ s : Fin (n + m), ∀ t : Fin (n + m), SameSpecies n s t →
      SameSpecies (n + 1) (mIdx_dev s) (mIdx_dev t) := by
    intro s t h
    simp only [SameSpecies] at h ⊢
    rw [mIdx_species_dev, mIdx_species_dev]
    exact h
  have hslice : ∀ (r : Fin (n + m) → ℂ) (i : Fin (n + m)) (z₀ : ℂ),
      (fun z => mu τ a (Function.update r i z)) =ᶠ[nhds z₀] fun z =>
        a (Function.update (mergePt (admW τ (Function.update r i z₀)) r) (mIdx_dev i) z) *
          (deriv (fun z => theta1 z τ) 0 ^ 2 *
            Emerge (τ : ℂ) (admW τ (Function.update r i z₀)) (Function.update r i z))⁻¹ := by
    intro r i z₀
    obtain ⟨_, hloc⟩ := mu_local_dev τ ha (Function.update r i z₀) (admW_spec_dev τ _)
    have hT : Filter.Tendsto (fun z => Function.update r i z) (nhds z₀) (nhds (Function.update r i z₀)) :=
      ((continuous_const : Continuous fun _ : ℂ => r).update i continuous_id).tendsto z₀
    filter_upwards [hT.eventually hloc] with z hz
    rw [hz]
    unfold mergeAt
    rw [mergePt_update_dev, div_eq_mul_inv]
  have hFa : ∀ (r : Fin (n + m) → ℂ) (i : Fin (n + m)) (z₀ : ℂ), AnalyticAt ℂ (fun z =>
      (deriv (fun z => theta1 z τ) 0 ^ 2 *
        Emerge (τ : ℂ) (admW τ (Function.update r i z₀)) (Function.update r i z))⁻¹) z₀ := fun r i z₀ =>
    (((hEd _ r i).const_mul _).analyticAt z₀).inv (mul_ne_zero hc0 (Emerge_ne_zero_dev τ (admW_spec_dev τ _)))
  rw [mem_Gnum]
  refine ⟨⟨?_, fun r i => ?_⟩, fun r c => ?_, fun r k => ?_, fun r k => ?_, fun s t hst hss r => ?_,
    fun s t hst hss => ?_, fun s t hs ht r hr => ?_⟩
  · -- continuity
    rw [continuous_iff_continuousAt]
    intro r₀
    obtain ⟨_, hloc⟩ := mu_local_dev τ ha r₀ (admW_spec_dev τ r₀)
    refine ContinuousAt.congr ?_ hloc.symm
    exact ((isOsgood_mergePt_dev hao _).1.continuousAt).div (continuousAt_const.mul (hEc _).continuousAt)
      (mul_ne_zero hc0 (Emerge_ne_zero_dev τ (admW_spec_dev τ r₀)))
  · -- separate holomorphy
    intro z₀
    refine DifferentiableAt.congr_of_eventuallyEq ?_ (hslice r i z₀)
    exact ((hao.2 _ _) z₀).mul (hFa r i z₀).differentiableAt
  · -- (i)
    have hw := admW_spec_dev τ r
    have hw' : ∀ i, admW τ r + c - (fun i => r i + c) i ∉ Λu τ := fun i => by
      simpa [show admW τ r + c - (r i + c) = admW τ r - r i by ring] using hw i
    show mergeAt τ a (admW τ (fun i => r i + c)) (fun i => r i + c) = mergeAt τ a (admW τ r) r
    rw [lemC_c_indep τ ha _ (admW_spec_dev τ _) hw']
    unfold mergeAt
    rw [mergePt_add_const_dev, ha0, Emerge_add_const_dev]
  · -- (ii), the shift by 1
    have hw := admW_spec_dev τ r
    have hw' : ∀ i, admW τ r - Function.update r k (r k + 1) i ∉ Λu τ := by
      intro i
      by_cases hik : i = k
      · subst hik
        rw [Function.update_self]
        intro hl
        refine hw i (mem_Λu_of_add_dev τ (neg_mem_Λu_dev τ (one_mem_Λu_dev τ)) ?_)
        rwa [show admW τ r - r i + -1 = admW τ r - (r i + 1) by ring]
      · rw [Function.update_of_ne hik]
        exact hw i
    show mergeAt τ a (admW τ _) _ = ε.1 * mergeAt τ a (admW τ r) r
    rw [lemC_c_indep τ ha _ (admW_spec_dev τ _) hw']
    unfold mergeAt
    rw [Emerge_update_add_one_dev, mergePt_update_dev,
      show r k + 1 = mergePt (admW τ r) r (mIdx_dev k) + 1 by rw [mergePt_mIdx_dev], ha1, mul_div_assoc]
  · -- (ii), the shift by τ
    have hw := admW_spec_dev τ r
    have hw' : ∀ i, admW τ r - Function.update r k (r k + τ) i ∉ Λu τ := by
      intro i
      by_cases hik : i = k
      · subst hik
        rw [Function.update_self]
        intro hl
        refine hw i (mem_Λu_of_add_dev τ (neg_mem_Λu_dev τ (tau_mem_Λu_dev τ)) ?_)
        rwa [show admW τ r - r i + -(τ : ℂ) = admW τ r - (r i + τ) by ring]
      · rw [Function.update_of_ne hik]
        exact hw i
    show mergeAt τ a (admW τ _) _ = ε.2 * cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ -
      4 * π * I * (((n + m : ℕ) : ℂ) * r k - ∑ i, r i)) * mergeAt τ a (admW τ r) r
    rw [lemC_c_indep τ ha _ (admW_spec_dev τ _) hw']
    unfold mergeAt
    rw [Emerge_update_add_tau_dev, mergePt_update_dev,
      show r k + (τ : ℂ) = mergePt (admW τ r) r (mIdx_dev k) + τ by rw [mergePt_mIdx_dev], haτ,
      mergePt_mIdx_dev, sum_mergePt_dev]
    have hexp : cexp (-2 * π * I * ((((n + 1) + (m + 1) : ℕ) : ℂ) - 1) * τ -
        4 * π * I * ((((n + 1) + (m + 1) : ℕ) : ℂ) * r k - (2 * admW τ r + ∑ i, r i))) =
        cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ - 4 * π * I * (((n + m : ℕ) : ℂ) * r k - ∑ i, r i)) *
          cexp (8 * π * I * (admW τ r - r k) - 4 * π * I * τ) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    have hX := Complex.exp_ne_zero (8 * π * I * (admW τ r - r k) - 4 * π * I * τ)
    field_simp
  · -- (iii)
    have hw := admW_spec_dev τ r
    have hw' : ∀ i, admW τ r - (r ∘ Equiv.swap s t) i ∉ Λu τ := fun i => hw _
    show mergeAt τ a (admW τ _) _ = -mergeAt τ a (admW τ r) r
    rw [lemC_c_indep τ ha _ (admW_spec_dev τ _) hw']
    unfold mergeAt
    rw [mergePt_swap_dev _ _ hst, has _ _ (mIdx_injective_dev.ne hst) (hspec s t hss), Emerge_swap_dev, neg_div]
  · -- (C1)
    intro r l hl j hj
    rw [(hslice r s (r t + l)).iteratedDeriv_eq j]
    have hvan := hC1 _ _ (mIdx_lt_dev hst) (hspec s t hss) (mergePt (admW τ (Function.update r s (r t + l))) r) l hl
    rw [mergePt_mIdx_dev] at hvan
    have hG : Differentiable ℂ fun z => a (Function.update (mergePt (admW τ (Function.update r s (r t + l))) r)
      (mIdx_dev s) z) := hao.2 _ _
    have e : (fun z => a (Function.update (mergePt (admW τ (Function.update r s (r t + l))) r) (mIdx_dev s) z) *
        (deriv (fun z => theta1 z τ) 0 ^ 2 *
          Emerge (τ : ℂ) (admW τ (Function.update r s (r t + l))) (Function.update r s z))⁻¹) =
        (fun z => a (Function.update (mergePt (admW τ (Function.update r s (r t + l))) r) (mIdx_dev s) z)) *
          fun z => (deriv (fun z => theta1 z τ) 0 ^ 2 *
            Emerge (τ : ℂ) (admW τ (Function.update r s (r t + l))) (Function.update r s z))⁻¹ := rfl
    rw [e, iteratedDeriv_mul hG.contDiff.contDiffAt (hFa r s (r t + l)).contDiffAt]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < 3 := by
      have := Finset.mem_range.1 hi
      omega
    rw [hvan i hi', mul_zero, zero_mul]
  · -- (C2)
    have hw₀ := admW_spec_dev τ r
    obtain ⟨_, hloc⟩ := mu_local_dev τ ha r hw₀
    have hsl : ∀ i, (fun z => mu τ a (Function.update r i z)) =ᶠ[nhds (r i)]
        fun z => mergeAt τ a (admW τ r) (Function.update r i z) := by
      intro i
      have hT : Filter.Tendsto (fun z => Function.update r i z) (nhds (r i)) (nhds r) := by
        have := ((continuous_const : Continuous fun _ : ℂ => r).update i continuous_id).tendsto (r i)
        simpa using this
      exact hT.eventually hloc
    have hst' : s ≠ t := by
      intro h
      subst h
      omega
    have hu : ∀ i, (fun z => mergeAt τ a (admW τ r) (Function.update r i z)) = fun z =>
        a (Function.update (mergePt (admW τ r) r) (mIdx_dev i) z) *
          (deriv (fun z => theta1 z τ) 0 ^ 2 * Emerge (τ : ℂ) (admW τ r) (Function.update r i z))⁻¹ := by
      intro i
      funext z
      unfold mergeAt
      rw [mergePt_update_dev, div_eq_mul_inv]
    have hFst : (fun z => (deriv (fun z => theta1 z τ) 0 ^ 2 * Emerge (τ : ℂ) (admW τ r) (Function.update r s z))⁻¹) =
        fun z => (deriv (fun z => theta1 z τ) 0 ^ 2 * Emerge (τ : ℂ) (admW τ r) (Function.update r t z))⁻¹ := by
      funext z
      rw [← Emerge_swap_dev τ (admW τ r) (Function.update r s z) s t]
      congr 3
      funext j
      by_cases hjt : j = t
      · subst hjt
        simp [Equiv.swap_apply_right]
      · by_cases hjs : j = s
        · subst hjs
          simp [Equiv.swap_apply_left, Function.update_of_ne hst'.symm, Function.update_of_ne hst', hr]
        · simp [Equiv.swap_apply_of_ne_of_ne hjs hjt, Function.update_of_ne hjs, Function.update_of_ne hjt]
    have hFd : ∀ i, DifferentiableAt ℂ (fun z => (deriv (fun z => theta1 z τ) 0 ^ 2 *
        Emerge (τ : ℂ) (admW τ r) (Function.update r i z))⁻¹) (r i) := by
      intro i
      refine (((hEd _ r i).const_mul _) (r i)).inv ?_
      rw [Function.update_eq_self]
      exact mul_ne_zero hc0 (Emerge_ne_zero_dev τ hw₀)
    unfold relDeriv
    rw [(hsl s).deriv_eq, (hsl t).deriv_eq, hu s, hu t, deriv_fun_mul ((hao.2 _ _) _) (hFd s),
      deriv_fun_mul ((hao.2 _ _) _) (hFd t), hFst]
    have hdF : deriv (fun z => (deriv (fun z => theta1 z τ) 0 ^ 2 *
        Emerge (τ : ℂ) (admW τ r) (Function.update r t z))⁻¹) (r s) =
        deriv (fun z => (deriv (fun z => theta1 z τ) 0 ^ 2 *
          Emerge (τ : ℂ) (admW τ r) (Function.update r t z))⁻¹) (r t) := by rw [hr]
    have hAs : a (Function.update (mergePt (admW τ r) r) (mIdx_dev s) (r s)) = a (mergePt (admW τ r) r) := by
      rw [show r s = mergePt (admW τ r) r (mIdx_dev s) from (mergePt_mIdx_dev _ _ _).symm, Function.update_eq_self]
    have hAt : a (Function.update (mergePt (admW τ r) r) (mIdx_dev t) (r t)) = a (mergePt (admW τ r) r) := by
      rw [show r t = mergePt (admW τ r) r (mIdx_dev t) from (mergePt_mIdx_dev _ _ _).symm, Function.update_eq_self]
    rw [hdF, hAs, hAt]
    simp only [Function.update_eq_self]
    have h2 := hC2 (mIdx_dev s) (mIdx_dev t) ((mIdx_species_dev s).2 hs)
      (by have := (mIdx_species_dev t).not.2 (by omega); omega) (mergePt (admW τ r) r)
      (by rw [mergePt_mIdx_dev, mergePt_mIdx_dev, hr])
    unfold relDeriv at h2
    rw [mergePt_mIdx_dev, mergePt_mIdx_dev] at h2
    linear_combination (deriv (fun z => theta1 z τ) 0 ^ 2 * Emerge (τ : ℂ) (admW τ r) r)⁻¹ * h2

/-- **Proposition C.induct** (proof): "`$\mu:\kzG(n,m;\varepsilon)\to\kzG(n-1,m-1;\varepsilon)$ is linear (Lemma~\ref{kz:lem:C}(d))`"
— the merge as a linear map (linearity: `𝖺 ↦ 𝖺|_M/(ϑ₁'(0)² E)` is linear). -/
def muL (τ : ℍ) (n m : ℕ) (ε : ℂ × ℂ) : Gnum τ (n + 1) (m + 1) ε →ₗ[ℂ] Gnum τ n m ε where
  toFun a := ⟨mu τ (a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ), lemC_d τ a.2⟩
  map_add' a b := by
    ext r
    simp [mu, mergeAt, add_div]
  map_smul' c a := by
    ext r
    simp [mu, mergeAt, mul_div_assoc]

/-! ## Lemma C.D -/

/-! ### Proof devices for Lemma C.D (proof phase, round two; not statements of the paper)

The division by `J²` in the Osgood class (`Jdiv_dev`): one pair at a time by (T3); the quotient keeps the order `≥ 2`
along the other pairs at the generic points, where the divided factor does not vanish (`generic_slice_dev`), and (T2)
extends it. A numerator vanishing to order `≥ 2` along every pair is `c J²` (`const_of_Jdiv_dev`): the quotient has the
multipliers `ε` in each variable (from those of `𝖺` and `J²`, at generic points and then by continuity), so each slice is
constant (`const_of_root_mult_dev`, `ε` being a pair of roots of unity unless `𝒢 = 0`), hence the quotient is constant
(`const_of_slices_dev`). For Lemma C.D(b), the order `≥ 2` along an up–down divisor: `𝖺 = 0` on `{x₁ = y₁}` from
`μ(a) = 0` and Lemma C.C(c), at the admissible centres and then by continuity in `w` (`merge_zero_dev`, the density
argument of `admW_spec_dev`), on `{x_a = y_k}` by antisymmetry (`updown_zero_dev`), `∂_{x_a} 𝖺 = 0` there by (C2) and
the derivative along the diagonal (`updown_deriv_zero_dev`: F1-lower's `isOsgood2_differentiable_dev` through
`differentiable_update2_dev`, the pattern of F0's `fderiv_diag`), and the order passes to the translates through the
multipliers of the slice (`slice_order2_lattice_dev`: `order2_shift_dev`, the pattern of `order4_shift_dev`, with
`lattice_closed_dev`; `slice_vanish_of_factor_dev` is the converse of `slice_factor_dev`). -/

theorem const_of_slices_dev {N : ℕ} {f : (Fin N → ℂ) → ℂ}
    (h : ∀ (u : Fin N → ℂ) (k : Fin N) (z : ℂ), f (Function.update u k z) = f u) (u v : Fin N → ℂ) : f u = f v := by
  have key : ∀ S : Finset (Fin N), f u = f (S.piecewise v u) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · rw [Finset.piecewise_empty]
    · intro a S _ ih
      rw [Finset.piecewise_insert, h, ih]
  rw [key Finset.univ, Finset.piecewise_univ]

theorem generic_ne_dev (τ : ℍ) {N : ℕ} {u : Fin N → ℂ} (hu : ∀ p ∈ pairsLT_dev N, u p.1 - u p.2 ∉ Λu τ)
    {i j : Fin N} (hij : i ≠ j) : u i - u j ∉ Λu τ := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact hu (i, j) ((mem_pairsLT_dev _).2 h)
  · intro hl
    refine hu (j, i) ((mem_pairsLT_dev _).2 h) ?_
    rw [show u j - u i = -(u i - u j) by ring]
    exact neg_mem_Λu_dev τ hl

theorem generic_slice_dev (τ : ℍ) {N : ℕ} {u : Fin N → ℂ} (hu : ∀ p ∈ pairsLT_dev N, u p.1 - u p.2 ∉ Λu τ)
    {q p : Fin N × Fin N} (hq : q.1 < q.2) (hp : p.1 < p.2) (hpq : p ≠ q) {l : ℂ} (hl : l ∈ Λu τ) :
    Function.update u q.1 (u q.2 + l) p.1 - Function.update u q.1 (u q.2 + l) p.2 ∉ Λu τ := by
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.1 := fun h => absurd (h1.trans h.symm) hp.ne
    have h3 : p.2 ≠ q.2 := fun h => hpq (Prod.ext h1 h)
    rw [h1, Function.update_self, Function.update_of_ne h2]
    intro hl'
    refine generic_ne_dev τ hu (Ne.symm h3) (mem_Λu_of_add_dev τ hl ?_)
    rwa [show u q.2 - u p.2 + l = u q.2 + l - u p.2 by ring]
  · by_cases h2 : p.2 = q.1
    · have h4 : p.1 ≠ q.2 := by
        intro h
        rw [Fin.lt_def] at hp hq
        rw [Fin.ext_iff] at h h2
        omega
      rw [h2, Function.update_self, Function.update_of_ne h1]
      intro hl'
      refine generic_ne_dev τ hu h4 (mem_Λu_of_add_dev τ (neg_mem_Λu_dev τ hl) ?_)
      rwa [show u p.1 - u q.2 + -l = u p.1 - (u q.2 + l) by ring]
    · rw [Function.update_of_ne h1, Function.update_of_ne h2]
      exact generic_ne_dev τ hu hp.ne

theorem Jdiv_dev (τ : ℍ) {N : ℕ} {f : (Fin N → ℂ) → ℂ} (hf : IsOsgood f)
    (hv : ∀ i j : Fin N, i < j → VanishesAlong τ f i j 2) :
    ∃ g : (Fin N → ℂ) → ℂ, IsOsgood g ∧ ∀ u, f u = Jfun τ u ^ 2 * g u := by
  have hS : Dense {u : Fin N → ℂ | ∀ p ∈ pairsLT_dev N, u p.1 - u p.2 ∉ Λu τ} :=
    dense_generic_dev τ _ fun p hp => ((mem_pairsLT_dev p).1 hp).ne
  have key : ∀ P : Finset (Fin N × Fin N), P ⊆ pairsLT_dev N → ∃ g : (Fin N → ℂ) → ℂ, IsOsgood g ∧
      (∀ u, f u = (∏ p ∈ P, theta1 (u p.1 - u p.2) τ ^ 2) * g u) ∧
      ∀ q ∈ pairsLT_dev N, q ∉ P → VanishesAlong τ g q.1 q.2 2 := by
    intro P
    refine Finset.induction_on P ?_ ?_
    · intro _
      exact ⟨f, hf, fun u => by simp, fun q hq _ => hv q.1 q.2 ((mem_pairsLT_dev q).1 hq)⟩
    · intro p₀ P hp₀ ih hsub
      obtain ⟨g, hg, hfg, hgv⟩ := ih ((Finset.subset_insert p₀ P).trans hsub)
      have hp₀mem : p₀ ∈ pairsLT_dev N := hsub (Finset.mem_insert_self p₀ P)
      have hlt₀ : p₀.1 < p₀.2 := (mem_pairsLT_dev p₀).1 hp₀mem
      obtain ⟨Q, hQ, hgQ⟩ := div_theta1_pow_dev τ hg hlt₀.ne 2 (hgv p₀ hp₀mem hp₀)
      refine ⟨Q, hQ, fun u => ?_, fun q hq hqP => ?_⟩
      · rw [hfg u, hgQ u, Finset.prod_insert hp₀]
        ring
      · have hq' : q ∉ P := fun h => hqP (Finset.mem_insert_of_mem h)
        have hqne : q ≠ p₀ := fun h => hqP (h ▸ Finset.mem_insert_self p₀ P)
        have hltq : q.1 < q.2 := (mem_pairsLT_dev q).1 hq
        refine vanishesAlong_of_dense_dev τ hQ q.1 q.2 2 hS fun u hu l hl j hj => ?_
        have hD0 : theta1 (Function.update u q.1 (u q.2 + l) p₀.1 - Function.update u q.1 (u q.2 + l) p₀.2) τ ≠ 0 :=
          fun h0 => generic_slice_dev τ hu hltq hlt₀ (Ne.symm hqne) hl ((theta1_eq_zero_iff τ _).1 h0)
        have hDd : Differentiable ℂ fun z => theta1 (Function.update u q.1 z p₀.1 - Function.update u q.1 z p₀.2) τ :=
          (theta1_differentiable τ).comp
            ((differentiable_update_apply_dev u q.1 p₀.1).sub (differentiable_update_apply_dev u q.1 p₀.2))
        have hFa : AnalyticAt ℂ (fun z =>
            (theta1 (Function.update u q.1 z p₀.1 - Function.update u q.1 z p₀.2) τ ^ 2)⁻¹) (u q.2 + l) :=
          ((hDd.pow 2).analyticAt _).inv (pow_ne_zero 2 hD0)
        have hev : (fun z => Q (Function.update u q.1 z)) =ᶠ[nhds (u q.2 + l)] fun z =>
            g (Function.update u q.1 z) *
              (theta1 (Function.update u q.1 z p₀.1 - Function.update u q.1 z p₀.2) τ ^ 2)⁻¹ := by
          filter_upwards [(hDd.continuous.continuousAt).eventually_ne hD0] with z hz
          rw [hgQ (Function.update u q.1 z)]
          have h2 := mul_inv_cancel₀ (pow_ne_zero 2 hz)
          linear_combination (-(Q (Function.update u q.1 z))) * h2
        rw [hev.iteratedDeriv_eq j]
        have hvan := hgv q hq hq' u l hl
        have e : (fun z => g (Function.update u q.1 z) *
            (theta1 (Function.update u q.1 z p₀.1 - Function.update u q.1 z p₀.2) τ ^ 2)⁻¹) =
            (fun z => g (Function.update u q.1 z)) *
              fun z => (theta1 (Function.update u q.1 z p₀.1 - Function.update u q.1 z p₀.2) τ ^ 2)⁻¹ := rfl
        rw [e, iteratedDeriv_mul ((hg.2 u q.1).contDiff.contDiffAt) hFa.contDiffAt]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi' : i < 2 := by
          have := Finset.mem_range.1 hi
          omega
        rw [hvan i hi', mul_zero, zero_mul]
  obtain ⟨g, hg, hfg, _⟩ := key (pairsLT_dev N) subset_rfl
  refine ⟨g, hg, fun u => ?_⟩
  rw [hfg u, Jfun_eq_pairs_dev, ← Finset.prod_pow]

theorem const_of_Jdiv_dev (τ : ℍ) {n m : ℕ} (hN : 0 < n + m) {ε : ℂ × ℂ} {a : (Fin (n + m) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ n m ε) (hv : ∀ i j : Fin (n + m), i < j → VanishesAlong τ a i j 2) :
    ∃ c : ℂ, ∀ u, a u = c * Jfun τ u ^ 2 := by
  by_cases hroot : ε.1 ^ (n + m) = 1 ∧ ε.2 ^ (n + m) = 1
  swap
  · have hb := Gnum_eq_bot_of_not_root τ n m hroot
    have h0 : a ∈ (⊥ : Submodule ℂ ((Fin (n + m) → ℂ) → ℂ)) := hb ▸ ha
    have ha0 : a = 0 := (Submodule.mem_bot ℂ).1 h0
    exact ⟨0, fun u => by rw [ha0]; simp⟩
  obtain ⟨hao, _, ha1, haτ, _, _, _⟩ := id ha
  obtain ⟨g, hg, hag⟩ := Jdiv_dev τ hao hv
  have hS : Dense {u : Fin (n + m) → ℂ | ∀ p ∈ pairsLT_dev (n + m), u p.1 - u p.2 ∉ Λu τ} :=
    dense_generic_dev τ _ fun p hp => ((mem_pairsLT_dev p).1 hp).ne
  have hJne : ∀ u ∈ {u : Fin (n + m) → ℂ | ∀ p ∈ pairsLT_dev (n + m), u p.1 - u p.2 ∉ Λu τ}, Jfun τ u ≠ 0 :=
    fun u hu => Jfun_ne_zero_dev τ u fun i j hij => hu (i, j) ((mem_pairsLT_dev _).2 hij)
  have hg1 : ∀ (u : Fin (n + m) → ℂ) (k : Fin (n + m)), g (Function.update u k (u k + 1)) = ε.1 * g u := by
    intro u₀ k
    have h := Continuous.ext_on hS (hg.1.comp (continuous_id.update k ((continuous_apply k).add continuous_const)))
      (continuous_const.mul hg.1) fun u hu => by
        show g (Function.update u k (u k + 1)) = ε.1 * g u
        have hJ := hJne u hu
        have h1 := ha1 u k
        rw [hag, hag, Jfun_sq_add_one] at h1
        exact mul_left_cancel₀ (pow_ne_zero 2 hJ) (by rw [h1]; ring)
    exact congrFun h u₀
  have hgτ : ∀ (u : Fin (n + m) → ℂ) (k : Fin (n + m)), g (Function.update u k (u k + τ)) = ε.2 * g u := by
    intro u₀ k
    have h := Continuous.ext_on hS (hg.1.comp (continuous_id.update k ((continuous_apply k).add continuous_const)))
      (continuous_const.mul hg.1) fun u hu => by
        show g (Function.update u k (u k + τ)) = ε.2 * g u
        have hJ := hJne u hu
        have h1 := haτ u k
        rw [hag, hag, Jfun_sq_add_tau] at h1
        have hX := Complex.exp_ne_zero (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ -
          4 * π * I * (((n + m : ℕ) : ℂ) * u k - ∑ i, u i))
        exact mul_left_cancel₀ (mul_ne_zero hX (pow_ne_zero 2 hJ)) (by rw [h1]; ring)
    exact congrFun h u₀
  have hslice : ∀ (u : Fin (n + m) → ℂ) (k : Fin (n + m)) (z : ℂ), g (Function.update u k z) = g u := by
    intro u k z
    have h1 : ∀ z, g (Function.update u k (z + 1)) = ε.1 * g (Function.update u k z) := by
      intro z
      have h := hg1 (Function.update u k z) k
      rwa [Function.update_self, Function.update_idem] at h
    have hτ' : ∀ z, g (Function.update u k (z + τ)) = ε.2 * g (Function.update u k z) := by
      intro z
      have h := hgτ (Function.update u k z) k
      rwa [Function.update_self, Function.update_idem] at h
    have h := const_of_root_mult_dev τ (hg.2 u k) (by omega) hroot.1 hroot.2 h1 hτ' z (u k)
    rwa [Function.update_eq_self] at h
  refine ⟨g 0, fun u => ?_⟩
  rw [hag u, mul_comm, const_of_slices_dev hslice u 0]

theorem order2_shift_dev {G β : ℂ → ℂ} (hβ : Differentiable ℂ β) (hβ0 : ∀ w, β w ≠ 0) {c : ℂ}
    (hG : ∀ w, G (w + c) = β w * G w) (z : ℂ) :
    (∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ z ∧ ∀ᶠ w in nhds z, G w = (w - z) ^ 2 * g₁ w) ↔
      (∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ (z + c) ∧ ∀ᶠ w in nhds (z + c), G w = (w - (z + c)) ^ 2 * g₁ w) := by
  constructor
  · rintro ⟨g₁, hg₁, hev⟩
    have hsub : AnalyticAt ℂ (fun w : ℂ => w - c) (z + c) := by fun_prop
    have hg₁' : AnalyticAt ℂ g₁ ((fun w : ℂ => w - c) (z + c)) := by simpa using hg₁
    refine ⟨fun w => β (w - c) * g₁ (w - c), ((hβ.analyticAt _).comp hsub).mul
      (AnalyticAt.comp (f := fun w : ℂ => w - c) (x := z + c) hg₁' hsub), ?_⟩
    have hT : Filter.Tendsto (fun w : ℂ => w - c) (nhds (z + c)) (nhds z) :=
      (continuous_sub_right c).tendsto' (z + c) z (by ring)
    filter_upwards [hT.eventually hev] with w hw
    have h := hG (w - c)
    rw [sub_add_cancel] at h
    rw [h, hw]
    ring
  · rintro ⟨g₁, hg₁, hev⟩
    have hadd : AnalyticAt ℂ (fun w : ℂ => w + c) z := by fun_prop
    refine ⟨fun w => (β w)⁻¹ * g₁ (w + c), ((hβ.analyticAt z).inv (hβ0 z)).mul
      (AnalyticAt.comp (f := fun w : ℂ => w + c) (x := z) hg₁ hadd), ?_⟩
    have hT : Filter.Tendsto (fun w : ℂ => w + c) (nhds z) (nhds (z + c)) :=
      (by fun_prop : Continuous fun w : ℂ => w + c).tendsto z
    filter_upwards [hT.eventually hev] with w hw
    have h := hG w
    rw [hw] at h
    have hb := hβ0 w
    field_simp
    linear_combination -h

theorem slice_vanish_of_factor_dev {g : ℂ → ℂ} (hg : Differentiable ℂ g) {z₀ : ℂ} {k : ℕ} {g₁ : ℂ → ℂ}
    (hg₁ : AnalyticAt ℂ g₁ z₀) (hev : ∀ᶠ z in nhds z₀, g z = (z - z₀) ^ k * g₁ z) :
    ∀ j < k, iteratedDeriv j g z₀ = 0 :=
  (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hg.analyticAt z₀)).1
    ((natCast_le_analyticOrderAt (hg.analyticAt z₀)).2 ⟨g₁, hg₁, hev.mono fun z hz => by rw [hz, smul_eq_mul]⟩)

theorem slice_order2_lattice_dev (τ : ℍ) {N : ℕ} {ε : ℂ × ℂ} {a : (Fin N → ℂ) → ℂ} (hao : IsOsgood a)
    (hε1 : ε.1 ≠ 0) (hε2 : ε.2 ≠ 0)
    (ha1 : ∀ (u : Fin N → ℂ) (k : Fin N), a (Function.update u k (u k + 1)) = ε.1 * a u)
    (haτ : ∀ (u : Fin N → ℂ) (k : Fin N), a (Function.update u k (u k + τ)) =
      ε.2 * cexp (-2 * π * I * ((N : ℂ) - 1) * τ - 4 * π * I * ((N : ℂ) * u k - ∑ i, u i)) * a u)
    (u : Fin N → ℂ) (i : Fin N) (z₀ : ℂ)
    (h0 : ∀ k < 2, iteratedDeriv k (fun z => a (Function.update u i z)) z₀ = 0) :
    ∀ l ∈ Λu τ, ∀ k < 2, iteratedDeriv k (fun z => a (Function.update u i z)) (z₀ + l) = 0 := by
  intro l hl
  have hSd : Differentiable ℂ fun z => a (Function.update u i z) := hao.2 u i
  have hS1 : ∀ z, a (Function.update u i (z + 1)) = ε.1 * a (Function.update u i z) := by
    intro z
    have h := ha1 (Function.update u i z) i
    rwa [Function.update_self, Function.update_idem] at h
  have hSτ : ∀ z, a (Function.update u i (z + τ)) = ε.2 * cexp (-2 * π * I * ((N : ℂ) - 1) * τ -
      4 * π * I * ((N : ℂ) * z - (∑ k, u k - u i + z))) * a (Function.update u i z) := by
    intro z
    have h := haτ (Function.update u i z) i
    rwa [Function.update_self, Function.update_idem, sum_update_dev] at h
  have hP1 := order2_shift_dev (G := fun z => a (Function.update u i z)) (differentiable_const ε.1)
    (fun _ => hε1) (c := 1) hS1
  have hPτ := order2_shift_dev (G := fun z => a (Function.update u i z))
    (β := fun z => ε.2 * cexp (-2 * π * I * ((N : ℂ) - 1) * τ - 4 * π * I * ((N : ℂ) * z - (∑ k, u k - u i + z))))
    (by fun_prop) (fun _ => mul_ne_zero hε2 (Complex.exp_ne_zero _)) (c := τ) hSτ
  obtain ⟨g₁, hg₁, hev⟩ := lattice_closed_dev τ (P := fun z => ∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ z ∧
      ∀ᶠ w in nhds z, a (Function.update u i w) = (w - z) ^ 2 * g₁ w)
    (fun z => (hP1 z).1) (fun z => (hP1 z).2) (fun z => (hPτ z).1) (fun z => (hPτ z).2) (slice_factor_dev hSd h0) l hl
  exact slice_vanish_of_factor_dev hSd hg₁ hev

/-- The pattern of `differentiable_mergePt_dev` (above) for two coordinates `s ≠ t` of a base point. -/
theorem differentiable_update2_dev {N : ℕ} {a : (Fin N → ℂ) → ℂ} (ha : IsOsgood a) (u : Fin N → ℂ) {s t : Fin N}
    (hst : s ≠ t) : Differentiable ℂ fun p : ℂ × ℂ => a (Function.update (Function.update u s p.1) t p.2) := by
  set G : ℂ × ℂ → ℂ := fun p => a (Function.update (Function.update u s p.1) t p.2) with hG
  have hGos : IsOsgood2_dev G := by
    refine ⟨?_, fun b => ?_, fun x => ?_⟩
    · refine ha.1.comp (continuous_pi fun i => ?_)
      by_cases hit : i = t
      · simp only [hit, Function.update_self]
        exact continuous_snd
      · by_cases his : i = s
        · simp only [his, Function.update_of_ne hst, Function.update_self]
          exact continuous_fst
        · simp only [Function.update_of_ne hit, Function.update_of_ne his]
          exact continuous_const
    · have e : (fun x => G (x, b)) = fun x => a (Function.update (Function.update u t b) s x) :=
        funext fun x => by simp only [hG]; rw [Function.update_comm hst]
      rw [e]
      exact ha.2 _ s
    · exact ha.2 (Function.update u s x) t
  exact isOsgood2_differentiable_dev hGos

theorem merge_zero_dev (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) (hmu : mu τ a = 0) (w : ℂ) (r : Fin (n + m) → ℂ) :
    a (mergePt w r) = 0 := by
  have hS : Dense {w : ℂ | ∀ i, w - r i ∉ Λu τ} := by
    have hC : (⋃ i, (fun l => r i + l) '' Λu τ).Countable :=
      Set.countable_iUnion fun i => (Λu_countable_dev τ).image _
    refine Dense.mono ?_ (hC.dense_compl ℂ)
    intro w hw i hi
    exact hw (Set.mem_iUnion.2 ⟨i, ⟨w - r i, hi, add_sub_cancel (r i) w⟩⟩)
  have key : ∀ w ∈ {w : ℂ | ∀ i, w - r i ∉ Λu τ}, a (mergePt w r) = 0 := by
    intro w hw
    have hind := lemC_c_indep τ ha r hw (admW_spec_dev τ r)
    have hm : mergeAt τ a (admW τ r) r = 0 := congrFun hmu r
    rw [hm] at hind
    have hD : deriv (fun z => theta1 z τ) 0 ^ 2 * Emerge (τ : ℂ) w r ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 (theta1_deriv_zero_ne_zero τ)) (Emerge_ne_zero_dev τ hw)
    unfold mergeAt at hind
    exact (div_eq_zero_iff.1 hind).resolve_right hD
  exact congrFun (Continuous.ext_on hS (differentiable_mergePt_dev ha.1 r).continuous continuous_const key) w

theorem mergePt_rest_dev {n m : ℕ} (v : Fin ((n + 1) + (m + 1)) → ℂ)
    (h : v (Fin.castAdd (m + 1) 0) = v (Fin.natAdd (n + 1) 0)) :
    mergePt (v (Fin.castAdd (m + 1) 0)) (fun i => v (mIdx_dev i)) = v := by
  funext j
  induction j using Fin.addCases with
  | left a' =>
    induction a' using Fin.cases with
    | zero => exact mergePt_s0_dev _ _
    | succ a => simp [mergePt, mIdx_dev]
  | right b' =>
    induction b' using Fin.cases with
    | zero => rw [mergePt_t0_dev]; exact h
    | succ k => simp [mergePt, mIdx_dev]

theorem updown_zero_dev (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) (hmu : mu τ a = 0) {i j : Fin ((n + 1) + (m + 1))} (hi : (i : ℕ) < n + 1)
    (hj : n + 1 ≤ (j : ℕ)) (v : Fin ((n + 1) + (m + 1)) → ℂ) (hv : v i = v j) : a v = 0 := by
  obtain ⟨_, _, _, _, has, _, _⟩ := id ha
  have hz : ∀ v : Fin ((n + 1) + (m + 1)) → ℂ, v (Fin.castAdd (m + 1) 0) = v (Fin.natAdd (n + 1) 0) → a v = 0 := by
    intro v hv
    rw [← mergePt_rest_dev v hv]
    exact merge_zero_dev τ ha hmu _ _
  have hsw : ∀ s t : Fin ((n + 1) + (m + 1)), SameSpecies (n + 1) s t → ∀ v : Fin ((n + 1) + (m + 1)) → ℂ,
      a (v ∘ Equiv.swap s t) = 0 → a v = 0 := by
    intro s t hss v h
    by_cases hst : s = t
    · rw [hst, Equiv.swap_self, Equiv.coe_refl, Function.comp_id] at h
      exact h
    · rw [has s t hst hss v] at h
      exact neg_eq_zero.1 h
  have hs₀ : ((Fin.castAdd (m + 1) (0 : Fin (n + 1)) : Fin ((n + 1) + (m + 1))) : ℕ) = 0 := by simp
  have ht₀ : ((Fin.natAdd (n + 1) (0 : Fin (m + 1)) : Fin ((n + 1) + (m + 1))) : ℕ) = n + 1 := by simp
  have h1 : Fin.castAdd (m + 1) (0 : Fin (n + 1)) ≠ Fin.natAdd (n + 1) (0 : Fin (m + 1)) := castAdd_ne_natAdd_dev _ _
  have h2 : Fin.castAdd (m + 1) (0 : Fin (n + 1)) ≠ j := fun h => by rw [← h, hs₀] at hj; omega
  have h3 : j ≠ i := fun h => by rw [h] at hj; omega
  refine hsw (Fin.castAdd (m + 1) 0) i ?_ v (hsw (Fin.natAdd (n + 1) 0) j ?_ _ (hz _ ?_))
  · unfold SameSpecies
    rw [hs₀]
    constructor <;> intro <;> omega
  · unfold SameSpecies
    rw [ht₀]
    constructor <;> intro <;> omega
  · simp only [Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_left, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h2) h3]
    exact hv

theorem updown_deriv_zero_dev (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) (hmu : mu τ a = 0) {i j : Fin ((n + 1) + (m + 1))} (hi : (i : ℕ) < n + 1)
    (hj : n + 1 ≤ (j : ℕ)) (v : Fin ((n + 1) + (m + 1)) → ℂ) (hv : v i = v j) :
    deriv (fun z => a (Function.update v i z)) (v i) = 0 := by
  obtain ⟨hao, _, _, _, _, _, hC2⟩ := id ha
  have hij : i ≠ j := fun h => by rw [h] at hi; omega
  have hGd := differentiable_update2_dev hao v hij
  set G : ℂ × ℂ → ℂ := fun p => a (Function.update (Function.update v i p.1) j p.2)
  have hF : HasFDerivAt G (fderiv ℂ G (v i, v i)) (v i, v i) := (hGd (v i, v i)).hasFDerivAt
  have hdiag : HasDerivAt (fun w : ℂ => G (w, w)) (fderiv ℂ G (v i, v i) (1, 1)) (v i) :=
    hF.comp_hasDerivAt (f := fun w : ℂ => (w, w)) (v i) ((hasDerivAt_id (v i)).prodMk (hasDerivAt_id (v i)))
  have h0 : fderiv ℂ G (v i, v i) (1, 1) = 0 := by
    have e : (fun w : ℂ => G (w, w)) = fun _ => (0 : ℂ) := by
      funext w
      show a (Function.update (Function.update v i w) j w) = 0
      exact updown_zero_dev τ ha hmu hi hj _
        (by rw [Function.update_of_ne hij, Function.update_self, Function.update_self])
    rw [e] at hdiag
    exact hdiag.unique (hasDerivAt_const (v i) 0)
  have h1 : HasDerivAt (fun x : ℂ => G (x, v i)) (fderiv ℂ G (v i, v i) (1, 0)) (v i) :=
    hF.comp_hasDerivAt (f := fun x : ℂ => (x, v i)) (v i)
      ((hasDerivAt_id (v i)).prodMk (hasDerivAt_const (v i) (v i)))
  have h2 : HasDerivAt (fun y : ℂ => G (v i, y)) (fderiv ℂ G (v i, v i) (0, 1)) (v i) :=
    hF.comp_hasDerivAt (f := fun y : ℂ => (v i, y)) (v i)
      ((hasDerivAt_const (v i) (v i)).prodMk (hasDerivAt_id (v i)))
  have hsum : fderiv ℂ G (v i, v i) (1, 0) + fderiv ℂ G (v i, v i) (0, 1) = 0 := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, h0]
  have e1 : (fun x : ℂ => G (x, v i)) = fun x => a (Function.update v i x) := by
    funext x
    show a (Function.update (Function.update v i x) j (v i)) = a (Function.update v i x)
    have h' : Function.update (Function.update v i x) j (v i) = Function.update v i x :=
      Function.update_eq_self_iff.2 (by rw [Function.update_of_ne hij.symm, hv])
    rw [h']
  have e2 : (fun y : ℂ => G (v i, y)) = fun y => a (Function.update v j y) := by
    funext y
    show a (Function.update (Function.update v i (v i)) j y) = a (Function.update v j y)
    rw [Function.update_eq_self]
  rw [e1] at h1
  rw [e2] at h2
  have hrel := hC2 i j hi hj v hv
  unfold relDeriv at hrel
  rw [h1.deriv, ← hv, h2.deriv] at hrel
  rw [h1.deriv]
  linear_combination (hrel + hsum) / 2

theorem updown_vanish_dev (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) (hmu : mu τ a = 0) (hε1 : ε.1 ≠ 0) (hε2 : ε.2 ≠ 0)
    {i j : Fin ((n + 1) + (m + 1))} (hi : (i : ℕ) < n + 1) (hj : n + 1 ≤ (j : ℕ)) : VanishesAlong τ a i j 2 := by
  obtain ⟨hao, _, ha1, haτ, _, _, _⟩ := id ha
  have hij : i ≠ j := fun h => by rw [h] at hi; omega
  intro u l hl
  refine slice_order2_lattice_dev τ hao hε1 hε2 ha1 haτ u i (u j) (fun k hk => ?_) l hl
  have hv : Function.update u i (u j) i = Function.update u i (u j) j := by
    rw [Function.update_self, Function.update_of_ne hij.symm]
  interval_cases k
  · rw [iteratedDeriv_zero]
    exact updown_zero_dev τ ha hmu hi hj _ hv
  · rw [iteratedDeriv_one]
    have h := updown_deriv_zero_dev τ ha hmu hi hj _ hv
    simpa only [Function.update_idem, Function.update_self] using h

/-! ### Proof devices for the sectors with one variable (proof phase, round two; not statements of the paper): with
`N = 1`, (i) makes a numerator constant, (ii) makes it zero unless `ε = (1,1)`, and every constant is a numerator at
`ε = (1,1)` (the other conditions are vacuous); a point where `J ≠ 0` (from `dense_generic_dev`) -/

theorem Gnum_single_dev (τ : ℍ) {n m : ℕ} (h1 : n + m = 1) {ε : ℂ × ℂ} {a : (Fin (n + m) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ n m ε) (u : Fin (n + m) → ℂ) : (∀ v, a v = a u) ∧ (a u ≠ 0 → ε = (1, 1)) := by
  obtain ⟨_, ha0, ha1, haτ, _, _, _⟩ := ha
  have hsub : ∀ i j : Fin (n + m), i = j := fun i j => Fin.ext (by have := i.isLt; have := j.isLt; omega)
  have k : Fin (n + m) := ⟨0, by omega⟩
  have hconst : ∀ v, a v = a u := by
    intro v
    rw [show v = fun i => u i + (v k - u k) from funext fun i => by rw [hsub i k]; ring]
    exact ha0 u _
  refine ⟨hconst, fun hne => ?_⟩
  have hsum : ∑ i, u i = u k := Finset.sum_eq_single k (fun j _ hj => absurd (hsub j k) hj)
    (fun h => absurd (Finset.mem_univ k) h)
  have e1 := ha1 u k
  rw [hconst (Function.update u k (u k + 1))] at e1
  have eτ := haτ u k
  rw [hconst (Function.update u k (u k + τ)), hsum,
    show -2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ - 4 * π * I * (((n + m : ℕ) : ℂ) * u k - u k) = 0 by
      rw [h1]; push_cast; ring, Complex.exp_zero, mul_one] at eτ
  have hε1 : ε.1 = 1 := by
    have h' : (ε.1 - 1) * a u = 0 := by linear_combination -e1
    rcases mul_eq_zero.1 h' with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hne
  have hε2 : ε.2 = 1 := by
    have h' : (ε.2 - 1) * a u = 0 := by linear_combination -eτ
    rcases mul_eq_zero.1 h' with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hne
  exact Prod.ext hε1 hε2

theorem const_mem_Gnum_single_dev (τ : ℍ) {n m : ℕ} (h1 : n + m = 1) (c : ℂ) :
    (fun _ : Fin (n + m) → ℂ => c) ∈ Gnum τ n m (1, 1) := by
  have hsub : ∀ i j : Fin (n + m), i = j := fun i j => Fin.ext (by have := i.isLt; have := j.isLt; omega)
  rw [mem_Gnum]
  refine ⟨⟨continuous_const, fun u i => differentiable_const c⟩, fun u c' => rfl, fun u k => by simp,
    fun u k => ?_, fun s t hst _ u => absurd (hsub s t) hst, fun s t hst _ => ?_, fun s t hs ht u _ => ?_⟩
  · have hsum : ∑ i, u i = u k := Finset.sum_eq_single k (fun j _ hj => absurd (hsub j k) hj)
      (fun h => absurd (Finset.mem_univ k) h)
    rw [hsum, show -2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ - 4 * π * I * (((n + m : ℕ) : ℂ) * u k - u k) = 0 by
      rw [h1]; push_cast; ring, Complex.exp_zero]
    simp
  · exact absurd (hsub s t) (ne_of_lt hst)
  · exfalso
    have := hsub s t
    subst this
    omega

theorem exists_Jfun_ne_zero_dev (τ : ℍ) (N : ℕ) : ∃ u : Fin N → ℂ, Jfun τ u ≠ 0 := by
  obtain ⟨u, hu⟩ := (dense_generic_dev τ (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2)
    (fun p hp => (Finset.mem_filter.1 hp).2.ne)).nonempty
  exact ⟨u, Jfun_ne_zero_dev τ u fun i j hij => hu (i, j) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩)⟩

/-! ### Proof device for Lemma C.D(a) (proof phase, round two; not a statement of the paper): with one species and
`N ≥ 2`, (C1) gives the order `≥ 2` along every pair, so a numerator is `c J²` (`const_of_Jdiv_dev`), and the
antisymmetry of the pair `(0, 1)` against the symmetry of `J²` makes `c = 0` -/

theorem Gnum_eq_bot_of_same_dev (τ : ℍ) {n m : ℕ} (h2 : 2 ≤ n + m) (hsame : ∀ s t : Fin (n + m), SameSpecies n s t)
    (ε : ℂ × ℂ) : Gnum τ n m ε = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  obtain ⟨_, _, _, _, has, hC1, _⟩ := id ha
  have hv : ∀ i j : Fin (n + m), i < j → VanishesAlong τ a i j 2 := by
    intro i j hij u l hl k hk
    exact hC1 i j hij (hsame i j) u l hl k (by omega)
  obtain ⟨c, hc⟩ := const_of_Jdiv_dev τ (by omega) ha hv
  obtain ⟨u₀, hu₀⟩ := exists_Jfun_ne_zero_dev τ (n + m)
  have hJ : Jfun τ u₀ ^ 2 ≠ 0 := pow_ne_zero 2 hu₀
  have h01 : (⟨0, by omega⟩ : Fin (n + m)) ≠ ⟨1, by omega⟩ := fun h => by simp [Fin.ext_iff] at h
  have h1 := has _ _ h01 (hsame _ _) u₀
  rw [hc, hc, Jfun_sq_perm] at h1
  have hc0 : c = 0 := by
    have h2' : c * Jfun τ u₀ ^ 2 = 0 := by linear_combination h1 / 2
    exact (mul_eq_zero.1 h2').resolve_right hJ
  funext u
  rw [hc u, hc0, zero_mul]
  rfl

/-- **Lemma C.D(a)**: "`For $k\ge2$, $\kzG(k,0;\varepsilon)=\kzG(0,k;\varepsilon)=0$.`" -/
theorem Gnum_polarized (τ : ℍ) {k : ℕ} (hk : 2 ≤ k) (ε : ℂ × ℂ) : Gnum τ k 0 ε = ⊥ ∧ Gnum τ 0 k ε = ⊥ := by
  refine ⟨Gnum_eq_bot_of_same_dev τ (by omega) (fun s t => ?_) ε,
    Gnum_eq_bot_of_same_dev τ (by omega) (fun s t => ?_) ε⟩
  · have hs := s.isLt
    have ht := t.isLt
    exact Iff.intro (fun _ => by omega) (fun _ => by omega)
  · exact Iff.intro (fun h => by omega) (fun h => by omega)

/-- **Lemma C.D(a)**: "`Also $\kzG(1,0;\varepsilon)=\kzG(0,1;\varepsilon)$, which is $\C$ (the constants) if $\varepsilon=(1,1)$ and $0$ otherwise.`"
— the constants at `ε = (1,1)` (at `N = 1`, `J² = 1` and the numerator is `g`). -/
theorem Gnum_one_zero_pp (τ : ℍ) :
    Gnum τ 1 0 (1, 1) = Submodule.span ℂ {fun _ => 1} ∧ Gnum τ 0 1 (1, 1) = Submodule.span ℂ {fun _ => 1} := by
  have key : ∀ {n m : ℕ}, n + m = 1 → Gnum τ n m (1, 1) = Submodule.span ℂ {fun _ => 1} := by
    intro n m h1
    apply le_antisymm
    · intro a ha
      obtain ⟨u⟩ : Nonempty (Fin (n + m) → ℂ) := inferInstance
      rw [Submodule.mem_span_singleton]
      refine ⟨a u, funext fun v => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      exact ((Gnum_single_dev τ h1 ha u).1 v).symm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact const_mem_Gnum_single_dev τ h1 1
  exact ⟨key (by norm_num), key (by norm_num)⟩

/-- **Lemma C.D(a)**: "`Also $\kzG(1,0;\varepsilon)=\kzG(0,1;\varepsilon)$, which is $\C$ (the constants) if $\varepsilon=(1,1)$ and $0$ otherwise.`"
— zero otherwise. -/
theorem Gnum_one_zero_ne (τ : ℍ) {ε : ℂ × ℂ} (hε : ε ≠ (1, 1)) : Gnum τ 1 0 ε = ⊥ ∧ Gnum τ 0 1 ε = ⊥ := by
  have key : ∀ {n m : ℕ}, n + m = 1 → Gnum τ n m ε = ⊥ := by
    intro n m h1
    rw [eq_bot_iff]
    intro a ha
    rw [Submodule.mem_bot]
    funext v
    have h := Gnum_single_dev τ h1 ha v
    by_contra hne
    exact hε (h.2 hne)
  exact ⟨key (by norm_num), key (by norm_num)⟩

/-- **Lemma C.D(b)**: "`Let $n,m\ge1$, $g\in\kzG(n,m;\varepsilon)$ and $\mu(g)=0$. Then $g$ is constant.`" — in numerator
form, `a = c J²` (the proof: "`So $G_{ak}=v^2\cdot(\text{holomorphic})$`", then Liouville in each variable). -/
theorem lemD_b (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) (hmu : mu τ a = 0) : ∃ c : ℂ, ∀ u, a u = c * Jfun τ u ^ 2 := by
  by_cases hroot : ε.1 ^ ((n + 1) + (m + 1)) = 1 ∧ ε.2 ^ ((n + 1) + (m + 1)) = 1
  swap
  · have hb := Gnum_eq_bot_of_not_root τ (n + 1) (m + 1) hroot
    have h0 : a ∈ (⊥ : Submodule ℂ ((Fin ((n + 1) + (m + 1)) → ℂ) → ℂ)) := hb ▸ ha
    have ha0 : a = 0 := (Submodule.mem_bot ℂ).1 h0
    exact ⟨0, fun u => by rw [ha0]; simp⟩
  have hε1 : ε.1 ≠ 0 := fun h => by
    have h1 := hroot.1
    rw [h, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  have hε2 : ε.2 ≠ 0 := fun h => by
    have h1 := hroot.2
    rw [h, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  obtain ⟨_, _, _, _, _, hC1, _⟩ := id ha
  refine const_of_Jdiv_dev τ (by omega) ha fun i j hij => ?_
  by_cases hss : SameSpecies (n + 1) i j
  · intro u l hl k hk
    exact hC1 i j hij hss u l hl k (by omega)
  · have hlt : (i : ℕ) < (j : ℕ) := hij
    have hi : (i : ℕ) < n + 1 := by
      by_contra h
      exact hss (Iff.intro (fun h' => absurd h' h) (fun h' => by omega))
    have hj : n + 1 ≤ (j : ℕ) := by
      by_contra h
      exact hss (Iff.intro (fun _ => by omega) (fun _ => hi))
    exact updown_vanish_dev τ ha hmu hε1 hε2 hi hj

/-- **Lemma C.D(b)**: "`Hence $g=0$ if $\max(n,m)\ge2$ or $\varepsilon\neq(1,1)$.`" (in the sector `(n + 1, m + 1)`,
`max ≥ 2` is `1 ≤ n ∨ 1 ≤ m`). -/
theorem lemD_b_zero (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ}
    (ha : a ∈ Gnum τ (n + 1) (m + 1) ε) (hmu : mu τ a = 0) (h : 1 ≤ n ∨ 1 ≤ m ∨ ε ≠ (1, 1)) : a = 0 := by
  obtain ⟨c, hc⟩ := lemD_b τ ha hmu
  obtain ⟨_, _, ha1, haτ, has, _, _⟩ := ha
  obtain ⟨u₀, hu₀⟩ := exists_Jfun_ne_zero_dev τ ((n + 1) + (m + 1))
  have hJ : Jfun τ u₀ ^ 2 ≠ 0 := pow_ne_zero 2 hu₀
  suffices hc0 : c = 0 by
    funext u
    rw [hc u, hc0, zero_mul]
    rfl
  have hswap : ∀ s t : Fin ((n + 1) + (m + 1)), s ≠ t → SameSpecies (n + 1) s t → c = 0 := by
    intro s t hst hss
    have h1 := has s t hst hss u₀
    rw [hc, hc, Jfun_sq_perm] at h1
    have h2 : c * Jfun τ u₀ ^ 2 = 0 := by linear_combination h1 / 2
    exact (mul_eq_zero.1 h2).resolve_right hJ
  rcases h with h | h | h
  · have hlt : 1 < n + 1 := by omega
    refine hswap (Fin.castAdd (m + 1) 0) (Fin.castAdd (m + 1) ⟨1, hlt⟩) ?_ ?_
    · intro he
      have := congrArg Fin.val he
      simp at this
    · simp [SameSpecies, hlt]
  · have hlt : 1 < m + 1 := by omega
    refine hswap (Fin.natAdd (n + 1) 0) (Fin.natAdd (n + 1) ⟨1, hlt⟩) ?_ ?_
    · intro he
      have := congrArg Fin.val he
      simp at this
    · simp [SameSpecies]
  · by_contra hc0
    apply h
    have k₀ : Fin ((n + 1) + (m + 1)) := Fin.castAdd (m + 1) 0
    have e1 := ha1 u₀ k₀
    rw [hc, hc, Jfun_sq_add_one] at e1
    have eτ := haτ u₀ k₀
    rw [hc, hc, Jfun_sq_add_tau] at eτ
    have hX := Complex.exp_ne_zero (-2 * π * I * ((((n + 1) + (m + 1) : ℕ) : ℂ) - 1) * τ -
      4 * π * I * ((((n + 1) + (m + 1) : ℕ) : ℂ) * u₀ k₀ - ∑ i, u₀ i))
    have hε1 : ε.1 = 1 := by
      have h' : (ε.1 - 1) * (c * Jfun τ u₀ ^ 2) = 0 := by linear_combination -e1
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact sub_eq_zero.1 h''
      · exact absurd h'' (mul_ne_zero hc0 hJ)
    have hε2 : ε.2 = 1 := by
      have h' : (ε.2 - 1) * (c * (cexp (-2 * π * I * ((((n + 1) + (m + 1) : ℕ) : ℂ) - 1) * τ -
          4 * π * I * ((((n + 1) + (m + 1) : ℕ) : ℂ) * u₀ k₀ - ∑ i, u₀ i)) * Jfun τ u₀ ^ 2)) = 0 := by
        linear_combination -eτ
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact sub_eq_zero.1 h''
      · exact absurd h'' (mul_ne_zero hc0 (mul_ne_zero hX hJ))
    exact Prod.ext hε1 hε2

/-! ## Proposition C.induct -/

/-- **Proposition C.induct**: "`and injective (Lemma~\ref{kz:lem:D}(b))`" — for `max(n,m) ≥ 2` in the sector
`(n + 1, m + 1)`, the merge is injective. -/
theorem muL_injective (τ : ℍ) {n m : ℕ} (h : 1 ≤ n ∨ 1 ≤ m) (ε : ℂ × ℂ) : Function.Injective (muL τ n m ε) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hmu : mu τ (x : (Fin ((n + 1) + (m + 1)) → ℂ) → ℂ) = 0 := congrArg Subtype.val hx
  have h0 := lemD_b_zero τ x.2 hmu (by rcases h with h | h; exact Or.inl h; exact Or.inr (Or.inl h))
  exact Subtype.ext h0

/-- **Proposition C.induct**: "`Let $n,m\ge1$ with $\max(n,m)\ge2$. If $\varepsilon_1^2=\varepsilon_2^2=1$ then $\dim\kzG(n,m;\varepsilon)\le\dim\kzG(n-1,m-1;\varepsilon)$; otherwise $\kzG(n,m;\varepsilon)=0$.`"
— the inequality, with the finite dimension it carries up (for every `ε`; for `ε² ≠ 1` both sides vanish). -/
theorem finrank_Gnum_le_merge (τ : ℍ) {n m : ℕ} (h : 1 ≤ n ∨ 1 ≤ m) (ε : ℂ × ℂ)
    (hfin : FiniteDimensional ℂ (Gnum τ n m ε)) :
    FiniteDimensional ℂ (Gnum τ (n + 1) (m + 1) ε) ∧
      Module.finrank ℂ (Gnum τ (n + 1) (m + 1) ε) ≤ Module.finrank ℂ (Gnum τ n m ε) := by
  have hinj := muL_injective τ h ε
  have : FiniteDimensional ℂ (Gnum τ (n + 1) (m + 1) ε) := Module.Finite.of_injective (muL τ n m ε) hinj
  exact ⟨this, LinearMap.finrank_le_finrank_of_injective hinj⟩

/-- **Proposition C.induct**: "`Let $n,m\ge1$ with $\max(n,m)\ge2$. If $\varepsilon_1^2=\varepsilon_2^2=1$ then $\dim\kzG(n,m;\varepsilon)\le\dim\kzG(n-1,m-1;\varepsilon)$; otherwise $\kzG(n,m;\varepsilon)=0$.`"
— the vanishing. -/
theorem Gnum_eq_bot_of_merge (τ : ℍ) {n m : ℕ} (h : 1 ≤ n ∨ 1 ≤ m) {ε : ℂ × ℂ}
    (hε : ¬ (ε.1 ^ 2 = 1 ∧ ε.2 ^ 2 = 1)) : Gnum τ (n + 1) (m + 1) ε = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have h0 : muL τ n m ε ⟨a, ha⟩ = muL τ n m ε 0 := by
    rw [map_zero]
    exact Subtype.ext (lemC_c_zero τ ha hε)
  rw [Submodule.mem_bot]
  exact congrArg Subtype.val (muL_injective τ h ε h0)

/-! ## Proposition C.base -/

/-- **Proposition C.base(a)**: "`$\kzG(0,0;\varepsilon)=\C$; $\kzG(k,0;\varepsilon)=\kzG(0,k;\varepsilon)=0$ for $k\ge2$; $\kzG(1,0;\varepsilon)=\kzG(0,1;\varepsilon)=\C\,\delta_{\varepsilon,(1,1)}$.`"
— "`(a) is Lemma~\ref{kz:lem:D}(a).`": the conjunction of `Gnum_zero_zero`, `Gnum_polarized`, `Gnum_one_zero_pp` and
`Gnum_one_zero_ne`. -/
theorem base_a (τ : ℍ) (ε : ℂ × ℂ) :
    Gnum τ 0 0 ε = ⊤ ∧ (∀ k, 2 ≤ k → Gnum τ k 0 ε = ⊥ ∧ Gnum τ 0 k ε = ⊥) ∧
      (ε = (1, 1) → Gnum τ 1 0 ε = Submodule.span ℂ {fun _ => 1} ∧ Gnum τ 0 1 ε = Submodule.span ℂ {fun _ => 1}) ∧
      (ε ≠ (1, 1) → Gnum τ 1 0 ε = ⊥ ∧ Gnum τ 0 1 ε = ⊥) :=
  ⟨Gnum_zero_zero τ ε, fun _ hk => Gnum_polarized τ hk ε, fun h => h ▸ Gnum_one_zero_pp τ,
    fun h => Gnum_one_zero_ne τ h⟩

/-! ### Proof devices for Proposition C.base(b), (c) (proof phase, round two; not statements of the paper)

At `N = 2`, `J = ϑ₁(u₀ − u₁)` (`Jfun_two_dev`); `J²` is a numerator at `ε = (1,1)` ((iii) and (C1) are vacuous, (C2)
holds since each slice of `J²` has a double zero on the diagonal, `Jsq_slice_deriv_dev`), and its merge vanishes
(`mu_Jsq_dev`). The merge of the numerator of `℘_ε(x₁ − y₁)` is `1` (the proof of Proposition C.base: "`$\mu(\wp)=1$`";
the numerator form of F1-lower's `merge_dEps` at `p = 0`): its value on the diagonal is the limit of `ϑ₁(v)²℘_ε(v)`,
which is `ϑ₁'(0)²` (Mathlib's `hasDerivAt_iff_tendsto_slope` and F1-lower's `tendsto_sq_mul_of_dev`,
`not_mem_Λu_punctured_dev`; `numerator_const_dEps_one_dev`). Then `a − μ(a)·f` has merge `0`, and Lemma C.D(b)
applies; the linearity of `μ` in this sector is `mu_lin_one_dev`, `mu_sub_smul_one_dev`. -/

theorem Jfun_two_dev (τ : ℂ) (u : Fin (1 + 1) → ℂ) : Jfun τ u = theta1 (u 0 - u 1) τ := by
  rw [Jfun_eq_pairs_dev]
  have h : pairsLT_dev (1 + 1) = {((0 : Fin (1 + 1)), (1 : Fin (1 + 1)))} := by decide
  rw [h, Finset.prod_singleton]

theorem Jsq_slice_deriv_dev (τ : ℍ) {N : ℕ} {i j : Fin N} (hij : i ≠ j) (u : Fin N → ℂ) (hu : u i = u j) :
    deriv (fun z => Jfun τ (Function.update u i z) ^ 2) (u i) = 0 := by
  obtain ⟨K, hK, hJK⟩ := Jfun_sq_factor τ hij
  have hθ0 : theta1 (u i - u j) τ = 0 := by
    rw [hu, sub_self]
    exact (theta1_eq_zero_iff τ 0).2 (zero_mem_Λu_dev τ)
  obtain ⟨h₁, hh₁, _, hevh⟩ := theta1_sub_factor_dev τ (c := u j) (z₀ := u i) hθ0
  have hd : Differentiable ℂ fun z => Jfun τ (Function.update u i z) ^ 2 := ((Jfun_isOsgood τ N).2 u i).pow 2
  have h := slice_vanish_of_factor_dev hd (k := 2) (g₁ := fun z => h₁ z ^ 2 * K (Function.update u i z))
    ((hh₁.pow 2).mul ((hK.2 u i).analyticAt (u i))) (by
      filter_upwards [hevh] with z hz
      show Jfun τ (Function.update u i z) ^ 2 = (z - u i) ^ 2 * (h₁ z ^ 2 * K (Function.update u i z))
      rw [hJK, Function.update_self, Function.update_of_ne hij.symm, hz]
      ring)
  have h1 := h 1 (by norm_num)
  rwa [iteratedDeriv_one] at h1

theorem Jsq_mem_Gnum_one_one_dev (τ : ℍ) : (fun u : Fin (1 + 1) → ℂ => Jfun τ u ^ 2) ∈ Gnum τ 1 1 (1, 1) := by
  have hJ := Jfun_isOsgood τ (1 + 1)
  have hsp : ∀ s t : Fin (1 + 1), s ≠ t → ¬ SameSpecies 1 s t := by
    intro s t hst hss
    have hs := s.isLt
    have ht := t.isLt
    have hne : (s : ℕ) ≠ (t : ℕ) := fun h => hst (Fin.ext h)
    rcases Nat.lt_or_ge (s : ℕ) 1 with h | h
    · have := hss.1 h
      omega
    · have : ¬ (t : ℕ) < 1 := fun h' => by
        have := hss.2 h'
        omega
      omega
  rw [mem_Gnum]
  refine ⟨⟨hJ.1.pow 2, fun u i => (hJ.2 u i).pow 2⟩, fun u c => Jfun_sq_add_const τ u c,
    fun u k => ?_, fun u k => ?_, fun s t hst hss => absurd hss (hsp s t hst),
    fun s t hst hss => absurd hss (hsp s t (ne_of_lt hst)), fun s t hs ht u hu => ?_⟩
  · show Jfun τ (Function.update u k (u k + 1)) ^ 2 = 1 * Jfun τ u ^ 2
    rw [Jfun_sq_add_one, one_mul]
  · show Jfun τ (Function.update u k (u k + τ)) ^ 2 = 1 * cexp (-2 * π * I * (((1 + 1 : ℕ) : ℂ) - 1) * τ -
      4 * π * I * (((1 + 1 : ℕ) : ℂ) * u k - ∑ i, u i)) * Jfun τ u ^ 2
    rw [Jfun_sq_add_tau, one_mul]
  · have hst : s ≠ t := fun h => by rw [h] at hs; omega
    show deriv (fun z => Jfun τ (Function.update u s z) ^ 2) (u s) -
      deriv (fun z => Jfun τ (Function.update u t z) ^ 2) (u t) = 0
    rw [Jsq_slice_deriv_dev τ hst u hu, Jsq_slice_deriv_dev τ hst.symm u hu.symm, sub_zero]

theorem mu_Jsq_dev (τ : ℍ) {n m : ℕ} : mu τ (fun u : Fin ((n + 1) + (m + 1)) → ℂ => Jfun τ u ^ 2) = 0 := by
  funext r
  show mergeAt τ (fun u => Jfun τ u ^ 2) (admW τ r) r = 0
  have hJ0 : Jfun τ (mergePt (admW τ r) r) = 0 := by
    rw [Jfun_eq_pairs_dev]
    refine Finset.prod_eq_zero ((mem_pairsLT_dev (Fin.castAdd (m + 1) 0, Fin.natAdd (n + 1) 0)).2 ?_) ?_
    · rw [Fin.lt_def]
      simp
    · show theta1 (mergePt (admW τ r) r (Fin.castAdd (m + 1) 0) - mergePt (admW τ r) r (Fin.natAdd (n + 1) 0)) τ = 0
      rw [mergePt_s0_dev, mergePt_t0_dev, sub_self]
      exact (theta1_eq_zero_iff τ 0).2 (zero_mem_Λu_dev τ)
  simp [mergeAt, hJ0]

theorem mergePt_zero_zero_dev (w : ℂ) (r : Fin (0 + 0) → ℂ) :
    mergePt (n := 0) (m := 0) w r = fun _ : Fin (1 + 1) => w := by
  funext j
  induction j using Fin.addCases with
  | left a' =>
    induction a' using Fin.cases with
    | zero => exact mergePt_s0_dev w r
    | succ a => exact a.elim0
  | right b' =>
    induction b' using Fin.cases with
    | zero => exact mergePt_t0_dev w r
    | succ k => exact k.elim0

theorem numerator_const_dEps_one_dev (τ : ℍ) (ε : Eps) {f : (Fin (1 + 1) → ℂ) → ℂ}
    (hf : IsNumerator τ 1 1 (fun _ => 1) (dEps τ ε 1) f) (w : ℂ) :
    f (fun _ => w) = deriv (fun z => theta1 z τ) 0 ^ 2 := by
  have hθ0 : theta1 0 τ = 0 := (theta1_eq_zero_iff τ 0).2 (zero_mem_Λu_dev τ)
  have e0 : (Fin.castAdd 1 (0 : Fin 1) : Fin (1 + 1)) = 0 := rfl
  have e1 : (Fin.natAdd 1 (0 : Fin 1) : Fin (1 + 1)) = 1 := rfl
  have h10 : (1 : Fin (1 + 1)) ≠ 0 := by decide
  have hpc : Continuous fun v : ℂ => Function.update (fun _ : Fin (1 + 1) => w) 0 (w + v) :=
    (continuous_const : Continuous fun _ : ℂ => fun _ : Fin (1 + 1) => w).update 0
      (continuous_const.add continuous_id)
  have hp0 : Function.update (fun _ : Fin (1 + 1) => w) 0 (w + 0) = fun _ => w :=
    Function.update_eq_self_iff.2 (add_zero w)
  have hcont : Filter.Tendsto (fun v => f (Function.update (fun _ : Fin (1 + 1) => w) 0 (w + v)))
      (nhdsWithin 0 {0}ᶜ) (nhds (f fun _ => w)) := by
    have h := (hf.1.1.comp hpc).tendsto' 0 (f fun _ => w) (by simp only [Function.comp_apply]; rw [hp0])
    exact h.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  have hval : ∀ v, v ∉ Λu τ →
      f (Function.update (fun _ : Fin (1 + 1) => w) 0 (w + v)) = theta1 v τ ^ 2 * wpE τ ε v := by
    intro v hv
    have hpol : Function.update (fun _ : Fin (1 + 1) => w) 0 (w + v) ∉ polarSet τ 1 1 := by
      rintro ⟨a, k, hak⟩
      apply hv
      have ha : a = 0 := Subsingleton.elim a 0
      have hk : k = 0 := Subsingleton.elim k 0
      subst ha hk
      rw [e0, e1, Function.update_self, Function.update_of_ne h10, add_sub_cancel_left] at hak
      exact hak
    rw [hf.2 _ hpol]
    simp only [stateFun]
    rw [dEps_one, Jfun_two_dev, e0, e1, Function.update_self, Function.update_of_ne h10, add_sub_cancel_left,
      one_mul]
  have hlim : Filter.Tendsto (fun v => theta1 v τ ^ 2 * wpE τ ε v) (nhdsWithin 0 {0}ᶜ)
      (nhds (deriv (fun z => theta1 z τ) 0 ^ 2)) := by
    have hs := hasDerivAt_iff_tendsto_slope.1 (theta1_differentiable τ 0).hasDerivAt
    have hw := tendsto_sq_mul_of_dev (wpE_sub_inv_sq_analyticAt τ ε)
    have h := (hs.pow 2).mul hw
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv' : v ≠ 0 := hv
    rw [slope_def_field, hθ0, sub_zero, sub_zero, div_pow, div_mul_eq_mul_div,
      div_eq_iff (pow_ne_zero 2 hv')]
    ring
  have hev : (fun v => f (Function.update (fun _ : Fin (1 + 1) => w) 0 (w + v))) =ᶠ[nhdsWithin 0 {0}ᶜ]
      fun v => theta1 v τ ^ 2 * wpE τ ε v := by
    filter_upwards [not_mem_Λu_punctured_dev τ (zero_mem_Λu_dev τ)] with v hv
    exact hval v hv
  exact tendsto_nhds_unique (hcont.congr' hev) hlim

theorem mu_numerator_dEps_one_dev (τ : ℍ) (ε : Eps) {f : (Fin (1 + 1) → ℂ) → ℂ}
    (hf : IsNumerator τ 1 1 (fun _ => 1) (dEps τ ε 1) f) : mu τ (n := 0) (m := 0) f = fun _ => 1 := by
  funext r
  show mergeAt τ (n := 0) (m := 0) f (admW τ r) r = 1
  unfold mergeAt
  rw [mergePt_zero_zero_dev, numerator_const_dEps_one_dev τ ε hf]
  have hE : Emerge (τ : ℂ) (admW τ r) r = 1 := by simp [Emerge]
  rw [hE, mul_one, div_self (pow_ne_zero 2 (theta1_deriv_zero_ne_zero τ))]

theorem mu_sub_smul_one_dev (τ : ℍ) (a b : (Fin (1 + 1) → ℂ) → ℂ) (c : ℂ) (r : Fin (0 + 0) → ℂ) :
    mu τ (n := 0) (m := 0) (a - c • b) r = mu τ (n := 0) (m := 0) a r - c * mu τ (n := 0) (m := 0) b r := by
  simp only [mu, mergeAt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem mu_lin_one_dev (τ : ℍ) (a b : (Fin (1 + 1) → ℂ) → ℂ) (s t : ℂ) (r : Fin (0 + 0) → ℂ) :
    mu τ (n := 0) (m := 0) (s • a + t • b) r =
      s * mu τ (n := 0) (m := 0) a r + t * mu τ (n := 0) (m := 0) b r := by
  simp only [mu, mergeAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Proposition C.base(b)**: "`$\kzG(1,1;(1,1))=\mathrm{span}\{\wp(x_1-y_1),\,1\}$, of dimension $2$.`" — in numerator
form: spanned by the numerator of `℘(x_1 − y_1)` (F1-lower's `dEps … .pp 1`, `dEps_one`) and `J² = ϑ₁(x_1 − y_1)²`, the
numerator of `g = 1`. -/
theorem Gnum_one_one_pp (τ : ℍ) {f : (Fin (1 + 1) → ℂ) → ℂ} (hf : IsNumerator τ 1 1 (fun _ => 1) (dEps τ .pp 1) f) :
    Gnum τ 1 1 (1, 1) = Submodule.span ℂ {f, fun u => Jfun τ u ^ 2} := by
  have hfm : f ∈ Gnum τ 1 1 (1, 1) := dEps_numerator_one_mem τ .pp 1 hf
  have hJm := Jsq_mem_Gnum_one_one_dev τ
  have hmuf := mu_numerator_dEps_one_dev τ .pp hf
  apply le_antisymm
  · intro a ha
    obtain ⟨r₀⟩ : Nonempty (Fin (0 + 0) → ℂ) := inferInstance
    have hb : a - mu τ (n := 0) (m := 0) a r₀ • f ∈ Gnum τ 1 1 (1, 1) :=
      Submodule.sub_mem _ ha (Submodule.smul_mem _ _ hfm)
    have hmub : mu τ (n := 0) (m := 0) (a - mu τ (n := 0) (m := 0) a r₀ • f) = 0 := by
      funext r
      show mu τ (n := 0) (m := 0) (a - mu τ (n := 0) (m := 0) a r₀ • f) r = 0
      rw [mu_sub_smul_one_dev, hmuf, show r = r₀ from funext fun i => i.elim0]
      simp
    obtain ⟨c', hc'⟩ := lemD_b τ (n := 0) (m := 0) hb hmub
    rw [Submodule.mem_span_pair]
    refine ⟨mu τ (n := 0) (m := 0) a r₀, c', funext fun u => ?_⟩
    have h := hc' u
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -h
  · rw [Submodule.span_le]
    exact Set.insert_subset_iff.2 ⟨hfm, Set.singleton_subset_iff.2 hJm⟩

/-- **Proposition C.base(b)**: "`$\kzG(1,1;(1,1))=\mathrm{span}\{\wp(x_1-y_1),\,1\}$, of dimension $2$.`" — the dimension. -/
theorem finrank_Gnum_one_one_pp (τ : ℍ) :
    FiniteDimensional ℂ (Gnum τ 1 1 (1, 1)) ∧ Module.finrank ℂ (Gnum τ 1 1 (1, 1)) = 2 := by
  obtain ⟨f, hf⟩ := dEps_numerator_one_exists τ .pp 1
  rw [Gnum_one_one_pp τ hf]
  have hli : LinearIndependent ℂ ![f, fun u : Fin (1 + 1) → ℂ => Jfun τ u ^ 2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    obtain ⟨r₀⟩ : Nonempty (Fin (0 + 0) → ℂ) := inferInstance
    have h := congrFun (congrArg (mu τ (n := 0) (m := 0)) hst) r₀
    have h0 : mu τ (n := 0) (m := 0) (0 : (Fin (1 + 1) → ℂ) → ℂ) r₀ = 0 := by simp [mu, mergeAt]
    have hmJ : mu τ (n := 0) (m := 0) (fun u : Fin (1 + 1) → ℂ => Jfun τ u ^ 2) r₀ = 0 :=
      congrFun (mu_Jsq_dev τ (n := 0) (m := 0)) r₀
    rw [mu_lin_one_dev, mu_numerator_dEps_one_dev τ .pp hf, hmJ, h0] at h
    have hs : s = 0 := by simpa using h
    subst hs
    refine ⟨rfl, ?_⟩
    obtain ⟨u₀, hu₀⟩ := exists_Jfun_ne_zero_dev τ (1 + 1)
    have h2 := congrFun hst u₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, zero_add, Pi.zero_apply] at h2
    exact (mul_eq_zero.1 h2).resolve_right (pow_ne_zero 2 hu₀)
  refine ⟨Module.Finite.span_of_finite ℂ ((Set.finite_singleton _).insert _), ?_⟩
  rw [← Matrix.range_cons_cons_empty f (fun u : Fin (1 + 1) → ℂ => Jfun τ u ^ 2) ![], finrank_span_eq_card hli,
    Fintype.card_fin]

/-- **Proposition C.base(c)**: "`For $\varepsilon\in\{\pm1\}^2\setminus\{(1,1)\}$: $\kzG(1,1;\varepsilon)=\C\,\wp_\varepsilon(x_1-y_1)$, of dimension $1$.`"
— in numerator form: spanned by the numerator of `℘_ε(x_1 − y_1)` (`dEps … ε 1`). -/
theorem Gnum_one_one_eps (τ : ℍ) {ε : Eps} (hε : ε ≠ .pp) {f : (Fin (1 + 1) → ℂ) → ℂ}
    (hf : IsNumerator τ 1 1 (fun _ => 1) (dEps τ ε 1) f) : Gnum τ 1 1 ε.pair = Submodule.span ℂ {f} := by
  have hfm : f ∈ Gnum τ 1 1 ε.pair := dEps_numerator_one_mem τ ε 1 hf
  have hmuf := mu_numerator_dEps_one_dev τ ε hf
  have hne : ε.pair ≠ (1, 1) := by
    intro h
    apply hε
    cases ε with
    | pp => rfl
    | mp => exact absurd (congrArg Prod.fst h) (by norm_num [Eps.pair, Eps.e1])
    | pm => exact absurd (congrArg Prod.snd h) (by norm_num [Eps.pair, Eps.e2])
    | mm => exact absurd (congrArg Prod.fst h) (by norm_num [Eps.pair, Eps.e1])
  apply le_antisymm
  · intro a ha
    obtain ⟨r₀⟩ : Nonempty (Fin (0 + 0) → ℂ) := inferInstance
    have hb : a - mu τ (n := 0) (m := 0) a r₀ • f ∈ Gnum τ 1 1 ε.pair :=
      Submodule.sub_mem _ ha (Submodule.smul_mem _ _ hfm)
    have hmub : mu τ (n := 0) (m := 0) (a - mu τ (n := 0) (m := 0) a r₀ • f) = 0 := by
      funext r
      show mu τ (n := 0) (m := 0) (a - mu τ (n := 0) (m := 0) a r₀ • f) r = 0
      rw [mu_sub_smul_one_dev, hmuf, show r = r₀ from funext fun i => i.elim0]
      simp
    have h0 := lemD_b_zero τ (n := 0) (m := 0) hb hmub (Or.inr (Or.inr hne))
    rw [Submodule.mem_span_singleton]
    exact ⟨mu τ (n := 0) (m := 0) a r₀, (sub_eq_zero.1 h0).symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hfm

/-- **Proposition C.base(c)**: the dimension. -/
theorem finrank_Gnum_one_one_eps (τ : ℍ) {ε : Eps} (hε : ε ≠ .pp) :
    FiniteDimensional ℂ (Gnum τ 1 1 ε.pair) ∧ Module.finrank ℂ (Gnum τ 1 1 ε.pair) = 1 := by
  obtain ⟨f, hf⟩ := dEps_numerator_one_exists τ ε 1
  rw [Gnum_one_one_eps τ hε hf]
  have hf0 : f ≠ 0 := by
    intro h0
    obtain ⟨r₀⟩ : Nonempty (Fin (0 + 0) → ℂ) := inferInstance
    have h1 := congrFun (mu_numerator_dEps_one_dev τ ε hf) r₀
    rw [h0] at h1
    simp [mu, mergeAt] at h1
  exact ⟨Module.Finite.span_of_finite ℂ (Set.finite_singleton f), finrank_span_singleton hf0⟩

/-- **Proposition C.base(d)**: "`$\kzG(1,1;\varepsilon)=0$ if $\varepsilon^2\neq1$.`" -/
theorem Gnum_one_one_eq_bot (τ : ℍ) {ε : ℂ × ℂ} (hε : ¬ (ε.1 ^ 2 = 1 ∧ ε.2 ^ 2 = 1)) : Gnum τ 1 1 ε = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have hne : ε ≠ (1, 1) := by
    rintro rfl
    exact hε ⟨by norm_num, by norm_num⟩
  rw [Submodule.mem_bot]
  exact lemD_b_zero τ (n := 0) (m := 0) ha (lemC_c_zero τ ha hε) (Or.inr (Or.inr hne))

/-! ## Corollary C.bounds -/

/-! ### Proof devices for Corollary C.bounds (proof phase, round two; not statements of the paper): a merge into a
zero space comes from a zero space (`muL_injective`); `ε ∈ {±1}²` is a sign pair; `𝒢(1,1;ε)` is finite-dimensional
(Proposition C.base(b)–(d)) -/

theorem Gnum_bot_of_merge_dev (τ : ℍ) {n m : ℕ} (h : 1 ≤ n ∨ 1 ≤ m) (ε : ℂ × ℂ) (hb : Gnum τ n m ε = ⊥) :
    Gnum τ (n + 1) (m + 1) ε = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have hz : ∀ f, f ∈ Gnum τ n m ε → f = 0 := fun f hf => by
    rw [hb] at hf
    exact (Submodule.mem_bot ℂ).1 hf
  have h0 : muL τ n m ε ⟨a, ha⟩ = muL τ n m ε 0 := by
    rw [map_zero]
    exact Subtype.ext (hz _ (muL τ n m ε ⟨a, ha⟩).2)
  rw [Submodule.mem_bot]
  exact congrArg Subtype.val (muL_injective τ h ε h0)

theorem exists_eps_pair_dev {ε : ℂ × ℂ} (h : ε.1 ^ 2 = 1 ∧ ε.2 ^ 2 = 1) : ∃ e : Eps, ε = e.pair := by
  obtain ⟨h1, h2⟩ := h
  rcases mul_self_eq_one_iff.1 ((sq ε.1).symm.trans h1) with e1 | e1 <;>
    rcases mul_self_eq_one_iff.1 ((sq ε.2).symm.trans h2) with e2 | e2
  · exact ⟨.pp, Prod.ext (by simp [Eps.pair, Eps.e1, e1]) (by simp [Eps.pair, Eps.e2, e2])⟩
  · exact ⟨.pm, Prod.ext (by simp [Eps.pair, Eps.e1, e1]) (by simp [Eps.pair, Eps.e2, e2])⟩
  · exact ⟨.mp, Prod.ext (by simp [Eps.pair, Eps.e1, e1]) (by simp [Eps.pair, Eps.e2, e2])⟩
  · exact ⟨.mm, Prod.ext (by simp [Eps.pair, Eps.e1, e1]) (by simp [Eps.pair, Eps.e2, e2])⟩

theorem finiteDimensional_Gnum_one_one_dev (τ : ℍ) (ε : ℂ × ℂ) : FiniteDimensional ℂ (Gnum τ 1 1 ε) := by
  by_cases h : ε.1 ^ 2 = 1 ∧ ε.2 ^ 2 = 1
  · obtain ⟨e, rfl⟩ := exists_eps_pair_dev h
    by_cases he : e = .pp
    · subst he
      exact (finrank_Gnum_one_one_pp τ).1
    · exact (finrank_Gnum_one_one_eps τ he).1
  · rw [Gnum_one_one_eq_bot τ h]
    infer_instance

/-- **Corollary C.bounds(a)**: "`If $|n-m|\ge2$ then $\kzG(n,m;\varepsilon)=0$.`" -/
theorem Gnum_eq_bot_of_imbalanced (τ : ℍ) {n m : ℕ} (h : n + 2 ≤ m ∨ m + 2 ≤ n) (ε : ℂ × ℂ) : Gnum τ n m ε = ⊥ := by
  induction n generalizing m with
  | zero =>
    rcases h with h | h
    · exact (Gnum_polarized τ (k := m) (by omega) ε).2
    · omega
  | succ n ih =>
    cases m with
    | zero =>
      rcases h with h | h
      · omega
      · exact (Gnum_polarized τ (k := n + 1) (by omega) ε).1
    | succ m =>
      exact Gnum_bot_of_merge_dev τ (by omega) ε (ih (m := m) (by omega))

/-- **Corollary C.bounds(b)**: "`$\dim\kzG(m+1,m;\varepsilon)\le\delta_{\varepsilon,(1,1)}$`" — at `ε = (1,1)`, with the
species exchanged as well (Theorem C.T2(ii): "`$S_z=-\tfrac12$ is the same with the species exchanged.`"). -/
theorem finrank_Gnum_odd_pp (τ : ℍ) (m : ℕ) :
    (FiniteDimensional ℂ (Gnum τ (m + 1) m (1, 1)) ∧ Module.finrank ℂ (Gnum τ (m + 1) m (1, 1)) ≤ 1) ∧
      (FiniteDimensional ℂ (Gnum τ m (m + 1) (1, 1)) ∧ Module.finrank ℂ (Gnum τ m (m + 1) (1, 1)) ≤ 1) := by
  induction m with
  | zero =>
    obtain ⟨h1, h2⟩ := Gnum_one_zero_pp τ
    have hv1 : (fun _ : Fin (1 + 0) → ℂ => (1 : ℂ)) ≠ 0 := fun h => one_ne_zero (congrFun h fun _ => 0)
    have hv2 : (fun _ : Fin (0 + 1) → ℂ => (1 : ℂ)) ≠ 0 := fun h => one_ne_zero (congrFun h fun _ => 0)
    refine ⟨?_, ?_⟩
    · show FiniteDimensional ℂ (Gnum τ 1 0 (1, 1)) ∧ Module.finrank ℂ (Gnum τ 1 0 (1, 1)) ≤ 1
      rw [h1]
      exact ⟨inferInstance, (finrank_span_singleton hv1).le⟩
    · show FiniteDimensional ℂ (Gnum τ 0 1 (1, 1)) ∧ Module.finrank ℂ (Gnum τ 0 1 (1, 1)) ≤ 1
      rw [h2]
      exact ⟨inferInstance, (finrank_span_singleton hv2).le⟩
  | succ m ih =>
    obtain ⟨⟨hf1, hr1⟩, ⟨hf2, hr2⟩⟩ := ih
    obtain ⟨hf1', hr1'⟩ := finrank_Gnum_le_merge τ (n := m + 1) (m := m) (Or.inl (by omega)) (1, 1) hf1
    obtain ⟨hf2', hr2'⟩ := finrank_Gnum_le_merge τ (n := m) (m := m + 1) (Or.inr (by omega)) (1, 1) hf2
    exact ⟨⟨hf1', hr1'.trans hr1⟩, ⟨hf2', hr2'.trans hr2⟩⟩

/-- **Corollary C.bounds(b)**: "`$\dim\kzG(m+1,m;\varepsilon)\le\delta_{\varepsilon,(1,1)}$`" — zero for `ε ≠ (1,1)`, with
the species exchanged as well. -/
theorem Gnum_odd_eq_bot (τ : ℍ) (m : ℕ) {ε : ℂ × ℂ} (hε : ε ≠ (1, 1)) :
    Gnum τ (m + 1) m ε = ⊥ ∧ Gnum τ m (m + 1) ε = ⊥ := by
  induction m with
  | zero => exact Gnum_one_zero_ne τ hε
  | succ m ih =>
    exact ⟨Gnum_bot_of_merge_dev τ (n := m + 1) (m := m) (Or.inl (by omega)) ε ih.1,
      Gnum_bot_of_merge_dev τ (n := m) (m := m + 1) (Or.inr (by omega)) ε ih.2⟩

/-- **Corollary C.bounds(c)**: "`$\dim\kzG(p,p;\varepsilon)\le\dim\kzG(1,1;\varepsilon)$, which is $2$, $1$ or $0$ as in Proposition~\ref{kz:prop:base}`"
— the inequality, with the finite dimension (`p = q + 1`). -/
theorem finrank_Gnum_even_le (τ : ℍ) (q : ℕ) (ε : ℂ × ℂ) :
    FiniteDimensional ℂ (Gnum τ (q + 1) (q + 1) ε) ∧
      Module.finrank ℂ (Gnum τ (q + 1) (q + 1) ε) ≤ Module.finrank ℂ (Gnum τ 1 1 ε) := by
  induction q with
  | zero => exact ⟨finiteDimensional_Gnum_one_one_dev τ ε, le_rfl⟩
  | succ q ih =>
    obtain ⟨hf, hr⟩ := ih
    obtain ⟨hf', hr'⟩ := finrank_Gnum_le_merge τ (n := q + 1) (m := q + 1) (Or.inl (by omega)) ε hf
    exact ⟨hf', hr'.trans hr⟩

/-- **Corollary C.bounds(c)**: "`$\dim\kzG(p,p;\varepsilon)\le\dim\kzG(1,1;\varepsilon)$, which is $2$, $1$ or $0$ as in Proposition~\ref{kz:prop:base}`"
— for `ε ∈ {±1}²`: at most `2` at `(1,1)`, at most `1` otherwise. -/
theorem finrank_Gnum_even_eps (τ : ℍ) (q : ℕ) (ε : Eps) :
    FiniteDimensional ℂ (Gnum τ (q + 1) (q + 1) ε.pair) ∧
      Module.finrank ℂ (Gnum τ (q + 1) (q + 1) ε.pair) ≤ if ε = .pp then 2 else 1 := by
  obtain ⟨hf, hr⟩ := finrank_Gnum_even_le τ q ε.pair
  refine ⟨hf, hr.trans ?_⟩
  by_cases he : ε = .pp
  · subst he
    rw [ite_eq_left rfl]
    exact (finrank_Gnum_one_one_pp τ).2.le
  · rw [ite_eq_right he]
    exact (finrank_Gnum_one_one_eps τ he).2.le

/-- **Corollary C.bounds**, with Proposition C.induct and C.base(d): `𝒢(n,m;ε) = 0` for `ε² ≠ 1` in every sector with
`N ≥ 1` ("`Iterate Proposition~\ref{kz:prop:induct} along $(n,m)\to(n-1,m-1)\to\cdots$, ending at $(|n-m|,0)$ or $(0,|n-m|)$, at $(1,0)$, or at $(1,1)$; every intermediate step has $\max\ge2$.`"). -/
theorem Gnum_eq_bot_of_sq_ne_one (τ : ℍ) {n m : ℕ} (hN : 0 < n + m) {ε : ℂ × ℂ}
    (hε : ¬ (ε.1 ^ 2 = 1 ∧ ε.2 ^ 2 = 1)) : Gnum τ n m ε = ⊥ := by
  have hne : ε ≠ (1, 1) := by
    rintro rfl
    exact hε ⟨by norm_num, by norm_num⟩
  rcases n with _ | n <;> rcases m with _ | m
  · omega
  · rcases m with _ | m
    · exact (Gnum_one_zero_ne τ hne).2
    · exact (Gnum_polarized τ (k := m + 1 + 1) (by omega) ε).2
  · rcases n with _ | n
    · exact (Gnum_one_zero_ne τ hne).1
    · exact (Gnum_polarized τ (k := n + 1 + 1) (by omega) ε).1
  · by_cases h : 1 ≤ n ∨ 1 ≤ m
    · exact Gnum_eq_bot_of_merge τ h hε
    · have hn : n = 0 := by omega
      have hm : m = 0 := by omega
      subst hn
      subst hm
      exact Gnum_one_one_eq_bot τ hε

end HRTorus.ZeroModes

end -- noncomputable section
