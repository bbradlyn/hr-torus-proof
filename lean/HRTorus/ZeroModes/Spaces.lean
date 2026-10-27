import HRTorus.ZeroModes.Formulation

/-!
# Definition C.G through numerators, `Θ_2[ε]` for `ε ∈ μ_N²`, and Lemma C.B (`ZeroModes.Spaces`)

Written by Claude Opus 5.5 (an AI model), 2026-10-26. **Statement phase and proof phase (2026-10-26): the
definitions and statements were written first, every theorem that carries content `sorry`, and reviewed against the
paper before any proof; the proof phase (round one) then proved every statement, the reviewed text unchanged, four
of Lemma C.B's statements moved after the projector devices their proofs use. The proof devices — the declarations
named `_dev`, in marked sections — are not statements of the paper. The one-line derivations (two membership
lemmas, the dimension of `Θ_2[ε]` from Lemma C.theta(a), the identification of `Θ_2[ε]` with block F1-lower's `Θ2`
for `ε ∈ {±1}²`) are written out.**
The paper: the HR paper, `papers/hr/appendices/C-kernel.tex` — Definition C.`G` (`kz:def:G`), Lemma C.`B` (`kz:lem:B`)
(a)–(c) with the spaces `Θ_2[ε]` for `ε ∈ μ_N²`, the many-body translations `kz:eq:TK-T1`, and the membership in
`𝒢(n,m;ε)` of the explicit functions of Proposition C.`explicit` (`kz:prop:explicit`).

## The model

* **Numerators throughout.** No meromorphic function of several variables is defined. `Gnum τ n m ε` is the space of
  the numerators `a = J²g` of `g ∈ 𝒢(n,m;ε)`: functions on `u = (x, y) : Fin (n + m) → ℂ` in the Osgood class with
  (i) `a(u + c𝟙) = a(u)`; (ii) `a(u + e_k) = ε₁ a(u)`, `a(u + τe_k) = ε₂ e^{−2πi(N−1)τ − 4πi(Nu_k − U)} a(u)` (the
  multipliers of `g` times those of `J²`, Lemma C.theta(f)); (iii) antisymmetry in the `x`'s and in the `y`'s;
  (iv) transported: (C1) — `J²` vanishes to order exactly two along every coincidence divisor and `g` vanishes on the
  same-spin ones, so "the polar set of `g` lies in the up–down divisors, with poles of order `≤ 2`" is exactly "`a`
  vanishes to order `≥ 3` along the same-spin divisors"; (v) transported: (C2) (Lemma C.even with
  `S = J²/ϑ₁(x_a − y_k)²`, even in the pair's relative coordinate). The map `g ↦ J²g` is the identification; it is not
  formalized (no `g` exists in the Lean), and every statement of this block is about numerators.
* **Multipliers.** `ε = (ε₁, ε₂)` is a pair of complex numbers (`ℂ × ℂ`, the paper's `U(1)²` without the modulus
  condition): Lemma C.B(a) is then a statement about general multipliers. `μ_N²` is parametrized by
  `(j, k) ∈ Fin N × Fin N` through `rootPair N (j, k) = (e^{2πij/N}, e^{2πik/N})`, a bijection onto the pairs of `N`-th
  roots of unity (`rootPair_injective`, `exists_rootPair`); block F1-lower's `ε ∈ {±1}²` (the type `Eps`) enters through
  `Eps.pair ε = (ε₁, ε₂)`, among the `rootPair N (j, k)` exactly when `N` is even, apart from `(1,1)`
  (`exists_rootPair_eps`, `eps_pair_pow_iff_of_odd`).
* **`Θ_2[ε]`** for general `ε` is `Θ2g τ ε`, the paper's definition verbatim; for `ε ∈ μ_N²` it is
  `thetaSpace τ (−j/N) (k/N) 2` (`Θ2g_rootPair`), two-dimensional by Lemma C.theta(a); for `ε ∈ {±1}²` it is F1-lower's
  `Θ2 τ ε` (`Θ2g_pair`, by definition).
* **Lemma C.B(b)** in numerator form: the image of `Θ_2[ε] ⊗ 𝒢(n,m;ε)` is the span of the products `F(U) a(u)`
  (`imageTensor`); "well defined" is `imageTensor ≤ V`; "surjective" is `V ≤ ⨆_ε imageTensor`; "injective" is the
  independence statement `lemB_injective`; the dimension formula is stated as the inequality the count uses and as the
  paper's equality, both under the finite dimension of every `Gnum` (`Module.finrank` is `0` on an
  infinite-dimensional space).
* **The decomposition** (the proof of "surjective"): the projector route at the function level — `T_K²`, `T_1²` of
  `kz:eq:TK-T1` as linear maps on functions (`TK2`, `T12`), the projectors
  `P_{jk} = N⁻² Σ_{r,s<N} ω^{−jr−ks} (T_K²)^r (T_1²)^s` (`projJK`), and the devices that pin the route: finite order on
  the shape, `Σ_{jk} P_{jk} = 1`, the eigenvalues of `P_{jk} f`, `P_{jk}` preserving `V`, and an eigenfunction of `V`
  lying in the image (the paper's `2×2` system for the coefficients). No eigenspace theory of Mathlib is used.
* **The explicit numerators belong to `Gnum`.** F1-lower's `…_numerator_props` are stated for `F ∈ Θ_2[ε]`, and the
  constant `F = 1` is not in `Θ_2[ε]`; the membership of the numerator of `J²g` itself (`F = 1`) is therefore restated
  here (`…_numerator_one_exists`, `…_numerator_one_mem`), and the proof phase (round one) proved it through copies of
  F1-lower's devices: `…_numerator_factor_diff_dev` (F1-lower's `…_numerator_factor_dev` with `F ∈ Θ_2[ε]` weakened to
  `Differentiable ℂ F`), F1-lower's `C2_of_laurent_dev` (which takes `Differentiable ℂ F` already), and
  `vanishes3_core_gen_dev`, `C1_of_factor_gen_dev` (F1-lower's `vanishes3_core_dev`, `C1_of_factor_dev` with general
  nonvanishing multipliers, those of `Gnum`, in place of the shape's), assembled in `numerator_one_gnum_dev`.
-/

open Complex
open scoped Real UpperHalfPlane

noncomputable section

namespace HRTorus.ZeroModes

/-! ## The multipliers: `ε ∈ μ_N²` and `ε ∈ {±1}²` -/

/-- The pair `(ε₁, ε₂) ∈ {±1}²` of a sign pair of block F1-lower. -/
def Eps.pair (ε : Eps) : ℂ × ℂ := (ε.e1, ε.e2)

/-- The pair `(e^{2πij/N}, e^{2πik/N})` of `N`-th roots of unity — the parametrization of Lemma C.B's
"`$\varepsilon\in\mu_N^2$`" by `(j, k) ∈ Fin N × Fin N`. -/
def rootPair (N : ℕ) (jk : Fin N × Fin N) : ℂ × ℂ :=
  (cexp (2 * π * I * ((jk.1 : ℕ) : ℂ) / (N : ℂ)), cexp (2 * π * I * ((jk.2 : ℕ) : ℂ) / (N : ℂ)))

/-! ### Proof devices for the multipliers (proof phase, round one; not statements of the paper): the `N`-th roots of
unity `e^{2πij/N}`, `j < N`, from `Complex.exp_eq_one_iff` and the complex logarithm -/

theorem rootExp_pow_dev {N : ℕ} (hN : N ≠ 0) (j : ℕ) : cexp (2 * π * I * (j : ℂ) / (N : ℂ)) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [← Complex.exp_nat_mul]
  have e : (N : ℂ) * (2 * π * I * (j : ℂ) / (N : ℂ)) = (j : ℂ) * (2 * π * I) := by
    field_simp
  rw [e]
  exact Complex.exp_nat_mul_two_pi_mul_I j

theorem rootExp_inj_dev {N a b : ℕ} (ha : a < N) (hb : b < N)
    (h : cexp (2 * π * I * (a : ℂ) / (N : ℂ)) = cexp (2 * π * I * (b : ℂ) / (N : ℂ))) : a = b := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h1 : cexp (2 * π * I * (((a : ℂ) - b) / N)) = 1 := by
    rw [show 2 * π * I * (((a : ℂ) - b) / N) = 2 * π * I * a / N - 2 * π * I * b / N by ring, Complex.exp_sub, h,
      div_self (Complex.exp_ne_zero _)]
  obtain ⟨z, hz⟩ := Complex.exp_eq_one_iff.mp h1
  have h2 : ((a : ℂ) - b) / N = z := by
    apply mul_left_cancel₀ hpi
    rw [hz]
    ring
  rw [div_eq_iff hNc] at h2
  have h3 : (a : ℤ) - b = z * N := by exact_mod_cast h2
  have hz0 : z = 0 := by
    rcases lt_trichotomy z 0 with hz' | hz' | hz'
    · have : z ≤ -1 := by omega
      nlinarith
    · exact hz'
    · have : 1 ≤ z := by omega
      nlinarith
  subst hz0
  omega

theorem rootExp_surj_dev {N : ℕ} (hN : 0 < N) {x : ℂ} (hx : x ^ N = 1) :
    ∃ j : ℕ, j < N ∧ cexp (2 * π * I * (j : ℂ) / (N : ℂ)) = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hx
    exact zero_ne_one hx
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : cexp ((N : ℂ) * Complex.log x) = 1 := by
    rw [Complex.exp_nat_mul, Complex.exp_log hx0, hx]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
  have hlog : Complex.log x = 2 * π * I * k / N := by
    rw [eq_div_iff hNc]
    linear_combination hk
  have hj0 : 0 ≤ k % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  have hj1 : k % (N : ℤ) < N := Int.emod_lt_of_pos _ (by exact_mod_cast hN)
  refine ⟨(k % (N : ℤ)).toNat, by omega, ?_⟩
  have hcast : (((k % (N : ℤ)).toNat : ℕ) : ℂ) = ((k % (N : ℤ) : ℤ) : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg hj0
  have hk' : ((k % (N : ℤ) : ℤ) : ℂ) = (k : ℂ) - N * ((k / (N : ℤ) : ℤ) : ℂ) := by
    have := Int.emod_add_mul_ediv k N
    rw [eq_sub_iff_add_eq]
    exact_mod_cast this
  rw [hcast, hk', show 2 * π * I * ((k : ℂ) - N * ((k / (N : ℤ) : ℤ) : ℂ)) / N =
      2 * π * I * k / N - ((k / (N : ℤ) : ℤ) : ℂ) * (2 * π * I) by field_simp, Complex.exp_sub,
    Complex.exp_int_mul_two_pi_mul_I, div_one, ← hlog, Complex.exp_log hx0]

/-- `rootPair N (j, k) ∈ μ_N²`. -/
theorem rootPair_pow (N : ℕ) (jk : Fin N × Fin N) : (rootPair N jk).1 ^ N = 1 ∧ (rootPair N jk).2 ^ N = 1 := by
  have hN : N ≠ 0 := Nat.pos_iff_ne_zero.mp jk.1.pos
  exact ⟨rootExp_pow_dev hN _, rootExp_pow_dev hN _⟩

/-- The parametrization is injective: the sum over `Fin N × Fin N` is a sum over `μ_N²` without repetition. -/
theorem rootPair_injective (N : ℕ) : Function.Injective (rootPair N) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  simp only [rootPair, Prod.mk.injEq] at h
  rw [Prod.mk.injEq]
  exact ⟨Fin.ext (rootExp_inj_dev j.isLt j'.isLt h.1), Fin.ext (rootExp_inj_dev k.isLt k'.isLt h.2)⟩

/-- The parametrization is onto `μ_N²`. -/
theorem exists_rootPair {N : ℕ} (hN : 0 < N) {ε : ℂ × ℂ} (h : ε.1 ^ N = 1 ∧ ε.2 ^ N = 1) :
    ∃ jk : Fin N × Fin N, rootPair N jk = ε := by
  obtain ⟨i, hi, hie⟩ := rootExp_surj_dev hN h.1
  obtain ⟨j, hj, hje⟩ := rootExp_surj_dev hN h.2
  refine ⟨(⟨i, hi⟩, ⟨j, hj⟩), ?_⟩
  simp only [rootPair]
  rw [hie, hje]

/-- At even `N`, the four pairs of `{±1}²` are among `μ_N²` (Theorem C.T2(iii): "`Corollary~\ref{kz:cor:bounds}(c) and $\{\pm1\}^2\subset\mu_N^2$ give`"). -/
theorem exists_rootPair_eps {N : ℕ} (hN : 0 < N) (heven : Even N) (ε : Eps) :
    ∃ jk : Fin N × Fin N, rootPair N jk = ε.pair := by
  apply exists_rootPair hN
  cases ε <;> simp [Eps.pair, Eps.e1, Eps.e2, heven.neg_one_pow]

/-- At odd `N`, the only pair of `{±1}²` in `μ_N²` is `(1,1)`. -/
theorem eps_pair_pow_iff_of_odd {N : ℕ} (hodd : Odd N) (ε : Eps) :
    (ε.pair.1 ^ N = 1 ∧ ε.pair.2 ^ N = 1) ↔ ε = .pp := by
  have h1 : (-1 : ℂ) ≠ 1 := by norm_num
  cases ε <;> simp [Eps.pair, Eps.e1, Eps.e2, hodd.neg_one_pow, h1]

/-! ## `Θ_2[ε]` for general multipliers -/

/-- **Lemma C.B(b)**: "`For $\varepsilon\in\mu_N^2$ let $\kzTh_2[\varepsilon]$ be the space of entire $F$ with $F(U+1)=\varepsilon_1^{-1}F(U)$ and $F(U+\tau)=\varepsilon_2^{-1}e^{-4\pi iU-2\pi i\tau}F(U)$.`"
— for any pair `ε = (ε₁, ε₂)` (block F1-lower's `Θ2` is the case `ε ∈ {±1}²`, `Θ2g_pair`). -/
def Θ2g (τ : ℂ) (ε : ℂ × ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {F | Differentiable ℂ F ∧ (∀ U, F (U + 1) = ε.1⁻¹ * F U) ∧
      ∀ U, F (U + τ) = ε.2⁻¹ * cexp (-4 * π * I * U - 2 * π * I * τ) * F U}
  add_mem' := by
    rintro F G ⟨hF, hF1, hF2⟩ ⟨hG, hG1, hG2⟩
    refine ⟨hF.add hG, fun U => ?_, fun U => ?_⟩
    · simp only [Pi.add_apply, hF1, hG1]; ring
    · simp only [Pi.add_apply, hF2, hG2]; ring
  zero_mem' := ⟨differentiable_const 0, fun U => by simp, fun U => by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, hF1, hF2⟩
    refine ⟨hF.const_smul c, fun U => ?_, fun U => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hF1]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, hF2]; ring

/-- For `ε ∈ {±1}²`, `Θ_2[ε]` is block F1-lower's `Θ2 τ ε` (by definition). -/
theorem Θ2g_pair (τ : ℂ) (ε : Eps) : Θ2g τ ε.pair = Θ2 τ ε :=
  rfl

/-- **Lemma C.B(b)**: "`$\kzTh_2[\varepsilon]=\kzTh_2[a,b]$ with $e^{2\pi ia}=\varepsilon_1^{-1}$ and $e^{-2\pi ib}=\varepsilon_2^{-1}$`"
— for `ε = (e^{2πij/N}, e^{2πik/N})`: `a = −j/N`, `b = k/N`. -/
theorem Θ2g_rootPair (τ : ℂ) {N : ℕ} (jk : Fin N × Fin N) :
    Θ2g τ (rootPair N jk) = thetaSpace τ (-((jk.1 : ℕ) : ℝ) / N) (((jk.2 : ℕ) : ℝ) / N) 2 := by
  have e1 : (rootPair N jk).1⁻¹ = cexp (2 * π * I * ((-((jk.1 : ℕ) : ℝ) / N : ℝ) : ℂ)) := by
    simp only [rootPair]
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have e2 : ∀ U : ℂ, (rootPair N jk).2⁻¹ * cexp (-4 * π * I * U - 2 * π * I * τ) =
      cexp (-2 * π * I * (((((jk.2 : ℕ) : ℝ) / N : ℝ)) : ℂ)) * cexp (-π * I * ((2 : ℕ) : ℂ) * (2 * U + τ)) := by
    intro U
    simp only [rootPair]
    rw [← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  ext F
  constructor
  · rintro ⟨hd, h1, h2⟩
    exact ⟨hd, fun U => by rw [h1, e1], fun U => by rw [h2, e2]⟩
  · rintro ⟨hd, h1, h2⟩
    exact ⟨hd, fun U => by rw [h1, e1], fun U => by rw [h2, e2]⟩

/-- **Lemma C.B(b)**: "`It is two-dimensional`" (Lemma C.theta(a) at `ℓ = 2`, through `Θ2g_rootPair`). -/
theorem finrank_Θ2g_rootPair (τ : ℍ) {N : ℕ} (jk : Fin N × Fin N) :
    Module.finrank ℂ (Θ2g τ (rootPair N jk)) = 2 := by
  rw [Θ2g_rootPair]
  exact finrank_thetaSpace τ _ _ two_pos

/-! ## Definition C.G, in numerator form -/

/-- The conditions on a numerator `a = J²g` of `g ∈ 𝒢(n,m;ε)` (`N = n + m`, `U = Σ_i u_i`): the Osgood class; (i); (ii)
with the multipliers of `g` times those of `J²`; (iii); (iv) as (C1); (v) as (C2) — the docstring of `Gnum`. -/
def IsGnum (τ : ℍ) (n m : ℕ) (ε : ℂ × ℂ) (a : (Fin (n + m) → ℂ) → ℂ) : Prop :=
  IsOsgood a ∧
    (∀ (u : Fin (n + m) → ℂ) (c : ℂ), a (fun i => u i + c) = a u) ∧
    (∀ (u : Fin (n + m) → ℂ) (k : Fin (n + m)), a (Function.update u k (u k + 1)) = ε.1 * a u) ∧
    (∀ (u : Fin (n + m) → ℂ) (k : Fin (n + m)), a (Function.update u k (u k + τ)) =
      ε.2 * cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ - 4 * π * I * (((n + m : ℕ) : ℂ) * u k - ∑ i, u i)) *
        a u) ∧
    (∀ s t : Fin (n + m), s ≠ t → SameSpecies n s t → ∀ u, a (u ∘ Equiv.swap s t) = -a u) ∧
    C1 τ n m a ∧ C2 n m a

/-! ### Proof devices for `Gnum` (statement phase; not statements of the paper): closure under the linear operations -/

theorem Gnum_zero_mem_dev (τ : ℍ) (n m : ℕ) (ε : ℂ × ℂ) : IsGnum τ n m ε 0 := by
  refine ⟨isOsgood_zero_dev, fun u c => rfl, fun u k => by simp, fun u k => by simp, fun s t _ _ u => by simp,
    C1_zero_dev τ n m, C2_zero_dev n m⟩

theorem Gnum_add_mem_dev (τ : ℍ) (n m : ℕ) (ε : ℂ × ℂ) {a b : (Fin (n + m) → ℂ) → ℂ} (ha : IsGnum τ n m ε a)
    (hb : IsGnum τ n m ε b) : IsGnum τ n m ε (a + b) := by
  obtain ⟨hao, ha0, ha1, haτ, has, ha1', ha2'⟩ := ha
  obtain ⟨hbo, hb0, hb1, hbτ, hbs, hb1', hb2'⟩ := hb
  refine ⟨isOsgood_add_dev hao hbo, fun u c => ?_, fun u k => ?_, fun u k => ?_, fun s t hst hss u => ?_,
    C1_add_dev τ hao hbo ha1' hb1', C2_add_dev hao hbo ha2' hb2'⟩
  · simp only [Pi.add_apply, ha0 u c, hb0 u c]
  · simp only [Pi.add_apply, ha1 u k, hb1 u k]
    ring
  · simp only [Pi.add_apply, haτ u k, hbτ u k]
    ring
  · simp only [Pi.add_apply, has s t hst hss u, hbs s t hst hss u]
    ring

theorem Gnum_smul_mem_dev (τ : ℍ) (n m : ℕ) (ε : ℂ × ℂ) (c : ℂ) {a : (Fin (n + m) → ℂ) → ℂ}
    (ha : IsGnum τ n m ε a) : IsGnum τ n m ε (c • a) := by
  obtain ⟨hao, ha0, ha1, haτ, has, ha1', ha2'⟩ := ha
  refine ⟨isOsgood_smul_dev c hao, fun u c' => ?_, fun u k => ?_, fun u k => ?_, fun s t hst hss u => ?_,
    C1_smul_dev τ c ha1', C2_smul_dev c ha2'⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ha0 u c']
  · simp only [Pi.smul_apply, smul_eq_mul, ha1 u k]
    ring
  · simp only [Pi.smul_apply, smul_eq_mul, haτ u k]
    ring
  · simp only [Pi.smul_apply, smul_eq_mul, has s t hst hss u]
    ring

/-- **Definition C.G**, in numerator form: "`For $n,m\ge0$, $N=n+m$, and $\varepsilon=(\varepsilon_1,\varepsilon_2)\in U(1)^2$, let $\kzG(n,m;\varepsilon)$ be the space of meromorphic $g(x_1,\dots,x_n;y_1,\dots,y_m)$ on $\C^N$ such that`"
(i) "`$g(u+c\one)=g(u)$ for all $c\in\C$`"; (ii) "`$g(u+e_k)=\varepsilon_1g(u)$ and $g(u+\tau e_k)=\varepsilon_2g(u)$ for every $k$`";
(iii) "`$g$ is antisymmetric in the $x$'s and in the $y$'s`"; (iv) "`the polar set of $g$ lies in $\bigcup_{a,k}\{x_a-y_k\in\Lambda_u\}$, with poles of order $\le2$`";
(v) "`at fixed pair centre, the $v^{-1}$ coefficient of $g$ at $x_a=y_k$ vanishes`".
`Gnum τ n m ε` is the space of the numerators `a = J²g` (the stage-F specification's form; the proof of Lemma C.B
writes their multipliers as "`$a_\ell(u+\tau e_k)=\varepsilon_2e^{-4\pi i(Nu_k-U)-2\pi i(N-1)\tau}a_\ell(u)$`"): in the Osgood class, with
(i) for `a` (`J²` is invariant, Lemma C.theta(f)); (ii) for `a`, the multipliers of `g` times
"`$J^2(u+\tau e_k)=e^{-2\pi i(N-1)\tau-4\pi i(Nu_k-U)}J^2(u)$`"; (iii) for `a` (`J²` is symmetric); (iv) transported to
(C1): `J²` vanishes to order exactly two along every coincidence divisor (Lemma C.theta(c), (f)), and
"`$g$ is regular on same-spin coincidences and vanishes there, by (iii) and (iv)`", so (iv) for `g` is exactly the
vanishing of `a` to order `≥ 3` along the same-spin divisors; (v) transported to (C2) by Lemma C.even,
"`Then $[\kzD_{x_ay_k}\mathsf a]_{x_a=y_k}\equiv0$ iff $\mathcal B\equiv0$.`", with `S = J²/ϑ₁(x_a − y_k)²`, invariant
under `x_a ↔ y_k`. At `n = m = 0` the conditions are empty: "`$\kzG(0,0;\varepsilon):=\C$`" (`Gnum_zero_zero`). -/
def Gnum (τ : ℍ) (n m : ℕ) (ε : ℂ × ℂ) : Submodule ℂ ((Fin (n + m) → ℂ) → ℂ) where
  carrier := {a | IsGnum τ n m ε a}
  zero_mem' := Gnum_zero_mem_dev τ n m ε
  add_mem' := fun ha hb => Gnum_add_mem_dev τ n m ε ha hb
  smul_mem' := fun c _ ha => Gnum_smul_mem_dev τ n m ε c ha

/-- Membership in `Gnum` (by definition). -/
theorem mem_Gnum {τ : ℍ} {n m : ℕ} {ε : ℂ × ℂ} {a : (Fin (n + m) → ℂ) → ℂ} : a ∈ Gnum τ n m ε ↔ IsGnum τ n m ε a :=
  Iff.rfl

/-- **Definition C.G**: "`$\kzG(0,0;\varepsilon):=\C$`" — at `n = m = 0` every function of the one point `Fin 0 → ℂ` is a
numerator (the conditions are empty). -/
theorem Gnum_zero_zero (τ : ℍ) (ε : ℂ × ℂ) : Gnum τ 0 0 ε = ⊤ := by
  rw [eq_top_iff]
  intro a _
  have hsub : ∀ u v : Fin (0 + 0) → ℂ, u = v := fun u v => funext fun i => i.elim0
  exact ⟨⟨continuous_of_const fun u v => by rw [hsub u v], fun u i => i.elim0⟩,
    fun u c => by rw [hsub (fun i => u i + c) u], fun u k => k.elim0, fun u k => k.elim0,
    fun s t _ _ u => s.elim0, fun s t _ _ => s.elim0, fun s t _ _ u _ => s.elim0⟩

/-- **Definition C.G**: "`$\kzG(0,0;\varepsilon):=\C$`" — one-dimensional. -/
theorem finrank_Gnum_zero_zero (τ : ℍ) (ε : ℂ × ℂ) :
    FiniteDimensional ℂ (Gnum τ 0 0 ε) ∧ Module.finrank ℂ (Gnum τ 0 0 ε) = 1 := by
  have : IsEmpty (Fin (0 + 0)) := ⟨fun i => i.elim0⟩
  let : Unique (Fin (0 + 0) → ℂ) := Pi.uniqueOfIsEmpty _
  let e : ((Fin (0 + 0) → ℂ) → ℂ) ≃ₗ[ℂ] ℂ := LinearEquiv.funUnique (Fin (0 + 0) → ℂ) ℂ ℂ
  have : FiniteDimensional ℂ ((Fin (0 + 0) → ℂ) → ℂ) := LinearEquiv.finiteDimensional e.symm
  have hrank : Module.finrank ℂ ((Fin (0 + 0) → ℂ) → ℂ) = 1 := by
    rw [e.finrank_eq, Module.finrank_self]
  rw [Gnum_zero_zero]
  exact ⟨inferInstance, by rw [finrank_top, hrank]⟩

/-! ## Lemma C.B(a) -/

/-! ### Proof devices for Lemma C.B(a) (proof phase, round one; not statements of the paper)

Shifting every coordinate by `d`, one at a time, multiplies by the product of the one-step multipliers
(`shift_all_dev`, an induction over `Fin.cons` as in F1-lower's `interpN_dev`); `E(u) = exp((2πi/τ)(U² − N Σ u_i²))` is
a nonvanishing entire function with the `τ`-multipliers of `J²` (`expQ_update_dev`) and invariant under `u ↦ u + τ𝟙`
(`expQ_add_dev`), so `a/E` has the constant multiplier `ε₂` under each `u_k ↦ u_k + τ`. -/

theorem shift_all_dev (d : ℂ) (M : ℂ → ℂ) :
    ∀ (N : ℕ) (φ : (Fin N → ℂ) → ℂ),
      (∀ (u : Fin N → ℂ) (k : Fin N), φ (Function.update u k (u k + d)) = M (u k) * φ u) →
      ∀ u : Fin N → ℂ, φ (fun i => u i + d) = (∏ i, M (u i)) * φ u := by
  intro N
  induction N with
  | zero =>
    intro φ _ u
    rw [Fin.prod_univ_zero, one_mul]
    congr 1
    funext i
    exact i.elim0
  | succ N ih =>
    intro φ hφ u
    have h2 : ∀ (v : Fin N → ℂ) (k : Fin N),
        φ (Fin.cons (u 0 + d) (Function.update v k (v k + d))) = M (v k) * φ (Fin.cons (u 0 + d) v) := by
      intro v k
      have := hφ (Fin.cons (u 0 + d) v) k.succ
      simpa only [Fin.cons_update, Fin.cons_succ] using this
    have e1 : (fun i => u i + d) = (Fin.cons (u 0 + d) (fun i : Fin N => Fin.tail u i + d) : Fin (N + 1) → ℂ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Fin.tail]
    have e2 : (Fin.cons (u 0 + d) (Fin.tail u) : Fin (N + 1) → ℂ) = Function.update u 0 (u 0 + d) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Fin.tail]
    have hih := ih (fun v => φ (Fin.cons (u 0 + d) v)) h2 (Fin.tail u)
    beta_reduce at hih
    rw [e1, hih, e2, hφ u 0, Fin.prod_univ_succ]
    simp only [Fin.tail]
    ring

theorem sum_sq_update_dev {N : ℕ} (u : Fin N → ℂ) (k : Fin N) (x : ℂ) :
    ∑ j, Function.update u k x j ^ 2 = ∑ j, u j ^ 2 - u k ^ 2 + x ^ 2 := by
  have h : ∀ j, Function.update u k x j ^ 2 = u j ^ 2 + (if j = k then x ^ 2 - u k ^ 2 else 0) := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [hj]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The nonvanishing factor `E(u) = exp((2πi/τ)(U² − N Σ u_i²))`. -/
def expQ_dev (τ : ℂ) {N : ℕ} (u : Fin N → ℂ) : ℂ :=
  cexp (2 * π * I / τ * ((∑ i, u i) ^ 2 - (N : ℂ) * ∑ i, u i ^ 2))

theorem expQ_update_dev (τ : ℍ) {N : ℕ} (u : Fin N → ℂ) (k : Fin N) :
    expQ_dev τ (Function.update u k (u k + τ)) =
      cexp (-2 * π * I * ((N : ℂ) - 1) * τ - 4 * π * I * ((N : ℂ) * u k - ∑ i, u i)) * expQ_dev τ u := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  unfold expQ_dev
  rw [sum_update_add_dev, sum_sq_update_dev, ← Complex.exp_add]
  congr 1
  field_simp
  ring

theorem expQ_add_dev (τ : ℍ) {N : ℕ} (u : Fin N → ℂ) : expQ_dev τ (fun i => u i + τ) = expQ_dev τ u := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hs1 : ∑ i, (u i + (τ : ℂ)) = ∑ i, u i + N * τ := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs2 : ∑ i, (u i + (τ : ℂ)) ^ 2 = ∑ i, u i ^ 2 + 2 * τ * ∑ i, u i + N * τ ^ 2 := by
    have e : ∀ i, (u i + (τ : ℂ)) ^ 2 = u i ^ 2 + 2 * τ * u i + τ ^ 2 := fun i => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  unfold expQ_dev
  rw [hs1, hs2]
  congr 1
  field_simp
  ring

/-- **Lemma C.B(a)**: "`$\kzG(n,m;\varepsilon)=0$ unless $\varepsilon_1^N=\varepsilon_2^N=1$`" — for general multipliers
(the proof: "`By (i), $g(u+\one)=g(u)$. By (ii) applied to each of the $N$ coordinates, $g(u+\one)=\varepsilon_1^Ng(u)$`";
at `N = 0` the hypothesis is false). -/
theorem Gnum_eq_bot_of_not_root (τ : ℍ) (n m : ℕ) {ε : ℂ × ℂ}
    (h : ¬ (ε.1 ^ (n + m) = 1 ∧ ε.2 ^ (n + m) = 1)) : Gnum τ n m ε = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  obtain ⟨_, ha0, ha1, haτ, -, -, -⟩ := ha
  have hall1 : ∀ u, a (fun i => u i + 1) = ε.1 ^ (n + m) * a u := by
    intro u
    have := shift_all_dev 1 (fun _ => ε.1) (n + m) a (fun u k => ha1 u k) u
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this
  have hb : ∀ (u : Fin (n + m) → ℂ) (k : Fin (n + m)),
      (fun v => a v / expQ_dev τ v) (Function.update u k (u k + τ)) = ε.2 * (fun v => a v / expQ_dev τ v) u := by
    intro u k
    simp only
    rw [haτ, expQ_update_dev]
    have h0 : expQ_dev τ u ≠ 0 := Complex.exp_ne_zero _
    have h1 : cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ - 4 * π * I * (((n + m : ℕ) : ℂ) * u k - ∑ i, u i)) ≠ 0 :=
      Complex.exp_ne_zero _
    field_simp
  have hallτ : ∀ u, a (fun i => u i + τ) / expQ_dev τ (fun i => u i + τ) = ε.2 ^ (n + m) * (a u / expQ_dev τ u) := by
    intro u
    have := shift_all_dev (τ : ℂ) (fun _ => ε.2) (n + m) (fun v => a v / expQ_dev τ v) hb u
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this
  funext u
  by_cases h1 : ε.1 ^ (n + m) = 1
  · have h2 : ε.2 ^ (n + m) ≠ 1 := fun h2 => h ⟨h1, h2⟩
    have h3 := hallτ u
    rw [expQ_add_dev, ha0 u τ] at h3
    have hE : expQ_dev τ u ≠ 0 := Complex.exp_ne_zero _
    have h4 : (1 - ε.2 ^ (n + m)) * (a u / expQ_dev τ u) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd (by linear_combination -h5) h2
    · rw [div_eq_zero_iff] at h5
      exact h5.resolve_right hE
  · have h3 := hall1 u
    rw [ha0 u 1] at h3
    have h4 : (1 - ε.1 ^ (n + m)) * a u = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd (by linear_combination -h5) h1
    · exact h5

/-! ### Proof devices for the explicit numerators at `F = 1` (proof phase, round one; not statements of the paper)

F1-lower's `gOdd_numerator_factor_dev`, `gOddSwap_numerator_factor_dev`, `dEps_numerator_factor_dev`,
`f5_numerator_factor_dev` (`ZeroModes.Explicit`), copied with the hypothesis `F ∈ Θ_2[ε]` weakened to
`Differentiable ℂ F` (their proofs use only the differentiability), so that they apply at `F = 1`. -/

theorem gOdd_numerator_factor_diff_dev (τ : ℍ) (m : ℕ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    ∃ f R : (Fin ((m + 1) + m) → ℂ) → ℂ, IsNumerator τ (m + 1) m F (gOdd τ m) f ∧ Differentiable ℂ R ∧
      ∀ u, f u = Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 * Jfun τ (fun k => u (Fin.natAdd (m + 1) k)) ^ 2 * R u := by
  refine ⟨fun u => F (∑ i, u i) * Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 *
      Jfun τ (fun k => u (Fin.natAdd (m + 1) k)) ^ 2 * detGOdd_dev τ m u,
    fun u => F (∑ i, u i) * detGOdd_dev τ m u, ⟨isOsgood_of_differentiable_dev ?_, fun u hu => ?_⟩,
    (differentiable_F_sum_dev hF).mul (differentiable_detGOdd_dev τ m),
    fun u => by beta_reduce; ring⟩
  · exact (((differentiable_F_sum_dev hF).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul
      ((differentiable_Jfun_comp_dev τ _).pow 2)).mul (differentiable_detGOdd_dev τ m)
  · have hgen : ∀ a k, u (Fin.castAdd m a) - u (Fin.natAdd (m + 1) k) ∉ Λu τ := fun a k hmem => hu ⟨a, k, hmem⟩
    beta_reduce
    rw [stateFun_eq_dev, gOdd_eq_updateCol_dev τ m _ _ 0]
    congr 1
    unfold detGOdd_dev
    rw [← Matrix.det_mul_column]
    refine congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ => M.det) ?_
    ext a k
    simp only [Matrix.of_apply, Matrix.updateCol_apply]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · simp
    · have hk : (Fin.castSucc k' : Fin (m + 1)) ≠ Fin.last m := (Fin.castSucc_lt_last k').ne
      simp only [Fin.lastCases_castSucc, hk, ite_false, Fin.snoc_castSucc]
      exact regEntry_eq_dev τ .pp _ _ a k' (hgen a k')

theorem gOddSwap_numerator_factor_diff_dev (τ : ℍ) (m : ℕ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    ∃ f R : (Fin (m + (m + 1)) → ℂ) → ℂ, IsNumerator τ m (m + 1) F (gOddSwap τ m) f ∧ Differentiable ℂ R ∧
      ∀ u, f u = Jfun τ (fun a => u (Fin.castAdd (m + 1) a)) ^ 2 * Jfun τ (fun k => u (Fin.natAdd m k)) ^ 2 * R u := by
  refine ⟨fun u => F (∑ i, u i) * Jfun τ (fun a => u (Fin.castAdd (m + 1) a)) ^ 2 *
      Jfun τ (fun k => u (Fin.natAdd m k)) ^ 2 * detGOddSwap_dev τ m u,
    fun u => F (∑ i, u i) * detGOddSwap_dev τ m u, ⟨isOsgood_of_differentiable_dev ?_, fun u hu => ?_⟩,
    (differentiable_F_sum_dev hF).mul (differentiable_detGOddSwap_dev τ m),
    fun u => by beta_reduce; ring⟩
  · exact (((differentiable_F_sum_dev hF).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul
      ((differentiable_Jfun_comp_dev τ _).pow 2)).mul (differentiable_detGOddSwap_dev τ m)
  · have hgen : ∀ (a : Fin (m + 1)) (k : Fin m), u (Fin.natAdd m a) - u (Fin.castAdd (m + 1) k) ∉ Λu τ := by
      intro a k hmem
      refine hu ⟨k, a, ?_⟩
      have := neg_mem_Λu_dev τ hmem
      rwa [neg_sub] at this
    beta_reduce
    rw [stateFun_eq_dev, prod_rowTheta_swap_dev]
    unfold gOddSwap
    rw [gOdd_eq_updateCol_dev τ m _ _ 0]
    congr 1
    unfold detGOddSwap_dev
    rw [← Matrix.det_mul_column]
    refine congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ => M.det) ?_
    ext a k
    simp only [Matrix.of_apply, Matrix.updateCol_apply]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · simp
    · have hk : (Fin.castSucc k' : Fin (m + 1)) ≠ Fin.last m := (Fin.castSucc_lt_last k').ne
      simp only [Fin.lastCases_castSucc, hk, ite_false, Fin.snoc_castSucc]
      exact regEntry_eq_dev τ .pp _ _ a k' (hgen a k')

theorem dEps_numerator_factor_diff_dev (τ : ℍ) (ε : Eps) (p : ℕ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    ∃ f R : (Fin (p + p) → ℂ) → ℂ, IsNumerator τ p p F (dEps τ ε p) f ∧ Differentiable ℂ R ∧
      ∀ u, f u = Jfun τ (fun a => u (Fin.castAdd p a)) ^ 2 * Jfun τ (fun k => u (Fin.natAdd p k)) ^ 2 * R u := by
  refine ⟨fun u => F (∑ i, u i) * Jfun τ (fun a => u (Fin.castAdd p a)) ^ 2 *
      Jfun τ (fun k => u (Fin.natAdd p k)) ^ 2 * detDEps_dev τ ε p u,
    fun u => F (∑ i, u i) * detDEps_dev τ ε p u, ⟨isOsgood_of_differentiable_dev ?_, fun u hu => ?_⟩,
    (differentiable_F_sum_dev hF).mul (differentiable_detDEps_dev τ ε p),
    fun u => by beta_reduce; ring⟩
  · exact (((differentiable_F_sum_dev hF).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul
      ((differentiable_Jfun_comp_dev τ _).pow 2)).mul (differentiable_detDEps_dev τ ε p)
  · have hgen : ∀ a k, u (Fin.castAdd p a) - u (Fin.natAdd p k) ∉ Λu τ := fun a k hmem => hu ⟨a, k, hmem⟩
    beta_reduce
    rw [stateFun_eq_dev]
    congr 1
    unfold dEps detDEps_dev
    rw [← Matrix.det_mul_column]
    refine congrArg (fun M : Matrix (Fin p) (Fin p) ℂ => M.det) ?_
    ext a k
    simp only [Matrix.of_apply]
    exact regEntry_eq_dev τ ε _ _ a k (hgen a k)

theorem f5_numerator_factor_diff_dev (τ : ℍ) (q : ℕ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    ∃ f R : (Fin ((q + 1) + (q + 1)) → ℂ) → ℂ, IsNumerator τ (q + 1) (q + 1) F (f5 τ q) f ∧ Differentiable ℂ R ∧
      ∀ u, f u = Jfun τ (fun a => u (Fin.castAdd (q + 1) a)) ^ 2 *
        Jfun τ (fun k => u (Fin.natAdd (q + 1) k)) ^ 2 * R u := by
  refine ⟨fun u => F (∑ i, u i) * Jfun τ (fun a => u (Fin.castAdd (q + 1) a)) ^ 2 *
      Jfun τ (fun k => u (Fin.natAdd (q + 1) k)) ^ 2 * detF5_dev τ q u,
    fun u => F (∑ i, u i) * detF5_dev τ q u, ⟨isOsgood_of_differentiable_dev ?_, fun u hu => ?_⟩,
    (differentiable_F_sum_dev hF).mul (differentiable_detF5_dev τ q),
    fun u => by beta_reduce; ring⟩
  · exact (((differentiable_F_sum_dev hF).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul
      ((differentiable_Jfun_comp_dev τ _).pow 2)).mul (differentiable_detF5_dev τ q)
  · have hgen : ∀ a k, u (Fin.castAdd (q + 1) a) - u (Fin.natAdd (q + 1) k) ∉ Λu τ :=
      fun a k hmem => hu ⟨a, k, hmem⟩
    beta_reduce
    rw [stateFun_eq_dev, f5_eq_sum_dev]
    congr 1
    unfold detF5_dev
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Matrix.det_mul_column]
    congr 1
    ext a k
    simp only [Matrix.of_apply, Matrix.updateCol_apply]
    split_ifs with hk
    · ring
    · exact regEntry_eq_dev τ .pp _ _ a k (hgen a k)

/-! ### Proof devices for the explicit numerators at `F = 1`, continued (proof phase, round one; not statements of the
paper)

F1-lower's `vanishes3_core_dev` and `C1_of_factor_dev` (`ZeroModes.Explicit`), copied with the multipliers of
`Θ_L[0,0]` in a variable replaced by general nonvanishing ones (`vanishes3_core_gen_dev`, `C1_of_factor_gen_dev`), and
the analog of F1-lower's `shape_of_numerator_dev` for the numerator of `J²g` itself, which has the multipliers of `Gnum`
(`numerator_one_gnum_dev`). -/

theorem vanishes3_core_gen_dev (τ : ℍ) {N : ℕ} {f Q : (Fin N → ℂ) → ℂ} (hQ : IsOsgood Q) {s t : Fin N}
    (hst : s ≠ t) (hfQ : ∀ u, f u = theta1 (u s - u t) τ ^ 2 * Q u)
    (hanti : ∀ u, f (u ∘ Equiv.swap s t) = -f u) {μ₁ : ℂ} (hμ₁ : μ₁ ≠ 0) {μ₂ : (Fin N → ℂ) → ℂ → ℂ}
    (hμ₂ : ∀ u z, μ₂ u z ≠ 0) (hμ₂c : ∀ u, Continuous (μ₂ u))
    (hm1 : ∀ u z, f (Function.update u s (z + 1)) = μ₁ * f (Function.update u s z))
    (hmτ : ∀ u z, f (Function.update u s (z + τ)) = μ₂ u z * f (Function.update u s z)) :
    VanishesAlong τ f s t 3 := by
  have hQanti : ∀ u, Q (u ∘ Equiv.swap s t) = -Q u := by
    have h := eq_zero_of_offDiff_dev τ hst (φ := fun u => Q (u ∘ Equiv.swap s t) + Q u)
      ((hQ.1.comp (continuous_pi fun i => continuous_apply _)).add hQ.1) fun u hu => by
        have hθ : theta1 (u s - u t) τ ≠ 0 := fun h0 => hu ((theta1_eq_zero_iff τ _).1 h0)
        have h1 := hanti u
        rw [hfQ, hfQ] at h1
        simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at h1
        have e := theta1_sq_neg_dev (u s - u t) τ
        rw [neg_sub] at e
        rw [e] at h1
        have h2 : theta1 (u s - u t) τ ^ 2 * (Q (u ∘ Equiv.swap s t) + Q u) = 0 := by linear_combination h1
        exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero 2 hθ)
    intro u
    have := congrFun h u
    simp only [Pi.zero_apply] at this
    linear_combination this
  have hQdiag : ∀ u, u s = u t → Q u = 0 := by
    intro u hu
    have h := hQanti u
    rw [swap_fix_dev u hu] at h
    linear_combination h / 2
  intro u l hl j hj
  set C : ℂ → ℂ := fun z => Q (Function.update u s z) with hCdef
  have hCd : Differentiable ℂ C := hQ.2 u s
  have hft : ∀ z, f (Function.update u s z) = theta1 (z - u t) τ ^ 2 * C z := by
    intro z
    rw [hfQ, Function.update_self, Function.update_of_ne hst.symm]
  have hS : ((fun l' => u t + l') '' Λu τ).Countable := (Λu_countable_dev τ).image _
  have hθne : ∀ z, z ∉ (fun l' => u t + l') '' Λu τ → theta1 (z - u t) τ ≠ 0 := fun z hz h0 =>
    hz ⟨z - u t, (theta1_eq_zero_iff τ _).1 h0, by simp⟩
  have hC1 : ∀ z, C (z + 1) = μ₁ * C z := by
    have h := Continuous.ext_on (hS.dense_compl ℂ) (hCd.continuous.comp (by fun_prop : Continuous fun z : ℂ => z + 1))
      (continuous_const.mul hCd.continuous) fun z hz => by
        have h1 := hm1 u z
        rw [hft, hft, show z + 1 - u t = (z - u t) + 1 by ring, theta1_add_one, neg_sq] at h1
        have h2 : theta1 (z - u t) τ ^ 2 * C (z + 1) = theta1 (z - u t) τ ^ 2 * (μ₁ * C z) := by
          linear_combination h1
        exact mul_left_cancel₀ (pow_ne_zero 2 (hθne z hz)) h2
    exact fun z => congrFun h z
  have hCτ : ∀ z, cexp (-2 * π * I * τ - 4 * π * I * (z - u t)) * C (z + τ) = μ₂ u z * C z := by
    have h := Continuous.ext_on (hS.dense_compl ℂ)
      ((by fun_prop : Continuous fun z : ℂ => cexp (-2 * π * I * τ - 4 * π * I * (z - u t))).mul
        (hCd.continuous.comp (by fun_prop : Continuous fun z : ℂ => z + (τ : ℂ))))
      ((hμ₂c u).mul hCd.continuous)
      fun z hz => by
        have h1 := hmτ u z
        rw [hft, hft, show z + (τ : ℂ) - u t = (z - u t) + τ by ring, theta1_add_tau] at h1
        have e2 : cexp (-π * I * τ - 2 * π * I * (z - u t)) ^ 2 =
            cexp (-2 * π * I * τ - 4 * π * I * (z - u t)) := by
          rw [← Complex.exp_nat_mul]
          congr 1
          push_cast
          ring
        have h2 : theta1 (z - u t) τ ^ 2 * (cexp (-2 * π * I * τ - 4 * π * I * (z - u t)) * C (z + τ)) =
            theta1 (z - u t) τ ^ 2 * (μ₂ u z * C z) := by
          linear_combination h1 - (theta1 (z - u t) τ ^ 2 * C (z + τ)) * e2
        exact mul_left_cancel₀ (pow_ne_zero 2 (hθne z hz)) h2
    exact fun z => congrFun h z
  have hZ1 : ∀ z, C z = 0 ↔ C (z + 1) = 0 := fun z => by
    rw [hC1]
    exact ⟨fun h0 => by rw [h0, mul_zero], fun h0 => (mul_eq_zero.1 h0).resolve_left hμ₁⟩
  have hZτ : ∀ z, C z = 0 ↔ C (z + τ) = 0 := fun z => by
    constructor
    · intro h0
      have h1 := hCτ z
      rw [h0, mul_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_left (Complex.exp_ne_zero _)
    · intro h0
      have h1 := hCτ z
      rw [h0, mul_zero] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left (hμ₂ u z)
  have h0 : C (u t) = 0 := hQdiag _ (by rw [Function.update_self, Function.update_of_ne hst.symm])
  have hq : ∀ q : ℤ, C (u t + q * τ) = 0 := by
    intro q
    induction q with
    | zero => simpa using h0
    | succ i ih =>
      have h1 := (hZτ _).1 ih
      convert h1 using 2
      push_cast
      ring
    | pred i ih =>
      refine (hZτ _).2 ?_
      convert ih using 2
      push_cast
      ring
  have hpq : ∀ p q : ℤ, C (u t + (p + q * τ)) = 0 := by
    intro p q
    induction p with
    | zero => simpa using hq q
    | succ i ih =>
      have h1 := (hZ1 _).1 ih
      convert h1 using 2
      push_cast
      ring
    | pred i ih =>
      refine (hZ1 _).2 ?_
      convert ih using 2
      push_cast
      ring
  obtain ⟨p, q, rfl⟩ := hl
  have hfun : (fun z => f (Function.update u s z)) = fun z => theta1 (z - u t) τ * theta1 (z - u t) τ * C z := by
    funext z
    rw [hft]
    ring
  have hθd : Differentiable ℂ fun z => theta1 (z - u t) τ :=
    (theta1_differentiable τ).comp (differentiable_id.sub_const _)
  have hθ0 : theta1 (u t + (p + q * τ) - u t) τ = 0 :=
    (theta1_eq_zero_iff τ _).2 ⟨p, q, by ring⟩
  rw [hfun]
  exact iteratedDeriv_mul3_dev hθd hθd hCd hθ0 hθ0 (hpq p q) j hj

theorem C1_of_factor_gen_dev (τ : ℍ) {n m : ℕ} {f R : (Fin (n + m) → ℂ) → ℂ}
    (hanti : ∀ s t : Fin (n + m), s ≠ t → SameSpecies n s t → ∀ u, f (u ∘ Equiv.swap s t) = -f u)
    {μ₁ : ℂ} (hμ₁ : μ₁ ≠ 0) {μ₂ : Fin (n + m) → (Fin (n + m) → ℂ) → ℂ → ℂ}
    (hμ₂ : ∀ i u z, μ₂ i u z ≠ 0) (hμ₂c : ∀ i u, Continuous (μ₂ i u))
    (hm1 : ∀ i u z, f (Function.update u i (z + 1)) = μ₁ * f (Function.update u i z))
    (hmτ : ∀ i u z, f (Function.update u i (z + τ)) = μ₂ i u z * f (Function.update u i z))
    (hR : IsOsgood R)
    (hfac : ∀ u, f u = Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 * Jfun τ (fun k => u (Fin.natAdd n k)) ^ 2 * R u) :
    C1 τ n m f := by
  intro s t hst hss
  have hne : s ≠ t := ne_of_lt hst
  have hJy : IsOsgood fun u : Fin (n + m) → ℂ => Jfun τ (fun k => u (Fin.natAdd n k)) ^ 2 :=
    isOsgood_of_differentiable_dev ((differentiable_Jfun_comp_dev τ _).pow 2)
  have hJx : IsOsgood fun u : Fin (n + m) → ℂ => Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 :=
    isOsgood_of_differentiable_dev ((differentiable_Jfun_comp_dev τ _).pow 2)
  induction s using Fin.addCases with
  | left a =>
    induction t using Fin.addCases with
    | left b =>
      have hab : a ≠ b := fun h => hne (by rw [h])
      obtain ⟨K, hK, hJ⟩ := Jfun_sq_factor τ hab
      refine vanishes3_core_gen_dev τ (Q := fun u => K (fun a => u (Fin.castAdd m a)) *
          Jfun τ (fun k => u (Fin.natAdd n k)) ^ 2 * R u)
        (isOsgood_mul_dev (isOsgood_mul_dev (isOsgood_comp_castAdd_dev hK) hJy) hR) hne (fun u => ?_)
        (hanti _ _ hne hss) hμ₁ (hμ₂ _) (hμ₂c _) (hm1 _) (hmτ _)
      rw [hfac, hJ (fun a => u (Fin.castAdd m a))]
      ring
    | right l =>
      have hss' : ((Fin.castAdd m a : Fin (n + m)) : ℕ) < n ↔ ((Fin.natAdd n l : Fin (n + m)) : ℕ) < n := hss
      simp only [Fin.val_castAdd, Fin.val_natAdd, a.isLt, true_iff] at hss'
      omega
  | right k =>
    induction t using Fin.addCases with
    | left b =>
      have hss' : ((Fin.natAdd n k : Fin (n + m)) : ℕ) < n ↔ ((Fin.castAdd m b : Fin (n + m)) : ℕ) < n := hss
      simp only [Fin.val_castAdd, Fin.val_natAdd, b.isLt, iff_true] at hss'
      omega
    | right l =>
      have hkl : k ≠ l := fun h => hne (by rw [h])
      obtain ⟨K, hK, hJ⟩ := Jfun_sq_factor τ hkl
      refine vanishes3_core_gen_dev τ (Q := fun u => Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 *
          K (fun k => u (Fin.natAdd n k)) * R u)
        (isOsgood_mul_dev (isOsgood_mul_dev hJx (isOsgood_comp_natAdd_dev hK)) hR) hne (fun u => ?_)
        (hanti _ _ hne hss) hμ₁ (hμ₂ _) (hμ₂c _) (hm1 _) (hmτ _)
      rw [hfac, hJ (fun k => u (Fin.natAdd n k))]
      ring

/-- The numerator of `J²g` (`F = 1`) for a `g` with the properties (i)–(iii) of Definition C.G and the factorization
`J(x)² J(y)² R`, with (C2), is in `Gnum`. -/
theorem numerator_one_gnum_dev (τ : ℍ) {n m : ℕ} (ε : ℂ × ℂ) (hε1 : ε.1 ≠ 0) (hε2 : ε.2 ≠ 0)
    (g : (Fin n → ℂ) → (Fin m → ℂ) → ℂ)
    (htr : ∀ x y c, g (fun i => x i + c) (fun j => y j + c) = g x y)
    (hx1 : ∀ x y a, g (Function.update x a (x a + 1)) y = ε.1 * g x y)
    (hxτ : ∀ x y a, g (Function.update x a (x a + τ)) y = ε.2 * g x y)
    (hy1 : ∀ x y k, g x (Function.update y k (y k + 1)) = ε.1 * g x y)
    (hyτ : ∀ x y k, g x (Function.update y k (y k + τ)) = ε.2 * g x y)
    (hxs : ∀ x y a b, a ≠ b → g (x ∘ Equiv.swap a b) y = -g x y)
    (hys : ∀ x y k l, k ≠ l → g x (y ∘ Equiv.swap k l) = -g x y)
    {f R : (Fin (n + m) → ℂ) → ℂ} (hf : IsNumerator τ n m (fun _ => 1) g f) (hR : Differentiable ℂ R)
    (hfac : ∀ u, f u = Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 * Jfun τ (fun k => u (Fin.natAdd n k)) ^ 2 * R u)
    (hC2 : C2 n m f) : f ∈ Gnum τ n m ε := by
  have hg1 : ∀ (v : Fin (n + m) → ℂ) (i : Fin (n + m)),
      g (fun a => Function.update v i (v i + 1) (Fin.castAdd m a))
        (fun k => Function.update v i (v i + 1) (Fin.natAdd n k)) =
        ε.1 * g (fun a => v (Fin.castAdd m a)) (fun k => v (Fin.natAdd n k)) := by
    intro v i
    induction i using Fin.addCases with
    | left a =>
      rw [castAdd_update_dev, natAdd_update_castAdd_dev]
      exact hx1 _ _ _
    | right k =>
      rw [castAdd_update_natAdd_dev, natAdd_update_dev]
      exact hy1 _ _ _
  have hgτ : ∀ (v : Fin (n + m) → ℂ) (i : Fin (n + m)),
      g (fun a => Function.update v i (v i + τ) (Fin.castAdd m a))
        (fun k => Function.update v i (v i + τ) (Fin.natAdd n k)) =
        ε.2 * g (fun a => v (Fin.castAdd m a)) (fun k => v (Fin.natAdd n k)) := by
    intro v i
    induction i using Fin.addCases with
    | left a =>
      rw [castAdd_update_dev, natAdd_update_castAdd_dev]
      exact hxτ _ _ _
    | right k =>
      rw [castAdd_update_natAdd_dev, natAdd_update_dev]
      exact hyτ _ _ _
  -- the identities off the polar set, then everywhere
  have hP1 : ∀ (i : Fin (n + m)) (v : Fin (n + m) → ℂ), f (Function.update v i (v i + 1)) = ε.1 * f v := by
    intro i
    have h := eq_zero_of_offPolar_dev τ (φ := fun v => f (Function.update v i (v i + 1)) - ε.1 * f v)
      ((hf.1.1.comp (continuous_update_add_dev i 1)).sub (continuous_const.mul hf.1.1)) fun v hv => by
        rw [hf.2 _ (update_not_mem_polar_dev τ v i (one_mem_Λu_dev τ) hv), hf.2 v hv]
        unfold stateFun
        rw [Jfun_sq_add_one, hg1]
        ring
    intro v
    have := congrFun h v
    simp only [Pi.zero_apply] at this
    linear_combination this
  have hPτ : ∀ (i : Fin (n + m)) (v : Fin (n + m) → ℂ), f (Function.update v i (v i + τ)) =
      ε.2 * cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ - 4 * π * I * (((n + m : ℕ) : ℂ) * v i - ∑ j, v j)) *
        f v := by
    intro i
    have h := eq_zero_of_offPolar_dev τ (φ := fun v => f (Function.update v i (v i + τ)) -
        ε.2 * cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ - 4 * π * I * (((n + m : ℕ) : ℂ) * v i - ∑ j, v j)) *
          f v)
      ((hf.1.1.comp (continuous_update_add_dev i τ)).sub ((continuous_const.mul (by fun_prop :
        Continuous fun v : Fin (n + m) → ℂ => cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ -
          4 * π * I * (((n + m : ℕ) : ℂ) * v i - ∑ j, v j)))).mul hf.1.1)) fun v hv => by
        rw [hf.2 _ (update_not_mem_polar_dev τ v i (tau_mem_Λu_dev τ) hv), hf.2 v hv]
        unfold stateFun
        rw [Jfun_sq_add_tau, hgτ]
        ring
    intro v
    have := congrFun h v
    simp only [Pi.zero_apply] at this
    linear_combination this
  have hPtr : ∀ (v : Fin (n + m) → ℂ) (c : ℂ), f (fun i => v i + c) = f v := by
    intro v c
    have h := eq_zero_of_offPolar_dev τ (φ := fun v => f (fun i => v i + c) - f v)
      ((hf.1.1.comp (continuous_id.add continuous_const)).sub hf.1.1) fun v hv => by
        have hv' : (fun i => v i + c) ∉ polarSet τ n m := by
          rintro ⟨a, k, hmem⟩
          refine hv ⟨a, k, ?_⟩
          simpa using hmem
        rw [hf.2 _ hv', hf.2 v hv]
        unfold stateFun
        rw [Jfun_sq_add_const]
        have := htr (fun a => v (Fin.castAdd m a)) (fun k => v (Fin.natAdd n k)) c
        simp only at this ⊢
        rw [this]
        ring
    have := congrFun h v
    simp only [Pi.zero_apply] at this
    linear_combination this
  have hanti : ∀ s t : Fin (n + m), s ≠ t → SameSpecies n s t → ∀ v, f (v ∘ Equiv.swap s t) = -f v := by
    intro s t hst hss
    have hsw : ∀ v : Fin (n + m) → ℂ,
        g (fun a => v (Equiv.swap s t (Fin.castAdd m a))) (fun k => v (Equiv.swap s t (Fin.natAdd n k))) =
          -g (fun a => v (Fin.castAdd m a)) (fun k => v (Fin.natAdd n k)) ∧
        (v ∉ polarSet τ n m → v ∘ Equiv.swap s t ∉ polarSet τ n m) := by
      intro v
      induction s using Fin.addCases with
      | left a =>
        induction t using Fin.addCases with
        | left b =>
          have hab : a ≠ b := fun h => hst (by rw [h])
          have hx : (fun a' => v (Equiv.swap (Fin.castAdd m a) (Fin.castAdd m b) (Fin.castAdd m a'))) =
              (fun a' => v (Fin.castAdd m a')) ∘ Equiv.swap a b := by
            funext a'
            rw [Function.comp_apply, (Fin.castAdd_injective n m).swap_apply]
          have hy : (fun k => v (Equiv.swap (Fin.castAdd m a) (Fin.castAdd m b) (Fin.natAdd n k))) =
              fun k => v (Fin.natAdd n k) := by
            funext k
            rw [Equiv.swap_apply_of_ne_of_ne (castAdd_ne_natAdd_dev _ _).symm (castAdd_ne_natAdd_dev _ _).symm]
          refine ⟨by rw [hx, hy, hxs _ _ _ _ hab], fun hv ⟨a', k, hmem⟩ => hv ⟨Equiv.swap a b a', k, ?_⟩⟩
          simp only [Function.comp_apply] at hmem
          rwa [(Fin.castAdd_injective n m).swap_apply,
            Equiv.swap_apply_of_ne_of_ne (castAdd_ne_natAdd_dev _ _).symm (castAdd_ne_natAdd_dev _ _).symm] at hmem
        | right l =>
          have hss' : ((Fin.castAdd m a : Fin (n + m)) : ℕ) < n ↔ ((Fin.natAdd n l : Fin (n + m)) : ℕ) < n := hss
          simp only [Fin.val_castAdd, Fin.val_natAdd, a.isLt, true_iff] at hss'
          omega
      | right k =>
        induction t using Fin.addCases with
        | left b =>
          have hss' : ((Fin.natAdd n k : Fin (n + m)) : ℕ) < n ↔ ((Fin.castAdd m b : Fin (n + m)) : ℕ) < n := hss
          simp only [Fin.val_castAdd, Fin.val_natAdd, b.isLt, iff_true] at hss'
          omega
        | right l =>
          have hkl : k ≠ l := fun h => hst (by rw [h])
          have hx : (fun a => v (Equiv.swap (Fin.natAdd n k) (Fin.natAdd n l) (Fin.castAdd m a))) =
              fun a => v (Fin.castAdd m a) := by
            funext a
            rw [Equiv.swap_apply_of_ne_of_ne (castAdd_ne_natAdd_dev _ _) (castAdd_ne_natAdd_dev _ _)]
          have hy : (fun k' => v (Equiv.swap (Fin.natAdd n k) (Fin.natAdd n l) (Fin.natAdd n k'))) =
              (fun k' => v (Fin.natAdd n k')) ∘ Equiv.swap k l := by
            funext k'
            rw [Function.comp_apply, (Fin.natAdd_injective m n).swap_apply]
          refine ⟨by rw [hx, hy, hys _ _ _ _ hkl], fun hv ⟨a, k', hmem⟩ => hv ⟨a, Equiv.swap k l k', ?_⟩⟩
          simp only [Function.comp_apply] at hmem
          rwa [(Fin.natAdd_injective m n).swap_apply,
            Equiv.swap_apply_of_ne_of_ne (castAdd_ne_natAdd_dev _ _) (castAdd_ne_natAdd_dev _ _)] at hmem
    have h := eq_zero_of_offPolar_dev τ (φ := fun v => f (v ∘ Equiv.swap s t) + f v)
      ((hf.1.1.comp (continuous_pi fun i => continuous_apply _)).add hf.1.1) fun v hv => by
        rw [hf.2 _ ((hsw v).2 hv), hf.2 v hv]
        unfold stateFun
        simp only [Function.comp_apply]
        rw [(hsw v).1, Jfun_sq_perm]
        ring
    intro v
    have := congrFun h v
    simp only [Pi.zero_apply] at this
    linear_combination this
  -- (C1) from the factorization, with the multipliers of `Gnum` in each variable
  have hC1 : C1 τ n m f := by
    refine C1_of_factor_gen_dev τ hanti hε1 (μ₂ := fun i u z => ε.2 * cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ -
        4 * π * I * (((n + m : ℕ) : ℂ) * z - ∑ j, Function.update u i z j)))
      (fun i u z => mul_ne_zero hε2 (Complex.exp_ne_zero _)) (fun i u => by fun_prop) (fun i u z => ?_)
      (fun i u z => ?_) (isOsgood_of_differentiable_dev hR) hfac
    · have h := hP1 i (Function.update u i z)
      rwa [Function.update_self, Function.update_idem] at h
    · have h := hPτ i (Function.update u i z)
      rwa [Function.update_self, Function.update_idem] at h
  exact ⟨hf.1, hPtr, fun u k => hP1 k u, fun u k => hPτ k u, hanti, hC1, hC2⟩

/-! ## The explicit numerators belong to `Gnum` (Proposition C.explicit, membership, at `F = 1`) -/

/-- **Proposition C.explicit(a)**: the numerator of `J² g_{2m+1}` exists ("`By (iv) and Lemma~\ref{kz:lem:theta}(f), $J^2g$ has no poles along any divisor, so it is holomorphic.`"). -/
theorem gOdd_numerator_one_exists (τ : ℍ) (m : ℕ) : ∃ f, IsNumerator τ (m + 1) m (fun _ => 1) (gOdd τ m) f := by
  obtain ⟨f, -, hf, -⟩ := gOdd_numerator_factor_diff_dev τ m (differentiable_const (1 : ℂ))
  exact ⟨f, hf⟩

/-- **Proposition C.explicit(a)**: "`It lies in $\kzG(m+1,m;(1,1))$`" — in numerator form. -/
theorem gOdd_numerator_one_mem (τ : ℍ) (m : ℕ) {f : (Fin ((m + 1) + m) → ℂ) → ℂ}
    (hf : IsNumerator τ (m + 1) m (fun _ => 1) (gOdd τ m) f) : f ∈ Gnum τ (m + 1) m (1, 1) := by
  have hG := gOdd_G τ m
  obtain ⟨f₀, R, hf₀, hR, hfac⟩ := gOdd_numerator_factor_diff_dev τ m (differentiable_const (1 : ℂ))
  have heq := numerator_unique_dev τ hf hf₀
  have hfd : Differentiable ℂ f := by
    rw [heq, funext hfac]
    exact (((differentiable_Jfun_comp_dev τ _).pow 2).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul hR
  have hC2 := C2_of_laurent_dev τ (differentiable_const (1 : ℂ)) hf hfd (wp_sub_inv_sq_analyticAt τ)
    fun a k x y hxy hgen => gOdd_laurent_dev τ m a k x y hxy hgen
  exact numerator_one_gnum_dev τ (1, 1) one_ne_zero one_ne_zero (gOdd τ m) hG.1
    (fun x y a => by rw [(hG.2.1 x y a).1]; simp) (fun x y a => by rw [(hG.2.1 x y a).2]; simp)
    (fun x y k => by rw [(hG.2.2.1 x y k).1]; simp) (fun x y k => by rw [(hG.2.2.1 x y k).2]; simp)
    hG.2.2.2.1 hG.2.2.2.2 hf hR (fun u => by rw [heq]; exact hfac u) hC2

/-- **Theorem C.T2(ii)**, `S_z = −½` ("`$S_z=-\tfrac12$ is the same with the species exchanged.`"): the numerator of
`J² g_{2m+1}(y; x)` exists. -/
theorem gOddSwap_numerator_one_exists (τ : ℍ) (m : ℕ) :
    ∃ f, IsNumerator τ m (m + 1) (fun _ => 1) (gOddSwap τ m) f := by
  obtain ⟨f, -, hf, -⟩ := gOddSwap_numerator_factor_diff_dev τ m (differentiable_const (1 : ℂ))
  exact ⟨f, hf⟩

/-- **Theorem C.T2(ii)**, `S_z = −½`: the numerator lies in `𝒢(m, m+1; (1,1))`. -/
theorem gOddSwap_numerator_one_mem (τ : ℍ) (m : ℕ) {f : (Fin (m + (m + 1)) → ℂ) → ℂ}
    (hf : IsNumerator τ m (m + 1) (fun _ => 1) (gOddSwap τ m) f) : f ∈ Gnum τ m (m + 1) (1, 1) := by
  have hG := gOdd_G τ m
  obtain ⟨f₀, R, hf₀, hR, hfac⟩ := gOddSwap_numerator_factor_diff_dev τ m (differentiable_const (1 : ℂ))
  have heq := numerator_unique_dev τ hf hf₀
  have hfd : Differentiable ℂ f := by
    rw [heq, funext hfac]
    exact (((differentiable_Jfun_comp_dev τ _).pow 2).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul hR
  have hC2 := C2_of_laurent_dev τ (differentiable_const (1 : ℂ)) hf hfd (wp_sub_inv_sq_analyticAt τ)
    fun a k x y hxy hgen => gOddSwap_laurent_dev τ m a k x y hxy hgen
  exact numerator_one_gnum_dev τ (1, 1) one_ne_zero one_ne_zero (gOddSwap τ m)
    (fun x y c => by unfold gOddSwap; exact hG.1 y x c)
    (fun x y a => by unfold gOddSwap; rw [(hG.2.2.1 y x a).1]; simp)
    (fun x y a => by unfold gOddSwap; rw [(hG.2.2.1 y x a).2]; simp)
    (fun x y k => by unfold gOddSwap; rw [(hG.2.1 y x k).1]; simp)
    (fun x y k => by unfold gOddSwap; rw [(hG.2.1 y x k).2]; simp)
    (fun x y a b hab => by unfold gOddSwap; exact hG.2.2.2.2 y x a b hab)
    (fun x y k l hkl => by unfold gOddSwap; exact hG.2.2.2.1 y x k l hkl) hf hR (fun u => by rw [heq]; exact hfac u)
    hC2

/-- **Proposition C.explicit(b)**: the numerator of `J² d^{(p)}_ε` exists. -/
theorem dEps_numerator_one_exists (τ : ℍ) (ε : Eps) (p : ℕ) :
    ∃ f, IsNumerator τ p p (fun _ => 1) (dEps τ ε p) f := by
  obtain ⟨f, -, hf, -⟩ := dEps_numerator_factor_diff_dev τ ε p (differentiable_const (1 : ℂ))
  exact ⟨f, hf⟩

/-- **Proposition C.explicit(b)**: "`$d^{(p)}_\varepsilon:=\det[\wp_\varepsilon(x_i-y_j)]_{p\times p}$ lies in $\kzG(p,p;\varepsilon)$`"
— in numerator form. -/
theorem dEps_numerator_one_mem (τ : ℍ) (ε : Eps) (p : ℕ) {f : (Fin (p + p) → ℂ) → ℂ}
    (hf : IsNumerator τ p p (fun _ => 1) (dEps τ ε p) f) : f ∈ Gnum τ p p ε.pair := by
  have hG := dEps_G τ ε p
  obtain ⟨f₀, R, hf₀, hR, hfac⟩ := dEps_numerator_factor_diff_dev τ ε p (differentiable_const (1 : ℂ))
  have heq := numerator_unique_dev τ hf hf₀
  have hfd : Differentiable ℂ f := by
    rw [heq, funext hfac]
    exact (((differentiable_Jfun_comp_dev τ _).pow 2).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul hR
  have hL : ∀ (a k : Fin p) (x y : Fin p → ℂ), x a = y k → (∀ a' k', (a' ≠ a ∨ k' ≠ k) → x a' - y k' ∉ Λu τ) →
      ∃ c : ℂ, ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ ∀ v,
        dEps τ ε p (Function.update x a (x a + v / 2)) (Function.update y k (y k - v / 2)) = c * wpE τ ε v + H v := by
    intro a k x y hxy hgen
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := a.isLt; omega⟩
    exact dEps_laurent_dev τ ε q a k x y hxy hgen
  have hC2 := C2_of_laurent_dev τ (differentiable_const (1 : ℂ)) hf hfd (wpE_sub_inv_sq_analyticAt τ ε) hL
  exact numerator_one_gnum_dev τ ε.pair (Eps_e1_ne_zero_dev ε) (Eps_e2_ne_zero_dev ε) (dEps τ ε p) hG.1 hG.2.1
    hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2.1 hG.2.2.2.2.2.2 hf hR (fun u => by rw [heq]; exact hfac u) hC2

/-- **Proposition C.explicit(c)**: the numerator of `J² f_5^{(p)}` exists (`p = q + 1`). -/
theorem f5_numerator_one_exists (τ : ℍ) (q : ℕ) :
    ∃ f, IsNumerator τ (q + 1) (q + 1) (fun _ => 1) (f5 τ q) f := by
  obtain ⟨f, -, hf, -⟩ := f5_numerator_factor_diff_dev τ q (differentiable_const (1 : ℂ))
  exact ⟨f, hf⟩

/-- **Proposition C.explicit(c)**: "`lies in $\kzG(p,p;(1,1))$`" — in numerator form. -/
theorem f5_numerator_one_mem (τ : ℍ) (q : ℕ) {f : (Fin ((q + 1) + (q + 1)) → ℂ) → ℂ}
    (hf : IsNumerator τ (q + 1) (q + 1) (fun _ => 1) (f5 τ q) f) : f ∈ Gnum τ (q + 1) (q + 1) (1, 1) := by
  have hG := f5_G τ q
  obtain ⟨f₀, R, hf₀, hR, hfac⟩ := f5_numerator_factor_diff_dev τ q (differentiable_const (1 : ℂ))
  have heq := numerator_unique_dev τ hf hf₀
  have hfd : Differentiable ℂ f := by
    rw [heq, funext hfac]
    exact (((differentiable_Jfun_comp_dev τ _).pow 2).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul hR
  have hC2 := C2_of_laurent_dev τ (differentiable_const (1 : ℂ)) hf hfd (wp_sub_inv_sq_analyticAt τ)
    fun a k x y hxy hgen => f5_laurent_dev τ q a k x y hxy hgen
  exact numerator_one_gnum_dev τ (1, 1) one_ne_zero one_ne_zero (f5 τ q) hG.1
    (fun x y a => by rw [(hG.2.1 x y a).1]; simp) (fun x y a => by rw [(hG.2.1 x y a).2]; simp)
    (fun x y k => by rw [(hG.2.2.1 x y k).1]; simp) (fun x y k => by rw [(hG.2.2.1 x y k).2]; simp)
    hG.2.2.2.1 hG.2.2.2.2 hf hR (fun u => by rw [heq]; exact hfac u) hC2

/-! ## Lemma C.B(b): the factorization -/

/-- The image of `Θ_2[ε] ⊗ 𝒢(n,m;ε)` under "`F\otimes g\mapsto F(U)\,J^2(u)\,g(u),`", in numerator form: the span of the
products `F(U) a(u)`, `F ∈ Θ_2[ε]`, `a ∈ Gnum τ n m ε` (`U = Σ_i u_i`). -/
def imageTensor (τ : ℍ) (n m : ℕ) (ε : ℂ × ℂ) : Submodule ℂ ((Fin (n + m) → ℂ) → ℂ) :=
  Submodule.span ℂ {f | ∃ F ∈ Θ2g τ ε, ∃ a ∈ Gnum τ n m ε, f = fun u => F (∑ i, u i) * a u}

/-! ### Proof devices for Lemma C.B(b), "well defined" (proof phase, round one; not statements of the paper): a product
`F(U) a(u)` with `F ∈ Θ_2[ε]`, `a ∈ Gnum τ n m ε` (nonzero multipliers) lies in `V` at level `2N` — the multipliers
cancel (`ε₁⁻¹·ε₁`, and `ε₂⁻¹ e^{−4πiU−2πiτ}·ε₂ e^{−2πi(N−1)τ−4πi(Nu_k−U)} = e^{−iπ·2N(2u_k+τ)}`), the factor `F(U)` does
not change a slice's vanishing order (`vanish3_mul_dev`), and `D_{st}` annihilates it -/

theorem sum_update_dev {N : ℕ} (u : Fin N → ℂ) (i : Fin N) (z : ℂ) :
    ∑ j, Function.update u i z j = ∑ j, u j - u i + z := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase _ u (Finset.mem_univ i)]
  ring

theorem mul_mult_dev {e x y A B C : ℂ} (he : e ≠ 0) (h : A * B = C) : e⁻¹ * A * x * (e * B * y) = C * (x * y) := by
  rw [← h]
  have : e⁻¹ * e = 1 := inv_mul_cancel₀ he
  linear_combination (A * B * x * y) * this

theorem prod_mem_V_dev (τ : ℍ) {n m : ℕ} {ε : ℂ × ℂ} (hε1 : ε.1 ≠ 0) (hε2 : ε.2 ≠ 0) {F : ℂ → ℂ}
    (hF : F ∈ Θ2g τ ε) {a : (Fin (n + m) → ℂ) → ℂ} (ha : a ∈ Gnum τ n m ε) :
    (fun u => F (∑ i, u i) * a u) ∈ V τ (2 * (n + m)) n m := by
  obtain ⟨hFd, hF1, hFτ⟩ := hF
  obtain ⟨hao, _, ha1, haτ, has, ha1', ha2'⟩ := ha
  have hs1 : ∀ (u : Fin (n + m) → ℂ) i z, a (Function.update u i (z + 1)) = ε.1 * a (Function.update u i z) := by
    intro u i z
    have h := ha1 (Function.update u i z) i
    rwa [Function.update_self, Function.update_idem] at h
  have hsτ : ∀ (u : Fin (n + m) → ℂ) i z, a (Function.update u i (z + τ)) =
      ε.2 * cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ -
        4 * π * I * (((n + m : ℕ) : ℂ) * z - (∑ j, u j - u i + z))) * a (Function.update u i z) := by
    intro u i z
    have h := haτ (Function.update u i z) i
    rwa [Function.update_self, Function.update_idem, sum_update_dev] at h
  have hM : ∀ (u : Fin (n + m) → ℂ) (i : Fin (n + m)), Differentiable ℂ fun z => F (∑ j, u j - u i + z) :=
    fun u i => hFd.comp ((differentiable_const _).add differentiable_id)
  have e : ∀ (u : Fin (n + m) → ℂ) (i : Fin (n + m)),
      (fun z => (fun u => F (∑ i, u i) * a u) (Function.update u i z)) =
        fun z => F (∑ j, u j - u i + z) * a (Function.update u i z) := fun u i => by
    funext z
    simp only [sum_update_dev]
  refine ⟨⟨isOsgood_mul_dev (isOsgood_of_differentiable_dev (differentiable_F_sum_dev hFd)) hao,
    fun u i => ?_, fun s t hst hss u => ?_⟩, fun s t hst hss u l hl j hj => ?_, fun s t hs ht u hu => ?_⟩
  · rw [e u i]
    refine ⟨(hM u i).mul (hao.2 u i), fun z => ?_, fun z => ?_⟩
    · beta_reduce
      rw [show ∑ j, u j - u i + (z + 1) = (∑ j, u j - u i + z) + 1 by ring, hF1, hs1]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
      have : ε.1⁻¹ * ε.1 = 1 := inv_mul_cancel₀ hε1
      linear_combination (F (∑ j, u j - u i + z) * a (Function.update u i z)) * this
    · beta_reduce
      rw [show ∑ j, u j - u i + (z + τ) = (∑ j, u j - u i + z) + τ by ring, hFτ, hsτ]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
      refine mul_mult_dev hε2 ?_
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
  · show F (∑ i, (u ∘ Equiv.swap s t) i) * a (u ∘ Equiv.swap s t) = -(F (∑ i, u i) * a u)
    rw [has s t hst hss u]
    simp only [Function.comp_apply]
    rw [Equiv.sum_comp]
    ring
  · rw [e u s]
    exact vanish3_mul_dev (hM u s) (hao.2 u s) (fun j' hj' => ha1' s t hst hss u l hl j' hj') j hj
  · unfold relDeriv
    rw [e u s, e u t, deriv_fun_mul ((hM u s) _) ((hao.2 u s) _), deriv_fun_mul ((hM u t) _) ((hao.2 u t) _)]
    have hd : ∀ i : Fin (n + m), deriv (fun z => F (∑ j, u j - u i + z)) (u i) = deriv F (∑ j, u j) := by
      intro i
      have h := ((hFd (∑ j, u j - u i + u i)).hasDerivAt).comp_const_add (∑ j, u j - u i) (u i)
      rw [h.deriv, show ∑ j, u j - u i + u i = ∑ j, u j by ring]
    have h2 := ha2' s t hs ht u hu
    unfold relDeriv at h2
    rw [hd s, hd t, show ∑ j, u j - u s + u s = ∑ j, u j by ring, show ∑ j, u j - u t + u t = ∑ j, u j by ring,
      Function.update_eq_self, Function.update_eq_self]
    linear_combination F (∑ j, u j) * h2

/-- **Lemma C.B(b)**, "the map is well defined": "`Let $F\in\kzTh_2[\varepsilon]$, $g\in\kzG(n,m;\varepsilon)$ and $f:=FJ^2g$.`"
"`Boundary conditions: under $u_k\mapsto u_k+1$ the factors give $\varepsilon_1^{-1}\cdot1\cdot\varepsilon_1=1$`" — the image
lies in `V_{n,m}` at level `L = 2N`. -/
theorem imageTensor_le_V (τ : ℍ) (n m : ℕ) (jk : Fin (n + m) × Fin (n + m)) :
    imageTensor τ n m (rootPair (n + m) jk) ≤ V τ (2 * (n + m)) n m := by
  unfold imageTensor
  rw [Submodule.span_le]
  rintro f ⟨F, hF, a, ha, rfl⟩
  exact prod_mem_V_dev τ (Complex.exp_ne_zero _) (Complex.exp_ne_zero _) hF ha

/-! ## The many-body translations `T_K²`, `T_1²` and Lemma C.B(c) -/

/-- `kz:eq:TK-T1`: "`T_K^2F(u)=F(u+\one/N),\qquad T_1^2F(u)=e^{4\pi iU+2\pi i\tau}F(u+\tau\one/N),`" — `T_K²` on functions
of `N` variables. -/
def TK2 (N : ℕ) : Module.End ℂ ((Fin N → ℂ) → ℂ) where
  toFun f := fun u => f (fun i => u i + 1 / (N : ℂ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `kz:eq:TK-T1`: `T_1²F(u) = e^{4πiU + 2πiτ} F(u + τ𝟙/N)`. -/
def T12 (τ : ℂ) (N : ℕ) : Module.End ℂ ((Fin N → ℂ) → ℂ) where
  toFun f := fun u => cexp (4 * π * I * (∑ i, u i) + 2 * π * I * τ) * f (fun i => u i + τ / (N : ℂ))
  map_add' f g := by
    funext u
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- **Lemma C.B(c)**: "`On the image of $\kzTh_2[\varepsilon]\otimes\kzG(n,m;\varepsilon)$, $(T_K^2,T_1^2)=(\varepsilon_1^{-1},\varepsilon_2^{-1})$`". -/
theorem lemB_c (τ : ℍ) {n m : ℕ} (hN : 0 < n + m) (ε : ℂ × ℂ) {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : f ∈ imageTensor τ n m ε) : TK2 (n + m) f = ε.1⁻¹ • f ∧ T12 τ (n + m) f = ε.2⁻¹ • f := by
  have hNc : ((n + m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : ∀ (u : Fin (n + m) → ℂ) (c : ℂ), ∑ i, (u i + c) = ∑ i, u i + ((n + m : ℕ) : ℂ) * c := by
    intro u c
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hgen : ∀ F ∈ Θ2g τ ε, ∀ a ∈ Gnum τ n m ε,
      TK2 (n + m) (fun u => F (∑ i, u i) * a u) = ε.1⁻¹ • (fun u => F (∑ i, u i) * a u) ∧
        T12 τ (n + m) (fun u => F (∑ i, u i) * a u) = ε.2⁻¹ • (fun u => F (∑ i, u i) * a u) := by
    intro F hF a ha
    obtain ⟨_, hF1, hFτ⟩ := hF
    have ha0 := ha.2.1
    constructor
    · funext u
      show F (∑ i, (u i + 1 / ((n + m : ℕ) : ℂ))) * a (fun i => u i + 1 / ((n + m : ℕ) : ℂ)) =
        ε.1⁻¹ * (F (∑ i, u i) * a u)
      rw [hs, ha0, mul_one_div_cancel hNc, hF1]
      ring
    · funext u
      show cexp (4 * π * I * (∑ i, u i) + 2 * π * I * τ) *
          (F (∑ i, (u i + (τ : ℂ) / ((n + m : ℕ) : ℂ))) * a (fun i => u i + (τ : ℂ) / ((n + m : ℕ) : ℂ))) =
        ε.2⁻¹ * (F (∑ i, u i) * a u)
      rw [hs, ha0, show ((n + m : ℕ) : ℂ) * ((τ : ℂ) / ((n + m : ℕ) : ℂ)) = τ by field_simp, hFτ]
      have he : cexp (4 * π * I * (∑ i, u i) + 2 * π * I * τ) * cexp (-4 * π * I * (∑ i, u i) - 2 * π * I * τ) = 1 := by
        rw [← Complex.exp_add, show 4 * π * I * (∑ i, u i) + 2 * π * I * τ + (-4 * π * I * (∑ i, u i) - 2 * π * I * τ) =
          (0 : ℂ) by ring, Complex.exp_zero]
      linear_combination (ε.2⁻¹ * F (∑ i, u i) * a u) * he
  have hsub : imageTensor τ n m ε ≤
      LinearMap.ker (TK2 (n + m) - ε.1⁻¹ • 1) ⊓ LinearMap.ker (T12 τ (n + m) - ε.2⁻¹ • 1) := by
    unfold imageTensor
    rw [Submodule.span_le]
    rintro f ⟨F, hF, a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := hgen F hF a ha
    simp only [SetLike.mem_coe, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, h1, h2, sub_self, and_self]
  have := hsub hf
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] at this
  exact this

/-! ### Proof devices for Lemma C.B(b), the surjective half (statement phase; not statements of the paper): the
projector route at the function level

`P_{jk} := N⁻² Σ_{r,s<N} ω^{−(jr+ks)} (T_K²)^r (T_1²)^s`, `ω = e^{2πi/N}`. On a function of the shape at level `2N`,
`(T_K²)^N` and `(T_1²)^N` are the identity (from the multipliers), the two operators commute (on all functions,
`e^{4πi} = 1`), so `Σ_{jk} P_{jk} f = f` and `P_{jk} f` is a joint eigenfunction with eigenvalues `(ω^j, ω^k)`;
`P_{jk}` preserves `V` (translations by `c𝟙` and a factor depending on `U` only, which `D_{st}` annihilates and which
does not change a slice's vanishing order); a joint eigenfunction in `V` lies in the image for
`ε = (ω^{−j}, ω^{−k})` (the coefficients `a_ℓ` from the `2×2` system, jointly differentiable by
`differentiable_of_isCanonShape_dev`, and the conditions passed to them slice by slice, with `c` a parameter of the slice). -/

/-- The projector `P_{jk}` onto the joint eigenspace of `(T_K², T_1²)` with eigenvalues `(e^{2πij/N}, e^{2πik/N})`. -/
def projJK (τ : ℂ) (N : ℕ) (jk : Fin N × Fin N) : Module.End ℂ ((Fin N → ℂ) → ℂ) :=
  ((N : ℂ)⁻¹ ^ 2) • ∑ r : Fin N, ∑ s : Fin N,
    cexp (-(2 * π * I * ((((jk.1 : ℕ) * (r : ℕ) + (jk.2 : ℕ) * (s : ℕ) : ℕ) : ℂ)) / (N : ℂ))) •
      (TK2 N ^ (r : ℕ) * T12 τ N ^ (s : ℕ))

/-! ### Proof devices for the projectors (proof phase, round one; not statements of the paper)

`P_{jk} = N⁻² Q_j(T_K²) Q_k(T_1²)` with `Q_j(A) := Σ_{r<N} e^{−2πijr/N} A^r` (`Qop_dev`, `projJK_eq_Qop_dev`); the
character sums `Σ_{j<N} e^{−2πijr/N} = N δ_{r0}` (`char_sum_dev`) give `Σ_j Q_j(A) = N` (`sum_Qop_dev`); on a vector with
`A^N v = v`, `A Q_j(A) v = e^{2πij/N} Q_j(A) v` (`Qop_eigen_dev`, the sum reindexed cyclically, `cyclic_sum_dev`); `Q_j(A)`
commutes with what commutes with `A` (`Qop_comm_dev`); the powers of `T_K²`, `T_1²` in closed form
(`TK2_pow_apply_dev`, `T12_pow_apply_dev`). -/

def Qop_dev {M : Type*} [AddCommGroup M] [Module ℂ M] (N j : ℕ) (A : Module.End ℂ M) : Module.End ℂ M :=
  ∑ r : Fin N, cexp (-(2 * π * I * ((j * (r : ℕ) : ℕ) : ℂ) / (N : ℂ))) • A ^ (r : ℕ)

theorem projJK_eq_Qop_dev (τ : ℂ) (N : ℕ) (jk : Fin N × Fin N) :
    projJK τ N jk = ((N : ℂ)⁻¹ ^ 2) • (Qop_dev N jk.1 (TK2 N) * Qop_dev N jk.2 (T12 τ N)) := by
  unfold projJK Qop_dev
  congr 1
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [smul_mul_smul_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem char_sum_dev {N : ℕ} (hN : 0 < N) {r : ℕ} (hr : r < N) :
    ∑ j : Fin N, cexp (-(2 * π * I * (((j : ℕ) * r : ℕ) : ℂ) / (N : ℂ))) = if r = 0 then (N : ℂ) else 0 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpow : ∀ j : ℕ, cexp (-(2 * π * I * ((j * r : ℕ) : ℂ) / (N : ℂ))) =
      cexp (-(2 * π * I * (r : ℂ) / (N : ℂ))) ^ j := by
    intro j
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Fin.sum_univ_eq_sum_range (fun j => cexp (-(2 * π * I * ((j * r : ℕ) : ℂ) / (N : ℂ)))) N]
  simp only [hpow]
  split_ifs with h0
  · subst h0
    simp
  · have hζN : cexp (-(2 * π * I * (r : ℂ) / (N : ℂ))) ^ N = 1 := by
      rw [← Complex.exp_nat_mul, show (N : ℂ) * -(2 * π * I * (r : ℂ) / (N : ℂ)) = -((r : ℂ) * (2 * π * I)) by
        field_simp, Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I, inv_one]
    have hζ1 : cexp (-(2 * π * I * (r : ℂ) / (N : ℂ))) ≠ 1 := by
      intro h
      have h' : cexp (2 * π * I * (r : ℂ) / (N : ℂ)) = cexp (2 * π * I * ((0 : ℕ) : ℂ) / (N : ℂ)) := by
        have e : cexp (2 * π * I * (r : ℂ) / (N : ℂ)) = (cexp (-(2 * π * I * (r : ℂ) / (N : ℂ))))⁻¹ := by
          rw [← Complex.exp_neg, neg_neg]
        rw [e, h, inv_one]
        simp
      exact h0 (rootExp_inj_dev hr hN h')
    rw [geom_sum_eq hζ1, hζN, sub_self, zero_div]

theorem sum_Qop_dev {M : Type*} [AddCommGroup M] [Module ℂ M] {N : ℕ} (hN : 0 < N) (A : Module.End ℂ M) :
    ∑ j : Fin N, Qop_dev N j A = (N : ℂ) • 1 := by
  unfold Qop_dev
  rw [Finset.sum_comm, Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
  · rw [← Finset.sum_smul, char_sum_dev hN hN]
    simp
  · intro r _ hr
    have hr' : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
    rw [← Finset.sum_smul, char_sum_dev hN r.isLt]
    simp [hr']
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem cyclic_sum_dev {M : Type*} [AddCommGroup M] (N : ℕ) (h : ℕ → M) (hper : h N = h 0) :
    ∑ r ∈ Finset.range N, h (r + 1) = ∑ r ∈ Finset.range N, h r := by
  have := Finset.sum_range_succ' h N
  rw [Finset.sum_range_succ, hper] at this
  exact (add_right_cancel this).symm

theorem Qop_eigen_dev {M : Type*} [AddCommGroup M] [Module ℂ M] {N : ℕ} (hN : 0 < N) (j : ℕ)
    (A : Module.End ℂ M) {v : M} (hv : (A ^ N) v = v) :
    A (Qop_dev N j A v) = cexp (2 * π * I * (j : ℂ) / (N : ℂ)) • Qop_dev N j A v := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hQ : Qop_dev N j A v = ∑ r ∈ Finset.range N,
      cexp (-(2 * π * I * ((j * r : ℕ) : ℂ) / (N : ℂ))) • (A ^ r) v := by
    unfold Qop_dev
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    exact Fin.sum_univ_eq_sum_range (fun r => cexp (-(2 * π * I * ((j * r : ℕ) : ℂ) / (N : ℂ))) • (A ^ r) v) N
  have hstep : ∀ r : ℕ, A (cexp (-(2 * π * I * ((j * r : ℕ) : ℂ) / (N : ℂ))) • (A ^ r) v) =
      cexp (2 * π * I * (j : ℂ) / (N : ℂ)) •
        (cexp (-(2 * π * I * ((j * (r + 1) : ℕ) : ℂ) / (N : ℂ))) • (A ^ (r + 1)) v) := by
    intro r
    rw [map_smul, ← Module.End.mul_apply, ← pow_succ', smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hper : cexp (-(2 * π * I * ((j * N : ℕ) : ℂ) / (N : ℂ))) • (A ^ N) v =
      cexp (-(2 * π * I * ((j * 0 : ℕ) : ℂ) / (N : ℂ))) • (A ^ 0) v := by
    rw [hv, pow_zero, Module.End.one_apply]
    congr 1
    rw [show -(2 * π * I * ((j * N : ℕ) : ℂ) / (N : ℂ)) = -((j : ℂ) * (2 * π * I)) by push_cast; field_simp,
      Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I]
    simp
  rw [hQ, map_sum]
  simp only [hstep]
  rw [← Finset.smul_sum,
    cyclic_sum_dev N (fun r => cexp (-(2 * π * I * ((j * r : ℕ) : ℂ) / (N : ℂ))) • (A ^ r) v) hper]

theorem Qop_comm_dev {M : Type*} [AddCommGroup M] [Module ℂ M] (N j : ℕ) {A B : Module.End ℂ M}
    (hAB : A * B = B * A) : B * Qop_dev N j A = Qop_dev N j A * B := by
  unfold Qop_dev
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ((Commute.pow_left (show Commute A B from hAB) (r : ℕ))).eq]

theorem TK2_pow_apply_dev (N k : ℕ) (f : (Fin N → ℂ) → ℂ) :
    (TK2 N ^ k) f = fun u => f (fun i => u i + (k : ℂ) / (N : ℂ)) := by
  induction k generalizing f with
  | zero =>
    funext u
    simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    funext u
    show f (fun i => (u i + (k : ℂ) / (N : ℂ)) + 1 / (N : ℂ)) = f (fun i => u i + ((k + 1 : ℕ) : ℂ) / (N : ℂ))
    congr 1
    funext i
    push_cast
    ring

theorem T12_pow_apply_dev (τ : ℂ) {N : ℕ} (hN : (N : ℂ) ≠ 0) (k : ℕ) (f : (Fin N → ℂ) → ℂ) :
    (T12 τ N ^ k) f = fun u => cexp (4 * π * I * (k : ℂ) * (∑ i, u i) + 2 * π * I * τ * (k : ℂ) ^ 2) *
      f (fun i => u i + (k : ℂ) * τ / (N : ℂ)) := by
  induction k generalizing f with
  | zero =>
    funext u
    simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    funext u
    show cexp (4 * π * I * (k : ℂ) * (∑ i, u i) + 2 * π * I * τ * (k : ℂ) ^ 2) *
        (cexp (4 * π * I * (∑ i, (u i + (k : ℂ) * τ / (N : ℂ))) + 2 * π * I * τ) *
          f (fun i => (u i + (k : ℂ) * τ / (N : ℂ)) + τ / (N : ℂ))) = _
    have hs : ∑ i, (u i + (k : ℂ) * τ / (N : ℂ)) = ∑ i, u i + k * τ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [hs, ← mul_assoc, ← Complex.exp_add]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      funext i
      push_cast
      field_simp
      ring

theorem TK2_T12_comm_dev (τ : ℂ) (N : ℕ) : TK2 N * T12 τ N = T12 τ N * TK2 N := by
  apply LinearMap.ext
  intro f
  funext u
  show cexp (4 * π * I * (∑ i, (u i + 1 / (N : ℂ))) + 2 * π * I * τ) *
      f (fun i => (u i + 1 / (N : ℂ)) + τ / (N : ℂ)) =
    cexp (4 * π * I * (∑ i, u i) + 2 * π * I * τ) * f (fun i => (u i + τ / (N : ℂ)) + 1 / (N : ℂ))
  have hf : (fun i => (u i + 1 / (N : ℂ)) + τ / (N : ℂ)) = (fun i => (u i + τ / (N : ℂ)) + 1 / (N : ℂ)) := by
    funext i
    ring
  rw [hf]
  congr 1
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div_cancel hNc, show 4 * π * I * (∑ i, u i + 1) + 2 * π * I * τ =
        (4 * π * I * (∑ i, u i) + 2 * π * I * τ) + ((2 : ℕ) : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem TK2_pow_dev (τ : ℍ) {n m : ℕ} (hN : 0 < n + m) {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : IsCanonShape τ (2 * (n + m)) n m f) : (TK2 (n + m) ^ (n + m)) f = f := by
  have hNc : ((n + m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : ∀ (u : Fin (n + m) → ℂ) (k : Fin (n + m)),
      f (Function.update u k (u k + 1)) = (fun _ => (1 : ℂ)) (u k) * f u := by
    intro u k
    have := (hf.2.1 u k).2.1 (u k)
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, Function.update_eq_self] at this
    simpa using this
  rw [TK2_pow_apply_dev]
  funext u
  rw [show (fun i => u i + ((n + m : ℕ) : ℂ) / ((n + m : ℕ) : ℂ)) = fun i => u i + 1 by
    funext i
    rw [div_self hNc], shift_all_dev 1 (fun _ => 1) (n + m) f h1 u]
  simp

theorem T12_pow_dev (τ : ℍ) {n m : ℕ} (hN : 0 < n + m) {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : IsCanonShape τ (2 * (n + m)) n m f) : (T12 τ (n + m) ^ (n + m)) f = f := by
  have hNc : ((n + m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hτs : ∀ (u : Fin (n + m) → ℂ) (k : Fin (n + m)), f (Function.update u k (u k + τ)) =
      (fun z => cexp (-π * I * ((2 * (n + m) : ℕ) : ℂ) * (2 * z + τ))) (u k) * f u := by
    intro u k
    have := (hf.2.1 u k).2.2 (u k)
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, Function.update_eq_self] at this
    exact this
  rw [T12_pow_apply_dev (τ : ℂ) hNc]
  funext u
  rw [show (fun i => u i + ((n + m : ℕ) : ℂ) * τ / ((n + m : ℕ) : ℂ)) = fun i => u i + τ by
    funext i
    field_simp, shift_all_dev (τ : ℂ) (fun z => cexp (-π * I * ((2 * (n + m) : ℕ) : ℂ) * (2 * z + τ))) (n + m) f hτs u,
    ← Complex.exp_sum, ← mul_assoc, ← Complex.exp_add]
  have hsum : ∑ i, -π * I * ((2 * (n + m) : ℕ) : ℂ) * (2 * u i + τ) =
      -π * I * ((2 * (n + m) : ℕ) : ℂ) * (2 * ∑ i, u i + ((n + m : ℕ) : ℂ) * τ) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hsum, show 4 * π * I * ((n + m : ℕ) : ℂ) * (∑ i, u i) + 2 * π * I * τ * ((n + m : ℕ) : ℂ) ^ 2 +
      -π * I * ((2 * (n + m) : ℕ) : ℂ) * (2 * ∑ i, u i + ((n + m : ℕ) : ℂ) * τ) = 0 by push_cast; ring,
    Complex.exp_zero, one_mul]

theorem sum_projJK_dev (τ : ℂ) {N : ℕ} (hN : 0 < N) {f : (Fin N → ℂ) → ℂ} :
    ∑ jk : Fin N × Fin N, projJK τ N jk f = f := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [projJK_eq_Qop_dev]
  rw [← LinearMap.sum_apply, ← Finset.smul_sum, Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum, sum_Qop_dev hN, sum_Qop_dev hN, smul_mul_smul_comm, mul_one, smul_smul,
    LinearMap.smul_apply, Module.End.one_apply, show (N : ℂ)⁻¹ ^ 2 * ((N : ℂ) * (N : ℂ)) = 1 by field_simp, one_smul]

theorem TK2_projJK_dev (τ : ℂ) {N : ℕ} (hN : 0 < N) {f : (Fin N → ℂ) → ℂ} (h1 : (TK2 N ^ N) f = f)
    (jk : Fin N × Fin N) :
    TK2 N (projJK τ N jk f) = (rootPair N jk).1 • projJK τ N jk f := by
  have hcomm : Commute (TK2 N) (T12 τ N) := TK2_T12_comm_dev τ N
  have hc : TK2 N ^ N * Qop_dev N jk.2 (T12 τ N) = Qop_dev N jk.2 (T12 τ N) * TK2 N ^ N :=
    Qop_comm_dev N jk.2 (A := T12 τ N) (B := TK2 N ^ N) (hcomm.pow_left N).symm.eq
  have hv : (TK2 N ^ N) (Qop_dev N jk.2 (T12 τ N) f) = Qop_dev N jk.2 (T12 τ N) f := by
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply, h1]
  rw [projJK_eq_Qop_dev]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul]
  rw [Qop_eigen_dev hN jk.1 (TK2 N) hv, smul_comm]
  rfl

theorem T12_projJK_dev (τ : ℂ) {N : ℕ} (hN : 0 < N) {f : (Fin N → ℂ) → ℂ} (h2 : (T12 τ N ^ N) f = f)
    (jk : Fin N × Fin N) :
    T12 τ N (projJK τ N jk f) = (rootPair N jk).2 • projJK τ N jk f := by
  have hc : T12 τ N * Qop_dev N jk.1 (TK2 N) = Qop_dev N jk.1 (TK2 N) * T12 τ N :=
    Qop_comm_dev N jk.1 (A := TK2 N) (B := T12 τ N) (TK2_T12_comm_dev τ N)
  rw [projJK_eq_Qop_dev]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul]
  rw [← Module.End.mul_apply (T12 τ N), hc, Module.End.mul_apply, Qop_eigen_dev hN jk.2 (T12 τ N) h2, map_smul,
    smul_comm]
  rfl

/-! ### Proof devices for `P_{jk}` preserving `V` (proof phase, round one; not statements of the paper): the
translations `u ↦ u + c𝟙` times a factor `G(U)` with compensating multipliers preserve `V` (`transl_mem_V_dev`), so
`T_K²` (`G = 1`, `c = 1/N`) and `T_1²` (`G = e^{4πiU+2πiτ}`, `c = τ/N`) do, hence their powers and `Q_j` -/

theorem update_add_dev {N : ℕ} (u : Fin N → ℂ) (i : Fin N) (z c : ℂ) :
    (fun j => Function.update u i z j + c) = Function.update (fun j => u j + c) i (z + c) := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem transl_mem_V_dev (τ : ℍ) {L n m : ℕ} {f : (Fin (n + m) → ℂ) → ℂ} (hf : f ∈ V τ L n m) (c : ℂ)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hG1 : ∀ U, G (U + 1) = G U)
    (hGτ : ∀ U, G (U + τ) * cexp (-2 * π * I * (L : ℂ) * c) = G U) :
    (fun u => G (∑ i, u i) * f (fun i => u i + c)) ∈ V τ L n m := by
  obtain ⟨⟨hfo, hfs, hfa⟩, hf1, hf2⟩ := hf
  have hM : ∀ (u : Fin (n + m) → ℂ) (i : Fin (n + m)), Differentiable ℂ fun z => G (∑ j, u j - u i + z) :=
    fun u i => hG.comp ((differentiable_const _).add differentiable_id)
  have hT : ∀ (u : Fin (n + m) → ℂ) (i : Fin (n + m)),
      Differentiable ℂ fun z => f (Function.update (fun j => u j + c) i (z + c)) :=
    fun u i => (hfo.2 (fun j => u j + c) i).comp (differentiable_id.add_const c)
  have e : ∀ (u : Fin (n + m) → ℂ) (i : Fin (n + m)),
      (fun z => (fun u => G (∑ i, u i) * f (fun i => u i + c)) (Function.update u i z)) =
        fun z => G (∑ j, u j - u i + z) * f (Function.update (fun j => u j + c) i (z + c)) := fun u i => by
    funext z
    simp only [sum_update_dev, update_add_dev]
  refine ⟨⟨⟨(hG.continuous.comp (continuous_finsetSum _ fun i _ => continuous_apply i)).mul
      (hfo.1.comp (continuous_id.add continuous_const)), fun u i => by rw [e u i]; exact (hM u i).mul (hT u i)⟩,
    fun u i => ?_, fun s t hst hss u => ?_⟩, fun s t hst hss u l hl j hj => ?_, fun s t hs ht u hu => ?_⟩
  · rw [e u i]
    obtain ⟨_, hF1, hFτ⟩ := hfs (fun j => u j + c) i
    refine ⟨(hM u i).mul (hT u i), fun z => ?_, fun z => ?_⟩
    · beta_reduce
      have h1 := hF1 (z + c)
      beta_reduce at h1
      rw [show ∑ j, u j - u i + (z + 1) = (∑ j, u j - u i + z) + 1 by ring, hG1,
        show z + 1 + c = (z + c) + 1 by ring, h1]
      simp
    · beta_reduce
      have h2 := hFτ (z + c)
      beta_reduce at h2
      rw [show ∑ j, u j - u i + (z + τ) = (∑ j, u j - u i + z) + τ by ring,
        show z + τ + c = (z + c) + τ by ring, h2]
      have hg := hGτ (∑ j, u j - u i + z)
      have he : cexp (-π * I * (L : ℂ) * (2 * (z + c) + τ)) =
          cexp (-π * I * (L : ℂ) * (2 * z + τ)) * cexp (-2 * π * I * (L : ℂ) * c) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
      rw [he]
      linear_combination (cexp (-π * I * (L : ℂ) * (2 * z + τ)) *
        f (Function.update (fun j => u j + c) i (z + c))) * hg
  · show G (∑ i, (u ∘ Equiv.swap s t) i) * f (fun i => (u ∘ Equiv.swap s t) i + c) =
      -(G (∑ i, u i) * f (fun i => u i + c))
    have hsw : (fun i => (u ∘ Equiv.swap s t) i + c) = (fun i => u i + c) ∘ Equiv.swap s t := rfl
    rw [hsw, hfa s t hst hss]
    simp only [Function.comp_apply]
    rw [Equiv.sum_comp]
    ring
  · rw [e u s]
    have hv := hf1 s t hst hss (fun j => u j + c) l hl
    refine vanish3_mul_dev (hM u s) (hT u s) (fun j' hj' => ?_) j hj
    have hc := congrFun (iteratedDeriv_comp_add_const (n := j')
      (f := fun w => f (Function.update (fun j => u j + c) s w)) (s := c)) (u t + l)
    rw [hc, show u t + l + c = u t + c + l by ring]
    exact hv j' hj'
  · unfold relDeriv
    rw [e u s, e u t, deriv_fun_mul ((hM u s) _) ((hT u s) _), deriv_fun_mul ((hM u t) _) ((hT u t) _)]
    have hd : ∀ i : Fin (n + m), deriv (fun z => G (∑ j, u j - u i + z)) (u i) = deriv G (∑ j, u j) := by
      intro i
      have h := ((hG (∑ j, u j - u i + u i)).hasDerivAt).comp_const_add (∑ j, u j - u i) (u i)
      rw [h.deriv, show ∑ j, u j - u i + u i = ∑ j, u j by ring]
    have hdT : ∀ i : Fin (n + m), deriv (fun z => f (Function.update (fun j => u j + c) i (z + c))) (u i) =
        deriv (fun z => f (Function.update (fun j => u j + c) i z)) (u i + c) := by
      intro i
      have h := ((hfo.2 (fun j => u j + c) i (u i + c)).hasDerivAt).comp_add_const (u i) c
      exact h.deriv
    have h2 := hf2 s t hs ht (fun j => u j + c) (by simp only [hu])
    unfold relDeriv at h2
    rw [hd s, hd t, hdT s, hdT t, show ∑ j, u j - u s + u s = ∑ j, u j by ring,
      show ∑ j, u j - u t + u t = ∑ j, u j by ring, Function.update_eq_self, Function.update_eq_self]
    simp only at h2
    linear_combination G (∑ j, u j) * h2

theorem TK2_mem_V_dev (τ : ℍ) {n m : ℕ} (hN : 0 < n + m) {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : f ∈ V τ (2 * (n + m)) n m) : TK2 (n + m) f ∈ V τ (2 * (n + m)) n m := by
  have hNc : ((n + m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc2 : ((2 * (n + m) : ℕ) : ℂ) * (1 / ((n + m : ℕ) : ℂ)) = 2 := by
    rw [one_div, Nat.cast_mul, mul_assoc, mul_inv_cancel₀ hNc, mul_one, Nat.cast_ofNat]
  have h := transl_mem_V_dev τ hf (1 / ((n + m : ℕ) : ℂ)) (G := fun _ => 1) (differentiable_const 1)
    (fun _ => rfl) (fun _ => by
      rw [mul_assoc (-2 * π * I : ℂ), hc2, show -2 * π * I * (2 : ℂ) = -((2 : ℕ) * (2 * π * I)) by
        push_cast
        ring, Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I]
      simp)
  have e : TK2 (n + m) f = fun u => (fun _ => (1 : ℂ)) (∑ i, u i) * f (fun i => u i + 1 / ((n + m : ℕ) : ℂ)) := by
    funext u
    show f (fun i => u i + 1 / ((n + m : ℕ) : ℂ)) = _
    simp
  rw [e]
  exact h

theorem T12_mem_V_dev (τ : ℍ) {n m : ℕ} (hN : 0 < n + m) {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : f ∈ V τ (2 * (n + m)) n m) : T12 τ (n + m) f ∈ V τ (2 * (n + m)) n m := by
  have hNc : ((n + m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc2 : ((2 * (n + m) : ℕ) : ℂ) * ((τ : ℂ) / ((n + m : ℕ) : ℂ)) = 2 * τ := by
    rw [div_eq_mul_inv, Nat.cast_mul, mul_comm (τ : ℂ), ← mul_assoc, mul_assoc ((2 : ℕ) : ℂ),
      mul_inv_cancel₀ hNc, mul_one, Nat.cast_ofNat]
  exact transl_mem_V_dev τ hf ((τ : ℂ) / ((n + m : ℕ) : ℂ)) (G := fun U => cexp (4 * π * I * U + 2 * π * I * τ))
    (by fun_prop)
    (fun U => by
      rw [show 4 * π * I * (U + 1) + 2 * π * I * τ = (4 * π * I * U + 2 * π * I * τ) + ((2 : ℕ) : ℂ) * (2 * π * I) by
        push_cast
        ring, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one])
    (fun U => by
      rw [← Complex.exp_add, mul_assoc (-2 * π * I : ℂ), hc2]
      congr 1
      ring)

theorem pow_mem_V_dev (τ : ℍ) {n m : ℕ} {A : Module.End ℂ ((Fin (n + m) → ℂ) → ℂ)}
    (hA : ∀ f ∈ V τ (2 * (n + m)) n m, A f ∈ V τ (2 * (n + m)) n m) (r : ℕ) :
    ∀ f ∈ V τ (2 * (n + m)) n m, (A ^ r) f ∈ V τ (2 * (n + m)) n m := by
  induction r with
  | zero =>
    intro f hf
    rwa [pow_zero, Module.End.one_apply]
  | succ r ih =>
    intro f hf
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hA f hf)

theorem Qop_mem_V_dev (τ : ℍ) {n m : ℕ} (j : ℕ) {A : Module.End ℂ ((Fin (n + m) → ℂ) → ℂ)}
    (hA : ∀ f ∈ V τ (2 * (n + m)) n m, A f ∈ V τ (2 * (n + m)) n m) {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : f ∈ V τ (2 * (n + m)) n m) : Qop_dev (n + m) j A f ∈ V τ (2 * (n + m)) n m := by
  unfold Qop_dev
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun r _ => by
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (pow_mem_V_dev τ hA r f hf)

theorem projJK_mem_V_dev (τ : ℍ) {n m : ℕ} (hN : 0 < n + m) (jk : Fin (n + m) × Fin (n + m))
    {f : (Fin (n + m) → ℂ) → ℂ} (hf : f ∈ V τ (2 * (n + m)) n m) :
    projJK τ (n + m) jk f ∈ V τ (2 * (n + m)) n m := by
  rw [projJK_eq_Qop_dev, LinearMap.smul_apply, Module.End.mul_apply]
  exact Submodule.smul_mem _ _ (Qop_mem_V_dev τ jk.1 (fun g hg => TK2_mem_V_dev τ hN hg)
    (Qop_mem_V_dev τ jk.2 (fun g hg => T12_mem_V_dev τ hN hg) hf))

/-! ### Proof devices for a joint eigenfunction lying in the image (proof phase, round one; not statements of the paper)

For a joint eigenfunction `f ∈ V` of `(T_K², T_1²)` with eigenvalues `(λ₁, λ₂)`, `Φ_u(C) := f(u + ((C − U)/N)𝟙)`
(`dshift_dev`) lies in `Θ_2[(λ₁⁻¹, λ₂⁻¹)]`. In a basis `b₀, b₁` of that space (`Θ2g_basis_dev`, the pattern of
`thetaSpace_basis_dev`) with interpolation points `z₀, z₁` (`interp1_gen_dev`), the coefficients
`coef_a(u) = Σ_c W_{ca} Φ_u(z_c)` give `Φ_u(C) = Σ_a b_a(C) coef_a(u)`, so `f(u) = Σ_a b_a(U) coef_a(u)` and
`f(u + c𝟙) = Σ_a b_a(U + Nc) coef_a(u)`. The conditions pass to each `coef_a` (`coef_mem_Gnum_dev`): the multipliers
from those of `f` and the eigenvalues; (C1) slice by slice with `c` a parameter, the orders `0, 1, 2` in turn
(`coef_vanish_dev`), each with the independence of `c ↦ b_a(X + Nc)` (`indep_eval_dev`); (C2) through
`relDeriv_transl_dev` and `relDeriv_sum_mul_dev`. -/

def dshift_dev {N : ℕ} (u : Fin N → ℂ) (C : ℂ) : Fin N → ℂ := fun i => u i + (C - ∑ j, u j) / (N : ℂ)

theorem sum_dshift_dev {N : ℕ} (hN : (N : ℂ) ≠ 0) (u : Fin N → ℂ) (C : ℂ) : ∑ i, dshift_dev u C i = C := by
  have hinv : (N : ℂ) * (N : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hN
  simp only [dshift_dev, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination (C - ∑ j, u j) * hinv

theorem dshift_add_const_dev {N : ℕ} (hN : (N : ℂ) ≠ 0) (u : Fin N → ℂ) (c C : ℂ) :
    dshift_dev (fun i => u i + c) C = dshift_dev u C := by
  have hinv : (N : ℂ) * (N : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hN
  funext i
  simp only [dshift_dev, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination (-c) * hinv

theorem dshift_shift_dev {N : ℕ} (u : Fin N → ℂ) (C d : ℂ) :
    (fun i => dshift_dev u C i + d / (N : ℂ)) = dshift_dev u (C + d) := by
  funext i
  simp only [dshift_dev]
  ring

theorem dshift_self_dev {N : ℕ} (u : Fin N → ℂ) : dshift_dev u (∑ i, u i) = u := by
  funext i
  simp [dshift_dev]

theorem dshift_update_dev {N : ℕ} (u : Fin N → ℂ) (k : Fin N) (C d : ℂ) :
    dshift_dev (Function.update u k (u k + d)) C =
      Function.update (dshift_dev u (C - d)) k (dshift_dev u (C - d) k + d) := by
  funext i
  simp only [dshift_dev, sum_update_dev]
  by_cases h : i = k
  · subst h
    simp only [Function.update_self]
    ring
  · simp only [Function.update_of_ne h, dshift_dev]
    ring

theorem dshift_swap_dev {N : ℕ} (u : Fin N → ℂ) (s t : Fin N) (C : ℂ) :
    dshift_dev (u ∘ Equiv.swap s t) C = dshift_dev u C ∘ Equiv.swap s t := by
  funext i
  simp only [dshift_dev, Function.comp_apply]
  rw [Equiv.sum_comp (Equiv.swap s t) u]

theorem differentiable_dshift_C_dev {N : ℕ} (u : Fin N → ℂ) : Differentiable ℂ fun C : ℂ => dshift_dev u C := by
  unfold dshift_dev
  exact differentiable_pi.2 fun i => (differentiable_const (u i)).add ((differentiable_id.sub_const _).div_const _)

theorem differentiable_dshift_u_dev {N : ℕ} (C : ℂ) : Differentiable ℂ fun u : Fin N → ℂ => dshift_dev u C := by
  unfold dshift_dev
  simp only [div_eq_mul_inv]
  exact differentiable_pi.2 fun i => (differentiable_apply i).add
    (((differentiable_const C).sub (Differentiable.fun_sum fun j _ => differentiable_apply j)).mul_const _)

theorem indep_eval_dev {ι : Type*} [Fintype ι] {b : ι → ℂ → ℂ} (hli : LinearIndependent ℂ b) {α : ι → ℂ}
    (h : ∀ C, ∑ a, b a C * α a = 0) : ∀ a, α a = 0 := by
  refine Fintype.linearIndependent_iff.1 hli α ?_
  funext C
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  calc ∑ a, α a * b a C = ∑ a, b a C * α a := Finset.sum_congr rfl fun a _ => mul_comm _ _
    _ = 0 := h C

theorem coef_vanish_dev {b : Fin 2 → ℂ → ℂ} (hb : ∀ a, Differentiable ℂ (b a)) (hli : LinearIndependent ℂ b)
    {A : Fin 2 → ℂ → ℂ} (hA : ∀ a, Differentiable ℂ (A a)) {z₀ : ℂ}
    (h : ∀ w : ℂ, ∀ j < 3, iteratedDeriv j (fun z => ∑ a, b a (w + z) * A a z) z₀ = 0) :
    ∀ a, ∀ j < 3, iteratedDeriv j (A a) z₀ = 0 := by
  have hM : ∀ (w : ℂ) (a : Fin 2), Differentiable ℂ fun z => b a (w + z) :=
    fun w a => (hb a).comp ((differentiable_const w).add differentiable_id)
  have key : ∀ j, j < 3 → ∀ a, iteratedDeriv j (A a) z₀ = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hstep : ∀ w, iteratedDeriv j (fun z => ∑ a, b a (w + z) * A a z) z₀ =
          ∑ a, b a (w + z₀) * iteratedDeriv j (A a) z₀ := by
        intro w
        rw [iteratedDeriv_fun_sum fun a _ =>
          (show Differentiable ℂ fun z => b a (w + z) * A a z from (hM w a).mul (hA a)).contDiff.contDiffAt]
        refine Finset.sum_congr rfl fun a _ => ?_
        have e : (fun z => b a (w + z) * A a z) = (fun z => b a (w + z)) * A a := rfl
        rw [e, iteratedDeriv_mul (hM w a).contDiff.contDiffAt (hA a).contDiff.contDiffAt,
          Finset.sum_eq_single 0]
        · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero]
        · intro i hi hi0
          have hlt : j - i < j := by
            have := Finset.mem_range.1 hi
            omega
          rw [ih (j - i) hlt (by omega) a, mul_zero]
        · intro h0
          exact absurd (Finset.mem_range.2 (Nat.succ_pos j)) h0
      exact indep_eval_dev hli fun C => by
        have h' := h (C - z₀) j hj
        rw [hstep, sub_add_cancel] at h'
        exact h'
  intro a j hj
  exact key j hj a

theorem relDeriv_transl_dev {N : ℕ} {f : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) (c : ℂ) (s t : Fin N)
    (u : Fin N → ℂ) : relDeriv (fun v => f (fun i => v i + c)) s t u = relDeriv f s t (fun i => u i + c) := by
  unfold relDeriv
  have e : ∀ i : Fin N, (fun z => (fun v => f (fun i => v i + c)) (Function.update u i z)) =
      fun z => f (Function.update (fun j => u j + c) i (z + c)) := fun i => by
    funext z
    simp only [update_add_dev]
  have hd : ∀ i : Fin N, deriv (fun z => f (Function.update (fun j => u j + c) i (z + c))) (u i) =
      deriv (fun z => f (Function.update (fun j => u j + c) i z)) (u i + c) := fun i =>
    ((hf.2 (fun j => u j + c) i (u i + c)).hasDerivAt.comp_add_const (u i) c).deriv
  rw [e s, e t, hd s, hd t]

theorem relDeriv_sum_mul_dev {N : ℕ} {ι : Type*} [Fintype ι] {G : ι → ℂ → ℂ} (hG : ∀ a, Differentiable ℂ (G a))
    {A : ι → (Fin N → ℂ) → ℂ} (hA : ∀ a, IsOsgood (A a)) (s t : Fin N) (u : Fin N → ℂ) :
    relDeriv (fun v => ∑ a, G a (∑ i, v i) * A a v) s t u = ∑ a, G a (∑ i, u i) * relDeriv (A a) s t u := by
  unfold relDeriv
  have e : ∀ i : Fin N, (fun z => (fun v => ∑ a, G a (∑ i, v i) * A a v) (Function.update u i z)) =
      fun z => ∑ a, G a (∑ j, u j - u i + z) * A a (Function.update u i z) := fun i => by
    funext z
    simp only [sum_update_dev]
  have hd : ∀ i : Fin N, deriv (fun z => ∑ a, G a (∑ j, u j - u i + z) * A a (Function.update u i z)) (u i) =
      ∑ a, (deriv (G a) (∑ j, u j) * A a u + G a (∑ j, u j) * deriv (fun z => A a (Function.update u i z)) (u i)) := by
    intro i
    have h : ∀ a, HasDerivAt (fun z => G a (∑ j, u j - u i + z) * A a (Function.update u i z))
        (deriv (G a) (∑ j, u j) * A a u + G a (∑ j, u j) * deriv (fun z => A a (Function.update u i z)) (u i))
        (u i) := by
      intro a
      have h1 := ((hG a (∑ j, u j - u i + u i)).hasDerivAt).comp_const_add (∑ j, u j - u i) (u i)
      have h3 := h1.mul ((hA a).2 u i (u i)).hasDerivAt
      rwa [show ∑ j, u j - u i + u i = ∑ j, u j by ring, Function.update_eq_self] at h3
    exact (HasDerivAt.fun_sum fun a _ => h a).deriv
  rw [e s, e t, hd s, hd t, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem Θ2g_basis_dev (τ : ℍ) {N : ℕ} (jk : Fin N × Fin N) :
    ∃ b : Fin 2 → ℂ → ℂ, (∀ k, b k ∈ Θ2g τ (rootPair N jk)) ∧ LinearIndependent ℂ b ∧
      ∀ F ∈ Θ2g τ (rootPair N jk), F ∈ Submodule.span ℂ (Set.range b) := by
  have h2 : 0 < Module.finrank ℂ (Θ2g (τ : ℂ) (rootPair N jk)) := by
    rw [finrank_Θ2g_rootPair]
    norm_num
  have : Module.Finite ℂ (Θ2g (τ : ℂ) (rootPair N jk)) := Module.finite_of_finrank_pos h2
  let B := Module.finBasisOfFinrankEq ℂ (Θ2g (τ : ℂ) (rootPair N jk)) (finrank_Θ2g_rootPair τ jk)
  refine ⟨fun k => (B k : ℂ → ℂ), fun k => (B k).2,
    B.linearIndependent.map' (Θ2g (τ : ℂ) (rootPair N jk)).subtype (Submodule.ker_subtype _), fun F hF => ?_⟩
  have hsum : (⟨F, hF⟩ : Θ2g (τ : ℂ) (rootPair N jk)) = ∑ k, B.repr ⟨F, hF⟩ k • B k := (B.sum_repr _).symm
  have hF' : F = ∑ k, B.repr ⟨F, hF⟩ k • (B k : ℂ → ℂ) := by
    have := congrArg Subtype.val hsum
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this
  rw [hF']
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

theorem exists_rootPair_inv_dev {N : ℕ} (hN : 0 < N) (jk : Fin N × Fin N) :
    ∃ jk' : Fin N × Fin N, rootPair N jk' = ((rootPair N jk).1⁻¹, (rootPair N jk).2⁻¹) :=
  exists_rootPair hN ⟨by simp only [inv_pow, (rootPair_pow N jk).1, inv_one],
    by simp only [inv_pow, (rootPair_pow N jk).2, inv_one]⟩

theorem coef_mem_Gnum_dev (τ : ℍ) {n m : ℕ} (hN : 0 < n + m) {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : f ∈ V τ (2 * (n + m)) n m) {l1 l2 : ℂ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0)
    (hK : ∀ v, f (fun i => v i + 1 / ((n + m : ℕ) : ℂ)) = l1 * f v)
    (h1 : ∀ v, cexp (4 * π * I * (∑ i, v i) + 2 * π * I * τ) * f (fun i => v i + (τ : ℂ) / ((n + m : ℕ) : ℂ)) =
      l2 * f v)
    {b : Fin 2 → ℂ → ℂ} (hb : ∀ a, Differentiable ℂ (b a)) (hli : LinearIndependent ℂ b)
    (W : Fin 2 → Fin 2 → ℂ) (z : Fin 2 → ℂ) {coef : Fin 2 → (Fin (n + m) → ℂ) → ℂ}
    (hcoef : ∀ a u, coef a u = ∑ c, W c a * f (dshift_dev u (z c)))
    (hrepr : ∀ u C, f (dshift_dev u C) = ∑ a, b a C * coef a u) (a : Fin 2) :
    coef a ∈ Gnum τ n m (l1⁻¹, l2⁻¹) := by
  have hNc : ((n + m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hfd : Differentiable ℂ f := differentiable_of_isCanonShape_dev τ (by omega) hf.1
  obtain ⟨⟨hfo, hfs, hfa⟩, hf1, hf2⟩ := hf
  have hcoefd : ∀ a', Differentiable ℂ (coef a') := by
    intro a'
    rw [show coef a' = fun u => ∑ c, W c a' * f (dshift_dev u (z c)) from funext (hcoef a')]
    exact Differentiable.fun_sum fun c _ => (differentiable_const _).mul (hfd.comp (differentiable_dshift_u_dev (z c)))
  have hcoefo : ∀ a', IsOsgood (coef a') := fun a' => isOsgood_of_differentiable_dev (hcoefd a')
  have hrepr' : ∀ (v : Fin (n + m) → ℂ) (c : ℂ),
      f (fun i => v i + c) = ∑ a', b a' (∑ i, v i + ((n + m : ℕ) : ℂ) * c) * coef a' v := by
    intro v c
    rw [← hrepr]
    congr 1
    funext i
    simp only [dshift_dev, add_sub_cancel_left, mul_div_cancel_left₀ c hNc]
  have P1 : ∀ (v : Fin (n + m) → ℂ) (k : Fin (n + m)), f (Function.update v k (v k + 1)) = f v := by
    intro v k
    have h := (hfs v k).2.1 (v k)
    beta_reduce at h
    rw [h, Function.update_eq_self]
    simp
  have Pτ : ∀ (v : Fin (n + m) → ℂ) (k : Fin (n + m)), f (Function.update v k (v k + τ)) =
      cexp (-π * I * ((2 * (n + m) : ℕ) : ℂ) * (2 * v k + τ)) * f v := by
    intro v k
    have h := (hfs v k).2.2 (v k)
    beta_reduce at h
    rw [h, Function.update_eq_self]
    simp
  rw [mem_Gnum]
  refine ⟨hcoefo a, fun u c => ?_, fun u k => ?_, fun u k => ?_, fun s t hst hss u => ?_, fun s t hst hss => ?_,
    fun s t hs ht u hu => ?_⟩
  · simp only [hcoef, dshift_add_const_dev hNc]
  · dsimp only
    simp only [hcoef]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hk := hK (dshift_dev u (z c - 1))
    rw [dshift_shift_dev, sub_add_cancel] at hk
    rw [dshift_update_dev, P1, (eq_inv_mul_iff_mul_eq₀ hl1).2 hk.symm]
    ring
  · dsimp only
    simp only [hcoef]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hv := h1 (dshift_dev u (z c - τ))
    rw [sum_dshift_dev hNc, dshift_shift_dev, sub_add_cancel] at hv
    have hD : ((n + m : ℕ) : ℂ) * ((z c - τ - ∑ j, u j) / ((n + m : ℕ) : ℂ)) = z c - τ - ∑ j, u j :=
      mul_div_cancel₀ _ hNc
    have hexp : cexp (-π * I * ((2 * (n + m) : ℕ) : ℂ) * (2 * dshift_dev u (z c - τ) k + τ)) *
        cexp (4 * π * I * (z c - τ) + 2 * π * I * τ) =
        cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ - 4 * π * I * (((n + m : ℕ) : ℂ) * u k - ∑ i, u i)) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [dshift_dev]
      rw [Nat.cast_mul, Nat.cast_ofNat]
      linear_combination (-4 * π * I) * hD
    rw [dshift_update_dev, Pτ, (eq_inv_mul_iff_mul_eq₀ hl2).2 hv.symm, ← hexp]
    ring
  · simp only [hcoef]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dshift_swap_dev, hfa s t hst hss]
    ring
  · intro u l hl
    refine coef_vanish_dev hb hli (A := fun a' z' => coef a' (Function.update u s z'))
      (fun a' => (hcoefo a').2 u s) (z₀ := u t + l) (fun w j hj => ?_) a
    show iteratedDeriv j (fun z' => ∑ a', b a' (w + z') * coef a' (Function.update u s z')) (u t + l) = 0
    obtain ⟨c, hNcw⟩ : ∃ c : ℂ, ((n + m : ℕ) : ℂ) * c = w - (∑ i, u i - u s) :=
      ⟨(w - (∑ i, u i - u s)) / ((n + m : ℕ) : ℂ), mul_div_cancel₀ _ hNc⟩
    have hfun : (fun z' => ∑ a', b a' (w + z') * coef a' (Function.update u s z')) =
        fun z' => f (Function.update (fun i => u i + c) s (z' + c)) := by
      funext z'
      rw [← update_add_dev, hrepr' (Function.update u s z') c, sum_update_dev]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [show ∑ j, u j - u s + z' + ((n + m : ℕ) : ℂ) * c = w + z' by rw [hNcw]; ring]
    rw [hfun]
    have hc' := congrFun (iteratedDeriv_comp_add_const (n := j)
      (f := fun w' => f (Function.update (fun i => u i + c) s w')) (s := c)) (u t + l)
    rw [hc', show u t + l + c = u t + c + l by ring]
    exact hf1 s t hst hss (fun i => u i + c) l hl j hj
  · have key : ∀ c : ℂ, ∑ a', b a' (∑ i, u i + ((n + m : ℕ) : ℂ) * c) * relDeriv (coef a') s t u = 0 := by
      intro c
      have h2 := hf2 s t hs ht (fun i => u i + c) (by simp only [hu])
      rw [← relDeriv_transl_dev hfo c s t u,
        show (fun v => f (fun i => v i + c)) =
          fun v => ∑ a', b a' (∑ i, v i + ((n + m : ℕ) : ℂ) * c) * coef a' v from funext fun v => hrepr' v c,
        relDeriv_sum_mul_dev (G := fun a' U => b a' (U + ((n + m : ℕ) : ℂ) * c))
          (fun a' => (hb a').comp (differentiable_id.add_const (((n + m : ℕ) : ℂ) * c))) hcoefo] at h2
      exact h2
    have hα : ∀ a', relDeriv (coef a') s t u = 0 := by
      refine indep_eval_dev hli fun C => ?_
      obtain ⟨c, hc⟩ : ∃ c : ℂ, ∑ i, u i + ((n + m : ℕ) : ℂ) * c = C :=
        ⟨(C - ∑ i, u i) / ((n + m : ℕ) : ℂ), by rw [mul_div_cancel₀ _ hNc]; ring⟩
      have h := key c
      rw [hc] at h
      exact h
    exact hα a

theorem eigen_mem_imageTensor_dev (τ : ℍ) {n m : ℕ} (hN : 0 < n + m) {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : f ∈ V τ (2 * (n + m)) n m) (jk : Fin (n + m) × Fin (n + m))
    (hK : TK2 (n + m) f = (rootPair (n + m) jk).1 • f) (h1 : T12 τ (n + m) f = (rootPair (n + m) jk).2 • f) :
    f ∈ imageTensor τ n m ((rootPair (n + m) jk).1⁻¹, (rootPair (n + m) jk).2⁻¹) := by
  have hNc : ((n + m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hl1 : (rootPair (n + m) jk).1 ≠ 0 := Complex.exp_ne_zero _
  have hl2 : (rootPair (n + m) jk).2 ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨jk', hjk'⟩ := exists_rootPair_inv_dev hN jk
  obtain ⟨b, hbmem, hli, hspan⟩ := Θ2g_basis_dev τ jk'
  rw [hjk'] at hbmem hspan
  obtain ⟨z, hz⟩ := exists_points_det_ne_zero_dev 2 b hli
  have hfd : Differentiable ℂ f := differentiable_of_isCanonShape_dev τ (by omega) hf.1
  have hK' : ∀ v, f (fun i => v i + 1 / ((n + m : ℕ) : ℂ)) = (rootPair (n + m) jk).1 * f v :=
    fun v => congrFun hK v
  have h1' : ∀ v, cexp (4 * π * I * (∑ i, v i) + 2 * π * I * τ) * f (fun i => v i + (τ : ℂ) / ((n + m : ℕ) : ℂ)) =
      (rootPair (n + m) jk).2 * f v := fun v => congrFun h1 v
  have hΦ : ∀ u, (fun C => f (dshift_dev u C)) ∈
      Θ2g τ ((rootPair (n + m) jk).1⁻¹, (rootPair (n + m) jk).2⁻¹) := by
    intro u
    refine ⟨hfd.comp (differentiable_dshift_C_dev u), fun C => ?_, fun C => ?_⟩
    · show f (dshift_dev u (C + 1)) = ((rootPair (n + m) jk).1⁻¹)⁻¹ * f (dshift_dev u C)
      rw [inv_inv, ← dshift_shift_dev]
      exact hK' (dshift_dev u C)
    · show f (dshift_dev u (C + τ)) =
        ((rootPair (n + m) jk).2⁻¹)⁻¹ * cexp (-4 * π * I * C - 2 * π * I * τ) * f (dshift_dev u C)
      rw [inv_inv, ← dshift_shift_dev]
      have h := h1' (dshift_dev u C)
      rw [sum_dshift_dev hNc] at h
      have he : cexp (-4 * π * I * C - 2 * π * I * τ) * cexp (4 * π * I * C + 2 * π * I * τ) = 1 := by
        rw [← Complex.exp_add, show -4 * π * I * C - 2 * π * I * τ + (4 * π * I * C + 2 * π * I * τ) = (0 : ℂ) by ring,
          Complex.exp_zero]
      linear_combination cexp (-4 * π * I * C - 2 * π * I * τ) * h -
        f (fun i => dshift_dev u C i + (τ : ℂ) / ((n + m : ℕ) : ℂ)) * he
  obtain ⟨coef, hcoef⟩ : ∃ coef : Fin 2 → (Fin (n + m) → ℂ) → ℂ,
      ∀ a u, coef a u = ∑ c, (Matrix.of fun a c => b a (z c))⁻¹ c a * f (dshift_dev u (z c)) :=
    ⟨_, fun _ _ => rfl⟩
  have hrepr : ∀ u C, f (dshift_dev u C) = ∑ a, b a C * coef a u := by
    intro u C
    rw [interp1_gen_dev b (isUnit_iff_ne_zero.mpr hz) (hspan _ (hΦ u)) C]
    simp only [hcoef, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  have hf_eq : f = ∑ a, fun u => b a (∑ i, u i) * coef a u := by
    funext u
    simp only [Finset.sum_apply]
    rw [← hrepr, dshift_self_dev]
  rw [hf_eq]
  exact Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨b a, hbmem a, coef a,
    coef_mem_Gnum_dev τ hN hf hl1 hl2 hK' h1' (fun a' => (hbmem a').1) hli _ z hcoef hrepr a, rfl⟩

/-! ## Lemma C.B(b): the surjective and injective halves and the count

These four reviewed statements stood after `imageTensor_le_V` in the statement phase; they are placed here, unchanged,
because their proofs use `T_K²`, `T_1²`, the projectors and the devices above (proof phase, round one). -/

/-- **Lemma C.B(b)**, the surjective half: "`$T_K^2$ and $T_1^2$ preserve $V_{n,m}$`"; "`They commute and have finite order, so $V_{n,m}=\bigoplus V_\lambda$ over joint eigenvalues $\lambda=(\lambda_1,\lambda_2)\in\mu_N^2$.`"
"`So $C\mapsto\varphi((C-U)/N)$ lies in $\kzTh_2[\varepsilon]$ with $\varepsilon=(\lambda_1^{-1},\lambda_2^{-1})$.`"
"`The coefficients are unique and are obtained by solving a $2\times2$ system from two values of $c$, so they are holomorphic in $u$.`"
"`\emph{The conditions pass to each $a_\ell$.}`" — every `f ∈ V_{n,m}` (level `2N`, `N ≥ 1`) lies in the sum over
`ε ∈ μ_N²` of the images. -/
theorem V_le_iSup_imageTensor (τ : ℍ) {n m : ℕ} (hN : 0 < n + m) :
    V τ (2 * (n + m)) n m ≤ ⨆ jk : Fin (n + m) × Fin (n + m), imageTensor τ n m (rootPair (n + m) jk) := by
  intro f hf
  have hK := TK2_pow_dev τ hN hf.1
  have hT := T12_pow_dev τ hN hf.1
  rw [← sum_projJK_dev (τ : ℂ) hN (f := f)]
  refine Submodule.sum_mem _ fun jk _ => ?_
  obtain ⟨jk', hjk'⟩ := exists_rootPair_inv_dev hN jk
  have hmem := eigen_mem_imageTensor_dev τ hN (projJK_mem_V_dev τ hN jk hf) jk
    (TK2_projJK_dev (τ : ℂ) hN hK jk) (T12_projJK_dev (τ : ℂ) hN hT jk)
  rw [← hjk'] at hmem
  exact Submodule.mem_iSup_of_mem jk' hmem

/-! ### Proof devices for the injective half (proof phase, round one; not statements of the paper): on a joint
eigenfunction with eigenvalues `rootPair jk₁`, `P_{jk'}` is the identity if `jk' = jk₁` and zero otherwise
(`projJK_eigen_dev`), from the character sums `Σ_{r<N} e^{−2πijr/N} e^{2πij₁r/N} = N δ_{jj₁}` (`root_char_dev`). -/

theorem root_char_dev {N : ℕ} (hN : 0 < N) (j j₁ : Fin N) :
    ∑ r : Fin N, cexp (-(2 * π * I * (((j : ℕ) * (r : ℕ) : ℕ) : ℂ) / (N : ℂ))) *
      cexp (2 * π * I * ((j₁ : ℕ) : ℂ) / (N : ℂ)) ^ (r : ℕ) = if j₁ = j then (N : ℂ) else 0 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinv : (N : ℂ) * (N : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hNc
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, ζ = cexp (2 * π * I * ((j₁ : ℕ) : ℂ) / (N : ℂ)) *
      cexp (-(2 * π * I * ((j : ℕ) : ℂ) / (N : ℂ))) := ⟨_, rfl⟩
  have hterm : ∀ r : ℕ, cexp (-(2 * π * I * (((j : ℕ) * r : ℕ) : ℂ) / (N : ℂ))) *
      cexp (2 * π * I * ((j₁ : ℕ) : ℂ) / (N : ℂ)) ^ r = ζ ^ r := by
    intro r
    rw [hζ, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun r => ζ ^ r)]
  by_cases h : j₁ = j
  · rw [ite_eq_left h]
    have h1 : ζ = 1 := by
      rw [hζ, h, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    rw [h1]
    simp
  · rw [ite_eq_right h]
    have hζ1 : ζ ≠ 1 := by
      intro h1
      apply h
      have h2 : cexp (-(2 * π * I * ((j : ℕ) : ℂ) / (N : ℂ))) * cexp (2 * π * I * ((j : ℕ) : ℂ) / (N : ℂ)) = 1 := by
        rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
      have h3 : cexp (2 * π * I * ((j₁ : ℕ) : ℂ) / (N : ℂ)) = cexp (2 * π * I * ((j : ℕ) : ℂ) / (N : ℂ)) := by
        linear_combination (-cexp (2 * π * I * ((j₁ : ℕ) : ℂ) / (N : ℂ))) * h2 -
          cexp (2 * π * I * ((j : ℕ) : ℂ) / (N : ℂ)) * hζ + cexp (2 * π * I * ((j : ℕ) : ℂ) / (N : ℂ)) * h1
      exact Fin.ext (rootExp_inj_dev j₁.isLt j.isLt h3)
    have hζN : ζ ^ N = 1 := by
      rw [hζ, mul_pow, rootExp_pow_dev hN.ne' (j₁ : ℕ), one_mul, ← Complex.exp_nat_mul,
        show (N : ℂ) * -(2 * π * I * ((j : ℕ) : ℂ) / (N : ℂ)) = -(((j : ℕ) : ℂ) * (2 * π * I)) by
          linear_combination (-(2 * π * I * ((j : ℕ) : ℂ))) * hinv,
        Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I, inv_one]
    rw [geom_sum_eq hζ1, hζN, sub_self, zero_div]

theorem projJK_eigen_dev (τ : ℂ) {N : ℕ} (hN : 0 < N) {v : (Fin N → ℂ) → ℂ} (jk₁ jk' : Fin N × Fin N)
    (hK : TK2 N v = (rootPair N jk₁).1 • v) (hT : T12 τ N v = (rootPair N jk₁).2 • v) :
    projJK τ N jk' v = if jk₁ = jk' then v else 0 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpow : ∀ (A : Module.End ℂ ((Fin N → ℂ) → ℂ)) (μ : ℂ), A v = μ • v → ∀ r : ℕ, (A ^ r) v = μ ^ r • v := by
    intro A μ hA r
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hA, smul_smul, pow_succ]
  have hQ : ∀ (A : Module.End ℂ ((Fin N → ℂ) → ℂ)) (j j₁ : Fin N),
      A v = cexp (2 * π * I * ((j₁ : ℕ) : ℂ) / (N : ℂ)) • v →
      Qop_dev N j A v = (if j₁ = j then (N : ℂ) else 0) • v := by
    intro A j j₁ hA
    unfold Qop_dev
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hpow A _ hA, smul_smul]
    rw [← Finset.sum_smul, root_char_dev hN j j₁]
  rw [projJK_eq_Qop_dev, LinearMap.smul_apply, Module.End.mul_apply, hQ (T12 τ N) jk'.2 jk₁.2 hT, map_smul,
    hQ (TK2 N) jk'.1 jk₁.1 hK, smul_smul, smul_smul]
  by_cases h : jk₁ = jk'
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl,
      show (N : ℂ)⁻¹ ^ 2 * (N : ℂ) * (N : ℂ) = 1 by field_simp, one_smul]
  · rw [ite_eq_right h]
    by_cases h1 : jk₁.1 = jk'.1
    · have h2 : jk₁.2 ≠ jk'.2 := fun h2 => h (Prod.ext h1 h2)
      rw [ite_eq_right h2]
      simp
    · rw [ite_eq_right h1]
      simp

/-- **Lemma C.B(b)**, the injective half: "`Suppose $\sum_\varepsilon\sum_\ell F_{\varepsilon,\ell}(U)J^2g_{\varepsilon,\ell}=0$, where for each $\varepsilon$ the $F_{\varepsilon,\ell}$ ($\ell=1,2$) are a basis of $\kzTh_2[\varepsilon]$.`"
"`Hence every $g_{\varepsilon,\ell}(u)=0$.`" — in numerator form, with two independent `F` in each `Θ_2[ε]`,
`ε ∈ μ_N²`. -/
theorem lemB_injective (τ : ℍ) {n m : ℕ} (hN : 0 < n + m)
    (F : Fin (n + m) × Fin (n + m) → Fin 2 → ℂ → ℂ) (hF : ∀ jk r, F jk r ∈ Θ2g τ (rootPair (n + m) jk))
    (hFi : ∀ jk, LinearIndependent ℂ (F jk))
    (a : Fin (n + m) × Fin (n + m) → Fin 2 → (Fin (n + m) → ℂ) → ℂ)
    (ha : ∀ jk r, a jk r ∈ Gnum τ n m (rootPair (n + m) jk))
    (hsum : ∀ u : Fin (n + m) → ℂ, ∑ jk, ∑ r, F jk r (∑ i, u i) * a jk r u = 0) :
    ∀ jk r, a jk r = 0 := by
  have hNc : ((n + m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : ∀ (u : Fin (n + m) → ℂ) (c : ℂ), ∑ i, (u i + c) = ∑ i, u i + ((n + m : ℕ) : ℂ) * c := by
    intro u c
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hg : ∀ jk, (fun u => ∑ r, F jk r (∑ i, u i) * a jk r u) ∈ imageTensor τ n m (rootPair (n + m) jk) := by
    intro jk
    have e : (fun u => ∑ r, F jk r (∑ i, u i) * a jk r u) = ∑ r, fun u => F jk r (∑ i, u i) * a jk r u := by
      funext u
      simp only [Finset.sum_apply]
    rw [e]
    exact Submodule.sum_mem _ fun r _ => Submodule.subset_span ⟨F jk r, hF jk r, a jk r, ha jk r, rfl⟩
  choose jinv hjinv using fun jk : Fin (n + m) × Fin (n + m) => exists_rootPair_inv_dev hN jk
  intro jk₀ r₀
  have hproj : ∀ jk, projJK τ (n + m) (jinv jk₀) (fun u => ∑ r, F jk r (∑ i, u i) * a jk r u) =
      if jk = jk₀ then (fun u => ∑ r, F jk r (∑ i, u i) * a jk r u) else 0 := by
    intro jk
    obtain ⟨hK, hT⟩ := lemB_c τ hN (rootPair (n + m) jk) (hg jk)
    rw [show (rootPair (n + m) jk).1⁻¹ = (rootPair (n + m) (jinv jk)).1 by rw [hjinv]] at hK
    rw [show (rootPair (n + m) jk).2⁻¹ = (rootPair (n + m) (jinv jk)).2 by rw [hjinv]] at hT
    rw [projJK_eigen_dev (τ : ℂ) hN (jinv jk) (jinv jk₀) hK hT]
    have hiff : jinv jk = jinv jk₀ ↔ jk = jk₀ := by
      constructor
      · intro h
        have h2 := hjinv jk
        rw [h, hjinv jk₀, Prod.mk.injEq] at h2
        apply rootPair_injective (n + m)
        exact Prod.ext (inv_inj.1 h2.1).symm (inv_inj.1 h2.2).symm
      · rintro rfl
        rfl
    by_cases h : jk = jk₀
    · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
    · rw [ite_eq_right (mt hiff.1 h), ite_eq_right h]
  have hzero : (∑ jk, fun u => ∑ r, F jk r (∑ i, u i) * a jk r u) = 0 := by
    funext u
    simp only [Finset.sum_apply, Pi.zero_apply]
    exact hsum u
  have hg0 : (fun u => ∑ r, F jk₀ r (∑ i, u i) * a jk₀ r u) = 0 := by
    have h := congrArg (projJK τ (n + m) (jinv jk₀)) hzero
    rw [map_sum, map_zero] at h
    simp only [hproj] at h
    simpa using h
  have hα : ∀ u, ∀ r, a jk₀ r u = 0 := by
    intro u
    refine indep_eval_dev (hFi jk₀) fun C => ?_
    obtain ⟨c, hc⟩ : ∃ c : ℂ, ∑ i, u i + ((n + m : ℕ) : ℂ) * c = C :=
      ⟨(C - ∑ i, u i) / ((n + m : ℕ) : ℂ), by rw [mul_div_cancel₀ _ hNc]; ring⟩
    have h := congrFun hg0 (fun i => u i + c)
    simp only [Pi.zero_apply] at h
    rw [hs, hc] at h
    have hinv_a : ∀ r, a jk₀ r (fun i => u i + c) = a jk₀ r u := fun r => (mem_Gnum.1 (ha jk₀ r)).2.1 u c
    simp only [hinv_a] at h
    exact h
  funext u
  exact hα u r₀

/-! ### Proof devices for the count (proof phase, round one; not statements of the paper): for a basis `b_ε` of each
`Θ_2[ε]`, the linear map `Ψ(a) = Σ_ε Σ_ℓ b_{ε,ℓ}(U) a_{ε,ℓ}(u)` on `Π_ε (Fin 2 → 𝒢(ε))` (`tensorMap_dev`) has its image in
`V` (`prod_mem_V_dev`), contains `V` (`V_le_iSup_imageTensor`), and is injective (`lemB_injective`); its domain has
dimension `2 Σ_ε dim 𝒢(ε)`. -/

def tensorMap_dev (τ : ℍ) (n m : ℕ) (b : Fin (n + m) × Fin (n + m) → Fin 2 → ℂ → ℂ) :
    (Π jk : Fin (n + m) × Fin (n + m), Fin 2 → Gnum τ n m (rootPair (n + m) jk)) →ₗ[ℂ]
      ((Fin (n + m) → ℂ) → ℂ) where
  toFun x := fun u => ∑ jk, ∑ r, b jk r (∑ i, u i) * (x jk r : (Fin (n + m) → ℂ) → ℂ) u
  map_add' x y := by
    funext u
    simp only [Pi.add_apply, Submodule.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext u
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun jk _ => Finset.sum_congr rfl fun r _ => ?_
    ring

theorem tensorMap_mem_V_dev (τ : ℍ) {n m : ℕ} {b : Fin (n + m) × Fin (n + m) → Fin 2 → ℂ → ℂ}
    (hb : ∀ jk r, b jk r ∈ Θ2g τ (rootPair (n + m) jk))
    (x : Π jk : Fin (n + m) × Fin (n + m), Fin 2 → Gnum τ n m (rootPair (n + m) jk)) :
    tensorMap_dev τ n m b x ∈ V τ (2 * (n + m)) n m := by
  have e : tensorMap_dev τ n m b x =
      ∑ jk, ∑ r, fun u => b jk r (∑ i, u i) * (x jk r : (Fin (n + m) → ℂ) → ℂ) u := by
    funext u
    simp only [Finset.sum_apply]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun jk _ => Submodule.sum_mem _ fun r _ =>
    prod_mem_V_dev τ (Complex.exp_ne_zero _) (Complex.exp_ne_zero _) (hb jk r) (x jk r).2

theorem V_le_range_tensorMap_dev (τ : ℍ) {n m : ℕ} (hN : 0 < n + m)
    {b : Fin (n + m) × Fin (n + m) → Fin 2 → ℂ → ℂ}
    (hspan : ∀ jk, ∀ F ∈ Θ2g τ (rootPair (n + m) jk), F ∈ Submodule.span ℂ (Set.range (b jk))) :
    V τ (2 * (n + m)) n m ≤ LinearMap.range (tensorMap_dev τ n m b) := by
  refine (V_le_iSup_imageTensor τ hN).trans (iSup_le fun jk => ?_)
  unfold imageTensor
  rw [Submodule.span_le]
  rintro g ⟨F, hF, a, ha, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan jk F hF)
  rw [SetLike.mem_coe, LinearMap.mem_range]
  refine ⟨Pi.single jk (fun r => c r • (⟨a, ha⟩ : Gnum τ n m (rootPair (n + m) jk))), ?_⟩
  funext u
  simp only [tensorMap_dev, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single jk]
  · simp only [Pi.single_eq_same, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [← hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  · intro jk' _ hne
    rw [Pi.single_eq_of_ne hne]
    simp
  · intro h
    exact absurd (Finset.mem_univ jk) h

theorem tensorMap_injective_dev (τ : ℍ) {n m : ℕ} (hN : 0 < n + m)
    {b : Fin (n + m) × Fin (n + m) → Fin 2 → ℂ → ℂ} (hb : ∀ jk r, b jk r ∈ Θ2g τ (rootPair (n + m) jk))
    (hli : ∀ jk, LinearIndependent ℂ (b jk)) : Function.Injective (tensorMap_dev τ n m b) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h := lemB_injective τ hN b hb hli (fun jk r => (x jk r : (Fin (n + m) → ℂ) → ℂ)) (fun jk r => (x jk r).2)
    (fun u => congrFun hx u)
  funext jk r
  exact Subtype.ext (h jk r)

theorem finrank_tensorDomain_dev (τ : ℍ) (n m : ℕ)
    (hfin : ∀ jk : Fin (n + m) × Fin (n + m), FiniteDimensional ℂ (Gnum τ n m (rootPair (n + m) jk))) :
    Module.finrank ℂ (Π jk : Fin (n + m) × Fin (n + m), Fin 2 → Gnum τ n m (rootPair (n + m) jk)) =
      2 * ∑ jk : Fin (n + m) × Fin (n + m), Module.finrank ℂ (Gnum τ n m (rootPair (n + m) jk)) := by
  rw [Module.finrank_pi_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun jk _ => ?_
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Lemma C.B(b)**: "`In particular $\dim\ker H|_{n,m}=2\sum_{\varepsilon\in\mu_N^2}\dim\kzG(n,m;\varepsilon)$`" — the
inequality the count uses (from the surjective half), with the finite dimension of `V` it yields. -/
theorem finrank_V_le (τ : ℍ) {n m : ℕ} (hN : 0 < n + m)
    (hfin : ∀ jk : Fin (n + m) × Fin (n + m), FiniteDimensional ℂ (Gnum τ n m (rootPair (n + m) jk))) :
    FiniteDimensional ℂ (V τ (2 * (n + m)) n m) ∧
      Module.finrank ℂ (V τ (2 * (n + m)) n m) ≤
        2 * ∑ jk : Fin (n + m) × Fin (n + m), Module.finrank ℂ (Gnum τ n m (rootPair (n + m) jk)) := by
  refine ⟨V_finiteDimensional_dev τ (by omega) n m, ?_⟩
  choose b hb hli hspan using fun jk : Fin (n + m) × Fin (n + m) => Θ2g_basis_dev τ jk
  calc Module.finrank ℂ (V τ (2 * (n + m)) n m)
      ≤ Module.finrank ℂ (LinearMap.range (tensorMap_dev τ n m b)) :=
        Submodule.finrank_mono (V_le_range_tensorMap_dev τ hN hspan)
    _ ≤ Module.finrank ℂ (Π jk : Fin (n + m) × Fin (n + m), Fin 2 → Gnum τ n m (rootPair (n + m) jk)) :=
        LinearMap.finrank_range_le _
    _ = 2 * ∑ jk : Fin (n + m) × Fin (n + m), Module.finrank ℂ (Gnum τ n m (rootPair (n + m) jk)) :=
        finrank_tensorDomain_dev τ n m hfin

/-- **Lemma C.B(b)**: "`In particular $\dim\ker H|_{n,m}=2\sum_{\varepsilon\in\mu_N^2}\dim\kzG(n,m;\varepsilon)$`" — the
equality (with the injective half). -/
theorem finrank_V_eq (τ : ℍ) {n m : ℕ} (hN : 0 < n + m)
    (hfin : ∀ jk : Fin (n + m) × Fin (n + m), FiniteDimensional ℂ (Gnum τ n m (rootPair (n + m) jk))) :
    Module.finrank ℂ (V τ (2 * (n + m)) n m) =
      2 * ∑ jk : Fin (n + m) × Fin (n + m), Module.finrank ℂ (Gnum τ n m (rootPair (n + m) jk)) := by
  choose b hb hli hspan using fun jk : Fin (n + m) × Fin (n + m) => Θ2g_basis_dev τ jk
  have hrange : LinearMap.range (tensorMap_dev τ n m b) = V τ (2 * (n + m)) n m := by
    refine le_antisymm (fun g hg => ?_) (V_le_range_tensorMap_dev τ hN hspan)
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hg
    exact tensorMap_mem_V_dev τ hb x
  rw [← hrange, LinearMap.finrank_range_of_inj (tensorMap_injective_dev τ hN hb hli),
    finrank_tensorDomain_dev τ n m hfin]

end HRTorus.ZeroModes

end -- noncomputable section
