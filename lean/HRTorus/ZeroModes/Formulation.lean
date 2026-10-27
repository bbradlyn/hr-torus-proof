import HRTorus.ZeroModes.Explicit

/-!
# Lemma C.A completed: the kernel of `H_N` in a sector is the space `V_{n,m}` (`ZeroModes.Formulation`)

Written by Claude Opus 5.5 (an AI model), 2026-10-26. **Statement phase and proof phase (2026-10-26): the
definitions and statements were written first, every theorem that carries content `sorry`, and reviewed against the
paper before any proof; the proof phase (round one) then proved every statement, the reviewed text unchanged. The
proof devices — the declarations named `_dev`, in marked sections — are not statements of the paper. The one-line
derivations (the two equivalences from their directions, the dimension from the linear equivalence, the membership lemma
of `V`) are written out as a machine check that the statements connect.**
The paper: the HR paper, `papers/hr/appendices/C-kernel.tex` — Lemma C.`A` (`kz:lem:A`) in the directions
(1) ⇒ (3) and (3) ⇒ (2) (block F1-lower's `ZeroModes.Canonical` has (2) ⇒ (3) ⇒ (1)), the equivalence (1) ⇔ (2) for the
Lean's `H_N`, and from Lemma C.`B` (`kz:lem:B`) the space `V_{n,m}`.

## The model

* (1) is `Ψ ∈ ker H_N` for the Lean's `H_N` (Definition 2.7); (3) is `b_ν(k)Ψ = 0` for every `ν` and every `k ∈ ℤ`
  (the paper's `n ∈ ℤ_{2L}`; `bcen` has period `2N_φ`, `bcen_add_two_Nφ`); (2) is (C1) and (C2) of the canonical
  component, as `ZeroModes.Canonical` defines them (`C1`, `C2`, `VanishesAlong`).
* (1) ⇒ (3) is Theorem 4.2(c) (`localForm_c`): `⟨Ψ, H_NΨ⟩ = κ³/√(2π) Σ_n Σ_ν ‖b_ν(n)Ψ‖²`, a sum of squares.
* (3) ⇒ (2): (C2) from Lemma C.A3's identity (`lemA3`) with every `β_n = 0`, for the pair coefficients of the first up
  and the first down variable (`comp_cons_cons`, `comp_Bpair`, `Bpair_up_dn`), then for every up–down pair by
  antisymmetry; (C1) by the paper's paragraph on same-spin pairs — the diagonal condition `[D F]_{x_a = x_b} = 0` with
  antisymmetry gives order `≥ 3` along the diagonal (slice-wise, the device `vanishesAlong_of_relDeriv_dev`, the
  converse of F1-lower's `relDeriv_eq_zero_of_C1_dev`), and the multipliers carry it to the lattice translates.
* **`V τ L n m`** is the paper's `V_{n,m}` at level `L` and modular parameter `τ ∈ ℍ`: the submodule of
  `(Fin (n + m) → ℂ) → ℂ` cut out by the shape of a canonical component (`IsCanonShape τ L n m`), (C1) and (C2) — every
  condition is linear; the closure under the linear operations is three proof devices. Through `Ψ ↦ canon T n m Ψ`
  (`canon_shape`, `canon_injective`, `canon_surj`) the kernel in the sector `(n, m)` is linearly equivalent to
  `V (tauT T) T.Nφ n m` (`kerSector_equiv_V`), for every `(n, m)`: the equivalence does not need `n + m = N`.
* Two devices the decomposition of `ZeroModes.Spaces` needs: a function of the shape at a level `L ≥ 1` is jointly
  (Fréchet) differentiable (its expansion in a basis of `Θ_L[0,0]` in each variable), in particular every canonical
  component (`comp_apply`: a finite sum of products of entire functions of one variable); and `V` is finite-dimensional.
-/

open Complex
open scoped Real UpperHalfPlane InnerProductSpace

noncomputable section

namespace HRTorus.ZeroModes

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op)

/-! ## Lemma C.A, (1) ⇒ (3) and (3) ⇒ (2) -/

/-! ### Proof devices for the expansion of a function of the shape (proof phase, round one; not statements of the paper)

F1-lower's `interp1_dev`, `interpN_dev`, `expand_dev` (`ZeroModes.Canonical`) are stated for the orbitals
of a torus; copied here with the orbitals replaced by any finite family `b` whose span holds every slice
(`interp1_gen_dev`, `interpN_gen_dev`, `expand_gen_dev`); a basis of `Θ_L[0,0]` as functions for `L ≥ 1`
(`thetaSpace_basis_dev`, the pattern of F1-lower's `exists_Θ2_pair_dev`); for `L = 0` the space is the constants
(`thetaSpace_zero_const_dev`, Liouville for a doubly periodic entire function). -/

theorem interp1_gen_dev {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → ℂ → ℂ) {z : ι → ℂ}
    (hz : IsUnit (Matrix.of fun a c => b a (z c)).det) {F : ℂ → ℂ}
    (hF : F ∈ Submodule.span ℂ (Set.range b)) (w : ℂ) :
    F w = ∑ c, F (z c) * ∑ a, (Matrix.of fun a c => b a (z c))⁻¹ c a * b a w := by
  set M := Matrix.of fun a c => b a (z c) with hM
  rw [Submodule.mem_span_range_iff_exists_fun] at hF
  obtain ⟨d, rfl⟩ := hF
  have hMW : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hz
  have key : ∀ a' a, ∑ c, M a' c * M⁻¹ c a = if a' = a then 1 else 0 := by
    intro a' a
    have := congrFun (congrFun hMW a') a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc ∑ a, d a * b a w = ∑ a', ∑ a, d a' * (if a' = a then 1 else 0) * b a w := by
        refine Finset.sum_congr rfl fun a' _ => ?_
        simp
    _ = ∑ a', ∑ a, d a' * (∑ c, M a' c * M⁻¹ c a) * b a w := by simp only [key]
    _ = ∑ a', ∑ a, ∑ c, d a' * M a' c * M⁻¹ c a * b a w := by
        refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = ∑ a', ∑ c, ∑ a, d a' * M a' c * M⁻¹ c a * b a w :=
        Finset.sum_congr rfl fun a' _ => Finset.sum_comm
    _ = ∑ c, ∑ a', ∑ a, d a' * M a' c * M⁻¹ c a * b a w := Finset.sum_comm
    _ = ∑ c, (∑ a', d a' * b a' (z c)) * ∑ a, M⁻¹ c a * b a w := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [hM, Matrix.of_apply]
        ring

theorem interpN_gen_dev {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → ℂ → ℂ) {z : ι → ℂ}
    (hz : IsUnit (Matrix.of fun a c => b a (z c)).det) :
    ∀ (N : ℕ) (g : (Fin N → ℂ) → ℂ),
      (∀ (u : Fin N → ℂ) (i : Fin N), (fun w => g (Function.update u i w)) ∈ Submodule.span ℂ (Set.range b)) →
      ∀ u : Fin N → ℂ, g u = ∑ B : Fin N → ι, g (z ∘ B) *
        ∏ i, ∑ a, (Matrix.of fun a c => b a (z c))⁻¹ (B i) a * b a (u i) := by
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
    have h1 : (fun w => g (Fin.cons w (Fin.tail u))) ∈ Submodule.span ℂ (Set.range b) := by
      simpa only [e0] using hg u 0
    have h2 : ∀ (b0 : ι) (v : Fin N → ℂ) (i : Fin N),
        (fun w' => g (Fin.cons (z b0) (Function.update v i w'))) ∈ Submodule.span ℂ (Set.range b) := by
      intro b0 v i
      simpa only [Fin.cons_update] using hg (Fin.cons (z b0) v) i.succ
    conv_lhs => rw [← Fin.cons_self_tail u]
    rw [interp1_gen_dev b hz h1 (u 0), ← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hih := ih (fun v => g (Fin.cons (z c) v)) (h2 c) (Fin.tail u)
    beta_reduce at hih
    rw [hih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun B' _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.comp_cons,
      Fin.tail]
    ring

theorem expand_gen_dev {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → ℂ → ℂ) {z : ι → ℂ}
    (hz : IsUnit (Matrix.of fun a c => b a (z c)).det) (N : ℕ) (g : (Fin N → ℂ) → ℂ)
    (hg : ∀ (u : Fin N → ℂ) (i : Fin N), (fun w => g (Function.update u i w)) ∈ Submodule.span ℂ (Set.range b)) :
    ∃ c : (Fin N → ι) → ℂ, ∀ v, g v = ∑ K, c K * ∏ i, b (K i) (v i) := by
  set W := (Matrix.of fun a c => b a (z c))⁻¹ with hW
  refine ⟨fun K => ∑ B : Fin N → ι, g (z ∘ B) * ∏ i, W (B i) (K i), fun v => ?_⟩
  rw [interpN_gen_dev b hz N g hg v]
  simp only [Fintype.prod_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun B _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem thetaSpace_basis_dev (τ : ℍ) {L : ℕ} (hL : 0 < L) :
    ∃ b : Fin L → ℂ → ℂ, (∀ k, b k ∈ thetaSpace τ 0 0 L) ∧ LinearIndependent ℂ b ∧
      ∀ F ∈ thetaSpace τ 0 0 L, F ∈ Submodule.span ℂ (Set.range b) := by
  have h2 : 0 < Module.finrank ℂ (thetaSpace (τ : ℂ) 0 0 L) := by
    rw [finrank_thetaSpace τ 0 0 hL]
    exact hL
  have : Module.Finite ℂ (thetaSpace (τ : ℂ) 0 0 L) := Module.finite_of_finrank_pos h2
  let B := Module.finBasisOfFinrankEq ℂ (thetaSpace (τ : ℂ) 0 0 L) (finrank_thetaSpace τ 0 0 hL)
  refine ⟨fun k => (B k : ℂ → ℂ), fun k => (B k).2,
    B.linearIndependent.map' (thetaSpace (τ : ℂ) 0 0 L).subtype (Submodule.ker_subtype _), fun F hF => ?_⟩
  have hsum : (⟨F, hF⟩ : thetaSpace (τ : ℂ) 0 0 L) = ∑ k, B.repr ⟨F, hF⟩ k • B k := (B.sum_repr _).symm
  have hF' : F = ∑ k, B.repr ⟨F, hF⟩ k • (B k : ℂ → ℂ) := by
    have := congrArg Subtype.val hsum
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this
  rw [hF']
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

/-- The expansion of a function of the shape at a level `L ≥ 1` in products of basis functions of `Θ_L[0,0]`. -/
theorem expand_shape_dev (τ : ℍ) {L n m : ℕ} (hL : 0 < L) {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : IsCanonShape τ L n m f) :
    ∃ (b : Fin L → ℂ → ℂ) (c : (Fin (n + m) → Fin L) → ℂ), (∀ k, b k ∈ thetaSpace τ 0 0 L) ∧
      ∀ v, f v = ∑ K, c K * ∏ i, b (K i) (v i) := by
  obtain ⟨b, hb, hli, hspan⟩ := thetaSpace_basis_dev τ hL
  obtain ⟨z, hz⟩ := exists_points_det_ne_zero_dev L b hli
  obtain ⟨c, hc⟩ := expand_gen_dev b (isUnit_iff_ne_zero.mpr hz) (n + m) f fun u i => hspan _ (hf.2.1 u i)
  exact ⟨b, c, hb, hc⟩

/-- `Θ_0[0,0]` is the constants: a doubly periodic entire function is bounded, hence constant (Liouville). -/
theorem thetaSpace_zero_const_dev (τ : ℍ) {F : ℂ → ℂ} (hF : F ∈ thetaSpace τ 0 0 0) (z w : ℂ) : F z = F w := by
  obtain ⟨hd, h1, h2⟩ := hF
  have h1' : ∀ U, F (U + 1) = F U := fun U => by simpa using h1 U
  have h2' : ∀ U, F (U + τ) = F U := fun U => by simpa using h2 U
  have hq : ∀ (U : ℂ) (q : ℤ), F (U + q * τ) = F U := by
    intro U q
    induction q with
    | zero => simp
    | succ i ih =>
      rw [show U + ((i + 1 : ℤ) : ℂ) * τ = (U + (i : ℂ) * τ) + τ by push_cast; ring, h2']
      exact_mod_cast ih
    | pred i ih =>
      rw [← h2' (U + ((-(i : ℤ) - 1 : ℤ) : ℂ) * τ)]
      rw [show U + ((-(i : ℤ) - 1 : ℤ) : ℂ) * τ + τ = U + ((-(i : ℤ) : ℤ) : ℂ) * τ by push_cast; ring]
      exact ih
  have hp : ∀ (U : ℂ) (p : ℤ), F (U + p) = F U := by
    intro U p
    induction p with
    | zero => simp
    | succ i ih =>
      rw [show U + ((i + 1 : ℤ) : ℂ) = (U + (i : ℂ)) + 1 by push_cast; ring, h1']
      exact_mod_cast ih
    | pred i ih =>
      rw [← h1' (U + ((-(i : ℤ) - 1 : ℤ) : ℂ))]
      rw [show U + ((-(i : ℤ) - 1 : ℤ) : ℂ) + 1 = U + ((-(i : ℤ) : ℤ) : ℂ) by push_cast; ring]
      exact ih
  have hτ : (τ : ℂ).im ≠ 0 := τ.coe_im_pos.ne'
  set K := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * τ) '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) with hK
  have hKc : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hd.continuous.continuousOn
  have hrep : ∀ x, ∃ y ∈ K, F x = F y := by
    intro x
    set bb := x.im / (τ : ℂ).im with hbb
    set aa := x.re - bb * (τ : ℂ).re with haa
    have hx : x = ((Int.fract aa : ℝ) : ℂ) + ((Int.fract bb : ℝ) : ℂ) * τ + ((⌊aa⌋ : ℤ) : ℂ) +
        ((⌊bb⌋ : ℤ) : ℂ) * τ := by
      have ea := Int.floor_add_fract aa
      have eb := Int.floor_add_fract bb
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.intCast_re, Complex.intCast_im]
        linear_combination -ea - (τ : ℂ).re * eb - haa
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero,
          Complex.intCast_im, Complex.intCast_re, zero_add]
        have : (Int.fract bb + (⌊bb⌋ : ℝ)) * (τ : ℂ).im = x.im := by
          rw [add_comm, eb, hbb, div_mul_cancel₀ _ hτ]
        linear_combination -this
    refine ⟨((Int.fract aa : ℝ) : ℂ) + ((Int.fract bb : ℝ) : ℂ) * τ,
      ⟨(Int.fract aa, Int.fract bb), ⟨⟨Int.fract_nonneg aa, (Int.fract_lt_one aa).le⟩,
        ⟨Int.fract_nonneg bb, (Int.fract_lt_one bb).le⟩⟩, rfl⟩, ?_⟩
    rw [hx, hq, hp]
  have hbdd : Bornology.IsBounded (Set.range F) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hrep x
    rw [hxy]
    exact hC y hy
  exact hd.apply_eq_apply_of_bounded hbdd z w

/-! ### Proof devices for the diagonal (proof phase, round one; not statements of the paper)

A finite sum `h(z, w) = Σ_K P_K B_K(z) C_K(w)` of products of entire functions, antisymmetric, with `∂_z h = ∂_w h` on the
diagonal, vanishes with `∂_z h` and `∂_z² h` on the diagonal (`diag_order3_dev`; the mixed partials are explicit for such
a sum); the order of vanishing of a slice in `Θ_L[0,0]` is carried along the lattice (`vanish3_translate_dev`, by the
Leibniz rule `iteratedDeriv_mul` and the multipliers, as in F1-lower's `vanishes3_core_dev`). -/

theorem hasDerivAt_sumL_dev {κ : Type*} [Fintype κ] (P : κ → ℂ) {D : κ → ℂ → ℂ} (E : κ → ℂ → ℂ)
    (hD : ∀ K, Differentiable ℂ (D K)) (y x : ℂ) :
    HasDerivAt (fun z => ∑ K, P K * D K z * E K y) (∑ K, P K * deriv (D K) x * E K y) x :=
  HasDerivAt.fun_sum fun K _ => ((hD K x).hasDerivAt.const_mul (P K)).mul_const (E K y)

theorem hasDerivAt_sumR_dev {κ : Type*} [Fintype κ] (P : κ → ℂ) (D : κ → ℂ → ℂ) {E : κ → ℂ → ℂ}
    (hE : ∀ K, Differentiable ℂ (E K)) (y x : ℂ) :
    HasDerivAt (fun z => ∑ K, P K * D K y * E K z) (∑ K, P K * D K y * deriv (E K) x) x :=
  HasDerivAt.fun_sum fun K _ => (hE K x).hasDerivAt.const_mul (P K * D K y)

theorem hasDerivAt_sumD_dev {κ : Type*} [Fintype κ] (P : κ → ℂ) {D E : κ → ℂ → ℂ}
    (hD : ∀ K, Differentiable ℂ (D K)) (hE : ∀ K, Differentiable ℂ (E K)) (x : ℂ) :
    HasDerivAt (fun z => ∑ K, P K * D K z * E K z)
      (∑ K, (P K * deriv (D K) x * E K x + P K * D K x * deriv (E K) x)) x :=
  HasDerivAt.fun_sum fun K _ => by
    have := ((hD K x).hasDerivAt.const_mul (P K)).mul (hE K x).hasDerivAt
    convert this using 1

theorem diag_order3_dev {κ : Type*} [Fintype κ] (P : κ → ℂ) (B C : κ → ℂ → ℂ)
    (hB : ∀ K, Differentiable ℂ (B K)) (hC : ∀ K, Differentiable ℂ (C K))
    (hanti : ∀ z w, ∑ K, P K * B K z * C K w = -∑ K, P K * B K w * C K z)
    (hdiag : ∀ w, ∑ K, P K * deriv (B K) w * C K w = ∑ K, P K * B K w * deriv (C K) w) (w : ℂ) :
    ∀ j < 3, iteratedDeriv j (fun z => ∑ K, P K * B K z * C K w) w = 0 := by
  have hB' : ∀ K, Differentiable ℂ (deriv (B K)) := fun K => (hB K).deriv
  have hC' : ∀ K, Differentiable ℂ (deriv (C K)) := fun K => (hC K).deriv
  -- first derivatives in `z` of the antisymmetry, at every point
  have hfirst : ∀ v z, ∑ K, P K * deriv (B K) z * C K v = -∑ K, P K * B K v * deriv (C K) z := by
    intro v z
    have e : (fun z => ∑ K, P K * B K z * C K v) = fun z => -∑ K, P K * B K v * C K z :=
      funext fun z => hanti z v
    have d1 := hasDerivAt_sumL_dev P C hB v z
    rw [e] at d1
    exact d1.unique (hasDerivAt_sumR_dev P B hC v z).neg
  have h1 : ∀ v, ∑ K, P K * deriv (B K) v * C K v = 0 := by
    intro v
    have a := hfirst v v
    have b := hdiag v
    linear_combination (a + b) / 2
  have h2 : ∀ v, ∑ K, P K * B K v * deriv (C K) v = 0 := fun v => by rw [← hdiag v, h1 v]
  -- second derivatives
  have hsecond : ∀ v, ∑ K, P K * deriv (deriv (B K)) v * C K v = -∑ K, P K * B K v * deriv (deriv (C K)) v := by
    intro v
    have e : (fun z => ∑ K, P K * deriv (B K) z * C K v) = fun z => -∑ K, P K * B K v * deriv (C K) z :=
      funext fun z => hfirst v z
    have d1 := hasDerivAt_sumL_dev P C hB' v v
    rw [e] at d1
    exact d1.unique (hasDerivAt_sumR_dev P B hC' v v).neg
  have hD1 : ∀ v, ∑ K, (P K * deriv (deriv (B K)) v * C K v + P K * deriv (B K) v * deriv (C K) v) = 0 := by
    intro v
    have d := hasDerivAt_sumD_dev P hB' hC v
    rw [show (fun z => ∑ K, P K * deriv (B K) z * C K z) = fun _ => (0 : ℂ) from funext h1] at d
    exact d.unique (hasDerivAt_const v 0)
  have hD2 : ∀ v, ∑ K, (P K * deriv (B K) v * deriv (C K) v + P K * B K v * deriv (deriv (C K)) v) = 0 := by
    intro v
    have d := hasDerivAt_sumD_dev P hB hC' v
    rw [show (fun z => ∑ K, P K * B K z * deriv (C K) z) = fun _ => (0 : ℂ) from funext h2] at d
    exact d.unique (hasDerivAt_const v 0)
  have h11 : ∑ K, P K * deriv (deriv (B K)) w * C K w = 0 := by
    have a := hsecond w
    have b := hD1 w
    have c := hD2 w
    rw [Finset.sum_add_distrib] at b c
    linear_combination (b - c + a) / 2
  intro j hj
  interval_cases j
  · simp only [iteratedDeriv_zero]
    have := hanti w w
    linear_combination this / 2
  · rw [iteratedDeriv_one, (hasDerivAt_sumL_dev P C hB w w).deriv]
    exact h1 w
  · rw [iteratedDeriv_succ, iteratedDeriv_one]
    have e : deriv (fun z => ∑ K, P K * B K z * C K w) = fun x => ∑ K, P K * deriv (B K) x * C K w :=
      funext fun x => (hasDerivAt_sumL_dev P C hB w x).deriv
    rw [e, (hasDerivAt_sumL_dev P C hB' w w).deriv]
    exact h11

theorem vanish3_mul_dev {M G : ℂ → ℂ} (hM : Differentiable ℂ M) (hG : Differentiable ℂ G) {w : ℂ}
    (h : ∀ j < 3, iteratedDeriv j G w = 0) : ∀ j < 3, iteratedDeriv j (fun z => M z * G z) w = 0 := by
  intro j hj
  have e : (fun z => M z * G z) = M * G := rfl
  rw [e, iteratedDeriv_mul (hM.contDiff.contDiffAt) (hG.contDiff.contDiffAt)]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : j - i < 3 := by
    have := Finset.mem_range.1 hi
    omega
  rw [h (j - i) hi', mul_zero]

theorem vanish3_translate_dev (τ : ℍ) {L : ℕ} {F : ℂ → ℂ} (hF : F ∈ thetaSpace τ 0 0 L) {w : ℂ}
    (h0 : ∀ j < 3, iteratedDeriv j F w = 0) {l : ℂ} (hl : l ∈ Λu τ) : ∀ j < 3, iteratedDeriv j F (w + l) = 0 := by
  obtain ⟨hd, h1, h2⟩ := hF
  have h1' : (fun z => F (z + 1)) = F := funext fun U => by simpa using h1 U
  have h2' : ∀ U, F (U + τ) = cexp (-π * I * (L : ℂ) * (2 * U + τ)) * F U := fun U => by simpa using h2 U
  have hMd : Differentiable ℂ fun z : ℂ => cexp (-π * I * (L : ℂ) * (2 * z + τ)) := by fun_prop
  have hMd' : Differentiable ℂ fun z : ℂ => (cexp (-π * I * (L : ℂ) * (2 * z + τ)))⁻¹ := by
    have : (fun z : ℂ => (cexp (-π * I * (L : ℂ) * (2 * z + τ)))⁻¹) =
        fun z : ℂ => cexp (-(-π * I * (L : ℂ) * (2 * z + τ))) := funext fun z => (Complex.exp_neg _).symm
    rw [this]
    fun_prop
  have hFτ : (fun z => F (z + τ)) = fun z => cexp (-π * I * (L : ℂ) * (2 * z + τ)) * F z := funext h2'
  have hFτ' : F = fun z => (cexp (-π * I * (L : ℂ) * (2 * z + τ)))⁻¹ * F (z + τ) := by
    funext z
    rw [h2', ← mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]
  have hd2 : Differentiable ℂ fun z => F (z + τ) := hd.comp (differentiable_id.add_const _)
  -- the property `Z v` (value and first two derivatives zero at `v`) under `v ↦ v ± 1`, `v ↦ v ± τ`
  set Z : ℂ → Prop := fun v => ∀ j < 3, iteratedDeriv j F v = 0 with hZ
  have hZ1 : ∀ v, Z (v + 1) ↔ Z v := by
    intro v
    have e : ∀ j, iteratedDeriv j F (v + 1) = iteratedDeriv j F v := by
      intro j
      have := congrFun (iteratedDeriv_comp_add_const (n := j) (f := F) (s := 1)) v
      rw [h1'] at this
      exact this.symm
    simp only [hZ, e]
  have hZτ : ∀ v, Z (v + τ) ↔ Z v := by
    intro v
    have e : ∀ j, iteratedDeriv j F (v + τ) = iteratedDeriv j (fun z => F (z + τ)) v := by
      intro j
      exact (congrFun (iteratedDeriv_comp_add_const (n := j) (f := F) (s := (τ : ℂ))) v).symm
    constructor
    · intro h
      have h' : ∀ j < 3, iteratedDeriv j (fun z => F (z + τ)) v = 0 := fun j hj => by rw [← e]; exact h j hj
      intro j hj
      rw [hFτ']
      exact vanish3_mul_dev hMd' hd2 h' j hj
    · intro h j hj
      rw [e, hFτ]
      exact vanish3_mul_dev hMd hd h j hj
  have hq : ∀ q : ℤ, Z (w + q * τ) := by
    intro q
    induction q with
    | zero => simpa using h0
    | succ i ih =>
      have := (hZτ _).2 ih
      rwa [show w + ((i : ℤ) : ℂ) * τ + τ = w + ((i + 1 : ℤ) : ℂ) * τ by push_cast; ring] at this
    | pred i ih =>
      refine (hZτ _).1 ?_
      rwa [show w + ((-(i : ℤ) - 1 : ℤ) : ℂ) * τ + τ = w + ((-(i : ℤ) : ℤ) : ℂ) * τ by push_cast; ring]
  have hpq : ∀ p q : ℤ, Z (w + (p + q * τ)) := by
    intro p q
    induction p with
    | zero => simpa using hq q
    | succ i ih =>
      have := (hZ1 _).2 ih
      rwa [show w + (((i : ℤ) : ℂ) + q * τ) + 1 = w + (((i + 1 : ℤ) : ℂ) + q * τ) by push_cast; ring] at this
    | pred i ih =>
      refine (hZ1 _).1 ?_
      rwa [show w + (((-(i : ℤ) - 1 : ℤ) : ℂ) + q * τ) + 1 = w + (((-(i : ℤ) : ℤ) : ℂ) + q * τ) by
        push_cast; ring]
  obtain ⟨p, q, rfl⟩ := hl
  exact hpq p q

theorem swap_fix_dev {N : ℕ} {s t : Fin N} (v : Fin N → ℂ) (hv : v s = v t) : v ∘ Equiv.swap s t = v := by
  funext i
  simp only [Function.comp_apply]
  rcases eq_or_ne i s with rfl | his
  · rw [Equiv.swap_apply_left, hv]
  · rcases eq_or_ne i t with rfl | hit
    · rw [Equiv.swap_apply_right, hv]
    · rw [Equiv.swap_apply_of_ne_of_ne his hit]

/-- The proof of `vanishesAlong_of_relDeriv_dev`, placed ahead of Lemma C.A, (3) ⇒ (2), which uses it. -/
theorem vanishesAlong_of_relDeriv_core_dev (τ : ℍ) {L n m : ℕ} {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : IsCanonShape τ L n m f) (_hd : Differentiable ℂ f) {s t : Fin (n + m)} (hst : s ≠ t)
    (hss : SameSpecies n s t) (hdiag : ∀ u : Fin (n + m) → ℂ, u s = u t → relDeriv f s t u = 0) :
    VanishesAlong τ f s t 3 := by
  rcases Nat.eq_zero_or_pos L with hL0 | hL
  · -- `L = 0`: every slice is constant, and zero by antisymmetry
    subst hL0
    intro u l _ j hj
    have hzero : f (Function.update u s (u t)) = 0 := by
      have hv : (Function.update u s (u t)) s = (Function.update u s (u t)) t := by
        rw [Function.update_self, Function.update_of_ne hst.symm]
      have h := hf.2.2 s t hst hss (Function.update u s (u t))
      rw [swap_fix_dev _ hv] at h
      linear_combination h / 2
    have e : (fun z => f (Function.update u s z)) = fun _ => 0 := funext fun z => by
      rw [thetaSpace_zero_const_dev τ (hf.2.1 u s) z (u t), hzero]
    rw [e, iteratedDeriv_const]
    simp
  · -- `L ≥ 1`: the expansion in products of basis functions of `Θ_L[0,0]`
    obtain ⟨b, c, hb, hc⟩ := expand_shape_dev τ hL hf
    have hbd : ∀ k, Differentiable ℂ (b k) := fun k => (hb k).1
    intro u l hl
    set R : Finset (Fin (n + m)) := (Finset.univ.erase s).erase t with hR
    set P : (Fin (n + m) → Fin L) → ℂ := fun K => c K * ∏ i ∈ R, b (K i) (u i) with hP
    have hsplit : ∀ z w, f (Function.update (Function.update u s z) t w) =
        ∑ K, P K * b (K s) z * b (K t) w := by
      intro z w
      rw [hc]
      refine Finset.sum_congr rfl fun K _ => ?_
      have ht : t ∈ Finset.univ.erase s := Finset.mem_erase.mpr ⟨Ne.symm hst, Finset.mem_univ t⟩
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s), ← Finset.mul_prod_erase _ _ ht, ← hR]
      have hrest : ∏ i ∈ R, b (K i) (Function.update (Function.update u s z) t w i) =
          ∏ i ∈ R, b (K i) (u i) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hit : i ≠ t := Finset.ne_of_mem_erase hi
        have his : i ≠ s := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
        rw [Function.update_of_ne hit, Function.update_of_ne his]
      rw [hrest, Function.update_of_ne hst, Function.update_self, Function.update_self]
      simp only [hP]
      ring
    have hanti2 : ∀ z w, ∑ K, P K * b (K s) z * b (K t) w = -∑ K, P K * b (K s) w * b (K t) z := by
      intro z w
      rw [← hsplit, ← hsplit]
      have h := hf.2.2 s t hst hss (Function.update (Function.update u s w) t z)
      rw [← h]
      congr 1
      funext i
      simp only [Function.comp_apply]
      rcases eq_or_ne i s with rfl | his
      · rw [Equiv.swap_apply_left, Function.update_self, Function.update_of_ne hst, Function.update_self]
      · rcases eq_or_ne i t with rfl | hit
        · rw [Equiv.swap_apply_right, Function.update_self, Function.update_of_ne hst, Function.update_self]
        · rw [Equiv.swap_apply_of_ne_of_ne his hit, Function.update_of_ne hit, Function.update_of_ne his,
            Function.update_of_ne hit, Function.update_of_ne his]
    have hdiag2 : ∀ w, ∑ K, P K * deriv (b (K s)) w * b (K t) w =
        ∑ K, P K * b (K s) w * deriv (b (K t)) w := by
      intro w
      set v := Function.update (Function.update u s w) t w with hv
      have hvs : v s = w := by rw [hv, Function.update_of_ne hst, Function.update_self]
      have hvt : v t = w := by rw [hv, Function.update_self]
      have h := hdiag v (by rw [hvs, hvt])
      unfold relDeriv at h
      have e1 : (fun z => f (Function.update v s z)) = fun z => ∑ K, P K * b (K s) z * b (K t) w := by
        funext z
        rw [← hsplit, hv, Function.update_comm hst, Function.update_idem, Function.update_comm hst.symm]
      have e2 : (fun z => f (Function.update v t z)) = fun z => ∑ K, P K * b (K s) w * b (K t) z := by
        funext z
        rw [← hsplit, hv, Function.update_idem]
      rw [e1, e2, hvs, hvt, (hasDerivAt_sumL_dev P (fun K => b (K t)) (fun K => hbd (K s)) w w).deriv,
        (hasDerivAt_sumR_dev P (fun K => b (K s)) (fun K => hbd (K t)) w w).deriv] at h
      linear_combination h
    have hdiag3 := diag_order3_dev P (fun K => b (K s)) (fun K => b (K t)) (fun K => hbd (K s))
      (fun K => hbd (K t)) hanti2 hdiag2 (u t)
    have hslice : (fun z => f (Function.update u s z)) = fun z => ∑ K, P K * b (K s) z * b (K t) (u t) := by
      funext z
      have e : Function.update (Function.update u s z) t (u t) = Function.update u s z := by
        conv_lhs => rw [← Function.update_of_ne hst.symm z u]
        exact Function.update_eq_self t _
      rw [← hsplit, e]
    have hmem : (fun z => ∑ K, P K * b (K s) z * b (K t) (u t)) ∈ thetaSpace τ 0 0 L := by
      rw [← hslice]
      exact hf.2.1 u s
    intro j hj
    rw [hslice]
    exact vanish3_translate_dev τ hmem hdiag3 hl j hj

/-- The proof of `canon_differentiable_dev`, placed ahead of Lemma C.A, (3) ⇒ (2), which uses it. -/
theorem canon_differentiable_core_dev (T : Torus) (n m : ℕ) (Ψ : FockSpace T) :
    Differentiable ℂ (canon T n m Ψ) := by
  have e : (canon T n m Ψ : (Fin (n + m) → ℂ) → ℂ) = fun u => ∑ J : Fin (n + m) → ZMod T.Nφ,
      ⟪creVec T (canonSpins n m) J, Ψ⟫_ℂ * ∏ i, orbHol T (J i) (u i) :=
    funext (comp_apply T (canonSpins n m) Ψ)
  rw [e]
  exact Differentiable.fun_sum fun J _ => (differentiable_const _).mul
    (differentiable_finsetProd_dev _ fun i _ => (orbHol_differentiable T (J i)).comp (differentiable_apply i))

/-! ### Proof devices for Lemma C.A, (3) ⇒ (2) (proof phase, round one; not statements of the paper)

The converse of F1-lower's `Bpair_eq_zero_core_dev` and `Bpair_eq_zero_of_relDeriv_dev` (`ZeroModes.Canonical`),
whose text they copy with the implication reversed: if `B_k^{σ₀σ₁}Ψ = 0` for every `k`, the diagonal relative
derivative of the component in the first two variables vanishes (the pair coefficients' `β_k` are the components of
`B_k Ψ`, `comp_Bpair`, and Lemma C.A3's series, `lemA3`, is zero); any pair `s ≠ t` is brought to the first two places by
the same permutation (`comp_perm`). -/

theorem relDeriv_zero_core_dev (T : Torus) {N : ℕ} (σ : Fin (N + 2) → Spin) {Ψ : FockSpace T}
    (hB : ∀ k : ℤ, toCLM T (Bpair T (σ 0) (σ 1) k) Ψ = 0) (W : ℂ) (w : Fin N → ℂ) :
    relDeriv (comp T σ Ψ) 0 1 (Fin.cons W (Fin.cons W w : Fin (N + 1) → ℂ)) = 0 := by
  let ψ : ZMod T.Nφ → ZMod T.Nφ → ℂ := fun a b =>
    comp T (fun i : Fin N => σ i.succ.succ) (toCLM T (cjs T b (σ 1) * cjs T a (σ 0)) Ψ) w
  have hpair : ∀ z₀ z₁ : ℂ,
      pairFun T ψ z₀ z₁ = comp T σ Ψ (Fin.cons z₀ (Fin.cons z₁ w : Fin (N + 1) → ℂ)) := by
    intro z₀ z₁
    rw [comp_cons_cons]
    unfold pairFun
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hβ : ∀ k : ℤ, betaC T ψ k = 0 := by
    intro k
    have h := congrArg (fun Φ => comp T (fun i : Fin N => σ i.succ.succ) Φ w) (hB k)
    simp only [map_zero, Pi.zero_apply] at h
    rw [comp_Bpair] at h
    exact h
  unfold relDeriv
  have e0 : ∀ z : ℂ, Function.update (Fin.cons W (Fin.cons W w : Fin (N + 1) → ℂ) : Fin (N + 2) → ℂ) 0 z =
      Fin.cons z (Fin.cons W w : Fin (N + 1) → ℂ) := fun z => by
    rw [Fin.update_cons_zero]
  have e1 : ∀ z : ℂ, Function.update (Fin.cons W (Fin.cons W w : Fin (N + 1) → ℂ) : Fin (N + 2) → ℂ) 1 z =
      Fin.cons W (Fin.cons z w : Fin (N + 1) → ℂ) := fun z => by
    rw [← Fin.succ_zero_eq_one', ← Fin.cons_update, Fin.update_cons_zero]
  simp only [e0, e1, Fin.cons_zero, Fin.cons_one]
  simp only [← hpair]
  rw [lemA3]
  simp [hβ]

theorem relDeriv_zero_of_Bpair_dev (T : Torus) {N' : ℕ} (σc : Fin N' → Spin) {Ψ : FockSpace T} (s t : Fin N')
    (hst : s ≠ t) (hB : ∀ k : ℤ, toCLM T (Bpair T (σc s) (σc t) k) Ψ = 0) (u : Fin N' → ℂ) (hu : u s = u t) :
    relDeriv (comp T σc Ψ) s t u = 0 := by
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
  set v : Fin (N + 2) → ℂ := u ∘ ρ with hv
  have hvρ : v ∘ ρ.symm = u := by
    funext i
    simp [hv]
  have hv0 : v 0 = u s := by
    rw [hv, Function.comp_apply, hρ0]
  have hv1 : v 1 = u s := by
    rw [hv, Function.comp_apply, hρ1, hu]
  have hvcons : v = Fin.cons (u s) (Fin.cons (u s) (fun i : Fin N => v i.succ.succ) : Fin (N + 1) → ℂ) := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => rfl) i) i
    · exact hv0
    · exact hv1
  have hB' : ∀ k : ℤ, toCLM T (Bpair T ((σc ∘ ρ) 0) ((σc ∘ ρ) 1) k) Ψ = 0 := fun k => by
    simpa only [Function.comp_apply, hρ0, hρ1] using hB k
  have hcore := relDeriv_zero_core_dev T (σc ∘ ρ) hB' (u s) (fun i : Fin N => v i.succ.succ)
  rw [← hvcons] at hcore
  unfold relDeriv at hcore ⊢
  rw [hderiv v 0, hderiv v 1, ← mul_sub, hρ0, hρ1, hvρ, hv0, hv1] at hcore
  have hsgn : ((Equiv.Perm.sign ρ : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (Units.ne_zero _)
  rw [← hu]
  exact (mul_eq_zero.1 hcore).resolve_left hsgn

/-- **Lemma C.A, (1) ⇒ (3)**: "`(1)$\iff$($\kzP_{ij}\Psi=0$ for all $i<j$), because $H$ is a sum of positive operators`"
— for the Lean's `H_N`, by Theorem 4.2(c) (`localForm_c`, `H_N = κ³/√(2π) Σ_n Σ_ν b_ν(n)* b_ν(n)`): a vector of the
kernel is annihilated by every pair operator, "`$B_n^\mu\Psi=0$ for all $n\in\Z_{2L}$ and $\mu\in\{+1,0,-1\}$.`" (for every
`k ∈ ℤ`, by the period `2N_φ` of `bcen`). No sector is needed. -/
theorem lemA_HN_conv (T : Torus) {Ψ : FockSpace T}
    (hΨ : Ψ ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)))
    (ν : Triplet) (k : ℤ) : toCLM T (bcen T ν k) Ψ = 0 := by
  have hH : toCLM T (HN T) Ψ = 0 := by
    rw [LinearMap.mem_ker] at hΨ
    exact hΨ
  -- `⟨Ψ, H_N Ψ⟩ = κ³/√(2π) Σ_n Σ_ν ‖b_ν(n) Ψ‖²` vanishes, so every term does
  have hsq : ∀ A : FockOp T,
      ⟪Ψ, toCLM T (Matrix.conjTranspose A * A) Ψ⟫_ℂ = ((‖toCLM T A Ψ‖ ^ 2 : ℝ) : ℂ) := by
    intro A
    have e : toCLM T (Matrix.conjTranspose A * A) Ψ = toCLM T (Matrix.conjTranspose A) (toCLM T A Ψ) := by
      simp only [toCLM, map_mul, mul_apply_eq_comp]
    rw [e, ← inner_toCLM_dev, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hlin : ∀ (c : ℂ) (X : ℕ → Triplet → FockOp T),
      toCLM T (c • ∑ n ∈ Finset.range (2 * T.Nφ), ∑ ν' : Triplet, X n ν') Ψ =
        c • ∑ n ∈ Finset.range (2 * T.Nφ), ∑ ν' : Triplet, toCLM T (X n ν') Ψ := by
    intro c X
    simp only [toCLM, map_smul, map_sum, smul_apply, FunLike.coe_sum, Finset.sum_apply]
  have hsum : ∑ n ∈ Finset.range (2 * T.Nφ), ∑ ν' : Triplet, ‖toCLM T (bcen T ν' (n : ℤ)) Ψ‖ ^ 2 = 0 := by
    have h0 : ⟪Ψ, toCLM T (HN T) Ψ⟫_ℂ = 0 := by
      rw [hH, inner_zero_right]
    rw [localForm_c, hlin] at h0
    simp only [inner_smul_right, inner_sum, hsq] at h0
    have hc : ((T.κ ^ 3 / Real.sqrt (2 * π) : ℝ) : ℂ) ≠ 0 := by
      have hκ : 0 < T.κ := by
        unfold Torus.κ
        exact div_pos (by positivity) T.Ly_pos
      exact_mod_cast (div_pos (pow_pos hκ 3) (Real.sqrt_pos.mpr (by positivity))).ne'
    have h1 := (mul_eq_zero.1 h0).resolve_left hc
    exact_mod_cast h1
  have hzero : ∀ n ∈ Finset.range (2 * T.Nφ), ∀ ν' : Triplet, toCLM T (bcen T ν' (n : ℤ)) Ψ = 0 := by
    intro n hn ν'
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun (n' : ℕ) _ => Finset.sum_nonneg fun (ν'' : Triplet) _ =>
      sq_nonneg ‖toCLM T (bcen T ν'' (n' : ℤ)) Ψ‖).1 hsum n hn
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun (ν'' : Triplet) _ =>
      sq_nonneg ‖toCLM T (bcen T ν'' (n : ℤ)) Ψ‖).1 h1 ν' (Finset.mem_univ _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  -- every `k ∈ ℤ`, by the period `2N_φ`
  have hper : ∀ (r q : ℤ), bcen T ν (r + 2 * (T.Nφ : ℤ) * q) = bcen T ν r := by
    intro r q
    induction q with
    | zero => simp
    | succ i ih =>
      rw [show r + 2 * (T.Nφ : ℤ) * ((i : ℤ) + 1) = (r + 2 * (T.Nφ : ℤ) * (i : ℤ)) + 2 * (T.Nφ : ℤ) by ring,
        bcen_add_two_Nφ, ih]
    | pred i ih =>
      rw [← bcen_add_two_Nφ T ν (r + 2 * (T.Nφ : ℤ) * (-(i : ℤ) - 1)),
        show r + 2 * (T.Nφ : ℤ) * (-(i : ℤ) - 1) + 2 * (T.Nφ : ℤ) = r + 2 * (T.Nφ : ℤ) * (-(i : ℤ)) by ring, ih]
  have hNφ : (0 : ℤ) < 2 * (T.Nφ : ℤ) := by
    have := T.Nφ_pos
    omega
  have hr0 : 0 ≤ k % (2 * (T.Nφ : ℤ)) := Int.emod_nonneg _ hNφ.ne'
  have hr1 : k % (2 * (T.Nφ : ℤ)) < 2 * (T.Nφ : ℤ) := Int.emod_lt_of_pos _ hNφ
  have hk : k = k % (2 * (T.Nφ : ℤ)) + 2 * (T.Nφ : ℤ) * (k / (2 * (T.Nφ : ℤ))) :=
    (Int.emod_add_mul_ediv k _).symm
  rw [hk, hper, ← Int.toNat_of_nonneg hr0]
  exact hzero _ (Finset.mem_range.mpr (by omega)) ν

/-- **Lemma C.A, (3) ⇒ (2)**: if every `b_ν(k)` annihilates `Ψ` (any such `Ψ`, in any sector or none), its canonical
component in `(n, m)` satisfies (C1) and (C2). (C2) is "`\emph{Up--down pairs.} The condition is (C2) verbatim.`" with Lemma C.A3's identity
"`(\kzD f)(Z,Z)=i\kappa\sum_{n\in\Z}e^{i\kappa nZ+i\pi\tau n^2/(2L)}\,\beta_n(\psi)`" at `β_n = 0` (`lemA3`), the pair
coefficients being "`So $F_{ab}=\pm$ (canonical component of $c_{b\downarrow}c_{a\uparrow}\Psi$), with a sign that depends only on $(n,m)$.`";
(C1) is the paragraph on same-spin pairs: "`So the condition says $G=(x_a-x_b)G'$ with $G'$ antisymmetric, hence $G'=(x_a-x_b)G''$: order $\ge3$ along the covering diagonal.`"
and "`That map multiplies $F$ by the nonvanishing entire boundary-condition multiplier, so vanishing orders agree on all components. This is (C1).`" -/
theorem lemA_bcen_conv (T : Torus) (n m : ℕ) {Ψ : FockSpace T}
    (hb : ∀ (ν : Triplet) (k : ℤ), toCLM T (bcen T ν k) Ψ = 0) :
    C1 (tauT T) n m (canon T n m Ψ) ∧ C2 n m (canon T n m Ψ) := by
  have hBall : ∀ (σ σ' : Spin) (k : ℤ), toCLM T (Bpair T σ σ' k) Ψ = 0 := by
    intro σ σ' k
    cases σ <;> cases σ'
    · rw [Bpair_up_up]
      exact hb .plus k
    · rw [Bpair_up_dn]
      have h := hb .zero k
      simp only [toCLM] at h ⊢
      rw [map_smul, smul_apply, h, smul_zero]
    · rw [Bpair_dn_up, Bpair_up_dn]
      have h := hb .zero k
      simp only [toCLM] at h ⊢
      rw [map_smul, smul_apply, h, smul_zero]
    · rw [Bpair_dn_dn]
      exact hb .minus k
  have hdiag : ∀ s t : Fin (n + m), s ≠ t → ∀ u : Fin (n + m) → ℂ, u s = u t →
      relDeriv (canon T n m Ψ) s t u = 0 :=
    fun s t hst u hu => relDeriv_zero_of_Bpair_dev T (canonSpins n m) s t hst (fun k => hBall _ _ k) u hu
  refine ⟨fun s t hst hss => ?_, fun s t hs ht u hu => hdiag s t (fun h => by rw [h] at hs; omega) u hu⟩
  exact vanishesAlong_of_relDeriv_core_dev (tauT T) (canon_shape T n m Ψ) (canon_differentiable_core_dev T n m Ψ)
    (ne_of_lt hst) hss fun u hu => hdiag s t (ne_of_lt hst) u hu

/-! ## Lemma C.A, the equivalences (one-line derivations from the four directions) -/

/-- **Lemma C.A, (1) ⇔ (2)**: "`Let $\Psi$ have $N_\uparrow=n$, $N_\downarrow=m$ and canonical component $F$. The following are equivalent.`"
— for the Lean's `H_N`: a vector of the sector `(n, m)` lies in the kernel iff its canonical component satisfies (C1)
and (C2) (`lemA_HN_conv`, `lemA_bcen_conv`, and F1-lower's `lemA_HN`). -/
theorem lemA_iff (T : Torus) (nn : SectorLabel T) {n m : ℕ} (hn : (nn.1 : ℕ) = n) (hm : (nn.2 : ℕ) = m)
    (Ψ : FockSpace T) :
    Ψ ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) ⊓
        sector T nn ↔
      Ψ ∈ sector T nn ∧ C1 (tauT T) n m (canon T n m Ψ) ∧ C2 n m (canon T n m Ψ) := by
  rw [Submodule.mem_inf]
  exact ⟨fun h => ⟨h.2, lemA_bcen_conv T n m (lemA_HN_conv T h.1)⟩,
    fun h => ⟨lemA_HN T nn hn hm h.1 h.2.1 h.2.2, h.1⟩⟩

/-- **Lemma C.A, (1) ⇔ (3)**: "`$B_n^\mu\Psi=0$ for all $n\in\Z_{2L}$ and $\mu\in\{+1,0,-1\}$.`" — for a vector of the sector
`(n, m)`, membership in the kernel of `H_N` is the vanishing of every `b_ν(k)Ψ`. -/
theorem lemA_iff_bcen (T : Torus) (nn : SectorLabel T) {n m : ℕ} (hn : (nn.1 : ℕ) = n) (hm : (nn.2 : ℕ) = m)
    (Ψ : FockSpace T) :
    Ψ ∈ LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) ⊓
        sector T nn ↔
      Ψ ∈ sector T nn ∧ ∀ (ν : Triplet) (k : ℤ), toCLM T (bcen T ν k) Ψ = 0 := by
  rw [Submodule.mem_inf]
  refine ⟨fun h => ⟨h.2, lemA_HN_conv T h.1⟩, fun h => ?_⟩
  obtain ⟨h1, h2⟩ := lemA_bcen_conv T n m h.2
  exact ⟨lemA_HN T nn hn hm h.1 h1 h2, h.1⟩

/-! ## The space `V_{n,m}` -/

/-! ### Proof devices for the closure of `V` and `Gnum` (proof phase, round one; not statements of the paper): the
Osgood class, the slice-wise vanishing, (C1) and (C2) are closed under the linear operations -/

theorem isOsgood_zero_dev {N : ℕ} : IsOsgood (0 : (Fin N → ℂ) → ℂ) :=
  ⟨continuous_const, fun _ _ => differentiable_const 0⟩

theorem isOsgood_add_dev {N : ℕ} {f g : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) (hg : IsOsgood g) :
    IsOsgood (f + g) :=
  ⟨hf.1.add hg.1, fun u i => (hf.2 u i).add (hg.2 u i)⟩

theorem isOsgood_smul_dev {N : ℕ} (c : ℂ) {f : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) : IsOsgood (c • f) :=
  ⟨hf.1.const_smul c, fun u i => (hf.2 u i).const_smul c⟩

theorem vanishesAlong_zero_dev (τ : ℍ) {N : ℕ} (s t : Fin N) (k : ℕ) :
    VanishesAlong τ (0 : (Fin N → ℂ) → ℂ) s t k := by
  intro u l _ j _
  simp

theorem vanishesAlong_add_dev (τ : ℍ) {N : ℕ} {f g : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) (hg : IsOsgood g)
    {s t : Fin N} {k : ℕ} (h1 : VanishesAlong τ f s t k) (h2 : VanishesAlong τ g s t k) :
    VanishesAlong τ (f + g) s t k := by
  intro u l hl j hj
  have e : (fun z => (f + g) (Function.update u s z)) =
      (fun z => f (Function.update u s z)) + fun z => g (Function.update u s z) := rfl
  rw [e, iteratedDeriv_add ((hf.2 u s).contDiff.contDiffAt) ((hg.2 u s).contDiff.contDiffAt),
    h1 u l hl j hj, h2 u l hl j hj, add_zero]

theorem vanishesAlong_smul_dev (τ : ℍ) {N : ℕ} (c : ℂ) {f : (Fin N → ℂ) → ℂ} {s t : Fin N} {k : ℕ}
    (h1 : VanishesAlong τ f s t k) : VanishesAlong τ (c • f) s t k := by
  intro u l hl j hj
  have e : (fun z => (c • f) (Function.update u s z)) = c • fun z => f (Function.update u s z) := rfl
  rw [e, iteratedDeriv_const_smul_field, h1 u l hl j hj, smul_zero]

theorem relDeriv_add_dev {N : ℕ} {f g : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) (hg : IsOsgood g) (s t : Fin N)
    (u : Fin N → ℂ) : relDeriv (f + g) s t u = relDeriv f s t u + relDeriv g s t u := by
  unfold relDeriv
  have e : ∀ i : Fin N, (fun z => (f + g) (Function.update u i z)) =
      fun z => f (Function.update u i z) + g (Function.update u i z) := fun i => rfl
  rw [e s, e t, deriv_fun_add ((hf.2 u s) _) ((hg.2 u s) _), deriv_fun_add ((hf.2 u t) _) ((hg.2 u t) _)]
  ring

theorem relDeriv_smul_dev {N : ℕ} (c : ℂ) (f : (Fin N → ℂ) → ℂ) (s t : Fin N) (u : Fin N → ℂ) :
    relDeriv (c • f) s t u = c * relDeriv f s t u := by
  unfold relDeriv
  have e : ∀ i : Fin N, (fun z => (c • f) (Function.update u i z)) = fun z => c * f (Function.update u i z) :=
    fun i => rfl
  rw [e s, e t, deriv_const_mul_field, deriv_const_mul_field]
  ring

theorem C1_zero_dev (τ : ℍ) (n m : ℕ) : C1 τ n m 0 := fun s t _ _ => vanishesAlong_zero_dev τ s t 3

theorem C1_add_dev (τ : ℍ) {n m : ℕ} {f g : (Fin (n + m) → ℂ) → ℂ} (hf : IsOsgood f) (hg : IsOsgood g)
    (h1 : C1 τ n m f) (h2 : C1 τ n m g) : C1 τ n m (f + g) :=
  fun s t hst hss => vanishesAlong_add_dev τ hf hg (h1 s t hst hss) (h2 s t hst hss)

theorem C1_smul_dev (τ : ℍ) {n m : ℕ} (c : ℂ) {f : (Fin (n + m) → ℂ) → ℂ} (h1 : C1 τ n m f) : C1 τ n m (c • f) :=
  fun s t hst hss => vanishesAlong_smul_dev τ c (h1 s t hst hss)

theorem C2_zero_dev (n m : ℕ) : C2 n m 0 := by
  intro s t _ _ u _
  simp [relDeriv]

theorem C2_add_dev {n m : ℕ} {f g : (Fin (n + m) → ℂ) → ℂ} (hf : IsOsgood f) (hg : IsOsgood g) (h1 : C2 n m f)
    (h2 : C2 n m g) : C2 n m (f + g) := fun s t hs ht u hu => by
  rw [relDeriv_add_dev hf hg, h1 s t hs ht u hu, h2 s t hs ht u hu, add_zero]

theorem C2_smul_dev {n m : ℕ} (c : ℂ) {f : (Fin (n + m) → ℂ) → ℂ} (h1 : C2 n m f) : C2 n m (c • f) :=
  fun s t hs ht u hu => by rw [relDeriv_smul_dev, h1 s t hs ht u hu, mul_zero]

/-! ### Proof devices for the space `V_{n,m}` (statement phase; not statements of the paper): its closure under the
linear operations — the shape, (C1) and (C2) are linear conditions -/

theorem V_zero_mem_dev (τ : ℍ) (L n m : ℕ) :
    IsCanonShape τ L n m 0 ∧ C1 τ n m 0 ∧ C2 n m 0 := by
  refine ⟨⟨isOsgood_zero_dev, fun u i => (thetaSpace τ 0 0 L).zero_mem, fun s t _ _ u => by simp⟩,
    C1_zero_dev τ n m, C2_zero_dev n m⟩

theorem V_add_mem_dev (τ : ℍ) (L n m : ℕ) {f g : (Fin (n + m) → ℂ) → ℂ}
    (hf : IsCanonShape τ L n m f ∧ C1 τ n m f ∧ C2 n m f) (hg : IsCanonShape τ L n m g ∧ C1 τ n m g ∧ C2 n m g) :
    IsCanonShape τ L n m (f + g) ∧ C1 τ n m (f + g) ∧ C2 n m (f + g) := by
  obtain ⟨⟨hfo, hfs, hfa⟩, hf1, hf2⟩ := hf
  obtain ⟨⟨hgo, hgs, hga⟩, hg1, hg2⟩ := hg
  refine ⟨⟨isOsgood_add_dev hfo hgo, fun u i => (thetaSpace τ 0 0 L).add_mem (hfs u i) (hgs u i),
    fun s t hst hss u => ?_⟩, C1_add_dev τ hfo hgo hf1 hg1, C2_add_dev hfo hgo hf2 hg2⟩
  simp only [Pi.add_apply, hfa s t hst hss u, hga s t hst hss u, neg_add]

theorem V_smul_mem_dev (τ : ℍ) (L n m : ℕ) (c : ℂ) {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : IsCanonShape τ L n m f ∧ C1 τ n m f ∧ C2 n m f) :
    IsCanonShape τ L n m (c • f) ∧ C1 τ n m (c • f) ∧ C2 n m (c • f) := by
  obtain ⟨⟨hfo, hfs, hfa⟩, hf1, hf2⟩ := hf
  refine ⟨⟨isOsgood_smul_dev c hfo, fun u i => (thetaSpace τ 0 0 L).smul_mem c (hfs u i),
    fun s t hst hss u => ?_⟩, C1_smul_dev τ c hf1, C2_smul_dev c hf2⟩
  simp only [Pi.smul_apply, smul_eq_mul, hfa s t hst hss u, mul_neg]

/-- **Lemma C.B**: "`let $V_{n,m}$ be the space of canonical components satisfying \textup{(C1)}, \textup{(C2)}, i.e.\ $\ker H|_{n,m}$ by Lemma~\ref{kz:lem:A}`"
— at level `L` and modular parameter `τ`: the functions of the shape of a canonical component of the sector `(n, m)`
(`IsCanonShape τ L n m`: in the Osgood class, each variable in `Θ_L[0,0]`, antisymmetric in the `x`'s and in the `y`'s)
that satisfy (C1) and (C2). -/
def V (τ : ℍ) (L n m : ℕ) : Submodule ℂ ((Fin (n + m) → ℂ) → ℂ) where
  carrier := {f | IsCanonShape τ L n m f ∧ C1 τ n m f ∧ C2 n m f}
  zero_mem' := V_zero_mem_dev τ L n m
  add_mem' := fun hf hg => V_add_mem_dev τ L n m hf hg
  smul_mem' := fun c _ hf => V_smul_mem_dev τ L n m c hf

/-- Membership in `V` (by definition). -/
theorem mem_V {τ : ℍ} {L n m : ℕ} {f : (Fin (n + m) → ℂ) → ℂ} :
    f ∈ V τ L n m ↔ IsCanonShape τ L n m f ∧ C1 τ n m f ∧ C2 n m f :=
  Iff.rfl

/-- **Lemma C.B** with **Lemma C.A**: "`let $V_{n,m}$ be the space of canonical components satisfying \textup{(C1)}, \textup{(C2)}, i.e.\ $\ker H|_{n,m}$ by Lemma~\ref{kz:lem:A}`"
— the kernel of `H_N` in the sector `(n, m)` is linearly equivalent to `V (tauT T) T.Nφ n m` through the canonical
component (`lemA_iff`, `canon_shape`, `canon_injective`, `canon_surj`). -/
theorem kerSector_equiv_V (T : Torus) (nn : SectorLabel T) {n m : ℕ} (hn : (nn.1 : ℕ) = n) (hm : (nn.2 : ℕ) = m) :
    ∃ e : ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) ⊓
        sector T nn) ≃ₗ[ℂ] ↥(V (tauT T) T.Nφ n m),
      ∀ Ψ, (e Ψ : (Fin (n + m) → ℂ) → ℂ) = canon T n m (Ψ : FockSpace T) := by
  have hmemV : ∀ Ψ : ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
      (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T nn), canon T n m (Ψ : FockSpace T) ∈ V (tauT T) T.Nφ n m := by
    intro Ψ
    have h := Submodule.mem_inf.mp Ψ.2
    obtain ⟨h1, h2⟩ := lemA_bcen_conv T n m (lemA_HN_conv T h.1)
    exact ⟨canon_shape T n m Ψ, h1, h2⟩
  let φ : ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ)) (n := Conf (ZMod T.Nφ)) (HN T)) ⊓
      sector T nn) →ₗ[ℂ] ↥(V (tauT T) T.Nφ n m) :=
    { toFun := fun Ψ => ⟨canon T n m (Ψ : FockSpace T), hmemV Ψ⟩
      map_add' := fun Ψ Φ => by
        apply Subtype.ext
        simp only [Submodule.coe_add, map_add]
      map_smul' := fun c Ψ => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply] }
  have hinj : Function.Injective φ := by
    intro Ψ Φ h
    have h' : canon T n m ((Ψ : FockSpace T) - Φ) = 0 := by
      have := congrArg Subtype.val h
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [map_sub, this, sub_self]
    have hs : (Ψ : FockSpace T) - Φ ∈ sector T nn :=
      Submodule.sub_mem _ (Submodule.mem_inf.mp Ψ.2).2 (Submodule.mem_inf.mp Φ.2).2
    exact Subtype.ext (sub_eq_zero.mp (canon_injective T nn hn hm hs h'))
  have hsurj : Function.Surjective φ := by
    intro f
    obtain ⟨Ψ, hΨ, hcan⟩ := canon_surj T nn hn hm f.2.1
    have hc1 : C1 (tauT T) n m (canon T n m Ψ) := by
      rw [hcan]
      exact f.2.2.1
    have hc2 : C2 n m (canon T n m Ψ) := by
      rw [hcan]
      exact f.2.2.2
    refine ⟨⟨Ψ, Submodule.mem_inf.mpr ⟨lemA_HN T nn hn hm hΨ hc1 hc2, hΨ⟩⟩, Subtype.ext ?_⟩
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    exact hcan
  have hbij : Function.Bijective φ := ⟨hinj, hsurj⟩
  refine ⟨LinearEquiv.ofBijective φ hbij, fun Ψ => ?_⟩
  rw [LinearEquiv.ofBijective_apply]
  try rfl

/-- **Lemma C.B**: the first step of "`In particular $\dim\ker H|_{n,m}=2\sum_{\varepsilon\in\mu_N^2}\dim\kzG(n,m;\varepsilon)$`",
`dim ker H|_{n,m} = dim V_{n,m}` (from `kerSector_equiv_V`). -/
theorem finrank_ker_eq_finrank_V (T : Torus) (nn : SectorLabel T) {n m : ℕ} (hn : (nn.1 : ℕ) = n)
    (hm : (nn.2 : ℕ) = m) :
    Module.finrank ℂ ↥(LinearMap.ker (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Conf (ZMod T.Nφ))
        (n := Conf (ZMod T.Nφ)) (HN T)) ⊓ sector T nn) =
      Module.finrank ℂ ↥(V (tauT T) T.Nφ n m) := by
  obtain ⟨e, -⟩ := kerSector_equiv_V T nn hn hm
  exact e.finrank_eq

/-! ### Proof device for Lemma C.A, (3) ⇒ (2) (statement phase; not a statement of the paper): the converse of
F1-lower's `relDeriv_eq_zero_of_C1_dev` -/

/-- The paragraph on same-spin pairs, slice-wise: a jointly differentiable function of the shape whose diagonal condition
`[D_{st} f]_{u_s = u_t} = 0` holds for a same-species pair vanishes to order `≥ 3` along `{u_s − u_t ∈ Λ_u}` (on the
diagonal: the value and `∂_s f` vanish by antisymmetry and the diagonal condition, `∂_s² f` by the diagonal condition
differentiated along the diagonal together with antisymmetry; at the lattice translates: the multipliers of
`Θ_L[0,0]`). -/
theorem vanishesAlong_of_relDeriv_dev (τ : ℍ) {L n m : ℕ} {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : IsCanonShape τ L n m f) (hd : Differentiable ℂ f) {s t : Fin (n + m)} (hst : s ≠ t)
    (hss : SameSpecies n s t) (hdiag : ∀ u : Fin (n + m) → ℂ, u s = u t → relDeriv f s t u = 0) :
    VanishesAlong τ f s t 3 := by
  exact vanishesAlong_of_relDeriv_core_dev τ hf hd hst hss hdiag

/-! ### Proof devices for `ZeroModes.Spaces` (statement phase; not statements of the paper): joint differentiability
and finite dimension -/

/-- A function of the shape of a canonical component at a level `L ≥ 1` is jointly (Fréchet) differentiable: each
variable lies in the `L`-dimensional `Θ_L[0,0]` (`finrank_thetaSpace`), so the function is a finite sum of products of
basis functions of one variable (interpolation at points where the basis matrix is invertible, as `canon_surj`'s
`expand_dev` does for the orbitals). -/
theorem differentiable_of_isCanonShape_dev (τ : ℍ) {L n m : ℕ} (hL : 0 < L) {f : (Fin (n + m) → ℂ) → ℂ}
    (hf : IsCanonShape τ L n m f) : Differentiable ℂ f := by
  obtain ⟨b, c, hb, hc⟩ := expand_shape_dev τ hL hf
  rw [show f = fun v => ∑ K, c K * ∏ i, b (K i) (v i) from funext hc]
  exact Differentiable.fun_sum fun K _ => (differentiable_const _).mul
    (differentiable_finsetProd_dev _ fun i _ => (hb (K i)).1.comp (differentiable_apply i))

/-- "`$e^{Y^2/2}\psi$ is an entire function of $z$ for every $f\in\hN$`" — a canonical component is jointly differentiable
(`comp_apply`: a finite sum of products of entire functions of one variable). -/
theorem canon_differentiable_dev (T : Torus) (n m : ℕ) (Ψ : FockSpace T) : Differentiable ℂ (canon T n m Ψ) := by
  exact canon_differentiable_core_dev T n m Ψ

/-- `V_{n,m}` is finite-dimensional at every level `L ≥ 1` (the expansion of `differentiable_of_isCanonShape_dev`: `V`
lies in the span of the products of `N` basis functions of `Θ_L[0,0]`). -/
theorem V_finiteDimensional_dev (τ : ℍ) {L : ℕ} (hL : 0 < L) (n m : ℕ) : FiniteDimensional ℂ (V τ L n m) := by
  obtain ⟨b, hb, hli, hspan⟩ := thetaSpace_basis_dev τ hL
  obtain ⟨z, hz⟩ := exists_points_det_ne_zero_dev L b hli
  let P : (Fin (n + m) → Fin L) → (Fin (n + m) → ℂ) → ℂ := fun K v => ∏ i, b (K i) (v i)
  have hle : V τ L n m ≤ Submodule.span ℂ (Set.range P) := by
    intro f hf
    obtain ⟨c, hc⟩ := expand_gen_dev b (isUnit_iff_ne_zero.mpr hz) (n + m) f fun u i => hspan _ (hf.1.2.1 u i)
    have e : f = ∑ K, c K • P K := by
      funext v
      rw [hc v]
      simp [P, Finset.sum_apply, smul_eq_mul]
    rw [e]
    exact Submodule.sum_mem _ fun K _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self K))
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range P)) :=
    Module.Finite.span_of_finite ℂ (Set.finite_range P)
  exact Submodule.finiteDimensional_of_le hle

end HRTorus.ZeroModes

end -- noncomputable section
