import HRTorus.IndexCore.Determinant
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The finite-dimensional core of the HR index theorem: the assembly

Written by Claude Opus 5.5 (an AI model), 2026-10-23. The main theorem `HRTorus.IndexCore.index_core` was stated
in `Statement.lean` first and proved there by `sorry`. Its statement was then moved
here **verbatim** (the text between `theorem` and `:= by` is byte-identical), and it is proved
below from the lemmas of the other modules.

The proof is the paper's (Theorem 6.18 from Lemma 6.17(iii)–(iv)) with the quantitative cases:
* `p = 0`: then `|Tr(P T₋)| ≤ p ‖T₋‖ = 0`, and `n = 0`;
* `ε (648π² + 8) ≤ 1` (that is, `ε ≤ ε_* = 1/(2 c_𝓜)`): Lemmas 6.14–6.17 give
  `dist(Tr(P T₋), ℤ) ≤ p (393 M + 17) √ε` (`SepBounds.index_core_small`), with `n` an integer
  nearest to `Tr(P T̃)`;
* `ε (648π² + 8) > 1`: `Tr(P T₋)` is real, within `1/2` of `round(Tr(P T₋))`, and
  `1/2 ≤ 400 p (M + 1) √ε` because `√ε > 1/81`.
Both regimes close with any constant `C ≥ 400` in place of `1000` (`SepBounds.index_core_aux`);
the statement's `1000 p (M + 1)` is the case `C = 1000`.
-/

open scoped InnerProductSpace ComplexConjugate Real
open Complex (I)

noncomputable section
open Classical

namespace HRTorus.IndexCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-- `√a ≤ c √ε` from `a ≤ c² ε`. -/
theorem sqrt_le_mul_sqrt {a c ε : ℝ} (hc : 0 ≤ c) (h : a ≤ c ^ 2 * ε) : √a ≤ c * √ε :=
  calc √a ≤ √(c ^ 2 * ε) := Real.sqrt_le_sqrt h
    _ = c * √ε := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

namespace Setting

variable {S : Setting E} {ε M : ℝ}

/-- **The core for `ε ≤ ε_*`**, with the constant this proof gives:
`dist(Tr(P T₋), ℤ) ≤ p (393 M + 17) √ε` when `ε (648π² + 8) ≤ 1`. -/
theorem SepBounds.index_core_small (h : S.SepBounds ε) (hU2 : ‖⁅S.U, S.P⁆‖ ≤ ε)
    (hU4 : ‖NormedSpace.exp ((2 * π * I) • (S.Q + S.Tplus)) - 1‖ ≤ ε)
    (clu_M : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π), ‖⁅S.Qf (S.Mplus φ), S.Mminus φ⁆‖ ≤ ε)
    (clu_M_adj : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖⁅S.Qf (star (S.Mplus φ)), star (S.Mminus φ)⁆‖ ≤ ε)
    (clu_O : ‖⁅S.Qf S.Oplus, S.Ominus⁆‖ ≤ ε)
    (clu_O_adj : ‖⁅S.Qf (star S.Oplus), star S.Ominus⁆‖ ≤ ε)
    (norm_Tminus : ‖S.Tminus‖ ≤ M) (norm_Kminus : ‖S.Kminus‖ ≤ M)
    (hsmall : ε * (648 * π ^ 2 + 8) ≤ 1) :
    ∃ n : ℤ, ‖trc (S.P * S.Tminus) - n‖ ≤ S.p * (393 * M + 17) * √ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hU2
  have hM : 0 ≤ M := (norm_nonneg _).trans norm_Tminus
  have hπ0 : 0 < π := Real.pi_pos
  have hπ1 : π < 3.15 := Real.pi_lt_d2
  have hπ3 : 3 < π := Real.pi_gt_three
  have hπ2 : π ^ 2 ≤ 9.9225 := by nlinarith
  have hπ2' : 9 ≤ π ^ 2 := by nlinarith
  have hπc : π ^ 3 ≤ 31.26 := by nlinarith [mul_le_mul_of_nonneg_left hπ2 hπ0.le]
  have hε1 : ε ≤ 1 / 5776 := by nlinarith [mul_le_mul_of_nonneg_left hπ2' hε]
  set t := √ε with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htt : t * t = ε := Real.mul_self_sqrt hε
  have ht76 : t ≤ 1 / 76 := by nlinarith
  have hεt : ε ≤ t / 76 := by nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht76)]
  have hcM : cM * ε ≤ 1 / 2 := by rw [cM]; nlinarith
  have hcO : cO * ε ≤ 1 / 2 := by rw [cO]; nlinarith [mul_nonneg (sq_nonneg π) hε]
  -- Corollary 6.15: the two commutators with `P`
  have s1 : ∀ u ∈ Set.Icc (0 : ℝ) (2 * π), ‖⁅S.Mminus u, S.P⁆‖ ≤ 81 * t := fun u hu =>
    (h.norm_lie_Mminus_P_le hU2 clu_M clu_M_adj hcM hu).trans
      (sqrt_le_mul_sqrt (by norm_num) (by rw [cM]; nlinarith [mul_le_mul_of_nonneg_left hπ2 hε]))
  have s2 : ‖⁅S.P, S.Ominus⁆‖ ≤ 30 * t := by
    rw [norm_lie_comm]
    exact (h.norm_lie_Ominus_P_le clu_O clu_O_adj hcO).trans
      (sqrt_le_mul_sqrt (by norm_num) (by rw [cO]; nlinarith [mul_le_mul_of_nonneg_left hπ2 hε]))
  -- Lemma 6.16: the size of `ℰ` on `[0, 2π]`, and the comparison at `2π`
  have hT : ‖S.Ttilde‖ ≤ 3 * M := norm_Ttilde_le norm_Tminus norm_Kminus
  have hB1 := h.norm_lie_QbarMinus_B_le
  have hB2 := h.norm_lie_B_Ttilde_le
  have hE : ∀ u ∈ Set.Icc (0 : ℝ) (2 * π), ‖S.Ec u‖ ≤
      81 * t * (3 * M) + (4 * π ^ 2 * (4 * ε) * (3 * M) + 2 * π * (9 * ε)) := by
    intro u hu
    have hu0 := hu.1
    have hu1 := hu.2
    have hu2 : u ^ 2 ≤ 4 * π ^ 2 := by nlinarith
    have hua : |u| ≤ 2 * π := by rw [abs_of_nonneg hu0]; exact hu1
    refine (S.norm_Ec_le u).trans (add_le_add ?_ (add_le_add ?_ ?_))
    · exact mul_le_mul (s1 u hu) hT (norm_nonneg _) (by positivity)
    · exact mul_le_mul (mul_le_mul hu2 hB1 (norm_nonneg _) (by positivity)) hT (norm_nonneg _)
        (by positivity)
    · exact mul_le_mul hua hB2 (norm_nonneg _) (by positivity)
  have hZY := S.norm_Zc_sub_Yc_le_mul (by positivity : (0 : ℝ) ≤ 2 * π) hE
  -- Lemma 6.17(i)–(iv)
  have hMm := h.norm_Mminus_two_pi_sub_le hU4
  have hdet := S.norm_detP_Zc_two_pi_sub_one_le
  have hUP : ‖⁅S.P, S.U⁆‖ ≤ ε := by rw [norm_lie_comm]; exact hU2
  have hexp := S.norm_cexp_trc_Ttilde_sub_one_le
  obtain ⟨n, hn⟩ := S.exists_int_norm_trc_Ttilde_sub_le
  have hiv := S.norm_trc_Ttilde_sub_trc_Tminus_le
  refine ⟨n, ?_⟩
  have hp0 : (0 : ℝ) ≤ S.p := Nat.cast_nonneg _
  set CE := 81 * t * (3 * M) + (4 * π ^ 2 * (4 * ε) * (3 * M) + 2 * π * (9 * ε)) with hCE
  have k1 : ‖trc (S.P * S.Tminus) - trc (S.P * S.Ttilde)‖ ≤ S.p * (2 * ε * M) := by
    rw [norm_sub_rev]
    refine hiv.trans ?_
    have := mul_le_mul hU2 norm_Kminus (norm_nonneg _) hε
    calc 2 * (S.p : ℝ) * ‖⁅S.U, S.P⁆‖ * ‖S.Kminus‖ = 2 * S.p * (‖⁅S.U, S.P⁆‖ * ‖S.Kminus‖) := by
          ring
      _ ≤ 2 * S.p * (ε * M) := by gcongr
      _ = S.p * (2 * ε * M) := by ring
  have k2 : ‖detP S.P (S.Zc (2 * π)) - 1‖ ≤
      S.p * ((24 * π ^ 2 + 1) * ε + 3 * ε + 2 * (30 * t)) := by
    refine hdet.trans (mul_le_mul_of_nonneg_left ?_ hp0)
    linarith
  have k3 : ‖trc (S.P * S.Ttilde) - n‖ ≤ (S.p * (CE * (2 * π)) +
      S.p * ((24 * π ^ 2 + 1) * ε + 3 * ε + 2 * (30 * t))) / 4 := by
    refine hn.trans ?_
    have : ‖Complex.exp (2 * π * I * trc (S.P * S.Ttilde)) - 1‖ ≤ S.p * (CE * (2 * π)) +
        S.p * ((24 * π ^ 2 + 1) * ε + 3 * ε + 2 * (30 * t)) := by
      refine hexp.trans (add_le_add (mul_le_mul_of_nonneg_left ?_ hp0) k2)
      rw [norm_sub_rev]; exact hZY
    linarith
  -- the arithmetic
  have key : 2 * ε * M + (CE * (2 * π) + ((24 * π ^ 2 + 1) * ε + 3 * ε + 2 * (30 * t))) / 4 ≤
      (393 * M + 17) * t := by
    have hMt : 0 ≤ M * t := mul_nonneg hM ht0
    have a1 : π * (M * t) ≤ 3.15 * (M * t) := mul_le_mul_of_nonneg_right hπ1.le hMt
    have a4 : M * ε ≤ M * (t / 76) := mul_le_mul_of_nonneg_left hεt hM
    have a2 : π ^ 3 * (M * ε) ≤ 31.26 * (M * (t / 76)) :=
      (mul_le_mul_of_nonneg_right hπc (mul_nonneg hM hε)).trans
        (mul_le_mul_of_nonneg_left a4 (by norm_num))
    have a3 : π ^ 2 * ε ≤ 9.9225 * (t / 76) :=
      (mul_le_mul_of_nonneg_right hπ2 hε).trans (mul_le_mul_of_nonneg_left hεt (by norm_num))
    have e : 2 * ε * M + (CE * (2 * π) + ((24 * π ^ 2 + 1) * ε + 3 * ε + 2 * (30 * t))) / 4 =
        2 * (M * ε) + (486 * (π * (M * t)) + 96 * (π ^ 3 * (M * ε)) + 60 * (π ^ 2 * ε) +
          4 * ε + 60 * t) / 4 := by
      rw [hCE]; ring
    rw [e]
    linarith [a1, a2, a3, a4, hεt, hMt, ht0]
  calc ‖trc (S.P * S.Tminus) - n‖
      ≤ ‖trc (S.P * S.Tminus) - trc (S.P * S.Ttilde)‖ + ‖trc (S.P * S.Ttilde) - n‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ S.p * (2 * ε * M) + (S.p * (CE * (2 * π)) +
        S.p * ((24 * π ^ 2 + 1) * ε + 3 * ε + 2 * (30 * t))) / 4 := add_le_add k1 k3
    _ = S.p * (2 * ε * M +
        (CE * (2 * π) + ((24 * π ^ 2 + 1) * ε + 3 * ε + 2 * (30 * t))) / 4) := by ring
    _ ≤ S.p * ((393 * M + 17) * t) := mul_le_mul_of_nonneg_left key hp0
    _ = S.p * (393 * M + 17) * t := by ring

/-- **The core with any constant `C ≥ 400`**: `dist(Tr(P T₋), ℤ) ≤ C p (M + 1) √ε`. -/
theorem SepBounds.index_core_aux (h : S.SepBounds ε) (hU2 : ‖⁅S.U, S.P⁆‖ ≤ ε)
    (hU4 : ‖NormedSpace.exp ((2 * π * I) • (S.Q + S.Tplus)) - 1‖ ≤ ε)
    (clu_M : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π), ‖⁅S.Qf (S.Mplus φ), S.Mminus φ⁆‖ ≤ ε)
    (clu_M_adj : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖⁅S.Qf (star (S.Mplus φ)), star (S.Mminus φ)⁆‖ ≤ ε)
    (clu_O : ‖⁅S.Qf S.Oplus, S.Ominus⁆‖ ≤ ε)
    (clu_O_adj : ‖⁅S.Qf (star S.Oplus), star S.Ominus⁆‖ ≤ ε)
    (norm_Tminus : ‖S.Tminus‖ ≤ M) (norm_Kminus : ‖S.Kminus‖ ≤ M) {C : ℝ} (hC : 400 ≤ C) :
    ∃ n : ℤ, ‖trc (S.P * S.Tminus) - n‖ ≤ C * S.p * (M + 1) * √ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hU2
  have hM : 0 ≤ M := (norm_nonneg _).trans norm_Tminus
  rcases Nat.eq_zero_or_pos S.p with hp | hp
  · -- `p = 0`: `|Tr(P T₋)| ≤ p ‖T₋‖ = 0`
    refine ⟨0, ?_⟩
    have h0 : ‖trc (S.P * S.Tminus)‖ ≤ (S.p : ℝ) * ‖S.Tminus‖ :=
      norm_trc_P_mul_le S.isStarProjection_P S.Tminus
    simp only [hp, Nat.cast_zero, zero_mul, mul_zero, Int.cast_zero, sub_zero] at h0 ⊢
    exact h0
  have hp1 : (1 : ℝ) ≤ S.p := Nat.one_le_cast.mpr hp
  by_cases hsmall : ε * (648 * π ^ 2 + 8) ≤ 1
  · -- `ε ≤ ε_*`
    obtain ⟨n, hn⟩ := h.index_core_small hU2 hU4 clu_M clu_M_adj clu_O clu_O_adj norm_Tminus
      norm_Kminus hsmall
    refine ⟨n, hn.trans ?_⟩
    have hC' : 393 * M + 17 ≤ C * (M + 1) := by nlinarith
    calc (S.p : ℝ) * (393 * M + 17) * √ε ≤ S.p * (C * (M + 1)) * √ε := by gcongr
      _ = C * S.p * (M + 1) * √ε := by ring
  · -- `ε > ε_*`: `Tr(P T₋)` is real and within `1/2` of an integer
    have hlarge : 1 < ε * (648 * π ^ 2 + 8) := not_le.mp hsmall
    have hre := trc_P_mul_eq_re S.isStarProjection_P S.Tminus_sa
    refine ⟨round (trc (S.P * S.Tminus)).re, ?_⟩
    rw [hre, ← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_sub_round _).trans ?_
    have hπ0 : 0 < π := Real.pi_pos
    have hπ1 : π < 3.15 := Real.pi_lt_d2
    have hπ2 : π ^ 2 ≤ 9.9225 := by nlinarith
    have hε81 : (1 / 81 : ℝ) ^ 2 ≤ ε := by nlinarith [mul_le_mul_of_nonneg_left hπ2 hε]
    have ht81 : 1 / 81 ≤ √ε :=
      calc (1 : ℝ) / 81 = √((1 / 81) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ √ε := Real.sqrt_le_sqrt hε81
    calc (1 : ℝ) / 2 ≤ 400 * 1 * (0 + 1) * (1 / 81) := by norm_num
      _ ≤ C * S.p * (M + 1) * √ε := by gcongr

end Setting

/-- **The finite-dimensional core of the HR index theorem (Theorem 6.18), quantitatively.**
Each hypothesis `… ≤ ε` is one input that Section 6 shows to be `O(N^{-∞})`; `M` bounds the two
operator norms the argument uses. Conclusion: `Tr(P T_-)` is within `C(p, M) √ε` of an integer.

The statement as first written in `Statement.lean`, moved here verbatim, now proved. -/
theorem index_core (S : Setting E) (ε M : ℝ)
    /- (U2) of Assumption 6.4. -/
    (hU2 : ‖⁅S.U, S.P⁆‖ ≤ ε)
    /- (U4) of Assumption 6.4, the `+` half (the only half the `T_-` statement uses, in Step 2
    of the proof of Lemma 6.17(i)). -/
    (hU4 : ‖NormedSpace.exp ((2 * π * I) • (S.Q + S.Tplus)) - 1‖ ≤ ε)
    /- Lemma 6.13(ii), the separated pairs, class 1: `[A, Q_m]`, `A ∈ {K_-, K^U_-, K_+, K^U_+}`,
    and for a general `U` also `[T_±, Q_m]`. -/
    (sep_Kminus_Qmid : ‖⁅S.Kminus, S.Qmid⁆‖ ≤ ε)
    (sep_KUminus_Qmid : ‖⁅S.KUminus, S.Qmid⁆‖ ≤ ε)
    (sep_Kplus_Qmid : ‖⁅S.Kplus, S.Qmid⁆‖ ≤ ε)
    (sep_KUplus_Qmid : ‖⁅S.KUplus, S.Qmid⁆‖ ≤ ε)
    (sep_Tminus_Qmid : ‖⁅S.Tminus, S.Qmid⁆‖ ≤ ε)
    (sep_Tplus_Qmid : ‖⁅S.Tplus, S.Qmid⁆‖ ≤ ε)
    /- Lemma 6.13(ii), class 2: `(Q_-, B_+)`, `B_+ ∈ {K_+, K^U_+}`, `(A_-, Q_+)`,
    `A_- ∈ {K_-, K^U_-}`, and for a general `U` also `(Q_-, T_+)`, `(T_-, Q_+)`. -/
    (sep_Qminus_Kplus : ‖⁅S.Qminus, S.Kplus⁆‖ ≤ ε)
    (sep_Qminus_KUplus : ‖⁅S.Qminus, S.KUplus⁆‖ ≤ ε)
    (sep_Kminus_Qplus : ‖⁅S.Kminus, S.Qplus⁆‖ ≤ ε)
    (sep_KUminus_Qplus : ‖⁅S.KUminus, S.Qplus⁆‖ ≤ ε)
    (sep_Qminus_Tplus : ‖⁅S.Qminus, S.Tplus⁆‖ ≤ ε)
    (sep_Tminus_Qplus : ‖⁅S.Tminus, S.Qplus⁆‖ ≤ ε)
    /- Lemma 6.13(ii), class 3: `(A_-, B_+)`, `A_- ∈ {T_-, K_-, K^U_-}`,
    `B_+ ∈ {T_+, K_+, K^U_+}` (all nine for a general `U`). -/
    (sep_Tminus_Tplus : ‖⁅S.Tminus, S.Tplus⁆‖ ≤ ε)
    (sep_Tminus_Kplus : ‖⁅S.Tminus, S.Kplus⁆‖ ≤ ε)
    (sep_Tminus_KUplus : ‖⁅S.Tminus, S.KUplus⁆‖ ≤ ε)
    (sep_Kminus_Tplus : ‖⁅S.Kminus, S.Tplus⁆‖ ≤ ε)
    (sep_Kminus_Kplus : ‖⁅S.Kminus, S.Kplus⁆‖ ≤ ε)
    (sep_Kminus_KUplus : ‖⁅S.Kminus, S.KUplus⁆‖ ≤ ε)
    (sep_KUminus_Tplus : ‖⁅S.KUminus, S.Tplus⁆‖ ≤ ε)
    (sep_KUminus_Kplus : ‖⁅S.KUminus, S.Kplus⁆‖ ≤ ε)
    (sep_KUminus_KUplus : ‖⁅S.KUminus, S.KUplus⁆‖ ≤ ε)
    /- Corollary 6.15 (through Lemma 6.14 and Proposition 6.10(ii)): the clustering commutators
    `ε_1 ≤ ‖[\mathcal Q(V_+), V_-]‖`, `ε_2 ≤ ‖[\mathcal Q(V_+^*), V_-^*]‖` for
    `V_± = \mathcal M_±(φ)`, uniformly in `φ ∈ [0, 2π]`, and for `V_± = e^{2πi \overline Q_±}`. -/
    (clu_M : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π), ‖⁅S.Qf (S.Mplus φ), S.Mminus φ⁆‖ ≤ ε)
    (clu_M_adj : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖⁅S.Qf (star (S.Mplus φ)), star (S.Mminus φ)⁆‖ ≤ ε)
    (clu_O : ‖⁅S.Qf S.Oplus, S.Ominus⁆‖ ≤ ε)
    (clu_O_adj : ‖⁅S.Qf (star S.Oplus), star S.Ominus⁆‖ ≤ ε)
    /- The norms (Lemma 6.12's table): only `‖T_-‖` and `‖K_-‖` enter the constants. -/
    (norm_Tminus : ‖S.Tminus‖ ≤ M)
    (norm_Kminus : ‖S.Kminus‖ ≤ M) :
    ∃ n : ℤ, ‖LinearMap.trace ℂ E (S.P * S.Tminus : E →L[ℂ] E).toLinearMap - n‖ ≤
      indexConst S.p M * √ε := by
  have h : S.SepBounds ε := ⟨sep_Kminus_Qmid, sep_KUminus_Qmid, sep_Kplus_Qmid, sep_KUplus_Qmid,
    sep_Tminus_Qmid, sep_Tplus_Qmid, sep_Qminus_Kplus, sep_Qminus_KUplus, sep_Kminus_Qplus,
    sep_KUminus_Qplus, sep_Qminus_Tplus, sep_Tminus_Qplus, sep_Tminus_Tplus, sep_Tminus_Kplus,
    sep_Tminus_KUplus, sep_Kminus_Tplus, sep_Kminus_Kplus, sep_Kminus_KUplus, sep_KUminus_Tplus,
    sep_KUminus_Kplus, sep_KUminus_KUplus⟩
  obtain ⟨n, hn⟩ := h.index_core_aux hU2 hU4 clu_M clu_M_adj clu_O clu_O_adj norm_Tminus
    norm_Kminus (C := 1000) (by norm_num)
  exact ⟨n, hn⟩

/-- The tightened form (tightened after the proof): the same hypotheses give the bound
with `400 p (M + 1)` in place of `1000 p (M + 1)`. -/
theorem index_core_400 (S : Setting E) (ε M : ℝ) (h : S.SepBounds ε)
    (hU2 : ‖⁅S.U, S.P⁆‖ ≤ ε)
    (hU4 : ‖NormedSpace.exp ((2 * π * I) • (S.Q + S.Tplus)) - 1‖ ≤ ε)
    (clu_M : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π), ‖⁅S.Qf (S.Mplus φ), S.Mminus φ⁆‖ ≤ ε)
    (clu_M_adj : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
      ‖⁅S.Qf (star (S.Mplus φ)), star (S.Mminus φ)⁆‖ ≤ ε)
    (clu_O : ‖⁅S.Qf S.Oplus, S.Ominus⁆‖ ≤ ε)
    (clu_O_adj : ‖⁅S.Qf (star S.Oplus), star S.Ominus⁆‖ ≤ ε)
    (norm_Tminus : ‖S.Tminus‖ ≤ M) (norm_Kminus : ‖S.Kminus‖ ≤ M) :
    ∃ n : ℤ, ‖LinearMap.trace ℂ E (S.P * S.Tminus : E →L[ℂ] E).toLinearMap - n‖ ≤
      400 * S.p * (M + 1) * √ε :=
  h.index_core_aux hU2 hU4 clu_M clu_M_adj clu_O clu_O_adj norm_Tminus norm_Kminus le_rfl

end HRTorus.IndexCore

end -- noncomputable section (and `open Classical`)

/-! ## What Lean prints -/

#check HRTorus.IndexCore.index_core
#check @HRTorus.IndexCore.index_core
#print axioms HRTorus.IndexCore.index_core
#print axioms HRTorus.IndexCore.index_core_400
#print axioms HRTorus.IndexCore.Setting.SepBounds.index_core_small
