import HRTorus.IndexCore.ExpBounds

/-!
# Lemma 6.13(i) and (iii), with explicit constants

Written by Claude Opus 5.5 (an AI model), 2026-10-23. The HR paper's Lemma 6.13 in the finite setting: the exact relations (i); from
the 21 separated commutators of Lemma 6.13(ii) (`SepBounds`, each `≤ ε`), the commutator bounds
A1–A14 below; and the consequences (iii) with explicit constants:

* `‖𝓜(φ) - 𝓜₋(φ) 𝓜₊(φ)‖ ≤ 19.5 φ² ε`;
* `‖e^{2πiQ̄} - e^{2πiQ̄₋} e^{2πiQ̄₊}‖ ≤ 10 π² ε`;
* `‖[P, 𝓜(φ)]‖ ≤ 2 ‖[U, P]‖` and `[P, e^{itQ̄}] = 0` (in particular `[P, e^{2πiQ̄}] = 0`);
* the derivation of Lemma 6.14's `ε_c` from the separated commutators:
  `‖[𝓜₋(φ), 𝓜₊(φ)]‖ ≤ 21 φ² ε` and `‖[e^{2πiQ̄₋}, e^{2πiQ̄₊}]‖ ≤ 12 π² ε`.
-/

open scoped InnerProductSpace ComplexConjugate Real
open Complex (I)

noncomputable section

namespace HRTorus.IndexCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

namespace Setting

variable (S : Setting E)

/-! ## The forms of `Statement.lean` and the operators of Definition 6.11 -/

theorem Mminus_eq (φ : ℝ) : S.Mminus φ = expI φ S.QbarUMinus * expI (-φ) S.QbarMinus := by
  rw [Setting.Mminus, exp_I_mul_smul, exp_neg_I_mul_smul]

theorem Mplus_eq (φ : ℝ) : S.Mplus φ = expI φ S.QbarUPlus * expI (-φ) S.QbarPlus := by
  rw [Setting.Mplus, exp_I_mul_smul, exp_neg_I_mul_smul]

theorem Ominus_eq : S.Ominus = expI (2 * π) S.QbarMinus := by
  rw [Setting.Ominus, exp_two_pi_I_smul]

theorem Oplus_eq : S.Oplus = expI (2 * π) S.QbarPlus := by
  rw [Setting.Oplus, exp_two_pi_I_smul]

/-- `Q̄^U = U* Q̄ U` (Definition 6.11). -/
def QbarU : E →L[ℂ] E := star S.U * S.Qbar * S.U

/-- `𝓜(φ) = U* e^{iφQ̄} U e^{-iφQ̄}` (Definition 6.11). -/
def M (φ : ℝ) : E →L[ℂ] E := star S.U * expI φ S.Qbar * S.U * expI (-φ) S.Qbar

/-! ## Self-adjointness of the generators -/

theorem isSelfAdjoint_conj {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (star S.U * X * S.U) := by
  rw [IsSelfAdjoint, star_mul, star_mul, star_star, hX.star_eq, ← mul_assoc]

theorem isSelfAdjoint_KUminus : IsSelfAdjoint S.KUminus := S.isSelfAdjoint_conj S.isSelfAdjoint_Kminus

theorem isSelfAdjoint_KUplus : IsSelfAdjoint S.KUplus := S.isSelfAdjoint_conj S.isSelfAdjoint_Kplus

theorem isSelfAdjoint_QbarMinus : IsSelfAdjoint S.QbarMinus :=
  S.Qminus_sa.sub S.isSelfAdjoint_Kminus

theorem isSelfAdjoint_QbarPlus : IsSelfAdjoint S.QbarPlus :=
  S.Qplus_sa.sub S.isSelfAdjoint_Kplus

theorem isSelfAdjoint_QbarUMinus : IsSelfAdjoint S.QbarUMinus :=
  (S.Qminus_sa.add S.Tminus_sa).sub S.isSelfAdjoint_KUminus

theorem isSelfAdjoint_QbarUPlus : IsSelfAdjoint S.QbarUPlus :=
  (S.Qplus_sa.add S.Tplus_sa).sub S.isSelfAdjoint_KUplus

theorem isSelfAdjoint_QbarU : IsSelfAdjoint S.QbarU := S.isSelfAdjoint_conj S.isSelfAdjoint_Qbar

theorem isSelfAdjoint_Ttilde : IsSelfAdjoint S.Ttilde :=
  (S.Tminus_sa.sub S.isSelfAdjoint_KUminus).add S.isSelfAdjoint_Kminus

/-! ## Lemma 6.13(i): the exact relations -/

/-- `Q̄ = Q̄₋ + Q_m + Q̄₊`. -/
theorem Qbar_eq : S.Qbar = S.QbarMinus + S.Qmid + S.QbarPlus := by
  rw [Setting.Qbar, Setting.QbarMinus, Setting.QbarPlus, Setting.Q]; abel

/-- `Q̄^U = Q̄^U₋ + Q_m + Q̄^U₊`, from `U* Q U - Q = T₋ + T₊` ((U4)). -/
theorem QbarU_eq : S.QbarU = S.QbarUMinus + S.Qmid + S.QbarUPlus := by
  have ht : star S.U * S.Q * S.U = S.Tminus + S.Tplus + S.Q := eq_add_of_sub_eq S.transport
  simp only [QbarU, Setting.Qbar, Setting.QbarUMinus, Setting.QbarUPlus, Setting.KUminus,
    Setting.KUplus]
  rw [mul_sub, mul_sub, sub_mul, sub_mul, ht, Setting.Q]
  abel

/-- `𝓜(φ) = e^{iφQ̄^U} e^{-iφQ̄}`. -/
theorem M_eq (φ : ℝ) : S.M φ = expI φ S.QbarU * expI (-φ) S.Qbar := by
  rw [Setting.M, conj_expI _ S.U_unitary]
  rfl

/-! ## Lemma 6.13(ii): the separated commutators, as one hypothesis -/

/-- The 21 separated commutators of Lemma 6.13(ii), each `≤ ε` (the hypotheses `sep_*` of
`index_core`, in the same orientation). -/
structure SepBounds (ε : ℝ) : Prop where
  Kminus_Qmid : ‖⁅S.Kminus, S.Qmid⁆‖ ≤ ε
  KUminus_Qmid : ‖⁅S.KUminus, S.Qmid⁆‖ ≤ ε
  Kplus_Qmid : ‖⁅S.Kplus, S.Qmid⁆‖ ≤ ε
  KUplus_Qmid : ‖⁅S.KUplus, S.Qmid⁆‖ ≤ ε
  Tminus_Qmid : ‖⁅S.Tminus, S.Qmid⁆‖ ≤ ε
  Tplus_Qmid : ‖⁅S.Tplus, S.Qmid⁆‖ ≤ ε
  Qminus_Kplus : ‖⁅S.Qminus, S.Kplus⁆‖ ≤ ε
  Qminus_KUplus : ‖⁅S.Qminus, S.KUplus⁆‖ ≤ ε
  Kminus_Qplus : ‖⁅S.Kminus, S.Qplus⁆‖ ≤ ε
  KUminus_Qplus : ‖⁅S.KUminus, S.Qplus⁆‖ ≤ ε
  Qminus_Tplus : ‖⁅S.Qminus, S.Tplus⁆‖ ≤ ε
  Tminus_Qplus : ‖⁅S.Tminus, S.Qplus⁆‖ ≤ ε
  Tminus_Tplus : ‖⁅S.Tminus, S.Tplus⁆‖ ≤ ε
  Tminus_Kplus : ‖⁅S.Tminus, S.Kplus⁆‖ ≤ ε
  Tminus_KUplus : ‖⁅S.Tminus, S.KUplus⁆‖ ≤ ε
  Kminus_Tplus : ‖⁅S.Kminus, S.Tplus⁆‖ ≤ ε
  Kminus_Kplus : ‖⁅S.Kminus, S.Kplus⁆‖ ≤ ε
  Kminus_KUplus : ‖⁅S.Kminus, S.KUplus⁆‖ ≤ ε
  KUminus_Tplus : ‖⁅S.KUminus, S.Tplus⁆‖ ≤ ε
  KUminus_Kplus : ‖⁅S.KUminus, S.Kplus⁆‖ ≤ ε
  KUminus_KUplus : ‖⁅S.KUminus, S.KUplus⁆‖ ≤ ε

variable {S} {ε : ℝ}

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem norm_lie_le_of_comm {x y : E →L[ℂ] E} (h : ‖⁅y, x⁆‖ ≤ ε) : ‖⁅x, y⁆‖ ≤ ε :=
  (norm_lie_comm x y).trans_le h

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem norm_lie_eq_zero_of_commute {x y : E →L[ℂ] E} (h : Commute x y) : ‖⁅x, y⁆‖ = 0 := by
  rw [h.lie_eq, norm_zero]

/-! ## The generator commutators A1–A14 -/

/-- A1: `‖[Q_m, Q̄₋]‖ ≤ ε`. -/
theorem SepBounds.A1 (h : S.SepBounds ε) : ‖⁅S.Qmid, S.QbarMinus⁆‖ ≤ ε := by
  have h1 := norm_lie_sub_right_le S.Qmid S.Qminus S.Kminus
  have z := norm_lie_eq_zero_of_commute S.comm_Qminus_Qmid.symm
  have c1 := norm_lie_le_of_comm h.Kminus_Qmid
  rw [Setting.QbarMinus]; linarith

/-- A2: `‖[Q_m, Q̄₊]‖ ≤ ε`. -/
theorem SepBounds.A2 (h : S.SepBounds ε) : ‖⁅S.Qmid, S.QbarPlus⁆‖ ≤ ε := by
  have h1 := norm_lie_sub_right_le S.Qmid S.Qplus S.Kplus
  have z := norm_lie_eq_zero_of_commute S.comm_Qmid_Qplus
  have c1 := norm_lie_le_of_comm h.Kplus_Qmid
  rw [Setting.QbarPlus]; linarith

/-- A3: `‖[Q_m, Q̄^U₊]‖ ≤ 2ε`. -/
theorem SepBounds.A3 (h : S.SepBounds ε) : ‖⁅S.Qmid, S.QbarUPlus⁆‖ ≤ 2 * ε := by
  have h1 := norm_lie_sub_right_le S.Qmid (S.Qplus + S.Tplus) S.KUplus
  have h2 := norm_lie_add_right_le S.Qmid S.Qplus S.Tplus
  have z := norm_lie_eq_zero_of_commute S.comm_Qmid_Qplus
  have c1 := norm_lie_le_of_comm h.Tplus_Qmid
  have c2 := norm_lie_le_of_comm h.KUplus_Qmid
  rw [Setting.QbarUPlus]; linarith

/-- A4: `‖[Q_m, Q̄^U₋]‖ ≤ 2ε`. -/
theorem SepBounds.A4 (h : S.SepBounds ε) : ‖⁅S.Qmid, S.QbarUMinus⁆‖ ≤ 2 * ε := by
  have h1 := norm_lie_sub_right_le S.Qmid (S.Qminus + S.Tminus) S.KUminus
  have h2 := norm_lie_add_right_le S.Qmid S.Qminus S.Tminus
  have z := norm_lie_eq_zero_of_commute S.comm_Qminus_Qmid.symm
  have c1 := norm_lie_le_of_comm h.Tminus_Qmid
  have c2 := norm_lie_le_of_comm h.KUminus_Qmid
  rw [Setting.QbarUMinus]; linarith

/-- A5: `‖[Q̄₋, Q̄₊]‖ ≤ 3ε`. -/
theorem SepBounds.A5 (h : S.SepBounds ε) : ‖⁅S.QbarMinus, S.QbarPlus⁆‖ ≤ 3 * ε := by
  have l := norm_lie_sub_left_le S.Qminus S.Kminus (S.Qplus - S.Kplus)
  have r1 := norm_lie_sub_right_le S.Qminus S.Qplus S.Kplus
  have r2 := norm_lie_sub_right_le S.Kminus S.Qplus S.Kplus
  have z := norm_lie_eq_zero_of_commute S.comm_Qminus_Qplus
  have := h.Qminus_Kplus; have := h.Kminus_Qplus; have := h.Kminus_Kplus
  rw [Setting.QbarMinus, Setting.QbarPlus]; linarith

/-- A6: `‖[Q̄^U₋, Q̄^U₊]‖ ≤ 8ε`. -/
theorem SepBounds.A6 (h : S.SepBounds ε) : ‖⁅S.QbarUMinus, S.QbarUPlus⁆‖ ≤ 8 * ε := by
  set Y := S.Qplus + S.Tplus - S.KUplus
  have l1 := norm_lie_sub_left_le (S.Qminus + S.Tminus) S.KUminus Y
  have l2 := norm_lie_add_left_le S.Qminus S.Tminus Y
  have r := fun x : E →L[ℂ] E => norm_lie_sub_right_le x (S.Qplus + S.Tplus) S.KUplus
  have r' := fun x : E →L[ℂ] E => norm_lie_add_right_le x S.Qplus S.Tplus
  have a1 := r S.Qminus; have a2 := r S.Tminus; have a3 := r S.KUminus
  have b1 := r' S.Qminus; have b2 := r' S.Tminus; have b3 := r' S.KUminus
  have z := norm_lie_eq_zero_of_commute S.comm_Qminus_Qplus
  have := h.Qminus_Tplus; have := h.Qminus_KUplus; have := h.Tminus_Qplus
  have := h.Tminus_Tplus; have := h.Tminus_KUplus; have := h.KUminus_Qplus
  have := h.KUminus_Tplus; have := h.KUminus_KUplus
  rw [Setting.QbarUMinus, Setting.QbarUPlus]; linarith

/-- A7: `‖[Q̄^U₋, Q̄₊]‖ ≤ 5ε`. -/
theorem SepBounds.A7 (h : S.SepBounds ε) : ‖⁅S.QbarUMinus, S.QbarPlus⁆‖ ≤ 5 * ε := by
  set Y := S.Qplus - S.Kplus
  have l1 := norm_lie_sub_left_le (S.Qminus + S.Tminus) S.KUminus Y
  have l2 := norm_lie_add_left_le S.Qminus S.Tminus Y
  have a1 := norm_lie_sub_right_le S.Qminus S.Qplus S.Kplus
  have a2 := norm_lie_sub_right_le S.Tminus S.Qplus S.Kplus
  have a3 := norm_lie_sub_right_le S.KUminus S.Qplus S.Kplus
  have z := norm_lie_eq_zero_of_commute S.comm_Qminus_Qplus
  have := h.Qminus_Kplus; have := h.Tminus_Qplus; have := h.Tminus_Kplus
  have := h.KUminus_Qplus; have := h.KUminus_Kplus
  rw [Setting.QbarUMinus, Setting.QbarPlus]; linarith

/-- A8: `‖[Q̄₋, Q̄^U₊]‖ ≤ 5ε`. -/
theorem SepBounds.A8 (h : S.SepBounds ε) : ‖⁅S.QbarMinus, S.QbarUPlus⁆‖ ≤ 5 * ε := by
  set Y := S.Qplus + S.Tplus - S.KUplus
  have l := norm_lie_sub_left_le S.Qminus S.Kminus Y
  have a1 := norm_lie_sub_right_le S.Qminus (S.Qplus + S.Tplus) S.KUplus
  have a2 := norm_lie_sub_right_le S.Kminus (S.Qplus + S.Tplus) S.KUplus
  have b1 := norm_lie_add_right_le S.Qminus S.Qplus S.Tplus
  have b2 := norm_lie_add_right_le S.Kminus S.Qplus S.Tplus
  have z := norm_lie_eq_zero_of_commute S.comm_Qminus_Qplus
  have := h.Qminus_Tplus; have := h.Qminus_KUplus; have := h.Kminus_Qplus
  have := h.Kminus_Tplus; have := h.Kminus_KUplus
  rw [Setting.QbarMinus, Setting.QbarUPlus]; linarith

/-- A9: `‖[Q_m, T̃]‖ ≤ 3ε`. -/
theorem SepBounds.A9 (h : S.SepBounds ε) : ‖⁅S.Qmid, S.Ttilde⁆‖ ≤ 3 * ε := by
  have h1 := norm_lie_add_right_le S.Qmid (S.Tminus - S.KUminus) S.Kminus
  have h2 := norm_lie_sub_right_le S.Qmid S.Tminus S.KUminus
  have c1 := norm_lie_le_of_comm h.Tminus_Qmid
  have c2 := norm_lie_le_of_comm h.KUminus_Qmid
  have c3 := norm_lie_le_of_comm h.Kminus_Qmid
  rw [Setting.Ttilde]; linarith

/-- A10: `‖[Q̄₊, T̃]‖ ≤ 6ε`. -/
theorem SepBounds.A10 (h : S.SepBounds ε) : ‖⁅S.QbarPlus, S.Ttilde⁆‖ ≤ 6 * ε := by
  set Z := S.Tminus - S.KUminus + S.Kminus
  have l := norm_lie_sub_left_le S.Qplus S.Kplus Z
  have r := fun x : E →L[ℂ] E => norm_lie_add_right_le x (S.Tminus - S.KUminus) S.Kminus
  have r' := fun x : E →L[ℂ] E => norm_lie_sub_right_le x S.Tminus S.KUminus
  have a1 := r S.Qplus; have a2 := r S.Kplus; have b1 := r' S.Qplus; have b2 := r' S.Kplus
  have c1 := norm_lie_le_of_comm h.Tminus_Qplus
  have c2 := norm_lie_le_of_comm h.KUminus_Qplus
  have c3 := norm_lie_le_of_comm h.Kminus_Qplus
  have c4 := norm_lie_le_of_comm h.Tminus_Kplus
  have c5 := norm_lie_le_of_comm h.KUminus_Kplus
  have c6 := norm_lie_le_of_comm h.Kminus_Kplus
  rw [Setting.QbarPlus, Setting.Ttilde]; linarith

/-- A11: `‖[Q̄₋, Q_m + Q₊]‖ ≤ 2ε`. -/
theorem SepBounds.A11 (h : S.SepBounds ε) : ‖⁅S.QbarMinus, S.Qmid + S.Qplus⁆‖ ≤ 2 * ε := by
  have l := norm_lie_sub_left_le S.Qminus S.Kminus (S.Qmid + S.Qplus)
  have a1 := norm_lie_add_right_le S.Qminus S.Qmid S.Qplus
  have a2 := norm_lie_add_right_le S.Kminus S.Qmid S.Qplus
  have z1 := norm_lie_eq_zero_of_commute S.comm_Qminus_Qmid
  have z2 := norm_lie_eq_zero_of_commute S.comm_Qminus_Qplus
  have := h.Kminus_Qmid; have := h.Kminus_Qplus
  rw [Setting.QbarMinus]; linarith

/-- A12: `‖[Q̄^U₋, Q_m + Q₊ + T₊]‖ ≤ 7ε`. -/
theorem SepBounds.A12 (h : S.SepBounds ε) :
    ‖⁅S.QbarUMinus, S.Qmid + S.Qplus + S.Tplus⁆‖ ≤ 7 * ε := by
  set Y := S.Qmid + S.Qplus + S.Tplus
  have l1 := norm_lie_sub_left_le (S.Qminus + S.Tminus) S.KUminus Y
  have l2 := norm_lie_add_left_le S.Qminus S.Tminus Y
  have r := fun x : E →L[ℂ] E => norm_lie_add_right_le x (S.Qmid + S.Qplus) S.Tplus
  have r' := fun x : E →L[ℂ] E => norm_lie_add_right_le x S.Qmid S.Qplus
  have a1 := r S.Qminus; have a2 := r S.Tminus; have a3 := r S.KUminus
  have b1 := r' S.Qminus; have b2 := r' S.Tminus; have b3 := r' S.KUminus
  have z1 := norm_lie_eq_zero_of_commute S.comm_Qminus_Qmid
  have z2 := norm_lie_eq_zero_of_commute S.comm_Qminus_Qplus
  have := h.Qminus_Tplus; have := h.Tminus_Qmid; have := h.Tminus_Qplus
  have := h.Tminus_Tplus; have := h.KUminus_Qmid; have := h.KUminus_Qplus
  have := h.KUminus_Tplus
  rw [Setting.QbarUMinus]; linarith

/-- A13: `‖[Q_m, Q₊ + T₊]‖ ≤ ε`. -/
theorem SepBounds.A13 (h : S.SepBounds ε) : ‖⁅S.Qmid, S.Qplus + S.Tplus⁆‖ ≤ ε := by
  have h1 := norm_lie_add_right_le S.Qmid S.Qplus S.Tplus
  have z := norm_lie_eq_zero_of_commute S.comm_Qmid_Qplus
  have c1 := norm_lie_le_of_comm h.Tplus_Qmid
  linarith

/-- A14: `‖[Q₋ + Q_m, Q₊ + T₊]‖ ≤ 2ε`. -/
theorem SepBounds.A14 (h : S.SepBounds ε) :
    ‖⁅S.Qminus + S.Qmid, S.Qplus + S.Tplus⁆‖ ≤ 2 * ε := by
  have l := norm_lie_add_left_le S.Qminus S.Qmid (S.Qplus + S.Tplus)
  have a1 := norm_lie_add_right_le S.Qminus S.Qplus S.Tplus
  have a2 := norm_lie_add_right_le S.Qmid S.Qplus S.Tplus
  have z1 := norm_lie_eq_zero_of_commute S.comm_Qminus_Qplus
  have z2 := norm_lie_eq_zero_of_commute S.comm_Qmid_Qplus
  have := h.Qminus_Tplus
  have c1 := norm_lie_le_of_comm h.Tplus_Qmid
  linarith

/-! ## Lemma 6.13(iii): the consequences, with explicit constants -/

theorem abs_mul_abs_eq_sq (φ : ℝ) : |φ| * |φ| = φ ^ 2 := by
  rw [abs_mul_abs_self, sq]

theorem abs_mul_abs_neg_eq_sq (φ : ℝ) : |φ| * |-φ| = φ ^ 2 := by
  rw [abs_neg, abs_mul_abs_eq_sq]

theorem abs_neg_mul_abs_eq_sq (φ : ℝ) : |-φ| * |φ| = φ ^ 2 := by
  rw [abs_neg, abs_mul_abs_eq_sq]

theorem abs_neg_mul_abs_neg_eq_sq (φ : ℝ) : |-φ| * |-φ| = φ ^ 2 := by
  rw [abs_neg, abs_mul_abs_eq_sq]

/-- **Lemma 6.13(iii)**, the factorization of the flux insertion:
`‖𝓜(φ) - 𝓜₋(φ) 𝓜₊(φ)‖ ≤ 19.5 φ² ε`. -/
theorem SepBounds.norm_M_sub_le (h : S.SepBounds ε) (φ : ℝ) :
    ‖S.M φ - S.Mminus φ * S.Mplus φ‖ ≤ 39 / 2 * φ ^ 2 * ε := by
  have sUm := S.isSelfAdjoint_QbarUMinus
  have sUp := S.isSelfAdjoint_QbarUPlus
  have sm := S.Qmid_sa
  have sbm := S.isSelfAdjoint_QbarMinus
  have sbp := S.isSelfAdjoint_QbarPlus
  have hε : 0 ≤ ε := (norm_nonneg _).trans h.Kminus_Qmid
  set a₁ := expI φ S.QbarUMinus with ha₁
  set a₂ := expI φ S.Qmid with ha₂
  set a₃ := expI φ S.QbarUPlus with ha₃
  set b₁ := expI (-φ) S.QbarPlus with hb₁
  set b₂ := expI (-φ) S.Qmid with hb₂
  set b₃ := expI (-φ) S.QbarMinus with hb₃
  -- the four splittings (Lemma A.8)
  have s1 : ‖expI φ S.QbarU - a₁ * expI φ (S.Qmid + S.QbarUPlus)‖ ≤ φ ^ 2 / 2 * (10 * ε) := by
    have e : S.QbarU = S.QbarUMinus + (S.Qmid + S.QbarUPlus) := by rw [S.QbarU_eq, add_assoc]
    rw [e]
    refine (norm_expI_add_sub_le _ sUm (sm.add sUp) φ).trans ?_
    have l := norm_lie_add_right_le S.QbarUMinus S.Qmid S.QbarUPlus
    have a4 := norm_lie_le_of_comm h.A4
    have a6 := h.A6
    gcongr
    linarith
  have s2 : ‖expI φ (S.Qmid + S.QbarUPlus) - a₂ * a₃‖ ≤ φ ^ 2 / 2 * (2 * ε) :=
    (norm_expI_add_sub_le _ sm sUp φ).trans (by gcongr; exact h.A3)
  have s3 : ‖expI (-φ) S.Qbar - b₁ * expI (-φ) (S.Qmid + S.QbarMinus)‖ ≤
      φ ^ 2 / 2 * (4 * ε) := by
    have e : S.Qbar = S.QbarPlus + (S.Qmid + S.QbarMinus) := by rw [S.Qbar_eq]; abel
    rw [e]
    refine (norm_expI_add_sub_le _ sbp (sm.add sbm) (-φ)).trans ?_
    rw [neg_sq]
    have l := norm_lie_add_right_le S.QbarPlus S.Qmid S.QbarMinus
    have a2 := norm_lie_le_of_comm h.A2
    have a5 := norm_lie_le_of_comm h.A5
    gcongr
    linarith
  have s4 : ‖expI (-φ) (S.Qmid + S.QbarMinus) - b₂ * b₃‖ ≤ φ ^ 2 / 2 * ε := by
    refine (norm_expI_add_sub_le _ sm sbm (-φ)).trans ?_
    rw [neg_sq]
    gcongr
    exact h.A1
  -- the norms of the factors
  have n_a₁ := norm_expI_le _ sUm φ
  have n_b₁ := norm_expI_le _ sbp (-φ)
  have nX' : ‖a₁ * (a₂ * a₃)‖ ≤ 1 := by
    rw [norm_expI_mul _ sUm, norm_expI_mul _ sm]; exact norm_expI_le _ sUp φ
  have nZ : ‖expI (-φ) S.Qbar‖ ≤ 1 := norm_expI_le _ S.isSelfAdjoint_Qbar (-φ)
  -- step 1: the product of the four splittings
  have t1 : ‖expI φ S.QbarU * expI (-φ) S.Qbar - a₁ * (a₂ * a₃) * (b₁ * (b₂ * b₃))‖ ≤
      17 / 2 * φ ^ 2 * ε := by
    have hX : ‖expI φ S.QbarU - a₁ * (a₂ * a₃)‖ ≤ φ ^ 2 / 2 * (10 * ε) + φ ^ 2 / 2 * (2 * ε) := by
      calc ‖expI φ S.QbarU - a₁ * (a₂ * a₃)‖
          ≤ ‖expI φ S.QbarU - a₁ * expI φ (S.Qmid + S.QbarUPlus)‖ +
              ‖a₁ * expI φ (S.Qmid + S.QbarUPlus) - a₁ * (a₂ * a₃)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = ‖expI φ S.QbarU - a₁ * expI φ (S.Qmid + S.QbarUPlus)‖ +
              ‖expI φ (S.Qmid + S.QbarUPlus) - a₂ * a₃‖ := by
            rw [← mul_sub, norm_expI_mul _ sUm]
        _ ≤ _ := add_le_add s1 s2
    have hZ : ‖expI (-φ) S.Qbar - b₁ * (b₂ * b₃)‖ ≤ φ ^ 2 / 2 * (4 * ε) + φ ^ 2 / 2 * ε := by
      calc ‖expI (-φ) S.Qbar - b₁ * (b₂ * b₃)‖
          ≤ ‖expI (-φ) S.Qbar - b₁ * expI (-φ) (S.Qmid + S.QbarMinus)‖ +
              ‖b₁ * expI (-φ) (S.Qmid + S.QbarMinus) - b₁ * (b₂ * b₃)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = ‖expI (-φ) S.Qbar - b₁ * expI (-φ) (S.Qmid + S.QbarMinus)‖ +
              ‖expI (-φ) (S.Qmid + S.QbarMinus) - b₂ * b₃‖ := by
            rw [← mul_sub, norm_expI_mul _ sbp]
        _ ≤ _ := add_le_add s3 s4
    calc ‖expI φ S.QbarU * expI (-φ) S.Qbar - a₁ * (a₂ * a₃) * (b₁ * (b₂ * b₃))‖
        ≤ ‖expI φ S.QbarU - a₁ * (a₂ * a₃)‖ + ‖expI (-φ) S.Qbar - b₁ * (b₂ * b₃)‖ :=
          norm_mul_sub_mul_le nZ nX'
      _ ≤ _ := add_le_add hX hZ
      _ = 17 / 2 * φ ^ 2 * ε := by ring
  -- step 2: moving `e^{iφQ_m}` past `𝓜₊`
  have t2 : ‖a₁ * (a₂ * a₃) * (b₁ * (b₂ * b₃)) - a₁ * (a₃ * b₁) * b₃‖ ≤ 3 * φ ^ 2 * ε := by
    have hab : a₂ * b₂ = 1 := by rw [ha₂, hb₂, expI_mul_expI_neg]
    have e : a₁ * (a₂ * a₃) * (b₁ * (b₂ * b₃)) - a₁ * (a₃ * b₁) * b₃ =
        a₁ * (⁅a₂, a₃ * b₁⁆ * b₂) * b₃ := by
      have : ⁅a₂, a₃ * b₁⁆ * b₂ = a₂ * (a₃ * b₁) * b₂ - a₃ * b₁ * (a₂ * b₂) := by
        rw [Ring.lie_def]; noncomm_ring
      rw [this, hab, mul_one]; noncomm_ring
    rw [e, norm_mul_expI _ sbm, norm_expI_mul _ sUm, norm_mul_expI _ sm, norm_lie_comm]
    have n_a₃ := norm_expI_le _ sUp φ
    have l := norm_lie_mul_le a₂ n_a₃ n_b₁
    have c1 : ‖⁅a₃, a₂⁆‖ ≤ φ ^ 2 * (2 * ε) := by
      refine (norm_lie_expI_expI_le _ sUp sm φ φ).trans ?_
      rw [abs_mul_abs_eq_sq]; gcongr; exact norm_lie_le_of_comm h.A3
    have c2 : ‖⁅b₁, a₂⁆‖ ≤ φ ^ 2 * ε := by
      refine (norm_lie_expI_expI_le _ sbp sm (-φ) φ).trans ?_
      rw [abs_neg_mul_abs_eq_sq]; gcongr; exact norm_lie_le_of_comm h.A2
    linarith
  -- step 3: moving `𝓜₊` past `e^{-iφQ̄₋}`
  have t3 : ‖a₁ * (a₃ * b₁) * b₃ - a₁ * b₃ * (a₃ * b₁)‖ ≤ 8 * φ ^ 2 * ε := by
    have e : a₁ * (a₃ * b₁) * b₃ - a₁ * b₃ * (a₃ * b₁) = a₁ * ⁅a₃ * b₁, b₃⁆ := by
      rw [Ring.lie_def]; noncomm_ring
    rw [e, norm_expI_mul _ sUm]
    have n_a₃ := norm_expI_le _ sUp φ
    have l := norm_lie_mul_le b₃ n_a₃ n_b₁
    have c1 : ‖⁅a₃, b₃⁆‖ ≤ φ ^ 2 * (5 * ε) := by
      refine (norm_lie_expI_expI_le _ sUp sbm φ (-φ)).trans ?_
      rw [abs_mul_abs_neg_eq_sq]; gcongr; exact norm_lie_le_of_comm h.A8
    have c2 : ‖⁅b₁, b₃⁆‖ ≤ φ ^ 2 * (3 * ε) := by
      refine (norm_lie_expI_expI_le _ sbp sbm (-φ) (-φ)).trans ?_
      rw [abs_neg_mul_abs_neg_eq_sq]; gcongr; exact norm_lie_le_of_comm h.A5
    linarith
  rw [S.M_eq, S.Mminus_eq, S.Mplus_eq]
  calc ‖expI φ S.QbarU * expI (-φ) S.Qbar - a₁ * b₃ * (a₃ * b₁)‖
      ≤ ‖expI φ S.QbarU * expI (-φ) S.Qbar - a₁ * (a₂ * a₃) * (b₁ * (b₂ * b₃))‖ +
          ‖a₁ * (a₂ * a₃) * (b₁ * (b₂ * b₃)) - a₁ * b₃ * (a₃ * b₁)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖expI φ S.QbarU * expI (-φ) S.Qbar - a₁ * (a₂ * a₃) * (b₁ * (b₂ * b₃))‖ +
          (‖a₁ * (a₂ * a₃) * (b₁ * (b₂ * b₃)) - a₁ * (a₃ * b₁) * b₃‖ +
            ‖a₁ * (a₃ * b₁) * b₃ - a₁ * b₃ * (a₃ * b₁)‖) := by
        gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 17 / 2 * φ ^ 2 * ε + (3 * φ ^ 2 * ε + 8 * φ ^ 2 * ε) := by
        gcongr
    _ = 39 / 2 * φ ^ 2 * ε := by ring

/-- `e^{2πiQ_m} = 1`. -/
theorem expI_two_pi_Qmid : expI (2 * π) S.Qmid = 1 := by
  rw [← exp_two_pi_I_smul]; exact S.exp_Qmid

/-- **Lemma 6.13(iii)**: `‖e^{2πiQ̄} - e^{2πiQ̄₋} e^{2πiQ̄₊}‖ ≤ 10 π² ε`. -/
theorem SepBounds.norm_expI_Qbar_sub_le (h : S.SepBounds ε) :
    ‖expI (2 * π) S.Qbar - S.Ominus * S.Oplus‖ ≤ 10 * π ^ 2 * ε := by
  have sm := S.Qmid_sa
  have sbm := S.isSelfAdjoint_QbarMinus
  have sbp := S.isSelfAdjoint_QbarPlus
  have s1 : ‖expI (2 * π) S.Qbar - S.Ominus * expI (2 * π) (S.Qmid + S.QbarPlus)‖ ≤
      (2 * π) ^ 2 / 2 * (4 * ε) := by
    have e : S.Qbar = S.QbarMinus + (S.Qmid + S.QbarPlus) := by rw [S.Qbar_eq, add_assoc]
    rw [e, S.Ominus_eq]
    refine (norm_expI_add_sub_le _ sbm (sm.add sbp) (2 * π)).trans ?_
    have l := norm_lie_add_right_le S.QbarMinus S.Qmid S.QbarPlus
    have a1 := norm_lie_le_of_comm h.A1
    have a5 := h.A5
    gcongr
    linarith
  have s2 : ‖expI (2 * π) (S.Qmid + S.QbarPlus) - S.Oplus‖ ≤ (2 * π) ^ 2 / 2 * ε := by
    have := norm_expI_add_sub_le _ sm sbp (2 * π)
    rw [S.expI_two_pi_Qmid, one_mul] at this
    rw [S.Oplus_eq]
    exact this.trans (by gcongr; exact h.A2)
  calc ‖expI (2 * π) S.Qbar - S.Ominus * S.Oplus‖
      ≤ ‖expI (2 * π) S.Qbar - S.Ominus * expI (2 * π) (S.Qmid + S.QbarPlus)‖ +
          ‖S.Ominus * expI (2 * π) (S.Qmid + S.QbarPlus) - S.Ominus * S.Oplus‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖expI (2 * π) S.Qbar - S.Ominus * expI (2 * π) (S.Qmid + S.QbarPlus)‖ +
          ‖expI (2 * π) (S.Qmid + S.QbarPlus) - S.Oplus‖ := by
        rw [← mul_sub, S.Ominus_eq, norm_expI_mul _ sbm]
    _ ≤ (2 * π) ^ 2 / 2 * (4 * ε) + (2 * π) ^ 2 / 2 * ε := add_le_add s1 s2
    _ = 10 * π ^ 2 * ε := by ring

/-- `[P, e^{itQ̄}] = 0` (Lemma 6.13(iii), from Lemma 6.7). -/
theorem commute_P_expI_Qbar (t : ℝ) : Commute S.P (expI t S.Qbar) :=
  commute_expI_of_commute S.Qbar S.commute_Qbar_P.symm t

theorem lie_P_expI_Qbar (t : ℝ) : ⁅S.P, expI t S.Qbar⁆ = 0 :=
  (S.commute_P_expI_Qbar t).lie_eq

/-- `[P, e^{2πiQ̄}] = 0` in the form of `Statement.lean`. -/
theorem lie_P_exp_two_pi_Qbar : ⁅S.P, NormedSpace.exp ((2 * π * I) • S.Qbar)⁆ = 0 := by
  rw [exp_two_pi_I_smul]; exact S.lie_P_expI_Qbar _

/-- **Lemma 6.13(iii)**: `‖[P, 𝓜(φ)]‖ ≤ 2 ‖[U, P]‖`. -/
theorem norm_lie_P_M_le (φ : ℝ) : ‖⁅S.P, S.M φ⁆‖ ≤ 2 * ‖⁅S.U, S.P⁆‖ := by
  set A := expI φ S.Qbar with hA
  set A' := expI (-φ) S.Qbar with hA'
  have sQ := S.isSelfAdjoint_Qbar
  have hPA : S.P * A = A * S.P := (S.commute_P_expI_Qbar φ).eq
  have hPA' : S.P * A' = A' * S.P := (S.commute_P_expI_Qbar (-φ)).eq
  have e : ⁅S.P, S.M φ⁆ = ⁅S.P, star S.U⁆ * (A * S.U * A') + star S.U * A * ⁅S.P, S.U⁆ * A' := by
    have e0 : ⁅S.P, S.M φ⁆ - (⁅S.P, star S.U⁆ * (A * S.U * A') + star S.U * A * ⁅S.P, S.U⁆ * A') =
        star S.U * (S.P * A - A * S.P) * S.U * A' +
          star S.U * A * S.U * (S.P * A' - A' * S.P) := by
      simp only [Setting.M, Ring.lie_def]; rw [← hA, ← hA']; noncomm_ring
    rw [hPA, hPA', sub_self, sub_self, mul_zero, zero_mul, zero_mul, mul_zero, add_zero] at e0
    exact sub_eq_zero.mp e0
  have hU := S.U_unitary
  have hU' := Unitary.star_mem hU
  have n1 : ‖⁅S.P, star S.U⁆ * (A * S.U * A')‖ = ‖⁅S.U, S.P⁆‖ := by
    rw [← mul_assoc, ← mul_assoc, norm_mul_expI _ sQ,
      CStarRing.norm_mul_coe_unitary _ ⟨S.U, hU⟩, norm_mul_expI _ sQ]
    have : ⁅S.P, star S.U⁆ = star ⁅S.U, S.P⁆ := by
      rw [Ring.lie_def, Ring.lie_def, star_sub, star_mul, star_mul, S.star_P]
    rw [this]
    exact norm_star ⁅S.U, S.P⁆
  have n2 : ‖star S.U * A * ⁅S.P, S.U⁆ * A'‖ = ‖⁅S.U, S.P⁆‖ := by
    rw [norm_mul_expI _ sQ, mul_assoc, CStarRing.norm_coe_unitary_mul ⟨star S.U, hU'⟩,
      norm_expI_mul _ sQ, norm_lie_comm]
  rw [e]
  calc ‖⁅S.P, star S.U⁆ * (A * S.U * A') + star S.U * A * ⁅S.P, S.U⁆ * A'‖
      ≤ ‖⁅S.P, star S.U⁆ * (A * S.U * A')‖ + ‖star S.U * A * ⁅S.P, S.U⁆ * A'‖ :=
        norm_add_le _ _
    _ = 2 * ‖⁅S.U, S.P⁆‖ := by rw [n1, n2]; ring

/-! ## Lemma 6.14's `ε_c`, derived from the separated commutators -/

/-- `ε_c` for the flux insertions: `‖[𝓜₋(φ), 𝓜₊(φ)]‖ ≤ 21 φ² ε`. -/
theorem SepBounds.norm_lie_Mminus_Mplus_le (h : S.SepBounds ε) (φ : ℝ) :
    ‖⁅S.Mminus φ, S.Mplus φ⁆‖ ≤ 21 * φ ^ 2 * ε := by
  have sUm := S.isSelfAdjoint_QbarUMinus
  have sUp := S.isSelfAdjoint_QbarUPlus
  have sbm := S.isSelfAdjoint_QbarMinus
  have sbp := S.isSelfAdjoint_QbarPlus
  rw [S.Mminus_eq, S.Mplus_eq]
  set a₁ := expI φ S.QbarUMinus
  set a₃ := expI φ S.QbarUPlus
  set b₁ := expI (-φ) S.QbarPlus
  set b₃ := expI (-φ) S.QbarMinus
  have n_a₁ := norm_expI_le _ sUm φ
  have n_a₃ := norm_expI_le _ sUp φ
  have n_b₁ := norm_expI_le _ sbp (-φ)
  have n_b₃ := norm_expI_le _ sbm (-φ)
  have l := norm_lie_mul_le (a₃ * b₁) n_a₁ n_b₃
  have l1 : ‖⁅a₁, a₃ * b₁⁆‖ ≤ ‖⁅a₃, a₁⁆‖ + ‖⁅b₁, a₁⁆‖ := by
    rw [norm_lie_comm]; exact norm_lie_mul_le a₁ n_a₃ n_b₁
  have l2 : ‖⁅b₃, a₃ * b₁⁆‖ ≤ ‖⁅a₃, b₃⁆‖ + ‖⁅b₁, b₃⁆‖ := by
    rw [norm_lie_comm]; exact norm_lie_mul_le b₃ n_a₃ n_b₁
  have c1 : ‖⁅a₃, a₁⁆‖ ≤ φ ^ 2 * (8 * ε) := by
    refine (norm_lie_expI_expI_le _ sUp sUm φ φ).trans ?_
    rw [abs_mul_abs_eq_sq]; gcongr; exact norm_lie_le_of_comm h.A6
  have c2 : ‖⁅b₁, a₁⁆‖ ≤ φ ^ 2 * (5 * ε) := by
    refine (norm_lie_expI_expI_le _ sbp sUm (-φ) φ).trans ?_
    rw [abs_neg_mul_abs_eq_sq]; gcongr; exact norm_lie_le_of_comm h.A7
  have c3 : ‖⁅a₃, b₃⁆‖ ≤ φ ^ 2 * (5 * ε) := by
    refine (norm_lie_expI_expI_le _ sUp sbm φ (-φ)).trans ?_
    rw [abs_mul_abs_neg_eq_sq]; gcongr; exact norm_lie_le_of_comm h.A8
  have c4 : ‖⁅b₁, b₃⁆‖ ≤ φ ^ 2 * (3 * ε) := by
    refine (norm_lie_expI_expI_le _ sbp sbm (-φ) (-φ)).trans ?_
    rw [abs_neg_mul_abs_neg_eq_sq]; gcongr; exact norm_lie_le_of_comm h.A5
  linarith

/-- `ε_c` for the charge unitaries: `‖[e^{2πiQ̄₋}, e^{2πiQ̄₊}]‖ ≤ 12 π² ε`. -/
theorem SepBounds.norm_lie_Ominus_Oplus_le (h : S.SepBounds ε) :
    ‖⁅S.Ominus, S.Oplus⁆‖ ≤ 12 * π ^ 2 * ε := by
  rw [S.Ominus_eq, S.Oplus_eq]
  refine (norm_lie_expI_expI_le _ S.isSelfAdjoint_QbarMinus S.isSelfAdjoint_QbarPlus _ _).trans ?_
  have hπ : |2 * π| * |2 * π| = 4 * π ^ 2 := by rw [abs_mul_abs_self]; ring
  rw [hπ]
  have := h.A5
  nlinarith [Real.pi_pos, sq_nonneg π]

end Setting

end HRTorus.IndexCore
