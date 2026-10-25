import HRTorus.Assembly.Inputs

/-!
# The magnetic translation and the divisibility corollaries (T-0056 block E, `Assembly.Translation`)

Written by Claude Opus 5.5 (an AI model; recruit L11), 2026-10-25. **The definitions and statements were written first
and reviewed against the paper (the statement phase); proof phase rounds one and two added the proofs and the proof
devices, each section of which is marked as such. No theorem of this module is `sorry`. Round two moved six of the
devices of Lemma 7.1 to `Assembly.Inputs`, where the table of Lemma 6.12 first uses them.**
The paper: the HR paper, `papers/hr/sections/06-index-theorem.tex` — Assumption 6.4 `ass:U`; and
`papers/hr/sections/07-translation.tex` — Lemma 7.1 `lem:theta`, Corollary 7.2 `cor:translation`, Corollary 7.3
`cor:classwide`, Corollary 7.4 `cor:classwide-odd`. The core's `Orbital.translation_corollary`, `four_dvd_p`,
`odd_plus`, `odd_minus` (T-0052) are the finite-dimensional content of Corollaries 7.2–7.4.

## The model

* **Lemma 7.1** is stated on the paper's objects (matrices on `𝓗_N`), for a setting with (H1), (H2) and Assumption 6.3:
  (a) the commutations of `Θ`, (b) the transport identity and the properties of `T_±` (with `ι(T_±) ∈ Alg(∂_±)`), (c) the
  exponentials, (d) the traces, (e) `Θ^*K_±Θ ∈ 𝒜𝒮_{∂_±}` with prefactor exponent `5/2` and the trace identities. The core
  proves (a)'s `[Θ, P] = 0`, (b)'s identity, (c), (d) and (e)'s trace identity on its `Orbital` (`commute_Θ_P`,
  `transport_Γ`, `exp_Q_add_Tplus`, `trc_P_n`, `trc_P_Ttilde`); through `orbOf` and its identifications these are the
  matrix statements here.
* **Assumption 6.4** is `TransportAssumption D U T₋ T₊` (for a sequence of unitaries and of `T_±`), stated where §7 needs
  it: Corollary 7.2's first claim, that `U = Θ` satisfies it with (U2) and (U4)'s two relations exact.
* **Corollaries 7.2–7.4 are stated for the class**, as the paper states them: any setting whose `H` satisfies (H1) and
  (H2) (block C's `H1Data` with `H2`), with the filters of `ArgData.std` (the fixed choices of `Assembly.Setting`). The
  hollow-core model is the instance given by block C's `hollowCore_mem_class` (used in `Assembly.Main`).
* The sectors `(N/2, N/2)` and `((N ± 1)/2, (N ∓ 1)/2)` are `halfSector`, `oddSectorPlus`, `oddSectorMinus` (natural
  division, exact at the parities where they are used).
-/

open scoped InnerProductSpace Matrix ENNReal Real ComplexConjugate
open Complex (I)
open MeasureTheory Filter

noncomputable section

namespace HRTorus.Assembly

open HRTorus.SlotFrame HRTorus.LLL HRTorus.Fock HRTorus.Hamiltonian HRTorus.Locality
open HRTorus.IndexCore (bandΓ quarterMinus quarterMid quarterPlus)
open HRTorus.Fermion.Pilot.JW (Spin Mode Conf Op IsEven CAR Alg)

variable {η : ℝ → ℝ} {δ₀ : ℝ}

/-! ## The sectors of §§7–8 -/

/-- Corollary 7.3: "`the sectors $\nn_N=(N/2,N/2)$`" (the label `(⌊N/2⌋, ⌊N/2⌋)`, exact for even `N`). -/
def halfSector (T : Torus) : SectorLabel T :=
  (⟨T.N / 2, by unfold Torus.Nφ; omega⟩, ⟨T.N / 2, by unfold Torus.Nφ; omega⟩)

/-- Corollary 7.4: "`$\nn^\pm_N:=((N\pm1)/2,(N\mp1)/2)$`" — `𝐧^+_N` (exact for odd `N`). -/
def oddSectorPlus (T : Torus) : SectorLabel T :=
  (⟨(T.N + 1) / 2, by unfold Torus.Nφ; omega⟩, ⟨(T.N - 1) / 2, by unfold Torus.Nφ; omega⟩)

/-- Corollary 7.4: `𝐧^-_N = ((N − 1)/2, (N + 1)/2)`. -/
def oddSectorMinus (T : Torus) : SectorLabel T :=
  (⟨(T.N - 1) / 2, by unfold Torus.Nφ; omega⟩, ⟨(T.N + 1) / 2, by unfold Torus.Nφ; omega⟩)

/-! ## The hollow-core model in Setting 6.1 -/

/-- **The hollow-core model in Setting 6.1** (Corollary 4.8): over a torus sequence with `L_x ≥ c_*√N`, the Hamiltonians
`H_N` of Definition 2.7 with the (H1) data that block C's `hollowCore_mem_class` provides (local terms `h_R` of
Definition 4.1, `C_h = 7/π`, and (H2)), for the paper's profile `etaStd` and `δ₀ = √π`. -/
def hcSetting (Ts : TorusSeq δstd) (cstar : ℝ) (hc : 0 < cstar)
    (hLx : ∀ N ∈ Ts.idx, cstar * Real.sqrt N ≤ (Ts.T N).Lx) : IxSetting etaStd δstd where
  Ts := Ts
  cstar := cstar
  cstar_pos := hc
  Lx_ge := hLx
  H := fun N => HN (Ts.T N)
  d := ((hollowCore_mem_class isProfile_etaStd (Real.sqrt_pos.2 Real.pi_pos)).choose_spec.2 Ts).choose

/-! ## Assumption 6.4 -/

/-- **Assumption 6.4** (charge transport), for unitaries `U_N` and given `T_±`: "`$U=U_N$, $N\in\mathcal N$, are unitaries on $\Fock$ such that`"
"`[U,\Nup]=[U,\Ndn]=0`" (U1); "`\norm{[U,P]}=\Onf`" (U2); "`$U^*K_\pm U\in\AS_{\partial_\pm}$, with $K_\pm$ as in Definition~\ref{def:dressing}`"
(U3); "`there are self-adjoint, sector-preserving $T_\pm\in\AS_{\partial_\pm}$ with $\norm{T_\pm}\le CN^{m_T}$ such that $U^*QU-Q=T_-+T_+$ and $e^{2\pi\iu(Q+T_\pm)}=\one+\Onf$`"
(U4) — the `T_±` of (U4) as data. -/
structure TransportAssumption (D : ArgData η δ₀) (U Tm Tp : (N : ℕ) → FockOp (D.T N)) : Prop where
  unitary : ∀ N ∈ D.Ts.idx, U N ∈ unitary (FockOp (D.T N))
  U1 : ∀ N ∈ D.Ts.idx, Commute (U N) (Nsig (D.T N) .up) ∧ Commute (U N) (Nsig (D.T N) .dn)
  U2 : IsONegInf D.Ts fun (_ : Unit) N => U N * D.P N - D.P N * U N
  U3 : AlmostSupported η δ₀ D.Ts D.cutMinus (fun N => (U N)ᴴ * D.Km N * U N) ∧
    AlmostSupported η δ₀ D.Ts D.cutPlus (fun N => (U N)ᴴ * D.Kp N * U N)
  U4_sa : ∀ N ∈ D.Ts.idx, IsSelfAdjoint (Tm N) ∧ IsSelfAdjoint (Tp N) ∧ IsSectorPreserving (D.T N) (Tm N) ∧
    IsSectorPreserving (D.T N) (Tp N)
  U4_as : AlmostSupported η δ₀ D.Ts D.cutMinus Tm ∧ AlmostSupported η δ₀ D.Ts D.cutPlus Tp
  U4_norm : ∃ C mT : ℝ, ∀ N ∈ D.Ts.idx, ‖toCLM (D.T N) (Tm N)‖ ≤ C * (N : ℝ) ^ mT ∧
    ‖toCLM (D.T N) (Tp N)‖ ≤ C * (N : ℝ) ^ mT
  U4_transport : ∀ N ∈ D.Ts.idx, (U N)ᴴ * D.Q N * U N - D.Q N = Tm N + Tp N
  U4_exp : IsONegInf D.Ts (fun (_ : Unit) N => NormedSpace.exp ((2 * π * I : ℂ) • (D.Q N + Tm N)) - 1) ∧
    IsONegInf D.Ts (fun (_ : Unit) N => NormedSpace.exp ((2 * π * I : ℂ) • (D.Q N + Tp N)) - 1)

/-! ## Statements -/

/-! ### The hollow-core setting -/

/-- The (H1) data of `hcSetting` are Corollary 4.8's: the local terms `h_R` of Definition 4.1, `C_h = 7/π`, and (H2). -/
theorem hcSetting_data (Ts : TorusSeq δstd) (cstar : ℝ) (hc : 0 < cstar)
    (hLx : ∀ N ∈ Ts.idx, cstar * Real.sqrt N ≤ (Ts.T N).Lx) :
    (hcSetting Ts cstar hc hLx).d.h = (fun N => hR (Ts.T N)) ∧ (hcSetting Ts cstar hc hLx).d.Ch = ChHC ∧
      (hcSetting Ts cstar hc hLx).d.H2 := by
  obtain ⟨h1, h2, -, h4⟩ :=
    ((hollowCore_mem_class (δ₀ := δstd) isProfile_etaStd (Real.sqrt_pos.2 Real.pi_pos)).choose_spec.2 Ts).choose_spec
  exact ⟨h1, h2, h4⟩

/-! ### Proof devices for Lemma 7.1 (phase (b), round one; not statements of the paper)

The six that `Assembly.Inputs` uses (`natCast_injOn_dev` … `norm_toCLM_njs_dev`) moved there in round two. -/

section ThetaDevices

/-- The core's `Orbital` of the data at `N` with the filters replaced by `Ŵ(ω) = i/ω` and the step `1_{(−∞, −γ]}` (the
fields Lemma 7.1(d)'s trace identity does not use), so that it needs only Assumption 6.3 and (H2). -/
def orbDummy_dev (D : ArgData η δ₀) (hA : GapAssumption D.toIxSetting D.nn D.p D.Δ D.γ) (hH2 : D.d.H2) {N : ℕ}
    (hN : N ∈ D.Ts.idx) : IndexCore.Orbital (FockSpace (D.T N)) where
  H := toCLM (D.T N) (D.H N)
  H_sa := isSelfAdjoint_toCLM_dev (D.d.H_isSelfAdjoint N hN)
  Psec := toCLM (D.T N) (Psec (D.T N) (D.nn N))
  Psec_proj := (orbitalFit_spin (D.T N) .up (D.nn N)).Psec_proj
  Psec_H := commute_Psec_toCLM_dev _ (H_isSectorPreserving_dev D.toIxSetting hN)
  Nφ := (D.T N).Nφ
  N := N
  N_le_Nφ := (N_lt_Nφ_dev D hN).1.le
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
  disjoint_minus_mid := (IndexCore.quarters_partition (N_lt_Nφ_dev D hN).1.le).1
  disjoint_minus_plus := (IndexCore.quarters_partition (N_lt_Nφ_dev D hN).1.le).2.1
  disjoint_mid_plus := (IndexCore.quarters_partition (N_lt_Nφ_dev D hN).1.le).2.2.1
  bands_union := (IndexCore.quarters_partition (N_lt_Nφ_dev D hN).1.le).2.2.2
  γ := D.γ
  Δ := D.Δ
  a := D.E N 1
  b := D.E N D.p
  Δ_nonneg := hA.Δ_nonneg
  Δ_lt_γ := by linarith [hA.Δ_nonneg, hA.two_mul_Δ_lt]
  width := hA.spread N hN
  gap := fun μ v hv0 hv hHv => gap_of_secEig (D.d.H_isSelfAdjoint N hN) (H_isSectorPreserving_dev D.toIxSetting hN)
    (by linarith [hA.Δ_nonneg, hA.two_mul_Δ_lt]) (hA.gap N hN) μ v hv0 hv hHv
  Θ := toCLM (D.T N) (Θ (D.T N))
  Θ_unitary := (orbitalFit_spin (D.T N) .up (D.nn N)).Θ_unitary
  Psec_Θ := (orbitalFit_spin (D.T N) .up (D.nn N)).Psec_Θ
  Θ_H := commute_toCLM_dev (D.d.commute_Θ_of_H2 hH2 N hN)
  Θ_n := (orbitalFit_spin (D.T N) .up (D.nn N)).Θ_n
  Jminus := toCLM (D.T N) (D.Jminus N)
  Jplus := toCLM (D.T N) (D.Jplus N)
  Jminus_sa := isSelfAdjoint_toCLM_dev (J_isSelfAdjoint D.toIxSetting N hN).1
  Jplus_sa := isSelfAdjoint_toCLM_dev (J_isSelfAdjoint D.toIxSetting N hN).2.2.1
  Psec_Jminus := commute_Psec_toCLM_dev _ (J_isSelfAdjoint D.toIxSetting N hN).2.1
  Psec_Jplus := commute_Psec_toCLM_dev _ (J_isSelfAdjoint D.toIxSetting N hN).2.2.2
  current_split := by
    rw [← toCLM_add_dev, Jminus_add_Jplus D.toIxSetting N hN, toCLM_smul_dev, toCLM_sub', toCLM_mul', toCLM_mul',
      Ring.lie_def]
    unfold IxSetting.Q Qband
    rw [toCLM_sum']
  W := fun ω => I / ω
  W_eq := fun ω _ => rfl
  W_conj := fun ω => by
    rw [map_div₀, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg, div_neg, neg_div]
  g := fun ω => if ω ≤ -D.γ then 1 else 0
  g_zero := fun ω hω => if_neg (by linarith [hA.Δ_nonneg, hA.two_mul_Δ_lt])
  g_one := fun ω hω => if_pos hω

theorem orbDummy_P_dev (D : ArgData η δ₀) (hA : GapAssumption D.toIxSetting D.nn D.p D.Δ D.γ) (hH2 : D.d.H2)
    {N : ℕ} (hN : N ∈ D.Ts.idx) : (orbDummy_dev D hA hH2 hN).toSetting.P = toCLM (D.T N) (D.P N) := by
  unfold ArgData.P
  rw [toCLM_mul', toCLM_cfc_indicator (D.d.H_isSelfAdjoint N hN) (isSelfAdjoint_toCLM_dev (D.d.H_isSelfAdjoint N hN))]
  rfl

theorem orbDummy_p_dev (D : ArgData η δ₀) (hA : GapAssumption D.toIxSetting D.nn D.p D.Δ D.γ) (hH2 : D.d.H2)
    {N : ℕ} (hN : N ∈ D.Ts.idx) : (orbDummy_dev D hA hH2 hN).toSetting.p = D.p := by
  show Module.finrank ℂ (LinearMap.range ((orbDummy_dev D hA hH2 hN).toSetting.P :
    FockSpace (D.T N) →ₗ[ℂ] FockSpace (D.T N))) = D.p
  rw [orbDummy_P_dev D hA hH2 hN, ← ArgData.rank_P D hA N hN,
    Matrix.rank_eq_finrank_range_toLin _ (EuclideanSpace.basisFun (Conf (ZMod (D.T N).Nφ)) ℂ).toBasis
      (EuclideanSpace.basisFun (Conf (ZMod (D.T N).Nφ)) ℂ).toBasis]
  rfl

end ThetaDevices

/-! ### Lemma 7.1 (the magnetic translation transports one orbital) -/

/-- **Lemma 7.1(a)**: "`$[\Theta,\Nup]=[\Theta,\Ndn]=0$, $[\Theta,H_N]=0$, and $[\Theta,P]=0$.`" -/
theorem theta_commute (D : ArgData η δ₀) (hA : GapAssumption D.toIxSetting D.nn D.p D.Δ D.γ) (hH2 : D.d.H2) :
    ∀ N ∈ D.Ts.idx, Commute (Θ (D.T N)) (Nsig (D.T N) .up) ∧ Commute (Θ (D.T N)) (Nsig (D.T N) .dn) ∧
      Commute (Θ (D.T N)) (D.H N) ∧ Commute (Θ (D.T N)) (D.P N) := by
  intro N hN
  have hΘs := Θ_isSectorPreserving (D.T N)
  have hΘH := D.d.commute_Θ_of_H2 hH2 N hN
  refine ⟨hΘs.1, hΘs.2, hΘH, ?_⟩
  have hH := D.d.H_isSelfAdjoint N hN
  have h1 : Commute (cfc ((Set.Icc (D.E N 1) (D.E N D.p)).indicator (1 : ℝ → ℝ)) (D.H N)) (Θ (D.T N)) :=
    Commute.cfc (𝕜 := ℝ) hΘH.symm (by rw [hH.star_eq]; exact hΘH.symm) _
  have h2 : Commute (Psec (D.T N) (D.nn N)) (Θ (D.T N)) :=
    ((isSectorPreserving_iff_commute _ _).mp hΘs (D.nn N)).symm
  unfold ArgData.P
  exact (h1.mul_left h2).symm

/-- **Lemma 7.1(b)**: "`$\Theta^*Q\Theta-Q=n_{N\up}-n_{0\up}$. With $T_-:=-n_{0\up}$ and $T_+:=n_{N\up}$, the operators $T_\pm$ are self-adjoint and sector-preserving, $\norm{T_\pm}=1$, $\iota(T_\pm)\in\Alg(\partial_\pm)$, and $\Theta^*Q\Theta-Q=T_-+T_+$.`" -/
theorem theta_transport (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) :
    ∀ N ∈ D.Ts.idx,
      (Θ (D.T N))ᴴ * D.Q N * Θ (D.T N) - D.Q N =
          njs (D.T N) (N : ZMod (D.T N).Nφ) .up - njs (D.T N) 0 .up ∧
        IsSelfAdjoint (D.Tminus N) ∧ IsSectorPreserving (D.T N) (D.Tminus N) ∧
        IsSelfAdjoint (D.Tplus N) ∧ IsSectorPreserving (D.T N) (D.Tplus N) ∧
        ‖toCLM (D.T N) (D.Tminus N)‖ = 1 ∧ ‖toCLM (D.T N) (D.Tplus N)‖ = 1 ∧
        iota η δ₀ (D.T N) (D.Tminus N) ∈ Alg (D.cutMinus N) ∧ iota η δ₀ (D.T N) (D.Tplus N) ∈ Alg (D.cutPlus N) ∧
        (Θ (D.T N))ᴴ * D.Q N * Θ (D.T N) - D.Q N = D.Tminus N + D.Tplus N := by
  intro N hN
  obtain ⟨hlt, hpos⟩ := N_lt_Nφ_dev D hN
  have hT := D.Ts.admissible N hN
  have hP0 := isStarProjection_njs (D.T N) 0 .up
  have hPN := isStarProjection_njs (D.T N) (N : ZMod (D.T N).Nφ) .up
  have hι0 := iota_njs_mem_Alg hη hδ₀ hT (0 : ZMod (D.T N).Nφ)
  rw [ZMod.val_zero, Nat.cast_zero] at hι0
  have hιN := iota_njs_mem_Alg hη hδ₀ hT (N : ZMod (D.T N).Nφ)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hιN
  have htr := theta_transport_dev D hN
  refine ⟨htr, hP0.isSelfAdjoint.neg, ⟨(njs_commute_Nsig _ _ _ _).neg_left, (njs_commute_Nsig _ _ _ _).neg_left⟩,
    hPN.isSelfAdjoint, ⟨njs_commute_Nsig _ _ _ _, njs_commute_Nsig _ _ _ _⟩, ?_, norm_toCLM_njs_dev _ _, ?_, hιN, ?_⟩
  · unfold ArgData.Tminus
    rw [toCLM_neg_dev, norm_neg, norm_toCLM_njs_dev]
  · unfold ArgData.Tminus
    rw [← iotaHom_apply hη hδ₀ hT, map_neg, iotaHom_apply hη hδ₀ hT, ← neg_one_smul ℂ]
    exact Alg_smul_mem _ hι0
  · rw [htr]
    unfold ArgData.Tminus ArgData.Tplus
    abel

/-- **Lemma 7.1(c)**: "`$e^{2\pi\iu(Q+T_-)}=e^{2\pi\iu(Q+T_+)}=\one$; moreover $e^{2\pi\iu(Q_++T_+)}=e^{2\pi\iu Q_m}=\one$.`" -/
theorem theta_exp (D : ArgData η δ₀) :
    ∀ N ∈ D.Ts.idx,
      NormedSpace.exp ((2 * π * I : ℂ) • (D.Q N + D.Tminus N)) = 1 ∧
      NormedSpace.exp ((2 * π * I : ℂ) • (D.Q N + D.Tplus N)) = 1 ∧
      NormedSpace.exp ((2 * π * I : ℂ) • (D.Qplus N + D.Tplus N)) = 1 ∧
      NormedSpace.exp ((2 * π * I : ℂ) • D.Qmid N) = 1 := by
  intro N hN
  obtain ⟨hlt, hpos⟩ := N_lt_Nφ_dev D hN
  have h0 : (0 : ZMod (D.T N).Nφ) ∈ bandΓ (D.T N).Nφ N :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hpos, Nat.cast_zero⟩
  have hNΓ : (N : ZMod (D.T N).Nφ) ∉ bandΓ (D.T N).Nφ N := by
    unfold bandΓ
    rw [natCast_mem_image_range_dev hlt.le hlt]
    omega
  have hNp : (N : ZMod (D.T N).Nφ) ∉ quarterPlus (D.T N).Nφ N := by
    unfold quarterPlus
    intro h
    obtain ⟨k, hk, hkN⟩ := Finset.mem_image.mp h
    rw [Finset.mem_Ico] at hk
    have := natCast_injOn_dev (n := (D.T N).Nφ) (m := (D.T N).Nφ) le_rfl
      (by simp only [Finset.coe_range, Set.mem_Iio]; omega) (by simp only [Finset.coe_range, Set.mem_Iio]; omega) hkN
    omega
  have e1 : D.Q N + D.Tminus N = Qband (D.T N) ((bandΓ (D.T N).Nφ N).erase 0) := by
    unfold IxSetting.Q ArgData.Tminus Qband
    rw [Finset.sum_erase_eq_sub h0]
    abel
  have e2 : D.Q N + D.Tplus N = Qband (D.T N) (insert (N : ZMod (D.T N).Nφ) (bandΓ (D.T N).Nφ N)) := by
    unfold IxSetting.Q ArgData.Tplus Qband
    rw [Finset.sum_insert hNΓ]
    abel
  have e3 : D.Qplus N + D.Tplus N = Qband (D.T N) (insert (N : ZMod (D.T N).Nφ) (quarterPlus (D.T N).Nφ N)) := by
    unfold IxSetting.Qplus ArgData.Tplus Qband
    rw [Finset.sum_insert hNp]
    abel
  rw [e1, e2, e3]
  exact ⟨exp_Qband _ _, exp_Qband _ _, exp_Qband _ _, exp_Qband _ _⟩

/-- **Lemma 7.1(d)**: "`$\Tr(Pn_{j\up})=p\,n_{\up,N}/\Nphi$ for every $j\in\Z_{\Nphi}$; in particular $\Tr(PT_-)=-p\,n_{\up,N}/\Nphi$.`" -/
theorem theta_trace (D : ArgData η δ₀) (hA : GapAssumption D.toIxSetting D.nn D.p D.Δ D.γ) (hH2 : D.d.H2) :
    ∀ N ∈ D.Ts.idx,
      (∀ j : ZMod (D.T N).Nφ,
        Matrix.trace (D.P N * njs (D.T N) j .up) = (D.p : ℂ) * ((D.nn N).1 : ℕ) / (D.T N).Nφ) ∧
      Matrix.trace (D.P N * D.Tminus N) = -((D.p : ℂ) * ((D.nn N).1 : ℕ) / (D.T N).Nφ) := by
  intro N hN
  have hP := orbDummy_P_dev D hA hH2 hN
  have hp := orbDummy_p_dev D hA hH2 hN
  have hj : ∀ j : ZMod (D.T N).Nφ,
      Matrix.trace (D.P N * njs (D.T N) j .up) = (D.p : ℂ) * ((D.nn N).1 : ℕ) / (D.T N).Nφ := by
    intro j
    rw [← trc_toCLM (T := D.T N), toCLM_mul', ← hP]
    have h1 := (orbDummy_dev D hA hH2 hN).trc_P_n j
    rw [hp] at h1
    exact h1
  refine ⟨hj, ?_⟩
  unfold ArgData.Tminus
  rw [mul_neg, Matrix.trace_neg, hj 0]

/-- **Lemma 7.1(e)**: "`$\Theta^*K_\pm\Theta\in\AS_{\partial_\pm}$, and $\Tr(P\,\Theta^*K_-\Theta)=\Tr(PK_-)$; hence $\Tr(P\Tt)=\Tr(PT_-)$ exactly.`"
— with the prefactor exponent `5/2` of its proof. -/
theorem theta_dressing (hη : IsProfile η) (hδ₀ : 0 < δ₀) (D : ArgData η δ₀) (hD : D.Valid) (hH2 : D.d.H2) :
    (∃ C : ℕ → ℝ, ASBound η δ₀ D.Ts D.cutMinus D.KUminus (5 / 2) C ∧
      ASBound η δ₀ D.Ts D.cutPlus D.KUplus (5 / 2) C) ∧
    ∀ N ∈ D.Ts.idx, Matrix.trace (D.P N * D.KUminus N) = Matrix.trace (D.P N * D.Km N) ∧
      Matrix.trace (D.P N * D.Ttilde N) = Matrix.trace (D.P N * D.Tminus N) := by
  obtain ⟨-, -, C, -, -, h3, h4⟩ := table_K hη hδ₀ D hD hH2
  refine ⟨⟨C, h3, h4⟩, fun N hN => ?_⟩
  have hc := (theta_commute D hD.gap hH2 N hN).2.2.2
  have hu : Θ (D.T N) * (Θ (D.T N))ᴴ = 1 := mul_conjTranspose_self_of_mem_unitary (Θ_mem_unitary _)
  have h1 : Matrix.trace (D.P N * D.KUminus N) = Matrix.trace (D.P N * D.Km N) := by
    unfold ArgData.KUminus
    rw [← mul_assoc (D.P N), Matrix.trace_mul_comm (D.P N * ((Θ (D.T N))ᴴ * D.Km N)) (Θ (D.T N)),
      ← mul_assoc (Θ (D.T N)) (D.P N), hc.eq, mul_assoc (D.P N), ← mul_assoc (Θ (D.T N)) (Θ (D.T N))ᴴ, hu,
      one_mul]
  refine ⟨h1, ?_⟩
  unfold ArgData.Ttilde
  rw [mul_add, mul_sub, Matrix.trace_add, Matrix.trace_sub, h1]
  ring

/-! ### Corollary 7.2 (the translation corollary) -/

/-- **Corollary 7.2**: "`In Setting~\ref{set:index}, let $H$ satisfy (H1) and (H2), and let Assumption~\ref{ass:gap} hold for sectors $\nn_N=(n_{\up,N},n_{\dn,N})$. Then $U=\Theta$ satisfies Assumption~\ref{ass:U}, with $T_\pm$ as in Lemma~\ref{lem:theta}, and with (U2) and the two relations in (U4) holding exactly; and there are integers $n_N$ such that for every $k$ there is $C_k$ with`"
"`\Bigl\lvert\,p\,\frac{n_{\up,N}}{\Nphi}-n_N\Bigr\rvert\le C_kN^{-k}\qquad\text{for all }N\in\mathcal N .`"
— for the data `ArgData.std` (the fixed filters). -/
theorem translation_corollary (hη : IsProfile η) (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) (hH2 : S.d.H2)
    {nn : (N : ℕ) → SectorLabel (S.T N)} {p : ℕ} {Δ γ : ℝ} (hA : GapAssumption S nn p Δ γ) :
    TransportAssumption (ArgData.std S nn p Δ γ) (fun N => Θ (S.T N)) (ArgData.std S nn p Δ γ).Tminus
        (ArgData.std S nn p Δ γ).Tplus ∧
      (∀ N ∈ S.Ts.idx, Commute (Θ (S.T N)) ((ArgData.std S nn p Δ γ).P N)) ∧
      (∀ N ∈ S.Ts.idx,
        (Θ (S.T N))ᴴ * S.Q N * Θ (S.T N) - S.Q N =
            (ArgData.std S nn p Δ γ).Tminus N + (ArgData.std S nn p Δ γ).Tplus N ∧
          NormedSpace.exp ((2 * π * I : ℂ) • (S.Q N + (ArgData.std S nn p Δ γ).Tminus N)) = 1 ∧
          NormedSpace.exp ((2 * π * I : ℂ) • (S.Q N + (ArgData.std S nn p Δ γ).Tplus N)) = 1) ∧
      ∃ n : ℕ → ℤ, ∀ k : ℕ, ∃ C : ℝ, ∀ N ∈ S.Ts.idx,
        |(p : ℝ) * ((nn N).1 : ℕ) / (S.T N).Nφ - n N| ≤ C * (N : ℝ) ^ (-(k : ℝ)) := by
  classical
  have hDv : (ArgData.std S nn p Δ γ).Valid := ArgData.valid_std hA
  obtain ⟨hTe, hTm, hTp⟩ := table_T hη hδ₀ (ArgData.std S nn p Δ γ)
  obtain ⟨⟨C, hKUm, hKUp⟩, -⟩ := theta_dressing hη hδ₀ _ hDv hH2
  have hc := theta_commute (ArgData.std S nn p Δ γ) hA hH2
  have htr := theta_transport hη hδ₀ (ArgData.std S nn p Δ γ)
  have hex := theta_exp (ArgData.std S nn p Δ γ)
  have hzero : ∀ a : (N : ℕ) → FockOp (S.T N), (∀ N ∈ S.Ts.idx, a N = 0) →
      IsONegInf (ArgData.std S nn p Δ γ).Ts fun (_ : Unit) N => a N := by
    intro a ha k
    refine ⟨0, fun _ N hN => ?_⟩
    dsimp only
    rw [ha N hN, toCLM_zero_dev, norm_zero, zero_mul]
  refine ⟨⟨fun N _ => Θ_mem_unitary _, fun N hN => ⟨(hc N hN).1, (hc N hN).2.1⟩,
    hzero _ fun N hN => by rw [(hc N hN).2.2.2.eq, sub_self], ⟨⟨⟨_, _, hKUm⟩⟩, ⟨⟨_, _, hKUp⟩⟩⟩,
    fun N hN => ⟨(htr N hN).2.1, (htr N hN).2.2.2.1, (htr N hN).2.2.1, (htr N hN).2.2.2.2.1⟩,
    ⟨⟨⟨_, _, hTm⟩⟩, ⟨⟨_, _, hTp⟩⟩⟩, ⟨1, 0, fun N hN => ?_⟩, fun N hN => (htr N hN).2.2.2.2.2.2.2.2.2,
    hzero _ fun N hN => by rw [(hex N hN).1, sub_self], hzero _ fun N hN => by rw [(hex N hN).2.1, sub_self]⟩,
    fun N hN => (hc N hN).2.2.2, fun N hN => ⟨(htr N hN).2.2.2.2.2.2.2.2.2, (hex N hN).1, (hex N hN).2.1⟩, ?_⟩
  · rw [Real.rpow_zero, mul_one, (hTe N hN).2.2.1, (hTe N hN).2.2.2.2.2]
    exact ⟨le_rfl, le_rfl⟩
  have key : ∀ N ∈ S.Ts.idx, ∃ m : ℤ, |(p : ℝ) * ((nn N).1 : ℕ) / (S.T N).Nφ - m| ≤
      400 * (p : ℝ) * ((ArgData.std S nn p Δ γ).Mb N + 1) * Real.sqrt ((ArgData.std S nn p Δ γ).eps N) := by
    intro N hN
    have h := obligations _ hDv hH2 N hN
    obtain ⟨m, hm⟩ := IndexCore.Orbital.translation_corollary (inputs_orbOf _ hDv hN h)
    rw [orbOf_p _ hDv hN h] at hm
    exact ⟨m, hm⟩
  choose! n hn using key
  refine ⟨n, fun k => ?_⟩
  obtain ⟨C₁, hC₁⟩ := eps_isONegInf hη hδ₀ _ hDv hH2 (2 * k + 4)
  exact ⟨400 * (p : ℝ) * (|1 + 4 * π * S.d.Ch * moment (Wfilt cutoff γ) 0| + 1) * Real.sqrt |C₁|,
    fun N hN => (hn N hN).trans (limit_bound_dev (one_le_of_mem_idx S.Ts hN)
      (c₀ := 1 + 4 * π * S.d.Ch * moment (Wfilt cutoff γ) 0) k p (hC₁ N hN))⟩

/-! ### Corollary 7.3 (half filling with zero spin polarization) -/

/-- **Corollary 7.3**: "`Let $\mathcal N$ consist of even integers, let the tori and $H$ be as in Setting~\ref{set:index} with (H1) and (H2), and suppose that Assumption~\ref{ass:gap} holds for the sectors $\nn_N=(N/2,N/2)$, $N\in\mathcal N$. Then $p\in4\Z$.`"
— its proof: the core's `four_dvd_p` at one `N ∈ 𝒩` beyond `eventually_small`'s threshold ("`$\mathcal N$ is infinite, hence unbounded`"). -/
theorem four_dvd_of_halfFilling (hη : IsProfile η) (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) (hH2 : S.d.H2)
    (heven : ∀ N ∈ S.Ts.idx, Even N) {p : ℕ} {Δ γ : ℝ}
    (hA : GapAssumption S (fun N => halfSector (S.T N)) p Δ γ) : 4 ∣ p := by
  have hDv : (ArgData.std S (fun N => halfSector (S.T N)) p Δ γ).Valid := ArgData.valid_std hA
  obtain ⟨N₀, hN₀⟩ := eventually_small hη hδ₀ _ hDv hH2
  obtain ⟨N, hN, hlt⟩ := S.Ts.idx_infinite.exists_gt N₀
  have h := obligations _ hDv hH2 N hN
  have hq : 4 * (orbOf _ N hN h).nup = (orbOf _ N hN h).Nφ := by
    show 4 * ((S.T N).N / 2) = 2 * (S.T N).N
    obtain ⟨m, hm⟩ := heven N hN
    have hTN : (S.T N).N = N := S.Ts.T_N N hN
    omega
  have hs := hN₀ N hN hlt.le
  rw [← orbOf_p _ hDv hN h] at hs
  have h4 := IndexCore.Orbital.four_dvd_p (inputs_orbOf _ hDv hN h) hq hs
  rwa [orbOf_p _ hDv hN h] at h4

/-- **Corollary 7.3 for the hollow-core model**: along an infinite set of even `N` with `L_x ≥ c_*√N`, Assumption 6.3 for
the hollow-core Hamiltonians in the sectors `(N/2, N/2)` gives `4 ∣ p` (`four_dvd_of_halfFilling` for `hcSetting`). -/
theorem four_dvd_hollowCore (Ts : TorusSeq δstd) (cstar : ℝ) (hc : 0 < cstar)
    (hLx : ∀ N ∈ Ts.idx, cstar * Real.sqrt N ≤ (Ts.T N).Lx) (heven : ∀ N ∈ Ts.idx, Even N) {p : ℕ} {Δ γ : ℝ}
    (hA : GapAssumption (hcSetting Ts cstar hc hLx) (fun N => halfSector (Ts.T N)) p Δ γ) : 4 ∣ p :=
  four_dvd_of_halfFilling isProfile_etaStd (Real.sqrt_pos.2 Real.pi_pos) (hcSetting Ts cstar hc hLx)
    (hcSetting_data Ts cstar hc hLx).2.2 heven hA

/-- **Corollary 7.3**: "`In particular, no Hamiltonian satisfying (H1) and (H2) has, in the sectors $(N/2,N/2)$ along an infinite set of even $N$, a uniformly gapped patch at the bottom of the spectrum (in the sense of Section~\ref{sec:intro}) whose dimension is not divisible by four; for instance, of dimension ten.`" -/
theorem no_gapped_patch (hη : IsProfile η) (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) (hH2 : S.d.H2)
    (heven : ∀ N ∈ S.Ts.idx, Even N) {p : ℕ} (hp : ¬ 4 ∣ p) (Δ γ : ℝ) :
    ¬ GapAssumption S (fun N => halfSector (S.T N)) p Δ γ :=
  fun hA => hp (four_dvd_of_halfFilling hη hδ₀ S hH2 heven hA)

/-! ### Corollary 7.4 (odd `N` and spin one half) -/

/-! #### Proof devices for Corollary 7.4 (phase (b), round two; not statements of the paper)

The setting restricted to an infinite subset `𝒩' ⊆ 𝒩` (`restrict_dev`: "`The tori and $H$, restricted to $\mathcal N'$, are
as in Setting~\ref{set:index} with (H1) and (H2)`"), so that Corollary 7.2 applies along `𝒩'`; and the arithmetic of (i)
(`odd_contra_dev`): `p/4 ± p/(4N)` is not within `b < min{1/8, p/(4N)}` of an integer `k` when `p ≥ 1` and
`N ≥ 2p` — the paper's two cases `p ∉ 4ℤ` and `p ∈ 4ℤ` become `p − 4k ≠ 0` and `p − 4k = 0`. -/

section OddDevices

/-- The setting restricted to `M ⊆ 𝒩` infinite: the same tori, `c_*`, Hamiltonians and (H1) data. -/
def restrict_dev (S : IxSetting η δ₀) (M : Set ℕ) (hM : M ⊆ S.Ts.idx) (hMi : M.Infinite) : IxSetting η δ₀ where
  Ts := ⟨M, hMi, S.Ts.T, fun N hN => S.Ts.T_N N (hM hN), fun N hN => S.Ts.admissible N (hM hN)⟩
  cstar := S.cstar
  cstar_pos := S.cstar_pos
  Lx_ge := fun N hN => S.Lx_ge N (hM hN)
  H := S.H
  d := ⟨S.d.h, S.d.Ch, S.d.CH, fun N hN => S.d.H_isSelfAdjoint N (hM hN), fun N hN => S.d.eq_opIntegral N (hM hN),
    fun N hN => S.d.h_add_Lx N (hM hN), fun N hN => S.d.h_add_Ly N (hM hN), fun N hN => S.d.h_measurable N (hM hN),
    fun N hN => S.d.h_isSelfAdjoint N (hM hN), fun N hN => S.d.h_isSectorPreserving N (hM hN),
    fun N hN => S.d.norm_h_le N (hM hN), fun k N hN => S.d.approx k N (hM hN)⟩

theorem restrict_H2_dev (S : IxSetting η δ₀) {M : Set ℕ} (hM : M ⊆ S.Ts.idx) (hMi : M.Infinite) (hH2 : S.d.H2) :
    (restrict_dev S M hM hMi).d.H2 :=
  fun N hN R => hH2 N (hM hN) R

theorem odd_contra_dev {p : ℕ} (hp : 1 ≤ p) {N : ℕ} (hN : 2 * p ≤ N) {σ b : ℝ} (hσ : |σ| = 1) (k : ℤ)
    (hb1 : b < 1 / 8) (hb2 : b < (p : ℝ) / (4 * N)) (h : |(p : ℝ) / 4 + σ * ((p : ℝ) / (4 * N)) - k| ≤ b) :
    False := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hN' : (2 : ℝ) * p ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hy0 : 0 < (p : ℝ) / (4 * N) := by positivity
  have hy1 : (p : ℝ) / (4 * N) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hσy : |σ * ((p : ℝ) / (4 * N))| = (p : ℝ) / (4 * N) := by rw [abs_mul, hσ, one_mul, abs_of_pos hy0]
  rcases eq_or_ne ((p : ℤ) - 4 * k) 0 with hm | hm
  · have h' : ((p : ℝ) - 4 * k) = 0 := by exact_mod_cast hm
    have e2 : (p : ℝ) / 4 + σ * ((p : ℝ) / (4 * N)) - k = σ * ((p : ℝ) / (4 * N)) := by linarith
    rw [e2, hσy] at h
    linarith
  · have h1 : (1 : ℝ) ≤ |(p : ℝ) - 4 * k| := by
      have h0 : (1 : ℤ) ≤ |(p : ℤ) - 4 * k| := Int.one_le_abs hm
      exact_mod_cast h0
    have h2 : (1 : ℝ) / 4 ≤ |(p : ℝ) / 4 - k| := by
      have e : (p : ℝ) / 4 - k = ((p : ℝ) - 4 * k) / 4 := by ring
      rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith
    have h3 := abs_sub_abs_le_abs_sub ((p : ℝ) / 4 - k) (-(σ * ((p : ℝ) / (4 * N))))
    have e3 : (p : ℝ) / 4 - k - -(σ * ((p : ℝ) / (4 * N))) = (p : ℝ) / 4 + σ * ((p : ℝ) / (4 * N)) - k := by ring
    rw [e3, abs_neg, hσy] at h3
    linarith

end OddDevices

/-- **Corollary 7.4(i)**: "`There are no $p\in\N$, $\Delta\ge0$ and $\gamma>2\Delta$ for which Assumption~\ref{ass:gap} holds for the sectors $\nn^+_N$ along an infinite subset of $\mathcal N$; and likewise for $\nn^-_N$.`" -/
theorem no_gap_odd (hη : IsProfile η) (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) (hH2 : S.d.H2)
    (hodd : ∀ N ∈ S.Ts.idx, Odd N) :
    (¬ ∃ (p : ℕ) (Δ γ : ℝ), 0 ≤ Δ ∧ 2 * Δ < γ ∧ ∃ M ⊆ S.Ts.idx, M.Infinite ∧ ∀ N ∈ M,
      secEig (S.T N) (S.H N) (oddSectorPlus (S.T N)) p - secEig (S.T N) (S.H N) (oddSectorPlus (S.T N)) 1 ≤ Δ ∧
        γ ≤ secEig (S.T N) (S.H N) (oddSectorPlus (S.T N)) (p + 1) -
          secEig (S.T N) (S.H N) (oddSectorPlus (S.T N)) p) ∧
    (¬ ∃ (p : ℕ) (Δ γ : ℝ), 0 ≤ Δ ∧ 2 * Δ < γ ∧ ∃ M ⊆ S.Ts.idx, M.Infinite ∧ ∀ N ∈ M,
      secEig (S.T N) (S.H N) (oddSectorMinus (S.T N)) p - secEig (S.T N) (S.H N) (oddSectorMinus (S.T N)) 1 ≤ Δ ∧
        γ ≤ secEig (S.T N) (S.H N) (oddSectorMinus (S.T N)) (p + 1) -
          secEig (S.T N) (S.H N) (oddSectorMinus (S.T N)) p) := by
  have key : ∀ (sec : (T : Torus) → SectorLabel T) (σ : ℝ), |σ| = 1 →
      (∀ N ∈ S.Ts.idx, ∀ q : ℝ, q * (((sec (S.T N)).1 : ℕ) : ℝ) / ((S.T N).Nφ : ℝ) = q / 4 + σ * (q / (4 * N))) →
      ¬ ∃ (p : ℕ) (Δ γ : ℝ), 0 ≤ Δ ∧ 2 * Δ < γ ∧ ∃ M ⊆ S.Ts.idx, M.Infinite ∧ ∀ N ∈ M,
        secEig (S.T N) (S.H N) (sec (S.T N)) p - secEig (S.T N) (S.H N) (sec (S.T N)) 1 ≤ Δ ∧
          γ ≤ secEig (S.T N) (S.H N) (sec (S.T N)) (p + 1) - secEig (S.T N) (S.H N) (sec (S.T N)) p := by
    rintro sec σ hσ hrel ⟨p, Δ, γ, hΔ, hγ, M, hM, hMi, hgap⟩
    have hA : GapAssumption (restrict_dev S M hM hMi) (fun N => sec ((restrict_dev S M hM hMi).T N)) p Δ γ :=
      ⟨hΔ, hγ, fun N hN => (hgap N hN).1, fun N hN => (hgap N hN).2⟩
    obtain ⟨-, -, -, n, hn⟩ := translation_corollary hη hδ₀ (restrict_dev S M hM hMi)
      (restrict_H2_dev S hM hMi hH2) hA
    obtain ⟨C, hC⟩ := hn 2
    obtain ⟨N1, hN1M⟩ := hMi.nonempty
    have hp : 1 ≤ p := (one_le_p_lt_finrank (Δ := Δ) (by linarith) (hgap N1 hN1M).2).1
    obtain ⟨N, hNM, hNlt⟩ := hMi.exists_gt (2 * p + ⌈8 * |C|⌉₊ + ⌈4 * |C|⌉₊ + 1)
    have hNi : N ∈ S.Ts.idx := hM hNM
    have h : |(p : ℝ) / 4 + σ * ((p : ℝ) / (4 * N)) - n N| ≤ C * (N : ℝ) ^ (-((2 : ℕ) : ℝ)) := by
      rw [← hrel N hNi p]
      exact hC N hNM
    have hN1 : (1 : ℝ) ≤ N := by
      have : 1 ≤ N := by omega
      exact_mod_cast this
    have h8 : 8 * |C| < (N : ℝ) := by
      have h1 := Nat.le_ceil (8 * |C|)
      have h2 : ((2 * p + ⌈8 * |C|⌉₊ + ⌈4 * |C|⌉₊ + 1 : ℕ) : ℝ) < N := by exact_mod_cast hNlt
      push_cast at h2
      have : (0 : ℝ) ≤ ⌈4 * |C|⌉₊ := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      linarith
    have h4 : 4 * |C| < (N : ℝ) := by linarith [abs_nonneg C]
    have hpow : (N : ℝ) ^ (-((2 : ℕ) : ℝ)) = 1 / (N : ℝ) ^ 2 := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]
    have hb : C * (N : ℝ) ^ (-((2 : ℕ) : ℝ)) ≤ |C| / (N : ℝ) ^ 2 := by
      rw [hpow, mul_one_div]
      exact div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hb1 : |C| / (N : ℝ) ^ 2 < 1 / 8 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hb2 : |C| / (N : ℝ) ^ 2 < (p : ℝ) / (4 * N) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [abs_nonneg C]
    exact odd_contra_dev hp (by omega) hσ (n N) (hb.trans_lt hb1) (hb.trans_lt hb2) h
  have hφ : ∀ N ∈ S.Ts.idx, ((S.T N).Nφ : ℝ) = 2 * N := fun N hN => by
    show (((2 * (S.T N).N) : ℕ) : ℝ) = 2 * N
    rw [S.Ts.T_N N hN, Nat.cast_mul, Nat.cast_ofNat]
  refine ⟨key oddSectorPlus 1 (by norm_num) fun N hN q => ?_, key oddSectorMinus (-1) (by norm_num) fun N hN q => ?_⟩
  · obtain ⟨m, hm⟩ := hodd N hN
    have h1 : (((oddSectorPlus (S.T N)).1 : ℕ) : ℝ) = m + 1 := by
      show ((((S.T N).N + 1) / 2 : ℕ) : ℝ) = m + 1
      have e : ((S.T N).N + 1) / 2 = m + 1 := by rw [S.Ts.T_N N hN, hm]; omega
      rw [e, Nat.cast_add, Nat.cast_one]
    have hm' : (N : ℝ) = 2 * m + 1 := by rw [hm]; push_cast; ring
    have hne : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    rw [h1, hφ N hN, hm']
    field_simp
    ring
  · obtain ⟨m, hm⟩ := hodd N hN
    have h1 : (((oddSectorMinus (S.T N)).1 : ℕ) : ℝ) = m := by
      show ((((S.T N).N - 1) / 2 : ℕ) : ℝ) = m
      have e : ((S.T N).N - 1) / 2 = m := by rw [S.Ts.T_N N hN, hm]; omega
      rw [e]
    have hm' : (N : ℝ) = 2 * m + 1 := by rw [hm]; push_cast; ring
    have hne : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    rw [h1, hφ N hN, hm']
    field_simp
    ring

/-- **Corollary 7.4(ii)**: "`For every $D\in\N$ and $\gamma>0$, for all but finitely many $N\in\mathcal N$ the restriction of $H_N$ to $\sect{\nn^\pm_N}$ has more than $D$ eigenvalues, counted with multiplicity, in $[E_1(N),E_1(N)+\gamma)$, where $E_1(N)$ is its lowest eigenvalue.`"
— the paper's `D` is `Dc` here. -/
theorem many_low_odd (hη : IsProfile η) (hδ₀ : 0 < δ₀) (S : IxSetting η δ₀) (hH2 : S.d.H2)
    (hodd : ∀ N ∈ S.Ts.idx, Odd N) (Dc : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    {N ∈ S.Ts.idx | ¬ Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (S.T N) (oddSectorPlus (S.T N))))).filter
        fun k => secEig (S.T N) (S.H N) (oddSectorPlus (S.T N)) k ∈
          Set.Ico (secEig (S.T N) (S.H N) (oddSectorPlus (S.T N)) 1)
            (secEig (S.T N) (S.H N) (oddSectorPlus (S.T N)) 1 + γ)).card}.Finite ∧
    {N ∈ S.Ts.idx | ¬ Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (S.T N) (oddSectorMinus (S.T N))))).filter
        fun k => secEig (S.T N) (S.H N) (oddSectorMinus (S.T N)) k ∈
          Set.Ico (secEig (S.T N) (S.H N) (oddSectorMinus (S.T N)) 1)
            (secEig (S.T N) (S.H N) (oddSectorMinus (S.T N)) 1 + γ)).card}.Finite := by
  obtain ⟨hng1, hng2⟩ := no_gap_odd hη hδ₀ S hH2 hodd
  have key : ∀ sec : (T : Torus) → SectorLabel T,
      (∀ N ∈ S.Ts.idx, 2 * Dc + 1 ≤ N → Dc + 1 ≤ Module.finrank ℂ (sector (S.T N) (sec (S.T N)))) →
      (¬ ∃ (p : ℕ) (Δ γ : ℝ), 0 ≤ Δ ∧ 2 * Δ < γ ∧ ∃ M ⊆ S.Ts.idx, M.Infinite ∧ ∀ N ∈ M,
        secEig (S.T N) (S.H N) (sec (S.T N)) p - secEig (S.T N) (S.H N) (sec (S.T N)) 1 ≤ Δ ∧
          γ ≤ secEig (S.T N) (S.H N) (sec (S.T N)) (p + 1) - secEig (S.T N) (S.H N) (sec (S.T N)) p) →
      {N ∈ S.Ts.idx | ¬ Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (S.T N) (sec (S.T N))))).filter
        fun k => secEig (S.T N) (S.H N) (sec (S.T N)) k ∈
          Set.Ico (secEig (S.T N) (S.H N) (sec (S.T N)) 1)
            (secEig (S.T N) (S.H N) (sec (S.T N)) 1 + γ)).card}.Finite := by
    intro sec hdim hng
    rw [← Set.not_infinite]
    intro hinf
    -- one `N`: a pair `(i, p)` with `E_p - E_1 ≤ γ/4^{i+1}` and `E_{p+1} - E_p ≥ 3γ/4^{i+1}`
    have hpair : ∀ N ∈ S.Ts.idx, 2 * Dc + 1 ≤ N →
        ¬ Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (S.T N) (sec (S.T N))))).filter
          fun k => secEig (S.T N) (S.H N) (sec (S.T N)) k ∈
            Set.Ico (secEig (S.T N) (S.H N) (sec (S.T N)) 1)
              (secEig (S.T N) (S.H N) (sec (S.T N)) 1 + γ)).card →
        ∃ q : Fin (Dc + 1) × Fin (Dc + 1),
          secEig (S.T N) (S.H N) (sec (S.T N)) q.2 - secEig (S.T N) (S.H N) (sec (S.T N)) 1 ≤
              γ / 4 ^ ((q.1 : ℕ) + 1) ∧
            3 * (γ / 4 ^ ((q.1 : ℕ) + 1)) ≤ secEig (S.T N) (S.H N) (sec (S.T N)) ((q.2 : ℕ) + 1) -
              secEig (S.T N) (S.H N) (sec (S.T N)) q.2 := by
      intro N hN hN2 hcnt
      push_neg at hcnt
      set E := secEig (S.T N) (S.H N) (sec (S.T N)) with hEdef
      have hmono : Monotone E := secEig_mono _ _ _
      have hd := hdim N hN hN2
      -- `E_{Dc+1} ≥ E_1 + γ`
      have hA : E 1 + γ ≤ E (Dc + 1) := by
        by_contra hlt
        push_neg at hlt
        have hsub : Finset.Icc 1 (Dc + 1) ⊆ (Finset.Icc 1 (Module.finrank ℂ (sector (S.T N) (sec (S.T N))))).filter
            fun k => E k ∈ Set.Ico (E 1) (E 1 + γ) := by
          intro k hk
          rw [Finset.mem_Icc] at hk
          rw [Finset.mem_filter, Finset.mem_Icc, Set.mem_Ico]
          exact ⟨⟨hk.1, hk.2.trans hd⟩, hmono hk.1, (hmono hk.2).trans_lt hlt⟩
        have := Finset.card_le_card hsub
        rw [Nat.card_Icc] at this
        omega
      -- the counts at the scales `γ / 4^i`
      set c : ℕ → ℕ := fun i => ((Finset.Icc 1 (Dc + 1)).filter fun j => E j < E 1 + γ / 4 ^ i).card with hc
      have hs : ∀ i : ℕ, 0 < γ / 4 ^ i := fun i => by positivity
      have hc0 : c 0 ≤ Dc := by
        have hsub : (Finset.Icc 1 (Dc + 1)).filter (fun j => E j < E 1 + γ / 4 ^ 0) ⊆ Finset.Icc 1 Dc := by
          intro j hj
          rw [Finset.mem_filter, Finset.mem_Icc] at hj
          rw [Finset.mem_Icc]
          refine ⟨hj.1.1, ?_⟩
          by_contra h
          have hj' : j = Dc + 1 := by omega
          rw [hj', pow_zero, div_one] at hj
          linarith [hj.2]
        have := Finset.card_le_card hsub
        rw [Nat.card_Icc] at this
        simp only [hc]
        omega
      have hc1 : ∀ i, 1 ≤ c i := fun i => by
        simp only [hc]
        refine Finset.card_pos.mpr ⟨1, ?_⟩
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨le_rfl, by omega⟩, by linarith [hs i]⟩
      have hanti : ∀ i, c (i + 1) ≤ c i := fun i => by
        simp only [hc]
        refine Finset.card_le_card fun j hj => ?_
        rw [Finset.mem_filter] at hj ⊢
        refine ⟨hj.1, hj.2.trans_le ?_⟩
        have : γ / 4 ^ (i + 1) ≤ γ / 4 ^ i := by
          rw [pow_succ]
          exact div_le_div_of_nonneg_left hγ.le (by positivity) (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 4) i])
        linarith
      -- a scale where the count does not drop
      obtain ⟨i, hi, hci⟩ : ∃ i ≤ Dc, c (i + 1) = c i := by
        by_contra h
        push_neg at h
        have hdrop : ∀ i ≤ Dc + 1, c i + i ≤ c 0 := by
          intro i
          induction i with
          | zero => intro _; simp
          | succ n ih =>
            intro hn
            have h1 := ih (by omega)
            have h2 : c (n + 1) < c n := lt_of_le_of_ne (hanti n) (h n (by omega))
            omega
        have := hdrop (Dc + 1) le_rfl
        omega
      set p := c i with hp
      have hp1 : 1 ≤ p := hc1 i
      have hcle : ∀ j, c j ≤ c 0 := fun j => by
        induction j with
        | zero => exact le_rfl
        | succ n ih => exact (hanti n).trans ih
      have hpD : p ≤ Dc := (hcle i).trans hc0
      -- `E_p - E_1 < γ / 4^{i+1}` and `E_{p+1} - E_1 ≥ γ / 4^i`
      have ha : E p < E 1 + γ / 4 ^ (i + 1) := by
        by_contra hge
        push_neg at hge
        have hsub : (Finset.Icc 1 (Dc + 1)).filter (fun j => E j < E 1 + γ / 4 ^ (i + 1)) ⊆ Finset.Icc 1 (p - 1) := by
          intro j hj
          rw [Finset.mem_filter, Finset.mem_Icc] at hj
          rw [Finset.mem_Icc]
          refine ⟨hj.1.1, ?_⟩
          by_contra h
          have hjp : p ≤ j := by omega
          linarith [hmono hjp, hj.2]
        have := Finset.card_le_card hsub
        rw [Nat.card_Icc] at this
        have h' : c (i + 1) ≤ p - 1 := by simp only [hc]; omega
        omega
      have hb : E 1 + γ / 4 ^ i ≤ E (p + 1) := by
        by_contra hlt
        push_neg at hlt
        have hsub : Finset.Icc 1 (p + 1) ⊆ (Finset.Icc 1 (Dc + 1)).filter (fun j => E j < E 1 + γ / 4 ^ i) := by
          intro j hj
          rw [Finset.mem_Icc] at hj
          rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hj.1, by omega⟩, (hmono hj.2).trans_lt hlt⟩
        have := Finset.card_le_card hsub
        rw [Nat.card_Icc] at this
        have h' : p + 1 ≤ c i := by simp only [hc]; omega
        omega
      refine ⟨(⟨i, by omega⟩, ⟨p, by omega⟩), ?_, ?_⟩
      · show E p - E 1 ≤ γ / 4 ^ (i + 1)
        linarith
      · show 3 * (γ / 4 ^ (i + 1)) ≤ E (p + 1) - E p
        have e : γ / 4 ^ i = 4 * (γ / 4 ^ (i + 1)) := by
          rw [pow_succ]
          field_simp
        linarith
    -- the pigeonhole over the infinitely many `N`
    have hF' : ({N ∈ S.Ts.idx | ¬ Dc < ((Finset.Icc 1 (Module.finrank ℂ (sector (S.T N) (sec (S.T N))))).filter
        fun k => secEig (S.T N) (S.H N) (sec (S.T N)) k ∈
          Set.Ico (secEig (S.T N) (S.H N) (sec (S.T N)) 1)
            (secEig (S.T N) (S.H N) (sec (S.T N)) 1 + γ)).card} ∩ {N | 2 * Dc + 1 ≤ N}).Infinite := by
      have hfin : ({N | ¬ 2 * Dc + 1 ≤ N} : Set ℕ).Finite := by
        refine (Set.finite_lt_nat (2 * Dc + 1)).subset fun N hN => ?_
        simp only [Set.mem_setOf_eq, not_le] at hN ⊢
        exact hN
      have h := hinf.diff hfin
      refine h.mono fun N hN => ⟨hN.1, ?_⟩
      have := hN.2
      simp only [Set.mem_setOf_eq, not_not] at this
      exact this
    haveI := hF'.to_subtype
    obtain ⟨q, hq⟩ := Finite.exists_infinite_fiber fun x : ↥({N ∈ S.Ts.idx | ¬ Dc <
        ((Finset.Icc 1 (Module.finrank ℂ (sector (S.T N) (sec (S.T N))))).filter
          fun k => secEig (S.T N) (S.H N) (sec (S.T N)) k ∈
            Set.Ico (secEig (S.T N) (S.H N) (sec (S.T N)) 1)
              (secEig (S.T N) (S.H N) (sec (S.T N)) 1 + γ)).card} ∩ {N | 2 * Dc + 1 ≤ N}) =>
      Classical.choose (hpair x.1 x.2.1.1 x.2.2 x.2.1.2)
    have hMinf := (Set.infinite_coe_iff.mp hq).image Subtype.val_injective.injOn
    refine hng ⟨q.2, γ / 4 ^ ((q.1 : ℕ) + 1), 3 * (γ / 4 ^ ((q.1 : ℕ) + 1)), by positivity,
      by have : 0 < γ / 4 ^ ((q.1 : ℕ) + 1) := by positivity
         linarith, _, ?_, hMinf, ?_⟩
    · rintro N ⟨x, -, rfl⟩
      exact x.2.1.1
    · rintro N ⟨x, hx, rfl⟩
      have h := Classical.choose_spec (hpair x.1 x.2.1.1 x.2.2 x.2.1.2)
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      rw [hx] at h
      exact h
  -- the dimensions: `C(2N, (N-1)/2) ≥ (N-1)/2 + 1`
  have hdimbound : ∀ N ∈ S.Ts.idx, 2 * Dc + 1 ≤ N →
      Dc + 1 ≤ (S.T N).Nφ.choose (((S.T N).N - 1) / 2) := by
    intro N hN hN2
    have hTN : (S.T N).N = N := S.Ts.T_N N hN
    have h1 : ((S.T N).N - 1) / 2 + 1 ≤ (S.T N).Nφ := by
      show ((S.T N).N - 1) / 2 + 1 ≤ 2 * (S.T N).N
      omega
    have h2 := Nat.choose_le_choose (((S.T N).N - 1) / 2) h1
    rw [Nat.choose_succ_self_right] at h2
    omega
  refine ⟨key oddSectorPlus (fun N hN hN2 => ?_) hng1, key oddSectorMinus (fun N hN hN2 => ?_) hng2⟩
  · rw [finrank_sector]
    have h1 := hdimbound N hN hN2
    have h2 : 0 < (S.T N).Nφ.choose (((S.T N).N + 1) / 2) :=
      Nat.choose_pos (by show ((S.T N).N + 1) / 2 ≤ 2 * (S.T N).N; omega)
    show Dc + 1 ≤ (S.T N).Nφ.choose (((S.T N).N + 1) / 2) * (S.T N).Nφ.choose (((S.T N).N - 1) / 2)
    nlinarith
  · rw [finrank_sector]
    have h1 := hdimbound N hN hN2
    have h2 : 0 < (S.T N).Nφ.choose (((S.T N).N + 1) / 2) :=
      Nat.choose_pos (by show ((S.T N).N + 1) / 2 ≤ 2 * (S.T N).N; omega)
    show Dc + 1 ≤ (S.T N).Nφ.choose (((S.T N).N - 1) / 2) * (S.T N).Nφ.choose (((S.T N).N + 1) / 2)
    nlinarith

end HRTorus.Assembly

end -- noncomputable section
