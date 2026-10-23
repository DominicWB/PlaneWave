import PlaneWave.KineticLog.OpenLocal

/-!
# Logarithmic kinetic bound, part 26: `prop:free-kinetic-log`

The kinetic-energy comparison for the isolated-system grid, for a supplied strong free-space
solution `i ψ' = H_∞ ψ` (`HasFreeHamiltonian`, weak gradients `∇ψ(s)`), the range-cut cell
Hamiltonian `H_L` (`L ≥ 2π`, zero mode removed as in `prop:free-dyn`; the omitted scalar only
changes phases, which leave kinetic expectations unchanged), a `C²` cutoff `χ` with the leakage
conditions of `prop:free-dyn` on `[0, t]`, the cutoff-domain condition (H_dom)
`φ₀ = T(χ ψ₀) ∈ D(H_L²)`, the open-grid kernel class and a grid propagator `U_g` of the Fourier
grid Hamiltonian:

  `|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩|
      ≤ C D_*² [1 + t + log(2 + K)]/K³ + C (𝒟_∞ + D_*) (1 + t) ε`,

`ψ_g(t) = U_g(t) P' φ₀` (not renormalised), `D_* ≥ ‖φ₀‖ + ‖H_L φ₀‖ + ‖H_L² φ₀‖`,
`𝒟_∞ ≥ ‖ψ₀‖ + ‖H_∞ ψ₀‖`, `K = 2πm/L ≥ K₀`, `m ≥ 8`; `C = freeKinC sys V_θ D̄` and
`K₀ = cellK0 sys V_θ` depend only on the system, the profile bound and the cutoff bound `D̄`.

The free-space kinetic energy `⟨ψ, T_p ψ⟩` is the quadratic form `freeKinQ` (`inner_kinP_eq`);
the grid one is `regExpect` on the register.

* `norm_commT_le_N`, `KinMult.expect_smul_unit`, `exists_evoData_gL`: tools;
* `torus_pair_step`: the transplanted state against the cell trajectory (graph pairing on the
  torus, Duhamel `free_dyn_torus`);
* `cell_step`: the cell-to-grid estimate `cell_kinetic_explicit` at the explicit thresholds;
* **`free_kinetic_log_endpoint`**: `prop:free-kinetic-log` with explicit constants.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter MeasureTheory Set PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic PlaneWaveGrid
  PlaneWaveGridDynamics FreeBoundary FSNormal

namespace KineticLog

attribute [local instance] FreeBoundary.unitAddCircleMeasureSpaceFB15
  FreeBoundary.unitAddCircleProbabilityMeasureFB15 FreeBoundary.molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Tools -/

/-- **The transplanted commutator without leakage**: `‖T([K, χ] f)‖ ≤ 3η (D₁ + D₂/2) N` when
`‖f‖, ‖∂f‖ ≤ N` (masses `≥ 1`). -/
lemma norm_commT_le_N {L : ℝ} (X : Cutoff eta L) (hL : 0 < L) {m : Fin eta → ℝ}
    (hm : ∀ i, 1 ≤ m i) (f : FreeL2 eta) (g : Fin eta × Fin 3 → FreeL2 eta) {N : ℝ}
    (hf : ‖f‖ ≤ N) (hg : ∀ a, ‖g a‖ ≤ N) : ‖X.commT hL m f g‖ ≤ X.commConst * N := by
  have hT2 : ∀ a, ‖(X.d2W a).cutL2 hL f‖ ≤ X.D2 * N := fun a =>
    ((X.d2W a).norm_cutL2_le hL f).trans (mul_le_mul_of_nonneg_left hf (X.d2W a).B_nonneg)
  have hT1 : ∀ a, ‖(X.d1W a).cutL2 hL (g a)‖ ≤ X.D1 * N := fun a =>
    ((X.d1W a).norm_cutL2_le hL (g a)).trans
      (mul_le_mul_of_nonneg_left (hg a) (X.d1W a).B_nonneg)
  have hc : ∀ a : Fin eta × Fin 3, ‖(-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹‖ ≤ 1 / 2 := by
    intro a
    have hm0 : 0 < m a.1 := lt_of_lt_of_le one_pos (hm a.1)
    rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h2]
    have h3 : (m a.1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hm a.1)
    have h4 : 0 ≤ (m a.1)⁻¹ := inv_nonneg.mpr hm0.le
    nlinarith
  unfold Cutoff.commT Cutoff.commConst
  calc ‖∑ a : Fin eta × Fin 3, ((-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹) •
        ((X.d2W a).cutL2 hL f + (2 : ℂ) • (X.d1W a).cutL2 hL (g a))‖
      ≤ ∑ a : Fin eta × Fin 3, ‖((-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹) •
        ((X.d2W a).cutL2 hL f + (2 : ℂ) • (X.d1W a).cutL2 hL (g a))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin eta × Fin 3, 1 / 2 * (X.D2 * N + 2 * (X.D1 * N)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_smul]
        have hv : ‖(X.d2W a).cutL2 hL f + (2 : ℂ) • (X.d1W a).cutL2 hL (g a)‖ ≤
            X.D2 * N + 2 * (X.D1 * N) := by
          refine (norm_add_le _ _).trans (add_le_add (hT2 a) ?_)
          rw [norm_smul]
          have h2 : ‖(2 : ℂ)‖ = 2 := by simp
          rw [h2]
          exact mul_le_mul_of_nonneg_left (hT1 a) (by norm_num)
        exact mul_le_mul (hc a) hv (norm_nonneg _) (by norm_num)
    _ = (Fintype.card (Fin eta × Fin 3) : ℝ) * (X.D1 + X.D2 / 2) * N := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

omit [Fintype ν] in
/-- Kinetic expectations do not see phases: `⟨e x, μ e x⟩ = ⟨x, μ x⟩` for `|e| = 1`. -/
lemma KinMult.expect_smul_unit {sys : CoulombSystem eta ν} {g : ℝ} (μ : KinMult sys g) {e : ℂ}
    (he : ‖e‖ = 1) (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    μ.expect (e • x) = μ.expect x := by
  unfold KinMult.expect
  refine tsum_congr fun p => ?_
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, he, one_mul]

lemma one_le_relConstN (sys : CoulombSystem eta ν) : 1 ≤ relConstN sys := by
  have hM := sys.one_le_maxMass
  have hQ := chargeWeight_nonneg sys
  unfold relConstN
  have h1 : (3 : ℝ) ≤ 3 + 8 * sys.maxMass * chargeWeight sys ^ 2 := by
    have : 0 ≤ 8 * sys.maxMass * chargeWeight sys ^ 2 := by positivity
    linarith
  nlinarith

/-- **The exact cell evolution as `EvoData`**: the `g_L` propagator on the Fourier coefficients,
with the cut datum `φ₀ ∈ D(H_L²)` (`H_L φ₀ = h₀`, `H_L h₀ = h₁`). -/
theorem exists_evoData_gL (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (hR : R ≤ L / 2)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUcont : ∀ ψ, Continuous fun t => U t ψ)
    (hgraphU : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasGLHamiltonian sys L θ (U t f) (U t h))
    (hderivU : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    {φ₀ h₀ h₁ : MolecularPositionL2 eta} (hdom0 : HasGLHamiltonian sys L θ φ₀ h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁) :
    ∃ D : EvoData L H,
      (∀ t x, D.U t x = (molecularPositionSynthesis eta).symm
        (U t (molecularPositionSynthesis eta x))) ∧
      Sm eta L D.u₀ = (molecularPositionSynthesis eta).symm φ₀ ∧
      D.Xi = ‖φ₀‖ + ‖h₀‖ + ‖h₁‖ := by
  have hiff := hasGLHamiltonian_iff_H2 sys hL hθ hR H hKernel
  obtain ⟨u₀, hu1, hu2⟩ := (hiff _ _).mp hdom0
  obtain ⟨v₀, hv1, hv2⟩ := (hiff _ _).mp hdom1
  have huv : H u₀ = Sm eta L v₀ := by
    apply (molecularPositionSynthesis eta).injective
    rw [hu2, ← hv1]
    rfl
  have hrel : ∀ u : MolecularFourierH2 eta, HasGLHamiltonian sys L θ
      (molecularPositionSynthesis eta (molecularH2StateMap eta (2 * Real.pi / L) u))
          (molecularPositionSynthesis eta (H u)) := fun u =>
    (hiff _ _).mpr ⟨u, rfl, rfl⟩
  refine ⟨{ U := fun t =>
              ((molecularPositionSynthesis eta).trans (U t)).trans
                (molecularPositionSynthesis eta).symm
            U0 := fun x => ?_
            graph := fun t u => ?_
            deriv := fun t u => ?_
            cont := fun x => ?_
            u₀ := u₀
            v₀ := v₀
            uv := huv }, fun t x => rfl, ?_, ?_⟩
  · simp [hU0]
  · obtain ⟨u', h1, h2⟩ := (hiff _ _).mp (hgraphU t _ _ (hrel u))
    refine ⟨u', ?_, ?_⟩
    · change molecularH2StateMap eta (2 * Real.pi / L) u' = (molecularPositionSynthesis eta).symm
        (U t (molecularPositionSynthesis eta (molecularH2StateMap eta (2 * Real.pi / L) u)))
      rw [← h1, LinearIsometryEquiv.symm_apply_apply]
    · change H u' =
        (molecularPositionSynthesis eta).symm (U t (molecularPositionSynthesis eta (H u)))
      rw [← h2, LinearIsometryEquiv.symm_apply_apply]
  · have h := ((molecularPositionSynthesis eta).symm.toContinuousLinearEquiv.toContinuousLinearMap
      |>.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hderivU t _ _ (hrel u))
    change HasDerivAt (fun s => (molecularPositionSynthesis eta).symm
      (U s (molecularPositionSynthesis eta (molecularH2StateMap eta (2 * Real.pi / L) u))))
      (-(Complex.I • (molecularPositionSynthesis eta).symm
        (U t (molecularPositionSynthesis eta (H u))))) t
    have e : ((molecularPositionSynthesis eta).symm.toContinuousLinearEquiv.toContinuousLinearMap
        |>.restrictScalars ℝ) (-(Complex.I • U t (molecularPositionSynthesis eta (H u)))) =
        -(Complex.I • (molecularPositionSynthesis eta).symm
          (U t (molecularPositionSynthesis eta (H u)))) := by
      simp
    rw [e] at h
    exact h
  · exact (molecularPositionSynthesis eta).symm.continuous.comp (hUcont _)
  · change molecularH2StateMap eta (2 * Real.pi / L) u₀ = (molecularPositionSynthesis eta).symm φ₀
    rw [← hu1, LinearIsometryEquiv.symm_apply_apply]
  · unfold EvoData.Xi
    change ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ + ‖H u₀‖ + ‖H v₀‖ = _
    rw [← LinearIsometryEquiv.norm_map (molecularPositionSynthesis eta)
        (molecularH2StateMap eta (2 * Real.pi / L) u₀),
      ← LinearIsometryEquiv.norm_map (molecularPositionSynthesis eta) (H u₀),
      ← LinearIsometryEquiv.norm_map (molecularPositionSynthesis eta) (H v₀), hu1,
      hu2, hv2]

/-! ## The two steps through the cell -/

set_option maxHeartbeats 1000000 in
/-- **The transplanted state against the exact cell trajectory**: graph pairing on the torus,
with the Duhamel estimate of `free_dyn_torus` for the state difference and the cell elliptic
bound for the two kinetic graph norms:
`|⟨T(χψ(t)), T_p T(χψ(t))⟩ - ⟨u_L(t), T_p u_L(t)⟩|
  ≤ c_χ ε t (2 (‖H_∞ψ(t)‖ + (Q/4) ‖ψ(t)‖ + c_χ N) + 2 b_U ‖ψ(t)‖ + b_e Ξ/2)`. -/
theorem torus_pair_step (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    (HL : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, HL (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta)
    (hU0 : ∀ ψ, U 0 ψ = ψ) (hUadd : ∀ s t ψ, U (s + t) ψ = U s (U t ψ))
    (hUcont : ∀ ψ, Continuous fun t => U t ψ)
    (hderivU : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (D : EvoData L HL)
    (hDU : ∀ t x, D.U t x = (molecularPositionSynthesis eta).symm
      (U t (molecularPositionSynthesis eta x)))
    (hDu0 : Sm eta L D.u₀ =
      (molecularPositionSynthesis eta).symm (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))
    {N : ℝ} (hNψ : ‖ψ t‖ ≤ N) (hNg : ∀ a, ‖grad t a‖ ≤ N) (p₀ : Fin eta) :
    |(regKin sys (gF L) p₀).expect ((molecularPositionSynthesis eta).symm
        (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ t))) -
      (regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀))| ≤
      X.commConst * ε * t * (2 * (‖H t‖ + zeroWeight sys / 4 * ‖ψ t‖ + X.commConst * N) +
        2 * relBU sys (tv R θ) molecularCanonicalUnitHardyConstant * ‖ψ t‖ +
        b0eU sys (tv R θ) molecularCanonicalUnitHardyConstant * D.Xi / 2) := by
  have hL := pos_of_two_pi_le hL2
  have hH0 := hardyUnit_nonneg
  have hPer := canonicalPeriodicCoulombHardyBound_explicit
  have hD1 : 0 ≤ X.D1 := (abs_nonneg _).trans (X.d1 0 (p₀, 0))
  have hD2 : 0 ≤ X.D2 := (abs_nonneg _).trans (X.d2 0 (p₀, 0))
  have hcc : 0 ≤ X.commConst := by unfold Cutoff.commConst; positivity
  -- the `H²` lift of the transplant at time `t`
  have htr := transplant_hasGLHamiltonian sys hL hR0 hρ hone P hP hpos X hret (hHam t) (hgrad t)
  obtain ⟨wt, hwt1, hwt2⟩ := (hasGLHamiltonian_iff_H2 sys hL hθ hR HL hKernel _ _).mp htr
  -- the cell trajectory
  obtain ⟨w', hw'1, hw'2, -⟩ := traj_tails_gL sys HL hKernel molecularCanonicalUnitHardyConstant
    hL2 hθ hPer hH0 D t
  -- Duhamel
  have hduh := (free_dyn_torus sys hL hθ hR0 hρ hone P hP hpos U hU0 hUadd hUcont hderivU X hret
    hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 (χo := fun _ => (0 : ℝ))
    (fun _ => le_rfl) (fun _ => zero_le_one) measurable_const 0 (fun x => by simp)).1
  set e := Complex.exp (-(Complex.I * (zeroModeShift sys L θ).re * t)) with he
  have he1 : ‖e‖ = 1 := by
    rw [he, Complex.norm_exp]
    simp
  -- the states as `H²` images
  have hSwt : molecularH2StateMap eta (gF L) wt = (molecularPositionSynthesis eta).symm
      (X.chiW.cutL2 hL (ψ t)) := by
    rw [← hwt1, LinearIsometryEquiv.symm_apply_apply]
    rfl
  have hSw' : molecularH2StateMap eta (gF L) w' = D.U t (Sm eta L D.u₀) := hw'1
  have hU' : D.U t (Sm eta L D.u₀) = (molecularPositionSynthesis eta).symm
      (U t (X.chiW.cutL2 hL (ψ 0))) := by
    rw [hDU, hDu0, LinearIsometryEquiv.apply_symm_apply]
  -- graph pairing
  have hpair := expect_sub_le (regKin sys (gF L) p₀) wt (e • w')
  rw [map_smul, KinMult.expect_smul_unit _ he1, hSwt, hSw'] at hpair
  refine hpair.trans ?_
  -- the state difference
  have hdiff : ‖(molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL (ψ t)) -
      e • D.U t (Sm eta L D.u₀)‖ ≤ X.commConst * ε * t := by
    rw [hU', ← map_smul, ← map_sub, LinearIsometryEquiv.norm_map]
    exact hduh
  -- the kinetic graph norm of the transplant
  have hcut : ∀ f : FreeL2 eta, ‖X.chiW.cutL2 hL f‖ ≤ ‖f‖ := fun f => by
    have h := X.chiW.norm_cutL2_le hL f
    have hB : X.chiW.B = 1 := rfl
    rw [hB, one_mul] at h
    exact h
  have hC0 := norm_zeroModeShift_le sys hL2 hθ hR
  have hcomm := norm_commT_le_N X hL sys.one_le_mass (ψ t) (grad t) hNψ hNg
  have hHwt : ‖HL wt‖ ≤ ‖H t‖ + zeroWeight sys / 4 * ‖ψ t‖ + X.commConst * N := by
    rw [← LinearIsometryEquiv.norm_map (molecularPositionSynthesis eta) (HL wt), hwt2]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) hcomm).trans ?_
    rw [norm_smul]
    have h1 := hcut (H t)
    have h2 : ‖zeroModeShift sys L θ‖ * ‖X.chiW.cutL2 hL (ψ t)‖ ≤ zeroWeight sys / 4 * ‖ψ t‖ :=
      mul_le_mul hC0 (hcut (ψ t)) (norm_nonneg _) (by have := zeroWeight_nonneg sys; positivity)
    linarith
  have hSwtn : ‖molecularH2StateMap eta (gF L) wt‖ ≤ ‖ψ t‖ := by
    rw [hSwt, LinearIsometryEquiv.norm_map]
    exact hcut (ψ t)
  have hC : 0 ≤ gLmassConst sys L (tv R θ) molecularCanonicalUnitHardyConstant :=
    gLmassConst_nonneg' sys (L := L) _ hθ
  have hT := kinetic_le_elliptic_gL sys L HL hKernel molecularCanonicalUnitHardyConstant hL hθ hPer
    hC wt
  rw [relB_gL_eq_U sys hL2 _ hH0] at hT
  have hb0 := relBU_nonneg sys hθ.tv_nonneg hH0
  have hμt : ‖(regKin sys (gF L) p₀).h2 wt‖ ≤
      2 * (‖H t‖ + zeroWeight sys / 4 * ‖ψ t‖ + X.commConst * N) +
        2 * relBU sys (tv R θ) molecularCanonicalUnitHardyConstant * ‖ψ t‖ := by
    refine ((regKin sys (gF L) p₀).norm_h2_le wt).trans (hT.trans ?_)
    have e1 : 2 * ‖HL wt‖ ≤ 2 * (‖H t‖ + zeroWeight sys / 4 * ‖ψ t‖ + X.commConst * N) := by
      linarith
    have e2 : 2 * relBU sys (tv R θ) molecularCanonicalUnitHardyConstant *
        ‖molecularH2StateMap eta (2 * Real.pi / L) wt‖ ≤
        2 * relBU sys (tv R θ) molecularCanonicalUnitHardyConstant * ‖ψ t‖ :=
      mul_le_mul_of_nonneg_left hSwtn (by positivity)
    linarith
  -- the kinetic graph norm of the cell trajectory
  have hμ' : ‖(regKin sys (gF L) p₀).h2 (e • w')‖ ≤
      b0eU sys (tv R θ) molecularCanonicalUnitHardyConstant * D.Xi / 2 := by
    rw [map_smul, norm_smul, he1, one_mul]
    refine ((regKin sys (gF L) p₀).norm_h2_le w').trans ?_
    have := norm_nonneg (Sm eta L w')
    change ‖coulombFourierKineticH2 sys (gF L) w'‖ ≤ _
    linarith
  calc ‖(molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL (ψ t)) -
        e • D.U t (Sm eta L D.u₀)‖ *
        (‖(regKin sys (gF L) p₀).h2 wt‖ + ‖(regKin sys (gF L) p₀).h2 (e • w')‖)
      ≤ X.commConst * ε * t * (2 * (‖H t‖ + zeroWeight sys / 4 * ‖ψ t‖ + X.commConst * N) +
        2 * relBU sys (tv R θ) molecularCanonicalUnitHardyConstant * ‖ψ t‖ +
        b0eU sys (tv R θ) molecularCanonicalUnitHardyConstant * D.Xi / 2) := by
        refine mul_le_mul hdiff ?_ (by positivity) (by positivity)
        linarith

/-- **The cell-to-grid step at the explicit thresholds** (`cell_kinetic_explicit`). -/
theorem cell_step (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L)
    (hθ : Profile R θ)
    (HL : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, HL (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (D : EvoData L HL) (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys (tv R θ) molecularCanonicalUnitHardyConstant ≤ gF L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t)
    {t : ℝ} (ht : 0 ≤ t) :
    |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
        regExpect sys (gF L) p₀ (Ug t (regCoeff m (Sm eta L D.u₀)))| ≤
      cellC sys (tv R θ) molecularCanonicalUnitHardyConstant * D.Xi ^ 2 *
        (1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3 := by
  have hL := pos_of_two_pi_le hL2
  have hV := hθ.tv_nonneg
  have hH0 := hardyUnit_nonneg
  have hPer := canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨hK8, hKbig⟩ := cellK0_scales hV hK
  obtain ⟨E⟩ := exists_exactEigen_gL sys HL hKernel molecularCanonicalUnitHardyConstant hL hθ hPer
  have E' : ExactEigen L HL (cU sys (tv R θ) molecularCanonicalUnitHardyConstant) :=
    shift_gL_eq_U sys (tv R θ) _ hL2 hH0 ▸ E
  obtain ⟨hT2, hTg, hTg2, hTm⟩ := T0U_scales hL2 (by omega : 2 ≤ m) (by linarith)
  exact cell_kinetic_explicit sys HL hKernel _ hL2 hθ hPer hH0 p₀ E' rfl m hm hK8 hKbig hT2 hTg
    hTg2 hTm hκ Ug hg0 hgcomm hgderiv D ht

/-! ## The constant -/

/-- The commutator constant of a cutoff bound `D̄`: `c̄ = 3η (D̄ + D̄/2)`. -/
noncomputable def commBar (eta : ℕ) (Dbar : ℝ) : ℝ :=
  (Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2)

/-- The localisation constant
`C_loc = (3/2)(1 + 4D̄ + D̄²) c₁′ + c̄ (2 (1 + Q/4 + c̄ c₁′ + b_U) + b_e/2)`. -/
noncomputable def locC (sys : CoulombSystem eta ν) (V Dbar : ℝ) : ℝ :=
  3 / 2 * (1 + 4 * Dbar + Dbar ^ 2) * relConstN sys +
    commBar eta Dbar * (2 * (1 + zeroWeight sys / 4 + commBar eta Dbar * relConstN sys +
      relBU sys V molecularCanonicalUnitHardyConstant) +
      b0eU sys V molecularCanonicalUnitHardyConstant / 2)

/-- **The constant of `prop:free-kinetic-log`**: `C = C_cell + C_loc`; it depends only on the
masses and charges, the profile bound `V_θ` and the cutoff bound `D̄`. -/
noncomputable def freeKinC (sys : CoulombSystem eta ν) (V Dbar : ℝ) : ℝ :=
  cellC sys V molecularCanonicalUnitHardyConstant + locC sys V Dbar

lemma commBar_nonneg {Dbar : ℝ} (hD : 0 ≤ Dbar) : 0 ≤ commBar eta Dbar := by
  unfold commBar
  positivity

lemma locC_nonneg (sys : CoulombSystem eta ν) {V Dbar : ℝ} (hV : 0 ≤ V) (hD : 0 ≤ Dbar) :
    0 ≤ locC sys V Dbar := by
  unfold locC
  have := relConstN_nonneg sys
  have := zeroWeight_nonneg sys
  have := relBU_nonneg sys hV hardyUnit_nonneg
  have := b0eU_nonneg sys hV hardyUnit_nonneg
  have := commBar_nonneg (eta := eta) hD
  positivity

lemma freeKinC_nonneg (sys : CoulombSystem eta ν) {V Dbar : ℝ} (hV : 0 ≤ V) (hD : 0 ≤ Dbar) :
    0 ≤ freeKinC sys V Dbar :=
  add_nonneg (cellC_nonneg hV hardyUnit_nonneg) (locC_nonneg sys hV hD)

lemma commConst_le_commBar {L : ℝ} (X : Cutoff eta L) {Dbar : ℝ} (hD1 : X.D1 ≤ Dbar)
    (hD2 : X.D2 ≤ Dbar) : X.commConst ≤ commBar eta Dbar := by
  unfold Cutoff.commConst commBar
  have : X.D1 + X.D2 / 2 ≤ Dbar + Dbar / 2 := by linarith
  exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)

/-- The final arithmetic of `prop:free-kinetic-log` (pure real inequalities). -/
lemma free_kin_assemble {a b c Q cC A B Dbar D1 c1 cc ccb Q4 rb be Dinf Dst Xi Ht ψt N ε t : ℝ}
    (hA : a ≤ 3 / 2 * (1 + 4 * D1 + D1 ^ 2) * N * ε)
    (hB : b ≤ cc * ε * t * (2 * (Ht + Q4 * ψt + cc * N) + 2 * rb * ψt + be * Xi / 2))
    (hC : c ≤ cC * Q) (hQ : 0 ≤ Q)
    (hD10 : 0 ≤ D1) (hD1 : D1 ≤ Dbar) (hc1 : 1 ≤ c1) (hN : N = c1 * Dinf) (hcc0 : 0 ≤ cc)
    (hcc : cc ≤ ccb) (hQ4 : 0 ≤ Q4) (hrb : 0 ≤ rb) (hbe : 0 ≤ be) (hDst : 0 ≤ Dst)
    (hXi0 : 0 ≤ Xi) (hXi : Xi ≤ Dst) (hHt0 : 0 ≤ Ht) (hHt : Ht ≤ Dinf) (hψt0 : 0 ≤ ψt)
    (hψt : ψt ≤ Dinf) (hε : 0 ≤ ε) (ht : 0 ≤ t) (hcC : 0 ≤ cC)
    (hAB : A = 3 / 2 * (1 + 4 * Dbar + Dbar ^ 2) * c1 +
      ccb * (2 * (1 + Q4 + ccb * c1 + rb) + be / 2)) (hB0 : B = cC + A) :
    a + b + c ≤ B * Q + B * ((Dinf + Dst) * (1 + t) * ε) := by
  have hDinf : 0 ≤ Dinf := hψt0.trans hψt
  have hc10 : 0 ≤ c1 := by linarith
  have hN0 : 0 ≤ N := by rw [hN]; exact mul_nonneg hc10 hDinf
  have hccb : 0 ≤ ccb := hcc0.trans hcc
  have hDb : 0 ≤ Dbar := hD10.trans hD1
  set Y := (Dinf + Dst) * (1 + t) * ε with hY
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  -- the free-space piece
  have hD12 : D1 ^ 2 ≤ Dbar ^ 2 := pow_le_pow_left₀ hD10 hD1 2
  have e1 : 1 + 4 * D1 + D1 ^ 2 ≤ 1 + 4 * Dbar + Dbar ^ 2 := by linarith
  have e2 : N * ε ≤ c1 * Y := by
    have f1 : Dinf ≤ (Dinf + Dst) * (1 + t) := by
      have : 0 ≤ (Dinf + Dst) * t := mul_nonneg (by linarith) ht
      have e : (Dinf + Dst) * (1 + t) = Dinf + Dst + (Dinf + Dst) * t := by ring
      rw [e]
      linarith
    have f2 : Dinf * ε ≤ (Dinf + Dst) * (1 + t) * ε := mul_le_mul_of_nonneg_right f1 hε
    have f3 : c1 * (Dinf * ε) ≤ c1 * ((Dinf + Dst) * (1 + t) * ε) :=
      mul_le_mul_of_nonneg_left f2 hc10
    rw [hN, hY]
    calc c1 * Dinf * ε = c1 * (Dinf * ε) := by ring
      _ ≤ _ := f3
  have hA' : a ≤ 3 / 2 * (1 + 4 * Dbar + Dbar ^ 2) * c1 * Y := by
    refine hA.trans ?_
    have e3 : 0 ≤ 1 + 4 * D1 + D1 ^ 2 := by positivity
    calc 3 / 2 * (1 + 4 * D1 + D1 ^ 2) * N * ε = 3 / 2 * (1 + 4 * D1 + D1 ^ 2) * (N * ε) := by
          ring
      _ ≤ 3 / 2 * (1 + 4 * Dbar + Dbar ^ 2) * (c1 * Y) :=
          mul_le_mul (by linarith) e2 (mul_nonneg hN0 hε) (by positivity)
      _ = _ := by ring
  -- the torus piece
  have hI0 : 0 ≤ 2 * (Ht + Q4 * ψt + cc * N) + 2 * rb * ψt + be * Xi / 2 := by
    have := mul_nonneg hQ4 hψt0
    have := mul_nonneg hcc0 hN0
    have := mul_nonneg hrb hψt0
    have := mul_nonneg hbe hXi0
    linarith
  have hIJ : 2 * (Ht + Q4 * ψt + cc * N) + 2 * rb * ψt + be * Xi / 2 ≤
      (2 * (1 + Q4 + ccb * c1 + rb) + be / 2) * (Dinf + Dst) := by
    have f1 : Q4 * ψt ≤ Q4 * Dinf := mul_le_mul_of_nonneg_left hψt hQ4
    have f2 : cc * N ≤ ccb * c1 * Dinf := by
      rw [hN, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hc10) hDinf
    have f3 : rb * ψt ≤ rb * Dinf := mul_le_mul_of_nonneg_left hψt hrb
    have f4 : be * Xi ≤ be * Dst := mul_le_mul_of_nonneg_left hXi hbe
    have g1 : 0 ≤ be * Dinf := mul_nonneg hbe hDinf
    have g2 : 0 ≤ Q4 * Dst := mul_nonneg hQ4 hDst
    have g3 : 0 ≤ ccb * c1 * Dst := mul_nonneg (mul_nonneg hccb hc10) hDst
    have g4 : 0 ≤ rb * Dst := mul_nonneg hrb hDst
    have e : (2 * (1 + Q4 + ccb * c1 + rb) + be / 2) * (Dinf + Dst) =
        2 * Dinf + 2 * (Q4 * Dinf) + 2 * (ccb * c1 * Dinf) + 2 * (rb * Dinf) + be * Dinf / 2 +
          (2 * Dst + 2 * (Q4 * Dst) + 2 * (ccb * c1 * Dst) + 2 * (rb * Dst) + be * Dst / 2) := by
      ring
    rw [e]
    linarith
  have hcct : cc * ε * t ≤ ccb * ((1 + t) * ε) := by
    have f1 : cc * (ε * t) ≤ ccb * (ε * t) := mul_le_mul_of_nonneg_right hcc (mul_nonneg hε ht)
    have f2 : ccb * (ε * t) ≤ ccb * ((1 + t) * ε) := by
      apply mul_le_mul_of_nonneg_left _ hccb
      nlinarith
    calc cc * ε * t = cc * (ε * t) := by ring
      _ ≤ _ := f1.trans f2
  have hB' : b ≤ ccb * (2 * (1 + Q4 + ccb * c1 + rb) + be / 2) * Y := by
    refine hB.trans ?_
    calc cc * ε * t * (2 * (Ht + Q4 * ψt + cc * N) + 2 * rb * ψt + be * Xi / 2)
        ≤ ccb * ((1 + t) * ε) * ((2 * (1 + Q4 + ccb * c1 + rb) + be / 2) * (Dinf + Dst)) :=
          mul_le_mul hcct hIJ hI0 (mul_nonneg hccb (by positivity))
      _ = _ := by rw [hY]; ring
  have hA0 : 0 ≤ A := by
    rw [hAB]
    have : 0 ≤ ccb * c1 := mul_nonneg hccb hc10
    positivity
  have hsplit : A * Y = 3 / 2 * (1 + 4 * Dbar + Dbar ^ 2) * c1 * Y +
      ccb * (2 * (1 + Q4 + ccb * c1 + rb) + be / 2) * Y := by
    rw [hAB]
    ring
  have h1 : 0 ≤ A * Q := mul_nonneg hA0 hQ
  have h2 : 0 ≤ cC * Y := mul_nonneg hcC hY0
  have hfin : B * Q + B * Y = cC * Q + A * Y + (A * Q + cC * Y) := by
    rw [hB0]
    ring
  rw [hfin]
  linarith

/-! ## `prop:free-kinetic-log` -/

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` (general cutoff, with (H_dom))**: for a supplied strong free-space
solution, a cutoff with derivative bounds `D̄`, leakage `ε` on `[0, t]`, the cutoff-domain
condition `H_L φ₀ = h₀`, `H_L h₀ = h₁` (`φ₀ = T(χ ψ₀)`, `H_L` the `g_L` Hamiltonian), any `m ≥ 8`
with `K = 2πm/L ≥ K₀`, any kernel of the open-grid class and any grid propagator `U_g`,
`|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C D_*² [1 + t + log(2 + K)]/K³
  + C (𝒟_∞ + D_*) (1 + t) ε`, `ψ_g(t) = U_g(t) P' φ₀`,
with `C = freeKinC sys V_θ D̄` and `K₀ = cellK0 sys V_θ` independent of `L`, `m`, `t`, `ε` and
the datum. -/
theorem free_kinetic_log_endpoint (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Dbar : ℝ} (hD1 : X.D1 ≤ Dbar) (hD2 : X.D2 ≤ Dbar)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁)
    {Dinf Dst : ℝ} (hDinf : ‖ψ 0‖ + ‖H 0‖ ≤ Dinf)
    (hDst : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys (tv R θ) molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
      freeKinC sys (tv R θ) Dbar * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) /
          (2 * Real.pi / L * m) ^ 3 +
        freeKinC sys (tv R θ) Dbar * (Dinf + Dst) * (1 + t) * ε := by
  have hL : 0 < L := pos_of_two_pi_le hL2
  have hV : 0 ≤ tv R θ := hθ.tv_nonneg
  have hH0 := hardyUnit_nonneg
  have hPer := canonicalPeriodicCoulombHardyBound_explicit
  have hD10 : 0 ≤ X.D1 := (abs_nonneg _).trans (X.d1 0 (p₀, 0))
  -- the cell and its exact evolution
  obtain ⟨HL, hKernel, -⟩ := exists_gLFourierH2Operator sys hL hθ
    molecularCanonicalUnitHardyConstant hPer
  obtain ⟨U, hU0, hUadd, hUcont, hgraphU, hderivU, -⟩ := exists_gLPropagator sys hL hθ hR
  obtain ⟨D, hDU, hDu0, hDXi⟩ := exists_evoData_gL sys hL hθ hR HL hKernel U hU0 hUcont hgraphU
    hderivU hdom0 hdom1
  have hXi : D.Xi ≤ Dst := hDXi ▸ hDst
  have hXi0 := D.Xi_nonneg
  -- conservation and regularity at time `t`
  have hcons := norm_conserved sys P hψd hHam t
  have hconsH := norm_H_conserved sys P hψd hHam t
  have hψH : ‖ψ t‖ + ‖H t‖ ≤ Dinf := by rw [hcons, hconsH]; exact hDinf
  have hc1 := one_le_relConstN sys
  obtain ⟨g', g2, -, -, -, hg', hg2, -, -, -, hb1, hb2, -, -⟩ :=
    free_hamiltonian_regularity_nuc sys P (hHam t)
  have hgg : g' = grad t := HasWeakGrad.unique hg' (hgrad t)
  rw [hgg] at hg2 hb1
  set N := relConstN sys * Dinf with hNdef
  have hcN : relConstN sys * (‖ψ t‖ + ‖H t‖) ≤ N :=
    mul_le_mul_of_nonneg_left hψH (relConstN_nonneg sys)
  have hNg : ∀ a, ‖grad t a‖ ≤ N := fun a => (hb1 a).trans hcN
  have hNg2 : ∀ a b, ‖g2 a b‖ ≤ N := fun a b => (hb2 a b).trans hcN
  have hNψ : ‖ψ t‖ ≤ N := by
    have h1 : ‖ψ t‖ ≤ Dinf := by linarith [norm_nonneg (H t)]
    have h2 : Dinf ≤ N := by
      rw [hNdef]
      have : 0 ≤ Dinf := (norm_nonneg _).trans h1
      nlinarith
    linarith
  -- the three steps
  have hA := free_torus_kin sys hL X hSm hBm hχB hSB hdS (hgrad t) hg2 hε (hleak0 t ⟨ht, le_rfl⟩)
    hNψ hNg hNg2 p₀
  have hB := torus_pair_step sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hSm hBm hχB hSB hdS hd2S
    hψd hHam hgrad ht hε hleak0 hleak1 HL hKernel U hU0 hUadd hUcont hderivU D hDU hDu0 hNψ hNg p₀
  have hC := cell_step sys hL2 hθ HL hKernel D p₀ m hm hK hκ Ug hg0 hgcomm hgderiv ht
  rw [← hDu0]
  -- assemble
  set K : ℝ := 2 * Real.pi / L * m with hKdef
  have hK8 : (8 : ℝ) ≤ K := (cellK0_scales hV hK).1
  have hlog : 0 ≤ Real.log (2 + K) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ Dst ^ 2 * (1 + t + Real.log (2 + K)) / K ^ 3 := by positivity
  have hC' : |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
      regExpect sys (gF L) p₀ (Ug t (regCoeff m (Sm eta L D.u₀)))| ≤
      cellC sys (tv R θ) molecularCanonicalUnitHardyConstant *
        (Dst ^ 2 * (1 + t + Real.log (2 + K)) / K ^ 3) := by
    refine hC.trans ?_
    have hX2 : D.Xi ^ 2 ≤ Dst ^ 2 := pow_le_pow_left₀ hXi0 hXi 2
    have hK3 : 0 < K ^ 3 := by positivity
    have hcC := cellC_nonneg (sys := sys) hV hH0
    change cellC sys (tv R θ) molecularCanonicalUnitHardyConstant * D.Xi ^ 2 *
      (1 + t + Real.log (2 + K)) / K ^ 3 ≤ _
    rw [mul_div_assoc, mul_div_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hcC
    exact mul_le_mul_of_nonneg_right hX2 (div_nonneg (by linarith) hK3.le)
  have htri := abs_sub_le (freeKinQ sys p₀ (grad t))
    ((regKin sys (gF L) p₀).expect ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL (ψ t))))
    (regExpect sys (gF L) p₀ (Ug t (regCoeff m (Sm eta L D.u₀))))
  have htri2 := abs_sub_le
    ((regKin sys (gF L) p₀).expect ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL (ψ t))))
    ((regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)))
    (regExpect sys (gF L) p₀ (Ug t (regCoeff m (Sm eta L D.u₀))))
  have hfin := free_kin_assemble (Dbar := Dbar) (c1 := relConstN sys) (ccb := commBar eta Dbar)
    (Q4 := zeroWeight sys / 4) (rb := relBU sys (tv R θ) molecularCanonicalUnitHardyConstant)
    (be := b0eU sys (tv R θ) molecularCanonicalUnitHardyConstant) (Dinf := Dinf) (Dst := Dst)
    (Xi := D.Xi) (Ht := ‖H t‖) (ψt := ‖ψ t‖) (N := N) (ε := ε) (t := t)
    (cC := cellC sys (tv R θ) molecularCanonicalUnitHardyConstant)
    (A := locC sys (tv R θ) Dbar) (B := freeKinC sys (tv R θ) Dbar)
    hA hB hC' hQ hD10 hD1 hc1 rfl
    (by unfold Cutoff.commConst; have := (abs_nonneg _).trans (X.d2 0 (p₀, 0)); positivity)
    (commConst_le_commBar X hD1 hD2) (by have := zeroWeight_nonneg sys; positivity)
    (relBU_nonneg sys hV hH0) (b0eU_nonneg sys hV hH0) (hXi0.trans hXi) hXi0 hXi
    (norm_nonneg _) (by linarith [norm_nonneg (ψ t)]) (norm_nonneg _)
    (by linarith [norm_nonneg (H t)]) hε ht (cellC_nonneg hV hH0) rfl rfl
  have hfin' : freeKinC sys (tv R θ) Dbar * (Dst ^ 2 * (1 + t + Real.log (2 + K)) / K ^ 3) +
      freeKinC sys (tv R θ) Dbar * ((Dinf + Dst) * (1 + t) * ε) =
      freeKinC sys (tv R θ) Dbar * Dst ^ 2 * (1 + t + Real.log (2 + K)) / K ^ 3 +
        freeKinC sys (tv R θ) Dbar * (Dinf + Dst) * (1 + t) * ε := by ring
  rw [← hfin']
  linarith

end KineticLog
