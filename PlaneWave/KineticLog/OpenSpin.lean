import PlaneWave.KineticLog.OpenStop

/-!
# Logarithmic kinetic bound, part 30: `prop:free-kinetic-log` and `cor:free-stopping-log` with spin

The spin-inclusive free-space space is `L²(ℝ^{3η}) ⊗ ℂ^ς` (`FreeSpinL2`), with the Hilbert norm
`‖Ψ‖² = Σ_σ ‖Ψ_σ‖²`; the Hamiltonians, the cutoff, the transplant, the register projector and the
kinetic energy act as the identity on spin. The leakage conditions are spin-summed at each time,
`Σ_σ ‖1_{(B^one)ᶜ} Ψ_σ(s)‖² ≤ ε²` and `Σ_σ ‖1_S ∇Ψ_σ(s)‖² ≤ ε²` for `s ∈ [0, t]`, as in
`free_dyn_torus_spin`; the componentwise leakages are never maximised separately in time.

The proof sums the three componentwise steps (free space, torus, cell-to-grid). The free-space
step uses the componentwise leakage at the single time `t`; the torus step uses the spin-inclusive
Duhamel estimate `‖φ(t) - e^{-iC₀t}(U(t) ⊗ 1) φ(0)‖ ≤ C ε t` of `free_dyn_torus_spin`; both are
summed by Cauchy–Schwarz over the spin components, and the cell-to-grid step is quadratic in the
data. The constants are those of the scalar theorem: there is no spin-dimension factor.

* `torus_pair_core`: the torus pairing with the state difference left explicit;
* **`free_kinetic_log_spin`** (`prop:free-kinetic-log` with spin, general cutoff, (H_dom));
* **`free_stopping_log_spin`** (`cor:free-stopping-log` with spin).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter MeasureTheory Set PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic PlaneWaveGrid
  PlaneWaveGridDynamics FreeBoundary FSNormal

namespace KineticLog

attribute [local instance] FreeBoundary.unitAddCircleMeasureSpaceFB15
  FreeBoundary.unitAddCircleProbabilityMeasureFB15 FreeBoundary.molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The torus pairing with an explicit state difference -/

set_option maxHeartbeats 1000000 in
/-- **The torus pairing** (`torus_pair_step` without the Duhamel estimate): for a state
`f ∈ D(H_∞)` with `H_∞ f = h`, `∂f = g` (`‖f‖, ‖g‖ ≤ N`) and the cell trajectory of the cut datum
`T(χ f₀)`,
`|⟨T(χf), T_p T(χf)⟩ - ⟨u_L(t), T_p u_L(t)⟩|
  ≤ ‖T(χ f) - e U(t) T(χ f₀)‖ (2 (‖h‖ + (Q/4)‖f‖ + c_χ N) + 2 b_U ‖f‖ + b_e Ξ/2)`
for every phase `|e| = 1`. -/
theorem torus_pair_core (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    (HL : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, HL (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta)
    (D : EvoData L HL)
    (hDU : ∀ t x, D.U t x = (molecularPositionSynthesis eta).symm
      (U t (molecularPositionSynthesis eta x)))
    {f0 : FreeL2 eta}
    (hDu0 : Sm eta L D.u₀ =
      (molecularPositionSynthesis eta).symm (X.chiW.cutL2 (pos_of_two_pi_le hL2) f0))
    {f h : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta} (hH : HasFreeHamiltonian sys P f h)
    (hg : HasWeakGrad f g) {N : ℝ} (hNf : ‖f‖ ≤ N) (hNg : ∀ a, ‖g a‖ ≤ N) (p₀ : Fin eta)
    (t : ℝ) {e : ℂ} (he1 : ‖e‖ = 1) :
    |(regKin sys (gF L) p₀).expect ((molecularPositionSynthesis eta).symm
        (X.chiW.cutL2 (pos_of_two_pi_le hL2) f)) -
      (regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀))| ≤
      ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) f - e • U t (X.chiW.cutL2 (pos_of_two_pi_le hL2) f0)‖ *
        (2 * (‖h‖ + zeroWeight sys / 4 * ‖f‖ + X.commConst * N) +
          2 * relBU sys (tv R θ) molecularCanonicalUnitHardyConstant * ‖f‖ +
          b0eU sys (tv R θ) molecularCanonicalUnitHardyConstant * D.Xi / 2) := by
  have hL := pos_of_two_pi_le hL2
  have hH0 := hardyUnit_nonneg
  have hPer := canonicalPeriodicCoulombHardyBound_explicit
  -- the `H²` lift of the transplant
  have htr := transplant_hasGLHamiltonian sys hL hR0 hρ hone P hP hpos X hret hH hg
  obtain ⟨wt, hwt1, hwt2⟩ := (hasGLHamiltonian_iff_H2 sys hL hθ hR HL hKernel _ _).mp htr
  -- the cell trajectory
  obtain ⟨w', hw'1, hw'2, -⟩ := traj_tails_gL sys HL hKernel molecularCanonicalUnitHardyConstant
    hL2 hθ hPer hH0 D t
  have hSwt : molecularH2StateMap eta (gF L) wt = (molecularPositionSynthesis eta).symm
      (X.chiW.cutL2 hL f) := by
    rw [← hwt1, LinearIsometryEquiv.symm_apply_apply]
    rfl
  have hSw' : molecularH2StateMap eta (gF L) w' = D.U t (Sm eta L D.u₀) := hw'1
  have hU' : D.U t (Sm eta L D.u₀) = (molecularPositionSynthesis eta).symm
      (U t (X.chiW.cutL2 hL f0)) := by
    rw [hDU, hDu0, LinearIsometryEquiv.apply_symm_apply]
  have hpair := expect_sub_le (regKin sys (gF L) p₀) wt (e • w')
  rw [map_smul, KinMult.expect_smul_unit _ he1, hSwt, hSw'] at hpair
  refine hpair.trans ?_
  have hdiff : ‖(molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL f) -
      e • D.U t (Sm eta L D.u₀)‖ = ‖X.chiW.cutL2 hL f - e • U t (X.chiW.cutL2 hL f0)‖ := by
    rw [hU', ← map_smul, ← map_sub, LinearIsometryEquiv.norm_map]
  have hcut : ∀ f' : FreeL2 eta, ‖X.chiW.cutL2 hL f'‖ ≤ ‖f'‖ := fun f' => by
    have h' := X.chiW.norm_cutL2_le hL f'
    have hB : X.chiW.B = 1 := rfl
    rw [hB, one_mul] at h'
    exact h'
  have hC0 := norm_zeroModeShift_le sys hL2 hθ hR
  have hcomm := norm_commT_le_N X hL sys.one_le_mass f g hNf hNg
  have hHwt : ‖HL wt‖ ≤ ‖h‖ + zeroWeight sys / 4 * ‖f‖ + X.commConst * N := by
    rw [← LinearIsometryEquiv.norm_map (molecularPositionSynthesis eta) (HL wt), hwt2]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) hcomm).trans ?_
    rw [norm_smul]
    have h1 := hcut h
    have h2 : ‖zeroModeShift sys L θ‖ * ‖X.chiW.cutL2 hL f‖ ≤ zeroWeight sys / 4 * ‖f‖ :=
      mul_le_mul hC0 (hcut f) (norm_nonneg _) (by have := zeroWeight_nonneg sys; positivity)
    linarith
  have hSwtn : ‖molecularH2StateMap eta (gF L) wt‖ ≤ ‖f‖ := by
    rw [hSwt, LinearIsometryEquiv.norm_map]
    exact hcut f
  have hC : 0 ≤ gLmassConst sys L (tv R θ) molecularCanonicalUnitHardyConstant :=
    gLmassConst_nonneg' sys (L := L) _ hθ
  have hT := kinetic_le_elliptic_gL sys L HL hKernel molecularCanonicalUnitHardyConstant hL hθ hPer
    hC wt
  rw [relB_gL_eq_U sys hL2 _ hH0] at hT
  have hb0 := relBU_nonneg sys hθ.tv_nonneg hH0
  have hμt : ‖(regKin sys (gF L) p₀).h2 wt‖ ≤
      2 * (‖h‖ + zeroWeight sys / 4 * ‖f‖ + X.commConst * N) +
        2 * relBU sys (tv R θ) molecularCanonicalUnitHardyConstant * ‖f‖ := by
    refine ((regKin sys (gF L) p₀).norm_h2_le wt).trans (hT.trans ?_)
    have e1 : 2 * ‖HL wt‖ ≤ 2 * (‖h‖ + zeroWeight sys / 4 * ‖f‖ + X.commConst * N) := by
      linarith
    have e2 : 2 * relBU sys (tv R θ) molecularCanonicalUnitHardyConstant *
        ‖molecularH2StateMap eta (2 * Real.pi / L) wt‖ ≤
        2 * relBU sys (tv R θ) molecularCanonicalUnitHardyConstant * ‖f‖ :=
      mul_le_mul_of_nonneg_left hSwtn (by positivity)
    linarith
  have hμ' : ‖(regKin sys (gF L) p₀).h2 (e • w')‖ ≤
      b0eU sys (tv R θ) molecularCanonicalUnitHardyConstant * D.Xi / 2 := by
    rw [map_smul, norm_smul, he1, one_mul]
    refine ((regKin sys (gF L) p₀).norm_h2_le w').trans ?_
    have := norm_nonneg (Sm eta L w')
    change ‖coulombFourierKineticH2 sys (gF L) w'‖ ≤ _
    linarith
  rw [hdiff]
  exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)

/-! ## `prop:free-kinetic-log` with spin -/

/-- `Σ_σ x_σ y_σ ≤ X Y` from `Σ x² ≤ X²`, `Σ y² ≤ Y²`. -/
lemma sum_mul_le_of_sq {ς : Type*} [Fintype ς] (x y : ς → ℝ) {X Y : ℝ} (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hx : ∑ σ, x σ ^ 2 ≤ X ^ 2) (hy : ∑ σ, y σ ^ 2 ≤ Y ^ 2) :
    ∑ σ, x σ * y σ ≤ X * Y := by
  refine (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y).trans ?_
  have h1 : Real.sqrt (∑ σ, x σ ^ 2) ≤ X := Real.sqrt_le_iff.mpr ⟨hX, hx⟩
  have h2 : Real.sqrt (∑ σ, y σ ^ 2) ≤ Y := Real.sqrt_le_iff.mpr ⟨hY, hy⟩
  exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) hX

/-- `Σ_σ (a_σ + b_σ)² ≤ (A + B)²` from `Σ a² ≤ A²`, `Σ b² ≤ B²`. -/
lemma sum_sq_add_le_of {ς : Type*} [Fintype ς] (a b : ς → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∑ σ, a σ ^ 2 ≤ A ^ 2) (hb : ∑ σ, b σ ^ 2 ≤ B ^ 2) :
    ∑ σ, (a σ + b σ) ^ 2 ≤ (A + B) ^ 2 := by
  have hab := sum_mul_le_of_sq a b hA hB ha hb
  have e : ∑ σ, (a σ + b σ) ^ 2 = ∑ σ, a σ ^ 2 + 2 * ∑ σ, a σ * b σ + ∑ σ, b σ ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [e]
  nlinarith

/-- The spin-inclusive free-space kinetic energy `Σ_σ ⟨Ψ_σ, T_p Ψ_σ⟩`. -/
noncomputable def freeKinQS (sys : CoulombSystem eta ν) (p : Fin eta) {ς : Type*} [Fintype ς]
    (grad : ς → Fin eta × Fin 3 → FreeL2 eta) : ℝ :=
  ∑ σ, freeKinQ sys p (grad σ)

set_option maxHeartbeats 2000000 in
/-- **`prop:free-kinetic-log` with finite internal spin** (general cutoff, (H_dom) for each spin
component): with the spin-summed leakage conditions on `[0, t]`,
`𝒟_∞ ≥ ‖Ψ₀‖ + ‖H_∞Ψ₀‖` and `D_* ≥ ‖φ₀‖ + ‖H_L φ₀‖ + ‖H_L² φ₀‖` in the Hilbert norms of the
spin-inclusive spaces,
`|Σ_σ ⟨Ψ_σ(t), T_p Ψ_σ(t)⟩ - Σ_σ ⟨Ψ_{g,σ}(t), T_p Ψ_{g,σ}(t)⟩|
  ≤ C D_*² [1 + t + log(2 + K)]/K³ + C (𝒟_∞ + D_*) (1 + t) ε`,
with the constant `C = freeKinC sys V_θ D̄` of the scalar theorem (no spin-dimension factor). -/
theorem free_kinetic_log_spin (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : ς → MolecularPositionL2 eta}
    (hdom0 : ∀ σ, HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ))
    (hdom1 : ∀ σ, HasGLHamiltonian sys L θ (h₀ σ) (h₁ σ))
    {Dinf Dst : ℝ} (hDinf : ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf)
    (hDst : Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
      Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst)
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
    |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))| ≤
      freeKinC sys (tv R θ) Dbar * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) /
          (2 * Real.pi / L * m) ^ 3 +
        freeKinC sys (tv R θ) Dbar * (Dinf + Dst) * (1 + t) * ε := by
  classical
  have hL : 0 < L := pos_of_two_pi_le hL2
  have hV : 0 ≤ tv R θ := hθ.tv_nonneg
  have hH0 := hardyUnit_nonneg
  have hPer := canonicalPeriodicCoulombHardyBound_explicit
  have hD10 : 0 ≤ X.D1 := (abs_nonneg _).trans (X.d1 0 (p₀, 0))
  have hD20 : 0 ≤ X.D2 := (abs_nonneg _).trans (X.d2 0 (p₀, 0))
  -- the cell and its evolutions
  obtain ⟨HL, hKernel, -⟩ := exists_gLFourierH2Operator sys hL hθ
    molecularCanonicalUnitHardyConstant hPer
  obtain ⟨U, hU0, hUadd, hUcont, hgraphU, hderivU, -⟩ := exists_gLPropagator sys hL hθ hR
  choose D hDU hDu0 hDXi using fun σ => exists_evoData_gL sys hL hθ hR HL hKernel U hU0 hUcont
    hgraphU hderivU (hdom0 σ) (hdom1 σ)
  -- componentwise solutions, conservation and regularity
  have hΨσ : ∀ σ s, HasDerivAt (fun s => Ψ s σ) (-(Complex.I • HΨ s σ)) s := fun σ s =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ς => FreeL2 eta) σ).hasFDerivAt.comp_hasDerivAt s (hψd s)
  have hcons : ∀ σ, ‖Ψ t σ‖ = ‖Ψ 0 σ‖ := fun σ =>
    norm_conserved sys P (ψ := fun s => Ψ s σ) (H := fun s => HΨ s σ) (hΨσ σ)
      (fun s => hHam s σ) t
  have hconsH : ∀ σ, ‖HΨ t σ‖ = ‖HΨ 0 σ‖ := fun σ =>
    norm_H_conserved sys P (ψ := fun s => Ψ s σ) (H := fun s => HΨ s σ) (hΨσ σ)
      (fun s => hHam s σ) t
  set n : ς → ℝ := fun σ => ‖Ψ 0 σ‖ + ‖HΨ 0 σ‖ with hn
  have hn0 : ∀ σ, 0 ≤ n σ := fun σ => by simp only [hn]; positivity
  have hc1 := one_le_relConstN sys
  have hreg : ∀ σ, ∃ g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta,
      (∀ b, HasWeakGrad (grad t σ b) (g2 b)) ∧ (∀ a, ‖grad t σ a‖ ≤ relConstN sys * n σ) ∧
        (∀ a b, ‖g2 a b‖ ≤ relConstN sys * n σ) := by
    intro σ
    obtain ⟨g', g2, -, -, -, hg', hg2, -, -, -, hb1, hb2, -, -⟩ :=
      free_hamiltonian_regularity_nuc sys P (hHam t σ)
    have hgg : g' = grad t σ := HasWeakGrad.unique hg' (hgrad t σ)
    rw [hgg] at hg2 hb1
    have hψH : ‖Ψ t σ‖ + ‖HΨ t σ‖ = n σ := by rw [hcons σ, hconsH σ]
    refine ⟨g2, hg2, fun a => ?_, fun a b => ?_⟩
    · rw [← hψH]; exact hb1 a
    · rw [← hψH]; exact hb2 a b
  choose g2 hg2 hNg hNg2 using hreg
  have hNψ : ∀ σ, ‖Ψ t σ‖ ≤ relConstN sys * n σ := fun σ => by
    have h1 : ‖Ψ t σ‖ ≤ n σ := by
      rw [hcons σ]; simp only [hn]; linarith [norm_nonneg (HΨ 0 σ)]
    nlinarith [hn0 σ]
  -- componentwise leakage at time `t`
  set ℓ : ς → ℝ := fun σ => ∫ r in Boneᶜ, ‖Ψ t σ r‖ ^ 2 with hℓ
  have hℓ0 : ∀ σ, 0 ≤ ℓ σ := fun σ => setIntegral_nonneg hBm.compl fun r _ => by positivity
  have hεσ : ∀ σ, ∫ r in Boneᶜ, ‖Ψ t σ r‖ ^ 2 ≤ Real.sqrt (ℓ σ) ^ 2 := fun σ => by
    rw [Real.sq_sqrt (hℓ0 σ)]
  have hℓsum : ∑ σ, Real.sqrt (ℓ σ) ^ 2 ≤ ε ^ 2 := by
    simp_rw [Real.sq_sqrt (hℓ0 _)]
    exact hleak0 t ⟨ht, le_rfl⟩
  -- the three componentwise steps
  have hA : ∀ σ, |freeKinQ sys p₀ (grad t σ) - (regKin sys (gF L) p₀).expect
      ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL (Ψ t σ)))| ≤
      3 / 2 * (1 + 4 * X.D1 + X.D1 ^ 2) * (relConstN sys * n σ) * Real.sqrt (ℓ σ) := fun σ =>
    free_torus_kin sys hL X hSm hBm hχB hSB hdS (hgrad t σ) (hg2 σ) (Real.sqrt_nonneg _) (hεσ σ)
      (hNψ σ) (hNg σ) (hNg2 σ) p₀
  set e := Complex.exp (-(Complex.I * (zeroModeShift sys L θ).re * t)) with he
  have he1 : ‖e‖ = 1 := by
    rw [he, Complex.norm_exp]
    simp
  set M : ς → ℝ := fun σ => 2 * (‖HΨ t σ‖ + zeroWeight sys / 4 * ‖Ψ t σ‖ +
      X.commConst * (relConstN sys * n σ)) +
      2 * relBU sys (tv R θ) molecularCanonicalUnitHardyConstant * ‖Ψ t σ‖ +
      b0eU sys (tv R θ) molecularCanonicalUnitHardyConstant * (D σ).Xi / 2 with hMdef
  have hB : ∀ σ, |(regKin sys (gF L) p₀).expect
      ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL (Ψ t σ))) -
      (regKin sys (gF L) p₀).expect ((D σ).U t (Sm eta L (D σ).u₀))| ≤
      ‖X.chiW.cutL2 hL (Ψ t σ) - e • U t (X.chiW.cutL2 hL (Ψ 0 σ))‖ * M σ := fun σ =>
    torus_pair_core sys hL2 hθ hR hR0 hρ hone P hP hpos X hret HL hKernel U (D σ) (hDU σ)
      (hDu0 σ) (hHam t σ) (hgrad t σ) (hNψ σ) (hNg σ) p₀ t he1
  have hC : ∀ σ, |(regKin sys (gF L) p₀).expect ((D σ).U t (Sm eta L (D σ).u₀)) -
      regExpect sys (gF L) p₀ (Ug t (regCoeff m (Sm eta L (D σ).u₀)))| ≤
      cellC sys (tv R θ) molecularCanonicalUnitHardyConstant * (D σ).Xi ^ 2 *
        (1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3 := fun σ =>
    cell_step sys hL2 hθ HL hKernel (D σ) p₀ m hm hK hκ Ug hg0 hgcomm hgderiv ht
  -- the spin sums
  have hsumn : ∑ σ, n σ ^ 2 ≤ Dinf ^ 2 := by
    have h1 : ∑ σ, ‖Ψ 0 σ‖ ^ 2 ≤ ‖Ψ 0‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
    have h2 : ∑ σ, ‖HΨ 0 σ‖ ^ 2 ≤ ‖HΨ 0‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
    refine (sum_sq_add_le_of (fun σ => ‖Ψ 0 σ‖) (fun σ => ‖HΨ 0 σ‖) (norm_nonneg _)
      (norm_nonneg _) h1 h2).trans ?_
    exact pow_le_pow_left₀ (by positivity) hDinf 2
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hXi : ∑ σ, (D σ).Xi ^ 2 ≤ Dst ^ 2 := by
    simp_rw [hDXi]
    refine (sum_sq_add3_le _ _ _).trans ?_
    exact pow_le_pow_left₀ (by positivity) hDst 2
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  have hΔ : ‖piLpMap (X.chiW.cutL2 hL) (Ψ t) - e • spinIso U t (piLpMap (X.chiW.cutL2 hL) (Ψ 0))‖
      ≤ X.commConst * ε * t :=
    (free_dyn_torus_spin sys hL hθ hR0 hρ hone P hP hpos U hU0 hUadd hUcont hderivU X hret hSm hBm
      hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 (χo := fun _ => (0 : ℝ))
      (fun _ => le_rfl) (fun _ => zero_le_one) measurable_const 0 (fun x => by simp)).1
  have hΔσ : ∑ σ, ‖X.chiW.cutL2 hL (Ψ t σ) - e • U t (X.chiW.cutL2 hL (Ψ 0 σ))‖ ^ 2 ≤
      (X.commConst * ε * t) ^ 2 := by
    have hcc : 0 ≤ X.commConst * ε * t := by unfold Cutoff.commConst; positivity
    refine le_trans (le_of_eq ?_) (pow_le_pow_left₀ (norm_nonneg _) hΔ 2)
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  set Q4 := zeroWeight sys / 4 with hQ4
  set rb := relBU sys (tv R θ) molecularCanonicalUnitHardyConstant with hrb
  set be := b0eU sys (tv R θ) molecularCanonicalUnitHardyConstant with hbe
  set c1 := relConstN sys with hc1def
  set cc := X.commConst with hccdef
  have hQ40 : 0 ≤ Q4 := by have := zeroWeight_nonneg sys; positivity
  have hrb0 : 0 ≤ rb := relBU_nonneg sys hV hH0
  have hbe0 : 0 ≤ be := b0eU_nonneg sys hV hH0
  have hcc0 : 0 ≤ cc := by rw [hccdef]; unfold Cutoff.commConst; positivity
  have hM : ∀ σ, M σ ≤ 2 * (1 + Q4 + cc * c1 + rb) * n σ + be / 2 * (D σ).Xi := by
    intro σ
    have h1 : ‖HΨ t σ‖ ≤ n σ := by
      rw [hconsH σ]; simp only [hn]; linarith [norm_nonneg (Ψ 0 σ)]
    have h2 : ‖Ψ t σ‖ ≤ n σ := by
      rw [hcons σ]; simp only [hn]; linarith [norm_nonneg (HΨ 0 σ)]
    have f1 : Q4 * ‖Ψ t σ‖ ≤ Q4 * n σ := mul_le_mul_of_nonneg_left h2 hQ40
    have f2 : rb * ‖Ψ t σ‖ ≤ rb * n σ := mul_le_mul_of_nonneg_left h2 hrb0
    have e1 : M σ = 2 * (‖HΨ t σ‖ + Q4 * ‖Ψ t σ‖ + cc * (c1 * n σ)) + 2 * rb * ‖Ψ t σ‖ +
        be * (D σ).Xi / 2 := rfl
    rw [e1]
    have e2 : 2 * (1 + Q4 + cc * c1 + rb) * n σ + be / 2 * (D σ).Xi =
        2 * (n σ + Q4 * n σ + cc * (c1 * n σ)) + 2 * rb * n σ + be * (D σ).Xi / 2 := by ring
    rw [e2]
    linarith
  have hM0 : ∀ σ, 0 ≤ M σ := fun σ => by
    have := (D σ).Xi_nonneg
    have := mul_nonneg hcc0 (mul_nonneg (by linarith : (0 : ℝ) ≤ c1) (hn0 σ))
    simp only [hMdef]
    positivity
  -- the sum of the free-space steps
  have hsumA : ∑ σ, 3 / 2 * (1 + 4 * X.D1 + X.D1 ^ 2) * (c1 * n σ) * Real.sqrt (ℓ σ) ≤
      3 / 2 * (1 + 4 * X.D1 + X.D1 ^ 2) * (c1 * Dinf) * ε := by
    have h := sum_mul_le_of_sq n (fun σ => Real.sqrt (ℓ σ)) hDinf0 hε hsumn hℓsum
    have e1 : ∑ σ, 3 / 2 * (1 + 4 * X.D1 + X.D1 ^ 2) * (c1 * n σ) * Real.sqrt (ℓ σ) =
        3 / 2 * (1 + 4 * X.D1 + X.D1 ^ 2) * c1 * ∑ σ, n σ * Real.sqrt (ℓ σ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [e1]
    have hk : 0 ≤ 3 / 2 * (1 + 4 * X.D1 + X.D1 ^ 2) * c1 := by
      have := (by linarith : (0 : ℝ) ≤ c1)
      positivity
    calc 3 / 2 * (1 + 4 * X.D1 + X.D1 ^ 2) * c1 * ∑ σ, n σ * Real.sqrt (ℓ σ)
        ≤ 3 / 2 * (1 + 4 * X.D1 + X.D1 ^ 2) * c1 * (Dinf * ε) :=
          mul_le_mul_of_nonneg_left h hk
      _ = _ := by ring
  -- the sum of the torus steps
  have hsumB : ∑ σ, ‖X.chiW.cutL2 hL (Ψ t σ) - e • U t (X.chiW.cutL2 hL (Ψ 0 σ))‖ * M σ ≤
      cc * ε * t * (2 * (Dinf + Q4 * Dinf + cc * (c1 * Dinf)) + 2 * rb * Dinf + be * Dst / 2) := by
    have hMs : ∑ σ, M σ ^ 2 ≤ (2 * (1 + Q4 + cc * c1 + rb) * Dinf + be / 2 * Dst) ^ 2 := by
      have hβ : 0 ≤ 2 * (1 + Q4 + cc * c1 + rb) := by
        have := mul_nonneg hcc0 (by linarith : (0 : ℝ) ≤ c1)
        positivity
      have h1 : ∑ σ, M σ ^ 2 ≤ ∑ σ, (2 * (1 + Q4 + cc * c1 + rb) * n σ + be / 2 * (D σ).Xi) ^ 2 :=
        Finset.sum_le_sum fun σ _ => pow_le_pow_left₀ (hM0 σ) (hM σ) 2
      refine h1.trans (sum_sq_add_le_of _ _ (by positivity) (by positivity) ?_ ?_)
      · have e : ∑ σ, (2 * (1 + Q4 + cc * c1 + rb) * n σ) ^ 2 =
            (2 * (1 + Q4 + cc * c1 + rb)) ^ 2 * ∑ σ, n σ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by ring
        have e' : (2 * (1 + Q4 + cc * c1 + rb) * Dinf) ^ 2 =
            (2 * (1 + Q4 + cc * c1 + rb)) ^ 2 * Dinf ^ 2 := by ring
        rw [e, e']
        exact mul_le_mul_of_nonneg_left hsumn (sq_nonneg _)
      · have e : ∑ σ, (be / 2 * (D σ).Xi) ^ 2 = (be / 2) ^ 2 * ∑ σ, (D σ).Xi ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by ring
        have e' : (be / 2 * Dst) ^ 2 = (be / 2) ^ 2 * Dst ^ 2 := by ring
        rw [e, e']
        exact mul_le_mul_of_nonneg_left hXi (sq_nonneg _)
    have hcct : 0 ≤ cc * ε * t := by positivity
    have hβ0 : 0 ≤ 2 * (1 + Q4 + cc * c1 + rb) * Dinf + be / 2 * Dst := by
      have := mul_nonneg hcc0 (by linarith : (0 : ℝ) ≤ c1)
      positivity
    refine (sum_mul_le_of_sq _ _ hcct hβ0 hΔσ hMs).trans (le_of_eq ?_)
    ring
  -- assemble
  have hsplit : ∀ σ, |freeKinQ sys p₀ (grad t σ) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
      ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL (Ψ 0 σ)))))| ≤
      3 / 2 * (1 + 4 * X.D1 + X.D1 ^ 2) * (c1 * n σ) * Real.sqrt (ℓ σ) +
        ‖X.chiW.cutL2 hL (Ψ t σ) - e • U t (X.chiW.cutL2 hL (Ψ 0 σ))‖ * M σ +
        cellC sys (tv R θ) molecularCanonicalUnitHardyConstant * (D σ).Xi ^ 2 *
          (1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3 := by
    intro σ
    have h1 := hA σ
    have h2 := hB σ
    have h3 := hC σ
    rw [hDu0 σ] at h3
    have t1 := abs_sub_le (freeKinQ sys p₀ (grad t σ))
      ((regKin sys (gF L) p₀).expect ((molecularPositionSynthesis eta).symm
        (X.chiW.cutL2 hL (Ψ t σ))))
      (regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL (Ψ 0 σ))))))
    have t2 := abs_sub_le ((regKin sys (gF L) p₀).expect ((molecularPositionSynthesis eta).symm
        (X.chiW.cutL2 hL (Ψ t σ))))
      ((regKin sys (gF L) p₀).expect ((D σ).U t (Sm eta L (D σ).u₀)))
      (regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL (Ψ 0 σ))))))
    rw [hDu0 σ] at t2 h2
    linarith
  have hsumC : ∑ σ, cellC sys (tv R θ) molecularCanonicalUnitHardyConstant * (D σ).Xi ^ 2 *
      (1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3 ≤
      cellC sys (tv R θ) molecularCanonicalUnitHardyConstant *
        (Dst ^ 2 * (1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3) := by
    have hK8 : (8 : ℝ) ≤ gF L * m := (cellK0_scales hV hK).1
    have hq : 0 ≤ (1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + gF L * m by linarith)
      positivity
    have e1 : ∑ σ, cellC sys (tv R θ) molecularCanonicalUnitHardyConstant * (D σ).Xi ^ 2 *
        (1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3 =
        cellC sys (tv R θ) molecularCanonicalUnitHardyConstant *
          ((∑ σ, (D σ).Xi ^ 2) * ((1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [e1]
    have e2 : Dst ^ 2 * (1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3 =
        Dst ^ 2 * ((1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXi hq)
      (cellC_nonneg hV hH0)
  unfold freeKinQS
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun σ _ => hsplit σ).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hV hK).1
  have hQ : 0 ≤ Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) /
      (2 * Real.pi / L * m) ^ 3 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 2 * Real.pi / L * m by linarith)
    positivity
  have hfin := free_kin_assemble (Dbar := Dbar) (c1 := c1) (ccb := commBar eta Dbar)
    (Q4 := Q4) (rb := rb) (be := be) (Dinf := Dinf) (Dst := Dst) (Xi := Dst) (Ht := Dinf)
    (ψt := Dinf) (N := c1 * Dinf) (ε := ε) (t := t)
    (cC := cellC sys (tv R θ) molecularCanonicalUnitHardyConstant)
    (A := locC sys (tv R θ) Dbar) (B := freeKinC sys (tv R θ) Dbar)
    hsumA hsumB hsumC hQ hD10 hD1 hc1 rfl hcc0
    (commConst_le_commBar X hD1 hD2) hQ40 hrb0 hbe0 hDst0 hDst0 le_rfl hDinf0 le_rfl hDinf0
    le_rfl hε ht (cellC_nonneg hV hH0) rfl rfl
  have hfin' : freeKinC sys (tv R θ) Dbar * (Dst ^ 2 * (1 + t + Real.log (2 + gF L * m)) /
      (gF L * m) ^ 3) + freeKinC sys (tv R θ) Dbar * ((Dinf + Dst) * (1 + t) * ε) =
      freeKinC sys (tv R θ) Dbar * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) /
          (2 * Real.pi / L * m) ^ 3 +
        freeKinC sys (tv R θ) Dbar * (Dinf + Dst) * (1 + t) * ε := by
    change freeKinC sys (tv R θ) Dbar * (Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) /
      (2 * Real.pi / L * m) ^ 3) + freeKinC sys (tv R θ) Dbar * ((Dinf + Dst) * (1 + t) * ε) = _
    ring
  rw [← hfin']
  exact hfin

/-! ## `cor:free-stopping-log` with spin -/

set_option maxHeartbeats 400000 in
/-- **`cor:free-stopping-log` with finite internal spin**: with the spin-summed leakage on
`[0, τ]`, `τ > 0`, and `v_p > 0`, the secants `[⟨T_p⟩(τ) - ⟨T_p⟩(0)]/(v_p τ)` of the
spin-inclusive free-space and grid trajectories differ by at most
`(2C D_*²/v_p)[1 + (1 + log(2 + K))/τ]/K³ + (2C(𝒟_∞ + D_*)/v_p)(1 + 1/τ) ε`,
`C = freeKinC sys V_θ D̄` (no spin-dimension factor). -/
theorem free_stopping_log_spin (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 τ, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 τ, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : ς → MolecularPositionL2 eta}
    (hdom0 : ∀ σ, HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ))
    (hdom1 : ∀ σ, HasGLHamiltonian sys L θ (h₀ σ) (h₁ σ))
    {Dinf Dst : ℝ} (hDinf : ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf)
    (hDst : Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
      Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst)
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
        (2 * Real.pi / L) x))) t)
    {vp : ℝ} (hvp : 0 < vp) :
    |(freeKinQS sys p₀ (grad τ) - freeKinQS sys p₀ (grad 0)) / (vp * τ) -
        (∑ σ, regExpect sys (gF L) p₀ (Ug τ (regCoeff m ((molecularPositionSynthesis eta).symm
            (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ))))) -
          ∑ σ, regExpect sys (gF L) p₀ (Ug 0 (regCoeff m ((molecularPositionSynthesis eta).symm
            (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))) / (vp * τ)| ≤
      2 * freeKinC sys (tv R θ) Dbar * Dst ^ 2 / vp *
          (1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ) / (2 * Real.pi / L * m) ^ 3 +
        2 * freeKinC sys (tv R θ) Dbar * (Dinf + Dst) / vp * (1 + 1 / τ) * ε := by
  have hV := hθ.tv_nonneg
  have hD10 : 0 ≤ X.D1 := (abs_nonneg _).trans (X.d1 0 (p₀, 0))
  have hDb : 0 ≤ Dbar := hD10.trans hD1
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hV hK).1
  have h1 := free_kinetic_log_spin sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hD1 hD2 hSm hBm
    hχB hSB hdS hd2S hψd hHam hgrad hτ.le hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm hK hκ Ug
    hg0 hgcomm hgderiv
  have h0 := free_kinetic_log_spin sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hD1 hD2 hSm hBm
    hχB hSB hdS hd2S hψd hHam hgrad le_rfl hε
    (fun s hs => hleak0 s ⟨hs.1, hs.2.trans hτ.le⟩) (fun s hs => hleak1 s ⟨hs.1, hs.2.trans hτ.le⟩)
    hdom0 hdom1 hDinf hDst p₀ m hm hK hκ Ug hg0 hgcomm hgderiv
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  exact secant_arith_free (freeKinC_nonneg sys hV hDb) hvp hτ (by linarith) (sq_nonneg Dst)
    (by linarith) hε h1 h0

end KineticLog
