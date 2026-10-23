import PlaneWave.KineticLog.OpenEndpoint

/-!
# Logarithmic kinetic bound, part 27: `prop:free-kinetic-log`, its forms and compatible cutoffs

* `exists_kinP`: the free-space kinetic energy `⟨ψ, T_p ψ⟩` of a state in `D(H_∞)` is defined:
  `T_p ψ ∈ L²` exists weakly and `⟪ψ, T_p ψ⟫ = freeKinQ` (so the endpoint compares
  `⟨ψ(t), T_p ψ(t)⟩` with the grid kinetic energy);
* **`free_kinetic_log`**: `prop:free-kinetic-log` with the constants before the quantifiers
  (general cutoff, (H_dom));
* **`free_kinetic_log_nbo`**, **`free_kinetic_log_bo`**: the compatible cutoffs, (H_dom) proved by
  the domain transfer of `prop:free-dyn` (`cut_state_domain_reg`, `cut_state_domain_reg_nuc`):
  `D_* ≤ (1 + Λ + Λ²) C_sys 𝒟_∞`, `𝒟_∞ = ‖ψ₀‖ + ‖H_∞ψ₀‖ + ‖H_∞²ψ₀‖`;
* **`free_kinetic_log_nbo_uniform`**, **`free_kinetic_log_bo_uniform`**: the explicit mass-weighted
  cutoff `χ_L = F(Σ_i m_i |x_i|²/(L/8)²)` (no clamped nuclei) and the explicit product cutoff
  (clamped nuclei, equal moving masses), uniform for `L ≥ L₀`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter MeasureTheory Set PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic PlaneWaveGrid
  PlaneWaveGridDynamics FreeBoundary FSNormal

namespace KineticLog

attribute [local instance] FreeBoundary.unitAddCircleMeasureSpaceFB15
  FreeBoundary.unitAddCircleProbabilityMeasureFB15 FreeBoundary.molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The free-space kinetic energy -/

/-- **`⟨ψ, T_p ψ⟩` for `ψ ∈ D(H_∞)`**: `T_p ψ` exists in `L²` (weakly) and every weak image `z`
has `⟪ψ, z⟫ = (1/(2 m_p)) Σ_c ‖∂_{p,c} ψ‖² = freeKinQ`. -/
theorem exists_kinP (sys : CoulombSystem eta ν) (P : ν → E3) {f h : FreeL2 eta}
    (hH : HasFreeHamiltonian sys P f h) {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad f g)
    (p : Fin eta) :
    (∃ z : FreeL2 eta, HasFreeWeakKinetic (massP sys p) f z) ∧
      ∀ z : FreeL2 eta, HasFreeWeakKinetic (massP sys p) f z →
        ⟪f, z⟫_ℂ = (freeKinQ sys p g : ℂ) := by
  obtain ⟨g', g2, -, -, -, hg', hg2, -⟩ := free_hamiltonian_regularity_nuc sys P hH
  exact ⟨⟨_, hasFreeWeakKinetic_massP sys p hg' hg2⟩, fun z hz => inner_kinP_eq sys p hz hg⟩

/-! ## The constants before the quantifiers -/

/-- **`prop:free-kinetic-log`** (general cutoff, (H_dom)): there are `C ≥ 0` and `K₀ > 0`,
depending only on the system, the profile bound `V` and the cutoff bound `D̄`, such that for every
`L ≥ 2π`, every profile with `V_θ = V`, every admissible cutoff with derivative bounds `D̄`, every
supplied free-space solution with leakage `ε` on `[0, t]` and cutoff-domain data, every `m ≥ 8`
with `K = 2πm/L ≥ K₀`, every kernel of the open-grid class and every grid propagator,
`|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C D_*² [1 + t + log(2 + K)]/K³
  + C (𝒟_∞ + D_*) (1 + t) ε`. -/
theorem free_kinetic_log (sys : CoulombSystem eta ν) (V Dbar : ℝ) (hV : 0 ≤ V) (hD : 0 ≤ Dbar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ {L R R0 ρ : ℝ} {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L), Profile R θ →
      R ≤ L / 2 → tv R θ = V → 0 ≤ R0 → 0 ≤ ρ → (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) →
      ∀ (P : ν → E3), (∀ l, ‖P l‖ ≤ R0) →
      (∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle)) →
      ∀ (X : Cutoff eta L), (∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ) →
      X.D1 ≤ Dbar → X.D2 ≤ Dbar →
      ∀ {Bone S : Set (Rcfg eta)}, MeasurableSet S → MeasurableSet Bone →
      (∀ r ∈ Bone, X.χ r = 1) → S ⊆ Boneᶜ → (∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0) →
      (∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0) →
      ∀ {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta},
      (∀ s, HasDerivAt ψ (-(Complex.I • H s)) s) → (∀ s, HasFreeHamiltonian sys P (ψ s) (H s)) →
      (∀ s, HasWeakGrad (ψ s) (grad s)) →
      ∀ {t ε : ℝ}, 0 ≤ t → 0 ≤ ε →
      (∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2) →
      (∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2) →
      ∀ {h₀ h₁ : MolecularPositionL2 eta},
      HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀ →
      HasGLHamiltonian sys L θ h₀ h₁ →
      ∀ {Dinf Dst : ℝ}, ‖ψ 0‖ + ‖H 0‖ ≤ Dinf →
      ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
        (PlaneWaveGridG.gLref L θ (tv R θ)) m κ →
      ∀ (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)),
      (∀ x, Ug 0 x = x) →
      (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        κ (2 * Real.pi / L) (Ug t x)) →
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
          (2 * Real.pi / L) x))) t) →
      |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
          ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
        C * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
          C * (Dinf + Dst) * (1 + t) * ε := by
  refine ⟨freeKinC sys V Dbar, freeKinC_nonneg sys hV hD,
    cellK0 sys V molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP hpos X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ψ H grad hψd hHam hgrad t ε ht hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst p₀ m
    hm hK κ hκ Ug hg0 hgcomm hgderiv
  subst hVθ
  exact free_kinetic_log_endpoint sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hD1 hD2 hSm hBm hχB
    hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm hK hκ Ug hg0
    hgcomm hgderiv

/-! ## Domain transfer -/

/-- `D_* ≤ G 𝒟` turns the bound of `prop:free-kinetic-log` into one in `𝒟` alone. -/
lemma transfer_arith {C G Dinf Dst q K t ε : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G) (hDinf : 0 ≤ Dinf)
    (hDst0 : 0 ≤ Dst) (hDst : Dst ≤ G * Dinf) (hq : 0 ≤ q) (hK : 0 < K) (ht : 0 ≤ t)
    (hε : 0 ≤ ε) :
    C * Dst ^ 2 * q / K ^ 3 + C * (Dinf + Dst) * (1 + t) * ε ≤
      C * (1 + G) ^ 2 * Dinf ^ 2 * q / K ^ 3 + C * (1 + G) ^ 2 * Dinf * (1 + t) * ε := by
  have hK3 : 0 < K ^ 3 := by positivity
  have h1 : Dst ^ 2 ≤ (1 + G) ^ 2 * Dinf ^ 2 := by
    have e : (1 + G) ^ 2 * Dinf ^ 2 = ((1 + G) * Dinf) ^ 2 := by ring
    rw [e]
    refine pow_le_pow_left₀ hDst0 (hDst.trans ?_) 2
    nlinarith
  have h2 : Dinf + Dst ≤ (1 + G) ^ 2 * Dinf := by
    have e1 : Dinf + Dst ≤ (1 + G) * Dinf := by nlinarith
    have e2 : (1 + G) * Dinf ≤ (1 + G) ^ 2 * Dinf := by
      have : (1 + G) ≤ (1 + G) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this hDinf
    linarith
  have t1 : C * Dst ^ 2 * q / K ^ 3 ≤ C * (1 + G) ^ 2 * Dinf ^ 2 * q / K ^ 3 := by
    apply div_le_div_of_nonneg_right _ hK3.le
    have := mul_le_mul_of_nonneg_left h1 hC
    have := mul_le_mul_of_nonneg_right this hq
    calc C * Dst ^ 2 * q ≤ C * ((1 + G) ^ 2 * Dinf ^ 2) * q := this
      _ = _ := by ring
  have t2 : C * (Dinf + Dst) * (1 + t) * ε ≤ C * (1 + G) ^ 2 * Dinf * (1 + t) * ε := by
    have h3 := mul_le_mul_of_nonneg_left h2 hC
    have h4 : 0 ≤ (1 + t) * ε := mul_nonneg (by linarith) hε
    have := mul_le_mul_of_nonneg_right h3 h4
    calc C * (Dinf + Dst) * (1 + t) * ε = C * (Dinf + Dst) * ((1 + t) * ε) := by ring
      _ ≤ C * ((1 + G) ^ 2 * Dinf) * ((1 + t) * ε) := this
      _ = _ := by ring
  linarith

/-! ## Compatible cutoffs without clamped nuclei -/

/-- The constant of `prop:free-kinetic-log` for a mass-compatible cutoff (no clamped nuclei):
`C (1 + (1 + Λ + Λ²) C_sys)²`, `Λ = domConst` the domain-transfer constant of `prop:free-dyn`. -/
noncomputable def freeKinConstNBO (sys : CoulombSystem eta ν) (V Dbar Cbar : ℝ) : ℝ :=
  freeKinC sys V Dbar * (1 + (1 + domConst sys.charge (zeroWeight sys / 4) Dbar Cbar +
    domConst sys.charge (zeroWeight sys / 4) Dbar Cbar ^ 2) * regConst sys) ^ 2

set_option maxHeartbeats 400000 in
/-- **`prop:free-kinetic-log` without clamped nuclei, mass-compatible cutoff**: the cutoff-domain
condition is proved (`cut_state_domain_reg`) and the data enter through
`‖ψ₀‖ + ‖H_∞ψ₀‖ + ‖H_∞²ψ₀‖ ≤ 𝒟`:
`|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C 𝒟² [1 + t + log(2 + K)]/K³ + C 𝒟 (1 + t) ε`,
`C = freeKinConstNBO sys V_θ D̄ C̄`. -/
theorem free_kinetic_log_nbo [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ}
    {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0)
    (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Dbar Cbar : ℝ} (hDbar : X.D ≤ Dbar) (hCbar : X.C ≤ Cbar)
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
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
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
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
      freeKinConstNBO sys (tv R θ) Dbar Cbar * D ^ 2 *
          (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstNBO sys (tv R θ) Dbar Cbar * D * (1 + t) * ε := by
  have hL := pos_of_two_pi_le hL2
  have hV := hθ.tv_nonneg
  have hc₀ := norm_zeroModeShift_le sys hL2 hθ hR
  obtain ⟨h₀, h₁, hd0, hd1, n0, n1, n2⟩ := cut_state_domain_reg sys hL hR0 hρ hone P hP hpos X
    hret (hHam 0) hH1 hc₀
  have hQ0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have hD0 : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  have hC0 : 0 ≤ Cbar := X.C_nonneg.trans hCbar
  set Λ := domConst sys.charge (zeroWeight sys / 4) Dbar Cbar with hΛ
  have hΛX : domConst sys.charge (zeroWeight sys / 4) X.D X.C ≤ Λ := domConst_mono _ hDbar hCbar
  have hΛX1 : 1 ≤ domConst sys.charge (zeroWeight sys / 4) X.D X.C :=
    one_le_domConst _ hQ0 X.D_nonneg X.C_nonneg
  have hΛ0 : 0 ≤ Λ := by linarith
  have hreg := one_le_regConst sys
  have hdat : 0 ≤ ‖ψ 0‖ + ‖H 0‖ + ‖k‖ := by positivity
  have hD00 : 0 ≤ D := hdat.trans hD
  set N := regConst sys * (‖ψ 0‖ + ‖H 0‖ + ‖k‖) with hNdef
  have hN : N ≤ regConst sys * D := mul_le_mul_of_nonneg_left hD (by linarith)
  have hN0 : 0 ≤ N := mul_nonneg (by linarith) hdat
  have hDst : ‖X.toCutoff.chiW.cutL2 hL (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤
      (1 + Λ + Λ ^ 2) * regConst sys * D := by
    have e1 : domConst sys.charge (zeroWeight sys / 4) X.D X.C * N ≤ Λ * N :=
      mul_le_mul_of_nonneg_right hΛX hN0
    have e2 : domConst sys.charge (zeroWeight sys / 4) X.D X.C ^ 2 * N ≤ Λ ^ 2 * N :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hΛX 2) hN0
    have e3 : (1 + Λ + Λ ^ 2) * N ≤ (1 + Λ + Λ ^ 2) * (regConst sys * D) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    have e4 : (1 + Λ + Λ ^ 2) * N = N + Λ * N + Λ ^ 2 * N := by ring
    have e5 : (1 + Λ + Λ ^ 2) * (regConst sys * D) = (1 + Λ + Λ ^ 2) * regConst sys * D := by
      ring
    linarith
  have hDinf : ‖ψ 0‖ + ‖H 0‖ ≤ D := by linarith [norm_nonneg k]
  have h := free_kinetic_log_endpoint sys hL2 hθ hR hR0 hρ hone P hP hpos X.toCutoff hret hDbar
    hDbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hd0 hd1 hDinf hDst p₀ m hm hK
    hκ Ug hg0 hgcomm hgderiv
  refine h.trans ?_
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hV hK).1
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hG : 0 ≤ (1 + Λ + Λ ^ 2) * regConst sys := by
    have : 0 ≤ Λ := by linarith
    have : 0 ≤ regConst sys := by linarith
    positivity
  have := transfer_arith (C := freeKinC sys (tv R θ) Dbar) (G := (1 + Λ + Λ ^ 2) * regConst sys)
    (q := 1 + t + Real.log (2 + 2 * Real.pi / L * m)) (K := 2 * Real.pi / L * m)
    (freeKinC_nonneg sys hV hD0) hG hD00 (by positivity) le_rfl (by positivity) (by linarith) ht hε
  unfold freeKinConstNBO
  rw [← hΛ]
  refine this.trans (le_of_eq ?_)
  ring

/-! ## Compatible cutoffs with clamped nuclei -/

/-- The constant of `prop:free-kinetic-log` for a cutoff flat near the clamped nuclei:
`C (1 + (1 + Λ' + Λ'²) C'_sys)²`, `Λ' = domConstN`. -/
noncomputable def freeKinConstBO (sys : CoulombSystem eta ν) (V Dbar Cbar δ : ℝ) : ℝ :=
  freeKinC sys V Dbar * (1 + (1 + domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4)
    Dbar Cbar δ + domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) Dbar Cbar δ ^ 2) *
      regConstN sys) ^ 2

set_option maxHeartbeats 400000 in
/-- **`prop:free-kinetic-log` with clamped nuclei, cutoff flat near the nuclei**: the
cutoff-domain condition is proved (`cut_state_domain_reg_nuc`):
`|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C 𝒟² [1 + t + log(2 + K)]/K³ + C 𝒟 (1 + t) ε`,
`C = freeKinConstBO sys V_θ D̄ C̄ δ`. -/
theorem free_kinetic_log_bo (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ)
    {Dbar Cbar : ℝ} (hDbar : X.D ≤ Dbar) (hCbar : X.C ≤ Cbar)
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
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
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
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
      freeKinConstBO sys (tv R θ) Dbar Cbar δ * D ^ 2 *
          (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstBO sys (tv R θ) Dbar Cbar δ * D * (1 + t) * ε := by
  have hL := pos_of_two_pi_le hL2
  have hV := hθ.tv_nonneg
  have hc₀ := norm_zeroModeShift_le sys hL2 hθ hR
  obtain ⟨h₀, h₁, hd0, hd1, n0, n1, n2⟩ := cut_state_domain_reg_nuc sys hL hR0 hρ hone P hP hpos
    X hret hδ hflat (hHam 0) hH1 hc₀
  have hQ0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have hD0 : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  set Λ := domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) Dbar Cbar δ with hΛ
  have hΛX : domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) X.D X.C δ ≤ Λ :=
    domConstN_mono _ _ _ hDbar hCbar
  have hΛX1 : 1 ≤ domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) X.D X.C δ :=
    one_le_domConstN _ _ hQ0 X.D_nonneg X.C_nonneg
  have hΛ0 : 0 ≤ Λ := by linarith
  have hreg := one_le_regConstN sys
  have hdat : 0 ≤ ‖ψ 0‖ + ‖H 0‖ + ‖k‖ := by positivity
  have hD00 : 0 ≤ D := hdat.trans hD
  set N := regConstN sys * (‖ψ 0‖ + ‖H 0‖ + ‖k‖) with hNdef
  have hN : N ≤ regConstN sys * D := mul_le_mul_of_nonneg_left hD (by linarith)
  have hN0 : 0 ≤ N := mul_nonneg (by linarith) hdat
  have hDst : ‖X.toCutoff.chiW.cutL2 hL (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤
      (1 + Λ + Λ ^ 2) * regConstN sys * D := by
    have e1 : domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) X.D X.C δ * N ≤
        Λ * N := mul_le_mul_of_nonneg_right hΛX hN0
    have e2 : domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) X.D X.C δ ^ 2 * N ≤
        Λ ^ 2 * N := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hΛX 2) hN0
    have e3 : (1 + Λ + Λ ^ 2) * N ≤ (1 + Λ + Λ ^ 2) * (regConstN sys * D) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    have e4 : (1 + Λ + Λ ^ 2) * N = N + Λ * N + Λ ^ 2 * N := by ring
    have e5 : (1 + Λ + Λ ^ 2) * (regConstN sys * D) = (1 + Λ + Λ ^ 2) * regConstN sys * D := by
      ring
    linarith
  have hDinf : ‖ψ 0‖ + ‖H 0‖ ≤ D := by linarith [norm_nonneg k]
  have h := free_kinetic_log_endpoint sys hL2 hθ hR hR0 hρ hone P hP hpos X.toCutoff hret hDbar
    hDbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hd0 hd1 hDinf hDst p₀ m hm hK
    hκ Ug hg0 hgcomm hgderiv
  refine h.trans ?_
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hV hK).1
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hG : 0 ≤ (1 + Λ + Λ ^ 2) * regConstN sys := by
    have : 0 ≤ Λ := by linarith
    have : 0 ≤ regConstN sys := by linarith
    positivity
  have := transfer_arith (C := freeKinC sys (tv R θ) Dbar) (G := (1 + Λ + Λ ^ 2) * regConstN sys)
    (q := 1 + t + Real.log (2 + 2 * Real.pi / L * m)) (K := 2 * Real.pi / L * m)
    (freeKinC_nonneg sys hV hD0) hG hD00 (by positivity) le_rfl (by positivity) (by linarith) ht hε
  unfold freeKinConstBO
  rw [← hΛ]
  refine this.trans (le_of_eq ?_)
  ring

end KineticLog
