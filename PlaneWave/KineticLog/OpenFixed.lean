import PlaneWave.KineticLog.OpenSpin

/-!
# Logarithmic kinetic bound, part 33: a fixed molecule in growing cells

The system `sys` stores the clamped nuclei on the unit torus. A molecule with nuclei at fixed
physical positions `P_ℓ ∈ B_{R₀}(0)` sits in the cell of size `L` as `sysAt sys P L` (nuclei at
`-P_ℓ/L`), which changes with `L`. The constants of `prop:free-kinetic-log` depend on the masses
and charges only (`freeKinC`, `cellK0` take the same values for every `sysAt sys P L`), so one
constant and one threshold serve every cell size and every nuclear configuration:

* **`free_kinetic_log_at`**: `prop:free-kinetic-log` (general cutoff, (H_dom)) with `∃ C, K₀`
  before `L`, the profile, the nuclear positions `P`, the cutoff, the solution, the time, the
  kernel and the grid propagator;
* **`free_kinetic_log_spin_at`**: the same with finite internal spin;
* **`free_stopping_log_at`**, **`free_stopping_log_spin_at`**: `cor:free-stopping-log` in the
  same form.

The explicit cutoffs with clamped nuclei are treated in this way in
`free_kinetic_log_bo_uniform`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter MeasureTheory Set PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic PlaneWaveGrid
  PlaneWaveGridDynamics FreeBoundary FSNormal

namespace KineticLog

attribute [local instance] FreeBoundary.unitAddCircleMeasureSpaceFB15
  FreeBoundary.unitAddCircleProbabilityMeasureFB15 FreeBoundary.molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` for a fixed molecule** (general cutoff, (H_dom)): there are `C ≥ 0`
and `K₀ > 0`, depending only on the masses and charges of `sys`, the profile variation `V` and
the cutoff bound `D̄`, such that for every `L ≥ 2π`, every profile with `V_θ = V`, every
nuclear configuration `P` in `B_{R₀}(0)` (the system `sysAt sys P L`), every admissible cutoff,
every supplied free-space solution with leakage `ε` on `[0, t]` and cutoff-domain data, every
`m ≥ 8` with `K = 2πm/L ≥ K₀`, every kernel of the open-grid class and every grid propagator,
`|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C D_*² [1 + t + log(2 + K)]/K³
  + C (𝒟_∞ + D_*) (1 + t) ε`. -/
theorem free_kinetic_log_at (sys : CoulombSystem eta ν) (V Dbar : ℝ) (hV : 0 ≤ V)
    (hD : 0 ≤ Dbar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ {L R R0 ρ : ℝ} {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L), Profile R θ →
      R ≤ L / 2 → tv R θ = V → 0 ≤ R0 → 0 ≤ ρ → (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) →
      ∀ (P : ν → E3), (∀ l, ‖P l‖ ≤ R0) →
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
      HasGLHamiltonian (sysAt sys P L) L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀ →
      HasGLHamiltonian (sysAt sys P L) L θ h₀ h₁ →
      ∀ {Dinf Dst : ℝ}, ‖ψ 0‖ + ‖H 0‖ ≤ Dinf →
      ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
        (PlaneWaveGridG.gLref L θ (tv R θ)) m κ →
      ∀ (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)),
      (∀ x, Ug 0 x = x) →
      (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x) =
          Hgrid eta m (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei).toNucData
            κ (2 * Real.pi / L) (Ug t x)) →
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys)
          (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x))) t) →
      |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
          ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
        C * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
          C * (Dinf + Dst) * (1 + t) * ε := by
  refine ⟨freeKinC sys V Dbar, freeKinC_nonneg sys hV hD,
    cellK0 sys V molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ψ H grad hψd hHam hgrad t ε ht hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst p₀ m
    hm hK κ hκ Ug hg0 hgcomm hgderiv
  subst hVθ
  exact free_kinetic_log_endpoint (sysAt sys P L) hL2 hθ hR hR0 hρ hone P hP (fun l => rfl) X
    hret hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf hDst
    p₀ m hm hK hκ Ug hg0 hgcomm hgderiv

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` for a fixed molecule, with finite internal spin**: one constant and
one threshold for every cell size, nuclear configuration and finite spin set, with the
spin-summed leakage at each time and the Hilbert norms of the spin-inclusive space. -/
theorem free_kinetic_log_spin_at (sys : CoulombSystem eta ν) (V Dbar : ℝ) (hV : 0 ≤ V)
    (hD : 0 ≤ Dbar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ {L R R0 ρ : ℝ} {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L), Profile R θ →
      R ≤ L / 2 → tv R θ = V → 0 ≤ R0 → 0 ≤ ρ → (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) →
      ∀ (P : ν → E3), (∀ l, ‖P l‖ ≤ R0) →
      ∀ (X : Cutoff eta L), (∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ) →
      X.D1 ≤ Dbar → X.D2 ≤ Dbar →
      ∀ {Bone S : Set (Rcfg eta)}, MeasurableSet S → MeasurableSet Bone →
      (∀ r ∈ Bone, X.χ r = 1) → S ⊆ Boneᶜ → (∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0) →
      (∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0) →
      ∀ (ς : Type) [Fintype ς] {Ψ HΨ : ℝ → FreeSpinL2 eta ς}
        {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta},
      (∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s) →
      (∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ)) →
      (∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ)) →
      ∀ {t ε : ℝ}, 0 ≤ t → 0 ≤ ε →
      (∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2) →
      (∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2) →
      ∀ {h₀ h₁ : ς → MolecularPositionL2 eta},
      (∀ σ, HasGLHamiltonian (sysAt sys P L) L θ
        (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ)) →
      (∀ σ, HasGLHamiltonian (sysAt sys P L) L θ (h₀ σ) (h₁ σ)) →
      ∀ {Dinf Dst : ℝ}, ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf →
      Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
        Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
        (PlaneWaveGridG.gLref L θ (tv R θ)) m κ →
      ∀ (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)),
      (∀ x, Ug 0 x = x) →
      (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x) =
          Hgrid eta m (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei).toNucData
            κ (2 * Real.pi / L) (Ug t x)) →
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys)
          (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x))) t) →
      |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
          ((molecularPositionSynthesis eta).symm
            (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))| ≤
        C * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
          C * (Dinf + Dst) * (1 + t) * ε := by
  refine ⟨freeKinC sys V Dbar, freeKinC_nonneg sys hV hD,
    cellK0 sys V molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ς _ Ψ HΨ grad hψd hHam hgrad t ε ht hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst
    p₀ m hm hK κ hκ Ug hg0 hgcomm hgderiv
  subst hVθ
  exact free_kinetic_log_spin (sysAt sys P L) hL2 hθ hR hR0 hρ hone P hP (fun l => rfl) X hret
    hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀
    m hm hK hκ Ug hg0 hgcomm hgderiv

set_option maxHeartbeats 1000000 in
/-- **`cor:free-stopping-log` for a fixed molecule**: one constant and one threshold for every
cell size and nuclear configuration; with leakage on `[0, τ]`, `τ > 0`, and `v_p > 0`, the
secants differ by at most `(C D_*²/v_p)[1 + (1 + log(2 + K))/τ]/K³ + (C(𝒟_∞ + D_*)/v_p)(1 + 1/τ) ε`
(`C = 2 freeKinC sys V D̄`). -/
theorem free_stopping_log_at (sys : CoulombSystem eta ν) (V Dbar : ℝ) (hV : 0 ≤ V)
    (hD : 0 ≤ Dbar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ {L R R0 ρ : ℝ} {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L), Profile R θ →
      R ≤ L / 2 → tv R θ = V → 0 ≤ R0 → 0 ≤ ρ → (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) →
      ∀ (P : ν → E3), (∀ l, ‖P l‖ ≤ R0) →
      ∀ (X : Cutoff eta L), (∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ) →
      X.D1 ≤ Dbar → X.D2 ≤ Dbar →
      ∀ {Bone S : Set (Rcfg eta)}, MeasurableSet S → MeasurableSet Bone →
      (∀ r ∈ Bone, X.χ r = 1) → S ⊆ Boneᶜ → (∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0) →
      (∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0) →
      ∀ {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta},
      (∀ s, HasDerivAt ψ (-(Complex.I • H s)) s) → (∀ s, HasFreeHamiltonian sys P (ψ s) (H s)) →
      (∀ s, HasWeakGrad (ψ s) (grad s)) →
      ∀ {τ ε : ℝ}, 0 < τ → 0 ≤ ε →
      (∀ s ∈ Icc 0 τ, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2) →
      (∀ s ∈ Icc 0 τ, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2) →
      ∀ {h₀ h₁ : MolecularPositionL2 eta},
      HasGLHamiltonian (sysAt sys P L) L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀ →
      HasGLHamiltonian (sysAt sys P L) L θ h₀ h₁ →
      ∀ {Dinf Dst : ℝ}, ‖ψ 0‖ + ‖H 0‖ ≤ Dinf →
      ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
        (PlaneWaveGridG.gLref L θ (tv R θ)) m κ →
      ∀ (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)),
      (∀ x, Ug 0 x = x) →
      (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x) =
          Hgrid eta m (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei).toNucData
            κ (2 * Real.pi / L) (Ug t x)) →
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys)
          (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x))) t) →
      ∀ {vp : ℝ}, 0 < vp →
      |(freeKinQ sys p₀ (grad τ) - freeKinQ sys p₀ (grad 0)) / (vp * τ) -
          (regExpect sys (gF L) p₀ (Ug τ (regCoeff m ((molecularPositionSynthesis eta).symm
              (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0))))) -
            regExpect sys (gF L) p₀ (Ug 0 (regCoeff m ((molecularPositionSynthesis eta).symm
              (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))) / (vp * τ)| ≤
        C * Dst ^ 2 / vp * (1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ) /
            (2 * Real.pi / L * m) ^ 3 +
          C * (Dinf + Dst) / vp * (1 + 1 / τ) * ε := by
  refine ⟨2 * freeKinC sys V Dbar, by have := freeKinC_nonneg sys hV hD; positivity,
    cellK0 sys V molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ψ H grad hψd hHam hgrad τ ε hτ hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst p₀ m
    hm hK κ hκ Ug hg0 hgcomm hgderiv vp hvp
  subst hVθ
  exact free_stopping_log (sysAt sys P L) hL2 hθ hR hR0 hρ hone P hP (fun l => rfl) X hret hD1
    hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad hτ hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm
    hK hκ Ug hg0 hgcomm hgderiv hvp

set_option maxHeartbeats 1000000 in
/-- **`cor:free-stopping-log` for a fixed molecule, with finite internal spin**: one constant and
one threshold for every cell size, nuclear configuration and finite spin set
(`C = 2 freeKinC sys V D̄`). -/
theorem free_stopping_log_spin_at (sys : CoulombSystem eta ν) (V Dbar : ℝ) (hV : 0 ≤ V)
    (hD : 0 ≤ Dbar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ {L R R0 ρ : ℝ} {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L), Profile R θ →
      R ≤ L / 2 → tv R θ = V → 0 ≤ R0 → 0 ≤ ρ → (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) →
      ∀ (P : ν → E3), (∀ l, ‖P l‖ ≤ R0) →
      ∀ (X : Cutoff eta L), (∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ) →
      X.D1 ≤ Dbar → X.D2 ≤ Dbar →
      ∀ {Bone S : Set (Rcfg eta)}, MeasurableSet S → MeasurableSet Bone →
      (∀ r ∈ Bone, X.χ r = 1) → S ⊆ Boneᶜ → (∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0) →
      (∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0) →
      ∀ (ς : Type) [Fintype ς] {Ψ HΨ : ℝ → FreeSpinL2 eta ς}
        {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta},
      (∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s) →
      (∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ)) →
      (∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ)) →
      ∀ {τ ε : ℝ}, 0 < τ → 0 ≤ ε →
      (∀ s ∈ Icc 0 τ, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2) →
      (∀ s ∈ Icc 0 τ, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2) →
      ∀ {h₀ h₁ : ς → MolecularPositionL2 eta},
      (∀ σ, HasGLHamiltonian (sysAt sys P L) L θ
        (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ)) →
      (∀ σ, HasGLHamiltonian (sysAt sys P L) L θ (h₀ σ) (h₁ σ)) →
      ∀ {Dinf Dst : ℝ}, ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf →
      Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
        Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
        (PlaneWaveGridG.gLref L θ (tv R θ)) m κ →
      ∀ (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)),
      (∀ x, Ug 0 x = x) →
      (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x) =
          Hgrid eta m (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei).toNucData
            κ (2 * Real.pi / L) (Ug t x)) →
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys)
          (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x))) t) →
      ∀ {vp : ℝ}, 0 < vp →
      |(freeKinQS sys p₀ (grad τ) - freeKinQS sys p₀ (grad 0)) / (vp * τ) -
          (∑ σ, regExpect sys (gF L) p₀ (Ug τ (regCoeff m ((molecularPositionSynthesis eta).symm
              (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ))))) -
            ∑ σ, regExpect sys (gF L) p₀ (Ug 0 (regCoeff m ((molecularPositionSynthesis eta).symm
              (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))) / (vp * τ)| ≤
        C * Dst ^ 2 / vp * (1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ) /
            (2 * Real.pi / L * m) ^ 3 +
          C * (Dinf + Dst) / vp * (1 + 1 / τ) * ε := by
  refine ⟨2 * freeKinC sys V Dbar, by have := freeKinC_nonneg sys hV hD; positivity,
    cellK0 sys V molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ς _ Ψ HΨ grad hψd hHam hgrad τ ε hτ hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst
    p₀ m hm hK κ hκ Ug hg0 hgcomm hgderiv vp hvp
  subst hVθ
  exact free_stopping_log_spin (sysAt sys P L) hL2 hθ hR hR0 hρ hone P hP (fun l => rfl) X hret
    hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad hτ hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀
    m hm hK hκ Ug hg0 hgcomm hgderiv hvp

end KineticLog
