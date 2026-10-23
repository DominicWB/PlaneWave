import PlaneWave.KineticLog.GridEndpoint
import PlaneWave.FluxSourceSpin

/-!
# Logarithmic kinetic bound, part 16: the periodic grid endpoints with finite internal spin

A spin-inclusive datum is a family `Ds : S → EvoData L H` over a finite set `S` of spin
configurations (`FSSpin`).  The grid Hamiltonian, the register projector `P'` and the kinetic
observable act as the identity on spin, so the spin-inclusive grid trajectory is
`(U_g(t) ⊗ 1)(P' ⊗ 1) Ψ₀ = (U_g(t) P' Ψ₀,σ)_σ` (`gridS`) and the grid kinetic energy is
`⟨Φ, (T_p ⊗ 1) Φ⟩ = Σ_σ ⟨Φ_σ, T_p Φ_σ⟩` (`regExpectS`).

* `thm_kinetic_log_grid_spin` (`thm:kinetic-log`, grid case with spin);
* `cor_stopping_log_grid_spin` (`cor:stopping-log`, grid case with spin).

The constants are those of the scalar theorems: the componentwise bounds are summed with
`Σ_σ Ξ_σ² ≤ Ξ_S²` (`FSSpin.sum_Xi_sq_le`), so there is no factor depending on `|S|`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal
open FSGalerkin (Kc)

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν] {S : Type} [Fintype S]

section Defs

variable {L : ℝ} {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}

/-- The spin-inclusive grid trajectory `(U_g(t) ⊗ 1)(P' ⊗ 1) Ψ₀`. -/
noncomputable def gridS (m : ℕ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (Ds : S → EvoData L H) (t : ℝ) : S → EuclideanSpace ℂ (RCfg eta m) :=
  fun σ => Ug t (regCoeff m (Sm eta L (Ds σ).u₀))

/-- The spin-inclusive register kinetic energy `⟨Φ, (T_p ⊗ 1) Φ⟩ = Σ_σ ⟨Φ_σ, T_p Φ_σ⟩`. -/
noncomputable def regExpectS (sys : CoulombSystem eta ν) (g : ℝ) (p : Fin eta) {m : ℕ}
    (Φ : S → EuclideanSpace ℂ (RCfg eta m)) : ℝ :=
  ∑ σ, regExpect sys g p (Φ σ)

end Defs

section Spin

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **`thm:kinetic-log`, grid case with spin**: for every spin-inclusive datum, every register
radius `2m` with `m ≥ m₀`, every kernel of the class `IsGridKernel`, every grid propagator and
every `t ≥ 0`,
`|⟨Ψ(t), (T_{p₀} ⊗ 1) Ψ(t)⟩ - ⟨Ψ_g(t), (T_{p₀} ⊗ 1) Ψ_g(t)⟩| ≤ C Ξ_S² [1 + t + log(2+K)]/K³`. -/
theorem thm_kinetic_log_grid_spin (p₀ : Fin eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ {κ : Lat3 → ℝ},
      IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
          (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys)
            (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            κ (2 * Real.pi / L) x))) t) →
        ∀ (Ds : S → EvoData L H) (t : ℝ), 0 ≤ t →
          |FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds t) -
              regExpectS sys (gF L) p₀ (gridS m Ug Ds t)| ≤
            C * FSSpin.XiS Ds ^ 2 * ((1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3) := by
  obtain ⟨C, hC, m₀, h⟩ := thm_kinetic_log_grid sys H hKernel Hunit hL hPeriodic p₀
  refine ⟨C, hC, max m₀ (mGrid sys L Hunit),
    fun m hm κ hκ Ug hg0 hgcomm hgderiv Ds t ht => ?_⟩
  obtain ⟨-, hK8, -, -⟩ := mGrid_scales hL (le_trans (le_max_right _ _) hm)
  have hK0 : 0 < Kc L m := by change 0 < gF L * m; linarith
  have hr : 0 ≤ (1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Kc L m by linarith)
    positivity
  have e : FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds t) -
      regExpectS sys (gF L) p₀ (gridS m Ug Ds t) =
      ∑ σ, ((regKin sys (gF L) p₀).expect (FSSpin.exactS Ds t σ) -
        regExpect sys (gF L) p₀ (gridS m Ug Ds t σ)) := by
    simp only [FSSpin.expectS, regExpectS, Finset.sum_sub_distrib]
  rw [e]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h m (le_trans (le_max_left _ _) hm) hκ Ug hg0 hgcomm hgderiv (Ds σ) t ht
  calc _ ≤ C * (Ds σ).Xi ^ 2 * (1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3) := by ring

include hKernel hL hPeriodic in
/-- **`cor:stopping-log`, grid case with spin**: for every window `[0, τ]`, `τ > 0`, and
reference speed `v_p > 0`, the spin-inclusive signed secants of the exact and grid trajectories
differ by at most `(C Ξ_S²/v_p) [1 + (1 + log(2 + K))/τ]/K³`. -/
theorem cor_stopping_log_grid_spin (p₀ : Fin eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ {κ : Lat3 → ℝ},
      IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
          (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys)
            (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            κ (2 * Real.pi / L) x))) t) →
        ∀ (Ds : S → EvoData L H) {vp τ : ℝ}, 0 < vp → 0 < τ →
          |(FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds τ) -
                FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds 0)) / (vp * τ) -
              (regExpectS sys (gF L) p₀ (gridS m Ug Ds τ) -
                regExpectS sys (gF L) p₀ (gridS m Ug Ds 0)) / (vp * τ)| ≤
            C * FSSpin.XiS Ds ^ 2 * ((1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 / vp) := by
  obtain ⟨C, hC, m₀, h⟩ := cor_stopping_log_grid sys H hKernel Hunit hL hPeriodic p₀
  refine ⟨C, hC, max m₀ (mGrid sys L Hunit),
    fun m hm κ hκ Ug hg0 hgcomm hgderiv Ds vp τ hvp hτ => ?_⟩
  obtain ⟨-, hK8, -, -⟩ := mGrid_scales hL (le_trans (le_max_right _ _) hm)
  have hK0 : 0 < Kc L m := by change 0 < gF L * m; linarith
  have hr : 0 ≤ (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 / vp := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Kc L m by linarith)
    positivity
  have e : (FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds τ) -
        FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds 0)) / (vp * τ) -
      (regExpectS sys (gF L) p₀ (gridS m Ug Ds τ) -
        regExpectS sys (gF L) p₀ (gridS m Ug Ds 0)) / (vp * τ) =
      ∑ σ, (((regKin sys (gF L) p₀).expect (FSSpin.exactS Ds τ σ) -
          (regKin sys (gF L) p₀).expect (FSSpin.exactS Ds 0 σ)) / (vp * τ) -
        (regExpect sys (gF L) p₀ (gridS m Ug Ds τ σ) -
          regExpect sys (gF L) p₀ (gridS m Ug Ds 0 σ)) / (vp * τ)) := by
    simp only [FSSpin.expectS, regExpectS, ← Finset.sum_sub_distrib, Finset.sum_div]
  rw [e]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h m (le_trans (le_max_left _ _) hm) hκ Ug hg0 hgcomm hgderiv (Ds σ) hvp hτ
  calc _ ≤ C * (Ds σ).Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 / vp) := by ring

end Spin

end KineticLog
