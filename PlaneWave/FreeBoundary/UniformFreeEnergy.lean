import PlaneWave.FreeBoundary.UniformGridEnergy
import PlaneWave.FreeBoundary.LowerBound

/-!
# `app:free`, `L`-uniform constants, part 4: eq:free-energy with an `L`-uniform grid constant

`PlaneWave.FreeBoundary.LowerBound` proves `|E_{N,L} + C₀ - E_∞| ≤ δ + C(L) K^{-3}` (`free_grid_two_sided`) and its
exponential form (`free_grid_exponential`) with the `L`-dependent grid constant of `PlaneWave.FreeBoundary.GridEnergy`. With
the `L`-uniform grid theorem of `PlaneWave.FreeBoundary.UniformGridEnergy` (`gLSectorGridErrorU`) the same holds for `L ≥ 2π` with
`C K^{-3}`, where `C = gLErrorConstU sys V E_b` and the threshold `K ≥ K₀ = gLKThresholdU sys V E_b`
depend on the system, the total variation `V` of the profile and an energy budget
`E_b ≥ |E_L| + 1`, not on `L`:

* `free_grid_two_sidedU`: `|E_{N,L} + C₀ - E_∞| ≤ δ + C K^{-3}`;
* **`free_grid_exponentialU`**: `|E_{N,L} + C₀ - E_∞| ≤ C' e^{-γL} + C K^{-3}`,
  `γ = min(α, β)/2`.

Since `|E_L + C₀ - E_∞| ≤ C' e^{-γL}` and `|C₀| ≤ π/(2L)·(Σ|q_a q_b| + Σ|q_a| Z_ℓ)`, one budget
`E_b` (for instance `|E_∞| + 2` for large `L`) serves for all large cells.
-/

set_option autoImplicit false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15
  molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **`prop:free`, the two-sided bound, with an `L`-uniform grid constant.** As
`free_grid_two_sided`, for `L ≥ 2π`, with the grid error `C K^{-3}` of `gLSectorGridErrorU`:
for every energy budget `E_b ≥ |E_L| + 1` and `m ≥ η + 8` with `K = (2π/L) m ≥ K₀(E_b)`,
`|E_{N,L} + C₀ - E_∞| ≤ δ + C(E_b) K^{-3}`. -/
theorem free_grid_two_sidedU (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L)
    (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (hw : 0 < w) (hwL : w < retainedRadius L R0 ρ)
    {EL : ℝ} (hEL : IsGLTorusGroundEnergy sys lab L θ EL)
    {Einf τ τA : ℝ} (hτ : τ < 1) (hτA : τA < 1)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (happrox : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | cfgSq r < (retainedRadius L R0 ρ - w) ^ 2}ᶜ, ‖φ r‖ ^ 2 ≤ τ)
    (hA : ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy sys L θ u hu ≤ EL + ε ∧
      ∫ x in {x | cfgSq (cellCoord L x) < (retainedRadius L R0 ρ - w) ^ 2}ᶜ, ‖u x‖ ^ 2 ≤ τA) :
    |EL + (zeroModeShift sys L θ).re - Einf| ≤
        Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) ∧
      ∀ Eb : ℝ, |EL| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys (tv R θ) Eb ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) +
              PlaneWaveGridG.gLErrorConstU sys (tv R θ) Eb /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have h := free_grid_two_sided sys lab hlab hL0 hθ hR hR0 hρ hone P hP hpos hw hwL hEL hτ hτA
    hlow happrox hA
  refine ⟨h.1, fun Eb hEb m hm hK => ?_⟩
  obtain ⟨E, hE, hgrid⟩ := PlaneWaveGridG.gLSectorGridErrorU sys lab hlab hL hθ
  have hEE : E = EL := hE.unique hEL
  subst hEE
  obtain ⟨Eg, hEg, herr⟩ := hgrid Eb hEb m hm hK
  refine ⟨Eg, hEg, ?_⟩
  have h3 : |Eg + (zeroModeShift sys L θ).re - Einf| ≤
      |Eg - E| + |E + (zeroModeShift sys L θ).re - Einf| := by
    have := abs_add_le (Eg - E) (E + (zeroModeShift sys L θ).re - Einf)
    rw [show Eg - E + (E + (zeroModeShift sys L θ).re - Einf) =
      Eg + (zeroModeShift sys L θ).re - Einf by ring] at this
    exact this
  linarith [h.1]

/-- **eq:free-energy in exponential form, with an `L`-uniform grid constant.** As
`free_grid_exponential`, for `L ≥ 2π`: `|E_L + C₀ - E_∞| ≤ C' e^{-γ L}` and, for every energy
budget `E_b ≥ |E_L| + 1` and `m ≥ η + 8` with `K = (2π/L) m ≥ K₀(E_b)`,
`|E_{N,L} + C₀ - E_∞| ≤ C' e^{-γ L} + C(E_b) K^{-3}`; `K₀` and `C` do not depend on `L`. -/
theorem free_grid_exponentialU (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L)
    (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (hw : 0 < w) (hwL : w < retainedRadius L R0 ρ)
    {EL : ℝ} (hEL : IsGLTorusGroundEnergy sys lab L θ EL)
    {Einf A α A' β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsmall : A * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))) ≤ 1 / 2)
    (hsmall' : A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w))) ≤ 1 / 2)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (happrox : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | cfgSq r < (retainedRadius L R0 ρ - w) ^ 2}ᶜ, ‖φ r‖ ^ 2 ≤
        A * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))))
    (hA : ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy sys L θ u hu ≤ EL + ε ∧
      ∫ x in {x | cfgSq (cellCoord L x) < (retainedRadius L R0 ρ - w) ^ 2}ᶜ, ‖u x‖ ^ 2 ≤
        A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w)))) :
    |EL + (zeroModeShift sys L θ).re - Einf| ≤
        Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
          Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) ∧
      ∀ Eb : ℝ, |EL| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys (tv R θ) Eb ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
              Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) +
              PlaneWaveGridG.gLErrorConstU sys (tv R θ) Eb /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by

  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have h := free_grid_exponential sys lab hlab hL0 hθ hR hR0 hρ hone P hP hpos hw hwL hEL hα hβ
    hsmall hsmall' hlow happrox hA
  refine ⟨h.1, fun Eb hEb m hm hK => ?_⟩
  obtain ⟨E, hE, hgrid⟩ := PlaneWaveGridG.gLSectorGridErrorU sys lab hlab hL hθ
  have hEE : E = EL := hE.unique hEL
  subst hEE
  obtain ⟨Eg, hEg, herr⟩ := hgrid Eb hEb m hm hK
  refine ⟨Eg, hEg, ?_⟩
  have h3 : |Eg + (zeroModeShift sys L θ).re - Einf| ≤
      |Eg - E| + |E + (zeroModeShift sys L θ).re - Einf| := by
    have := abs_add_le (Eg - E) (E + (zeroModeShift sys L θ).re - Einf)
    rw [show Eg - E + (E + (zeroModeShift sys L θ).re - Einf) =
      Eg + (zeroModeShift sys L θ).re - Einf by ring] at this
    exact this
  linarith [h.1]

end

end FreeBoundary
