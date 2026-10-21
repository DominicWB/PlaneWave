import PlaneWave.FreeBoundary.GridEnergy
import PlaneWave.FreeBoundary.Transplant

/-!
# `app:free`, part 11: the upper half of the composite bound

Combines the grid theorem for the `g_L` kernel (`PlaneWave.FreeBoundary.GridEnergy`, `|E_{N,L} - E_L| ≤ C K^{-3}`) with the
transplant inequality (`PlaneWave.FreeBoundary.Transplant`): when retained free-space trial states reach `E_∞ + δ`, the grid
energy satisfies `E_{N,L} + C₀ ≤ E_∞ + δ + C K^{-3}`, `K = 2πm/L`, `C₀` the zero-mode shift.
-/

set_option autoImplicit false

open MeasureTheory PlaneWaveCertificate
open scoped ComplexConjugate

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **The upper half of `|E_{N,L} - E_∞| ≤ ...`.** -/
theorem free_grid_upper (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {Einf δ : ℝ}
    (htrial : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ SuppRet L R0 ρ φ ∧
      IsFreeSector sys.sign lab φ ∧ 0 < ∫ r, ‖φ r‖ ^ 2 ∧
      (∫ r, freeKinetic sys.mass φ r * conj (φ r)).re + ∫ r, freePot sys P r * ‖φ r‖ ^ 2 ≤
        (Einf + δ + ε) * ∫ r, ‖φ r‖ ^ 2) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E ∧ E + (zeroModeShift sys L θ).re ≤ Einf + δ ∧
      ∀ m : ℕ, PlaneWaveGridG.gLGridThreshold sys L (tv R θ) E ≤ m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          Eg + (zeroModeShift sys L θ).re ≤ Einf + δ +
            PlaneWaveGridG.gLGridErrorConstant sys L (tv R θ) E /
              ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  obtain ⟨E, hE, hgrid⟩ := PlaneWaveGridG.gLSectorGridError sys lab hlab hL hθ
  have hup := free_upper_of_trial sys hL hθ hR hR0 hρ hone P hP hpos hE htrial
  refine ⟨E, hE, hup, fun m hm => ?_⟩
  obtain ⟨Eg, hEg, herr⟩ := hgrid m hm
  refine ⟨Eg, hEg, ?_⟩
  have h := (abs_le.mp herr).2
  linarith

end FreeBoundary
