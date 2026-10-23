import PlaneWave.KineticLog.GalerkinEndpoint
import PlaneWave.FluxSourceSpin

/-!
# Logarithmic kinetic bound, part 8: the Galerkin endpoints with finite internal spin

A spin-inclusive datum is a family `Ds : S → EvoData L H` over a finite set `S` of spin
configurations (`FSSpin`, the release's spin interface): the Hamiltonian, the cube projector and
the kinetic observable act as the identity on spin, and the data norm is
`Ξ_S = ‖Ψ₀‖ + ‖H Ψ₀‖ + ‖H² Ψ₀‖` with the norms of `ℓ²(S; ℓ²)` (`FSSpin.XiS`).

* `kinetic_retained_galerkin_spin`: `‖(P ⊗ 1) Ψ(t) - Ψ_N(t)‖ ≤ C Ξ_S [1 + t + log(2+K)]/K³`;
* `thm_kinetic_log_galerkin_spin` (`thm:kinetic-log`, Galerkin case with spin);
* `cor_stopping_log_galerkin_spin` (`cor:stopping-log`, Galerkin case with spin).

The constants are those of the scalar theorems: the componentwise bounds are summed with
Minkowski's inequality `Σ_σ Ξ_σ² ≤ Ξ_S²` (`FSSpin.sum_Xi_sq_le`), so there is no factor
depending on the number of spin configurations.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FSNormal FSGalerkin

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν] {S : Type} [Fintype S]

section Spin

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hL hKernel in
/-- **`eq:kinetic-retained-galerkin` with spin**: the `ℓ²(S; ℓ²)` norm of the retained
difference is at most `C Ξ_S [1 + t + log(2 + K)]/K³`. -/
theorem kinetic_retained_galerkin_spin (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (Ds : S → EvoData L H) (t : ℝ), 0 ≤ t →
      Real.sqrt (∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - FSSpin.galS sys n Ds t σ‖ ^ 2)
        ≤ C * FSSpin.XiS Ds * ((1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3) := by
  obtain ⟨C, hC, N₀, h⟩ := kinetic_retained_galerkin sys hL H hKernel Hunit hPeriodic
  refine ⟨C, hC, N₀, fun n hn Ds t ht => ?_⟩
  set r := (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 with hr
  have hr0 : 0 ≤ r := by
    have hK : 0 ≤ Kc L n := by
      have := gF_pos hL
      change 0 ≤ gF L * n
      positivity
    have hlog : 0 ≤ Real.log (2 + Kc L n) := Real.log_nonneg (by linarith)
    rw [hr]
    positivity
  have hσ : ∀ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - FSSpin.galS sys n Ds t σ‖ ≤
      C * r * (Ds σ).Xi := fun σ => by
    have := h n hn (Ds σ) t ht
    calc _ ≤ C * (Ds σ).Xi * (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := this
      _ = C * r * (Ds σ).Xi := by rw [hr]; ring
  have hsq : ∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - FSSpin.galS sys n Ds t σ‖ ^ 2 ≤
      (C * r * FSSpin.XiS Ds) ^ 2 := by
    calc ∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - FSSpin.galS sys n Ds t σ‖ ^ 2
        ≤ ∑ σ, (C * r) ^ 2 * (Ds σ).Xi ^ 2 := Finset.sum_le_sum fun σ _ => by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hσ σ) 2
      _ = (C * r) ^ 2 * ∑ σ, (Ds σ).Xi ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (C * r) ^ 2 * FSSpin.XiS Ds ^ 2 :=
          mul_le_mul_of_nonneg_left (FSSpin.sum_Xi_sq_le Ds) (sq_nonneg _)
      _ = (C * r * FSSpin.XiS Ds) ^ 2 := by ring
  calc Real.sqrt (∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) -
        FSSpin.galS sys n Ds t σ‖ ^ 2) ≤ Real.sqrt ((C * r * FSSpin.XiS Ds) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = C * r * FSSpin.XiS Ds := Real.sqrt_sq (by have := FSSpin.XiS_nonneg Ds; positivity)
    _ = C * FSSpin.XiS Ds * r := by ring

include hL hKernel in
/-- **`thm:kinetic-log`, Galerkin case with spin**: for every spin-inclusive datum, every cutoff
`n ≥ N₀` and every `t ≥ 0`,
`|⟨Ψ(t), (T_{p₀} ⊗ 1) Ψ(t)⟩ - ⟨Ψ_N(t), (T_{p₀} ⊗ 1) Ψ_N(t)⟩| ≤ C Ξ_S² [1 + t + log(2+K)]/K³`. -/
theorem thm_kinetic_log_galerkin_spin (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (p₀ : Fin eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (Ds : S → EvoData L H) (t : ℝ), 0 ≤ t →
      |FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds t) -
          FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds t)| ≤
        C * FSSpin.XiS Ds ^ 2 * ((1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3) := by
  obtain ⟨C, hC, N₀, h⟩ := thm_kinetic_log_galerkin sys hL H hKernel Hunit hPeriodic p₀
  refine ⟨C, hC, max N₀ (nGal sys L Hunit), fun n hn Ds t ht => ?_⟩
  obtain ⟨hK1, -, -⟩ := nGal_scales hL (le_trans (le_max_right _ _) hn)
  have hK0 : 0 < Kc L n := by change 0 < gF L * n; linarith
  have hr : 0 ≤ (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Kc L n by linarith)
    positivity
  rw [FSSpin.expectS_sub]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h n (le_trans (le_max_left _ _) hn) (Ds σ) t ht
  calc _ ≤ C * (Ds σ).Xi ^ 2 * (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3) := by ring

include hL hKernel in
/-- **`cor:stopping-log`, Galerkin case with spin**: for every window `[0, τ]`, `τ > 0`, and
reference speed `v_p > 0`, the spin-inclusive signed secants differ by at most
`(C Ξ_S²/v_p) [1 + (1 + log(2 + K))/τ]/K³`. -/
theorem cor_stopping_log_galerkin_spin (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (p₀ : Fin eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (Ds : S → EvoData L H) {vp τ : ℝ}, 0 < vp →
      0 < τ →
        |(FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds τ) -
              FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds 0)) / (vp * τ) -
            (FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds τ) -
              FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds 0)) / (vp * τ)| ≤
          C * FSSpin.XiS Ds ^ 2 * ((1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 / vp) := by
  obtain ⟨C, hC, N₀, h⟩ := cor_stopping_log_galerkin sys hL H hKernel Hunit hPeriodic p₀
  refine ⟨C, hC, max N₀ (nGal sys L Hunit), fun n hn Ds vp τ hvp hτ => ?_⟩
  obtain ⟨hK1, -, -⟩ := nGal_scales hL (le_trans (le_max_right _ _) hn)
  have hK0 : 0 < Kc L n := by change 0 < gF L * n; linarith
  have hr : 0 ≤ (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 / vp := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Kc L n by linarith)
    positivity
  have e : (FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds τ) -
        FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds 0)) / (vp * τ) -
      (FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds τ) -
        FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds 0)) / (vp * τ) =
      ∑ σ, (((regKin sys (gF L) p₀).expect (FSSpin.exactS Ds τ σ) -
          (regKin sys (gF L) p₀).expect (FSSpin.exactS Ds 0 σ)) / (vp * τ) -
        ((regKin sys (gF L) p₀).expect (FSSpin.galS sys n Ds τ σ) -
          (regKin sys (gF L) p₀).expect (FSSpin.galS sys n Ds 0 σ)) / (vp * τ)) := by
    simp only [FSSpin.expectS, ← Finset.sum_sub_distrib, Finset.sum_div]
  rw [e]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h n (le_trans (le_max_left _ _) hn) (Ds σ) hvp hτ
  calc _ ≤ C * (Ds σ).Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 / vp) := by ring

end Spin

end KineticLog
