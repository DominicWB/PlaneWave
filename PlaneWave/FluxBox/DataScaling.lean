import PlaneWave.FluxBox.BoxLedger

/-!
# Flux route, stage 3, part 50: scaling of the data

The flux integrand is quadratic in the data: scaling the data `(u₀, v₀) ↦ (c u₀, c v₀)` (`evoSmul`)
scales `Ξ` by `|c|` (`evoSmul_Xi`), the trajectory by `c` (`traj_evoSmul`) and the integrand by `c²`.
With `c = 1/Ξ` the box bound of `PlaneWave.FluxBox.BoxLedger` becomes **`flux_box_scaled`**:
`|∫₀ᵗ F| ≤ Ξ² (t (C_B c_Tr² (gN)^{-1/2} + RateBox(2c_Tr, 1)) + EndBox(2c_Tr))`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Scale

variable {L : ℝ} {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}

/-- The data scaled by `c`. -/
noncomputable def evoSmul (D : EvoData L H) (c : ℂ) : EvoData L H where
  U := D.U
  U0 := D.U0
  graph := D.graph
  deriv := D.deriv
  cont := D.cont
  u₀ := c • D.u₀
  v₀ := c • D.v₀
  uv := by rw [map_smul, D.uv, map_smul]

lemma evoSmul_Xi (D : EvoData L H) (c : ℂ) : (evoSmul D c).Xi = ‖c‖ * D.Xi := by
  unfold EvoData.Xi
  simp only [evoSmul, map_smul, norm_smul]
  ring

lemma traj_evoSmul (D : EvoData L H) (c : ℂ) (s : ℝ) :
    traj H (evoSmul D c) s = c • traj H D s := by
  apply traj_eq
  show Sm eta L (c • traj H D s) = D.U s (Sm eta L (c • D.u₀))
  rw [map_smul, traj_S, map_smul, map_smul]

variable (sys : CoulombSystem eta ν) (p₀ : Fin eta)

omit [Fintype ν] in
lemma Gf_smul_real (c : ℝ) (u v : MolecularFourierH2 eta) :
    Gf sys L H p₀ ((c : ℂ) • u) ((c : ℂ) • v) = ((c ^ 2 : ℝ) : ℂ) * Gf sys L H p₀ u v := by
  unfold Gf
  simp only [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  push_cast
  ring

omit [Fintype ν] in
/-- The flux integrand of the scaled data. -/
lemma flux_integrand_evoSmul (D : EvoData L H) (n : ℕ) (c : ℝ) (s : ℝ) :
    (Gf sys L H p₀ (traj H (evoSmul D c) s) (traj H (evoSmul D c) s)).re -
        (Gf sys L H p₀ (molecularH2Truncate n (traj H (evoSmul D c) s))
          (molecularH2Truncate n (traj H (evoSmul D c) s))).re =
      c ^ 2 * ((Gf sys L H p₀ (traj H D s) (traj H D s)).re -
        (Gf sys L H p₀ (molecularH2Truncate n (traj H D s)) (molecularH2Truncate n (traj H D s))).re) := by
  rw [traj_evoSmul, molecularH2Truncate_smul, Gf_smul_real, Gf_smul_real, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
  ring

end Scale

section Scaled

variable {sys : CoulombSystem eta ν} {L : ℝ}

/-- **The flux on the box, scaled**:
`|∫₀ᵗ F| ≤ Ξ² (t (C_B c_Tr² (gN)^{-1/2} + RateBox(2c_Tr, 1)) + EndBox(2c_Tr))`. -/
theorem flux_box_scaled (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (p₀ : Fin eta) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {N n : ℕ} (hn : 64 ≤ n) (hnN : n ≤ N) (hl : 1 ≤ gF L * (cst sys * n)) {nd nd' : ℕ}
    (hnd : gF L * (2 * N) ≤ 2 ^ nd) (hnd' : gF L * ((n : ℝ) / 4) ≤ 2 ^ nd')
    (D : EvoData L H) {t : ℝ} (ht : 0 ≤ t) :
    |∫ s in (0 : ℝ)..t, ((Gf sys L H p₀ (traj H D s) (traj H D s)).re -
        (Gf sys L H p₀ (molecularH2Truncate n (traj H D s))
          (molecularH2Truncate n (traj H D s))).re)| ≤
      D.Xi ^ 2 * (t * (CB sys L Hunit * cTr sys L Hunit ^ 2 * (gF L * N) ^ (-(1 / 2 : ℝ)) +
          RateBox sys L Hunit N n nd nd' (2 * cTr sys L Hunit) 1) +
        EndBox sys L Hunit N n (2 * cTr sys L Hunit)) := by
  rcases (D.Xi_nonneg).eq_or_lt with h0 | hpos
  · -- vanishing data
    have hS : Sm eta L D.u₀ = 0 := by
      have h1 : ‖Sm eta L D.u₀‖ ≤ D.Xi := by
        unfold EvoData.Xi
        have := norm_nonneg (H D.u₀)
        have := norm_nonneg (H D.v₀)
        linarith
      rw [← h0] at h1
      exact norm_le_zero_iff.mp h1
    have htr : ∀ s, traj H D s = 0 := fun s => traj_eq H D s 0 (by
      rw [hS, map_zero, map_zero])
    have hF : ∀ s, (Gf sys L H p₀ (traj H D s) (traj H D s)).re -
        (Gf sys L H p₀ (molecularH2Truncate n (traj H D s))
          (molecularH2Truncate n (traj H D s))).re = 0 := by
      intro s
      rw [htr s, molecularH2Truncate_zero]
      simp [Gf]
    rw [intervalIntegral.integral_congr (fun s _ => hF s), intervalIntegral.integral_zero, abs_zero,
      ← h0]
    simp
  · set c : ℝ := 1 / D.Xi with hc
    have hc0 : 0 < c := by positivity
    set D' := evoSmul D (c : ℂ) with hD'
    have hXi' : D'.Xi = 1 := by
      rw [hD', evoSmul_Xi, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, hc]
      field_simp
    have hb := flux_box_total hL H hKernel p₀ Hunit hPeriodic hn hnN hl hnd hnd' D' ht
    rw [hXi', mul_one] at hb
    rw [intervalIntegral.integral_congr (fun s _ => flux_integrand_evoSmul sys p₀ D n c s),
      intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (sq_nonneg c)] at hb
    have hcX : c ^ 2 * D.Xi ^ 2 = 1 := by
      rw [hc]; field_simp
    calc |∫ s in (0 : ℝ)..t, ((Gf sys L H p₀ (traj H D s) (traj H D s)).re -
          (Gf sys L H p₀ (molecularH2Truncate n (traj H D s))
            (molecularH2Truncate n (traj H D s))).re)| =
        D.Xi ^ 2 * (c ^ 2 * |∫ s in (0 : ℝ)..t, ((Gf sys L H p₀ (traj H D s) (traj H D s)).re -
          (Gf sys L H p₀ (molecularH2Truncate n (traj H D s))
            (molecularH2Truncate n (traj H D s))).re)|) := by
          rw [← mul_assoc, mul_comm (D.Xi ^ 2), hcX, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (sq_nonneg _)

end Scaled

end FSFlux
