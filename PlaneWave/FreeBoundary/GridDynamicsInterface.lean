import PlaneWave.FreeBoundary.Propagator
import PlaneWave.FreeBoundary.UniformGridEnergy
import PlaneWave.Grid

/-!
# `thm:grid-dyn-sharp` for the `g_L` kernel: the continuum interface

The release proves `thm:grid-dyn-sharp` for the Coulomb kernel. Its proof uses the Coulomb
Hamiltonian only through a short list of facts about the completed operator `H : H² → ℓ²` and
through the Galerkin reference of the register. This file proves those facts for the completed
`g_L` operator of `PlaneWave.FreeBoundary.CompletedHamiltonian` (zero mode removed):

* `extract_H_eq_gL`: the Galerkin compression `P H u = H_N (P S u) + P W (1 - P) u`;
* `potential_symm_gL`: `⟪S u, W u'⟫ = ⟪W u, S u'⟫`;
* `potential_le_half_gL`, `kinetic_le_elliptic_gL`: the relative bound with constant `1/2` and
  the elliptic estimate `‖T u‖ ≤ 2‖H u‖ + 2b‖S u‖`;
* `potential_tail_le_gL`, `tail_kinetic_le_gL`, `tails_at_time_gL`: the tails of `W u`, of the
  kinetic energy and of the evolved state beyond `K`, with the `g_L` tail constant
  `gLtailM = Q (1 + V_θ) c_tail M₂` of `PlaneWave.FreeBoundary.UniformCubic` (`gLpot_tail_boundP`,
  the tail constant in physical units, bounded uniformly in `L ≥ 2π`: `gLtailM_le_U`,
  `PlaneWave.FreeBoundary.GridDynamicsUniform`);
* `regCoeff_H_eq_gL`, `regCoeff_H_eq_grid_gL`: on the register,
  `P H u = H_gal (P S u) + P W (1 - P) u = H_grid (P S u) + (P W (1 - P) u - Δ (P S u))`, with the
  Galerkin Hamiltonian and the difference `Δ = R - D` of the grid core with reference kernel `ĝ_L`
  (`PlaneWave.FreeBoundary.GridCoreGeneral`, `PlaneWave.FreeBoundary.GridEnergy`); the grid
  Hamiltonian is the release's;
* the regularity of grid trajectories with the `g_L` coupling (`norm_wM_gridFlow_le_gL`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Set PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid
  PlaneWaveGridDynamics
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

open PlaneWaveGridG (gLgamma gLgamma_pos gLref gLNucData regParticlesOfG)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The `g_L` tail constant -/

/-- The tail constant `Q (1 + V) c_tail M₂` of the `g_L` potential at the `H²` budget `M₂`. -/
noncomputable def gLtailM (sys : CoulombSystem eta ν) (L V Hunit M : ℝ) : ℝ :=
  sys.couplingWeight * ((1 + V) * FSNormal.ctailP (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi /
      L)) * M

lemma gLtailM_nonneg (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {V : ℝ} (hV : 0 ≤ V)
    (Hunit : ℝ) {M : ℝ} (hM : 0 ≤ M) : 0 ≤ gLtailM sys L V Hunit M := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  have h1 := FSNormal.ctailP_nonneg (C := coulombCellAmplitude L ^ 2) (Hunit := Hunit) hg
  have h2 := sys.couplingWeight_nonneg
  unfold gLtailM
  have : 0 ≤ 1 + V := by linarith
  positivity

lemma gLtailM_mono (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {V : ℝ} (hV : 0 ≤ V)
    (Hunit : ℝ) {M M' : ℝ} (hM : M ≤ M') : gLtailM sys L V Hunit M ≤ gLtailM sys L V Hunit M' := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  have h1 := FSNormal.ctailP_nonneg (C := coulombCellAmplitude L ^ 2) (Hunit := Hunit) hg
  have h2 := sys.couplingWeight_nonneg
  have : 0 ≤ 1 + V := by linarith
  unfold gLtailM
  exact mul_le_mul_of_nonneg_left hM (by positivity)

/-- `K^{-1/2} = ρ` when `ρ ≥ 0` and `ρ² K = 1`. -/
lemma rpow_neg_half_eq {K rho : ℝ} (hK : 0 < K) (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * K = 1) :
    K ^ (-(1 / 2 : ℝ)) = rho := by
  have hrho : 0 < rho := by
    rcases hRho.lt_or_eq with h | h
    · exact h
    · rw [← h] at hRhoScale
      norm_num at hRhoScale
  have hKe : K = (rho⁻¹) ^ 2 := by
    field_simp
    linarith
  rw [Real.rpow_neg hK.le, ← Real.sqrt_eq_rpow, hKe, Real.sqrt_sq (by positivity), inv_inv]

/-- The relative-bound constant `b = C √(4C² + 2)` of the `g_L` potential. -/
noncomputable def relB_gL (sys : CoulombSystem eta ν) (L V Hunit : ℝ) : ℝ :=
  gLmassConst sys L V Hunit * Real.sqrt (4 * gLmassConst sys L V Hunit ^ 2 + 2)

lemma relB_gL_nonneg (sys : CoulombSystem eta ν) (L V Hunit : ℝ)
    (hC : 0 ≤ gLmassConst sys L V Hunit) : 0 ≤ relB_gL sys L V Hunit :=
  mul_nonneg hC (Real.sqrt_nonneg _)

/-! ## The continuum interface -/

section Interface

variable (sys : CoulombSystem eta ν) (L : ℝ) {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 0 < L) {R : ℝ} (hθ : Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel in
/-- **Galerkin compression.** `P H u = H_N (P S u) + P W (1 - P) u` in the coordinates of the
cube `n`. -/
theorem extract_H_eq_gL (n : ℕ) (u : MolecularFourierH2 eta) :
    extractCLM n (H u) =
      gLham sys L θ n (extractCLM n (molecularH2StateMap eta (2 * Real.pi / L) u)) +
        extractCLM n (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
          (u - molecularH2Truncate n u)) := by
  have hsplit : H u = H (molecularH2Truncate n u) + H (u - molecularH2Truncate n u) := by
    rw [← map_add, add_sub_cancel]
  have hlow : extractCLM n (H (molecularH2Truncate n u)) =
      gLham sys L θ n (extractCLM n (molecularH2StateMap eta (2 * Real.pi / L) u)) := by
    rw [← extract_truncate n (H (molecularH2Truncate n u)),
      ← gLH2OutputLp_eq_compression sys L θ H hKernel u n, gLH2OutputLp,
      extract_embed, extract_stateMap]
  rw [hsplit, map_add, hlow, coulombFourierHamiltonianH2_decomposition sys (2 * Real.pi / L) H
    (u - molecularH2Truncate n u), map_add, extract_kinetic_tail, zero_add]

include hKernel hθ in
/-- **Symmetry of the `g_L` potential on `H²`.** `⟪S u, W u'⟫ = ⟪W u, S u'⟫`. -/
lemma potential_symm_gL (u u' : MolecularFourierH2 eta) :
    ⟪molecularH2StateMap eta (2 * Real.pi / L) u,
        coulombFourierPotentialH2 sys (2 * Real.pi / L) H u'⟫_ℂ =
      ⟪coulombFourierPotentialH2 sys (2 * Real.pi / L) H u,
        molecularH2StateMap eta (2 * Real.pi / L) u'⟫_ℂ := by
  change ⟪molecularH2StateMap eta (2 * Real.pi / L) u,
      H u' - coulombFourierKineticH2 sys (2 * Real.pi / L) u'⟫_ℂ =
    ⟪H u - coulombFourierKineticH2 sys (2 * Real.pi / L) u,
      molecularH2StateMap eta (2 * Real.pi / L) u'⟫_ℂ
  rw [inner_sub_right, inner_sub_left, gLH2_symm sys L θ H hKernel hθ, kinetic_symm]

include hKernel hL hθ hPeriodic in
/-- `‖W u‖ ≤ ½ ‖T u‖ + b ‖S u‖`. -/
theorem potential_le_half_gL (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    (u : MolecularFourierH2 eta) :
    ‖coulombFourierPotentialH2 sys (2 * Real.pi / L) H u‖ ≤
      (1 / 2) * ‖coulombFourierKineticH2 sys (2 * Real.pi / L) u‖ +
        relB_gL sys L (tv R θ) Hunit * ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ := by
  have h := gL_potential_sq_le_quarter sys hL hθ H hKernel Hunit hPeriodic u
  set C := gLmassConst sys L (tv R θ) Hunit
  set X := ‖coulombFourierKineticH2 sys (2 * Real.pi / L) u‖
  set Y := ‖molecularH2StateMap eta (2 * Real.pi / L) u‖
  have hb2 : relB_gL sys L (tv R θ) Hunit ^ 2 = C ^ 2 * (4 * C ^ 2 + 2) := by
    rw [relB_gL, mul_pow, Real.sq_sqrt (by positivity)]
  have hX := norm_nonneg (coulombFourierKineticH2 sys (2 * Real.pi / L) u)
  have hY := norm_nonneg (molecularH2StateMap eta (2 * Real.pi / L) u)
  have hb := relB_gL_nonneg sys L (tv R θ) Hunit hC
  have hK : gLrelConst sys L (tv R θ) Hunit = C ^ 2 * (4 * C ^ 2 + 2) := rfl
  rw [hK] at h
  have h2 : ‖coulombFourierPotentialH2 sys (2 * Real.pi / L) H u‖ ^ 2 ≤
      ((1 / 2) * X + relB_gL sys L (tv R θ) Hunit * Y) ^ 2 := by
    calc _ ≤ 1 / 4 * X ^ 2 + C ^ 2 * (4 * C ^ 2 + 2) * Y ^ 2 := h
      _ ≤ ((1 / 2) * X + relB_gL sys L (tv R θ) Hunit * Y) ^ 2 := by
          rw [← hb2]
          nlinarith [mul_nonneg hX (mul_nonneg hb hY)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

include hKernel hL hθ hPeriodic in
/-- **Elliptic estimate.** `‖T u‖ ≤ 2 ‖H u‖ + 2b ‖S u‖`. -/
theorem kinetic_le_elliptic_gL (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    (u : MolecularFourierH2 eta) :
    ‖coulombFourierKineticH2 sys (2 * Real.pi / L) u‖ ≤
      2 * ‖H u‖ + 2 * relB_gL sys L (tv R θ) Hunit *
        ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ := by
  have hW := potential_le_half_gL sys L H hKernel Hunit hL hθ hPeriodic hC u
  have hdec := coulombFourierHamiltonianH2_decomposition sys (2 * Real.pi / L) H u
  have hT : coulombFourierKineticH2 sys (2 * Real.pi / L) u =
      H u - coulombFourierPotentialH2 sys (2 * Real.pi / L) H u := by
    rw [hdec]
    abel
  have h1 : ‖coulombFourierKineticH2 sys (2 * Real.pi / L) u‖ ≤
      ‖H u‖ + ‖coulombFourierPotentialH2 sys (2 * Real.pi / L) H u‖ := by
    rw [hT]
    exact norm_sub_le _ _
  linarith

include hKernel hL hθ hPeriodic in
/-- **Potential tail of a general `H²` state** (`eq:lam-gen` for `g_L`). For every register `r`
and `K ≥ 1`, the part of `W u` beyond `K` in register `r` is at most `C_W(M₂) K^{-1/2}` when
the `H²` norm of `u` is at most `M₂`. -/
theorem potential_tail_le_gL (r : Fin eta) (K rho M2 : ℝ) (hK1 : 1 ≤ K)
    (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * K = 1) (hM2 : 0 ≤ M2)
    (u : MolecularFourierH2 eta) (hu : ‖u‖ ≤ M2) :
    ‖tailMask (2 * Real.pi / L) K r (coulombFourierPotentialH2 sys (2 * Real.pi / L) H u)‖ ≤
      gLtailM sys L (tv R θ) Hunit M2 * rho := by
  set g := 2 * Real.pi / L
  set W := coulombFourierPotentialH2 sys g H
  set M := tailMask g K r
  set C := gLtailM sys L (tv R θ) Hunit M2 * rho
  have hK0 : 0 < K := by linarith
  have hrpow := rpow_neg_half_eq hK0 hRho hRhoScale
  -- finite compressions, for cubes `b ≥ N`
  have hfin : ∀ N b, N ≤ b → ‖molecularH2Truncate b (M (W (molecularH2Truncate N u)))‖ ≤ C := by
    intro N b hNb
    rw [truncate_tailMask, gL_truncate_potential_eq sys L θ H hKernel N b hNb u, tailMask_embed,
      finiteFourierLpEmbed_norm_eq_fullCoeffVector]
    have hH2 : fullH2Sq (finitePlaneWaveKabs g b)
        (finiteFourierCoeffExtract b (molecularH2Coeff g (molecularH2Truncate N u))) ≤
        M2 ^ 2 := by
      rw [fullH2Sq_extract_eq_truncation_norm_sq]
      have h1 := molecularH2Truncate_norm_le b (molecularH2Truncate N u)
      have h2 := molecularH2Truncate_norm_le N u
      have h3 : ‖molecularH2Truncate b (molecularH2Truncate N u)‖ ≤ M2 := by linarith
      exact pow_le_pow_left₀ (norm_nonneg _) h3 2
    have h := gLpot_tail_boundP sys hL hθ Hunit hPeriodic r hK1 hM2
      (fullCoeffVector (finiteFourierCoeffExtract b (molecularH2Coeff g (molecularH2Truncate N u))))
      hH2
    rw [hrpow] at h
    exact le_trans (le_of_eq rfl) h
  -- remove the output truncation
  have hN : ∀ N, ‖M (W (molecularH2Truncate N u))‖ ≤ C := by
    intro N
    have ht := molecularH2Truncate_tendsto (M (W (molecularH2Truncate N u)))
    exact le_of_tendsto ht.norm (eventually_atTop.mpr ⟨N, fun b hb => hfin N b hb⟩)
  -- remove the input truncation
  have hL1 : Tendsto (fun N => ‖M (W (molecularH2Truncate N u))‖) atTop (𝓝 ‖M (W u)‖) :=
    ((M.continuous.comp W.continuous).tendsto u |>.comp (molecularH2Truncate_tendsto u)).norm
  exact le_of_tendsto' hL1 hN

include hKernel hL hθ hPeriodic in
/-- **Kinetic tail** (`eq:dyn-wtail` for `g_L`, kinetic part). If `H u = S v`, then
`‖1_{a,>K} T u‖ ≤ (2 m̄/K²) ‖T v‖ + C_W(M₂) K^{-1/2}` for `‖u‖ ≤ M₂`. -/
theorem tail_kinetic_le_gL (a : Fin eta) (K rho M2 : ℝ) (hK1 : 1 ≤ K)
    (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * K = 1) (hM2 : 0 ≤ M2)
    (u v : MolecularFourierH2 eta) (hu : ‖u‖ ≤ M2)
    (huv : H u = molecularH2StateMap eta (2 * Real.pi / L) v) :
    ‖tailMask (2 * Real.pi / L) K a (coulombFourierKineticH2 sys (2 * Real.pi / L) u)‖ ≤
      (2 * sys.maxMass / K ^ 2) * ‖coulombFourierKineticH2 sys (2 * Real.pi / L) v‖ +
        gLtailM sys L (tv R θ) Hunit M2 * rho := by
  set g := 2 * Real.pi / L
  have hK : 0 < K := by linarith
  have hdec : coulombFourierKineticH2 sys g u = H u - coulombFourierPotentialH2 sys g H u := by
    rw [coulombFourierHamiltonianH2_decomposition sys g H u]
    abel
  have hW := potential_tail_le_gL sys L H hKernel Hunit hL hθ hPeriodic a K rho M2 hK1 hRho
    hRhoScale hM2 u hu
  have hHv : ‖tailMask g K a (H u)‖ ≤ (2 * sys.maxMass / K ^ 2) *
      ‖coulombFourierKineticH2 sys g v‖ := by
    rw [huv]
    refine (tail_stateMap_le sys L hK a v).trans ?_
    have hM := sys.one_le_maxMass
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := (tailMask g K a).le_opNorm (coulombFourierKineticH2 sys g v)
    have hnorm : ‖tailMask g K a‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun x => l2_norm_le_of_le _ x zero_le_one (fun p => by
        rw [tailMask_apply]
        split_ifs <;> simp))
    nlinarith [norm_nonneg (coulombFourierKineticH2 sys g v), norm_nonneg (tailMask g K a)]
  rw [hdec, map_sub]
  exact (norm_sub_le _ _).trans (add_le_add hHv hW)

include hKernel hL hθ hPeriodic in
/-- The register tails of the evolved state and of its kinetic energy, at one time:
`τ_a ≤ B` and `t_a ≤ (2m̄/K²) B` with `B = (2m̄/K²) Ξ₁ + C_W(M₂) K^{-1/2}`. -/
theorem tails_at_time_gL (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (a : Fin eta) (K rho : ℝ) (hK1 : 1 ≤ K)
    (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * K = 1)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (t : ℝ) (u : MolecularFourierH2 eta)
    (hu1 : molecularH2StateMap eta (2 * Real.pi / L) u =
      U t (molecularH2StateMap eta (2 * Real.pi / L) u₀))
    (hu2 : H u = U t (H u₀)) :
    let B := (2 * sys.maxMass / K ^ 2) * (2 * ‖H v₀‖ + 2 * relB_gL sys L (tv R θ) Hunit *
            ‖molecularH2StateMap eta (2 * Real.pi / L) v₀‖) +
          gLtailM sys L (tv R θ) Hunit
            (sys.maxMass * (‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ +
              2 * (2 * ‖H u₀‖ + 2 * relB_gL sys L (tv R θ) Hunit *
                ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖))) * rho
    ‖tailMask (2 * Real.pi / L) K a (coulombFourierKineticH2 sys (2 * Real.pi / L) u)‖ ≤ B ∧
      ‖tailMask (2 * Real.pi / L) K a (molecularH2StateMap eta (2 * Real.pi / L) u)‖ ≤
        (2 * sys.maxMass / K ^ 2) * B := by
  intro B
  set g := 2 * Real.pi / L
  set S := molecularH2StateMap eta g
  set T := coulombFourierKineticH2 sys g
  set b := relB_gL sys L (tv R θ) Hunit
  have hM := sys.one_le_maxMass
  have hK : 0 < K := by linarith
  have hb := relB_gL_nonneg sys L (tv R θ) Hunit hC
  obtain ⟨v, hv1, hv2⟩ := hgraph t v₀
  have huv' : H u = S v := by rw [hu2, huv, hv1]
  have hTu : ‖T u‖ ≤ 2 * ‖H u₀‖ + 2 * b * ‖S u₀‖ := by
    have h := kinetic_le_elliptic_gL sys L H hKernel Hunit hL hθ hPeriodic hC u
    rwa [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
  have hTv : ‖T v‖ ≤ 2 * ‖H v₀‖ + 2 * b * ‖S v₀‖ := by
    have h := kinetic_le_elliptic_gL sys L H hKernel Hunit hL hθ hPeriodic hC v
    rwa [hv1, hv2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
  have hu_le : ‖u‖ ≤ sys.maxMass * (‖S u₀‖ + 2 * (2 * ‖H u₀‖ + 2 * b * ‖S u₀‖)) := by
    have h := h2norm_le sys L u
    rw [hu1, LinearIsometryEquiv.norm_map] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    linarith
  set M2 := sys.maxMass * (‖S u₀‖ + 2 * (2 * ‖H u₀‖ + 2 * b * ‖S u₀‖))
  have hM2 : 0 ≤ M2 := (norm_nonneg u).trans hu_le
  have hkin := tail_kinetic_le_gL sys L H hKernel Hunit hL hθ hPeriodic a K rho M2 hK1 hRho
    hRhoScale hM2 u v hu_le huv'
  have hkinB : ‖tailMask g K a (T u)‖ ≤ B := by
    refine hkin.trans ?_
    simp only [B]
    gcongr
  exact ⟨hkinB, (tail_stateMap_le sys L hK a u).trans
    (mul_le_mul_of_nonneg_left hkinB (by positivity))⟩

end Interface

/-! ## The register: Galerkin compression with the `ĝ_L` reference -/

section Register

variable (sys : CoulombSystem eta ν) (L : ℝ) {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
  (hL : 0 < L) {R : ℝ} (hθ : Profile R θ)

/-- The release's grid Hamiltonian of a Coulomb system is the grid Hamiltonian of the grid core
with any nuclear data of the same charges and phases, in particular with the `ĝ_L` reference. -/
lemma Hgrid_eq_G (m : ℕ) (κ : Lat3 → ℝ) (g : ℝ) (x : EuclideanSpace ℂ (RCfg eta m)) :
    Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ g x =
      PlaneWaveGridG.Hgrid eta m (regParticlesOfG sys)
        (gLNucData sys hL hθ) κ g x := rfl

lemma regUnitary_eq_G (M : ℕ) (x : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode M))) :
    regUnitary eta M x = PlaneWaveGridG.regUnitary eta M x := rfl

include hKernel in
/-- **Galerkin compression on the register** (`g_L`). `P H u = H_gal (P S u) + P W (1 - P) u`,
with the Galerkin Hamiltonian of the reference `ĝ_L`. -/
theorem regCoeff_H_eq_gL (m : ℕ) (u : MolecularFourierH2 eta) :
    regCoeff m (H u) =
      PlaneWaveGridG.Hgal eta m (regParticlesOfG sys)
          (gLNucData sys hL hθ) (gLgamma L (tv R θ))
          (2 * Real.pi / L) (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u)) +
        regCoeff m (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
          (u - molecularH2Truncate (2 * m) u)) := by
  rw [regCoeff_eq, regCoeff_eq, regCoeff_eq, extract_H_eq_gL sys L H hKernel (2 * m) u, map_add]
  simp only [regUnitary_eq_G]
  rw [PlaneWaveGridG.Hgal_regUnitary_gL sys m hL hθ]

include hKernel hθ in
/-- **The Galerkin source against a register vector** (`g_L`). With `l` the `H²` lift of `φ`,
`⟪P W (1 - P) u, φ⟫ = ⟪(1 - P) S u, (1 - P) W l⟫`. -/
theorem inner_galSource_gL (m : ℕ) (u : MolecularFourierH2 eta)
    (φ : EuclideanSpace ℂ (RCfg eta m)) :
    ⟪regCoeff m (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
        (u - molecularH2Truncate (2 * m) u)), φ⟫_ℂ =
      ⟪molecularH2StateMap eta (2 * Real.pi / L) u -
          molecularH2Truncate (2 * m) (molecularH2StateMap eta (2 * Real.pi / L) u),
        coulombFourierPotentialH2 sys (2 * Real.pi / L) H
            (cubeLift (2 * Real.pi / L) (2 * m) ((regUnitary eta (2 * m)).symm φ)) -
          molecularH2Truncate (2 * m) (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
            (cubeLift (2 * Real.pi / L) (2 * m) ((regUnitary eta (2 * m)).symm φ)))⟫_ℂ := by
  set g := 2 * Real.pi / L
  set S := molecularH2StateMap eta g
  set W := coulombFourierPotentialH2 sys g H
  set ψ := (regUnitary eta (2 * m)).symm φ
  set x := u - molecularH2Truncate (2 * m) u
  have hSx : S x = S u - molecularH2Truncate (2 * m) (S u) := by
    show S (u - molecularH2Truncate (2 * m) u) = _
    rw [map_sub, stateMap_truncate]
  have h1 : ⟪regCoeff m (W x), φ⟫_ℂ = ⟪extractCLM (2 * m) (W x), ψ⟫_ℂ := by
    rw [regCoeff_eq]
    conv_lhs => rw [← (regUnitary eta (2 * m)).apply_symm_apply φ]
    exact LinearIsometryEquiv.inner_map_map _ _ _
  rw [h1, inner_extract_left, ← stateMap_cubeLift g (2 * m) ψ,
    ← potential_symm_gL sys L H hKernel hθ, hSx, inner_sub_truncate_left]

include hKernel hθ in
lemma norm_inner_galSource_le_gL (m : ℕ) (u : MolecularFourierH2 eta)
    (φ : EuclideanSpace ℂ (RCfg eta m)) :
    ‖⟪regCoeff m (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
        (u - molecularH2Truncate (2 * m) u)), φ⟫_ℂ‖ ≤
      ‖molecularH2StateMap eta (2 * Real.pi / L) u -
          molecularH2Truncate (2 * m) (molecularH2StateMap eta (2 * Real.pi / L) u)‖ *
        ‖coulombFourierPotentialH2 sys (2 * Real.pi / L) H
            (cubeLift (2 * Real.pi / L) (2 * m) ((regUnitary eta (2 * m)).symm φ)) -
          molecularH2Truncate (2 * m) (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
            (cubeLift (2 * Real.pi / L) (2 * m) ((regUnitary eta (2 * m)).symm φ)))‖ := by
  rw [inner_galSource_gL sys L H hKernel hθ m u φ]
  exact norm_inner_le_norm _ _

/-- The difference operator `Δ = R - D` of the grid core with the reference `ĝ_L`. -/
noncomputable abbrev DeltaGL (m : ℕ) (κ : Lat3 → ℝ) :
    EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  PlaneWaveGridG.Delta eta m (regParticlesOfG sys)
    (gLNucData sys hL hθ) (gLgamma L (tv R θ)) κ

include hKernel in
/-- `P H u = H_grid (P S u) + (P W (1 - P) u - Δ (P S u))` on the register (`Δ = R - D` with the
reference `ĝ_L`). -/
theorem regCoeff_H_eq_grid_gL (m : ℕ) (κ : Lat3 → ℝ) (u : MolecularFourierH2 eta) :
    regCoeff m (H u) =
      Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L)
          (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u)) +
        (regCoeff m (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
            (u - molecularH2Truncate (2 * m) u)) -
          DeltaGL sys L hL hθ m κ (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u))) := by
  rw [regCoeff_H_eq_gL sys L H hKernel hL hθ m u, Hgrid_eq_G sys L hL hθ,
    PlaneWaveGridG.Hgrid_eq (gamma := gLgamma L (tv R θ))]
  abel

end Register

/-! ## Regularity of grid trajectories with the `g_L` coupling -/

section Flow

/-- The coupling `m̄ Σ_t |c_t| γ_t` of the register potential with `γ = (1 + V)/(πL)`. -/
noncomputable def gLCoupling (sys : CoulombSystem eta ν) (L V : ℝ) : ℝ :=
  sys.maxMass * Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (gLgamma L V)

lemma gLCoupling_nonneg (sys : CoulombSystem eta ν) {L V : ℝ} (hL : 0 < L) (hV : 0 ≤ V) :
    0 ≤ gLCoupling sys L V :=
  mul_nonneg (by linarith [sys.one_le_maxMass])
    (Zc_nonneg (gLgamma_pos hL hV).le)

/-- The constant `(4/3)(1 + 104 Z J₀/g²)` of the regularity of grid trajectories, with the `g_L`
coupling `Z = gLCoupling`. -/
noncomputable def gridFlowConst_gL (sys : CoulombSystem eta ν) (L V : ℝ) : ℝ :=
  4 / 3 * (1 + 104 * gLCoupling sys L V *
    (J0g (gLCoupling sys L V) (2 * Real.pi / L) : ℝ) / (2 * Real.pi / L) ^ 2)

lemma gridFlowConst_gL_nonneg (sys : CoulombSystem eta ν) {L V : ℝ} (hL : 0 < L) (hV : 0 ≤ V) :
    0 ≤ gridFlowConst_gL sys L V := by
  unfold gridFlowConst_gL
  have := gLCoupling_nonneg sys hL hV
  positivity

/-- **Regularity of grid trajectories** (`lem:grid-traj`, `g_L`). -/
theorem norm_wM_gridFlow_le_gL (sys : CoulombSystem eta ν) {L V : ℝ} (hL : 0 < L) (hV : 0 ≤ V)
    {m : ℕ} {κ : Lat3 → ℝ} (hκb : ∀ x, |κ x| ≤ gLgamma L V * coul x)
    (U : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hcomm : ∀ x, U (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (U x))
    (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM (regParticlesOf sys)) (U v)‖ ≤
      5 / 3 * ‖wMul (wM (regParticlesOf sys)) v‖ + gridFlowConst_gL sys L V * ‖v‖ := by
  have hγ : 0 ≤ gLgamma L V := (gLgamma_pos hL hV).le
  have hg : 0 < 2 * Real.pi / L := by positivity
  exact (gridRegHam (eta := eta) (m := m) (P := regParticlesOf sys)
    (D := (posNucleiOf sys.nuclei).toNucData) hγ hκb hg).flow_le_weight U hcomm v

/-- The backward grid flow of `O_g v` (`g_L`). -/
theorem norm_wM_gridFlow_gridObs_le_gL (sys : CoulombSystem eta ν) {L V : ℝ} (hL : 0 < L)
    (hV : 0 ≤ V) {m : ℕ} {κ : Lat3 → ℝ} (hκb : ∀ x, |κ x| ≤ gLgamma L V * coul x)
    (U : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hcomm : ∀ x, U (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (U x))
    (a : Fin eta) {χ : Lat3 → ℂ} (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (v : EuclideanSpace ℂ (RCfg eta m)) {X S : ℝ}
    (hX : ‖wMul (wM (regParticlesOf sys)) v‖ ≤ X) (hS : ‖v‖ ≤ S) :
    ‖wMul (wM (regParticlesOf sys)) (U (gridObs a χ v))‖ ≤
      5 / 3 * ((2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * X + 14 * momTwo χ * S) +
        gridFlowConst_gL sys L V * ((∑' ν, ‖χ ν‖) * S) := by
  have hC : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hD : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hJ := gridFlowConst_gL_nonneg sys hL hV
  have hM := sys.one_le_maxMass
  have h1 := norm_wM_gridFlow_le_gL sys hL hV hκb U hcomm (gridObs a χ v)
  have h2 : ‖wMul (wM (regParticlesOf sys)) (gridObs a χ v)‖ ≤
      (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * ‖wMul (wM (regParticlesOf sys)) v‖ +
        14 * momTwo χ * ‖v‖ :=
    norm_wM_gridObs_le (regParticlesOf sys) a hχ1 hχ2 v
  have h3 : ‖gridObs a χ v‖ ≤ (∑' ν, ‖χ ν‖) * ‖v‖ :=
    ((gridObs a χ).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_gridObs_le a hχ1) (norm_nonneg v))
  have hc1 : 0 ≤ (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) := mul_nonneg (by linarith) hC
  have h2' : ‖wMul (wM (regParticlesOf sys)) (gridObs a χ v)‖ ≤
      (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * X + 14 * momTwo χ * S :=
    h2.trans (add_le_add (mul_le_mul_of_nonneg_left hX hc1)
      (mul_le_mul_of_nonneg_left hS (by positivity)))
  have h3' : ‖gridObs a χ v‖ ≤ (∑' ν, ‖χ ν‖) * S := h3.trans (mul_le_mul_of_nonneg_left hS hC)
  exact h1.trans (add_le_add (mul_le_mul_of_nonneg_left h2' (by norm_num))
    (mul_le_mul_of_nonneg_left h3' hJ))

end Flow

end FreeBoundary
