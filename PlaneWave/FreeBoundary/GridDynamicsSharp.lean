import PlaneWave.FreeBoundary.GridDynamicsInterface

/-!
# `thm:grid-dyn-sharp` for the `g_L` kernel: the sharp observable bound

The release's proof of the sharp grid-dynamics bound (`PlaneWave.Grid`, sections `DevGS2`–`DevGS5`),
for the completed `g_L` operator: the statements and proofs are the release's, with the continuum
interface of `PlaneWave.FreeBoundary.GridDynamicsInterface` (relative bound `relB_gL`, tail constant
`gLtailM`), the Galerkin reference `ĝ_L` of the grid core
(`PlaneWave.FreeBoundary.GridCoreGeneral`), the coupling `gLCoupling` (`γ = (1 + V_θ)/(πL)`) and the
kernel class `PlaneWaveGridG.IsGridKernel γ ρ_L m` (`γ ρ_L = ĝ_L` on `|ν| ≤ m`).

* `second_moment_regCoeff_le_gL`: the second kinetic moment of the projected trajectory;
* `norm_wM_sq_gridFlow_le_gL`, `shell_gridFlow_gridObs_le_gL`: second moments and shells of the
  grid flows;
* `grid_duality_shell_gL`: duality on the grid, with the shells of the backward flow;
* `grid_observable_error_sharp_gL`, **`grid_observable_rate_sharp_gL`**: `thm:grid-dyn-sharp` for
  `g_L` on the Fourier side: `A₁ K⁻⁵ + A₂ t K⁻³ + A₃ K^{-5/2} τ_χ(K) + ‖ψ₀‖² τ_χ^∞(m)`, with
  `(A₁, A₂, A₃) = gridConstsSharp_gL` independent of `K` and `t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics

open PlaneWaveGridG (gLgamma gLgamma_pos gLref gLNucData regParticlesOfG)

namespace FreeBoundary


section Continuum

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  {θ : ℝ → ℝ} (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 0 < L) {R : ℝ} (hθ : Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hθ hPeriodic in
/-- **The second kinetic moment of the projected trajectory** (`lem:grid-data2`, `eq:data2`): for
`ψ(t) = S u`, `‖W² P ψ(t)‖ ≤ ‖ψ₀‖ + (4/g²) Ξ₀ + (2/g²) η √Q (4m+1)^{3/2}` uniformly in `t`, where
`Q = k₀⁴ Ξ₀² + 120 m̄² Ξ₁²/g⁴ + 30 C_tail(M₀)²/g` (`k₀ ≥ 2` with `g k₀ ≥ 1` the first threshold of
the layer cake at which the bootstrapped tails are used). -/
theorem second_moment_regCoeff_le_gL (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (m : ℕ)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (t : ℝ) (u : MolecularFourierH2 eta)
    (hu1 : molecularH2StateMap eta (2 * Real.pi / L) u =
      U t (molecularH2StateMap eta (2 * Real.pi / L) u₀))
    (hu2 : H u = U t (H u₀)) (k₀ : ℕ) (hk₀ : 2 ≤ k₀) (hk₀g : 1 ≤ (2 * Real.pi / L) * k₀) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB_gL sys L (tv R θ) Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let C₀ : ℝ := gLtailM sys L (tv R θ) Hunit M₀
    let Q : ℝ := (k₀ : ℝ) ^ 4 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 / g ^ 4 + 30 * C₀ ^ 2 / g
    ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys))
        (regCoeff m (molecularH2StateMap eta g u)))‖ ≤
      S0 + 4 / g ^ 2 * Ξ₀ +
        2 / g ^ 2 * (eta * (Real.sqrt Q * Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3)) := by
  intro g b S0 Ξ₀ Ξ₁ M₀ C₀ Q
  have hb : 0 ≤ b := relB_gL_nonneg sys L (tv R θ) Hunit hC
  have hg : 0 < g := by positivity
  have hM₀ : 0 ≤ M₀ := by
    have hM := sys.one_le_maxMass
    have hS0 : 0 ≤ S0 := norm_nonneg _
    have hΞ₀ : 0 ≤ Ξ₀ := by positivity
    positivity
  have hSu : ‖molecularH2StateMap eta g u‖ = S0 := by
    show ‖molecularH2StateMap eta g u‖ = ‖molecularH2StateMap eta g u₀‖
    rw [hu1, LinearIsometryEquiv.norm_map]
  have hTu : ‖coulombFourierKineticH2 sys g u‖ ≤ Ξ₀ := by
    have h := kinetic_le_elliptic_gL sys L H hKernel Hunit hL hθ hPeriodic hC u
    rw [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
    exact h
  have hhigh : ∀ r : Fin eta, ∀ k : ℕ, k₀ ≤ k →
      ‖maskOp (Shell r k) (regCoeff m (coulombFourierKineticH2 sys g u))‖ ≤
        (2 * sys.maxMass / (g * k) ^ 2) * Ξ₁ + C₀ * Real.sqrt (1 / (g * k)) := by
    intro r k hkk
    have hgk1 : 1 ≤ g * k :=
      hk₀g.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hkk) hg.le)
    have hgkpos : 0 < g * k := by linarith
    have hρ : Real.sqrt (1 / (g * k)) ^ 2 * (g * k) = 1 := by
      rw [Real.sq_sqrt (div_nonneg zero_le_one hgkpos.le), div_mul_cancel₀ 1 hgkpos.ne']
    exact (norm_shell_regCoeff_le hg r k _).trans
      (tails_at_time_gL sys L H hKernel Hunit hL hθ hPeriodic hC U hgraph r (g * k)
        (Real.sqrt (1 / (g * k))) hgk1 (Real.sqrt_nonneg _) hρ u₀ v₀ huv t u hu1 hu2).1
  have hlow : ∀ r : Fin eta, ∀ k : ℕ,
      ‖maskOp (Shell r k) (regCoeff m (coulombFourierKineticH2 sys g u))‖ ≤ Ξ₀ := fun r k =>
    (norm_shell_regCoeff_le hg r k _).trans ((norm_tailMask_apply_le g (g * k) r _).trans hTu)
  exact second_moment_assemble (regParticlesOf sys) _ _ hg
    (norm_wM_sq_regCoeff_le_pt sys hg m u) ((norm_regCoeff_le _).trans hSu.le)
    ((norm_regCoeff_le _).trans hTu)
    (fun r => layer_bound r _ hg k₀ (by omega) (hlow r) (hhigh r))

end Continuum

section Flow

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **Second moment of a grid trajectory** (`lem:grid-data2` for `ψ_g(t)`, and the backward flows
in the proof of `thm:grid-dyn-sharp`): for a unitary `V` that commutes with the grid Hamiltonian,
`X(V w) ≤ flow2(X(w), ‖W w‖, ‖w‖)`; the bound does not depend on `V`, so it is uniform in time. -/
theorem norm_wM_sq_gridFlow_le_gL (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {R : ℝ} {θ : ℝ →
    ℝ} (hθ : Profile R θ) {m : ℕ}
    {κ : Lat3 → ℝ} (hκb : ∀ x, |κ x| ≤ gLgamma L (tv R θ) * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0)
    (V : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hcomm : ∀ x, V (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (V x))
    (w : EuclideanSpace ℂ (RCfg eta m)) {X Y S : ℝ}
    (hX : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) w)‖ ≤ X)
    (hY : ‖wMul (wM (regParticlesOf sys)) w‖ ≤ Y) (hS : ‖w‖ ≤ S) :
    ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) (V w))‖ ≤
      flow2 (2 * Real.pi / L) (gridFlowConst_gL sys L (tv R θ))
        (26 * gLCoupling sys L (tv R θ) * (J0g (gLCoupling sys L (tv R θ)) (2 * Real.pi / L) : ℝ))
        (secondConst (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
          (gLgamma L (tv R θ)) (2 * Real.pi / L) m) X Y S := by
  have hγ : 0 ≤ gLgamma L (tv R θ) := (gLgamma_pos hL hθ.tv_nonneg).le
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hsc : 0 ≤ secondConst (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (gLgamma L (tv R θ)) (2 * Real.pi / L) m := secondConst_nonneg _ _ hγ
  have hcJ := gridFlowConst_gL_nonneg sys hL hθ.tv_nonneg
  have hcH : 0 ≤ 26 * gLCoupling sys L (tv R θ) *
      (J0g (gLCoupling sys L (tv R θ)) (2 * Real.pi / L) : ℝ) := by
    have := gLCoupling_nonneg sys hL hθ.tv_nonneg
    positivity
  have h1 := second_elliptic (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData hγ hκb hsupp
    hg (V w)
  have h2 : ‖wMul (wM (regParticlesOf sys)) (V w)‖ ≤ 5 / 3 * Y + gridFlowConst_gL sys L (tv R θ) * S
      := by
    have h := norm_wM_gridFlow_le_gL sys hL hθ.tv_nonneg hκb V hcomm w
    have h3 := mul_le_mul_of_nonneg_left hY (by norm_num : (0 : ℝ) ≤ 5 / 3)
    have h4 := mul_le_mul_of_nonneg_left hS hcJ
    linarith
  have h4 : ‖wMul (wM (regParticlesOf sys)) (Hgrid eta m (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) (V w))‖ ≤
      5 / 3 * ‖wMul (wM (regParticlesOf sys)) (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) w)‖ +
      gridFlowConst_gL sys L (tv R θ) * ‖Hgrid eta m (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) w‖ := by
    rw [← hcomm]
    exact norm_wM_gridFlow_le_gL sys hL hθ.tv_nonneg hκb V hcomm _
  have h5 : ‖wMul (wM (regParticlesOf sys)) (Hgrid eta m (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) w)‖ ≤
      3 * (2 * Real.pi / L) ^ 2 / 4 * X + secondConst (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (gLgamma L (tv R θ)) (2 * Real.pi / L) m * Y := by
    have h := norm_wM_Hgrid_le (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData hγ hκb
      hsupp hg w
    have h6 := mul_le_mul_of_nonneg_left hX
        (by positivity : (0 : ℝ) ≤ 3 * (2 * Real.pi / L) ^ 2 / 4)
    have h7 := mul_le_mul_of_nonneg_left hY hsc
    linarith
  have h8 : ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) w‖ ≤ 5 * (2 * Real.pi / L) ^ 2 / 8 * Y +
        26 * gLCoupling sys L (tv R θ) *
          (J0g (gLCoupling sys L (tv R θ)) (2 * Real.pi / L) : ℝ) * S := by
    have h := (gridRegHam (eta := eta) (m := m) (P := regParticlesOf sys)
      (D := (posNucleiOf sys.nuclei).toNucData) hγ hκb hg).op_le w
    have h6 := mul_le_mul_of_nonneg_left hY
        (by positivity : (0 : ℝ) ≤ 5 * (2 * Real.pi / L) ^ 2 / 8)
    have h7 := mul_le_mul_of_nonneg_left hS hcH
    exact h.trans (add_le_add h6 h7)
  exact flow2_of_bounds hg hsc hcJ h1 h2 h4 h5 h8

/-- **The shells of the backward flows** (`thm:grid-dyn-sharp`): if `X(v) ≤ r F`, `‖W v‖ ≤ X_b` and
`‖v‖ ≤ S₀`, then for every time `τ` and register `r'`,
`(⌊m/4⌋+1)⁴ ‖1_{|q_{r'}|∞ > ⌊m/4⌋} U_g(τ) O_g v‖ ≤ m̄² r Φ` with
`Φ = flow2(σ; 8 C_χ F + 8 D⁽⁴⁾_χ S₀, (2 + 12 m̄) C_χ X_b + 14 D'_χ S₀, C_χ S₀)`, whenever
`secondConst ≤ σ r` and `r ≥ 1`. -/
theorem shell_gridFlow_gridObs_le_gL (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {R : ℝ} {θ : ℝ
    → ℝ} (hθ : Profile R θ) {m : ℕ}
    {κ : Lat3 → ℝ} (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (V : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hcomm : ∀ τ x, V τ (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (V τ x))
    (a : Fin eta) {χ : Lat3 → ℂ} (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (hχ4 : Summable fun ν => nsq ν ^ 2 * ‖χ ν‖)
    (v : EuclideanSpace ℂ (RCfg eta m)) {F Xb S0 r σ : ℝ} (hr : 1 ≤ r)
    (hX : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) v)‖ ≤ r * F)
    (hY : ‖wMul (wM (regParticlesOf sys)) v‖ ≤ Xb) (hS : ‖v‖ ≤ S0) (hXb : 0 ≤ Xb) (hS0 : 0 ≤ S0)
    (hsc : secondConst (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (gLgamma L (tv R θ)) (2 * Real.pi / L) m ≤ σ * r) (τ : ℝ) (r' : Fin eta) :
    (((m / 4 : ℕ) : ℝ) + 1) ^ 4 * ‖maskOp (High (m / 4) r') (V τ (gridObs a χ v))‖ ≤
      sys.maxMass ^ 2 * (r * flow2 (2 * Real.pi / L) (gridFlowConst_gL sys L (tv R θ))
        (26 * gLCoupling sys L (tv R θ) * (J0g (gLCoupling sys L (tv R θ)) (2 * Real.pi / L) : ℝ))
        σ (8 * (∑' ν, ‖χ ν‖) * F + 8 * momFour χ * S0)
        ((2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * Xb + 14 * momTwo χ * S0)
        ((∑' ν, ‖χ ν‖) * S0)) := by
  have hM := sys.one_le_maxMass
  have hCχ : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hD2 : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hD4 := momFour_nonneg χ
  have hcJ := gridFlowConst_gL_nonneg sys hL hθ.tv_nonneg
  have hcH : 0 ≤ 26 * gLCoupling sys L (tv R θ) *
      (J0g (gLCoupling sys L (tv R θ)) (2 * Real.pi / L) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (gLCoupling_nonneg sys hL hθ.tv_nonneg)) (Nat.cast_nonneg
        _)
  have hXo : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) (gridObs a χ v))‖ ≤
      (8 * (∑' ν, ‖χ ν‖) * F + 8 * momFour χ * S0) * r := by
    have h := norm_wM_sq_gridObs_le (regParticlesOf sys) a hχ1 hχ4 v
    have h1 := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 8 * (∑' ν, ‖χ ν‖))
    have h2 := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 8 * momFour χ)
    have h3 : 8 * momFour χ * S0 ≤ 8 * momFour χ * S0 * r :=
      le_mul_of_one_le_right (by positivity) hr
    have e : (8 * (∑' ν, ‖χ ν‖) * F + 8 * momFour χ * S0) * r =
        8 * (∑' ν, ‖χ ν‖) * (r * F) + 8 * momFour χ * S0 * r := by ring
    rw [e]
    linarith
  have hWo : ‖wMul (wM (regParticlesOf sys)) (gridObs a χ v)‖ ≤
      (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * Xb + 14 * momTwo χ * S0 := by
    have h := norm_wM_gridObs_le (regParticlesOf sys) a hχ1 hχ2 v
    have hc1 : 0 ≤ (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) :=
      mul_nonneg (by linarith) hCχ
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hY hc1)
      (mul_le_mul_of_nonneg_left hS (by positivity)))
  have hSo : ‖gridObs a χ v‖ ≤ (∑' ν, ‖χ ν‖) * S0 :=
    (((gridObs a χ).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_gridObs_le a hχ1) (norm_nonneg v))).trans
      (mul_le_mul_of_nonneg_left hS hCχ)
  have hflow := norm_wM_sq_gridFlow_le_gL sys hL hθ hκ.bound hκ.support (V τ) (hcomm τ) _ hXo hWo
      hSo
  have hWo0 : 0 ≤ (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * Xb + 14 * momTwo χ * S0 :=
    add_nonneg (mul_nonneg (mul_nonneg (by linarith) hCχ) hXb) (mul_nonneg (by positivity) hS0)
  have hhom := flow2_le_mul (g := 2 * Real.pi / L)
    (x := 8 * (∑' ν, ‖χ ν‖) * F + 8 * momFour χ * S0) hcJ hcH hWo0 (mul_nonneg hCχ hS0) hr hsc
    le_rfl
  have hsh := sq_sq_mul_norm_high_le (regParticlesOf sys) (m / 4) r' (V τ (gridObs a χ v))
  exact hsh.trans (mul_le_mul_of_nonneg_left (hflow.trans hhom) (sq_nonneg _))

end Flow

section Grid

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  {θ : ℝ → ℝ} (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 0 < L) {R : ℝ} (hθ : Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hθ hPeriodic in
/-- **Duality on the grid, with the flow shell as a parameter** (`thm:grid-dyn-sharp`): the
statement of `grid_duality` for every bound `τ_φ` of the shells `‖1_{|q_r|∞ > ⌊m/4⌋} U_g(τ) w‖`
of the flow, instead of the a priori shell `m̄ W_φ/(⌊m/4⌋+1)²`: `|⟪a(t) - ψ_g(t), w⟫|` is at most
`t` times `(η t₂)(η C_tail(M_l) ρ₂) + Z_c (A(s₀, m)(t₄ m̄ W_φ + τ_φ X_a) + 52 m τ_φ t₄)`. -/
theorem grid_duality_shell_gL (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ} (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ))
        (gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (rho₂ rho₄ : ℝ) (hK₄ : 1 ≤ (2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ))
    (hRho₂ : 0 ≤ rho₂) (hRhoScale₂ : rho₂ ^ 2 * ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) = 1)
    (hRho₄ : 0 ≤ rho₄) (hRhoScale₄ : rho₄ ^ 2 * ((2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ)) = 1)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (w : EuclideanSpace ℂ (RCfg eta m)) (Wφ τφ : ℝ)
    (hW : ∀ τ, ‖wMul (wM (regParticlesOf sys)) (Ug τ w)‖ ≤ Wφ) (hτφ0 : 0 ≤ τφ)
    (hτ : ∀ τ r, ‖maskOp (High (m / 4) r) (Ug τ w)‖ ≤ τφ) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB_gL sys L (tv R θ) Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let Ct : ℝ → ℝ := fun M => gLtailM sys L (tv R θ) Hunit M
    let tl : ℝ → ℝ → ℝ := fun K ρ =>
      (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    let s₀ : ℕ := m / 4
    let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (gLgamma L (tv R θ))
    let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
    let t₂ : ℝ := tl (g * ((2 * m : ℕ) : ℝ)) rho₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) rho₄
    ‖⟪regCoeff m (U t (molecularH2StateMap eta g u₀)) -
        Ug t (regCoeff m (molecularH2StateMap eta g u₀)), w⟫_ℂ‖ ≤
      ((eta * t₂) * (eta * (Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂)) +
        Zg * (formA s₀ m * (t₄ * (sys.maxMass * Wφ) + τφ * Xa) + 52 * m * (τφ * t₄))) * t := by
  intro g b S0 Ξ₀ Ξ₁ M₀ Ct tl s₀ Zg Xa t₂ t₄
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ b := relB_gL_nonneg sys L (tv R θ) Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ gLgamma L (tv R θ) := (gLgamma_pos hL hθ.tv_nonneg).le
  have hs₀ : 2 ≤ s₀ := by show 2 ≤ m / 4; omega
  have hs₀m : s₀ ≤ m := Nat.div_le_self m 4
  have hs₀r : (2 : ℝ) ≤ s₀ := by exact_mod_cast hs₀
  have hs₀2m : (s₀ : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
    exact_mod_cast (show s₀ ≤ 2 * m by omega)
  have hK₄' : 1 ≤ g * (s₀ : ℝ) := hK₄
  have hK₄2g : 2 * g ≤ g * (s₀ : ℝ) := by nlinarith
  have hK₂ : 1 ≤ g * ((2 * m : ℕ) : ℝ) := hK₄'.trans (mul_le_mul_of_nonneg_left hs₀2m hg.le)
  have hK₂2g : 2 * g ≤ g * ((2 * m : ℕ) : ℝ) :=
    hK₄2g.trans (mul_le_mul_of_nonneg_left hs₀2m hg.le)
  have hW0 : 0 ≤ Wφ := (norm_nonneg _).trans (hW 0)
  have hS0 : 0 ≤ S0 := norm_nonneg _
  have hΞ₀ : 0 ≤ Ξ₀ := by positivity
  have hΞ₁ : 0 ≤ Ξ₁ := by positivity
  have hM₀ : 0 ≤ M₀ := by positivity
  have hCt₀ : 0 ≤ Ct M₀ :=
    gLtailM_nonneg sys hL hθ.tv_nonneg Hunit hM₀
  have htl0 : ∀ K ρ, 0 ≤ ρ → 0 ≤ tl K ρ := by
    intro K ρ hρ
    show 0 ≤ (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    have h1 : 0 ≤ 2 * sys.maxMass / K ^ 2 := div_nonneg (by linarith) (sq_nonneg K)
    exact mul_nonneg h1 (add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hCt₀ hρ))
  have ht₂0 : 0 ≤ t₂ := htl0 _ _ hRho₂
  have ht₄0 : 0 ≤ t₄ := htl0 _ _ hRho₄
  have hZg : 0 ≤ Zg := Zc_nonneg hγ
  -- the trajectory and its Duhamel equation on the register
  choose u hu1 hu2 using fun s => hgraph s u₀
  have ha : ∀ s, HasDerivAt (fun s => regCoeff m (U s (molecularH2StateMap eta g u₀)))
      (-(Complex.I • (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ g
          (regCoeff m (U s (molecularH2StateMap eta g u₀))) +
        (regCoeff m (coulombFourierPotentialH2 sys g H (u s - molecularH2Truncate (2 * m) (u s))) -
          DeltaGL sys L hL hθ m κ (regCoeff m (U s (molecularH2StateMap eta g u₀))))))) s := by
    intro s
    have h1 := ((regCoeff (eta := eta) m).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
      (hderiv s u₀)
    refine h1.congr_deriv ?_
    rw [ContinuousLinearMap.coe_restrictScalars', map_neg, map_smul, ← hu2 s,
      regCoeff_H_eq_grid_gL sys L H hKernel hL hθ m κ (u s), hu1 s]
  have hbound := duality_pairing_le (Hgrid_isSymmetric hκ.even) Ug hg0 hgcomm hgderiv ha w ht
    (B := (eta * t₂) * (eta * (Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂)) +
      Zg * (formA s₀ m * (t₄ * (sys.maxMass * Wφ) + τφ * Xa) + 52 * m * (τφ * t₄)))
    (fun s _ => ?_)
  · simp only [h0] at hbound
    exact hbound
  -- the pairing at time `s`
  set φ := Ug (s - t) w with hφ
  have hφW : ‖wMul (wM (regParticlesOf sys)) φ‖ ≤ Wφ := hW (s - t)
  have hφT : ‖wMul wTot φ‖ ≤ sys.maxMass * Wφ :=
    (norm_wMul_wTot_le (regParticlesOf sys) φ).trans
      (mul_le_mul_of_nonneg_left hφW (regParticlesOf sys).maxMass_pos.le)
  have hu_le : ‖u s‖ ≤ M₀ := by
    have h := h2norm_le sys L (u s)
    have hT := kinetic_le_elliptic_gL sys L H hKernel Hunit hL hθ hPeriodic hC (u s)
    rw [hu1 s, LinearIsometryEquiv.norm_map] at h
    rw [hu1 s, hu2 s, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hT
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    show ‖molecularH2StateMap eta g u₀‖ + 2 * ‖coulombFourierKineticH2 sys g (u s)‖ ≤ S0 + 2 * Ξ₀
    linarith
  -- (i) the Galerkin source against the lift of the flow
  have hi : ‖⟪regCoeff m (coulombFourierPotentialH2 sys g H
      (u s - molecularH2Truncate (2 * m) (u s))),
      φ⟫_ℂ‖ ≤ (eta * t₂) * (eta * (Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂)) := by
    refine (norm_inner_galSource_le_gL sys L H hKernel hθ m (u s) φ).trans ?_
    have hδ : ‖molecularH2StateMap eta g (u s) -
        molecularH2Truncate (2 * m) (molecularH2StateMap eta g (u s))‖ ≤ eta * t₂ := by
      refine (norm_sub_truncate_le hg (2 * m) _).trans ?_
      have htl := fun c => (tails_at_time_gL sys L H hKernel Hunit hL hθ hPeriodic hC U hgraph c
        (g * ((2 * m : ℕ) : ℝ)) rho₂ hK₂ hRho₂ hRhoScale₂ u₀ v₀ huv s (u s) (hu1 s) (hu2 s)).2
      calc ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g (u s))‖
          ≤ ∑ _c : Fin eta, t₂ := sum_le_sum fun c _ => htl c
        _ = eta * t₂ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hMl : 0 ≤ (1 + g ^ 2) * (sys.maxMass * Wφ) := by positivity
    have hl : ‖cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm φ)‖ ≤
        (1 + g ^ 2) * (sys.maxMass * Wφ) :=
      (norm_cubeLift_regUnitary_le g φ).trans (mul_le_mul_of_nonneg_left hφT (by positivity))
    have hΛ : ‖coulombFourierPotentialH2 sys g H
        (cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm φ)) -
        molecularH2Truncate (2 * m) (coulombFourierPotentialH2 sys g H
          (cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm φ)))‖ ≤
        eta * (Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂) := by
      refine (norm_sub_truncate_le hg (2 * m) _).trans ?_
      calc ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (coulombFourierPotentialH2 sys g H
            (cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm φ)))‖
          ≤ ∑ _c : Fin eta, Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂ :=
            sum_le_sum fun c _ => potential_tail_le_gL sys L H hKernel Hunit hL hθ hPeriodic c _
                rho₂ _ hK₂ hRho₂ hRhoScale₂ hMl _ hl
        _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hΛ0 : 0 ≤ eta * (Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
        (gLtailM_nonneg sys hL hθ.tv_nonneg Hunit hMl) hRho₂)
    exact mul_le_mul hδ hΛ (norm_nonneg _) (by positivity)
  -- (ii) the grid difference against the flow
  have hii : ‖⟪DeltaGL sys L hL hθ m κ (regCoeff m (U s (molecularH2StateMap eta g u₀))), φ⟫_ℂ‖ ≤
      Zg * (formA s₀ m * (t₄ * (sys.maxMass * Wφ) + τφ * Xa) + 52 * m * (τφ * t₄)) := by
    rw [← inner_conj_symm, RCLike.norm_conj]
    have hτu : ∀ r, ‖maskOp (High s₀ r) (regCoeff m
        (U s (molecularH2StateMap eta g u₀)))‖ ≤ t₄ := by
      intro r
      rw [← hu1 s]
      exact (norm_high_regCoeff_le hg s₀ r _).trans (tails_at_time_gL sys L H hKernel Hunit hL
        hθ hPeriodic hC U hgraph r (g * (s₀ : ℝ)) rho₄ hK₄' hRho₄ hRhoScale₄ u₀ v₀ huv s (u s) (hu1
            s) (hu2 s)).2
    have hτv : ∀ r, ‖maskOp (High s₀ r) φ‖ ≤ τφ := fun r => hτ (s - t) r
    have hD0 := PlaneWaveGridG.Delta_form (P := regParticlesOfG sys)
      (D := gLNucData sys hL hθ) hγ
      (by omega : 1 ≤ s₀) hs₀m hκ.gridKernel (regCoeff m (U s (molecularH2StateMap eta g u₀))) φ
      ht₄0 hτφ0 hτu hτv
    have hD : ‖⟪φ, DeltaGL sys L hL hθ m κ (regCoeff m (U s (molecularH2StateMap eta g u₀)))⟫_ℂ‖ ≤
        Zg * (formA s₀ m * (t₄ * ‖wMul wTot φ‖ +
          τφ * ‖wMul wTot (regCoeff m (U s (molecularH2StateMap eta g u₀)))‖) +
          52 * m * (τφ * t₄)) := hD0
    refine hD.trans ?_
    have haT : ‖wMul wTot (regCoeff m (U s (molecularH2StateMap eta g u₀)))‖ ≤ Xa := by
      rw [← hu1 s]
      exact (norm_wTot_regCoeff_stateMap_le hg (u s)).trans
        (mul_le_mul_of_nonneg_left hu_le (by positivity))
    have hA := formA_nonneg s₀ m
    have h1 : t₄ * ‖wMul wTot φ‖ + τφ * ‖wMul wTot
        (regCoeff m (U s (molecularH2StateMap eta g u₀)))‖ ≤
        t₄ * (sys.maxMass * Wφ) + τφ * Xa :=
      add_le_add (mul_le_mul_of_nonneg_left hφT ht₄0) (mul_le_mul_of_nonneg_left haT hτφ0)
    have h2 := mul_le_mul_of_nonneg_left h1 hA
    have h3 := add_le_add h2 (le_refl (52 * (m : ℝ) * (τφ * t₄)))
    exact mul_le_mul_of_nonneg_left h3 hZg
  rw [inner_sub_left]
  exact (norm_sub_le _ _).trans (add_le_add hi hii)

include hKernel hL hθ hPeriodic in
-- the whole proof of `grid_observable_error` plus the second-moment budget: twice the default
set_option maxHeartbeats 400000 in
/-- **Observable error on the grid, sharp** (`thm:grid-dyn-sharp`, Fourier side, explicit form).
The setting of `grid_observable_error`, with in addition `D⁽⁴⁾_χ = Σ |ν|⁴ |χ̂(ν)| < ∞` and a first
layer-cake threshold `k₀ ≥ 2` with `g k₀ ≥ 1`: `|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫|` is at
most `2 δ (C_χ t₁ + τ_χ ‖ψ₀‖ + ‖O‖ δ) + ‖O‖ δ²` (term (I)) `+ C_χ t₁² + τ_χ^∞(m) ‖ψ₀‖²` (term (II))
`+ 2 t B_d` (term (III)), where `B_d` is the bound of `grid_duality_shell_gL` at the shell
`τ_φ = m̄² r Φ/(⌊m/4⌋+1)⁴` given by the double kinetic division of the second moments
`X(U_g(τ) O_g v) ≤ r Φ` of the backward flows, `r = (4m+1)^{3/2}`: here
`ξ = ‖ψ₀‖ + (4/g²) Ξ₀ + (2/g²) η √Q` (`second_moment_regCoeff_le_gL`), `F = flow2(σ; ξ, X_a, ‖ψ₀‖)`
bounds `X(v)/r` for `v ∈ {P ψ(t), ψ_g(t)}`, `o = 8 C_χ F + 8 D⁽⁴⁾_χ ‖ψ₀‖` bounds `X(O_g v)/r`
(`lem:grid-obs2`), and `Φ = flow2(σ; o, W_o, C_χ ‖ψ₀‖)`; none of `ξ, F, o, Φ` depends on `m`. -/
theorem grid_observable_error_sharp_gL (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ} (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ))
        (gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (rho₁ rho₂ rho₄ : ℝ) (hK₄ : 1 ≤ (2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ))
    (hRho₁ : 0 ≤ rho₁) (hRhoScale₁ : rho₁ ^ 2 * ((2 * Real.pi / L) * (m : ℝ)) = 1)
    (hRho₂ : 0 ≤ rho₂) (hRhoScale₂ : rho₂ ^ 2 * ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) = 1)
    (hRho₄ : 0 ≤ rho₄) (hRhoScale₄ : rho₄ ^ 2 * ((2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ)) = 1)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (a : Fin eta) (χ : Lattice3 → ℂ) (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (hχ4 : Summable fun ν => nsq ν ^ 2 * ‖χ ν‖)
    (hreal : ∀ ν, χ (-ν) = conj (χ ν)) (k₀ : ℕ) (hk₀ : 2 ≤ k₀)
    (hk₀g : 1 ≤ (2 * Real.pi / L) * k₀) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB_gL sys L (tv R θ) Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let Ct : ℝ → ℝ := fun M => gLtailM sys L (tv R θ) Hunit M
    let tl : ℝ → ℝ → ℝ := fun K ρ =>
      (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    let s₀ : ℕ := m / 4
    let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (gLgamma L (tv R θ))
    let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
    let CO : ℝ := ‖convOp (eta := eta) a χ‖
    let Cχ : ℝ := ∑' ν, ‖χ ν‖
    let τχ : ℝ := ∑' ν, if g * (m : ℝ) < g * Real.sqrt (latticeNormSq ν) then ‖χ ν‖ else 0
    let cJ : ℝ := gridFlowConst_gL sys L (tv R θ)
    let Xb : ℝ := 5 / 3 * Xa + cJ * S0
    let W : ℝ := 5 / 3 * ((2 + 12 * sys.maxMass) * Cχ * Xb + 14 * momTwo χ * S0) + cJ * (Cχ * S0)
    let Q : ℝ := (k₀ : ℝ) ^ 4 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 / g ^ 4 + 30 * Ct M₀ ^ 2 / g
    let r : ℝ := Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3
    let cH : ℝ := 26 * gLCoupling sys L (tv R θ) * (J0g (gLCoupling sys L (tv R θ)) g : ℝ)
    let σ : ℝ := Zg * (52 * (J0g (sys.maxMass * Zg) g : ℝ) + 4 * Real.sqrt 53 * sys.maxMass)
    let ξ : ℝ := S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * Real.sqrt Q)
    let F : ℝ := flow2 g cJ cH σ ξ Xa S0
    let Wo : ℝ := (2 + 12 * sys.maxMass) * Cχ * Xb + 14 * momTwo χ * S0
    let o : ℝ := 8 * Cχ * F + 8 * momFour χ * S0
    let Φ : ℝ := flow2 g cJ cH σ o Wo (Cχ * S0)
    let τφ : ℝ := sys.maxMass ^ 2 * (r * Φ) / ((s₀ : ℝ) + 1) ^ 4
    let t₁ : ℝ := tl (g * (m : ℝ)) rho₁
    let t₂ : ℝ := tl (g * ((2 * m : ℕ) : ℝ)) rho₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) rho₄
    let δ : ℝ := eta * t₂
    let Bd : ℝ := (eta * t₂) * (eta * (Ct ((1 + g ^ 2) * (sys.maxMass * W)) * rho₂)) +
      Zg * (formA s₀ m * (t₄ * (sys.maxMass * W) + τφ * Xa) + 52 * m * (τφ * t₄))
    let ψg := Ug t (regCoeff m (molecularH2StateMap eta g u₀))
    ‖⟪U t (molecularH2StateMap eta g u₀), convOp a χ (U t (molecularH2StateMap eta g u₀))⟫_ℂ -
        ⟪ψg, gridObs a χ ψg⟫_ℂ‖ ≤
      (2 * (δ * (Cχ * t₁ + τχ * S0 + CO * δ)) + CO * δ ^ 2) +
        (Cχ * (t₁ * t₁) + supTail χ m * (S0 * S0)) + 2 * (Bd * t) := by
  intro g b S0 Ξ₀ Ξ₁ M₀ Ct tl s₀ Zg Xa CO Cχ τχ cJ Xb W Q r cH σ ξ F Wo o Φ τφ t₁ t₂ t₄ δ Bd ψg
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ b := relB_gL_nonneg sys L (tv R θ) Hunit hC
  have hg : 0 < g := by positivity
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hs₀m : s₀ ≤ m := Nat.div_le_self m 4
  have hs₀mr : (s₀ : ℝ) ≤ m := by exact_mod_cast hs₀m
  have hK₁ : 1 ≤ g * (m : ℝ) :=
    (show 1 ≤ g * (s₀ : ℝ) from hK₄).trans (mul_le_mul_of_nonneg_left hs₀mr hg.le)
  have hK₁2g : 2 * g ≤ g * (m : ℝ) := by nlinarith
  have hm2m : (m : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by push_cast; linarith
  have hK₂ : 1 ≤ g * ((2 * m : ℕ) : ℝ) := hK₁.trans (mul_le_mul_of_nonneg_left hm2m hg.le)
  have hK₂2g : 2 * g ≤ g * ((2 * m : ℕ) : ℝ) := hK₁2g.trans (mul_le_mul_of_nonneg_left hm2m hg.le)
  have hS0 : 0 ≤ S0 := norm_nonneg _
  have hΞ₀ : 0 ≤ Ξ₀ := by positivity
  have hΞ₁ : 0 ≤ Ξ₁ := by positivity
  have hM₀ : 0 ≤ M₀ := by positivity
  have hCt₀ : 0 ≤ Ct M₀ :=
    gLtailM_nonneg sys hL hθ.tv_nonneg Hunit hM₀
  have htl0 : ∀ K ρ, 0 ≤ ρ → 0 ≤ tl K ρ := by
    intro K ρ hρ
    show 0 ≤ (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    have h1 : 0 ≤ 2 * sys.maxMass / K ^ 2 := div_nonneg (by linarith) (sq_nonneg K)
    exact mul_nonneg h1 (add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hCt₀ hρ))
  have ht₁0 : 0 ≤ t₁ := htl0 _ _ hRho₁
  have ht₂0 : 0 ≤ t₂ := htl0 _ _ hRho₂
  have hδ0 : 0 ≤ δ := mul_nonneg (Nat.cast_nonneg _) ht₂0
  have hCO : 0 ≤ CO := norm_nonneg _
  have hCχ : 0 ≤ Cχ := tsum_nonneg fun ν => norm_nonneg _
  have hτχ : 0 ≤ τχ := tsum_nonneg fun ν => by split_ifs <;> simp
  have hcJ : 0 ≤ cJ := gridFlowConst_gL_nonneg sys hL hθ.tv_nonneg
  have hXa : 0 ≤ Xa := by positivity
  -- the exact state at time `t`
  obtain ⟨u, hu1, hu2⟩ := hgraph t u₀
  have hψ : U t (molecularH2StateMap eta g u₀) = molecularH2StateMap eta g u := hu1.symm
  have hSu : ‖molecularH2StateMap eta g u‖ = S0 := by
    rw [← hψ, LinearIsometryEquiv.norm_map]
  have hnorm_le : ∀ (x : MolecularFourierH2 eta), ‖molecularH2StateMap eta g x‖ = S0 →
      ‖coulombFourierKineticH2 sys g x‖ ≤ Ξ₀ → ‖x‖ ≤ M₀ := by
    intro x hx hT
    refine (h2norm_le sys L x).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    show ‖molecularH2StateMap eta g x‖ + 2 * ‖coulombFourierKineticH2 sys g x‖ ≤ S0 + 2 * Ξ₀
    rw [hx]
    linarith
  have hu_le : ‖u‖ ≤ M₀ := by
    refine hnorm_le u hSu ?_
    have h := kinetic_le_elliptic_gL sys L H hKernel Hunit hL hθ hPeriodic hC u
    rw [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
    exact h
  have hu₀_le : ‖u₀‖ ≤ M₀ :=
    hnorm_le u₀ rfl (kinetic_le_elliptic_gL sys L H hKernel Hunit hL hθ hPeriodic hC u₀)
  -- the tails at `K` and `2K`
  have ht₁ : ∀ c, ‖tailMask g (g * (m : ℝ)) c (molecularH2StateMap eta g u)‖ ≤ t₁ := fun c =>
    (tails_at_time_gL sys L H hKernel Hunit hL hθ hPeriodic hC U hgraph c (g * (m : ℝ)) rho₁ hK₁
        hRho₁ hRhoScale₁ u₀ v₀ huv t u
      hu1 hu2).2
  have ht₂ : ∀ c, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖ ≤ t₂ :=
    fun c => (tails_at_time_gL sys L H hKernel Hunit hL hθ hPeriodic hC U hgraph c
      (g * ((2 * m : ℕ) : ℝ)) rho₂ hK₂ hRho₂ hRhoScale₂ u₀ v₀ huv t u hu1 hu2).2
  have hsum : ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖
      ≤ δ := by
    calc ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖
        ≤ ∑ _c : Fin eta, t₂ := sum_le_sum fun c _ => ht₂ c
      _ = δ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hδ : ‖molecularH2StateMap eta g u -
      molecularH2Truncate (2 * m) (molecularH2StateMap eta g u)‖ ≤ δ :=
    (norm_sub_truncate_le hg (2 * m) _).trans hsum
  -- symmetry of the observables
  have hO : ∀ x y, ⟪convOp a χ x, y⟫_ℂ = ⟪x, convOp a χ y⟫_ℂ := convOp_symm a hχ1 hreal
  have hOg : ∀ x y : EuclideanSpace ℂ (RCfg eta m), ⟪gridObs a χ x, y⟫_ℂ = ⟪x, gridObs a χ y⟫_ℂ :=
    gridObs_symm a hχ1 hreal
  -- (I): the never-projected tail at cutoff `2K`
  have hI : ‖⟪molecularH2StateMap eta g u, convOp a χ (molecularH2StateMap eta g u)⟫_ℂ -
      ⟪molecularH2Truncate (2 * m) (molecularH2StateMap eta g u),
        convOp a χ (molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))⟫_ℂ‖ ≤
      2 * (δ * (Cχ * t₁ + τχ * S0 + CO * δ)) + CO * δ ^ 2 := by
    have h := norm_inner_sub_proj_le (convOp a χ) hO (molecularH2StateMap eta g u)
      (molecularH2StateMap eta g u - molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))
    rw [sub_sub_cancel] at h
    refine h.trans ?_
    have hchi : ‖convOp a χ (molecularH2StateMap eta g u) -
        molecularH2Truncate (2 * m) (convOp a χ (molecularH2StateMap eta g u))‖ ≤
        Cχ * t₁ + τχ * S0 + CO * δ := by
      have hc := chitail hg (2 * m) a hχ1 (molecularH2StateMap eta g u)
      have e : g * ((2 * m : ℕ) : ℝ) / 2 = g * (m : ℝ) := by push_cast; ring
      rw [e] at hc
      refine hc.trans ?_
      have hA : Cχ * ‖tailMask g (g * (m : ℝ)) a (molecularH2StateMap eta g u)‖ ≤ Cχ * t₁ :=
        mul_le_mul_of_nonneg_left (ht₁ a) hCχ
      have hB : τχ * ‖molecularH2StateMap eta g u‖ ≤ τχ * S0 := by rw [hSu]
      have hC' : CO * ∑ c : Fin eta,
          ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖ ≤ CO * δ :=
        mul_le_mul_of_nonneg_left hsum hCO
      exact add_le_add (add_le_add hA hB) hC'
    have h1 : ‖⟪molecularH2StateMap eta g u - molecularH2Truncate (2 * m)
        (molecularH2StateMap eta g u),
        convOp a χ (molecularH2StateMap eta g u)⟫_ℂ‖ ≤ δ * (Cχ * t₁ + τχ * S0 + CO * δ) := by
      rw [inner_sub_truncate_left]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul hδ hchi (norm_nonneg _) hδ0)
    have h2 : ‖⟪molecularH2StateMap eta g u - molecularH2Truncate (2 * m)
        (molecularH2StateMap eta g u),
        convOp a χ (molecularH2StateMap eta g u -
          molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))⟫_ℂ‖ ≤ CO * δ ^ 2 := by
      refine (norm_inner_le_norm _ _).trans ?_
      set d := molecularH2StateMap eta g u - molecularH2Truncate (2 * m)
          (molecularH2StateMap eta g u)
      have hd : ‖convOp a χ d‖ ≤ CO * ‖d‖ := (convOp a χ).le_opNorm d
      calc ‖d‖ * ‖convOp a χ d‖ ≤ ‖d‖ * (CO * ‖d‖) := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
        _ = CO * ‖d‖ ^ 2 := by ring
        _ ≤ CO * δ ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hδ 2) hCO
    linarith
  -- (II): the form bound of the collocated observable
  have hA : ‖regCoeff m (molecularH2StateMap eta g u)‖ ≤ S0 :=
    (norm_regCoeff_le _).trans hSu.le
  have hII : ‖⟪molecularH2Truncate (2 * m) (molecularH2StateMap eta g u),
        convOp a χ (molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))⟫_ℂ -
      ⟪regCoeff m (molecularH2StateMap eta g u),
        gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ‖ ≤
      Cχ * (t₁ * t₁) + supTail χ m * (S0 * S0) := by
    rw [inner_truncate_convOp a hχ1, norm_sub_rev]
    refine (norm_inner_gridObs_sub_galObs_le a hχ1 _ _).trans ?_
    have hH : ‖maskOp (High m a) (regCoeff m (molecularH2StateMap eta g u))‖ ≤ t₁ :=
      (norm_high_regCoeff_le hg m a _).trans (ht₁ a)
    have h1 : ‖maskOp (High m a) (regCoeff m (molecularH2StateMap eta g u))‖ *
        ‖maskOp (High m a) (regCoeff m (molecularH2StateMap eta g u))‖ ≤ t₁ * t₁ :=
      mul_le_mul hH hH (norm_nonneg _) ht₁0
    have h2 : ‖regCoeff m (molecularH2StateMap eta g u)‖ *
        ‖regCoeff m (molecularH2StateMap eta g u)‖ ≤ S0 * S0 :=
      mul_le_mul hA hA (norm_nonneg _) hS0
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hCχ)
      (mul_le_mul_of_nonneg_left h2 (supTail_nonneg χ m))
  -- (III): the in-band error, by duality against the backward grid flows
  have ha₀ : ‖wMul (wM (regParticlesOf sys)) (regCoeff m (molecularH2StateMap eta g u₀))‖ ≤ Xa :=
    (norm_wM_le_wTot (regParticlesOf sys) _).trans ((norm_wTot_regCoeff_stateMap_le hg u₀).trans
      (mul_le_mul_of_nonneg_left hu₀_le (by positivity)))
  have haS₀ : ‖regCoeff m (molecularH2StateMap eta g u₀)‖ ≤ S0 := norm_regCoeff_le _
  have haT : ‖wMul (wM (regParticlesOf sys)) (regCoeff m (molecularH2StateMap eta g u))‖ ≤ Xb := by
    have h : ‖wMul (wM (regParticlesOf sys)) (regCoeff m (molecularH2StateMap eta g u))‖ ≤ Xa :=
      (norm_wM_le_wTot (regParticlesOf sys) _).trans ((norm_wTot_regCoeff_stateMap_le hg u).trans
        (mul_le_mul_of_nonneg_left hu_le (by positivity)))
    show _ ≤ 5 / 3 * Xa + cJ * S0
    have : 0 ≤ cJ * S0 := mul_nonneg hcJ hS0
    linarith
  have hbT : ‖wMul (wM (regParticlesOf sys)) ψg‖ ≤ Xb := by
    refine (norm_wM_gridFlow_le_gL sys hL hθ.tv_nonneg hκ.bound (Ug t) (hgcomm t) _).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left ha₀ (by norm_num))
      (mul_le_mul_of_nonneg_left haS₀ hcJ)
  have hbS : ‖ψg‖ ≤ S0 := by
    show ‖Ug t (regCoeff m (molecularH2StateMap eta g u₀))‖ ≤ S0
    rw [LinearIsometryEquiv.norm_map]
    exact haS₀
  have hWa : ∀ τ, ‖wMul (wM (regParticlesOf sys))
      (Ug τ (gridObs a χ (regCoeff m (molecularH2StateMap eta g u))))‖ ≤ W := fun τ =>
    norm_wM_gridFlow_gridObs_le_gL sys hL hθ.tv_nonneg hκ.bound (Ug τ) (hgcomm τ) a hχ1 hχ2 _ haT hA
  have hWb : ∀ τ, ‖wMul (wM (regParticlesOf sys)) (Ug τ (gridObs a χ ψg))‖ ≤ W := fun τ =>
    norm_wM_gridFlow_gridObs_le_gL sys hL hθ.tv_nonneg hκ.bound (Ug τ) (hgcomm τ) a hχ1 hχ2 _ hbT
        hbS
  -- the sharp shells: second moments of the backward flows and the double kinetic division
  have hγ : 0 ≤ gLgamma L (tv R θ) := (gLgamma_pos hL hθ.tv_nonneg).le
  have hr : 1 ≤ r := one_le_sqrt_pow_three m
  have hr0 : 0 ≤ r := by linarith
  have hZg : 0 ≤ Zg := Zc_nonneg hγ
  have hσ0 : 0 ≤ σ := mul_nonneg hZg (by positivity)
  have hcH : 0 ≤ cH :=
    mul_nonneg (mul_nonneg (by norm_num) (gLCoupling_nonneg sys hL hθ.tv_nonneg)) (Nat.cast_nonneg
        _)
  have hsc : secondConst (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (gLgamma L (tv R θ)) g m ≤ σ * r :=
    secondConst_le (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData hγ g m
  have hX2 : ∀ (s : ℝ) (x : MolecularFourierH2 eta),
      molecularH2StateMap eta g x = U s (molecularH2StateMap eta g u₀) → H x = U s (H u₀) →
      ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys))
        (regCoeff m (molecularH2StateMap eta g x)))‖ ≤ ξ * r := by
    intro s x hx1 hx2
    have h : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys))
        (regCoeff m (molecularH2StateMap eta g x)))‖ ≤
        S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * (Real.sqrt Q * r)) :=
      second_moment_regCoeff_le_gL sys L H hKernel Hunit hL hθ hPeriodic hC U hgraph m u₀ v₀ huv s x
          hx1 hx2 k₀ hk₀ hk₀g
    refine h.trans ?_
    have h1 : S0 ≤ S0 * r := le_mul_of_one_le_right hS0 hr
    have h2 : 4 / g ^ 2 * Ξ₀ ≤ 4 / g ^ 2 * Ξ₀ * r := le_mul_of_one_le_right (by positivity) hr
    have e : (S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * Real.sqrt Q)) * r =
        S0 * r + 4 / g ^ 2 * Ξ₀ * r + 2 / g ^ 2 * (eta * (Real.sqrt Q * r)) := by ring
    show _ ≤ (S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * Real.sqrt Q)) * r
    rw [e]
    linarith
  have hξ0 : 0 ≤ ξ := by
    have h1 : 0 ≤ 4 / g ^ 2 * Ξ₀ := mul_nonneg (by positivity) hΞ₀
    have h2 : 0 ≤ 2 / g ^ 2 * (eta * Real.sqrt Q) :=
      mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    show 0 ≤ S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * Real.sqrt Q)
    linarith
  have hF0 : 0 ≤ F := flow2_nonneg hcJ hcH hσ0 hξ0 hXa hS0
  have hξF : ξ ≤ F := le_flow2 hcJ hcH hσ0 hξ0 hXa hS0
  have hXaT : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys))
      (regCoeff m (molecularH2StateMap eta g u)))‖ ≤ r * F :=
    ((hX2 t u hu1 hu2).trans (mul_le_mul_of_nonneg_right hξF hr0)).trans_eq (mul_comm _ _)
  have hXbT : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) ψg)‖ ≤ r * F := by
    have h0' := hX2 0 u₀ (h0 _).symm (h0 _).symm
    have h := norm_wM_sq_gridFlow_le_gL sys hL hθ hκ.bound hκ.support (Ug t) (hgcomm t) _ h0' ha₀
        haS₀
    exact h.trans (flow2_le_mul hcJ hcH hXa hS0 hr hsc le_rfl)
  have hXb0 : 0 ≤ Xb := add_nonneg (mul_nonneg (by norm_num) hXa) (mul_nonneg hcJ hS0)
  have hD2 : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hWo0 : 0 ≤ Wo :=
    add_nonneg (mul_nonneg (mul_nonneg (by linarith) hCχ) hXb0) (mul_nonneg (by positivity) hS0)
  have ho0 : 0 ≤ o := add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCχ) hF0)
    (mul_nonneg (mul_nonneg (by norm_num) (momFour_nonneg χ)) hS0)
  have hΦ0 : 0 ≤ Φ := flow2_nonneg hcJ hcH hσ0 ho0 hWo0 (mul_nonneg hCχ hS0)
  have hτφ0 : 0 ≤ τφ := div_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hr0 hΦ0)) (by positivity)
  have hτ : ∀ v : EuclideanSpace ℂ (RCfg eta m),
      ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) v)‖ ≤ r * F →
      ‖wMul (wM (regParticlesOf sys)) v‖ ≤ Xb → ‖v‖ ≤ S0 →
      ∀ τ r', ‖maskOp (High (m / 4) r') (Ug τ (gridObs a χ v))‖ ≤ τφ := by
    intro v hXv hYv hSv τ r'
    have h := shell_gridFlow_gridObs_le_gL sys hL hθ hκ Ug hgcomm a hχ1 hχ2 hχ4 v hr hXv hYv hSv
        hXb0
      hS0 hsc τ r'
    have hpos : (0 : ℝ) < ((s₀ : ℝ) + 1) ^ 4 := by positivity
    show _ ≤ sys.maxMass ^ 2 * (r * Φ) / ((s₀ : ℝ) + 1) ^ 4
    rw [le_div_iff₀ hpos]
    linarith
  have hτa := hτ _ hXaT haT hA
  have hτb := hτ _ hXbT hbT hbS
  have he : regCoeff m (molecularH2StateMap eta g u) - ψg =
      regCoeff m (U t (molecularH2StateMap eta g u₀)) -
        Ug t (regCoeff m (molecularH2StateMap eta g u₀)) := by
    rw [hψ]
  have hd1 : ‖⟪regCoeff m (molecularH2StateMap eta g u) - ψg,
      gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ‖ ≤ Bd * t := by
    have h := grid_duality_shell_gL sys L H hKernel Hunit hL hθ hPeriodic hC U h0 hgraph
        hderiv m hm hκ Ug hg0
      hgcomm hgderiv rho₂ rho₄ hK₄ hRho₂ hRhoScale₂ hRho₄ hRhoScale₄ u₀ v₀ huv _ W τφ hWa hτφ0 hτa
          ht
    rw [he]
    exact h
  have hd2 : ‖⟪regCoeff m (molecularH2StateMap eta g u) - ψg, gridObs a χ ψg⟫_ℂ‖ ≤ Bd * t := by
    have h := grid_duality_shell_gL sys L H hKernel Hunit hL hθ hPeriodic hC U h0 hgraph
        hderiv m hm hκ Ug hg0
      hgcomm hgderiv rho₂ rho₄ hK₄ hRho₂ hRhoScale₂ hRho₄ hRhoScale₄ u₀ v₀ huv _ W τφ hWb hτφ0 hτb
          ht
    rw [he]
    exact h
  have hIII : ‖⟪regCoeff m (molecularH2StateMap eta g u),
        gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ - ⟪ψg, gridObs a χ ψg⟫_ℂ‖ ≤
      2 * (Bd * t) :=
    (norm_inner_sub_inner_le (gridObs a χ) hOg _ _).trans ((add_le_add hd1 hd2).trans_eq (by ring))
  -- assembly
  rw [hψ]
  have hsplit : ⟪molecularH2StateMap eta g u, convOp a χ (molecularH2StateMap eta g u)⟫_ℂ -
      ⟪ψg, gridObs a χ ψg⟫_ℂ =
      (⟪molecularH2StateMap eta g u, convOp a χ (molecularH2StateMap eta g u)⟫_ℂ -
        ⟪molecularH2Truncate (2 * m) (molecularH2StateMap eta g u),
          convOp a χ (molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))⟫_ℂ) +
      (⟪molecularH2Truncate (2 * m) (molecularH2StateMap eta g u),
          convOp a χ (molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))⟫_ℂ -
        ⟪regCoeff m (molecularH2StateMap eta g u),
          gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ) +
      (⟪regCoeff m (molecularH2StateMap eta g u),
          gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ - ⟪ψg, gridObs a χ ψg⟫_ℂ) := by
    ring
  rw [hsplit]
  exact (norm_add₃_le).trans (add_le_add (add_le_add hI hII) hIII)

end Grid

section Rates

variable {eta : ℕ} {ν : Type} [Fintype ν]


/-- The second-moment constant `Φ` of the backward flows of the smeared states
(`grid_observable_error_sharp_gL`) at the threshold `k₀ = kZero g`, as a function of the scalar data
`s0 = ‖ψ₀‖`, `hu = ‖H ψ₀‖`, `hs = ‖H ψ₀‖` (the decoded state of `H ψ₀`) and `hv = ‖H² ψ₀‖`; it does
not depend on `m` or `t`. -/
noncomputable def gridPhi_gL (sys : CoulombSystem eta ν) (L V Hunit : ℝ)
    (χ : Lattice3 → ℂ) (s0 hu hs hv : ℝ) : ℝ :=
  let g : ℝ := 2 * Real.pi / L
  let b : ℝ := relB_gL sys L V Hunit
  let S0 : ℝ := s0
  let Ξ₀ : ℝ := 2 * hu + 2 * b * S0
  let Ξ₁ : ℝ := 2 * hv + 2 * b * hs
  let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
  let Ct : ℝ → ℝ := fun M => gLtailM sys L V Hunit M
  let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (gLgamma L V)
  let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
  let Cχ : ℝ := ∑' ν, ‖χ ν‖
  let cJ : ℝ := gridFlowConst_gL sys L V
  let Xb : ℝ := 5 / 3 * Xa + cJ * S0
  let Q : ℝ := ((kZero g : ℕ) : ℝ) ^ 4 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 / g ^ 4 +
    30 * Ct M₀ ^ 2 / g
  let cH : ℝ := 26 * gLCoupling sys L V * (J0g (gLCoupling sys L V) g : ℝ)
  let σ : ℝ := Zg * (52 * (J0g (sys.maxMass * Zg) g : ℝ) + 4 * Real.sqrt 53 * sys.maxMass)
  let ξ : ℝ := S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * Real.sqrt Q)
  let F : ℝ := flow2 g cJ cH σ ξ Xa S0
  let Wo : ℝ := (2 + 12 * sys.maxMass) * Cχ * Xb + 14 * momTwo χ * S0
  let o : ℝ := 8 * Cχ * F + 8 * momFour χ * S0
  flow2 g cJ cH σ o Wo (Cχ * S0)


lemma gridPhi_gL_nonneg (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {R : ℝ} {θ : ℝ → ℝ} (hθ :
    Profile R θ) (Hunit : ℝ)
    (χ : Lattice3 → ℂ) (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    {s0 hu hs hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) :
    0 ≤ gridPhi_gL sys L (tv R θ) Hunit χ s0 hu hs hv := by
  have hb := relB_gL_nonneg sys L (tv R θ) Hunit hC
  have hM := sys.one_le_maxMass
  have hγ : 0 ≤ gLgamma L (tv R θ) := (gLgamma_pos hL hθ.tv_nonneg).le
  have hZ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (gLgamma L (tv R θ)) := Zc_nonneg hγ
  have hcJ := gridFlowConst_gL_nonneg sys hL hθ.tv_nonneg
  have hcH : 0 ≤ 26 * gLCoupling sys L (tv R θ) *
      (J0g (gLCoupling sys L (tv R θ)) (2 * Real.pi / L) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (gLCoupling_nonneg sys hL hθ.tv_nonneg)) (Nat.cast_nonneg
        _)
  have hCχ : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hD2 : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hD4 := momFour_nonneg χ
  have hσ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (gLgamma L (tv R θ)) * (52 * (J0g (sys.maxMass * Zc (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (gLgamma L (tv R θ))) (2 * Real.pi / L) : ℝ) +
        4 * Real.sqrt 53 * sys.maxMass) := by positivity
  have hΞ₀ : 0 ≤ 2 * hu + 2 * relB_gL sys L (tv R θ) Hunit * s0 := by positivity
  have hXa : 0 ≤ (1 + 1 / (2 * Real.pi / L) ^ 2) *
      (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB_gL sys L (tv R θ) Hunit * s0))) := by positivity
  have hXb : 0 ≤ 5 / 3 * ((1 + 1 / (2 * Real.pi / L) ^ 2) *
      (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB_gL sys L (tv R θ) Hunit * s0)))) +
      gridFlowConst_gL sys L (tv R θ) * s0 := by positivity
  show 0 ≤ flow2 _ _ _ _ _ _ _
  refine flow2_nonneg hcJ hcH hσ ?_ ?_ (mul_nonneg hCχ h0)
  · refine add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCχ) ?_)
      (mul_nonneg (mul_nonneg (by norm_num) hD4) h0)
    refine flow2_nonneg hcJ hcH hσ ?_ hXa h0
    have hQ : 0 ≤ (2 : ℝ) / (2 * Real.pi / L) ^ 2 * (eta * Real.sqrt
        (((kZero (2 * Real.pi / L) : ℕ) : ℝ) ^ 4 * (2 * hu + 2 * relB_gL sys L (tv R θ) Hunit * s0)
            ^ 2 +
          120 * sys.maxMass ^ 2 * (2 * hv + 2 * relB_gL sys L (tv R θ) Hunit * hs) ^ 2 /
            (2 * Real.pi / L) ^ 4 +
          30 * gLtailM sys L (tv R θ) Hunit
            (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB_gL sys L (tv R θ) Hunit * s0))) ^ 2 /
            (2 * Real.pi / L))) :=
      mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    have hX0 : 0 ≤ 4 / (2 * Real.pi / L) ^ 2 * (2 * hu + 2 * relB_gL sys L (tv R θ) Hunit * s0) :=
      mul_nonneg (by positivity) hΞ₀
    exact add_nonneg (add_nonneg h0 hX0) hQ
  · exact add_nonneg (mul_nonneg (mul_nonneg (by linarith) hCχ) hXb)
      (mul_nonneg (mul_nonneg (by norm_num) hD2) h0)


/-- The constants `(A₁, A₂, A₃)` of `thm:grid-dyn-sharp`, as functions of the scalar data
`s0 = ‖ψ₀‖`, `hu = ‖H ψ₀‖`, `hs = ‖H ψ₀‖` (the decoded state of `H ψ₀`) and `hv = ‖H² ψ₀‖`; they do
not depend on `m` (that is `K`) or on `t`.  Only `A₂` differs from `gridConsts`: the flow shell
enters through `T = 3072 m̄² Φ √g`, `Φ = gridPhi`. -/
noncomputable def gridConstsSharp_gL (sys : CoulombSystem eta ν) (L V Hunit : ℝ)
    (a : Fin eta) (χ : Lattice3 → ℂ) (s0 hu hs hv : ℝ) : ℝ × ℝ × ℝ :=
  let g : ℝ := 2 * Real.pi / L
  let b : ℝ := relB_gL sys L V Hunit
  let S0 : ℝ := s0
  let Ξ₀ : ℝ := 2 * hu + 2 * b * S0
  let Ξ₁ : ℝ := 2 * hv + 2 * b * hs
  let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
  let Ct : ℝ → ℝ := fun M => gLtailM sys L V Hunit M
  let τ₁ : ℝ := 2 * sys.maxMass * (2 * sys.maxMass * Ξ₁ + Ct M₀)
  let β₄ : ℝ := 128 * sys.maxMass * (128 * sys.maxMass * Ξ₁ + 8 * Ct M₀)
  let δ₁ : ℝ := eta * τ₁
  let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (gLgamma L V)
  let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
  let CO : ℝ := ‖convOp (eta := eta) a χ‖
  let Cχ : ℝ := ∑' ν, ‖χ ν‖
  let cJ : ℝ := gridFlowConst_gL sys L V
  let Xb : ℝ := 5 / 3 * Xa + cJ * S0
  let W : ℝ := 5 / 3 * ((2 + 12 * sys.maxMass) * Cχ * Xb + 14 * momTwo χ * S0) + cJ * (Cχ * S0)
  let cF : ℝ := 4 * Real.sqrt (5512 * g)
  let T : ℝ := 3072 * sys.maxMass ^ 2 * gridPhi_gL sys L V Hunit χ s0 hu hs hv *
    Real.sqrt g
  (2 * δ₁ * (Cχ * τ₁ + CO * δ₁) + CO * δ₁ ^ 2 + Cχ * τ₁ ^ 2,
    2 * (eta * δ₁ * Ct ((1 + g ^ 2) * (sys.maxMass * W)) +
      Zg * (cF * β₄ * (sys.maxMass * W) + cF * T * g ^ 2 * Xa + 52 * T * g * β₄)),
    2 * δ₁ * S0)


variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  {θ : ℝ → ℝ} (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 0 < L) {R : ℝ} (hθ : Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hθ hPeriodic in
/-- **`thm:grid-dyn-sharp`, rates (Fourier side).** For `m ≥ 8` and `K = g m ≥ 8`, and `χ` with
in addition `D⁽⁴⁾_χ = Σ |ν|⁴ |χ̂(ν)| < ∞`,
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤ A₁ K^{-5} + A₂ t K^{-3} + A₃ K^{-5/2} τ_χ(K)
+ ‖ψ₀‖² τ_χ^∞(m)`, with `(A₁, A₂, A₃) = gridConstsSharp` (independent of `K` and `t`): the energy
rate `t K^{-3}` of the Galerkin method (`thm:dyn`). -/
theorem grid_observable_rate_sharp_gL (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)

    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (a : Fin eta) (χ : Lattice3 → ℂ) (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (hχ4 : Summable fun ν => nsq ν ^ 2 * ‖χ ν‖)
    (hreal : ∀ ν, χ (-ν) = conj (χ ν))
    {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridConstsSharp_gL sys L (tv R θ) Hunit a χ ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then ‖χ ν‖ else 0
    let ψg := Ug t (regCoeff m (molecularH2StateMap eta g u₀))
    ‖⟪U t (molecularH2StateMap eta g u₀), convOp a χ (U t (molecularH2StateMap eta g u₀))⟫_ℂ -
        ⟪ψg, gridObs a χ ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖molecularH2StateMap eta g u₀‖ ^ 2 * supTail χ m := by
  intro g K A τχ ψg
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ relB_gL sys L (tv R θ) Hunit := relB_gL_nonneg sys L (tv R θ) Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ gLgamma L (tv R θ) := (gLgamma_pos hL hθ.tv_nonneg).le
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hK₄ : 1 ≤ g * ((m / 4 : ℕ) : ℝ) := by
    have : g * (m : ℝ) ≤ 8 * (g * ((m / 4 : ℕ) : ℝ)) := by nlinarith
    have hK' : (8 : ℝ) ≤ g * (m : ℝ) := hK
    linarith
  have hKpos : 0 < g * (m : ℝ) := by
    have hK' : (8 : ℝ) ≤ g * (m : ℝ) := hK
    linarith
  have hK₂pos : 0 < g * ((2 * m : ℕ) : ℝ) := by
    have : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    rw [this]
    linarith
  have hK₄pos : 0 < g * ((m / 4 : ℕ) : ℝ) := by linarith
  have hscale : ∀ X : ℝ, 0 < X → Real.sqrt (1 / X) ^ 2 * X = 1 := by
    intro X hX
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hS0 : 0 ≤ ‖molecularH2StateMap eta g u₀‖ := norm_nonneg _
  have hΞ₀ : 0 ≤ 2 * ‖H u₀‖ + 2 * relB_gL sys L (tv R θ) Hunit * ‖molecularH2StateMap eta g u₀‖ :=
      by
    positivity
  have hΞ₁ : 0 ≤ 2 * ‖H v₀‖ + 2 * relB_gL sys L (tv R θ) Hunit * ‖molecularH2StateMap eta g v₀‖ :=
      by
    positivity
  have hCt : ∀ M, 0 ≤ M → 0 ≤ gLtailM sys L (tv R θ) Hunit M :=
    fun M hM' => gLtailM_nonneg sys hL hθ.tv_nonneg Hunit hM'
  have hM₀ : 0 ≤ sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB_gL sys L (tv R θ) Hunit * ‖molecularH2StateMap eta g u₀‖)) := by
          positivity
  have hCχ : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hτχ : 0 ≤ τχ := tsum_nonneg fun ν => by split_ifs <;> simp
  have hZg : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (gLgamma L (tv R θ)) := Zc_nonneg hγ
  have hcJ : 0 ≤ gridFlowConst_gL sys L (tv R θ) := gridFlowConst_gL_nonneg sys hL hθ.tv_nonneg
  have hD : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hXa : 0 ≤ (1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB_gL sys L (tv R θ) Hunit * ‖molecularH2StateMap eta g u₀‖))) := by
          positivity
  have hW : 0 ≤ 5 / 3 * ((2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) *
      (5 / 3 * ((1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
        2 * (2 * ‖H u₀‖ + 2 * relB_gL sys L (tv R θ) Hunit * ‖molecularH2StateMap eta g u₀‖)))) +
        gridFlowConst_gL sys L (tv R θ) * ‖molecularH2StateMap eta g u₀‖) +
      14 * momTwo χ * ‖molecularH2StateMap eta g u₀‖) +
      gridFlowConst_gL sys L (tv R θ) * ((∑' ν, ‖χ ν‖) * ‖molecularH2StateMap eta g u₀‖) := by
          positivity
  have hΦ := gridPhi_gL_nonneg sys hL hθ Hunit χ hC
      (norm_nonneg (molecularH2StateMap eta g u₀))
    (norm_nonneg (H u₀)) (hs := ‖molecularH2StateMap eta g v₀‖) (hv := ‖H v₀‖)
  refine (grid_observable_error_sharp_gL sys L H hKernel Hunit hL hθ hPeriodic hC U h0 hgraph
      hderiv m hm hκ Ug
    hg0 hgcomm hgderiv (Real.sqrt (1 / (g * (m : ℝ))))
    (Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))) (Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))) hK₄
        (Real.sqrt_nonneg _) (hscale _ hKpos) (Real.sqrt_nonneg _) (hscale _ hK₂pos)
    (Real.sqrt_nonneg _) (hscale _ hK₄pos) u₀ v₀
    huv a χ hχ1 hχ2 hχ4 hreal (kZero g) (two_le_kZero g) (one_le_mul_kZero hg) ht).trans ?_
  exact grid_rate_arith_sharp (η := (eta : ℝ)) (mm := sys.maxMass)
    (Φ := gridPhi_gL sys L (tv R θ) Hunit χ ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖)
    (Ξ₁ := 2 * ‖H v₀‖ + 2 * relB_gL sys L (tv R θ) Hunit * ‖molecularH2StateMap eta g v₀‖)
    (C₀ := gLtailM sys L (tv R θ) Hunit
      (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
        2 * (2 * ‖H u₀‖ + 2 * relB_gL sys L (tv R θ) Hunit * ‖molecularH2StateMap eta g u₀‖))))
    (g := g) (t := t) (S0 := ‖molecularH2StateMap eta g u₀‖) (sT := supTail χ m)
    (Cχ := ∑' ν, ‖χ ν‖) (CO := ‖convOp (eta := eta) a χ‖) (τχ := τχ)
    (Zg := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (gLgamma L (tv R θ)))
    (m := m) (Ct := fun M => gLtailM sys L (tv R θ) Hunit M)
    (Nat.cast_nonneg eta) hM hΞ₁ (hCt _ hM₀) hg hm hK ht hS0 hCχ (norm_nonneg _) hτχ hZg hXa hW hCt
    hΦ

end Rates

end FreeBoundary
