import PlaneWave.Auxiliary.FluxSourceClauses

/-!
# Auxiliary claims, part 2: the log-free bounds of `lem:phi`

For the backward flow `φ(τ) = e^{i H_ret τ} A_p^E v` of the datum of a good state `v` with budget
`M`, `H_ret = H_N + D_K` with `D_K` symmetric and `‖D_K‖ ≤ C_Δ`, and `K = g n` with
`Λ = K/√2048 ≥ 1`:

* `phiSC_eq`: the weighted-flow constant is `φ_σ = c_σ K^{2σ - 1/2}` exactly, with
  `c_σ = C_fl(σ) C_{σ+1}^{1/2} (√2048)^{-(2σ - 1/2)}` independent of `n` (no logarithm);
* **`phi_logfree_high`** (eq:phi-norms and the bounds after it): `‖ℰ^σ φ(τ)‖ ≤ c_σ M K^{2σ - 1/2}`
  for `1/4 < σ ≤ 1`; in particular `‖ℰ^{1/2} φ‖ ≤ c M K^{1/2}`, `‖ℰ φ‖ ≤ c M K^{3/2}` and
  `‖ℰ^{3/4+ε} φ‖ ≤ c M K^{1+2ε}`;
* **`phi_logfree_low`**: `‖ℰ^α φ(τ)‖ ≤ c_{1/2}^{2α} M K^α` for `0 ≤ α ≤ 1/2`.

The constants depend on `C_Δ` and the system, not on `n` or `τ`.
-/

set_option autoImplicit false

open scoped InnerProductSpace
open PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- The log-free constant `c_σ = C_fl(σ) C_{σ+1}^{1/2} (√2048)^{-(2σ - 1/2)}`. -/
noncomputable def cphi (sys : CoulombSystem eta ν) (L Hunit CΔ σ : ℝ) : ℝ :=
  CflS sys L Hunit CΔ σ * Real.sqrt (momentConst eta (σ + 1)) *
    Real.sqrt 2048 ^ (-(2 * σ - 1 / 2))

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ}

lemma cphi_nonneg (Hunit : ℝ) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (σ : ℝ) : 0 ≤ cphi sys L Hunit CΔ σ := by
  unfold cphi
  have := CflS_nonneg sys (L := L) Hunit hCΔ σ
  positivity

include hL in
/-- `φ_σ = c_σ K^{2σ - 1/2}` (`Λ = K/√2048`), for `σ > 1/4`. -/
lemma phiSC_eq (Hunit CΔ : ℝ) {σ : ℝ} (hσ : 1 / 4 < σ) :
    phiSC sys L Hunit n CΔ σ = cphi sys L Hunit CΔ σ * Kc L n ^ (2 * σ - 1 / 2) := by
  have hg := gL_pos hL
  have hK0 : 0 ≤ Kc L n := by unfold Kc; positivity
  have hs : 0 < Real.sqrt 2048 := by positivity
  have hLam : Lam sys L n = Kc L n / Real.sqrt 2048 := by
    rw [FSAsymp.Lam_eq sys hL n]; unfold Kc; ring
  have hL0 : 0 ≤ Lam sys L n := by rw [hLam]; positivity
  have hM : 0 ≤ momentConst eta (σ + 1) := momentConst_nonneg eta (by linarith)
  unfold phiSC cphi
  rw [Real.sqrt_mul hM, Real.sqrt_eq_rpow (Lam sys L n ^ (4 * σ - 1)), ← Real.rpow_mul hL0, hLam,
    Real.div_rpow hK0 hs.le, Real.rpow_neg hs.le, div_eq_mul_inv,
    show (4 * σ - 1) * (1 / 2) = 2 * σ - 1 / 2 by ring]
  ring

include hL in
/-- **`lem:phi` with `A_p^E`, log-free, `1/4 < σ ≤ 1`** (eq:phi-norms and the bounds after it):
`‖ℰ^σ φ(τ)‖ ≤ c_σ M K^{2σ - 1/2}` uniformly in `τ`. -/
theorem phi_logfree_high (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) (hΛ : 1 ≤ Lam sys L n) (p₀ : Fin eta) {M : ℝ}
    (w : En eta n) (hw : IsGood sys L 1 M w) (τ : ℝ) {σ : ℝ} (hσ : 1 / 4 < σ) (hσ1 : σ ≤ 1) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) σ (retFlow sys L n hΔsym τ (datum sys L p₀ w))‖ ≤
      cphi sys L Hunit CΔ σ * M * Kc L n ^ (2 * σ - 1 / 2) := by
  have h := (flow_datum_bounds sys hL Hunit hPeriodic hΔsym hCΔ hΔb hΛ p₀ w hw τ hσ hσ1).2.2
  rw [phiSC_eq sys hL Hunit CΔ hσ] at h
  calc _ ≤ M * (cphi sys L Hunit CΔ σ * Kc L n ^ (2 * σ - 1 / 2)) := h
    _ = _ := by ring

include hL in
/-- **`lem:phi` with `A_p^E`, log-free, `0 ≤ α ≤ 1/2`**: `‖ℰ^α φ(τ)‖ ≤ c_{1/2}^{2α} M K^α`
uniformly in `τ`, by interpolation between `‖φ‖ ≤ M` and `‖ℰ^{1/2} φ‖ ≤ c_{1/2} M K^{1/2}`. -/
theorem phi_logfree_low (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) (hΛ : 1 ≤ Lam sys L n) (p₀ : Fin eta) {M : ℝ}
    (w : En eta n) (hw : IsGood sys L 1 M w) (τ : ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) α (retFlow sys L n hΔsym τ (datum sys L p₀ w))‖ ≤
      cphi sys L Hunit CΔ (1 / 2) ^ (2 * α) * M * Kc L n ^ α := by
  have h := flow_datum_interp sys hL Hunit hPeriodic hΔsym hCΔ hΔb hΛ p₀ w hw τ hα0 hα1
  have hg := gL_pos hL
  have hK0 : 0 ≤ Kc L n := by unfold Kc; positivity
  have hc := cphi_nonneg sys (L := L) Hunit hCΔ (1 / 2)
  rw [phiSC_eq sys hL Hunit CΔ (by norm_num), Real.mul_rpow hc (Real.rpow_nonneg hK0 _),
    ← Real.rpow_mul hK0, show (2 * (1 / 2 : ℝ) - 1 / 2) * (2 * α) = α by ring] at h
  calc _ ≤ M * (cphi sys L Hunit CΔ (1 / 2) ^ (2 * α) * Kc L n ^ α) := h
    _ = _ := by ring

end FSNormal
