import PlaneWave.KineticLog.OpenGridSpectral

/-!
# Logarithmic kinetic bound, part 19: the grid consistency error of the isolated cell

The grid residual of the range-cut cell Hamiltonian `H_L` on the register of radius `2m`,
`P' H_L u = G P' S u - C_g u`, `C_g u = Δ_L P' S u - P' W (1 - P') u`
(`regCoeff_H_eq_gRes_gL`), with
`Δ_L = R_wrap - D_drop` the difference of the grid and Galerkin kernels for the reference `ĝ_L`
(`FreeBoundary.DeltaGL`) and the exterior source `P' W (1 - P')`.  In the physical weight
`w_g^tot = 1 + g² Σ_b |n_b|²` (`FreeBoundary.wTotPh`) and with `L`-free constants:

* `norm_DeltaGL_le`: `‖Δ_L u‖ ≤ Z_c (A_g(s, m)(τ (1 + 12 η K²) + X) + 52 m τ)` (`Delta_formP`);
* `norm_gSrc_gL`, **`norm_gRes_gL`** (`lem:kinetic-strong` for `g_L`);
* **`grid_delta_raw_gL`** (`lem:kinetic-low`, grid form) and **`grid_transfer_raw_gL`**
  (`lem:kinetic-leakage`, grid form), with the raw constants `dRawU`, `fRawU`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Register weights -/

section Weights

variable {m : ℕ}

lemma wTotPh_le_reg (g : ℝ) (q : RCfg eta m) :
    FreeBoundary.wTotPh g q ≤ 1 + 12 * eta * (g * m) ^ 2 := by
  have h : ∑ a, nsq (gl (q a)) ≤ ∑ _a : Fin eta, 12 * (m : ℝ) ^ 2 :=
    Finset.sum_le_sum fun a _ => nsq_gl_le (q a)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold FreeBoundary.wTotPh
  have := mul_le_mul_of_nonneg_left h (sq_nonneg g)
  nlinarith

/-- `‖w_g^tot x‖ ≤ (1 + 12 η K²) ‖x‖`, `K = g m`. -/
lemma norm_wTotPh_le_reg (g : ℝ) (x : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (FreeBoundary.wTotPh g) x‖ ≤ (1 + 12 * eta * (g * m) ^ 2) * ‖x‖ := by
  have hc : (0 : ℝ) ≤ 1 + 12 * eta * (g * m) ^ 2 := by positivity
  refine (norm_le_of_pointwise (Y := ((1 + 12 * eta * (g * m) ^ 2 : ℝ) : ℂ) • x)
    fun q => ?_).trans ?_
  · rw [wMul_apply, PiLp.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (le_trans zero_le_one
        (FreeBoundary.wTotPh_ge_one g q)), Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_right (wTotPh_le_reg g q) (norm_nonneg _)
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]

end Weights

/-! ## The residual of `H_L` on the register -/

section Res

variable (sys : CoulombSystem eta ν) (L : ℝ) {R : ℝ} {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hL : 0 < L) (hθ : FreeBoundary.Profile R θ)

/-- **The grid residual of `H_L`** `C_g u = Δ_L P' S u - P' W (1 - P') u`. -/
noncomputable def gResGL (m : ℕ) (κ : Lat3 → ℝ) :
    MolecularFourierH2 eta →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  FreeBoundary.DeltaGL sys L hL hθ m κ ∘ₗ
      (regCoeff m ∘L molecularH2StateMap eta (2 * Real.pi / L)).toLinearMap -
    (gSrcL sys L H m).toLinearMap

lemma gResGL_apply (m : ℕ) (κ : Lat3 → ℝ) (u : MolecularFourierH2 eta) :
    gResGL sys L H hL hθ m κ u =
      FreeBoundary.DeltaGL sys L hL hθ m κ
          (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u)) -
        gSrcL sys L H m u := rfl

variable (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (FreeBoundary.gLlatHam sys L θ) N u q)

include hKernel in
/-- **The grid residual identity of `H_L`**: `P' H_L u = G P' S u - C_g u`. -/
lemma regCoeff_H_eq_gRes_gL (m : ℕ) (κ : Lat3 → ℝ) (u : MolecularFourierH2 eta) :
    regCoeff m (H u) =
      Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L)
          (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u)) -
              gResGL sys L H hL hθ m κ u := by
  rw [FreeBoundary.regCoeff_H_eq_grid_gL sys L H hKernel hL hθ m κ u, gResGL_apply, gSrcL_apply]
  abel

include hKernel in
/-- **The eigen-coordinate consistency identity of `H_L`**:
`(E_a + c - ν_k) ⟪e_a, P' b_k⟫ = ⟪e_a, C_g w_k⟫`. -/
lemma grid_cons_gL (m : ℕ) {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x) {c : ℝ}
    (E : ExactEigen L H c) (a : GrIdx eta m) (k : E.ι) :
    ((grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a + c -
        E.nu k : ℝ) : ℂ) *
        ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a,
          regCoeff m (E.b k)⟫_ℂ =
      ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a,
        gResGL sys L H hL hθ m κ (E.w k)⟫_ℂ := by
  have h := regCoeff_H_eq_gRes_gL sys L H hL hθ hKernel m κ (E.w k)
  have hS : molecularH2StateMap eta (2 * Real.pi / L) (E.w k) = E.b k := E.sm_w k
  rw [E.H_w k, map_smul, hS] at h
  have h2 := congrArg (fun x => ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (2 * Real.pi / L) hκe a, x⟫_ℂ) h
  simp only [inner_smul_right, inner_sub_right, inner_grB_Hgrid] at h2
  push_cast at h2 ⊢
  linear_combination -h2

/-- **The low consistency block of `H_L`** `A_ak = 1_{E_a + c + d ≤ 2Λ} ⟪e_a, C_g w_k⟫`. -/
noncomputable def grAGL (m : ℕ) {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x) {c : ℝ}
    (E : ExactEigen L H c) (d Λ : ℝ) (s : Finset E.ι) (a : GrIdx eta m) (k : s) : ℂ :=
  if grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a +
      (c + d) ≤ 2 * Λ then
    ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a,
      gResGL sys L H hL hθ m κ (E.w k)⟫_ℂ
  else 0

/-- Its Sylvester right-hand side `F_ak = 1_{E_a + c + d > 2Λ} ⟪e_a, C_g w_k⟫/(ν_k + d)`. -/
noncomputable def grFGL (m : ℕ) {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x) {c : ℝ}
    (E : ExactEigen L H c) (d Λ : ℝ) (s : Finset E.ι) (a : GrIdx eta m) (k : s) : ℂ :=
  if grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a +
      (c + d) ≤ 2 * Λ then 0
  else ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a,
      gResGL sys L H hL hθ m κ (E.w k)⟫_ℂ / ((E.nu k + d : ℝ) : ℂ)

lemma gResGL_zv_shift (m : ℕ) (κ : Lat3 → ℝ) {c : ℝ} (E : ExactEigen L H c) {d : ℝ}
    (hd : 0 ≤ d) (s : Finset E.ι) (f : EuclideanSpace ℂ s) :
    gResGL sys L H hL hθ m κ ((E.shift d hd).zv s f) =
      ∑ k : s, (f k / ((E.nu k + d : ℝ) : ℂ)) • gResGL sys L H hL hθ m κ (E.w k) := by
  unfold ExactEigen.zv
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

end Res

/-! ## The raw constants, uniform in `L` -/

section Constants

variable (sys : CoulombSystem eta ν) (L V Hunit : ℝ)

/-- The bare coupling `Z_c(γ_L)` of the grid core (`m̄ Z_c = z g`). -/
noncomputable def ZcL : ℝ :=
  PlaneWaveGridG.Zc (PlaneWaveGridG.regParticlesOfG sys)
    (PlaneWaveGridG.posNucleiOfG sys.nuclei).toNucData (PlaneWaveGridG.gLgamma L V)

/-- The exact low-energy shell coefficient at `s₀ = ⌊m/4⌋`: `C_abs^U/(K_s² √K_s)`. -/
noncomputable def tuU (m : ℕ) : ℝ :=
  cAbsU sys V Hunit / ((gF L * (m / 4 : ℕ)) ^ 2 * Real.sqrt (gF L * (m / 4 : ℕ)))

/-- The grid low-energy shell coefficient at `s₀`: `C_gt^U/((g(s₀+1))² √(g s₀))`. -/
noncomputable def tvU (c : ℝ) (m : ℕ) : ℝ :=
  cGtU sys V c / ((2 * Real.pi / L * (((m / 4 : ℕ) : ℝ) + 1)) ^ 2 *
    Real.sqrt (2 * Real.pi / L * (m / 4 : ℕ)))

/-- The weight coefficient of the grid low states, `m̄ c_W^U`. -/
noncomputable def xvU (c : ℝ) : ℝ := sys.maxMass * cWvU sys V c

/-- The weight coefficient of the exact low states, `m̄ c_z^U`. -/
noncomputable def xuU : ℝ := sys.maxMass * cZU sys V Hunit

/-- The exact low-energy exterior coefficient at the cube `2m`: `C_abs^U/(K₂² √K₂)`. -/
noncomputable def t2U (m : ℕ) : ℝ :=
  cAbsU sys V Hunit / ((gF L * (2 * m : ℕ)) ^ 2 * Real.sqrt (gF L * (2 * m : ℕ)))

/-- The exterior potential coefficient of the lift of the grid low states. -/
noncomputable def wvU (c : ℝ) (m : ℕ) : ℝ :=
  eta * FreeBoundary.gLtailMU sys V Hunit 1 * xvU sys V c / Real.sqrt (gF L * (2 * m : ℕ))

/-- **The raw weighted-consistency constant** `δ_raw` of `H_L`. -/
noncomputable def dRawU (c : ℝ) (m : ℕ) : ℝ :=
  ZcL sys L V * (PlaneWaveGridG.formAP (2 * Real.pi / L) (m / 4) m *
      (tuU sys L V Hunit m * xvU sys V c + tvU sys L V c m * xuU sys V Hunit) +
      52 * m * (tvU sys L V c m * tuU sys L V Hunit m)) +
    t2U sys L V Hunit m * wvU sys L V Hunit c m

/-- **The raw strong-consistency constant** `F_raw` of `H_L`. -/
noncomputable def fRawU (m : ℕ) : ℝ :=
  ZcL sys L V * (PlaneWaveGridG.formAP (2 * Real.pi / L) (m / 4) m *
      (tuU sys L V Hunit m * (1 + 12 * eta * (2 * Real.pi / L * m) ^ 2) + xuU sys V Hunit) +
      52 * m * tuU sys L V Hunit m) +
    t2U sys L V Hunit m * (eta * FreeBoundary.gLtailMU sys V Hunit 1 *
      (1 + 12 * eta * (2 * Real.pi / L * m) ^ 2)) / Real.sqrt (gF L * (2 * m : ℕ))

variable {sys L V Hunit}

lemma ZcL_nonneg (hL : 0 < L) (hV : 0 ≤ V) : 0 ≤ ZcL sys L V :=
  PlaneWaveGridG.Zc_nonneg (PlaneWaveGridG.gLgamma_pos hL hV).le

lemma tuU_nonneg (hL : 0 < L) (hV : 0 ≤ V) (hH : 0 ≤ Hunit) (m : ℕ) : 0 ≤ tuU sys L V Hunit m := by
  unfold tuU
  have := cAbsU_nonneg (sys := sys) hV hH
  have := gF_pos hL
  positivity

lemma tvU_nonneg (hL : 0 < L) (hV : 0 ≤ V) {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    0 ≤ tvU sys L V c m := by
  unfold tvU
  have := cGtU_nonneg sys hV hc
  have : 0 < 2 * Real.pi / L := by positivity
  positivity

lemma xvU_nonneg (hV : 0 ≤ V) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ xvU sys V c := by
  unfold xvU
  have := cWvU_nonneg sys hV hc
  have := sys.maxMass_pos
  positivity

lemma xuU_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ xuU sys V Hunit := by
  unfold xuU
  have := cZU_nonneg (sys := sys) hV hH
  have := sys.maxMass_pos
  positivity

lemma t2U_nonneg (hL : 0 < L) (hV : 0 ≤ V) (hH : 0 ≤ Hunit) (m : ℕ) : 0 ≤ t2U sys L V Hunit m := by
  unfold t2U
  have := cAbsU_nonneg (sys := sys) hV hH
  have := gF_pos hL
  positivity

lemma wvU_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    0 ≤ wvU sys L V Hunit c m := by
  unfold wvU
  have := xvU_nonneg (sys := sys) hV hc
  have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
  positivity

lemma dRawU_nonneg (hL : 0 < L) (hV : 0 ≤ V) (hH : 0 ≤ Hunit) {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    0 ≤ dRawU sys L V Hunit c m := by
  unfold dRawU
  have := ZcL_nonneg (sys := sys) hL hV
  have := PlaneWaveGridG.formAP_nonneg (2 * Real.pi / L) (m / 4) m
  have := tuU_nonneg (sys := sys) hL hV hH m
  have := tvU_nonneg (sys := sys) hL hV hc m
  have := xvU_nonneg (sys := sys) hV hc
  have := xuU_nonneg (sys := sys) hV hH
  have := t2U_nonneg (sys := sys) hL hV hH m
  have := wvU_nonneg (sys := sys) (L := L) hV hH hc m
  positivity

lemma fRawU_nonneg (hL : 0 < L) (hV : 0 ≤ V) (hH : 0 ≤ Hunit) (m : ℕ) :
    0 ≤ fRawU sys L V Hunit m := by
  unfold fRawU
  have := ZcL_nonneg (sys := sys) hL hV
  have := PlaneWaveGridG.formAP_nonneg (2 * Real.pi / L) (m / 4) m
  have := tuU_nonneg (sys := sys) hL hV hH m
  have := xuU_nonneg (sys := sys) hV hH
  have := t2U_nonneg (sys := sys) hL hV hH m
  have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
  have := gF_pos hL
  positivity

end Constants

/-! ## Strong consistency of `H_L` -/

section Strong

variable (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (FreeBoundary.gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 2 * Real.pi ≤ L) (hθ : FreeBoundary.Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hH : 0 ≤ Hunit)

include hKernel hL hθ hPeriodic hH in
/-- **Generic potential tail of `H_L` with an `H²` budget** (uniform in `L ≥ 2π`): for `K = g n ≥ 1`
and `‖u‖ ≤ M`, `‖(1 - P_n) W u‖ ≤ η C_tail^U(1) M / √K`. -/
theorem W_tail_le_h2_gL (n : ℕ) (hK1 : 1 ≤ gF L * n) (u : MolecularFourierH2 eta) {M : ℝ}
    (hM : 0 ≤ M) (hu : ‖u‖ ≤ M) :
    ‖Wp sys L H u - molecularH2Truncate n (Wp sys L H u)‖ ≤
      eta * FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit 1 * M / Real.sqrt (gF L * n) := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  have hρ : Real.sqrt (1 / K) ^ 2 * K = 1 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have ht : ∀ a, ‖tailMask (gF L) K a (Wp sys L H u)‖ ≤
      FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit M * Real.sqrt (1 / K) := fun a =>
    (FreeBoundary.potential_tail_le_gL sys L H hKernel Hunit hL0 hθ hPeriodic a K
      (Real.sqrt (1 / K)) M hK1 (Real.sqrt_nonneg _) hρ hM u hu).trans
      (mul_le_mul_of_nonneg_right (FreeBoundary.gLtailM_le_U sys hL hV hH hM) (Real.sqrt_nonneg _))
  have hsq : Real.sqrt (1 / K) = 1 / Real.sqrt K := by
    rw [Real.sqrt_div' 1 hK0.le, Real.sqrt_one]
  calc ‖Wp sys L H u - molecularH2Truncate n (Wp sys L H u)‖
      ≤ ∑ a : Fin eta, ‖tailMask (gF L) K a (Wp sys L H u)‖ :=
        PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL0) n _
    _ ≤ ∑ _a : Fin eta, FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit M *
          Real.sqrt (1 / K) := Finset.sum_le_sum fun a _ => ht a
    _ = eta * FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit 1 * M / Real.sqrt K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, gLtailMU_linear,
          hsq]
        ring

include hKernel hL hθ hPeriodic hH in
/-- **The exterior part of the consistency error of `H_L`**: if `‖S u - P_{2m} S u‖ ≤ τ₂`, then
`‖P' W (1 - P') u‖ ≤ τ₂ η C_tail^U (1 + 12 η K²)/√(2K)`. -/
lemma norm_gSrc_gL (m : ℕ) (hK1 : 1 ≤ gF L * (2 * m : ℕ))
    (u : MolecularFourierH2 eta) {τ₂ : ℝ}
    (hτ₂ : ‖Sm eta L u - molecularH2Truncate (2 * m) (Sm eta L u)‖ ≤ τ₂) :
    ‖gSrcL sys L H m u‖ ≤ τ₂ * (eta * FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit 1 *
      (1 + 12 * eta * (2 * Real.pi / L * m) ^ 2)) / Real.sqrt (gF L * (2 * m : ℕ)) := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  set x := gSrcL sys L H m u with hx
  set l := cubeLift (2 * Real.pi / L) (2 * m) ((regUnitary eta (2 * m)).symm x) with hl
  have hτ₂0 : 0 ≤ τ₂ := (norm_nonneg _).trans hτ₂
  have hCt : 0 ≤ FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit 1 :=
    gLtailMU_nonneg hV hH zero_le_one
  have hK0 : 0 < gF L * (2 * m : ℕ) := by linarith
  have hsK : 0 < Real.sqrt (gF L * (2 * m : ℕ)) := Real.sqrt_pos.mpr hK0
  set M := (1 + 12 * eta * (2 * Real.pi / L * m) ^ 2) * ‖x‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hlM : ‖l‖ ≤ M := by
    rw [hl, FreeBoundary.norm_cubeLift_regUnitary_eqP]
    exact norm_wTotPh_le_reg (2 * Real.pi / L) x
  have hW := W_tail_le_h2_gL sys H hKernel Hunit hL hθ hPeriodic hH (2 * m) hK1 l hM0 hlM
  have hpair := FreeBoundary.norm_inner_galSource_le_gL sys L H hKernel hθ m u x
  have hsq : ‖x‖ ^ 2 ≤ τ₂ * (eta * FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit 1 * M /
      Real.sqrt (gF L * (2 * m : ℕ))) := by
    have e : ‖⟪x, x⟫_ℂ‖ = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [← e]
    exact hpair.trans (mul_le_mul hτ₂ hW (norm_nonneg _) hτ₂0)
  rcases (norm_nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have e2 : τ₂ * (eta * FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit 1 * M /
        Real.sqrt (gF L * (2 * m : ℕ))) =
        τ₂ * (eta * FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit 1 *
          (1 + 12 * eta * (2 * Real.pi / L * m) ^ 2)) / Real.sqrt (gF L * (2 * m : ℕ)) * ‖x‖ := by
      rw [hM]
      field_simp
    rw [e2, sq] at hsq
    exact le_of_mul_le_mul_right hsq hpos

include hL hθ in
/-- **The grid difference of `g_L` in norm** (physical weight): if the shells of `u` beyond
`s₀ = ⌊m/4⌋` are at most `τ` and `‖w_g^tot u‖ ≤ X`, then
`‖Δ_L u‖ ≤ Z_c (A_g(s₀, m)(τ (1 + 12 η K²) + X) + 52 m τ)`. -/
lemma norm_DeltaGL_le (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ))
      (PlaneWaveGridG.gLref L θ (FreeBoundary.tv R θ)) m κ)
    (u : EuclideanSpace ℂ (RCfg eta m)) {τ X : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : ∀ r, ‖maskOp (High (m / 4) r) u‖ ≤ τ)
    (hX : ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L)) u‖ ≤ X) :
    ‖FreeBoundary.DeltaGL sys L (pos_of_two_pi_le hL) hθ m κ u‖ ≤
      ZcL sys L (FreeBoundary.tv R θ) * (PlaneWaveGridG.formAP (2 * Real.pi / L) (m / 4) m *
        (τ * (1 + 12 * eta * (2 * Real.pi / L * m) ^ 2) + X) + 52 * m * τ) := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hγ : 0 ≤ PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ) :=
    (PlaneWaveGridG.gLgamma_pos hL0 hV).le
  have hs1 : 1 ≤ m / 4 := by omega
  have hsm : m / 4 ≤ m := Nat.div_le_self m 4
  set x := FreeBoundary.DeltaGL sys L hL0 hθ m κ u with hxdef
  have hZ : 0 ≤ ZcL sys L (FreeBoundary.tv R θ) := ZcL_nonneg hL0 hV
  have hA := PlaneWaveGridG.formAP_nonneg (2 * Real.pi / L) (m / 4) m
  have hX0 : 0 ≤ X := (norm_nonneg _).trans hX
  have hc : (0 : ℝ) ≤ 1 + 12 * eta * (2 * Real.pi / L * m) ^ 2 := by positivity
  set Rb := ZcL sys L (FreeBoundary.tv R θ) * (PlaneWaveGridG.formAP (2 * Real.pi / L) (m / 4) m *
      (τ * (1 + 12 * eta * (2 * Real.pi / L * m) ^ 2) + X) + 52 * m * τ) with hRdef
  have hR0 : 0 ≤ Rb := by positivity
  rcases (norm_nonneg x).eq_or_lt with h | h
  · rw [← h]
    exact hR0
  have hf0 := PlaneWaveGridG.Delta_formP (P := PlaneWaveGridG.regParticlesOfG sys)
    (D := PlaneWaveGridG.gLNucData sys hL0 hθ) hg hγ hs1 hsm hκ.gridKernel u x hτ0 (norm_nonneg x)
    hτ (fun r => PlaneWaveGridG.norm_maskOp_le _ _)
  have hf : ‖⟪x, x⟫_ℂ‖ ≤ ZcL sys L (FreeBoundary.tv R θ) *
      (PlaneWaveGridG.formAP (2 * Real.pi / L) (m / 4) m *
        (τ * ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L)) x‖ +
          ‖x‖ * ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L)) u‖) + 52 * m * (‖x‖ * τ)) := hf0
  have hself : ‖⟪x, x⟫_ℂ‖ = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hf' : ‖x‖ ^ 2 ≤ ‖x‖ * Rb := by
    rw [hself] at hf
    refine hf.trans ?_
    have h2 : τ * ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L)) x‖ ≤
        τ * ((1 + 12 * eta * (2 * Real.pi / L * m) ^ 2) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_wTotPh_le_reg _ x) hτ0
    have h3 : ‖x‖ * ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L)) u‖ ≤ ‖x‖ * X :=
      mul_le_mul_of_nonneg_left hX (norm_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left (add_le_add h2 h3) hA
    have h5 := mul_le_mul_of_nonneg_left
      (add_le_add h4 (le_refl (52 * (m : ℝ) * (‖x‖ * τ)))) hZ
    refine h5.trans (le_of_eq ?_)
    rw [hRdef]
    ring
  have := mul_le_mul_of_nonneg_left (le_refl ‖x‖) (norm_nonneg x)
  nlinarith

include hKernel hL hθ hPeriodic hH in
/-- **`lem:kinetic-strong` for `H_L`** (uniform in `L ≥ 2π`): with the shells `τ` of `P' S u`
beyond `s₀`, its weight `X ≥ ‖w_g^tot P' S u‖` and the continuum tail `τ₂` beyond the cube `2m`,
`‖C_g u‖ ≤ Z_c (A_g(τ(1 + 12 η K²) + X) + 52 m τ) + τ₂ η C_tail^U (1 + 12 η K²)/√(2K)`. -/
theorem norm_gRes_gL (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ))
      (PlaneWaveGridG.gLref L θ (FreeBoundary.tv R θ)) m κ)
    (hK1 : 1 ≤ gF L * (2 * m : ℕ))
    (u : MolecularFourierH2 eta) {τ X τ₂ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : ∀ r, ‖maskOp (High (m / 4) r) (regCoeff m (Sm eta L u))‖ ≤ τ)
    (hX : ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L)) (regCoeff m (Sm eta L u))‖ ≤ X)
    (hτ₂ : ‖Sm eta L u - molecularH2Truncate (2 * m) (Sm eta L u)‖ ≤ τ₂) :
    ‖gResGL sys L H (pos_of_two_pi_le hL) hθ m κ u‖ ≤
      ZcL sys L (FreeBoundary.tv R θ) * (PlaneWaveGridG.formAP (2 * Real.pi / L) (m / 4) m *
          (τ * (1 + 12 * eta * (2 * Real.pi / L * m) ^ 2) + X) + 52 * m * τ) +
        τ₂ * (eta * FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit 1 *
          (1 + 12 * eta * (2 * Real.pi / L * m) ^ 2)) / Real.sqrt (gF L * (2 * m : ℕ)) := by
  rw [gResGL_apply]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_DeltaGL_le sys hL hθ m hm hκ _ hτ0 hτ hX
  · exact norm_gSrc_gL sys H hKernel Hunit hL hθ hPeriodic hH m hK1 u hτ₂

end Strong

/-! ## `lem:kinetic-low` and `lem:kinetic-leakage` on the grid of the cell -/

section Bounds

variable (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (FreeBoundary.gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 2 * Real.pi ≤ L) (hθ : FreeBoundary.Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hH : 0 ≤ Hunit)

include hKernel hL hθ hPeriodic hH in
/-- The shells, the weight and the exterior tail of the register image `P' S z` of the shifted
exact low combination `z = Σ_k (f_k/(ν_k + d)) w_k` of `H_L`. -/
lemma exact_low_reg_gL {c : ℝ} (E : ExactEigen L H c)
    (hcdef : c = cU sys (FreeBoundary.tv R θ) Hunit)
    {d : ℝ} (hd : 0 ≤ d) (m : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hKs1 : 1 ≤ gF L * (m / 4 : ℕ)) (hK1 : 1 ≤ gF L * (2 * m : ℕ))
    (hΛs : Λ + c ≤ (gF L * (m / 4 : ℕ)) ^ 2 / (4 * sys.maxMass))
    (hΛ2 : Λ + c ≤ (gF L * (2 * m : ℕ)) ^ 2 / (4 * sys.maxMass))
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) (f : EuclideanSpace ℂ s) :
    (∀ r, ‖maskOp (High (m / 4) r) (regCoeff m (Sm eta L ((E.shift d hd).zv s f)))‖ ≤
        tuU sys L (FreeBoundary.tv R θ) Hunit m * ‖f‖) ∧
      ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L))
          (regCoeff m (Sm eta L ((E.shift d hd).zv s f)))‖ ≤
        xuU sys (FreeBoundary.tv R θ) Hunit * ‖f‖ ∧
      ‖Sm eta L ((E.shift d hd).zv s f) -
          molecularH2Truncate (2 * m) (Sm eta L ((E.shift d hd).zv s f))‖ ≤
        t2U sys L (FreeBoundary.tv R θ) Hunit m * ‖f‖ := by
  set z := (E.shift d hd).zv s f with hz
  refine ⟨fun r => (norm_high_regCoeff_le_trunc (m / 4) r (Sm eta L z)).trans
    (norm_tail_zv_shift_gL sys H hKernel Hunit hL hθ hPeriodic hH E hcdef hd (m / 4) hKs1 hΛ1 hΛs
      s hs f), ?_, norm_tail_zv_shift_gL sys H hKernel Hunit hL hθ hPeriodic hH E hcdef hd (2 * m)
      hK1 hΛ1 hΛ2 s hs f⟩
  have h1 : ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L))
      (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) z))‖ ≤ ‖z‖ :=
    FreeBoundary.norm_wTotPh_regCoeff_stateMap_le _ z
  have h2 := h2norm_le sys L z
  have h3 : ‖molecularH2StateMap eta (2 * Real.pi / L) z‖ +
      2 * ‖coulombFourierKineticH2 sys (2 * Real.pi / L) z‖ ≤
        cZU sys (FreeBoundary.tv R θ) Hunit * ‖f‖ :=
    zv_budget_shift_gL sys H hKernel Hunit hL hθ hPeriodic hH E hcdef hd s f
  have hm := sys.one_le_maxMass
  have h4 : ‖z‖ ≤ sys.maxMass * (cZU sys (FreeBoundary.tv R θ) Hunit * ‖f‖) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (by linarith))
  refine h1.trans (h4.trans (le_of_eq ?_))
  unfold xuU
  ring

include hKernel hL hθ hPeriodic hH in
/-- **`lem:kinetic-low` for the grid of the cell** (uniform in `L ≥ 2π`): the doubly
inverse-weighted consistency matrix `A_ak/(λ_a μ_k)` of `H_L` on the low grid rows
`λ_a = E_a + c + d ≤ 2Λ` and the low exact columns `ν_k ≤ Λ` has norm at most `δ_raw`. -/
theorem grid_delta_raw_gL {c : ℝ} (E : ExactEigen L H c)
    (hcdef : c = cU sys (FreeBoundary.tv R θ) Hunit)
    {d : ℝ} (hd : 0 ≤ d) (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ))
      (PlaneWaveGridG.gLref L θ (FreeBoundary.tv R θ)) m κ)
    (hc1 : ∀ a : GrIdx eta m, 1 ≤ grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) hκ.even a + (c + d))
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hKs1 : 1 ≤ gF L * (m / 4 : ℕ)) (hK1 : 1 ≤ gF L * (2 * m : ℕ))
    (hΛs : Λ + c ≤ (gF L * (m / 4 : ℕ)) ^ 2 / (4 * sys.maxMass))
    (hΛ2 : Λ + c ≤ (gF L * (2 * m : ℕ)) ^ 2 / (4 * sys.maxMass))
    (hΛg : 4 * sys.maxMass * (2 * Λ + cGrU sys (FreeBoundary.tv R θ)) ≤
        (2 * Real.pi / L * (((m / 4 : ℕ) : ℝ) + 1)) ^ 2)
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) (f : EuclideanSpace ℂ s) :
    ‖mop (wmat (grLam sys L m hκ.even (c + d) Λ) (fun k : s => E.nu k + d)
        (grAGL sys L H (pos_of_two_pi_le hL) hθ m hκ.even E d Λ s)) f‖ ≤
      dRawU sys L (FreeBoundary.tv R θ) Hunit (c + d) m * ‖f‖ := by
  classical
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hγ : 0 ≤ PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ) :=
    (PlaneWaveGridG.gLgamma_pos hL0 hV).le
  have hc : 2 ≤ c := hcdef ▸ two_le_cU sys _ Hunit
  have hcd : 0 ≤ c + d := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hs0 : 2 ≤ m / 4 := by omega
  have hs1 : 1 ≤ m / 4 := by omega
  have hsm : m / 4 ≤ m := Nat.div_le_self m 4
  have hs2m : m / 4 ≤ 2 * m := by omega
  have hκb : ∀ x, |κ x| ≤ PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ) * coul x :=
    fun x => hκ.bound x
  set y := mop (wmat (grLam sys L m hκ.even (c + d) Λ) (fun k : s => E.nu k + d)
    (grAGL sys L H hL0 hθ m hκ.even E d Λ s)) f with hydef
  set z := (E.shift d hd).zv s f with hzdef
  set Rv := gResGL sys L H hL0 hθ m κ z with hRdef
  have hy : ∀ a, y a = lowW (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) hκ.even (c + d) Λ a * ⟪grB (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκ.even a, Rv⟫_ℂ := by
    intro a
    rw [hydef, mop_apply, hRdef, hzdef, gResGL_zv_shift sys L H hL0 hθ m κ E hd s f, inner_sum]
    simp only [wmat, grAGL, grLam, lowW, inner_smul_right]
    split_ifs with ha
    · rw [min_eq_left ha, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : ((grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
          hκ.even a + (c + d) : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by linarith [hc1 a])
      have h2 : ((E.nu k + d : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by linarith [E.nu_pos k])
      field_simp
    · simp
  set v := grVL (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
    hκ.even (c + d) Λ y with hvdef
  have hyy : ((‖y‖ ^ 2 : ℝ) : ℂ) = ⟪v, Rv⟫_ℂ := by
    rw [hvdef, inner_grVL_left, norm_sq_eucl]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, lowW_conj, mul_comm (lowW (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) hκ.even (c + d) Λ a), mul_assoc, ← hy a, Complex.conj_mul']
  obtain ⟨hτu, hXu, hτ₂⟩ := exact_low_reg_gL sys H hKernel Hunit hL hθ hPeriodic hH E hcdef hd m
    hΛ1 hKs1 hK1 hΛs hΛ2 s hs f
  set u := regCoeff m (Sm eta L z) with hudef
  have hgs : 1 ≤ 2 * Real.pi / L * ((m / 4 : ℕ) : ℝ) := hKs1
  have hτv : ∀ r, ‖maskOp (High (m / 4) r) v‖ ≤ tvU sys L (FreeBoundary.tv R θ) (c + d) m * ‖y‖ :=
    fun r => grid_low_tail_U sys hL hV hκ.even hκb hcd hΛ0 hc1 (m / 4) hs0 hs2m r hgs hΛg y
  have hXv : ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L)) v‖ ≤
      xvU sys (FreeBoundary.tv R θ) (c + d) * ‖y‖ := by
    refine (FreeBoundary.norm_wTotPh_le (regParticlesOf sys) (2 * Real.pi / L) v).trans ?_
    unfold xvU
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (norm_wPhys_grVL_le sys hL hV hκ.even hκb Λ hcd hc1 y) sys.maxMass_pos.le
  have htu0 := tuU_nonneg (sys := sys) hL0 hV hH m
  have htv0 := tvU_nonneg (sys := sys) hL0 hV hcd m
  have hxv0 := xvU_nonneg (sys := sys) hV hcd
  have hxu0 := xuU_nonneg (sys := sys) hV hH
  have ht20 := t2U_nonneg (sys := sys) hL0 hV hH m
  have hwv0 := wvU_nonneg (sys := sys) (L := L) hV hH hcd m
  have hf0 := norm_nonneg f
  have hy0 := norm_nonneg y
  -- the dropped and wrapped part
  have hΔ : ‖⟪v, FreeBoundary.DeltaGL sys L hL0 hθ m κ u⟫_ℂ‖ ≤
      ZcL sys L (FreeBoundary.tv R θ) * (PlaneWaveGridG.formAP (2 * Real.pi / L) (m / 4) m *
        ((tuU sys L (FreeBoundary.tv R θ) Hunit m * ‖f‖) *
          (xvU sys (FreeBoundary.tv R θ) (c + d) * ‖y‖) +
        (tvU sys L (FreeBoundary.tv R θ) (c + d) m * ‖y‖) *
          (xuU sys (FreeBoundary.tv R θ) Hunit * ‖f‖)) +
        52 * m * ((tvU sys L (FreeBoundary.tv R θ) (c + d) m * ‖y‖) *
          (tuU sys L (FreeBoundary.tv R θ) Hunit m * ‖f‖))) := by
    have hD0 := PlaneWaveGridG.Delta_formP (P := PlaneWaveGridG.regParticlesOfG sys)
      (D := PlaneWaveGridG.gLNucData sys hL0 hθ) hg hγ hs1 hsm hκ.gridKernel u v
      (by positivity) (by positivity) hτu hτv
    have hD : ‖⟪v, FreeBoundary.DeltaGL sys L hL0 hθ m κ u⟫_ℂ‖ ≤
        ZcL sys L (FreeBoundary.tv R θ) * (PlaneWaveGridG.formAP (2 * Real.pi / L) (m / 4) m *
          ((tuU sys L (FreeBoundary.tv R θ) Hunit m * ‖f‖) *
            ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L)) v‖ +
          (tvU sys L (FreeBoundary.tv R θ) (c + d) m * ‖y‖) *
            ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L)) u‖) +
          52 * m * ((tvU sys L (FreeBoundary.tv R θ) (c + d) m * ‖y‖) *
            (tuU sys L (FreeBoundary.tv R θ) Hunit m * ‖f‖))) := hD0
    refine hD.trans ?_
    have hZ := ZcL_nonneg (sys := sys) hL0 hV
    have hA := PlaneWaveGridG.formAP_nonneg (2 * Real.pi / L) (m / 4) m
    gcongr
  -- the exterior part
  have hsrc : ‖⟪v, gSrcL sys L H m z⟫_ℂ‖ ≤
      (t2U sys L (FreeBoundary.tv R θ) Hunit m * ‖f‖) *
        (wvU sys L (FreeBoundary.tv R θ) Hunit (c + d) m * ‖y‖) := by
    rw [← inner_conj_symm, RCLike.norm_conj, gSrcL_apply]
    refine (FreeBoundary.norm_inner_galSource_le_gL sys L H hKernel hθ m z v).trans
      (mul_le_mul hτ₂ ?_ (norm_nonneg _) (by positivity))
    have hM : ‖cubeLift (2 * Real.pi / L) (2 * m) ((regUnitary eta (2 * m)).symm v)‖ ≤
        xvU sys (FreeBoundary.tv R θ) (c + d) * ‖y‖ := by
      rw [FreeBoundary.norm_cubeLift_regUnitary_eqP]
      exact hXv
    have hW := W_tail_le_h2_gL sys H hKernel Hunit hL hθ hPeriodic hH (2 * m) hK1 _
      (by positivity) hM
    refine hW.trans (le_of_eq ?_)
    unfold wvU
    ring
  have hsplit : ⟪v, Rv⟫_ℂ = ⟪v, FreeBoundary.DeltaGL sys L hL0 hθ m κ u⟫_ℂ -
      ⟪v, gSrcL sys L H m z⟫_ℂ := by
    rw [hRdef, gResGL_apply, inner_sub_right]
    rfl
  have hy2 : ‖y‖ ^ 2 ≤ dRawU sys L (FreeBoundary.tv R θ) Hunit (c + d) m * ‖f‖ * ‖y‖ := by
    have h1 : ‖y‖ ^ 2 = ‖⟪v, Rv⟫_ℂ‖ := by
      have h := congrArg norm hyy
      rwa [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h
    rw [h1, hsplit]
    refine (norm_sub_le _ _).trans ((add_le_add hΔ hsrc).trans (le_of_eq ?_))
    unfold dRawU
    ring
  rcases hy0.eq_or_lt with h0 | hpos
  · rw [← h0]
    have := dRawU_nonneg (sys := sys) hL0 hV hH hcd m
    positivity
  · rw [sq] at hy2
    have h3 : ‖y‖ * ‖y‖ ≤ (dRawU sys L (FreeBoundary.tv R θ) Hunit (c + d) m * ‖f‖) * ‖y‖ := by
      linarith
    exact le_of_mul_le_mul_right h3 hpos

include hKernel hL hθ hPeriodic hH in
/-- **`lem:kinetic-leakage` for the grid of the cell** (uniform in `L ≥ 2π`): the separated block
on the high grid rows satisfies `‖Y‖ ≤ F_raw/(Λ - d)`. -/
theorem grid_transfer_raw_gL {c : ℝ} (E : ExactEigen L H c)
    (hcdef : c = cU sys (FreeBoundary.tv R θ) Hunit)
    {d : ℝ} (hd : 0 ≤ d) (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ))
      (PlaneWaveGridG.gLref L θ (FreeBoundary.tv R θ)) m κ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) (hdΛ : d < Λ)
    (hKs1 : 1 ≤ gF L * (m / 4 : ℕ)) (hK1 : 1 ≤ gF L * (2 * m : ℕ))
    (hΛs : Λ + c ≤ (gF L * (m / 4 : ℕ)) ^ 2 / (4 * sys.maxMass))
    (hΛ2 : Λ + c ≤ (gF L * (2 * m : ℕ)) ^ 2 / (4 * sys.maxMass))
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) :
    ‖mop (grY sys L H m hκ.even E d Λ s)‖ ≤
        fRawU sys L (FreeBoundary.tv R θ) Hunit m / (Λ - d) := by
  classical
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  have hc : 2 ≤ c := hcdef ▸ two_le_cU sys _ Hunit
  have hrow : ∀ a (k : s), grY sys L H m hκ.even E d Λ s a k ≠ 0 →
      2 * Λ ≤ grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
        hκ.even a + (c + d) := by
    intro a k hne
    by_contra hlt
    exact hne (by simp only [grY]; rw [if_pos (not_le.mp hlt).le])
  have hcol : ∀ a (k : s), grY sys L H m hκ.even E d Λ s a k ≠ 0 → |E.nu k + d| ≤ Λ + d := by
    intro a k _
    rw [abs_of_pos (by linarith [E.nu_pos k])]
    linarith [hs k k.2]
  have hsyl : ∀ a (k : s), ((grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) hκ.even a + (c + d) : ℝ) : ℂ) *
      grY sys L H m hκ.even E d Λ s a k - grY sys L H m hκ.even E d Λ s a k *
        ((E.nu k + d : ℝ) : ℂ) = grFGL sys L H hL0 hθ m hκ.even E d Λ s a k := by
    intro a k
    simp only [grY, grFGL]
    split_ifs with ha
    · ring
    · rw [← grid_cons_gL sys L H hL0 hθ hKernel m hκ.even E a k]
      have h2 : ((E.nu k + d : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by linarith [E.nu_pos k])
      field_simp
      push_cast
      ring
  have hS := norm_sylvester_le (fun a => grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (2 * Real.pi / L) hκ.even a + (c + d)) (fun k : s => E.nu k + d)
    (grY sys L H m hκ.even E d Λ s) (grFGL sys L H hL0 hθ m hκ.even E d Λ s) (α := 2 * Λ)
    (β := Λ + d) (by linarith) (by linarith) hrow hcol hsyl
  have hF : ‖mop (grFGL sys L H hL0 hθ m hκ.even E d Λ s)‖ ≤
      fRawU sys L (FreeBoundary.tv R θ) Hunit m := by
    refine norm_mop_le (fRawU_nonneg (sys := sys) hL0 hV hH m) fun f => ?_
    set z := (E.shift d hd).zv s f with hzdef
    have hcoord : ∀ a, ‖(mop (grFGL sys L H hL0 hθ m hκ.even E d Λ s) f) a‖ ≤
        1 * ‖((grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
          hκ.even).repr (gResGL sys L H hL0 hθ m κ z)) a‖ := by
      intro a
      rw [mop_apply, OrthonormalBasis.repr_apply_apply, hzdef,
        gResGL_zv_shift sys L H hL0 hθ m κ E hd s f, inner_sum, one_mul]
      simp only [grFGL, inner_smul_right]
      split_ifs with ha
      · simp
      · refine le_of_eq (congrArg norm (Finset.sum_congr rfl fun k _ => ?_))
        ring
    have h1 := norm_le_of_coord zero_le_one hcoord
    rw [one_mul, LinearIsometryEquiv.norm_map] at h1
    refine h1.trans ?_
    obtain ⟨hτu, hXu, hτ₂⟩ := exact_low_reg_gL sys H hKernel Hunit hL hθ hPeriodic hH E hcdef hd m
      hΛ1 hKs1 hK1 hΛs hΛ2 s hs f
    have htu0 := tuU_nonneg (sys := sys) hL0 hV hH m
    have h2 := norm_gRes_gL sys H hKernel Hunit hL hθ hPeriodic hH m hm hκ hK1 z
      (by positivity) hτu hXu hτ₂
    refine h2.trans (le_of_eq ?_)
    unfold fRawU
    field_simp
  calc ‖mop (grY sys L H m hκ.even E d Λ s)‖
      ≤ ‖mop (grFGL sys L H hL0 hθ m hκ.even E d Λ s)‖ / (2 * Λ - (Λ + d)) := hS
    _ ≤ fRawU sys L (FreeBoundary.tv R θ) Hunit m / (Λ - d) := by
        rw [show 2 * Λ - (Λ + d) = Λ - d by ring]
        exact div_le_div_of_nonneg_right hF (by linarith)

end Bounds

end KineticLog
