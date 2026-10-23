import PlaneWave.KineticLog.GridSpectral

/-!
# Logarithmic kinetic bound, part 10: the grid consistency error

For the physical periodic grid Hamiltonian `G = H_grid` of a kernel of the full class
(`IsGridKernel`, eq:kernelclass) on the register of radius `2m`, the residual of the projected
exact Hamiltonian is

  `P' H u = G P' S u - C_g u`,  `C_g u = Δ P' S u - P' W (1 - P') u`  (`regCoeff_H_eq_gRes`),

with `Δ = R_wrap - D_drop` the difference of the grid and Galerkin kernels (`Delta`) and
`P' W (1 - P')` the exterior (Galerkin) source.  This file proves

* the eigen-coordinate consistency identity `(E_a + c - ν_k) ⟪e_a, P' b_k⟫ = ⟪e_a, C_g w_k⟫`
  (`grid_cons`);
* **`lem:kinetic-strong`**: `‖C_g u‖ ≤ Z_c (A(s₀, m)(τ (1 + 12 η m²) + X) + 52 m τ)
  + τ₂ η C_t (1 + g²)(1 + 12 η m²)/√(2K)` in terms of the shells `τ` of `P' S u` beyond
  `s₀ = ⌊m/4⌋`, its register weight `X` and its continuum tail `τ₂` beyond the cube `2m`
  (`norm_gRes_le`); the exterior part is bounded by the self-pairing `inner_galSource`
  (`norm_gSrc_le`);
* **`lem:kinetic-low`, grid form**: the doubly inverse-weighted consistency matrix on the low rows
  `E_a + c ≤ 2Λ` and the low exact columns `ν_k ≤ Λ` has norm at most `δ_raw`, the bilinear
  estimate `eq:kinetic-forms` (`Delta_form`) applied to the exact (`norm_tail_zv_shift_le`) and
  grid (`grid_low_tail`) low-energy tails (`grid_delta_raw`);
* **`lem:kinetic-leakage`, grid form**: the separated Sylvester block on the high rows,
  `‖Y‖ ≤ ‖F‖/(Λ - d)` with `‖F‖` bounded by the strong consistency (`grid_transfer_raw`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The residual -/

section Res

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)

/-- The exterior (Galerkin) source `u ↦ P' W (1 - P') u` on the register. -/
noncomputable def gSrcL (m : ℕ) : MolecularFourierH2 eta →L[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  regCoeff m ∘L coulombFourierPotentialH2 sys (2 * Real.pi / L) H ∘L
    (ContinuousLinearMap.id ℂ _ - lpTruncateCLM (fourierConfigCube eta (2 * m)))

omit [Fintype ν] in
lemma gSrcL_apply (m : ℕ) (u : MolecularFourierH2 eta) :
    gSrcL sys L H m u = regCoeff m (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
      (u - molecularH2Truncate (2 * m) u)) := rfl

/-- **The grid residual** `C_g u = Δ P' S u - P' W (1 - P') u`. -/
noncomputable def gResL (m : ℕ) (κ : Lat3 → ℝ) :
    MolecularFourierH2 eta →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  Delta eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
      κ ∘ₗ (regCoeff m ∘L molecularH2StateMap eta (2 * Real.pi / L)).toLinearMap -
    (gSrcL sys L H m).toLinearMap

lemma gResL_apply (m : ℕ) (κ : Lat3 → ℝ) (u : MolecularFourierH2 eta) :
    gResL sys L H m κ u =
      Delta eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
          κ (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u)) - gSrcL sys L H m u := rfl

variable (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (hL : 0 < L)

include hKernel hL in
/-- **The grid residual identity**: `P' H u = G P' S u - C_g u`. -/
lemma regCoeff_H_eq_gRes (m : ℕ) (κ : Lat3 → ℝ) (u : MolecularFourierH2 eta) :
    regCoeff m (H u) =
      Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L)
          (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u)) - gResL sys L H m κ u := by
  rw [regCoeff_H_eq_grid sys L H hKernel hL m κ u, gResL_apply, gSrcL_apply]
  abel

include hKernel hL in
/-- **The eigen-coordinate consistency identity**:
`(E_a + c - ν_k) ⟪e_a, P' b_k⟫ = ⟪e_a, C_g w_k⟫` for every exact eigen-decomposition. -/
lemma grid_cons (m : ℕ) {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x) {c : ℝ}
    (E : ExactEigen L H c) (a : GrIdx eta m) (k : E.ι) :
    ((grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a + c -
        E.nu k : ℝ) : ℂ) *
        ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a,
          regCoeff m (E.b k)⟫_ℂ =
      ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a,
        gResL sys L H m κ (E.w k)⟫_ℂ := by
  have h := regCoeff_H_eq_gRes sys L H hKernel hL m κ (E.w k)
  have hS : molecularH2StateMap eta (2 * Real.pi / L) (E.w k) = E.b k := E.sm_w k
  rw [E.H_w k, map_smul, hS] at h
  have h2 := congrArg (fun x => ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (2 * Real.pi / L) hκe a, x⟫_ℂ) h
  simp only [inner_smul_right, inner_sub_right, inner_grB_Hgrid] at h2
  push_cast at h2 ⊢
  linear_combination -h2

end Res

/-! ## Strong consistency -/

section Strong

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **The exterior part of the consistency error**: if `‖S u - P_{2m} S u‖ ≤ τ₂`, then
`‖P' W (1 - P') u‖ ≤ τ₂ η C_t(1) (1 + g²)(1 + 12 η m²)/√(2K)` (self-pairing through
`inner_galSource`, the generic potential tail and the register weight `‖wTot φ‖ ≤ (1 + 12 η m²)‖φ‖`
of the lift). -/
lemma norm_gSrc_le (m : ℕ) (hK1 : 1 ≤ gF L * (2 * m : ℕ)) (hK2 : 2 * gF L ≤ gF L * (2 * m : ℕ))
    (u : MolecularFourierH2 eta) {τ₂ : ℝ}
    (hτ₂ : ‖Sm eta L u - molecularH2Truncate (2 * m) (Sm eta L u)‖ ≤ τ₂) :
    ‖gSrcL sys L H m u‖ ≤ τ₂ * (eta * CtW sys L Hunit 1 *
      ((1 + gF L ^ 2) * (1 + 12 * eta * (m : ℝ) ^ 2))) / Real.sqrt (gF L * (2 * m : ℕ)) := by
  set x := gSrcL sys L H m u with hx
  set l := cubeLift (2 * Real.pi / L) (2 * m) ((regUnitary eta (2 * m)).symm x) with hl
  have hgF : gF L = 2 * Real.pi / L := rfl
  have hτ₂0 : 0 ≤ τ₂ := (norm_nonneg _).trans hτ₂
  have hCt : 0 ≤ CtW sys L Hunit 1 := CtW_nonneg sys hL Hunit zero_le_one
  have hc12 : (0 : ℝ) ≤ 1 + 12 * eta * (m : ℝ) ^ 2 := by positivity
  have hK0 : 0 < gF L * (2 * m : ℕ) := by linarith
  have hsK : 0 < Real.sqrt (gF L * (2 * m : ℕ)) := Real.sqrt_pos.mpr hK0
  set M := (1 + gF L ^ 2) * (1 + 12 * eta * (m : ℝ) ^ 2) * ‖x‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hlM : ‖l‖ ≤ M := by
    refine (norm_cubeLift_regUnitary_le (2 * Real.pi / L) x).trans ?_
    rw [hM, ← hgF, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_wTot_le_reg x) (by positivity)
  have hW := W_tail_le_h2 sys H hKernel Hunit hL hPeriodic (2 * m) hK1 hK2 l hM0 hlM
  have hpair := norm_inner_galSource_le sys L H hKernel m u x
  have hsq : ‖x‖ ^ 2 ≤ τ₂ * (eta * CtW sys L Hunit 1 * M / Real.sqrt (gF L * (2 * m : ℕ))) := by
    have e : ‖⟪x, x⟫_ℂ‖ = ‖x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [← e]
    refine hpair.trans (mul_le_mul hτ₂ ?_ (norm_nonneg _) hτ₂0)
    exact hW
  rcases (norm_nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have e2 : τ₂ * (eta * CtW sys L Hunit 1 * M / Real.sqrt (gF L * (2 * m : ℕ))) =
        τ₂ * (eta * CtW sys L Hunit 1 * ((1 + gF L ^ 2) * (1 + 12 * eta * (m : ℝ) ^ 2))) /
          Real.sqrt (gF L * (2 * m : ℕ)) * ‖x‖ := by
      rw [hM]
      field_simp
    rw [e2, sq] at hsq
    exact le_of_mul_le_mul_right hsq hpos

include hKernel hL hPeriodic in
/-- **`lem:kinetic-strong`** (grid residual): with the shells `τ` of `P' S u` beyond `s₀ = ⌊m/4⌋`,
its register weight `X` and the continuum tail `τ₂` of `S u` beyond the cube `2m`,
`‖C_g u‖ ≤ Z_c (A(s₀, m)(τ (1 + 12 η m²) + X) + 52 m τ)
  + τ₂ η C_t(1) (1 + g²)(1 + 12 η m²)/√(2K)`, uniformly over the kernel class. -/
theorem norm_gRes_le (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (hK1 : 1 ≤ gF L * (2 * m : ℕ)) (hK2 : 2 * gF L ≤ gF L * (2 * m : ℕ))
    (u : MolecularFourierH2 eta) {τ X τ₂ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : ∀ r, ‖maskOp (High (m / 4) r) (regCoeff m (Sm eta L u))‖ ≤ τ)
    (hX : ‖wMul wTot (regCoeff m (Sm eta L u))‖ ≤ X)
    (hτ₂ : ‖Sm eta L u - molecularH2Truncate (2 * m) (Sm eta L u)‖ ≤ τ₂) :
    ‖gResL sys L H m κ u‖ ≤
      Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) *
          (formA (m / 4) m * (τ * (1 + 12 * eta * (m : ℝ) ^ 2) + X) + 52 * m * τ) +
        τ₂ * (eta * CtW sys L Hunit 1 * ((1 + gF L ^ 2) * (1 + 12 * eta * (m : ℝ) ^ 2))) /
          Real.sqrt (gF L * (2 * m : ℕ)) := by
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hs : 1 ≤ m / 4 := by omega
  have hsm : m / 4 ≤ m := Nat.div_le_self m 4
  rw [gResL_apply]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_Delta_le (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData hγ hs hsm
      hκ.gridKernel _ hτ0 hτ hX
  · exact norm_gSrc_le sys H hKernel Hunit hL hPeriodic m hK1 hK2 u hτ₂

end Strong

/-! ## Low grid states as test vectors -/

section TestVectors

variable {m : ℕ} (P : RegParticles eta) (Dn : NucData ν) {κ : Lat3 → ℝ} (g : ℝ)
  (hκe : ∀ x, κ (-x) = κ x)

lemma lowW_conj (c Λ : ℝ) (a : GrIdx eta m) :
    conj (lowW P Dn g hκe c Λ a) = lowW P Dn g hκe c Λ a := by
  unfold lowW
  split_ifs <;> simp [map_inv₀, Complex.conj_ofReal]

lemma inner_grVL_left (c Λ : ℝ) (f : EuclideanSpace ℂ (GrIdx eta m))
    (X : EuclideanSpace ℂ (RCfg eta m)) :
    ⟪grVL P Dn g hκe c Λ f, X⟫_ℂ =
      ∑ a, conj (lowW P Dn g hκe c Λ a * f a) * ⟪grB P Dn g hκe a, X⟫_ℂ := by
  rw [← (grB P Dn g hκe).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← grVL_coord, inner_conj_symm]

end TestVectors

/-! ## The raw constants -/

section Constants

variable (sys : CoulombSystem eta ν) (L Hunit : ℝ)

/-- The exact low-energy shell coefficient at `s₀ = ⌊m/4⌋`: `C_abs/(K_s² √K_s)`, `K_s = g s₀`. -/
noncomputable def tuG (m : ℕ) : ℝ :=
  cAbs sys L Hunit / ((gF L * (m / 4 : ℕ)) ^ 2 * Real.sqrt (gF L * (m / 4 : ℕ)))

/-- The grid low-energy shell coefficient at `s₀`: `C_gt/(g² (s₀+1)² √s₀)`. -/
noncomputable def tvG (c : ℝ) (m : ℕ) : ℝ :=
  cGt (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
      (2 * Real.pi / L) c /
    ((2 * Real.pi / L) ^ 2 * (((m / 4 : ℕ) : ℝ) + 1) ^ 2 * Real.sqrt (m / 4 : ℕ))

/-- The register weight coefficient of the grid low states, `m̄ c_W`. -/
noncomputable def xvG (c : ℝ) : ℝ :=
  (regParticlesOf sys).maxMass * cWv (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (coulombCellAmplitude L) (2 * Real.pi / L) c

/-- The register weight coefficient of the exact low states, `(1 + 1/g²) m̄ c_z`. -/
noncomputable def xuG : ℝ := (1 + 1 / (2 * Real.pi / L) ^ 2) * (sys.maxMass * cZ sys L Hunit)

/-- The exact low-energy exterior coefficient at the cube `2m`: `C_abs/(K₂² √K₂)`. -/
noncomputable def t2G (m : ℕ) : ℝ :=
  cAbs sys L Hunit / ((gF L * (2 * m : ℕ)) ^ 2 * Real.sqrt (gF L * (2 * m : ℕ)))

/-- The exterior potential coefficient of the lift of the grid low states. -/
noncomputable def wvG (c : ℝ) (m : ℕ) : ℝ :=
  eta * CtW sys L Hunit 1 * ((1 + gF L ^ 2) * xvG sys L c) / Real.sqrt (gF L * (2 * m : ℕ))

/-- **The raw weighted-consistency constant** `δ_raw` (`grid_delta_raw`). -/
noncomputable def dRawG (c : ℝ) (m : ℕ) : ℝ :=
  Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) *
      (formA (m / 4) m * (tuG sys L Hunit m * xvG sys L c + tvG sys L c m * xuG sys L Hunit) +
        52 * m * (tvG sys L c m * tuG sys L Hunit m)) +
    t2G sys L Hunit m * wvG sys L Hunit c m

/-- **The raw strong-consistency constant** `F_raw` (`grid_transfer_raw`). -/
noncomputable def fRawG (m : ℕ) : ℝ :=
  Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) *
      (formA (m / 4) m * (tuG sys L Hunit m * (1 + 12 * eta * (m : ℝ) ^ 2) + xuG sys L Hunit) +
        52 * m * tuG sys L Hunit m) +
    t2G sys L Hunit m * (eta * CtW sys L Hunit 1 *
      ((1 + gF L ^ 2) * (1 + 12 * eta * (m : ℝ) ^ 2))) / Real.sqrt (gF L * (2 * m : ℕ))

variable {sys L Hunit}

lemma tuG_nonneg (hL : 0 < L) (m : ℕ) : 0 ≤ tuG sys L Hunit m := by
  unfold tuG
  have := cAbs_nonneg sys Hunit hL
  have := gF_pos hL
  positivity

lemma tvG_nonneg (hL : 0 < L) {c : ℝ} (hc : 0 ≤ c) (m : ℕ) : 0 ≤ tvG sys L c m := by
  unfold tvG
  have := cGt_nonneg (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
    (coulombCellAmplitude_pos hL).le hc
  positivity

lemma xvG_nonneg (hL : 0 < L) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ xvG sys L c := by
  unfold xvG
  have := cWv_nonneg (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
    (coulombCellAmplitude_pos hL).le hc
  have := (regParticlesOf sys).maxMass_pos
  positivity

lemma xuG_nonneg : 0 ≤ xuG sys L Hunit := by
  unfold xuG
  have := cZ_nonneg sys (L := L) Hunit
  have := sys.one_le_maxMass
  positivity

lemma t2G_nonneg (hL : 0 < L) (m : ℕ) : 0 ≤ t2G sys L Hunit m := by
  unfold t2G
  have := cAbs_nonneg sys Hunit hL
  have := gF_pos hL
  positivity

lemma wvG_nonneg (hL : 0 < L) {c : ℝ} (hc : 0 ≤ c) (m : ℕ) : 0 ≤ wvG sys L Hunit c m := by
  unfold wvG
  have := xvG_nonneg (sys := sys) hL hc
  have := CtW_nonneg sys hL Hunit zero_le_one
  positivity

lemma dRawG_nonneg (hL : 0 < L) {c : ℝ} (hc : 0 ≤ c) (m : ℕ) : 0 ≤ dRawG sys L Hunit c m := by
  unfold dRawG
  have := Zc_nonneg (P := regParticlesOf sys) (D := (posNucleiOf sys.nuclei).toNucData)
    (coulombCellAmplitude_pos hL).le
  have := formA_nonneg (m / 4) m
  have := tuG_nonneg (sys := sys) (Hunit := Hunit) hL m
  have := tvG_nonneg (sys := sys) hL hc m
  have := xvG_nonneg (sys := sys) hL hc
  have := xuG_nonneg (sys := sys) (L := L) (Hunit := Hunit)
  have := t2G_nonneg (sys := sys) (Hunit := Hunit) hL m
  have := wvG_nonneg (sys := sys) (Hunit := Hunit) hL hc m
  positivity

lemma fRawG_nonneg (hL : 0 < L) (m : ℕ) : 0 ≤ fRawG sys L Hunit m := by
  unfold fRawG
  have := Zc_nonneg (P := regParticlesOf sys) (D := (posNucleiOf sys.nuclei).toNucData)
    (coulombCellAmplitude_pos hL).le
  have := formA_nonneg (m / 4) m
  have := tuG_nonneg (sys := sys) (Hunit := Hunit) hL m
  have := xuG_nonneg (sys := sys) (L := L) (Hunit := Hunit)
  have := t2G_nonneg (sys := sys) (Hunit := Hunit) hL m
  have := CtW_nonneg sys hL Hunit zero_le_one
  have := gF_pos hL
  positivity

end Constants

/-! ## The consistency matrices -/

section Matrices

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (m : ℕ) {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x)

/-- The clipped shifted grid eigenvalues `min(E_a + c, 2Λ)`. -/
noncomputable def grLam (c Λ : ℝ) (a : GrIdx eta m) : ℝ :=
  min (grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a + c)
    (2 * Λ)

/-- **The low consistency block** `A_ak = 1_{E_a + c + d ≤ 2Λ} ⟪e_a, C_g w_k⟫`. -/
noncomputable def grA {c : ℝ} (E : ExactEigen L H c) (d Λ : ℝ) (s : Finset E.ι)
    (a : GrIdx eta m) (k : s) : ℂ :=
  if grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a +
      (c + d) ≤ 2 * Λ then
    ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a,
      gResL sys L H m κ (E.w k)⟫_ℂ
  else 0

/-- **The separated block** `Y_ak = 1_{E_a + c + d > 2Λ} ⟪e_a, P' b_k⟫/(ν_k + d)`. -/
noncomputable def grY {c : ℝ} (E : ExactEigen L H c) (d Λ : ℝ) (s : Finset E.ι)
    (a : GrIdx eta m) (k : s) : ℂ :=
  if grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a +
      (c + d) ≤ 2 * Λ then 0
  else ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a,
      regCoeff m (E.b k)⟫_ℂ / ((E.nu k + d : ℝ) : ℂ)

/-- Its Sylvester right-hand side `F_ak = 1_{E_a + c + d > 2Λ} ⟪e_a, C_g w_k⟫/(ν_k + d)`. -/
noncomputable def grF {c : ℝ} (E : ExactEigen L H c) (d Λ : ℝ) (s : Finset E.ι)
    (a : GrIdx eta m) (k : s) : ℂ :=
  if grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a +
      (c + d) ≤ 2 * Λ then 0
  else ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a,
      gResL sys L H m κ (E.w k)⟫_ℂ / ((E.nu k + d : ℝ) : ℂ)

lemma gResL_zv_shift {c : ℝ} (E : ExactEigen L H c) {d : ℝ} (hd : 0 ≤ d) (s : Finset E.ι)
    (f : EuclideanSpace ℂ s) :
    gResL sys L H m κ ((E.shift d hd).zv s f) =
      ∑ k : s, (f k / ((E.nu k + d : ℝ) : ℂ)) • gResL sys L H m κ (E.w k) := by
  unfold ExactEigen.zv
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

end Matrices

/-! ## `lem:kinetic-low` and `lem:kinetic-leakage` on the grid -/

section Bounds

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- The shells, the weight and the exterior tail of the register image `P' S z` of the shifted
exact low combination `z = Σ_k (f_k/(ν_k + d)) w_k`. -/
lemma exact_low_reg {c : ℝ} (E : ExactEigen L H c) (hcdef : c = shiftC sys L Hunit)
    {d : ℝ} (hd : 0 ≤ d) (m : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hKs1 : 1 ≤ gF L * (m / 4 : ℕ)) (hKs2 : 2 * gF L ≤ gF L * (m / 4 : ℕ))
    (hK1 : 1 ≤ gF L * (2 * m : ℕ)) (hK2 : 2 * gF L ≤ gF L * (2 * m : ℕ))
    (hΛs : Λ + c ≤ (gF L * (m / 4 : ℕ)) ^ 2 / (4 * sys.maxMass))
    (hΛ2 : Λ + c ≤ (gF L * (2 * m : ℕ)) ^ 2 / (4 * sys.maxMass))
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) (f : EuclideanSpace ℂ s) :
    (∀ r, ‖maskOp (High (m / 4) r) (regCoeff m (Sm eta L ((E.shift d hd).zv s f)))‖ ≤
        tuG sys L Hunit m * ‖f‖) ∧
      ‖wMul wTot (regCoeff m (Sm eta L ((E.shift d hd).zv s f)))‖ ≤ xuG sys L Hunit * ‖f‖ ∧
      ‖Sm eta L ((E.shift d hd).zv s f) -
          molecularH2Truncate (2 * m) (Sm eta L ((E.shift d hd).zv s f))‖ ≤
        t2G sys L Hunit m * ‖f‖ := by
  set z := (E.shift d hd).zv s f with hz
  have hg : 0 < 2 * Real.pi / L := gF_pos hL
  refine ⟨fun r => (norm_high_regCoeff_le_trunc (m / 4) r (Sm eta L z)).trans
    (norm_tail_zv_shift_le sys H hKernel Hunit hL hPeriodic E hcdef hd (m / 4) hKs1 hKs2 hΛ1 hΛs
      s hs f), ?_, norm_tail_zv_shift_le sys H hKernel Hunit hL hPeriodic E hcdef hd (2 * m) hK1
      hK2 hΛ1 hΛ2 s hs f⟩
  have h1 : ‖wMul wTot (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) z))‖ ≤
      (1 + 1 / (2 * Real.pi / L) ^ 2) * ‖z‖ := norm_wTot_regCoeff_stateMap_le hg z
  have h2 := h2norm_le sys L z
  have h3 : ‖molecularH2StateMap eta (2 * Real.pi / L) z‖ +
      2 * ‖coulombFourierKineticH2 sys (2 * Real.pi / L) z‖ ≤ cZ sys L Hunit * ‖f‖ :=
    zv_budget_shift sys H hKernel Hunit hL hPeriodic E hcdef hd s f
  have hm := sys.one_le_maxMass
  have h4 : ‖z‖ ≤ sys.maxMass * (cZ sys L Hunit * ‖f‖) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (by linarith))
  refine h1.trans ?_
  unfold xuG
  calc (1 + 1 / (2 * Real.pi / L) ^ 2) * ‖z‖
      ≤ (1 + 1 / (2 * Real.pi / L) ^ 2) * (sys.maxMass * (cZ sys L Hunit * ‖f‖)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

include hKernel hL hPeriodic in
/-- **`lem:kinetic-low`, grid form** (`eq:kinetic-forms` in the eigenbases): the doubly
inverse-weighted consistency matrix `A_ak/(λ_a μ_k)` on the low grid rows `λ_a = E_a + c + d ≤ 2Λ`
and the low exact columns `ν_k ≤ Λ` (`μ_k = ν_k + d`) has norm at most `δ_raw`. -/
theorem grid_delta_raw {c : ℝ} (E : ExactEigen L H c) (hcdef : c = shiftC sys L Hunit)
    {d : ℝ} (hd : 0 ≤ d) (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (hc1 : ∀ a : GrIdx eta m, 1 ≤ grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) hκ.even a + (c + d))
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hKs1 : 1 ≤ gF L * (m / 4 : ℕ)) (hKs2 : 2 * gF L ≤ gF L * (m / 4 : ℕ))
    (hK1 : 1 ≤ gF L * (2 * m : ℕ)) (hK2 : 2 * gF L ≤ gF L * (2 * m : ℕ))
    (hΛs : Λ + c ≤ (gF L * (m / 4 : ℕ)) ^ 2 / (4 * sys.maxMass))
    (hΛ2 : Λ + c ≤ (gF L * (2 * m : ℕ)) ^ 2 / (4 * sys.maxMass))
    (hΛg : 4 * (regParticlesOf sys).maxMass * (2 * Λ + cGr (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) (2 * Real.pi / L)) ≤
        (2 * Real.pi / L) ^ 2 * (((m / 4 : ℕ) : ℝ) + 1) ^ 2)
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) (f : EuclideanSpace ℂ s) :
    ‖mop (wmat (grLam sys L m hκ.even (c + d) Λ) (fun k : s => E.nu k + d)
        (grA sys L H m hκ.even E d Λ s)) f‖ ≤ dRawG sys L Hunit (c + d) m * ‖f‖ := by
  classical
  have hg : 0 < 2 * Real.pi / L := gF_pos hL
  have hγ : 0 ≤ (coulombCellAmplitude L) := (coulombCellAmplitude_pos hL).le
  have hc : 2 ≤ c := hcdef ▸ two_le_shiftC sys L Hunit
  have hcd : 0 ≤ c + d := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hs0 : 2 ≤ m / 4 := by omega
  have hs1 : 1 ≤ m / 4 := by omega
  have hsm : m / 4 ≤ m := Nat.div_le_self m 4
  have hs2m : m / 4 ≤ 2 * m := by omega
  set y := mop (wmat (grLam sys L m hκ.even (c + d) Λ) (fun k : s => E.nu k + d)
    (grA sys L H m hκ.even E d Λ s)) f with hydef
  set z := (E.shift d hd).zv s f with hzdef
  set R := gResL sys L H m κ z with hRdef
  -- the coordinates of `y`
  have hy : ∀ a, y a =
      lowW (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκ.even
        (c + d) Λ a *
      ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκ.even a,
        R⟫_ℂ := by
    intro a
    rw [hydef, mop_apply, hRdef, hzdef, gResL_zv_shift sys L H m E hd s f, inner_sum]
    simp only [wmat, grA, grLam, lowW, inner_smul_right]
    split_ifs with ha
    · rw [min_eq_left ha, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 :
          ((grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
          (2 * Real.pi / L) hκ.even a + (c + d) : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by linarith [hc1 a])
      have h2 : ((E.nu k + d : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by linarith [E.nu_pos k])
      field_simp
    · simp
  -- the dual vector
  set v :=
      grVL (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκ.even
      (c + d) Λ y with hvdef
  have hyy : ((‖y‖ ^ 2 : ℝ) : ℂ) = ⟪v, R⟫_ℂ := by
    rw [hvdef, inner_grVL_left, norm_sq_eucl]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, lowW_conj,
        mul_comm (lowW (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (2 * Real.pi / L) hκ.even (c + d) Λ a), mul_assoc, ← hy a,
      Complex.conj_mul']
  -- the exact low-state bounds
  obtain ⟨hτu, hXu, hτ₂⟩ := exact_low_reg sys H hKernel Hunit hL hPeriodic E hcdef hd m hΛ1 hKs1
    hKs2 hK1 hK2 hΛs hΛ2 s hs f
  set u := regCoeff m (Sm eta L z) with hudef
  -- the grid low-state bounds
  have hτv : ∀ r, ‖maskOp (High (m / 4) r) v‖ ≤ tvG sys L (c + d) m * ‖y‖ := fun r =>
    grid_low_tail (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (2 * Real.pi / L) hκ.even hγ hκ.bound hg hcd hΛ0 hc1 (m / 4) hs0 hs2m r hΛg y
  have hXv : ‖wMul wTot v‖ ≤ xvG sys L (c + d) * ‖y‖ := by
    refine (norm_wMul_wTot_le (regParticlesOf sys) v).trans ?_
    unfold xvG
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (norm_wM_grVL_le (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
          (2 * Real.pi / L) hκ.even hγ hκ.bound hg Λ hcd hc1 y) (regParticlesOf sys).maxMass_pos.le
  have htu0 := tuG_nonneg (sys := sys) (Hunit := Hunit) hL m
  have htv0 := tvG_nonneg (sys := sys) hL hcd m
  have hxv0 := xvG_nonneg (sys := sys) hL hcd
  have hxu0 := xuG_nonneg (sys := sys) (L := L) (Hunit := Hunit)
  have ht20 := t2G_nonneg (sys := sys) (Hunit := Hunit) hL m
  have hwv0 := wvG_nonneg (sys := sys) (Hunit := Hunit) hL hcd m
  have hf0 := norm_nonneg f
  have hy0 := norm_nonneg y
  -- the dropped and wrapped part
  have hΔ :
      ‖⟪v, Delta eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) κ u⟫_ℂ‖ ≤
      Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) *
      (formA (m / 4) m * ((tuG sys L Hunit m * ‖f‖) * (xvG sys L (c + d) * ‖y‖) +
        (tvG sys L (c + d) m * ‖y‖) * (xuG sys L Hunit * ‖f‖)) +
        52 * m * ((tvG sys L (c + d) m * ‖y‖) * (tuG sys L Hunit m * ‖f‖))) := by
    refine (Delta_form (P := (regParticlesOf sys)) (D := (posNucleiOf sys.nuclei).toNucData)
      hγ hs1 hsm hκ.gridKernel u v (by positivity) (by positivity) hτu hτv).trans ?_
    have hZ := Zc_nonneg (P := (regParticlesOf sys)) (D := (posNucleiOf sys.nuclei).toNucData) hγ
    have hA := formA_nonneg (m / 4) m
    gcongr
  -- the exterior part
  have hsrc : ‖⟪v, gSrcL sys L H m z⟫_ℂ‖ ≤
      (t2G sys L Hunit m * ‖f‖) * (wvG sys L Hunit (c + d) m * ‖y‖) := by
    rw [← inner_conj_symm, RCLike.norm_conj, gSrcL_apply]
    refine (norm_inner_galSource_le sys L H hKernel m z v).trans
      (mul_le_mul hτ₂ ?_ (norm_nonneg _) (by positivity))
    have hl := norm_cubeLift_regUnitary_le (2 * Real.pi / L) v
    have hM : ‖cubeLift (2 * Real.pi / L) (2 * m) ((regUnitary eta (2 * m)).symm v)‖ ≤
        (1 + gF L ^ 2) * (xvG sys L (c + d) * ‖y‖) :=
      hl.trans (mul_le_mul_of_nonneg_left hXv (by positivity))
    have hW := W_tail_le_h2 sys H hKernel Hunit hL hPeriodic (2 * m) hK1 hK2 _ (by positivity) hM
    refine hW.trans (le_of_eq ?_)
    unfold wvG
    ring
  have hsplit : ⟪v, R⟫_ℂ =
      ⟪v, Delta eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) κ u⟫_ℂ - ⟪v, gSrcL sys L H m z⟫_ℂ := by
    rw [hRdef, gResL_apply, inner_sub_right]
    rfl
  have hy2 : ‖y‖ ^ 2 ≤ dRawG sys L Hunit (c + d) m * ‖f‖ * ‖y‖ := by
    have h1 : ‖y‖ ^ 2 = ‖⟪v, R⟫_ℂ‖ := by
      have h := congrArg norm hyy
      rwa [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h
    rw [h1, hsplit]
    refine (norm_sub_le _ _).trans ((add_le_add hΔ hsrc).trans (le_of_eq ?_))
    unfold dRawG
    ring
  rcases hy0.eq_or_lt with h0 | hpos
  · rw [← h0]
    have := dRawG_nonneg (sys := sys) (Hunit := Hunit) hL hcd m
    positivity
  · rw [sq, ← mul_comm ‖y‖] at hy2
    rw [mul_comm] at hy2
    nlinarith

include hKernel hL hPeriodic in
/-- **`lem:kinetic-leakage`, grid form**: the separated block on the high grid rows
`E_a + c + d > 2Λ` satisfies `‖Y‖ ≤ F_raw/(Λ - d)`: it solves the Sylvester equation
`λ_a Y_ak - Y_ak μ_k = F_ak` with `λ_a > 2Λ ≥ Λ + d ≥ μ_k`, and `‖F‖ ≤ ‖C_g z‖ ≤ F_raw`
(`norm_gRes_le`). -/
theorem grid_transfer_raw {c : ℝ} (E : ExactEigen L H c) (hcdef : c = shiftC sys L Hunit)
    {d : ℝ} (hd : 0 ≤ d) (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) (hdΛ : d < Λ)
    (hKs1 : 1 ≤ gF L * (m / 4 : ℕ)) (hKs2 : 2 * gF L ≤ gF L * (m / 4 : ℕ))
    (hK1 : 1 ≤ gF L * (2 * m : ℕ)) (hK2 : 2 * gF L ≤ gF L * (2 * m : ℕ))
    (hΛs : Λ + c ≤ (gF L * (m / 4 : ℕ)) ^ 2 / (4 * sys.maxMass))
    (hΛ2 : Λ + c ≤ (gF L * (2 * m : ℕ)) ^ 2 / (4 * sys.maxMass))
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) :
    ‖mop (grY sys L H m hκ.even E d Λ s)‖ ≤ fRawG sys L Hunit m / (Λ - d) := by
  classical
  have hc : 2 ≤ c := hcdef ▸ two_le_shiftC sys L Hunit
  -- the Sylvester equation
  have hrow : ∀ a (k : s), grY sys L H m hκ.even E d Λ s a k ≠ 0 →
      2 * Λ ≤
          grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
          (2 * Real.pi / L) hκ.even a + (c + d) := by
    intro a k hne
    by_contra hlt
    exact hne (by simp only [grY]; rw [if_pos (not_le.mp hlt).le])
  have hcol : ∀ a (k : s), grY sys L H m hκ.even E d Λ s a k ≠ 0 → |E.nu k + d| ≤ Λ + d := by
    intro a k _
    rw [abs_of_pos (by linarith [E.nu_pos k])]
    linarith [hs k k.2]
  have hsyl : ∀ a (k : s),
      ((grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκ.even a +
        (c + d) : ℝ) : ℂ) * grY sys L H m hκ.even E d Λ s a k -
        grY sys L H m hκ.even E d Λ s a k * ((E.nu k + d : ℝ) : ℂ) =
          grF sys L H m hκ.even E d Λ s a k := by
    intro a k
    simp only [grY, grF]
    split_ifs with ha
    · ring
    · rw [← grid_cons sys L H hKernel hL m hκ.even E a k]
      have h2 : ((E.nu k + d : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by linarith [E.nu_pos k])
      field_simp
      push_cast
      ring
  have hS := norm_sylvester_le
    (fun a => grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
      hκ.even a + (c + d)) (fun k : s => E.nu k + d)
    (grY sys L H m hκ.even E d Λ s) (grF sys L H m hκ.even E d Λ s) (α := 2 * Λ) (β := Λ + d)
    (by linarith) (by linarith) hrow hcol hsyl
  -- the right-hand side
  have hF : ‖mop (grF sys L H m hκ.even E d Λ s)‖ ≤ fRawG sys L Hunit m := by
    refine norm_mop_le (fRawG_nonneg (sys := sys) (Hunit := Hunit) hL m) fun f => ?_
    set z := (E.shift d hd).zv s f with hzdef
    have hcoord : ∀ a, ‖(mop (grF sys L H m hκ.even E d Λ s) f) a‖ ≤
        1 *
            ‖((grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            (2 * Real.pi / L) hκ.even).repr (gResL sys L H m κ z)) a‖ := by
      intro a
      rw [mop_apply, OrthonormalBasis.repr_apply_apply, hzdef, gResL_zv_shift sys L H m E hd s f,
        inner_sum, one_mul]
      simp only [grF, inner_smul_right]
      split_ifs with ha
      · simp
      · refine le_of_eq (congrArg norm (Finset.sum_congr rfl fun k _ => ?_))
        ring
    have h1 := norm_le_of_coord zero_le_one hcoord
    rw [one_mul, LinearIsometryEquiv.norm_map] at h1
    refine h1.trans ?_
    obtain ⟨hτu, hXu, hτ₂⟩ := exact_low_reg sys H hKernel Hunit hL hPeriodic E hcdef hd m hΛ1 hKs1
      hKs2 hK1 hK2 hΛs hΛ2 s hs f
    have htu0 := tuG_nonneg (sys := sys) (Hunit := Hunit) hL m
    have h2 := norm_gRes_le sys H hKernel Hunit hL hPeriodic m hm hκ hK1 hK2 z
      (by positivity) hτu hXu hτ₂
    refine h2.trans (le_of_eq ?_)
    unfold fRawG
    field_simp
  calc ‖mop (grY sys L H m hκ.even E d Λ s)‖
      ≤ ‖mop (grF sys L H m hκ.even E d Λ s)‖ / (2 * Λ - (Λ + d)) := hS
    _ ≤ fRawG sys L Hunit m / (Λ - d) := by
        rw [show 2 * Λ - (Λ + d) = Λ - d by ring]
        exact div_le_div_of_nonneg_right hF (by linarith)

end Bounds

end KineticLog
