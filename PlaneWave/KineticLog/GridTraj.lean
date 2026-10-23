import PlaneWave.KineticLog.GridShells

/-!
# Logarithmic kinetic bound, part 13: the shells of the exact and grid trajectories

The layer-cake estimate `norm_wM_regKin_shells` needs, for the two trajectories on the register,
a first weighted bound `‖W φ‖ ≤ B₀` and the shells `‖1_{|q_p|_∞ > T} W φ‖ ≤ B/√T`:

* **exact trajectory** `φ = P' ψ(t)` (`exact_traj_shells`): from the good-state budget of the
  exact trajectory (`traj_good`: `‖S w‖ + ‖T w‖ ≤ c_tr Ξ`, Euclidean tails `c_tr Ξ λ^{-5/2}` and
  `c_tr Ξ λ^{-1/2}` of `S w` and `T w` beyond every `λ ≥ 1`);
* **grid trajectory** `φ = e^{-iGt} P' ψ₀` (`grid_traj_shells`): from the regularity of grid
  trajectories (`RegHam.flow_le_weight`) and the kinetic tails of the grid trajectory
  (`lem:grid-tails`, `grid_kin_tail_euclid`) for `max(1, 4g) ≤ λ ≤ K`, with the data constant
  `D_g = gridTailConst ≤ G₄ Ξ` (`gridTailConst_le`), uniformly over the kernel class.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The data constant of the grid tails is linear in the data -/

section TailConst

variable (sys : CoulombSystem eta ν) (L Hunit Blow Cs Bker : ℝ)

lemma gridTailConst_linear (s0 hu hs hv : ℝ) :
    gridTailConst sys L Hunit Blow Cs Bker s0 hu hs hv =
      s0 * gridTailConst sys L Hunit Blow Cs Bker 1 0 0 0 +
        hu * gridTailConst sys L Hunit Blow Cs Bker 0 1 0 0 +
        hs * gridTailConst sys L Hunit Blow Cs Bker 0 0 1 0 +
        hv * gridTailConst sys L Hunit Blow Cs Bker 0 0 0 1 := by
  set C1 := finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker 1 with hC1
  have hCt : ∀ M, finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M = C1 * M := by
    intro M
    rw [hC1]
    unfold finiteCoulombPhysicalTailConstant finiteCoulombTailConstant
    ring
  simp only [gridTailConst, hCt]
  ring

/-- The sum `G₄` of the four unit values of `gridTailConst`. -/
noncomputable def gtcSum : ℝ :=
  gridTailConst sys L Hunit Blow Cs Bker 1 0 0 0 + gridTailConst sys L Hunit Blow Cs Bker 0 1 0 0 +
    gridTailConst sys L Hunit Blow Cs Bker 0 0 1 0 + gridTailConst sys L Hunit Blow Cs Bker 0 0 0 1

variable {sys L Hunit Blow Cs Bker}

lemma gtcSum_nonneg (hL : 0 < L) (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker) :
    0 ≤ gtcSum sys L Hunit Blow Cs Bker := by
  unfold gtcSum
  have h1 := gridTailConst_nonneg sys hL Hunit hC (s0 := 1) (hu := 0) (hs := 0) (hv := 0) hBlow hCs
    hBker zero_le_one le_rfl le_rfl le_rfl
  have h2 := gridTailConst_nonneg sys hL Hunit hC (s0 := 0) (hu := 1) (hs := 0) (hv := 0) hBlow hCs
    hBker le_rfl zero_le_one le_rfl le_rfl
  have h3 := gridTailConst_nonneg sys hL Hunit hC (s0 := 0) (hu := 0) (hs := 1) (hv := 0) hBlow hCs
    hBker le_rfl le_rfl zero_le_one le_rfl
  have h4 := gridTailConst_nonneg sys hL Hunit hC (s0 := 0) (hu := 0) (hs := 0) (hv := 1) hBlow hCs
    hBker le_rfl le_rfl le_rfl zero_le_one
  linarith

/-- `D_g ≤ G₄ X` when all four data norms are in `[0, X]`. -/
lemma gridTailConst_le (hL : 0 < L) (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker) {s0 hu hs hv X : ℝ}
    (_h0 : 0 ≤ s0) (_h1 : 0 ≤ hu) (_h2 : 0 ≤ hs) (_h3 : 0 ≤ hv)
    (h0X : s0 ≤ X) (h1X : hu ≤ X) (h2X : hs ≤ X) (h3X : hv ≤ X) :
    gridTailConst sys L Hunit Blow Cs Bker s0 hu hs hv ≤ gtcSum sys L Hunit Blow Cs Bker * X := by
  rw [gridTailConst_linear]
  unfold gtcSum
  have e1 := gridTailConst_nonneg sys hL Hunit hC (s0 := 1) (hu := 0) (hs := 0) (hv := 0) hBlow hCs
    hBker zero_le_one le_rfl le_rfl le_rfl
  have e2 := gridTailConst_nonneg sys hL Hunit hC (s0 := 0) (hu := 1) (hs := 0) (hv := 0) hBlow hCs
    hBker le_rfl zero_le_one le_rfl le_rfl
  have e3 := gridTailConst_nonneg sys hL Hunit hC (s0 := 0) (hu := 0) (hs := 1) (hv := 0) hBlow hCs
    hBker le_rfl le_rfl zero_le_one le_rfl
  have e4 := gridTailConst_nonneg sys hL Hunit hC (s0 := 0) (hu := 0) (hs := 0) (hv := 1) hBlow hCs
    hBker le_rfl le_rfl le_rfl zero_le_one
  nlinarith [mul_le_mul_of_nonneg_right h0X e1, mul_le_mul_of_nonneg_right h1X e2,
    mul_le_mul_of_nonneg_right h2X e3, mul_le_mul_of_nonneg_right h3X e4]

end TailConst

/-! ## The weight of a register image -/

section Weight

omit [Fintype ν] in
/-- `W P' S y = P' (S y + (2/g²) T y)` on the register. -/
lemma wM_regCoeff_eq (sys : CoulombSystem eta ν) {g : ℝ} (hg : 0 < g) {m : ℕ}
    (y : MolecularFourierH2 eta) :
    wMul (wM (regParticlesOf sys)) (regCoeff m (molecularH2StateMap eta g y)) =
      regCoeff m (molecularH2StateMap eta g y +
        ((2 / g ^ 2 : ℝ) : ℂ) • coulombFourierKineticH2 sys g y) := by
  rw [map_add, map_smul, regCoeff_kinetic]
  ext q
  simp only [wMul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have e : wM (regParticlesOf sys) q = 1 + 2 / g ^ 2 * kinT eta m (regParticlesOf sys) g q := by
    unfold kinT
    field_simp
    ring
  rw [e]
  push_cast
  ring

omit [Fintype ν] in
/-- The register weight from the kinetic multiplier: `W φ = φ + (2/g²) A φ`. -/
lemma wM_eq_add_kinT (sys : CoulombSystem eta ν) {g : ℝ} (hg : 0 < g) {m : ℕ}
    (φ : EuclideanSpace ℂ (RCfg eta m)) :
    wMul (wM (regParticlesOf sys)) φ =
      φ + ((2 / g ^ 2 : ℝ) : ℂ) • wMul (kinT eta m (regParticlesOf sys) g) φ := by
  ext q
  simp only [wMul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have e : wM (regParticlesOf sys) q = 1 + 2 / g ^ 2 * kinT eta m (regParticlesOf sys) g q := by
    unfold kinT
    field_simp
    ring
  rw [e]
  push_cast
  ring

end Weight

/-! ## The exact trajectory -/

section Exact

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **The shells of the exact trajectory on the register**: with `B₀ = (1 + 2/g²) c_tr Ξ`,
`‖W P' ψ(t)‖ ≤ B₀` and `‖1_{|q_p|_∞ > T} W P' ψ(t)‖ ≤ (B₀/√g)/√T` for `gT ≥ 1`. -/
theorem exact_traj_shells (D : EvoData L H) (t : ℝ) (m : ℕ) (p : Fin eta) :
    ‖wMul (wM (regParticlesOf sys)) (regCoeff m (D.U t (Sm eta L D.u₀)))‖ ≤
        (1 + 2 / gF L ^ 2) * (cTr sys L Hunit * D.Xi) ∧
      ∀ T : ℕ, 1 ≤ gF L * T →
        ‖maskOp (High T p) (wMul (wM (regParticlesOf sys)) (regCoeff m (D.U t (Sm eta L D.u₀))))‖ ≤
          (1 + 2 / gF L ^ 2) * (cTr sys L Hunit * D.Xi) / Real.sqrt (gF L) / Real.sqrt T := by
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D t
  set M := cTr sys L Hunit * D.Xi with hM
  have hg : 0 < gF L := gF_pos hL
  have hM0 : 0 ≤ M := hF.nonneg
  have hc : (0 : ℝ) ≤ 1 + 2 / gF L ^ 2 := by positivity
  have hS : regCoeff m (D.U t (Sm eta L D.u₀)) =
      regCoeff m (molecularH2StateMap eta (gF L) w) := by rw [← hw1]
  rw [hS]
  refine ⟨?_, fun T hT => ?_⟩
  · refine (norm_wM_regCoeff_le sys (gF L) (m := m) hg w).trans ?_
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans hF.1) hc
  · rw [wM_regCoeff_eq sys hg w]
    refine (norm_high_regCoeff_le hg T p _).trans ?_
    rw [map_add, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    obtain ⟨h1, h2⟩ := hF.2 p (gF L * T) hT
    have hgT : 0 < gF L * T := by linarith
    have hsq : Real.sqrt (gF L * T) = Real.sqrt (gF L) * Real.sqrt T :=
      Real.sqrt_mul hg.le T
    have hr1 : (gF L * T) ^ (-(1 / 2 : ℝ)) = 1 / (Real.sqrt (gF L) * Real.sqrt T) := by
      rw [rpow_neg_half_eq hgT, hsq]
    have hr5 : (gF L * T) ^ (-(5 / 2 : ℝ)) ≤ (gF L * T) ^ (-(1 / 2 : ℝ)) :=
      rpow_le_of_le_one hT (by norm_num)
    have h1' : ‖tailMask (gF L) (gF L * T) p (molecularH2StateMap eta (gF L) w)‖ ≤
        M * (1 / (Real.sqrt (gF L) * Real.sqrt T)) := by
      rw [← hr1]
      exact h1.trans (mul_le_mul_of_nonneg_left hr5 hM0)
    have h2' : ‖tailMask (gF L) (gF L * T) p (coulombFourierKineticH2 sys (gF L) w)‖ ≤
        M * (1 / (Real.sqrt (gF L) * Real.sqrt T)) := by
      rw [← hr1]
      exact h2
    calc ‖tailMask (gF L) (gF L * T) p (molecularH2StateMap eta (gF L) w)‖ +
          2 / gF L ^ 2 * ‖tailMask (gF L) (gF L * T) p (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ M * (1 / (Real.sqrt (gF L) * Real.sqrt T)) +
            2 / gF L ^ 2 * (M * (1 / (Real.sqrt (gF L) * Real.sqrt T))) :=
          add_le_add h1' (mul_le_mul_of_nonneg_left h2' (by positivity))
      _ = (1 + 2 / gF L ^ 2) * M / Real.sqrt (gF L) / Real.sqrt T := by
          rw [div_div]
          ring

end Exact

/-! ## The grid trajectory -/

section GridTrajectory

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

/-- The first weighted constant of grid trajectories,
`(5/3)(1 + 2/g²) c_tr + (4/3)(1 + 104 Z J₀/g²)`. -/
noncomputable def bG0 (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  5 / 3 * ((1 + 2 / gF L ^ 2) * cTr sys L Hunit) +
    4 / 3 * (1 + 104 * ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) *
      (J0g ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (gF L) : ℝ) / gF L ^ 2)

/-- The shell constant of grid trajectories, `(8 m̄ + 2/g²) G₄/√g`. -/
noncomputable def bG1 (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  (8 * sys.maxMass + 2 / gF L ^ 2) * gtcSum sys L Hunit (molecularCanonicalLowConstant L)
    (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L) /
      Real.sqrt (gF L)

include hKernel hL hPeriodic in
/-- **The shells of the grid trajectory on the register** (`lem:grid-traj`, `lem:grid-tails`):
`‖W U_g(t) P' ψ₀‖ ≤ b₀ Ξ` and `‖1_{|q_p|_∞ > T} W U_g(t) P' ψ₀‖ ≤ b₁ Ξ/√T` for
`max(1/g, 4) ≤ T ≤ m`, uniformly over the kernel class and the time. -/
theorem grid_traj_shells (D : EvoData L H) (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ gF L * m)
    {κ : Lat3 → ℝ} (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (t : ℝ) (p : Fin eta) :
    ‖wMul (wM (regParticlesOf sys)) (Ug t (regCoeff m (Sm eta L D.u₀)))‖ ≤
        bG0 sys L Hunit * D.Xi ∧
      ∀ T : ℕ, 1 ≤ gF L * T → 4 ≤ T → T ≤ m →
        ‖maskOp (High T p) (wMul (wM (regParticlesOf sys)) (Ug t (regCoeff m (Sm eta L D.u₀))))‖ ≤
          bG1 sys L Hunit * D.Xi / Real.sqrt T := by
  have hg : 0 < gF L := gF_pos hL
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hΞ := D.Xi_nonneg
  have hF0 := datum_fgood sys hL H hKernel Hunit hPeriodic D
  set x₀ := regCoeff m (Sm eta L D.u₀) with hx₀
  refine ⟨?_, fun T hT1 hT4 hTm => ?_⟩
  · -- regularity of grid trajectories
    have h := (gridRegHam (eta := eta) (m := m) (P := regParticlesOf sys)
      (D := (posNucleiOf sys.nuclei).toNucData) hγ hκ.bound hg).flow_le_weight (Ug t)
      (fun x => by rw [gridRegHam_op]; exact hgcomm t x) x₀
    rw [gridRegHam_W, gridRegHam_g, gridRegHam_Z, gridRegHam_J0] at h
    refine h.trans ?_
    have hw : ‖wMul (wM (regParticlesOf sys)) x₀‖ ≤ (1 + 2 / gF L ^ 2) * (cTr sys L Hunit * D.Xi) :=
      (norm_wM_regCoeff_le sys (gF L) (m := m) hg D.u₀).trans
        (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans hF0.1) (by positivity))
    have hx : ‖x₀‖ ≤ D.Xi := by
      refine (norm_regCoeff_le _).trans ?_
      unfold EvoData.Xi
      have := norm_nonneg (H D.u₀)
      have := norm_nonneg (H D.v₀)
      linarith
    have hZ : 0 ≤ (regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) :=
      mul_nonneg (regParticlesOf sys).maxMass_pos.le (Zc_nonneg hγ)
    have hc2 : 0 ≤ 4 / 3 * (1 + 104 * ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) *
        (J0g ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
          (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (gF L) : ℝ) /
            gF L ^ 2) := by positivity
    unfold bG0
    have e1 := mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 5 / 3)
    have e2 := mul_le_mul_of_nonneg_left hx hc2
    nlinarith
  · -- the kinetic tails of the grid trajectory
    obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
      molecularCanonicalTailConstants_spec L hL
    set lam := gF L * T with hlam
    have hl1 : 1 ≤ lam := hT1
    have hl4 : 4 * (2 * Real.pi / L) ≤ lam := by
      have : (4 : ℝ) ≤ T := by exact_mod_cast hT4
      change 4 * gF L ≤ gF L * T
      nlinarith
    have hlK : lam ≤ (2 * Real.pi / L) * m := by
      have : (T : ℝ) ≤ m := by exact_mod_cast hTm
      change gF L * T ≤ gF L * m
      exact mul_le_mul_of_nonneg_left this hg.le
    have h := grid_kin_tail_euclid sys L H hKernel Hunit hL hPeriodic hC D.U D.U0 D.graph m hm hK hκ
      Ug hgcomm (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) hBlow hCs hBker hLow hKernelScale hSobolev D.u₀ D.v₀
      D.uv t p hl1 hl4 hlK
    simp only at h
    obtain ⟨hA, hψ⟩ := h
    set Dg := gridTailConst sys L Hunit (molecularCanonicalLowConstant L)
      (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L)
      ‖molecularH2StateMap eta (2 * Real.pi / L) D.u₀‖ ‖H D.u₀‖
      ‖molecularH2StateMap eta (2 * Real.pi / L) D.v₀‖ ‖H D.v₀‖ with hDg
    have hDg0 : 0 ≤ Dg := gridTailConst_nonneg sys hL Hunit hC hBlow hCs hBker (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    have hDgle : Dg ≤ gtcSum sys L Hunit (molecularCanonicalLowConstant L)
        (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L) * D.Xi := by
      have hv : ‖molecularH2StateMap eta (2 * Real.pi / L) D.v₀‖ = ‖H D.u₀‖ := by
        have := D.uv
        change ‖Sm eta L D.v₀‖ = _
        rw [← this]
      have hX1 : ‖molecularH2StateMap eta (2 * Real.pi / L) D.u₀‖ ≤ D.Xi := by
        change ‖Sm eta L D.u₀‖ ≤ D.Xi
        unfold EvoData.Xi
        have := norm_nonneg (H D.u₀)
        have := norm_nonneg (H D.v₀)
        linarith
      have hX2 : ‖H D.u₀‖ ≤ D.Xi := by
        unfold EvoData.Xi
        have := norm_nonneg (Sm eta L D.u₀)
        have := norm_nonneg (H D.v₀)
        linarith
      have hX3 : ‖H D.v₀‖ ≤ D.Xi := by
        unfold EvoData.Xi
        have := norm_nonneg (Sm eta L D.u₀)
        have := norm_nonneg (H D.u₀)
        linarith
      exact gridTailConst_le hL hC hBlow hCs hBker (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
        (norm_nonneg _) hX1 hX2 (hv ▸ hX2) hX3
    set ψ := Ug t x₀ with hψdef
    have hlpos : 0 < lam := by linarith
    have hsl : Real.sqrt (1 / lam) = 1 / (Real.sqrt (gF L) * Real.sqrt T) := by
      rw [Real.sqrt_div' 1 hlpos.le, Real.sqrt_one, hlam, Real.sqrt_mul hg.le]
    -- the shell of `W ψ` against the two Euclidean tails
    rw [wM_eq_add_kinT sys hg ψ, map_add, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have k1 : ‖maskOp (High T p) ψ‖ ≤ 8 * sys.maxMass / lam ^ 2 * (Dg * Real.sqrt (1 / lam)) := by
      have := norm_high_regCoeff_le (m := m) hg T p (regEmb m ψ)
      rw [regCoeff_regEmb] at this
      exact this.trans hψ
    have k2 : ‖maskOp (High T p) (wMul (kinT eta m (regParticlesOf sys) (gF L)) ψ)‖ ≤
        Dg * Real.sqrt (1 / lam) := by
      have := norm_high_regCoeff_le (m := m) hg T p (regEmb m (wMul (kinT eta m (regParticlesOf sys)
        (gF L)) ψ))
      rw [regCoeff_regEmb] at this
      exact this.trans hA
    have hl2 : 8 * sys.maxMass / lam ^ 2 ≤ 8 * sys.maxMass := by
      have hm := sys.one_le_maxMass
      exact div_le_self (by positivity) (one_le_pow₀ hl1)
    have hs0 : 0 ≤ Dg * Real.sqrt (1 / lam) := by positivity
    calc ‖maskOp (High T p) ψ‖ +
          2 / gF L ^ 2 * ‖maskOp (High T p) (wMul (kinT eta m (regParticlesOf sys) (gF L)) ψ)‖
        ≤ 8 * sys.maxMass * (Dg * Real.sqrt (1 / lam)) +
            2 / gF L ^ 2 * (Dg * Real.sqrt (1 / lam)) := by
          refine add_le_add (k1.trans (mul_le_mul_of_nonneg_right hl2 hs0)) ?_
          exact mul_le_mul_of_nonneg_left k2 (by positivity)
      _ = (8 * sys.maxMass + 2 / gF L ^ 2) * Dg / Real.sqrt (gF L) / Real.sqrt T := by
          rw [hsl, div_div]
          field_simp
      _ ≤ bG1 sys L Hunit * D.Xi / Real.sqrt T := by
          unfold bG1
          have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by
            have : (1 : ℝ) ≤ T := by
              have : (4 : ℝ) ≤ T := by exact_mod_cast hT4
              linarith
            linarith)
          have hsg : 0 < Real.sqrt (gF L) := Real.sqrt_pos.mpr hg
          rw [div_le_div_iff_of_pos_right hsT]
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hsg]
          have hm := sys.one_le_maxMass
          have hc8 : 0 ≤ 8 * sys.maxMass + 2 / gF L ^ 2 := by positivity
          calc (8 * sys.maxMass + 2 / gF L ^ 2) * Dg ≤ (8 * sys.maxMass + 2 / gF L ^ 2) *
                (gtcSum sys L Hunit (molecularCanonicalLowConstant L)
                  (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L) *
                    D.Xi) := mul_le_mul_of_nonneg_left hDgle hc8
            _ = _ := by ring

end GridTrajectory

end KineticLog
