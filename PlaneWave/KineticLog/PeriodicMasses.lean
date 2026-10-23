import PlaneWave.KineticLog.PeriodicN

/-!
# Logarithmic kinetic bound, part 35: arbitrary positive masses

The Lean Coulomb systems (`CoulombSystem`) have masses `m_i ≥ 1`. `app:source` allows any positive
masses. This file covers them by a **charge rescaling**. For a system `S` with masses `μ_i > 0`,
charges `q_i` and nuclear charges `Z_ℓ` (`PosSystem`), and `λ = 1 + Σ_i 1/μ_i ≥ 1`, the Lean system
`S.scaled` has masses `λ μ_i ≥ 1`, charges `q_i/√λ` and nuclear charges `Z_ℓ/√λ`. In the same cell
and the same Fourier coefficients every operator of `S` is `λ` times that of `S.scaled`:

* the lattice kernel of the Hamiltonian (`latticeKernel_eq`), hence `H = λ H'`;
* the kinetic energies `T_p = λ T'_p` (`kinExpect_eq`, `gridExpect_eq`);
* the Galerkin Hamiltonian `H_N = λ H'_N` (`galerkinH_eq`) and the grid Hamiltonian `G = λ G'`
  (`gridH_eq`).

So `e^{-iHt} = e^{-iH'(λt)}`: the propagator data (`evoRescale`, with `Ξ' ≤ Ξ`), every solution of
the Galerkin equation (`galerkin_solution_eq`, by uniqueness for symmetric generators, `ode_unique`)
and every grid propagator (`Ug(·/λ)`) are those of `S.scaled` at time `λt`. The cutoffs `K` and the
kernel class do not change. Hence the endpoints of `S.scaled` give those of `S`:

* **`thm_kinetic_log_galerkin_pos`**, **`kinetic_retained_galerkin_pos`**,
  **`cor_stopping_log_galerkin_pos`**, **`thm_kinetic_log_grid_pos`**,
  **`cor_stopping_log_grid_pos`**: `thm:kinetic-log`, eq:kinetic-retained-galerkin and
  `cor:stopping-log` for arbitrary positive masses, with the constants first (`C = λ² C'`, and
  `λ C'` for the retained estimate);
* the spin forms `kinetic_retained_galerkin_spin_pos`, `thm_kinetic_log_galerkin_spin_pos`,
  `cor_stopping_log_galerkin_spin_pos`, `thm_kinetic_log_grid_spin_pos`,
  `cor_stopping_log_grid_spin_pos`, and the forms in terms of `N` (`*_pos_N`, `*_spin_pos_N`,
  as in part 34).

The hypotheses can be met: `PosSystem.exists_H` (the Hamiltonian of `S`), `exists_evoData_pos`
(the propagator data for every datum), `PosSystem.exists_galerkin_solution` and
`PosSystem.exists_gridPropagator`. For masses `≥ 1` the definitions are those of the release
(`PosSystem.ofCoulomb_latticeKernel`, `_kinExpect`, `_gridExpect`, `_galerkinH`, `_gridH`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal FSGalerkin

namespace KineticLog

variable {eta : ℕ} {ν : Type}

/-! ## Systems with positive masses and their rescaling -/

/-- **A periodic Coulomb system with arbitrary positive masses**: quantum particles with masses
`μ_i > 0` and charges `q_i`, and clamped nuclei (charges `Z_ℓ ≥ 0`, positions on the torus). -/
structure PosSystem (eta : ℕ) (ν : Type) where
  mass : Fin eta → ℝ
  mass_pos : ∀ i, 0 < mass i
  charge : Fin eta → ℝ
  nuclei : FiniteBONuclearData ν

namespace PosSystem

variable (S : PosSystem eta ν)

/-- The scale `λ = 1 + Σ_i 1/μ_i`. -/
noncomputable def lam : ℝ := 1 + ∑ i, 1 / S.mass i

lemma one_le_lam : 1 ≤ S.lam := by
  unfold lam
  have : 0 ≤ ∑ i, 1 / S.mass i := Finset.sum_nonneg fun i _ => (one_div_pos.mpr (S.mass_pos i)).le
  linarith

lemma lam_pos : 0 < S.lam := lt_of_lt_of_le one_pos S.one_le_lam

lemma one_le_lam_mul (i : Fin eta) : 1 ≤ S.lam * S.mass i := by
  have h1 : 1 / S.mass i ≤ S.lam := by
    unfold lam
    have := Finset.single_le_sum (f := fun j => 1 / S.mass j)
      (fun j _ => (one_div_pos.mpr (S.mass_pos j)).le) (Finset.mem_univ i)
    linarith
  have h2 := S.mass_pos i
  rw [div_le_iff₀ h2] at h1
  linarith

lemma sqrt_lam_pos : 0 < Real.sqrt S.lam := Real.sqrt_pos.mpr S.lam_pos

/-- Nuclei with charges multiplied by `c ≥ 0`. -/
def scaleNuclei (N : FiniteBONuclearData ν) (c : ℝ) (hc : 0 ≤ c) : FiniteBONuclearData ν where
  charge := fun l => c * N.charge l
  charge_nonneg := fun l => mul_nonneg hc (N.charge_nonneg l)
  position := N.position

/-- **The rescaled Lean system**: masses `λ μ_i ≥ 1`, charges `q_i/√λ`, nuclear charges
`Z_ℓ/√λ` (each particle its own species). -/
noncomputable def scaled : CoulombSystem eta ν where
  mass := fun i => S.lam * S.mass i
  one_le_mass := S.one_le_lam_mul
  charge := fun i => S.charge i / Real.sqrt S.lam
  species := fun i => i.val
  fermion := fun _ => true
  mass_eq := fun a b h => by rw [Fin.ext h]
  charge_eq := fun a b h => by rw [Fin.ext h]
  nuclei := scaleNuclei S.nuclei (1 / Real.sqrt S.lam) (by have := S.sqrt_lam_pos; positivity)

/-- The charges of `S` with unit masses: the system whose potential terms are those of `S`. -/
def unitSys : CoulombSystem eta ν where
  mass := fun _ => 1
  one_le_mass := fun _ => le_rfl
  charge := S.charge
  species := fun i => i.val
  fermion := fun _ => true
  mass_eq := fun _ _ _ => rfl
  charge_eq := fun a b h => by rw [Fin.ext h]
  nuclei := S.nuclei

@[simp] lemma scaled_mass (i : Fin eta) : S.scaled.mass i = S.lam * S.mass i := rfl
@[simp] lemma scaled_charge (i : Fin eta) : S.scaled.charge i = S.charge i / Real.sqrt S.lam := rfl
@[simp] lemma scaled_nuclei_charge (l : ν) :
    S.scaled.nuclei.charge l = 1 / Real.sqrt S.lam * S.nuclei.charge l := rfl
@[simp] lemma scaled_nuclei_position (l : ν) : S.scaled.nuclei.position l = S.nuclei.position l :=
  rfl
@[simp] lemma unitSys_charge (i : Fin eta) : S.unitSys.charge i = S.charge i := rfl
@[simp] lemma unitSys_nuclei : S.unitSys.nuclei = S.nuclei := rfl

lemma sqrt_lam_sq : Real.sqrt S.lam * Real.sqrt S.lam = S.lam :=
  Real.mul_self_sqrt S.lam_pos.le

/-! ## The lattice kernel -/

lemma lam_eq_sqrt_mul : (S.lam : ℂ) = (Real.sqrt S.lam : ℂ) * (Real.sqrt S.lam : ℂ) := by
  rw [← Complex.ofReal_mul, S.sqrt_lam_sq]

lemma sqrt_lam_ne : (Real.sqrt S.lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr S.sqrt_lam_pos.ne'

/-- The kinetic coefficient scales. -/
lemma kinetic_eq (L : ℝ) (q p : FourierConfig eta Lattice3) :
    (by classical
        exact (if p = q then (1 / 2 : ℂ) *
          ((∑ i : Fin eta, (2 * Real.pi / L) ^ 2 * latticeNormSq (q i) / S.mass i : ℝ) : ℂ)
          else 0) : ℂ) =
      (S.lam : ℂ) * coulombLatticeKineticKernel S.scaled L q p := by
  classical
  unfold coulombLatticeKineticKernel
  split_ifs with h
  · have e : ∀ i : Fin eta, (2 * Real.pi / L) ^ 2 * latticeNormSq (q i) / S.mass i =
        S.lam * ((2 * Real.pi / L) ^ 2 * latticeNormSq (q i) / S.scaled.mass i) := by
      intro i
      rw [scaled_mass]
      have := S.mass_pos i
      have := S.lam_pos
      field_simp
    simp_rw [e]
    rw [← Finset.mul_sum]
    push_cast
    ring
  · ring

variable [Fintype ν]

/-- **The lattice kernel of the Hamiltonian of `S`** in a cell of side `L`: the kinetic
coefficient `(1/2) Σ_a (2π/L)² |q_a|²/μ_a` plus the release's nuclear and pair kernels with the
charges of `S`. -/
noncomputable def latticeKernel (L : ℝ) (q p : FourierConfig eta Lattice3) : ℂ := by
  classical
  exact (if p = q then (1 / 2 : ℂ) *
      ((∑ i : Fin eta, (2 * Real.pi / L) ^ 2 * latticeNormSq (q i) / S.mass i : ℝ) : ℂ) else 0) +
    (coulombLatticeNuclearKernel S.unitSys (coulombCellAmplitude L) q p +
      coulombLatticePairKernel S.unitSys (coulombCellAmplitude L) q p)

/-- The nuclear kernel scales. -/
lemma nuclear_eq (γ : ℝ) (q p : FourierConfig eta Lattice3) :
    coulombLatticeNuclearKernel S.unitSys γ q p =
      (S.lam : ℂ) * coulombLatticeNuclearKernel S.scaled γ q p := by
  classical
  unfold coulombLatticeNuclearKernel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hB : ∀ l : ν, latticeReferenceConfigurationKernel i
      (latticeElectronNuclearKernel S.scaled.nuclei γ l) q p =
      (1 / (Real.sqrt S.lam : ℂ)) * latticeReferenceConfigurationKernel i
        (latticeElectronNuclearKernel S.nuclei γ l) q p := by
    intro l
    unfold latticeReferenceConfigurationKernel latticeElectronNuclearKernel
    split_ifs
    · rw [scaled_nuclei_charge, scaled_nuclei_position]
      push_cast
      ring
    · ring
  simp_rw [hB]
  rw [← Finset.mul_sum, unitSys_charge, scaled_charge, unitSys_nuclei, S.lam_eq_sqrt_mul]
  have := S.sqrt_lam_ne
  push_cast
  field_simp

omit [Fintype ν] in
/-- The pair kernel scales. -/
lemma pair_eq (γ : ℝ) (q p : FourierConfig eta Lattice3) :
    coulombLatticePairKernel S.unitSys γ q p =
      (S.lam : ℂ) * coulombLatticePairKernel S.scaled γ q p := by
  unfold coulombLatticePairKernel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun pr _ => ?_
  rw [scaled_charge, scaled_charge, unitSys_charge, unitSys_charge, S.lam_eq_sqrt_mul]
  have := S.sqrt_lam_ne
  push_cast
  field_simp

/-- **The kernel scales**: the kernel of `S` is `λ` times that of `S.scaled`. -/
lemma latticeKernel_eq (L : ℝ) (q p : FourierConfig eta Lattice3) :
    S.latticeKernel L q p = (S.lam : ℂ) * coulombLatticeHamiltonianKernel S.scaled L q p := by
  unfold latticeKernel coulombLatticeHamiltonianKernel
  rw [S.kinetic_eq L q p, S.nuclear_eq, S.pair_eq]
  ring

/-! ## The kinetic energies -/

omit [Fintype ν] in
/-- `|k_r|²/(2 μ_r) = λ |k_r|²/(2 λ μ_r)`. -/
lemma kinSymbol_eq_aux (g : ℝ) (r : Fin eta) (x : ℝ) :
    (1 / 2 : ℝ) * (g ^ 2 * x / S.mass r) =
      S.lam * ((1 / 2 : ℝ) * (g ^ 2 * x / S.scaled.mass r)) := by
  rw [scaled_mass]
  have := S.mass_pos r
  have := S.lam_pos
  field_simp

/-- **The kinetic energy of particle `r` of `S`** in a state with Fourier coefficients `x`:
`⟨x, T_r x⟩ = Σ_p g² |p_r|²/(2 μ_r) |x_p|²`. -/
noncomputable def kinExpect (g : ℝ) (r : Fin eta)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) : ℝ :=
  ∑' p, (1 / 2 : ℝ) * (g ^ 2 * latticeNormSq (p r) / S.mass r) * ‖x p‖ ^ 2

omit [Fintype ν] in
/-- The kinetic energy of `S` is `λ` times that of `S.scaled`. -/
lemma kinExpect_eq (g : ℝ) (r : Fin eta) (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    S.kinExpect g r x = S.lam * (regKin S.scaled g r).expect x := by
  unfold kinExpect
  change _ = S.lam * ∑' p, regSymbol S.scaled g r p * ‖x p‖ ^ 2
  rw [← tsum_mul_left]
  congr 1
  funext p
  unfold regSymbol
  rw [S.kinSymbol_eq_aux g r]
  ring

/-- **The kinetic energy of particle `r` of `S` on the grid register**:
`Σ_q g² |q_r|²/(2 μ_r) |x_q|²`. -/
noncomputable def gridExpect (g : ℝ) (r : Fin eta) {m : ℕ}
    (x : EuclideanSpace ℂ (RCfg eta m)) : ℝ :=
  ∑ q, (1 / 2 : ℝ) * (g ^ 2 * latticeNormSq (liftCfg q r) / S.mass r) * ‖x q‖ ^ 2

omit [Fintype ν] in
/-- The grid kinetic energy of `S` is `λ` times that of `S.scaled`. -/
lemma gridExpect_eq (g : ℝ) (r : Fin eta) {m : ℕ} (x : EuclideanSpace ℂ (RCfg eta m)) :
    S.gridExpect g r x = S.lam * regExpect S.scaled g r x := by
  unfold gridExpect regExpect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold regKinSym regSymbol
  rw [S.kinSymbol_eq_aux g r]
  ring

/-! ## The Galerkin Hamiltonian -/

omit [Fintype ν] in
lemma atom_smul {μ : Type*} [Fintype μ] (r : Fin eta) (c : ℂ) (K : μ → μ → ℂ)
    (p : FourierConfig eta μ) :
    referenceSliceKernelAtom r (fun v u => c * K v u) p = c • referenceSliceKernelAtom r K p := by
  classical
  ext q
  unfold referenceSliceKernelAtom
  simp only [PiLp.smul_apply, smul_eq_mul]
  split_ifs <;> simp

omit [Fintype ν] in
lemma refConvOp_smul {μ : Type*} [Fintype μ] (r : Fin eta) (c : ℂ) (K : μ → μ → ℂ) :
    referenceKernelConvolutionOperator r (fun v u => c * K v u) =
      c • referenceKernelConvolutionOperator r K := by
  apply LinearMap.ext
  intro u
  rw [LinearMap.smul_apply, referenceKernelConvolutionOperator_eq_sum,
    referenceKernelConvolutionOperator_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [atom_smul r c K p, smul_comm]

/-- The finite potential of `S` is `λ` times that of `S.scaled`. -/
lemma potential_eq (γ : ℝ) (n : ℕ) :
    finiteCoulombPotential S.unitSys γ n = (S.lam : ℂ) • finiteCoulombPotential S.scaled γ n := by
  have hs := S.sqrt_lam_ne
  have hlam := S.lam_eq_sqrt_mul
  unfold finiteCoulombPotential finiteCoulombNuclearPotential finiteCoulombPairPotential
  rw [smul_add]
  congr 1
  · have hk : ∀ l : ν, finiteElectronNuclearKernel S.scaled.nuclei γ n l =
        fun v u =>
          (1 / (Real.sqrt S.lam : ℂ)) * finiteElectronNuclearKernel S.nuclei γ n l v u := by
      intro l
      funext v u
      unfold finiteElectronNuclearKernel
      rw [scaled_nuclei_charge, scaled_nuclei_position]
      push_cast
      ring
    simp_rw [hk, refConvOp_smul, ← Finset.smul_sum, smul_smul, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [unitSys_charge, scaled_charge, unitSys_nuclei, hlam]
    congr 1
    push_cast
    field_simp
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun pr _ => ?_
    rw [smul_smul, scaled_charge, scaled_charge, unitSys_charge, unitSys_charge, hlam]
    congr 1
    push_cast
    field_simp

/-- **The Galerkin Hamiltonian of `S`** on the cube `|ν|_∞ ≤ n`:
`(1/2) Σ_a |k_a|²/μ_a + W_N`, `W_N` the finite Coulomb potential with the charges of `S`. -/
noncomputable def galerkinH (L : ℝ) (n : ℕ) : En eta n →ₗ[ℂ] En eta n :=
  diagHamiltonian (massKineticSymbol S.mass (finitePlaneWaveKabs (2 * Real.pi / L) n))
    (finiteCoulombPotential S.unitSys (coulombCellAmplitude L) n)

/-- **The Galerkin Hamiltonian scales**: `H_N = λ H'_N`. -/
lemma galerkinH_eq (L : ℝ) (n : ℕ) :
    S.galerkinH L n = (S.lam : ℂ) • finiteCoulombHamiltonian S.scaled L n := by
  apply LinearMap.ext
  intro v
  ext p
  rw [LinearMap.smul_apply]
  unfold galerkinH finiteCoulombHamiltonian
  rw [PiLp.smul_apply, diagHamiltonian_apply, diagHamiltonian_apply, S.potential_eq,
    LinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
  unfold massKineticSymbol
  have e : ∀ a : Fin eta, finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2 / S.mass a =
      S.lam * (finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2 / S.scaled.mass a) := by
    intro a
    rw [scaled_mass]
    have := S.mass_pos a
    have := S.lam_pos
    field_simp
  simp_rw [e]
  rw [← Finset.mul_sum]
  push_cast
  ring

lemma galerkinH_isSymmetric (L : ℝ) (n : ℕ) : (S.galerkinH L n).IsSymmetric := by
  rw [S.galerkinH_eq]
  intro x y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
    finiteCoulombHamiltonian_isSymmetric S.scaled L n x y, Complex.conj_ofReal]

/-! ## The grid Hamiltonian -/

/-- The grid kinetic coefficient `g²/2 Σ_a |q_a|²/μ_a` of `S`. -/
noncomputable def gridKin (m : ℕ) (g : ℝ) (q : RCfg eta m) : ℝ :=
  g ^ 2 / 2 * ∑ a, nsq (gl (q a)) / S.mass a

/-- **The grid Hamiltonian of `S`**: the kinetic multiplier plus the grid potential of the kernel
`κ` with the charges of `S`. -/
noncomputable def gridH (m : ℕ) (κ : Lat3 → ℝ) (g : ℝ) :
    EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  PlaneWaveGrid.wMul (S.gridKin m g) + PlaneWaveGrid.kOp (vGridK eta m (regParticlesOf S.unitSys)
    (posNucleiOf S.nuclei).toNucData κ)

/-- **The grid Hamiltonian scales**: `G = λ G'`. -/
lemma gridH_eq (m : ℕ) (κ : Lat3 → ℝ) (g : ℝ) :
    S.gridH m κ g = (S.lam : ℂ) • Hgrid eta m (regParticlesOf S.scaled)
      (posNucleiOf S.scaled.nuclei).toNucData κ g := by
  have hs := S.sqrt_lam_ne
  have hlam := S.lam_eq_sqrt_mul
  apply LinearMap.ext
  intro v
  ext q
  rw [LinearMap.smul_apply]
  unfold gridH Hgrid
  simp only [LinearMap.add_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PlaneWaveGrid.wMul_apply, PlaneWaveGrid.kOp_apply]
  rw [mul_add]
  congr 1
  · unfold gridKin kinT wM
    have e : ∀ a : Fin eta, nsq (gl (q a)) / S.mass a =
        S.lam * (nsq (gl (q a)) / (regParticlesOf S.scaled).mass a) := by
      intro a
      rw [regParticlesOf_mass, scaled_mass]
      have := S.mass_pos a
      have := S.lam_pos
      field_simp
    simp_rw [e]
    rw [← Finset.mul_sum]
    push_cast
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold vGridK
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases t with pr | il
    · simp only [RegParticles.tcoef, regParticlesOf_charge, gridTerm, scaled_charge,
        unitSys_charge]
      rw [hlam]
      push_cast
      field_simp
    · simp only [RegParticles.tcoef, regParticlesOf_charge, gridTerm, scaled_charge,
        unitSys_charge]
      unfold tk kgn
      split_ifs
      · simp only [PosNuclei.toNucData, posNucleiOf, scaled_nuclei_charge, scaled_nuclei_position]
        rw [hlam]
        push_cast
        field_simp
      · simp

/-! ## The Hamiltonian operator -/

omit [Fintype ν] in
lemma kernelAction_smul (g : ℝ) (c : ℂ)
    (K : FourierConfig eta Lattice3 → FourierConfig eta Lattice3 → ℂ) (N : ℕ)
    (u : MolecularFourierH2 eta) (q : FourierConfig eta Lattice3) :
    fourierCubeKernelAction g (fun q p => c * K q p) N u q =
      c * fourierCubeKernelAction g K N u q := by
  unfold fourierCubeKernelAction
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

lemma latticeKernel_fun (L : ℝ) :
    S.latticeKernel L =
      fun q p => (S.lam : ℂ) * coulombLatticeHamiltonianKernel S.scaled L q p := by
  funext q p
  exact S.latticeKernel_eq L q p

omit [Fintype ν] in
lemma lam_ne : (S.lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr S.lam_pos.ne'

/-- If `H` has the lattice kernel of `S`, then `λ⁻¹ H` has the lattice kernel of `S.scaled`. -/
lemma kernel_scaled {L : ℝ}
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (S.latticeKernel L) N u q) :
    ∀ N u q, ((S.lam : ℂ)⁻¹ • H) (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel S.scaled L)
        N u q := by
  intro N u q
  rw [_root_.smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hKernel,
    S.latticeKernel_fun, kernelAction_smul, ← mul_assoc, inv_mul_cancel₀ S.lam_ne, one_mul]

/-- **The Hamiltonian of `S` exists**: `λ H'`, where `H'` is the Hamiltonian of `S.scaled`
(`exists_coulombFourierH2Operator`). -/
theorem exists_H (L Hunit : ℝ) (hL : 0 < L)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2,
      ∀ N u q, H (molecularH2Truncate N u) q =
        fourierCubeKernelAction (2 * Real.pi / L) (S.latticeKernel L) N u q := by
  obtain ⟨H', hK', -⟩ := exists_coulombFourierH2Operator S.scaled L Hunit hL hPeriodic
  refine ⟨(S.lam : ℂ) • H', fun N u q => ?_⟩
  rw [_root_.smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hK',
    S.latticeKernel_fun, kernelAction_smul]

end PosSystem

/-! ## Time rescaling -/

section Rescale

variable {L : ℝ}
  {H H' : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}

/-- **Time rescaling of the propagator data**: if `H = c H'` with `c > 0`, then `s ↦ U(s/c)` is
a propagator of `H'`, with the same datum `u₀` and `v₀' = v₀/c`. -/
noncomputable def evoRescale (D : EvoData L H) (c : ℝ) (hc : 0 < c) (hH : H = (c : ℂ) • H') :
    EvoData L H' where
  U := fun s => D.U (s / c)
  U0 := fun x => by rw [zero_div]; exact D.U0 x
  graph := fun t u => by
    obtain ⟨u', h1, h2⟩ := D.graph (t / c) u
    refine ⟨u', h1, ?_⟩
    have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    subst hH
    simp only [_root_.smul_apply, LinearIsometryEquiv.map_smul] at h2
    exact smul_right_injective _ hc' h2
  deriv := fun t u => by
    have hd : HasDerivAt (fun s : ℝ => s / c) (1 / c) t := (hasDerivAt_id' t).div_const c
    have h := (D.deriv (t / c) u).scomp t hd
    subst hH
    have e : (1 / c) • -(Complex.I • D.U (t / c) (((c : ℂ) • H') u)) =
        -(Complex.I • D.U (t / c) (H' u)) := by
      rw [_root_.smul_apply, LinearIsometryEquiv.map_smul,
        RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal, smul_neg,
        smul_smul, smul_smul]
      congr 2
      have : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
      push_cast
      field_simp
    rw [e] at h
    exact h
  cont := fun x => (D.cont x).comp (continuous_id.div_const c)
  u₀ := D.u₀
  v₀ := ((c⁻¹ : ℝ) : ℂ) • D.v₀
  uv := by
    have h := D.uv
    subst hH
    rw [_root_.smul_apply] at h
    rw [map_smul, ← h, smul_smul]
    have : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    push_cast
    rw [inv_mul_cancel₀ this, one_smul]

@[simp] lemma evoRescale_U (D : EvoData L H) (c : ℝ) (hc : 0 < c) (hH : H = (c : ℂ) • H')
    (s : ℝ) : (evoRescale D c hc hH).U s = D.U (s / c) := rfl

@[simp] lemma evoRescale_u₀ (D : EvoData L H) (c : ℝ) (hc : 0 < c) (hH : H = (c : ℂ) • H') :
    (evoRescale D c hc hH).u₀ = D.u₀ := rfl

@[simp] lemma evoRescale_v₀ (D : EvoData L H) (c : ℝ) (hc : 0 < c) (hH : H = (c : ℂ) • H') :
    (evoRescale D c hc hH).v₀ = ((c⁻¹ : ℝ) : ℂ) • D.v₀ := rfl

/-- For `c ≥ 1` the data norm does not grow: `Ξ' ≤ Ξ`. -/
lemma Xi_evoRescale_le (D : EvoData L H) {c : ℝ} (hc : 1 ≤ c) (hH : H = (c : ℂ) • H') :
    (evoRescale D c (by linarith) hH).Xi ≤ D.Xi := by
  have hc0 : 0 < c := by linarith
  have hnc : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  have hnc' : ‖((c⁻¹ : ℝ) : ℂ)‖ = c⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc0)]
  have hinv : c⁻¹ ≤ c := by
    have : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
    linarith
  unfold FSNormal.EvoData.Xi
  simp only [evoRescale]
  subst hH
  simp only [_root_.smul_apply, map_smul, norm_smul, hnc, hnc']
  have h1 : ‖H' D.u₀‖ ≤ c * ‖H' D.u₀‖ := le_mul_of_one_le_left (norm_nonneg _) hc
  have h2 : c⁻¹ * ‖H' D.v₀‖ ≤ c * ‖H' D.v₀‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  linarith

end Rescale

/-! ## Uniqueness for the finite-dimensional dynamics -/

/-- **Uniqueness for `x' = -i A x`** with `A` symmetric: `⟪x - y, x - y⟫` is constant. -/
lemma ode_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) {x y : ℝ → E}
    (hx : ∀ s, HasDerivAt x (-(Complex.I • A (x s))) s)
    (hy : ∀ s, HasDerivAt y (-(Complex.I • A (y s))) s) (h0 : x 0 = y 0) (t : ℝ) :
    x t = y t := by
  set w : ℝ → E := fun s => x s - y s with hw
  have hwd : ∀ s, HasDerivAt w (-(Complex.I • A (w s))) s := by
    intro s
    have h := (hx s).sub (hy s)
    have e : -(Complex.I • A (x s)) - -(Complex.I • A (y s)) = -(Complex.I • A (w s)) := by
      simp only [hw, map_sub, smul_sub]
      abel
    rw [e] at h
    exact h
  have hd : ∀ s, HasDerivAt (fun s => ⟪w s, w s⟫_ℂ) 0 s := by
    intro s
    have h := HasDerivAt.inner ℂ (hwd s) (hwd s)
    have e : ⟪w s, -(Complex.I • A (w s))⟫_ℂ + ⟪-(Complex.I • A (w s)), w s⟫_ℂ = 0 := by
      rw [inner_neg_right, inner_neg_left, inner_smul_right, inner_smul_left, hA (w s) (w s),
        Complex.conj_I]
      ring
    rw [e] at h
    exact h
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  have hw0 : w 0 = 0 := by simp [hw, h0]
  rw [hw0, inner_zero_left, inner_self_eq_zero] at hc
  exact sub_eq_zero.mp hc

namespace PosSystem

variable [Fintype ν] (S : PosSystem eta ν)

/-- The Galerkin flow of `S`: the retained flow of `S.scaled` at time `-λ s`. -/
lemma hasDerivAt_galerkinFlow (L : ℝ) (n : ℕ) (u : En eta n) (s : ℝ) :
    HasDerivAt (fun s => retFlow S.scaled L n (zero_isSymmetric (n := n)) (-(S.lam * s)) u)
      (-(Complex.I • S.galerkinH L n
        (retFlow S.scaled L n (zero_isSymmetric (n := n)) (-(S.lam * s)) u))) s := by
  have hd : HasDerivAt (fun s : ℝ => -(S.lam * s)) (-S.lam) s := by
    have h := ((hasDerivAt_id' s).const_mul S.lam).neg
    rw [mul_one] at h
    exact h
  have h := (hasDerivAt_retFlow S.scaled L n (zero_isSymmetric (n := n)) (-(S.lam * s)) u).scomp
    s hd
  set v := retFlow S.scaled L n (zero_isSymmetric (n := n)) (-(S.lam * s)) u with hv
  have e : (-S.lam) • (Complex.I • Hret S.scaled L n 0 v) =
      -(Complex.I • S.galerkinH L n v) := by
    rw [S.galerkinH_eq]
    unfold Hret
    rw [LinearMap.add_apply, LinearMap.zero_apply, add_zero, LinearMap.smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal, smul_smul,
      smul_smul, ← neg_smul]
    congr 1
    push_cast
    ring
  rw [e] at h
  exact h

/-- **The Galerkin equation of `S` has solutions** for every initial value. -/
lemma exists_galerkin_solution (L : ℝ) (n : ℕ) (x : En eta n) :
    ∃ ψN : ℝ → En eta n, ψN 0 = x ∧
      ∀ s, HasDerivAt ψN (-(Complex.I • S.galerkinH L n (ψN s))) s :=
  ⟨fun s => retFlow S.scaled L n (zero_isSymmetric (n := n)) (-(S.lam * s)) x,
    by simp [retFlow_zero], S.hasDerivAt_galerkinFlow L n x⟩

/-- **Every solution of the Galerkin equation of `S`** is the retained flow of `S.scaled` at time
`λ t`. -/
lemma galerkin_solution_eq (L : ℝ) (n : ℕ) (ψN : ℝ → En eta n)
    (hψ : ∀ s, HasDerivAt ψN (-(Complex.I • S.galerkinH L n (ψN s))) s) (t : ℝ) :
    ψN t = retFlow S.scaled L n (zero_isSymmetric (n := n)) (-(S.lam * t)) (ψN 0) :=
  ode_unique (S.galerkinH L n) (S.galerkinH_isSymmetric L n) hψ
    (S.hasDerivAt_galerkinFlow L n (ψN 0)) (by simp [retFlow_zero]) t

/-- The grid Hamiltonian of `S` is symmetric for every even kernel. -/
lemma gridH_isSymmetric (m : ℕ) {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x) (g : ℝ) :
    (S.gridH m κ g).IsSymmetric := by
  rw [S.gridH_eq]
  intro x y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
    Hgrid_isSymmetric hκe x y, Complex.conj_ofReal]

/-- **The grid propagators of `S` exist** (for every even kernel; they are unique,
`PlaneWaveDynamics.exists_finitePropagator`). -/
theorem exists_gridPropagator (m : ℕ) {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x) (g : ℝ) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ t x, Ug t (S.gridH m κ g x) = S.gridH m κ g (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (S.gridH m κ g x))) t) := by
  obtain ⟨U, h0, -, -, hcomm, hderiv, -⟩ :=
    PlaneWaveDynamics.exists_finitePropagator (S.gridH_isSymmetric m hκe g)
  exact ⟨U, h0, hcomm, hderiv⟩

/-! ## Consistency with the release -/

/-- A Lean Coulomb system (masses `≥ 1`) as a system with positive masses. -/
def ofCoulomb (sys : CoulombSystem eta ν) : PosSystem eta ν where
  mass := sys.mass
  mass_pos := fun i => lt_of_lt_of_le one_pos (sys.one_le_mass i)
  charge := sys.charge
  nuclei := sys.nuclei

omit [Fintype ν] in
@[simp] lemma ofCoulomb_mass (sys : CoulombSystem eta ν) : (ofCoulomb sys).mass = sys.mass := rfl

/-- **The Hamiltonian kernel of `PosSystem` is the release's** when the masses are `≥ 1`. -/
lemma ofCoulomb_latticeKernel (sys : CoulombSystem eta ν) (L : ℝ)
    (q p : FourierConfig eta Lattice3) :
    (ofCoulomb sys).latticeKernel L q p = coulombLatticeHamiltonianKernel sys L q p := rfl

omit [Fintype ν] in
/-- The kinetic energies agree with the release's `regKin`. -/
lemma ofCoulomb_kinExpect (sys : CoulombSystem eta ν) (g : ℝ) (r : Fin eta)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    (ofCoulomb sys).kinExpect g r x = (regKin sys g r).expect x := rfl

omit [Fintype ν] in
/-- The grid kinetic energies agree with the release's `regExpect`. -/
lemma ofCoulomb_gridExpect (sys : CoulombSystem eta ν) (g : ℝ) (r : Fin eta) {m : ℕ}
    (x : EuclideanSpace ℂ (RCfg eta m)) :
    (ofCoulomb sys).gridExpect g r x = regExpect sys g r x := rfl

/-- The Galerkin Hamiltonian agrees with the release's `finiteCoulombHamiltonian`. -/
lemma ofCoulomb_galerkinH (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) :
    (ofCoulomb sys).galerkinH L n = finiteCoulombHamiltonian sys L n := rfl

/-- The grid Hamiltonian agrees with the release's `Hgrid`. -/
lemma ofCoulomb_gridH (sys : CoulombSystem eta ν) (m : ℕ) (κ : Lat3 → ℝ) (g : ℝ) :
    (ofCoulomb sys).gridH m κ g =
      Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ g := by
  unfold gridH Hgrid
  congr 2
  funext q
  unfold gridKin kinT wM
  simp only [regParticlesOf_mass, ofCoulomb_mass]
  ring

omit [Fintype ν] in
lemma H_eq_smul (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    H = (S.lam : ℂ) • ((S.lam : ℂ)⁻¹ • H) := by
  rw [smul_smul, mul_inv_cancel₀ S.lam_ne, one_smul]

end PosSystem

/-! ## The arithmetic of the rescaling -/

/-- `λ C Ξ'² [1 + λt + ℓ]/K³ ≤ λ² C Ξ² [1 + t + ℓ]/K³` for `λ ≥ 1` and `Ξ' ≤ Ξ`. -/
lemma lam_arith {lam C X X' t lg K : ℝ} (hlam : 1 ≤ lam) (hC : 0 ≤ C) (hX' : 0 ≤ X')
    (hXX : X' ≤ X) (ht : 0 ≤ t) (hlg : 0 ≤ lg) (hK : 0 ≤ K) :
    lam * (C * X' ^ 2 * (1 + lam * t + lg) / K ^ 3) ≤
      lam ^ 2 * C * X ^ 2 * (1 + t + lg) / K ^ 3 := by
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hK 3)
  have hl0 : 0 ≤ lam := by linarith
  have h1 : X' ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hX' hXX 2
  have h2 : 1 + lam * t + lg ≤ lam * (1 + t + lg) := by nlinarith
  have h3 : 0 ≤ 1 + lam * t + lg := by have := mul_nonneg hl0 ht; linarith
  calc lam * (C * X' ^ 2 * (1 + lam * t + lg))
      ≤ lam * (C * X ^ 2 * (lam * (1 + t + lg))) := by
        apply mul_le_mul_of_nonneg_left _ hl0
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h2 h3 (mul_nonneg hC (sq_nonneg _))
    _ = lam ^ 2 * C * X ^ 2 * (1 + t + lg) / 1 := by ring
    _ = lam ^ 2 * C * X ^ 2 * (1 + t + lg) := div_one _

/-- `C Ξ' [1 + λt + ℓ]/K³ ≤ λ C Ξ [1 + t + ℓ]/K³` for `λ ≥ 1` and `Ξ' ≤ Ξ`. -/
lemma lam_arith1 {lam C X X' t lg K : ℝ} (hlam : 1 ≤ lam) (hC : 0 ≤ C) (hX' : 0 ≤ X')
    (hXX : X' ≤ X) (ht : 0 ≤ t) (hlg : 0 ≤ lg) (hK : 0 ≤ K) :
    C * X' * (1 + lam * t + lg) / K ^ 3 ≤ lam * C * X * (1 + t + lg) / K ^ 3 := by
  apply div_le_div_of_nonneg_right _ (pow_nonneg hK 3)
  have hl0 : 0 ≤ lam := by linarith
  have h2 : 1 + lam * t + lg ≤ lam * (1 + t + lg) := by nlinarith
  have h3 : 0 ≤ 1 + lam * t + lg := by have := mul_nonneg hl0 ht; linarith
  calc C * X' * (1 + lam * t + lg) ≤ C * X * (lam * (1 + t + lg)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hXX hC) h2 h3 (mul_nonneg hC (by linarith))
    _ = lam * C * X * (1 + t + lg) := by ring

/-! ## The endpoints for arbitrary positive masses -/

section Endpoints

variable [Fintype ν] (S : PosSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (S.latticeKernel L) N u q)
  (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hL in
lemma log_two_add_Kc_nonneg (n : ℕ) : 0 ≤ Real.log (2 + Kc L n) :=
  Real.log_nonneg (by linarith [Kc_nonneg' hL n])

include hL in
lemma Kc_pos_of_one_le {n : ℕ} (hn : 1 ≤ n) : 0 < Kc L n := by
  change 0 < gF L * n
  exact mul_pos (gF_pos hL) (by exact_mod_cast hn)

include hL hKernel hPeriodic in
/-- **`thm:kinetic-log`, Galerkin case, arbitrary positive masses** (constants first): there are
`C ≥ 0` and `N₀` such that for every cutoff `n ≥ N₀`, every measured particle `p₀`, every datum
`ψ₀ ∈ D(H²)` of the Hamiltonian `H` of `S`, every solution `ψ_N` of the Galerkin equation
`i ψ_N' = H_N ψ_N` of `S` with `ψ_N(0) = P ψ₀`, and every `t ≥ 0`,
`|⟨ψ(t), T_{p₀} ψ(t)⟩ - ⟨ψ_N(t), T_{p₀} ψ_N(t)⟩| ≤ C 𝒟² [1 + t + log(2 + K)]/K³`, with the
kinetic energy `T_{p₀}` of mass `μ_{p₀}`. -/
theorem thm_kinetic_log_galerkin_pos :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (D : EvoData L H)
      (ψN : ℝ → En eta n), ψN 0 = ext eta n (Sm eta L D.u₀) →
      (∀ s, HasDerivAt ψN (-(Complex.I • S.galerkinH L n (ψN s))) s) → ∀ t : ℝ, 0 ≤ t →
      |S.kinExpect (gF L) p₀ (D.U t (Sm eta L D.u₀)) -
          S.kinExpect (gF L) p₀ (emb eta n (ψN t))| ≤
        C * D.Xi ^ 2 * (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := by
  obtain ⟨C, hC, N₀, h⟩ := thm_kinetic_log_galerkin_all S.scaled hL ((S.lam : ℂ)⁻¹ • H)
    (S.kernel_scaled H hKernel) Hunit hPeriodic
  refine ⟨S.lam ^ 2 * C, by have := S.lam_pos; positivity, N₀,
    fun n hn p₀ D ψN hψ0 hψ t ht => ?_⟩
  have hH := S.H_eq_smul H
  have hUt : S.lam * t / S.lam = t := mul_div_cancel_left₀ t S.lam_pos.ne'
  have h1 := h n hn p₀ (evoRescale D S.lam S.lam_pos hH) (S.lam * t)
    (mul_nonneg S.lam_pos.le ht)
  simp only [evoRescale_U, evoRescale_u₀, hUt] at h1
  have hψt := S.galerkin_solution_eq L n ψN hψ t
  rw [hψ0] at hψt
  rw [S.kinExpect_eq, S.kinExpect_eq, hψt, ← mul_sub, abs_mul, abs_of_pos S.lam_pos]
  calc _ ≤ S.lam * (C * (evoRescale D S.lam S.lam_pos hH).Xi ^ 2 *
        (1 + S.lam * t + Real.log (2 + Kc L n)) / Kc L n ^ 3) :=
        mul_le_mul_of_nonneg_left h1 S.lam_pos.le
    _ ≤ _ := lam_arith S.one_le_lam hC (FSNormal.EvoData.Xi_nonneg _)
        (Xi_evoRescale_le D S.one_le_lam hH) ht (log_two_add_Kc_nonneg hL n) (Kc_nonneg' hL n)

include hL hKernel hPeriodic in
/-- **eq:kinetic-retained-galerkin, arbitrary positive masses**: every solution `ψ_N` of the
Galerkin equation of `S` with `ψ_N(0) = P ψ₀` satisfies
`‖P ψ(t) - ψ_N(t)‖ ≤ C 𝒟 [1 + t + log(2 + K)]/K³`. -/
theorem kinetic_retained_galerkin_pos :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : EvoData L H) (ψN : ℝ → En eta n),
      ψN 0 = ext eta n (Sm eta L D.u₀) →
      (∀ s, HasDerivAt ψN (-(Complex.I • S.galerkinH L n (ψN s))) s) → ∀ t : ℝ, 0 ≤ t →
      ‖molecularH2Truncate n (D.U t (Sm eta L D.u₀)) - emb eta n (ψN t)‖ ≤
        C * D.Xi * (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := by
  obtain ⟨C, hC, N₀, h⟩ := kinetic_retained_galerkin S.scaled hL ((S.lam : ℂ)⁻¹ • H)
    (S.kernel_scaled H hKernel) Hunit hPeriodic
  refine ⟨S.lam * C, by have := S.lam_pos; positivity, N₀, fun n hn D ψN hψ0 hψ t ht => ?_⟩
  have hH := S.H_eq_smul H
  have hUt : S.lam * t / S.lam = t := mul_div_cancel_left₀ t S.lam_pos.ne'
  have h1 := h n hn (evoRescale D S.lam S.lam_pos hH) (S.lam * t) (mul_nonneg S.lam_pos.le ht)
  simp only [evoRescale_U, evoRescale_u₀, hUt] at h1
  have hψt := S.galerkin_solution_eq L n ψN hψ t
  rw [hψ0] at hψt
  rw [hψt]
  exact h1.trans (lam_arith1 S.one_le_lam hC (FSNormal.EvoData.Xi_nonneg _)
    (Xi_evoRescale_le D S.one_le_lam hH) ht (log_two_add_Kc_nonneg hL n) (Kc_nonneg' hL n))

include hL hKernel hPeriodic in
/-- **`cor:stopping-log`, Galerkin case, arbitrary positive masses**: for every window `[0, τ]`,
`τ > 0`, and reference speed `v_p > 0`, the signed secants of the exact and Galerkin
trajectories differ by at most `(C 𝒟²/v_p) [1 + (1 + log(2 + K))/τ]/K³`. -/
theorem cor_stopping_log_galerkin_pos :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (D : EvoData L H)
      (ψN : ℝ → En eta n), ψN 0 = ext eta n (Sm eta L D.u₀) →
      (∀ s, HasDerivAt ψN (-(Complex.I • S.galerkinH L n (ψN s))) s) → ∀ {vp τ : ℝ}, 0 < vp →
      0 < τ →
      |(S.kinExpect (gF L) p₀ (D.U τ (Sm eta L D.u₀)) -
            S.kinExpect (gF L) p₀ (D.U 0 (Sm eta L D.u₀))) / (vp * τ) -
          (S.kinExpect (gF L) p₀ (emb eta n (ψN τ)) -
            S.kinExpect (gF L) p₀ (emb eta n (ψN 0))) / (vp * τ)| ≤
        C * D.Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 := by
  obtain ⟨C, hC, N₀, h⟩ := thm_kinetic_log_galerkin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨2 * C, by positivity, max N₀ 1, fun n hn p₀ D ψN hψ0 hψ vp τ hvp hτ => ?_⟩
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  exact secant_arith hC hvp hτ (Kc_pos_of_one_le hL (le_trans (le_max_right _ _) hn))
    (h n hn₀ p₀ D ψN hψ0 hψ τ hτ.le) (h n hn₀ p₀ D ψN hψ0 hψ 0 le_rfl)

include hL hKernel hPeriodic in
/-- **`thm:kinetic-log`, grid case, arbitrary positive masses** (constants first): for every
register radius `2m` with `m ≥ m₀`, every measured particle, every kernel `κ` of the class
`IsGridKernel`, every grid propagator `U_g` of the grid Hamiltonian `G` of `S`, every datum and
every `t ≥ 0`, `|⟨ψ(t), T_{p₀} ψ(t)⟩ - ⟨ψ_g(t), T_{p₀} ψ_g(t)⟩| ≤ C 𝒟² [1 + t + log(2 + K)]/K³`. -/
theorem thm_kinetic_log_grid_pos :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) {κ : Lat3 → ℝ},
      IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (S.gridH m κ (2 * Real.pi / L) x) = S.gridH m κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (S.gridH m κ (2 * Real.pi / L) x))) t) →
        ∀ (D : EvoData L H) (t : ℝ), 0 ≤ t →
          |S.kinExpect (gF L) p₀ (D.U t (Sm eta L D.u₀)) -
              S.gridExpect (gF L) p₀ (Ug t (regCoeff m (Sm eta L D.u₀)))| ≤
            C * D.Xi ^ 2 * (1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3 := by
  obtain ⟨C, hC, m₀, h⟩ := thm_kinetic_log_grid_all S.scaled ((S.lam : ℂ)⁻¹ • H)
    (S.kernel_scaled H hKernel) Hunit hL hPeriodic
  refine ⟨S.lam ^ 2 * C, by have := S.lam_pos; positivity, m₀,
    fun m hm p₀ κ hκ Ug hg0 hgcomm hgderiv D t ht => ?_⟩
  have hH := S.H_eq_smul H
  have hlam0 := S.lam_pos
  have hl : (S.lam : ℂ) ≠ 0 := S.lam_ne
  set G := Hgrid eta m (regParticlesOf S.scaled) (posNucleiOf S.scaled.nuclei).toNucData κ
    (2 * Real.pi / L) with hG
  have hGS : S.gridH m κ (2 * Real.pi / L) = (S.lam : ℂ) • G := S.gridH_eq m κ _
  have hg0' : ∀ x, Ug (0 / S.lam) x = x := fun x => by rw [zero_div]; exact hg0 x
  have hgcomm' : ∀ t x, Ug (t / S.lam) (G x) = G (Ug (t / S.lam) x) := by
    intro t x
    have h2 := hgcomm (t / S.lam) x
    rw [hGS, LinearMap.smul_apply, LinearMap.smul_apply, LinearIsometryEquiv.map_smul] at h2
    exact smul_right_injective _ hl h2
  have hgderiv' : ∀ t x, HasDerivAt (fun s => Ug (s / S.lam) x)
      (-(Complex.I • Ug (t / S.lam) (G x))) t := by
    intro t x
    have hd : HasDerivAt (fun s : ℝ => s / S.lam) (1 / S.lam) t :=
      (hasDerivAt_id' t).div_const S.lam
    have h2 := (hgderiv (t / S.lam) x).scomp t hd
    have e : (1 / S.lam) • -(Complex.I • Ug (t / S.lam) (S.gridH m κ (2 * Real.pi / L) x)) =
        -(Complex.I • Ug (t / S.lam) (G x)) := by
      rw [hGS, LinearMap.smul_apply, LinearIsometryEquiv.map_smul,
        RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal, smul_neg,
        smul_smul, smul_smul]
      congr 2
      push_cast
      field_simp
    rw [e] at h2
    exact h2
  have hUt : S.lam * t / S.lam = t := mul_div_cancel_left₀ t hlam0.ne'
  have h1 := h m hm p₀ hκ (fun s => Ug (s / S.lam)) hg0' hgcomm' hgderiv'
    (evoRescale D S.lam hlam0 hH) (S.lam * t) (mul_nonneg hlam0.le ht)
  simp only [evoRescale_U, evoRescale_u₀, hUt] at h1
  rw [S.kinExpect_eq, S.gridExpect_eq, ← mul_sub, abs_mul, abs_of_pos hlam0]
  calc _ ≤ S.lam * (C * (evoRescale D S.lam hlam0 hH).Xi ^ 2 *
        (1 + S.lam * t + Real.log (2 + Kc L m)) / Kc L m ^ 3) :=
        mul_le_mul_of_nonneg_left h1 hlam0.le
    _ ≤ _ := lam_arith S.one_le_lam hC (FSNormal.EvoData.Xi_nonneg _)
        (Xi_evoRescale_le D S.one_le_lam hH) ht (log_two_add_Kc_nonneg hL m) (Kc_nonneg' hL m)

include hL hKernel hPeriodic in
/-- **`cor:stopping-log`, grid case, arbitrary positive masses**: the signed secants of the exact
and grid trajectories differ by at most `(C 𝒟²/v_p) [1 + (1 + log(2 + K))/τ]/K³`, uniformly over
the measured particle, the kernel class and the grid propagators of `S`. -/
theorem cor_stopping_log_grid_pos :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) {κ : Lat3 → ℝ},
      IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (S.gridH m κ (2 * Real.pi / L) x) = S.gridH m κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (S.gridH m κ (2 * Real.pi / L) x))) t) →
        ∀ (D : EvoData L H) {vp τ : ℝ}, 0 < vp → 0 < τ →
          |(S.kinExpect (gF L) p₀ (D.U τ (Sm eta L D.u₀)) -
                S.kinExpect (gF L) p₀ (D.U 0 (Sm eta L D.u₀))) / (vp * τ) -
              (S.gridExpect (gF L) p₀ (Ug τ (regCoeff m (Sm eta L D.u₀))) -
                S.gridExpect (gF L) p₀ (Ug 0 (regCoeff m (Sm eta L D.u₀)))) / (vp * τ)| ≤
            C * D.Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 := by
  obtain ⟨C, hC, m₀, h⟩ := thm_kinetic_log_grid_pos S hL H hKernel Hunit hPeriodic
  refine ⟨2 * C, by positivity, max m₀ 1,
    fun m hm p₀ κ hκ Ug hg0 hgcomm hgderiv D vp τ hvp hτ => ?_⟩
  have hm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hm
  exact secant_arith hC hvp hτ (Kc_pos_of_one_le hL (le_trans (le_max_right _ _) hm))
    (h m hm₀ p₀ hκ Ug hg0 hgcomm hgderiv D τ hτ.le) (h m hm₀ p₀ hκ Ug hg0 hgcomm hgderiv D 0 le_rfl)

include hL hKernel in
/-- **The propagator data of `S` exist** for every datum `u₀ ∈ D(H²)`, `H u₀ = S v₀`: the data of
`S.scaled` (`exists_coulombFourierPropagator`) rescaled in time. -/
theorem exists_evoData_pos (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = Sm eta L v₀) :
    ∃ D : EvoData L H, D.u₀ = u₀ ∧ D.v₀ = v₀ := by
  have huv' : ((S.lam : ℂ)⁻¹ • H) u₀ = Sm eta L ((S.lam : ℂ)⁻¹ • v₀) := by
    rw [_root_.smul_apply, huv, map_smul]
  obtain ⟨U, h0, -, hc, hg, hd, -⟩ := exists_coulombFourierPropagator S.scaled L hL
    ((S.lam : ℂ)⁻¹ • H) (S.kernel_scaled H hKernel)
  let D' : EvoData L ((S.lam : ℂ)⁻¹ • H) := ⟨U, h0, hg, hd, hc, u₀, _, huv'⟩
  have hu : D'.u₀ = u₀ := rfl
  have hv : D'.v₀ = (S.lam : ℂ)⁻¹ • v₀ := rfl
  have hH : (S.lam : ℂ)⁻¹ • H = (((S.lam)⁻¹ : ℝ) : ℂ) • H := by rw [Complex.ofReal_inv]
  refine ⟨evoRescale D' (S.lam)⁻¹ (inv_pos.mpr S.lam_pos) hH, by rw [evoRescale_u₀, hu], ?_⟩
  rw [evoRescale_v₀, hv, inv_inv, smul_smul, mul_inv_cancel₀ S.lam_ne, one_smul]

/-! ## Spin -/

include hL hKernel hPeriodic in
/-- **`thm:kinetic-log`, Galerkin case with spin, arbitrary positive masses**: for every finite
spin set `Sp`, propagator data `D_σ` and Galerkin solutions `ψ_{N,σ}` of `S` with
`ψ_{N,σ}(0) = P ψ_{0,σ}`,
`|⟨Ψ(t), (T_{p₀} ⊗ 1) Ψ(t)⟩ - ⟨Ψ_N(t), (T_{p₀} ⊗ 1) Ψ_N(t)⟩| ≤ C Ξ_S² [1 + t + log(2+K)]/K³`. -/
theorem thm_kinetic_log_galerkin_spin_pos :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (Sp : Type) [Fintype Sp]
      (Ds : Sp → EvoData L H) (ψN : Sp → ℝ → En eta n),
      (∀ σ, ψN σ 0 = ext eta n (Sm eta L (Ds σ).u₀)) →
      (∀ σ s, HasDerivAt (ψN σ) (-(Complex.I • S.galerkinH L n (ψN σ s))) s) →
      ∀ t : ℝ, 0 ≤ t →
      |∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds t σ) -
          ∑ σ, S.kinExpect (gF L) p₀ (emb eta n (ψN σ t))| ≤
        C * FSSpin.XiS Ds ^ 2 * ((1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3) := by
  obtain ⟨C, hC, N₀, h⟩ := thm_kinetic_log_galerkin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C, hC, N₀, fun n hn p₀ Sp _ Ds ψN hψ0 hψ t ht => ?_⟩
  have hr : 0 ≤ (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 :=
    div_nonneg (logQ_nonneg hL n ht) (pow_nonneg (Kc_nonneg' hL n) 3)
  rw [← Finset.sum_sub_distrib]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h n hn p₀ (Ds σ) (ψN σ) (hψ0 σ) (hψ σ) t ht
  calc _ ≤ C * (Ds σ).Xi ^ 2 * (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3) := by ring

include hL hKernel hPeriodic in
/-- **`cor:stopping-log`, Galerkin case with spin, arbitrary positive masses**: the
spin-inclusive signed secants differ by at most `(C Ξ_S²/v_p) [1 + (1 + log(2 + K))/τ]/K³`. -/
theorem cor_stopping_log_galerkin_spin_pos :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (Sp : Type) [Fintype Sp]
      (Ds : Sp → EvoData L H) (ψN : Sp → ℝ → En eta n),
      (∀ σ, ψN σ 0 = ext eta n (Sm eta L (Ds σ).u₀)) →
      (∀ σ s, HasDerivAt (ψN σ) (-(Complex.I • S.galerkinH L n (ψN σ s))) s) →
      ∀ {vp τ : ℝ}, 0 < vp → 0 < τ →
      |(∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds τ σ) -
            ∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds 0 σ)) / (vp * τ) -
          (∑ σ, S.kinExpect (gF L) p₀ (emb eta n (ψN σ τ)) -
            ∑ σ, S.kinExpect (gF L) p₀ (emb eta n (ψN σ 0))) / (vp * τ)| ≤
        C * FSSpin.XiS Ds ^ 2 * ((1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 / vp) := by
  obtain ⟨C, hC, N₀, h⟩ := cor_stopping_log_galerkin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C, hC, N₀, fun n hn p₀ Sp _ Ds ψN hψ0 hψ vp τ hvp hτ => ?_⟩
  have hr : 0 ≤ (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 / vp :=
    div_nonneg (div_nonneg (logQ'_nonneg hL n hτ) (pow_nonneg (Kc_nonneg' hL n) 3)) hvp.le
  simp only [← Finset.sum_sub_distrib, Finset.sum_div]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h n hn p₀ (Ds σ) (ψN σ) (hψ0 σ) (hψ σ) hvp hτ
  calc _ ≤ C * (Ds σ).Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 / vp) := by ring

include hL hKernel hPeriodic in
/-- **`thm:kinetic-log`, grid case with spin, arbitrary positive masses**: one constant for
every measured particle, finite spin set, kernel of the class and grid propagator of `S`. -/
theorem thm_kinetic_log_grid_spin_pos :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) (Sp : Type) [Fintype Sp]
      {κ : Lat3 → ℝ}, IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (S.gridH m κ (2 * Real.pi / L) x) = S.gridH m κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (S.gridH m κ (2 * Real.pi / L) x))) t) →
        ∀ (Ds : Sp → EvoData L H) (t : ℝ), 0 ≤ t →
          |∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds t σ) -
              ∑ σ, S.gridExpect (gF L) p₀ (gridS m Ug Ds t σ)| ≤
            C * FSSpin.XiS Ds ^ 2 * ((1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3) := by
  obtain ⟨C, hC, m₀, h⟩ := thm_kinetic_log_grid_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C, hC, m₀, fun m hm p₀ Sp _ κ hκ Ug hg0 hgcomm hgderiv Ds t ht => ?_⟩
  have hr : 0 ≤ (1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3 :=
    div_nonneg (logQ_nonneg hL m ht) (pow_nonneg (Kc_nonneg' hL m) 3)
  rw [← Finset.sum_sub_distrib]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h m hm p₀ hκ Ug hg0 hgcomm hgderiv (Ds σ) t ht
  calc _ ≤ C * (Ds σ).Xi ^ 2 * (1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3) := by ring

include hL hKernel hPeriodic in
/-- **`cor:stopping-log`, grid case with spin, arbitrary positive masses**. -/
theorem cor_stopping_log_grid_spin_pos :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) (Sp : Type) [Fintype Sp]
      {κ : Lat3 → ℝ}, IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (S.gridH m κ (2 * Real.pi / L) x) = S.gridH m κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (S.gridH m κ (2 * Real.pi / L) x))) t) →
        ∀ (Ds : Sp → EvoData L H) {vp τ : ℝ}, 0 < vp → 0 < τ →
          |(∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds τ σ) -
                ∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds 0 σ)) / (vp * τ) -
              (∑ σ, S.gridExpect (gF L) p₀ (gridS m Ug Ds τ σ) -
                ∑ σ, S.gridExpect (gF L) p₀ (gridS m Ug Ds 0 σ)) / (vp * τ)| ≤
            C * FSSpin.XiS Ds ^ 2 * ((1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 / vp) := by
  obtain ⟨C, hC, m₀, h⟩ := cor_stopping_log_grid_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C, hC, m₀, fun m hm p₀ Sp _ κ hκ Ug hg0 hgcomm hgderiv Ds vp τ hvp hτ => ?_⟩
  have hr : 0 ≤ (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 / vp :=
    div_nonneg (div_nonneg (logQ'_nonneg hL m hτ) (pow_nonneg (Kc_nonneg' hL m) 3)) hvp.le
  simp only [← Finset.sum_sub_distrib, Finset.sum_div]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h m hm p₀ hκ Ug hg0 hgcomm hgderiv (Ds σ) hvp hτ
  calc _ ≤ C * (Ds σ).Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 / vp) := by ring

include hL hKernel hPeriodic in
/-- **eq:kinetic-retained-galerkin with spin, arbitrary positive masses**: one constant for every
finite spin set, `‖(P ⊗ 1) Ψ(t) - Ψ_N(t)‖ ≤ C Ξ_S [1 + t + log(2 + K)]/K³`, `Ψ_N` any solution of
the Galerkin equation of `S` in each spin component. -/
theorem kinetic_retained_galerkin_spin_pos :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (Sp : Type) [Fintype Sp]
      (Ds : Sp → EvoData L H) (ψN : Sp → ℝ → En eta n),
      (∀ σ, ψN σ 0 = ext eta n (Sm eta L (Ds σ).u₀)) →
      (∀ σ s, HasDerivAt (ψN σ) (-(Complex.I • S.galerkinH L n (ψN σ s))) s) →
      ∀ t : ℝ, 0 ≤ t →
      Real.sqrt (∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - emb eta n (ψN σ t)‖ ^ 2) ≤
        C * FSSpin.XiS Ds * ((1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3) := by
  obtain ⟨C, hC, N₀, h⟩ := kinetic_retained_galerkin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C, hC, N₀, fun n hn Sp _ Ds ψN hψ0 hψ t ht => ?_⟩
  set r := (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 with hr
  have hr0 : 0 ≤ r := div_nonneg (logQ_nonneg hL n ht) (pow_nonneg (Kc_nonneg' hL n) 3)
  have hσ : ∀ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - emb eta n (ψN σ t)‖ ≤
      C * r * (Ds σ).Xi := fun σ => by
    have := h n hn (Ds σ) (ψN σ) (hψ0 σ) (hψ σ) t ht
    calc _ ≤ C * (Ds σ).Xi * (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := this
      _ = C * r * (Ds σ).Xi := by rw [hr]; ring
  have hsq : ∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - emb eta n (ψN σ t)‖ ^ 2 ≤
      (C * r * FSSpin.XiS Ds) ^ 2 := by
    calc ∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - emb eta n (ψN σ t)‖ ^ 2
        ≤ ∑ σ, (C * r) ^ 2 * (Ds σ).Xi ^ 2 := Finset.sum_le_sum fun σ _ => by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hσ σ) 2
      _ = (C * r) ^ 2 * ∑ σ, (Ds σ).Xi ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (C * r) ^ 2 * FSSpin.XiS Ds ^ 2 :=
          mul_le_mul_of_nonneg_left (FSSpin.sum_Xi_sq_le Ds) (sq_nonneg _)
      _ = (C * r * FSSpin.XiS Ds) ^ 2 := by ring
  calc Real.sqrt (∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - emb eta n (ψN σ t)‖ ^ 2)
      ≤ Real.sqrt ((C * r * FSSpin.XiS Ds) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = C * r * FSSpin.XiS Ds := Real.sqrt_sq (by have := FSSpin.XiS_nonneg Ds; positivity)
    _ = C * FSSpin.XiS Ds * r := by ring

/-! ## In terms of the number of basis functions -/

include hL hKernel hPeriodic in
/-- **`thm:kinetic-log`, Galerkin case, arbitrary positive masses, in terms of `N`**:
`N = (2n + 1)³` modes per register,
`|⟨ψ(t), T_{p₀} ψ(t)⟩ - ⟨ψ_N(t), T_{p₀} ψ_N(t)⟩| ≤ C 𝒟² [1 + t + log(2 + N)]/N`. -/
theorem thm_kinetic_log_galerkin_pos_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (D : EvoData L H)
      (ψN : ℝ → En eta n), ψN 0 = ext eta n (Sm eta L D.u₀) →
      (∀ s, HasDerivAt ψN (-(Complex.I • S.galerkinH L n (ψN s))) s) → ∀ t : ℝ, 0 ≤ t →
      |S.kinExpect (gF L) p₀ (D.U t (Sm eta L D.u₀)) -
          S.kinExpect (gF L) p₀ (emb eta n (ψN t))| ≤
        C * D.Xi ^ 2 * (1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) /
          (Fintype.card (FinitePlaneWaveMode n) : ℝ) := by
  obtain ⟨C, hC, N₀, h⟩ := thm_kinetic_log_galerkin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1,
    fun n hn p₀ D ψN hψ0 hψ t ht => ?_⟩
  exact (h n (le_trans (le_max_left _ _) hn) p₀ D ψN hψ0 hψ t ht).trans
    (scale_N hC (sq_nonneg _) (basis_N_arith hL (le_trans (le_max_right _ _) hn) ht))

include hL hKernel hPeriodic in
/-- **eq:kinetic-retained-galerkin, arbitrary positive masses, in terms of `N`**:
`‖P ψ(t) - ψ_N(t)‖ ≤ C 𝒟 [1 + t + log(2 + N)]/N`. -/
theorem kinetic_retained_galerkin_pos_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : EvoData L H) (ψN : ℝ → En eta n),
      ψN 0 = ext eta n (Sm eta L D.u₀) →
      (∀ s, HasDerivAt ψN (-(Complex.I • S.galerkinH L n (ψN s))) s) → ∀ t : ℝ, 0 ≤ t →
      ‖molecularH2Truncate n (D.U t (Sm eta L D.u₀)) - emb eta n (ψN t)‖ ≤
        C * D.Xi * (1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) /
          (Fintype.card (FinitePlaneWaveMode n) : ℝ) := by
  obtain ⟨C, hC, N₀, h⟩ := kinetic_retained_galerkin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1, fun n hn D ψN hψ0 hψ t ht => ?_⟩
  exact (h n (le_trans (le_max_left _ _) hn) D ψN hψ0 hψ t ht).trans
    (scale_N hC D.Xi_nonneg (basis_N_arith hL (le_trans (le_max_right _ _) hn) ht))

include hL hKernel hPeriodic in
/-- **`cor:stopping-log`, Galerkin case, arbitrary positive masses, in terms of `N`**: the signed
secants differ by at most `(C 𝒟²/v_p) [1 + (1 + log(2 + N))/τ]/N`. -/
theorem cor_stopping_log_galerkin_pos_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (D : EvoData L H)
      (ψN : ℝ → En eta n), ψN 0 = ext eta n (Sm eta L D.u₀) →
      (∀ s, HasDerivAt ψN (-(Complex.I • S.galerkinH L n (ψN s))) s) → ∀ {vp τ : ℝ}, 0 < vp →
      0 < τ →
      |(S.kinExpect (gF L) p₀ (D.U τ (Sm eta L D.u₀)) -
            S.kinExpect (gF L) p₀ (D.U 0 (Sm eta L D.u₀))) / (vp * τ) -
          (S.kinExpect (gF L) p₀ (emb eta n (ψN τ)) -
            S.kinExpect (gF L) p₀ (emb eta n (ψN 0))) / (vp * τ)| ≤
        C * D.Xi ^ 2 / vp *
          (1 + (1 + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) / τ) /
            (Fintype.card (FinitePlaneWaveMode n) : ℝ) := by
  obtain ⟨C, hC, N₀, h⟩ := cor_stopping_log_galerkin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1,
    fun n hn p₀ D ψN hψ0 hψ vp τ hvp hτ => ?_⟩
  refine (h n (le_trans (le_max_left _ _) hn) p₀ D ψN hψ0 hψ hvp hτ).trans ?_
  have hb := basis_N_arith_stop hL (le_trans (le_max_right _ _) hn) hτ
  have e1 : ∀ c : ℝ, c * D.Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 =
      c * (D.Xi ^ 2 / vp) * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 := fun c => by ring
  rw [e1]
  refine (scale_N hC (div_nonneg (sq_nonneg _) hvp.le) hb).trans (le_of_eq ?_)
  ring

include hL hKernel hPeriodic in
/-- **`thm:kinetic-log`, grid case, arbitrary positive masses, in terms of `N`**: for the
unpadded admissible size `n = 2m + 1` (`N = (2m + 1)³`),
`|⟨ψ(t), T_{p₀} ψ(t)⟩ - ⟨ψ_g(t), T_{p₀} ψ_g(t)⟩| ≤ C 𝒟² [1 + t + log(2 + N)]/N`. -/
theorem thm_kinetic_log_grid_pos_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) {κ : Lat3 → ℝ},
      IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (S.gridH m κ (2 * Real.pi / L) x) = S.gridH m κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (S.gridH m κ (2 * Real.pi / L) x))) t) →
        ∀ (D : EvoData L H) (t : ℝ), 0 ≤ t →
          |S.kinExpect (gF L) p₀ (D.U t (Sm eta L D.u₀)) -
              S.gridExpect (gF L) p₀ (Ug t (regCoeff m (Sm eta L D.u₀)))| ≤
            C * D.Xi ^ 2 * (1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode m) : ℝ))) /
              (Fintype.card (FinitePlaneWaveMode m) : ℝ) := by
  obtain ⟨C, hC, m₀, h⟩ := thm_kinetic_log_grid_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max m₀ 1,
    fun m hm p₀ κ hκ Ug hg0 hgcomm hgderiv D t ht => ?_⟩
  exact (h m (le_trans (le_max_left _ _) hm) p₀ hκ Ug hg0 hgcomm hgderiv D t ht).trans
    (scale_N hC (sq_nonneg _) (basis_N_arith hL (le_trans (le_max_right _ _) hm) ht))

include hL hKernel hPeriodic in
/-- **`cor:stopping-log`, grid case, arbitrary positive masses, in terms of `N`**. -/
theorem cor_stopping_log_grid_pos_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) {κ : Lat3 → ℝ},
      IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (S.gridH m κ (2 * Real.pi / L) x) = S.gridH m κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (S.gridH m κ (2 * Real.pi / L) x))) t) →
        ∀ (D : EvoData L H) {vp τ : ℝ}, 0 < vp → 0 < τ →
          |(S.kinExpect (gF L) p₀ (D.U τ (Sm eta L D.u₀)) -
                S.kinExpect (gF L) p₀ (D.U 0 (Sm eta L D.u₀))) / (vp * τ) -
              (S.gridExpect (gF L) p₀ (Ug τ (regCoeff m (Sm eta L D.u₀))) -
                S.gridExpect (gF L) p₀ (Ug 0 (regCoeff m (Sm eta L D.u₀)))) / (vp * τ)| ≤
            C * D.Xi ^ 2 / vp *
              (1 + (1 + Real.log (2 + (Fintype.card (FinitePlaneWaveMode m) : ℝ))) / τ) /
                (Fintype.card (FinitePlaneWaveMode m) : ℝ) := by
  obtain ⟨C, hC, m₀, h⟩ := cor_stopping_log_grid_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max m₀ 1,
    fun m hm p₀ κ hκ Ug hg0 hgcomm hgderiv D vp τ hvp hτ => ?_⟩
  refine (h m (le_trans (le_max_left _ _) hm) p₀ hκ Ug hg0 hgcomm hgderiv D hvp hτ).trans ?_
  have hb := basis_N_arith_stop hL (le_trans (le_max_right _ _) hm) hτ
  have e1 : ∀ c : ℝ, c * D.Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 =
      c * (D.Xi ^ 2 / vp) * (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 := fun c => by ring
  rw [e1]
  refine (scale_N hC (div_nonneg (sq_nonneg _) hvp.le) hb).trans (le_of_eq ?_)
  ring


include hL hKernel hPeriodic in
/-- **eq:kinetic-retained-galerkin with spin, arbitrary positive masses, in terms of `N`**. -/
theorem kinetic_retained_galerkin_spin_pos_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (Sp : Type) [Fintype Sp]
      (Ds : Sp → EvoData L H) (ψN : Sp → ℝ → En eta n),
      (∀ σ, ψN σ 0 = ext eta n (Sm eta L (Ds σ).u₀)) →
      (∀ σ s, HasDerivAt (ψN σ) (-(Complex.I • S.galerkinH L n (ψN σ s))) s) →
      ∀ t : ℝ, 0 ≤ t →
      Real.sqrt (∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - emb eta n (ψN σ t)‖ ^ 2) ≤
        C * FSSpin.XiS Ds * ((1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) /
          (Fintype.card (FinitePlaneWaveMode n) : ℝ)) := by
  obtain ⟨C, hC, N₀, h⟩ := kinetic_retained_galerkin_spin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1,
    fun n hn Sp _ Ds ψN hψ0 hψ t ht => ?_⟩
  exact (h n (le_trans (le_max_left _ _) hn) Sp Ds ψN hψ0 hψ t ht).trans
    (scale_N' hC (FSSpin.XiS_nonneg Ds) (basis_N_arith hL (le_trans (le_max_right _ _) hn) ht))

include hL hKernel hPeriodic in
/-- **`thm:kinetic-log`, Galerkin case with spin, arbitrary positive masses, in terms of `N`**. -/
theorem thm_kinetic_log_galerkin_spin_pos_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (Sp : Type) [Fintype Sp]
      (Ds : Sp → EvoData L H) (ψN : Sp → ℝ → En eta n),
      (∀ σ, ψN σ 0 = ext eta n (Sm eta L (Ds σ).u₀)) →
      (∀ σ s, HasDerivAt (ψN σ) (-(Complex.I • S.galerkinH L n (ψN σ s))) s) →
      ∀ t : ℝ, 0 ≤ t →
      |∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds t σ) -
          ∑ σ, S.kinExpect (gF L) p₀ (emb eta n (ψN σ t))| ≤
        C * FSSpin.XiS Ds ^ 2 *
          ((1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) /
            (Fintype.card (FinitePlaneWaveMode n) : ℝ)) := by
  obtain ⟨C, hC, N₀, h⟩ := thm_kinetic_log_galerkin_spin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1,
    fun n hn p₀ Sp _ Ds ψN hψ0 hψ t ht => ?_⟩
  exact (h n (le_trans (le_max_left _ _) hn) p₀ Sp Ds ψN hψ0 hψ t ht).trans
    (scale_N' hC (sq_nonneg _) (basis_N_arith hL (le_trans (le_max_right _ _) hn) ht))

include hL hKernel hPeriodic in
/-- **`cor:stopping-log`, Galerkin case with spin, arbitrary positive masses, in terms of `N`**. -/
theorem cor_stopping_log_galerkin_spin_pos_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (Sp : Type) [Fintype Sp]
      (Ds : Sp → EvoData L H) (ψN : Sp → ℝ → En eta n),
      (∀ σ, ψN σ 0 = ext eta n (Sm eta L (Ds σ).u₀)) →
      (∀ σ s, HasDerivAt (ψN σ) (-(Complex.I • S.galerkinH L n (ψN σ s))) s) →
      ∀ {vp τ : ℝ}, 0 < vp → 0 < τ →
      |(∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds τ σ) -
            ∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds 0 σ)) / (vp * τ) -
          (∑ σ, S.kinExpect (gF L) p₀ (emb eta n (ψN σ τ)) -
            ∑ σ, S.kinExpect (gF L) p₀ (emb eta n (ψN σ 0))) / (vp * τ)| ≤
        C * FSSpin.XiS Ds ^ 2 *
          ((1 + (1 + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) / τ) /
            (Fintype.card (FinitePlaneWaveMode n) : ℝ) / vp) := by
  obtain ⟨C, hC, N₀, h⟩ := cor_stopping_log_galerkin_spin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1,
    fun n hn p₀ Sp _ Ds ψN hψ0 hψ vp τ hvp hτ => ?_⟩
  refine (h n (le_trans (le_max_left _ _) hn) p₀ Sp Ds ψN hψ0 hψ hvp hτ).trans ?_
  have hb := basis_N_arith_stop hL (le_trans (le_max_right _ _) hn) hτ
  have e1 : C * FSSpin.XiS Ds ^ 2 * ((1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 / vp) =
      C * (FSSpin.XiS Ds ^ 2 / vp) * ((1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3) := by
    ring
  rw [e1]
  refine (scale_N' hC (div_nonneg (sq_nonneg _) hvp.le) hb).trans (le_of_eq ?_)
  ring

include hL hKernel hPeriodic in
/-- **`thm:kinetic-log`, grid case with spin, arbitrary positive masses, in terms of `N`**. -/
theorem thm_kinetic_log_grid_spin_pos_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) (Sp : Type) [Fintype Sp]
      {κ : Lat3 → ℝ}, IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (S.gridH m κ (2 * Real.pi / L) x) = S.gridH m κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (S.gridH m κ (2 * Real.pi / L) x))) t) →
        ∀ (Ds : Sp → EvoData L H) (t : ℝ), 0 ≤ t →
          |∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds t σ) -
              ∑ σ, S.gridExpect (gF L) p₀ (gridS m Ug Ds t σ)| ≤
            C * FSSpin.XiS Ds ^ 2 *
              ((1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode m) : ℝ))) /
                (Fintype.card (FinitePlaneWaveMode m) : ℝ)) := by
  obtain ⟨C, hC, m₀, h⟩ := thm_kinetic_log_grid_spin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max m₀ 1,
    fun m hm p₀ Sp _ κ hκ Ug hg0 hgcomm hgderiv Ds t ht => ?_⟩
  exact (h m (le_trans (le_max_left _ _) hm) p₀ Sp hκ Ug hg0 hgcomm hgderiv Ds t ht).trans
    (scale_N' hC (sq_nonneg _) (basis_N_arith hL (le_trans (le_max_right _ _) hm) ht))

include hL hKernel hPeriodic in
/-- **`cor:stopping-log`, grid case with spin, arbitrary positive masses, in terms of `N`**. -/
theorem cor_stopping_log_grid_spin_pos_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) (Sp : Type) [Fintype Sp]
      {κ : Lat3 → ℝ}, IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (S.gridH m κ (2 * Real.pi / L) x) = S.gridH m κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (S.gridH m κ (2 * Real.pi / L) x))) t) →
        ∀ (Ds : Sp → EvoData L H) {vp τ : ℝ}, 0 < vp → 0 < τ →
          |(∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds τ σ) -
                ∑ σ, S.kinExpect (gF L) p₀ (FSSpin.exactS Ds 0 σ)) / (vp * τ) -
              (∑ σ, S.gridExpect (gF L) p₀ (gridS m Ug Ds τ σ) -
                ∑ σ, S.gridExpect (gF L) p₀ (gridS m Ug Ds 0 σ)) / (vp * τ)| ≤
            C * FSSpin.XiS Ds ^ 2 *
              ((1 + (1 + Real.log (2 + (Fintype.card (FinitePlaneWaveMode m) : ℝ))) / τ) /
                (Fintype.card (FinitePlaneWaveMode m) : ℝ) / vp) := by
  obtain ⟨C, hC, m₀, h⟩ := cor_stopping_log_grid_spin_pos S hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max m₀ 1,
    fun m hm p₀ Sp _ κ hκ Ug hg0 hgcomm hgderiv Ds vp τ hvp hτ => ?_⟩
  refine (h m (le_trans (le_max_left _ _) hm) p₀ Sp hκ Ug hg0 hgcomm hgderiv Ds hvp hτ).trans ?_
  have hb := basis_N_arith_stop hL (le_trans (le_max_right _ _) hm) hτ
  have e1 : C * FSSpin.XiS Ds ^ 2 * ((1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 / vp) =
      C * (FSSpin.XiS Ds ^ 2 / vp) * ((1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3) := by
    ring
  rw [e1]
  refine (scale_N' hC (div_nonneg (sq_nonneg _) hvp.le) hb).trans (le_of_eq ?_)
  ring

end Endpoints

end KineticLog
