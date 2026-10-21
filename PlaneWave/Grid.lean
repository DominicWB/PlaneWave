import PlaneWave.Certificate
import PlaneWave.GridCore

/-!
# PlaneWaveGrid release: grid energy, grid dynamics, full kernel (Lean 4.32.1, Mathlib v4.32.1)

Connects `PlaneWave.GridCore` to the PlaneWaveCertificate release file: for a
periodic Coulomb system the register Galerkin Hamiltonian is the release file's finite
Hamiltonian at radius `2m` (up to a unitary reindexing), so the release theorem's cubic Ritz
energy at cutoff `2K` is the Galerkin Ritz energy of the core.

Main results, for every periodic Coulomb system `sys` (quantum particles with masses at least
one and charges, fermions and bosons, and static nuclei):

* `PlaneWaveGrid.periodicCoulombSectorGridError`: in the exchange sector of any admissible
  labelling `lab`, the ground pair `(ψ, E)` of the release file and, for every
  `m ≥ coulombGridThreshold sys L`, the grid ground energy `Eg` of the padded collocation
  method (`n' = 4m+1` points per direction, kernel `w_{≤2K}`, `K = (2π/L) m`) satisfy
  `|Eg - E| ≤ coulombGridErrorConstant sys L / K³` and
  `|Eg - E| ≤ coulombGridBasisErrorConstant sys L / (2m+1)³`;
* `PlaneWaveGrid.periodicCoulombGridError`: the same on the spin-inclusive space
  `L²((T³)^η; ⊗_a ℂ^{d_a})`, with spin-dependent grid states that change by the exchange sign
  of the species under simultaneous exchange of the grid positions and spins of two particles
  of one species, and whose components with a spin value at or above the multiplicity of its
  species vanish.

The theorems with `Kernel` in their names (`periodicCoulombSectorKernelGridError`,
`periodicCoulombKernelGridError`) state the same for every kernel of the class `𝒦_K` of the
manuscript (`IsGridKernel`: real, even Fourier coefficients bounded by `γ/|ν|²`, equal to it for
`‖k_ν‖ ≤ K` and zero beyond `‖k_ν‖∞ = 2K`), with the same threshold and constants; the
statements for `w_{≤2K}` are their instances at `sharpKernel`. The Born--Oppenheimer theorems
`periodicMolecularGridError` (electronic space `Λ^η(L²(T³) ⊗ ℂ²)`) and
`periodicMolecularSectorGridError` (exchange sector of any `lab`), and their `Kernel`
versions, are these theorems at the system `CoulombSystem.bo eta data` of electrons and
clamped nuclei. The constants and the threshold depend only on the system and `L`, and not on
the sector or the kernel. Part `PolynomialBounds` bounds them by polynomials in `η`, the
largest mass and the charge weight (`coulombGridErrorConstant_le_poly`,
`coulombGridThreshold_le_poly`, and for the Born--Oppenheimer problem
`gridErrorConstant_le_poly`, `gridThreshold_le_poly`).

Since 2026-10-12 this file also holds the grid parts of the manuscript's dynamical results and
full-kernel collocation, merged from development files. Part II of the release file describes the
merge; here the namespaces of the development files are renamed as follows: `GridDynTest` to
`PlaneWaveGridDynamics`, `FullKernelTest` to `PlaneWaveFullKernel`, `KineticTest` to
`PlaneWaveKinetic` and `SpinTest` to `PlaneWaveSpin`. Section `DevGD2` also adds five lemmas to
the namespace `PlaneWaveGrid.RegHam` of the core (`norm_kin_le`, `op_le`, `elliptic_gen`,
`flow_le`, `flow_le_weight`).

* Part `FullKernel` (namespace `PlaneWaveFullKernel`): `prop:fullkernel` in every sector
  (`periodicCoulombSectorFullKernelError`), on the spin-inclusive space
  (`periodicCoulombFullKernelError`) and for the Born--Oppenheimer problem
  (`periodicMolecularSectorFullKernelError`, `periodicMolecularFullKernelError`), with polynomial
  bounds on its constants and threshold (`fullKernelErrorConstant_le_poly`,
  `fullKernelBasisErrorConstant_le_poly`, `fullKernelThreshold_le_poly`,
  `fullKernelImpConstant₁_le_poly`, `fullKernelImpConstant₂_le_poly` and their Born--Oppenheimer
  forms `fullKernelErrorConstant_le_poly_bo`, `fullKernelBasisErrorConstant_le_poly_bo`,
  `fullKernelThreshold_le_poly_bo`, `fullKernelImpConstant₁_le_poly_bo`,
  `fullKernelImpConstant₂_le_poly_bo`), the bounds of the grid theorem in the same variable
  (`coulombGridErrorConstant_le_polyVar`, `coulombGridThreshold_le_polyVar`), and
  `fullKernelCorrSummable_exists` (at a single size the summability hypothesis always holds for
  some constant; its content is the uniformity in `m`).
* Part `GridDynamics` (namespace `PlaneWaveGridDynamics`): the grid propagator
  (`exists_posPropagator`), `prop:grid-dyn` (`thm_grid_dyn`, `thm_grid_dyn_min`, and the
  normalised grid state `grid_observable_normalised` with `grid_normalisation_threshold`) and
  `thm:grid-dyn-sharp` (`thm_grid_dyn_sharp`, `thm_grid_dyn_sharp_min`), for every kernel of the
  class.
* Part `KineticGrid` (namespace `PlaneWaveKinetic`): `prop:mult-grid` (`thm_mult_grid`), the grid
  form of `thm:mult-cap` (`thm_mult_cap_grid`) and of the corollaries (`stopping_grid`,
  `stopping_window_grid`).
* Part `SpinGrid` (namespace `PlaneWaveSpin`): the same on the spin-inclusive grid states, with the
  same constants at the spin-inclusive norms (`thm_grid_dyn_spin`, `thm_grid_dyn_min_spin`,
  `thm_grid_dyn_sharp_spin`, `thm_grid_dyn_sharp_min_spin`, `grid_observable_normalised_spin`,
  `grid_normalisation_threshold_spin`, `thm_mult_grid_spin`, `thm_mult_cap_grid_spin`,
  `stopping_grid_spin`, `stopping_window_grid_spin`).

The axiom reports of these 38 entry points are in `AxiomCheck.lean`, after those of the grid
theorems. One theorem of the development files was removed as a duplicate (`norm_wTot_le`; its
uses now name the core's `norm_wMul_wTot_le`); the release file's header lists the others and
the declarations the entry points do not use.
-/

/-! ════════════════════════════════════════════════════════════════════
## Part `Bridge`
════════════════════════════════════════════════════════════════════ -/

/-!
# Bridge to the periodic Coulomb certificate

We identify the register Galerkin operator `Hgal` (radius `2m`) of a Coulomb system with the
release file's `finiteCoulombHamiltonian sys L (2m)`, transport the cubic Ritz energy of the
release theorem at cutoff `2K`, and combine it with the finite comparison and the collocation
identity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PlaneWaveGrid

open Finset PlaneWaveCertificate

section Identification

variable {eta : ℕ} {ν : Type*} [Fintype ν]

/-- Positioned nuclei from the release file's nuclear data. -/
def posNucleiOf (data : FiniteBONuclearData ν) : PosNuclei ν where
  charge := data.charge
  charge_nonneg := data.charge_nonneg
  position := data.position

/-- The quantum particles of a Coulomb system on the register. -/
def regParticlesOf (sys : CoulombSystem eta ν) : RegParticles eta where
  mass := sys.mass
  one_le_mass := sys.one_le_mass
  charge := sys.charge

@[simp] lemma regParticlesOf_mass (sys : CoulombSystem eta ν) :
    (regParticlesOf sys).mass = sys.mass := rfl

@[simp] lemma regParticlesOf_charge (sys : CoulombSystem eta ν) :
    (regParticlesOf sys).charge = sys.charge := rfl

lemma nsq_eq_latticeNormSq (x : Lat3) : nsq x = latticeNormSq x := rfl

lemma latticeSub_eq (a b : Lattice3) : latticeSub a b = a - b := by
  funext i; simp [latticeSub]

/-- The release file's finite modes of radius `M` are the register modes. -/
noncomputable def modeEquiv (M : ℕ) : FinitePlaneWaveMode M ≃ GMode (2 * M + 1) := by
  classical
  refine Equiv.ofBijective (fun v => ofLat (finitePlaneWaveLatticeIndex M v)) ?_
  have hbox : ∀ v, InBox M (finitePlaneWaveLatticeIndex M v) := by
    intro v c
    have h := finitePlaneWaveLatticeIndex_coord_bounds M v c
    rw [abs_le]
    exact ⟨by simpa using h.1, by simpa using h.2⟩
  have hinj : Function.Injective (fun v => ofLat (M := M) (finitePlaneWaveLatticeIndex M v)) := by
    intro v w h
    have h2 : gl (ofLat (M := M) (finitePlaneWaveLatticeIndex M v)) =
        gl (ofLat (M := M) (finitePlaneWaveLatticeIndex M w)) := congrArg gl h
    rw [gl_ofLat (hbox v), gl_ofLat (hbox w)] at h2
    exact finitePlaneWaveLatticeIndex_injective M h2
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  rw [finitePlaneWaveMode_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma gl_modeEquiv (M : ℕ) (v : FinitePlaneWaveMode M) :
    gl (modeEquiv M v) = finitePlaneWaveLatticeIndex M v := by
  have hbox : InBox M (finitePlaneWaveLatticeIndex M v) := by
    intro c
    have h := finitePlaneWaveLatticeIndex_coord_bounds M v c
    rw [abs_le]
    exact ⟨by simpa using h.1, by simpa using h.2⟩
  exact gl_ofLat hbox

/-- Configurations: release modes to register modes. -/
noncomputable def cfgEquiv (eta M : ℕ) :
    FourierConfig eta (FinitePlaneWaveMode M) ≃ GConfig eta (2 * M + 1) :=
  Equiv.arrowCongr (Equiv.refl _) (modeEquiv M)

lemma cfgEquiv_apply (eta M : ℕ) (p : FourierConfig eta (FinitePlaneWaveMode M)) (i : Fin eta) :
    cfgEquiv eta M p i = modeEquiv M (p i) := rfl

/-- The lifted lattice configuration of a register configuration. -/
def liftCfg {M : ℕ} (q : GConfig eta (2 * M + 1)) : FourierConfig eta Lattice3 :=
  fun i => gl (q i)

lemma liftCfg_cfgEquiv (eta M : ℕ) (p : FourierConfig eta (FinitePlaneWaveMode M)) :
    liftCfg (cfgEquiv eta M p) = finiteConfigLatticeIndex eta M p := by
  funext i
  simp [liftCfg, cfgEquiv_apply, gl_modeEquiv, finiteConfigLatticeIndex]

lemma liftCfg_injective {M : ℕ} :
    Function.Injective (liftCfg : GConfig eta (2 * M + 1) → FourierConfig eta Lattice3) := by
  intro q p h
  funext i
  exact gl_injective (congrFun h i)

/-- A nuclear Galerkin term is the release file's lattice kernel of the interaction of one
particle to one nucleus. -/
lemma galTerm_nuclear_eq_lattice (m : ℕ) (L : ℝ) (hL : 0 < L) (data : FiniteBONuclearData ν)
    (i : Fin eta) (l : ν) (q p : RCfg eta m) :
    galTerm eta m (posNucleiOf data).toNucData (coulombCellAmplitude L) (Sum.inr (i, l)) q p =
      latticeReferenceConfigurationKernel i
        (latticeElectronNuclearKernel data (coulombCellAmplitude L) l) (liftCfg q)
        (liftCfg p) := by
  classical
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  simp only [galTerm]
  unfold latticeReferenceConfigurationKernel
  by_cases h : Spec1 (M := 2 * m) i q p
  · have h' : ∀ k : Fin eta, k ≠ i → liftCfg q k = liftCfg p k :=
      fun k hk => by simp [liftCfg, h k hk]
    rw [tk_of_rel h, if_pos h']
    simp only [latticeElectronNuclearKernel, knuc, PosNuclei.toNucData, posNucleiOf, kee,
      wTau, liftCfg, latticeSub_eq]
    rw [latticeCoulombKernel_of_amplitude_sq _ hγ, latticeSub_eq]
    simp [coul, nsq_eq_latticeNormSq, div_eq_mul_inv]
  · have h' : ¬ ∀ k : Fin eta, k ≠ i → liftCfg q k = liftCfg p k := by
      intro hh
      exact h fun k hk => gl_injective (hh k hk)
    rw [tk_of_not_rel h, if_neg h']

/-- A pair Galerkin term is the release file's lattice pair kernel (the release file's
`FiniteElectronPair` is the same subtype as `Pairs`). -/
lemma galTerm_pair_eq_lattice (m : ℕ) (L : ℝ) (hL : 0 < L) (D : NucData ν) (pr : Pairs eta)
    (q p : RCfg eta m) :
    galTerm eta m D (coulombCellAmplitude L) (Sum.inl pr) q p =
      latticeElectronPairConfigurationKernel pr.1.1 pr.1.2 (coulombCellAmplitude L ^ 2)
        (liftCfg q) (liftCfg p) := by
  classical
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  simp only [galTerm]
  unfold latticeElectronPairConfigurationKernel
  by_cases h : wRel2 (M := 2 * m) pr.1.1 pr.1.2 q p
  · have h' : (∀ k : Fin eta, k ≠ pr.1.1 → k ≠ pr.1.2 → liftCfg q k = liftCfg p k) ∧
        liftCfg q pr.1.1 + liftCfg q pr.1.2 = liftCfg p pr.1.1 + liftCfg p pr.1.2 :=
      ⟨fun k hk1 hk2 => by simp [liftCfg, h.1 k hk1 hk2], h.2⟩
    rw [tk_of_rel h, if_pos h']
    simp only [kee, wTau, liftCfg]
    rw [latticeCoulombKernel_of_amplitude_sq _ hγ, latticeSub_eq]
    simp [coul, nsq_eq_latticeNormSq, div_eq_mul_inv]
  · have h' : ¬ ((∀ k : Fin eta, k ≠ pr.1.1 → k ≠ pr.1.2 → liftCfg q k = liftCfg p k) ∧
        liftCfg q pr.1.1 + liftCfg q pr.1.2 = liftCfg p pr.1.1 + liftCfg p pr.1.2) := by
      rintro ⟨hh1, hh2⟩
      exact h ⟨fun k hk1 hk2 => gl_injective (hh1 k hk1 hk2), hh2⟩
    rw [tk_of_not_rel h, if_neg h']

/-- The register Galerkin Hamiltonian of a Coulomb system equals the release file's lattice
kernel. -/
lemma Hgal_eq_coulombLatticeKernel (sys : CoulombSystem eta ν) (m : ℕ) (L : ℝ) (hL : 0 < L) :
    Hgal eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
        (2 * Real.pi / L) =
      kOp (fun q p => coulombLatticeHamiltonianKernel sys L (liftCfg q) (liftCfg p)) := by
  classical
  apply LinearMap.ext
  intro u
  ext q
  simp only [Hgal, LinearMap.add_apply, PiLp.add_apply, wMul_apply, kOp_apply,
    coulombLatticeHamiltonianKernel, mul_add, Finset.sum_add_distrib]
  -- kinetic part
  have hk : kinT eta m (regParticlesOf sys) (2 * Real.pi / L) q =
      1 / 2 * ∑ i : Fin eta, (2 * Real.pi / L) ^ 2 * latticeNormSq (liftCfg q i) /
        sys.mass i := by
    simp only [kinT, wM, liftCfg, add_sub_cancel_left, Finset.mul_sum, nsq_eq_latticeNormSq,
      regParticlesOf_mass]
    exact sum_congr rfl fun i _ => by ring
  have hkin : (kinT eta m (regParticlesOf sys) (2 * Real.pi / L) q : ℂ) * u q =
      ∑ p, u p * coulombLatticeKineticKernel sys L (liftCfg q) (liftCfg p) := by
    have hEq : ∀ p, liftCfg p = liftCfg q ↔ p = q := fun p => liftCfg_injective.eq_iff
    simp only [coulombLatticeKineticKernel, hEq, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [hk]
    push_cast
    ring
  rw [hkin]
  congr 1
  -- potential part: register Galerkin terms versus lattice kernel
  unfold vGalK coulombLatticeNuclearKernel coulombLatticePairKernel
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Fintype.sum_equiv (Equiv.refl _) _ _ fun p => ?_
  rw [Equiv.refl_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, add_comm]
  congr 1
  · refine sum_congr rfl fun i _ => sum_congr rfl fun l _ => ?_
    rw [galTerm_nuclear_eq_lattice m L hL sys.nuclei i l q p]
    simp only [RegParticles.tcoef, regParticlesOf_charge]
  · refine Fintype.sum_equiv (Equiv.refl _) _ _ fun pr => ?_
    rw [Equiv.refl_apply, galTerm_pair_eq_lattice m L hL _ pr q p]
    simp only [RegParticles.tcoef, regParticlesOf_charge]

/-- The unitary reindexing between the release file's coefficient space and the register. -/
noncomputable def regUnitary (eta M : ℕ) :
    EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode M)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (GConfig eta (2 * M + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cfgEquiv eta M)

lemma regUnitary_apply (eta M : ℕ)
    (u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode M)))
    (p : FourierConfig eta (FinitePlaneWaveMode M)) :
    regUnitary eta M u (cfgEquiv eta M p) = u p := by
  simp [regUnitary, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

end Identification

section Transfer

variable {eta : ℕ} {ν : Type*} [Fintype ν]

lemma swapCfg_cfgEquiv (eta M : ℕ) (a b : Fin eta)
    (p : FourierConfig eta (FinitePlaneWaveMode M)) :
    swapCfg a b (cfgEquiv eta M p) = cfgEquiv eta M (swapConfig a b p) := by
  funext k
  rfl

lemma regUnitary_swap (eta M : ℕ)
    (u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode M)))
    (a b : Fin eta) (p : FourierConfig eta (FinitePlaneWaveMode M)) :
    regUnitary eta M u (swapCfg a b (cfgEquiv eta M p)) = u (swapConfig a b p) := by
  rw [swapCfg_cfgEquiv, regUnitary_apply]

lemma isSec_regUnitary_iff (eta M : ℕ) (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ)
    (u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode M))) :
    IsSec sgn lab (regUnitary eta M u) ↔ IsSectorVector sgn lab u := by
  constructor
  · intro h a b hab hlab p
    have := h a b hab hlab (cfgEquiv eta M p)
    rw [regUnitary_swap, regUnitary_apply] at this
    exact this
  · intro h a b hab hlab q
    obtain ⟨p, rfl⟩ := (cfgEquiv eta M).surjective q
    rw [regUnitary_swap, regUnitary_apply]
    exact h a b hab hlab p

/-- `Hgal` is the release file's finite Hamiltonian of the Coulomb system at radius `2m`, up
to reindexing. -/
lemma Hgal_regUnitary (sys : CoulombSystem eta ν) (m : ℕ) (L : ℝ) (hL : 0 < L)
    (u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode (2 * m)))) :
    Hgal eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
        (2 * Real.pi / L) (regUnitary eta (2 * m) u) =
      regUnitary eta (2 * m) (finiteCoulombHamiltonian sys L (2 * m) u) := by
  rw [Hgal_eq_coulombLatticeKernel sys m L hL, finiteCoulombHamiltonian_eq_latticeKernel]
  ext q
  obtain ⟨p, rfl⟩ := (cfgEquiv eta (2 * m)).surjective q
  rw [regUnitary_apply, kOp_apply, finiteCoefficientKernelOperator_apply]
  symm
  refine Fintype.sum_equiv (cfgEquiv eta (2 * m)) _ _ fun p' => ?_
  rw [regUnitary_apply, liftCfg_cfgEquiv, liftCfg_cfgEquiv]

/-- The release file's cubic Ritz energy at cutoff `2K` is the register Galerkin Ritz
energy. -/
lemma galRitz_of_cubic (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ) (m : ℕ) (L : ℝ)
    (hL : 0 < L) (EN : ℝ)
    (hEN : IsSectorCubicGalerkinGroundEnergy eta sys.sign lab
      ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) (2 * Real.pi / L) (2 * m)
      (finiteCoulombHamiltonian sys L (2 * m)) EN) :
    IsSecRitz sys.sign lab (Hgal eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) (2 * Real.pi / L)) EN := by
  constructor
  · intro v hv
    obtain ⟨w, rfl⟩ := (regUnitary eta (2 * m)).surjective v
    have hw : IsSectorVector sys.sign lab w :=
      (isSec_regUnitary_iff eta (2 * m) sys.sign lab w).mp hv
    have h := hEN.1 w hw (isCubicRetainedVector_physical_full_horizon eta L hL (2 * m) w)
    rw [Hgal_regUnitary sys m L hL, LinearIsometryEquiv.inner_map_map,
      LinearIsometryEquiv.norm_map]
    exact h
  · obtain ⟨phi, hF, _hC, hn, hv⟩ := hEN.2
    refine ⟨regUnitary eta (2 * m) phi,
      (isSec_regUnitary_iff eta (2 * m) sys.sign lab phi).mpr hF,
      by rw [LinearIsometryEquiv.norm_map, hn], ?_⟩
    rw [Hgal_regUnitary sys m L hL, LinearIsometryEquiv.inner_map_map]
    exact hv

/-- Every exchange sector of an admissible labelling contains a nonzero register state once
`m ≥ η`. -/
lemma exists_nonzero_sec (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ}
    (hlab : sys.IsAdmissible lab) (m : ℕ) (hm : eta ≤ m) :
    ∃ u : EuclideanSpace ℂ (RCfg eta m), IsSec sys.sign lab u ∧ u ≠ 0 := by
  have hcard : eta ≤ (Finset.univ : Finset (GMode (2 * (2 * m) + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    calc eta ≤ m := hm
      _ ≤ 2 * (2 * m) + 1 := by omega
      _ ≤ (2 * (2 * m) + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨u, hS, hu0, -⟩ := sys.exists_nonzero_sectorVector_supported_of_card hlab
    (μ := GMode (2 * (2 * m) + 1)) Finset.univ hcard
  exact ⟨u, hS, hu0⟩

end Transfer

section Final

variable {eta : ℕ} {ν : Type*} [Fintype ν]

/-- The grid ground energy of a Coulomb system in the exchange sector `lab` for the kernel
with coefficients `κ`: the Ritz energy of the padded collocation Hamiltonian `Hpos`
(`n' = 4m+1` points per direction, kernel `wKer κ m`, `K = (2π/L) m`) on grid functions in
that sector. -/
def IsCoulombSectorKernelGridGroundEnergy (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (L : ℝ) (m : ℕ) (κ : Lat3 → ℝ) (Eg : ℝ) : Prop :=
  IsSecRitz sys.sign lab (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
    (2 * Real.pi / L)) Eg

/-- The grid ground energy of a Coulomb system in the exchange sector `lab` for the truncated
kernel `w_{≤2K}` (coefficients `sharpKernel γ_L m`). -/
def IsCoulombSectorGridGroundEnergy (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ) (L : ℝ)
    (m : ℕ) (Eg : ℝ) : Prop :=
  IsCoulombSectorKernelGridGroundEnergy sys lab L m (sharpKernel (coulombCellAmplitude L) m) Eg

/-- The coupling `m̄ Σ_t |c_t| γ_t` of the register potential of a Coulomb system. -/
noncomputable def coulombGridCoupling (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  sys.maxMass * Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (coulombCellAmplitude L)

/-- Energy budget for the Galerkin ground energies at cutoff `2K`: the continuum budget plus
one, since above the threshold the cutoff error `C/(2K)³` is at most one. -/
noncomputable def coulombGridEnergyBudget (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  coulombGroundEnergyBudget sys L + 1

/-- The size threshold of the grid theorem: eight more than the largest of the cutoff
threshold (applied at `2m`), `η`, the size `C^{1/3}/(2g)` above which the cutoff error
`C/(2gm)³` is at most one (`C` the cutoff constant, `g = 2π/L`), and four times the size
`2 √(m̄ E_big)/g` of the bootstrap condition `4 m̄ E_big ≤ g² s²` at the tail threshold
`s = ⌊m/4⌋`. -/
noncomputable def coulombGridThreshold (sys : CoulombSystem eta ν) (L : ℝ) : ℕ :=
  max (coulombDataCubicThreshold sys L)
    (max eta (max (Nat.ceil (coulombDataCubicErrorConstant sys L ^ ((1 : ℝ) / 3) /
        (2 * (2 * Real.pi / L))))
      (4 * Nat.ceil (2 * Real.sqrt (sys.maxMass * Ebig sys.maxMass (coulombGridCoupling sys L)
        (2 * Real.pi / L) (coulombGridEnergyBudget sys L)) / (2 * Real.pi / L))))) + 8

/-- The error constant of the grid theorem: `512 g³ C_grid + C/8`, with the finite comparison
constant `C_grid` of the core (at the tail threshold `s = ⌊m/4⌋ ≥ m/8`) and the cutoff
constant `C` at cutoff `2K`. -/
noncomputable def coulombGridErrorConstant (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  512 * (2 * Real.pi / L) ^ 3 * Cgrid sys.maxMass (coulombGridCoupling sys L) (2 * Real.pi / L)
      (coulombGridEnergyBudget sys L) +
    coulombDataCubicErrorConstant sys L / 8

/-- The error constant in basis-count form, `N = (2m+1)³` the kernel-resolution count. -/
noncomputable def coulombGridBasisErrorConstant (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  27 * coulombGridErrorConstant sys L / (2 * Real.pi / L) ^ 3

lemma Ebig_nonneg {M Z g Eb : ℝ} (hZ : 0 ≤ Z) : 0 ≤ Ebig M Z g Eb := by
  unfold Ebig
  refine le_trans ?_ (le_max_left _ _)
  have := J0g_pos Z g
  positivity

end Final

end PlaneWaveGrid

/-! ════════════════════════════════════════════════════════════════════
## Part `GridTheorem`
════════════════════════════════════════════════════════════════════ -/

/-!
# Theorem `thm:grid-energy`

For a periodic Coulomb system, a positive cell length and every `m` at or above the threshold
`coulombGridThreshold`, the physical ground pair of the release file and the Ritz energy of
the padded truncated-kernel collocation method (`n' = 4m+1` grid points per direction, kernel
`w_{≤2K}`, `K = (2π/L) m`) satisfy

  `|E_grid - E| ≤ C / K³`   and   `|E_grid - E| ≤ C' / N`,   `N = (2m+1)³`,

with `C = coulombGridErrorConstant` and `C' = coulombGridBasisErrorConstant`, in the exchange
sector of every admissible labelling (`periodicCoulombSectorGridError`) and on the
spin-inclusive space (`periodicCoulombGridError`). The same holds, with the same threshold and
constants, for every kernel of the class `𝒦_K` (`periodicCoulombSectorKernelGridError`,
`periodicCoulombKernelGridError`): such a kernel agrees with `γ/|ν|²` on the box
`‖ν‖∞ ≤ 2⌊m/4⌋`, so the finite comparison runs at the tail threshold `s = ⌊m/4⌋` and gives
`|E_grid - E_gal| ≤ C_grid/s³ ≤ 512 C_grid/m³`. The Born--Oppenheimer statements are their
instances at `CoulombSystem.bo eta data`.
-/

set_option autoImplicit false

namespace PlaneWaveGrid

open Finset PlaneWaveCertificate

section Main

variable {eta : ℕ} {ν : Type*} [Fintype ν]

/-- **Grid energy theorem for a Coulomb system in an exchange sector, for every kernel of the
class `𝒦_K`.**  In the exchange sector of the admissible labelling `lab`, the grid ground energy
of every kernel of the class converges to the continuum ground energy at the rate `K⁻³`,
equivalently `N⁻¹` with `N = (2m+1)³`. The threshold and constants do not depend on `lab` or
on the kernel. -/
theorem periodicCoulombSectorKernelGridError (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ psi : MolecularPositionL2 eta,
      HasCoulombSectorGroundPair sys lab L psi E ∧
      |E| ≤ coulombGroundEnergyBudget sys L ∧
      ∀ m : ℕ, coulombGridThreshold sys L ≤ m → ∀ κ : Lat3 → ℝ,
        IsGridKernel (coulombCellAmplitude L) m κ →
        ∃ Eg : ℝ, IsCoulombSectorKernelGridGroundEnergy sys lab L m κ Eg ∧
          |Eg - E| ≤ coulombGridErrorConstant sys L / ((2 * Real.pi / L) * (m : ℝ)) ^ 3 ∧
          |Eg - E| ≤ coulombGridBasisErrorConstant sys L / (((2 * m + 1) ^ 3 : ℕ) : ℝ) := by
  obtain ⟨E, psi, hPair, hEbud, hCubic⟩ := coulomb_sector_data_cubic_error sys lab hlab L hL
  refine ⟨E, psi, hPair, hEbud, ?_⟩
  intro m hm κ hκ
  -- consequences of the threshold (before introducing abbreviations)
  have hthr := hm
  unfold coulombGridThreshold at hthr
  have hm8 : 8 ≤ m := by omega
  have hmcub : coulombDataCubicThreshold sys L ≤ 2 * m := by omega
  have hmeta : eta ≤ m := by omega
  have hmroot : Nat.ceil (coulombDataCubicErrorConstant sys L ^ ((1 : ℝ) / 3) /
      (2 * (2 * Real.pi / L))) ≤ m := by omega
  have hmbig : Nat.ceil (2 * Real.sqrt (sys.maxMass * Ebig sys.maxMass
      (coulombGridCoupling sys L) (2 * Real.pi / L) (coulombGridEnergyBudget sys L)) /
      (2 * Real.pi / L)) ≤ m / 4 := by omega
  -- the tail threshold `s = ⌊m/4⌋`
  have hs2 : 2 ≤ m / 4 := by omega
  have hsm : m / 4 ≤ m := Nat.div_le_self m 4
  have hms : m ≤ 8 * (m / 4) := by omega
  -- the Fourier Hamiltonian of the release file and the cubic Ritz energy at cutoff 2K
  obtain ⟨H, hKernel, -⟩ := exists_coulombFourierH2Operator sys L
    molecularCanonicalUnitHardyConstant hL canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨EN, hEN, _hcard, hNonneg, hRate, _hNRate⟩ := hCubic (2 * m) hmcub
  have hcont := (isCoulombSectorCubicGroundEnergy_iff_physicalGalerkinBridge
    sys lab L hL H hKernel _ EN).mp hEN
  have hLne : L ≠ 0 := hL.ne'
  have hfin := continuum_sector_cubic_ground_to_finite
    (coulombPhysicalGalerkinBridge sys lab L hL H hKernel) _ EN (2 * m) (2 * m)
    (by rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hLne]) le_rfl hcont
  have hgal := galRitz_of_cubic sys lab m L hL EN hfin
  -- abbreviations
  set g : ℝ := 2 * Real.pi / L with hgdef
  have hg : 0 < g := by positivity
  set γ : ℝ := coulombCellAmplitude L with hγdef
  have hγ : 0 ≤ γ := (coulombCellAmplitude_pos hL).le
  set P := regParticlesOf sys with hPdef
  set D := (posNucleiOf sys.nuclei).toNucData with hDdef
  set M : ℝ := sys.maxMass with hMdef
  have hM0 : 0 < M := sys.maxMass_pos
  set Z : ℝ := coulombGridCoupling sys L with hZdef
  have hZ : 0 ≤ Z := mul_nonneg hM0.le (Zc_nonneg hγ)
  set Eb : ℝ := coulombGridEnergyBudget sys L with hEbdef
  set Ccub : ℝ := coulombDataCubicErrorConstant sys L with hCcubdef
  have hCcub : 0 ≤ Ccub := coulombDataCubicErrorConstant_nonneg sys L
  set s : ℕ := m / 4 with hsdef
  -- real-valued threshold consequences
  have hmr : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hsr : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hmsr : (m : ℝ) ≤ 8 * s := by exact_mod_cast hms
  have hEbig0 : 0 ≤ M * Ebig M Z g Eb := mul_nonneg hM0.le (Ebig_nonneg hZ)
  have hbig : 4 * M * Ebig M Z g Eb ≤ g ^ 2 * (s : ℝ) ^ 2 := by
    have h1 : 2 * Real.sqrt (M * Ebig M Z g Eb) / g ≤ s :=
      (Nat.le_ceil _).trans (by exact_mod_cast hmbig)
    rw [div_le_iff₀ hg] at h1
    have h2 : (2 * Real.sqrt (M * Ebig M Z g Eb)) ^ 2 ≤ (s * g) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, Real.sq_sqrt hEbig0] at h2
    nlinarith
  -- the cutoff error at 2K is at most one, so |EN| ≤ Eb
  have hroot : Ccub ^ ((1 : ℝ) / 3) ≤ g * ((2 * m : ℕ) : ℝ) := by
    have h1 : Ccub ^ ((1 : ℝ) / 3) / (2 * g) ≤ m :=
      (Nat.le_ceil _).trans (by exact_mod_cast hmroot)
    rw [div_le_iff₀ (by positivity)] at h1
    push_cast
    linarith
  have hcube : Ccub ≤ (g * ((2 * m : ℕ) : ℝ)) ^ 3 := by
    have h1 : (Ccub ^ ((1 : ℝ) / 3)) ^ 3 = Ccub := by
      rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow hCcub (by norm_num)
    calc Ccub = (Ccub ^ ((1 : ℝ) / 3)) ^ 3 := h1.symm
      _ ≤ (g * ((2 * m : ℕ) : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hCcub _) hroot 3
  have h2m : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * m)
  have hENE : EN - E ≤ 1 :=
    hRate.trans ((div_le_one (by positivity)).mpr hcube)
  have hEb : |EN| ≤ Eb := by
    have h1 : |EN| ≤ |E| + 1 := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le E]
      · linarith [le_abs_self E]
    have h2 : Eb = coulombGroundEnergyBudget sys L + 1 := rfl
    rw [h2]
    linarith
  -- a nonzero register state in the sector, and constant masses and charges on the blocks
  have hNZ := exists_nonzero_sec sys hlab m hmeta
  have hP : ∀ a b, lab a = lab b → P.mass a = P.mass b ∧ P.charge a = P.charge b :=
    fun a b h => ⟨sys.mass_eq a b (hlab a b h), sys.charge_eq a b (hlab a b h)⟩
  -- the finite comparison at the tail threshold `s`
  obtain ⟨Eg, hRitz, hdiff⟩ := grid_galerkin_energy (P := P) (D := D) (m := m) sys.sign lab hP
    hγ hg hs2 hsm hms hκ.gridKernel hNZ EN Eb hEb hgal hbig
  have hpos : IsCoulombSectorKernelGridGroundEnergy sys lab L m κ Eg :=
    (isSecRitz_Hpos_iff sys.sign lab P (posNucleiOf sys.nuclei) κ hκ.even g Eg).mpr hRitz
  -- arithmetic: |Eg - E| ≤ 512 Cgrid/m³ + Ccub/(2gm)³ = coulombGridErrorConstant/(gm)³
  have hCg0 : 0 ≤ Cgrid M Z g Eb := by
    unfold Cgrid
    exact mul_nonneg (Cform_nonneg hZ) (sq_nonneg _)
  have hdiff' : |Eg - EN| ≤ 512 * Cgrid M Z g Eb / (m : ℝ) ^ 3 := by
    have hdiff2 : |Eg - EN| ≤ Cgrid M Z g Eb / (s : ℝ) ^ 3 := hdiff
    refine hdiff2.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm3 : (m : ℝ) ^ 3 ≤ 512 * (s : ℝ) ^ 3 := by
      calc (m : ℝ) ^ 3 ≤ (8 * (s : ℝ)) ^ 3 := pow_le_pow_left₀ hmr.le hmsr 3
        _ = 512 * (s : ℝ) ^ 3 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hm3 hCg0]
  have hrate' : EN - E ≤ Ccub / (8 * (g * m) ^ 3) := by
    refine hRate.trans (le_of_eq ?_)
    push_cast
    ring
  have htri : |Eg - E| ≤ |Eg - EN| + |EN - E| := by
    have := abs_sub_le Eg EN E
    linarith
  rw [abs_of_nonneg hNonneg] at htri
  have hGE : coulombGridErrorConstant sys L = 512 * g ^ 3 * Cgrid M Z g Eb + Ccub / 8 := rfl
  have hfinal : 512 * Cgrid M Z g Eb / (m : ℝ) ^ 3 + Ccub / (8 * (g * m) ^ 3) =
      coulombGridErrorConstant sys L / (g * (m : ℝ)) ^ 3 := by
    rw [hGE, div_add_div _ _ (by positivity) (by positivity),
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hK3' : |Eg - E| ≤ coulombGridErrorConstant sys L / (g * (m : ℝ)) ^ 3 :=
    calc |Eg - E| ≤ |Eg - EN| + (EN - E) := htri
      _ ≤ 512 * Cgrid M Z g Eb / (m : ℝ) ^ 3 + Ccub / (8 * (g * m) ^ 3) :=
        add_le_add hdiff' hrate'
      _ = coulombGridErrorConstant sys L / (g * (m : ℝ)) ^ 3 := hfinal
  refine ⟨Eg, hpos, hK3', hK3'.trans ?_⟩
  -- basis-count form: (2m+1)³ ≤ 27 m³
  have hC0 : 0 ≤ coulombGridErrorConstant sys L := by
    rw [hGE]
    positivity
  have hN : (((2 * m + 1) ^ 3 : ℕ) : ℝ) ≤ 27 * (m : ℝ) ^ 3 := by
    push_cast
    have : 2 * (m : ℝ) + 1 ≤ 3 * m := by linarith
    calc (2 * (m : ℝ) + 1) ^ 3 ≤ (3 * (m : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) this 3
      _ = 27 * (m : ℝ) ^ 3 := by ring
  have hNpos : (0 : ℝ) < (((2 * m + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hBE : coulombGridBasisErrorConstant sys L = 27 * coulombGridErrorConstant sys L / g ^ 3 :=
    rfl
  rw [hBE, mul_pow, div_le_div_iff₀ (by positivity) hNpos]
  calc coulombGridErrorConstant sys L * (((2 * m + 1) ^ 3 : ℕ) : ℝ)
      ≤ coulombGridErrorConstant sys L * (27 * (m : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hN hC0
    _ = 27 * coulombGridErrorConstant sys L / g ^ 3 * (g ^ 3 * (m : ℝ) ^ 3) := by
        rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
        ring

/-- **Grid energy theorem for a Coulomb system in an exchange sector** (`thm:grid-energy`, the
truncated kernel `w_{≤2K}`).  In the exchange sector of the admissible labelling `lab`, the
truncated-kernel grid ground energy converges to the continuum ground energy at the rate
`K⁻³`, equivalently `N⁻¹` with `N = (2m+1)³`. The threshold and constants do not depend on
`lab`. -/
theorem periodicCoulombSectorGridError (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ psi : MolecularPositionL2 eta,
      HasCoulombSectorGroundPair sys lab L psi E ∧
      |E| ≤ coulombGroundEnergyBudget sys L ∧
      ∀ m : ℕ, coulombGridThreshold sys L ≤ m →
        ∃ Eg : ℝ, IsCoulombSectorGridGroundEnergy sys lab L m Eg ∧
          |Eg - E| ≤ coulombGridErrorConstant sys L / ((2 * Real.pi / L) * (m : ℝ)) ^ 3 ∧
          |Eg - E| ≤ coulombGridBasisErrorConstant sys L / (((2 * m + 1) ^ 3 : ℕ) : ℝ) := by
  obtain ⟨E, psi, hPair, hBud, hGrid⟩ := periodicCoulombSectorKernelGridError sys lab hlab L hL
  exact ⟨E, psi, hPair, hBud, fun m hm =>
    hGrid m hm _ (sharpKernel_isGridKernel (coulombCellAmplitude_pos hL).le m)⟩

/-! ### The grid theorem on the spin-inclusive space -/

/-- Relabelling of grid registers as a representation of the permutation group. -/
noncomputable def gridRelabelling (eta n : ℕ) [NeZero n] :
    ParticleRelabelling eta (EuclideanSpace ℂ (GConfig eta n)) where
  act := gridPermute
  act_mul := gridPermute_mul
  act_one := gridPermute_one

lemma isSec_iff_isSignedSector {n : ℕ} [NeZero n] (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ)
    (u : EuclideanSpace ℂ (GConfig eta n)) :
    IsSec sgn lab u ↔ (gridRelabelling eta n).IsSignedSector sgn lab u :=
  isSec_iff_gridPermute sgn lab u

/-- Spin-dependent grid states of `eta` particles with spin values in `Fin D`: one grid
function on the padded register for each spin configuration, with the squared norm summed
over spins. -/
abbrev CoulombGridSpinState (eta D m : ℕ) :=
  PiLp 2 (fun _ : Fin eta → Fin D => EuclideanSpace ℂ (RCfg eta m))

/-- The physical spin states of a Coulomb system on the grid: exchanging the grid positions
and spins of two particles of one species multiplies the state by the exchange sign of the
species, and the components with a spin value at or above the multiplicity of its species
vanish. -/
def IsCoulombGridSpinSector (sys : CoulombSystem eta ν) (dim : ℕ → ℕ) {D m : ℕ}
    (Φ : CoulombGridSpinState eta D m) : Prop :=
  (gridRelabelling eta (2 * (2 * m) + 1)).IsCoulombSpinSector sys.toCoulombParticles dim Φ

/-- The spin-independent grid Hamiltonian: `Hpos` on each spin component. -/
noncomputable def spinHpos {S : Type*} [Fintype S] {m : ℕ} (P : RegParticles eta)
    (N : PosNuclei ν) (κ : Lat3 → ℝ) (g : ℝ) :
    PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m)) →ₗ[ℂ]
      PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m)) where
  toFun Φ := WithLp.toLp 2 (fun σ => Hpos P N κ g (Φ σ))
  map_add' := by
    intro Φ Ψ
    apply PiLp.ext
    intro σ
    change Hpos P N κ g ((Φ + Ψ) σ) = Hpos P N κ g (Φ σ) + Hpos P N κ g (Ψ σ)
    rw [PiLp.add_apply, map_add]
  map_smul' := by
    intro c Φ
    apply PiLp.ext
    intro σ
    change Hpos P N κ g ((c • Φ) σ) = c • Hpos P N κ g (Φ σ)
    rw [PiLp.smul_apply, map_smul]

lemma spinHpos_apply {S : Type*} [Fintype S] {m : ℕ} (P : RegParticles eta) (N : PosNuclei ν)
    (κ : Lat3 → ℝ) (g : ℝ) (Φ : PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m))) (σ : S) :
    spinHpos P N κ g Φ σ = Hpos P N κ g (Φ σ) := rfl

/-- The grid ground energy of a Coulomb system on the spin-inclusive space for the kernel with
coefficients `κ`: the Ritz energy of the spin-independent grid Hamiltonian on the physical
spin-dependent grid states. -/
def IsCoulombSpinKernelGridGroundEnergy (sys : CoulombSystem eta ν) (D : ℕ) (dim : ℕ → ℕ)
    (L : ℝ) (m : ℕ) (κ : Lat3 → ℝ) (Eg : ℝ) : Prop :=
  (∀ Φ : CoulombGridSpinState eta D m, IsCoulombGridSpinSector sys dim Φ →
    Eg * ‖Φ‖ ^ 2 ≤ (inner ℂ Φ (spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
      (2 * Real.pi / L) Φ)).re) ∧
  ∃ Φ : CoulombGridSpinState eta D m, IsCoulombGridSpinSector sys dim Φ ∧ ‖Φ‖ = 1 ∧
    (inner ℂ Φ (spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
      (2 * Real.pi / L) Φ)).re = Eg

/-- The grid ground energy of a Coulomb system on the spin-inclusive space for the truncated
kernel `w_{≤2K}`. -/
def IsCoulombSpinGridGroundEnergy (sys : CoulombSystem eta ν) (D : ℕ) (dim : ℕ → ℕ) (L : ℝ)
    (m : ℕ) (Eg : ℝ) : Prop :=
  IsCoulombSpinKernelGridGroundEnergy sys D dim L m (sharpKernel (coulombCellAmplitude L) m) Eg

/-- Symmetrization within species commutes with the spin-independent grid Hamiltonian of an
even kernel. -/
lemma spinHpos_symmetrize (sys : CoulombSystem eta ν) {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x)
    (g : ℝ) {D m : ℕ} (σ₀ : Fin eta → Fin D) (u : EuclideanSpace ℂ (RCfg eta m)) :
    spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ g
        ((gridRelabelling eta (2 * (2 * m) + 1)).symmetrize sys.toCoulombParticles σ₀ u) =
      (gridRelabelling eta (2 * (2 * m) + 1)).symmetrize sys.toCoulombParticles σ₀
        (Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ g u) := by
  apply PiLp.ext
  intro σ
  rw [spinHpos_apply]
  exact ((gridRelabelling eta (2 * (2 * m) + 1)).symmetrize_rel sys.toCoulombParticles
    (Rel := fun f h => h = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ g f)
    (fun π hπ f h hfh => by
      rw [hfh]
      exact (Hpos_gridPermute (regParticlesOf sys) (posNucleiOf sys.nuclei) hκe g π
        (fun k => ⟨hπ.mass k, hπ.charge k⟩) f).symm)
    (fun c f h hfh => by rw [hfh, map_smul])
    σ₀ (f := u) (h := Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ g u) rfl σ).symm

/-- The lowest grid energy over the sectors of the valid spin patterns is the grid ground
energy on the spin-inclusive space, for an even kernel. -/
theorem IsCoulombSpinKernelGridGroundEnergy.of_sectors {sys : CoulombSystem eta ν} {D : ℕ}
    {dim : ℕ → ℕ} {L : ℝ} {m : ℕ} {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x)
    (Eg : (Fin eta → Fin D) → ℝ)
    (hEg : ∀ σ, IsCoulombSectorKernelGridGroundEnergy sys (sys.spinSectorLabel σ) L m κ (Eg σ))
    (σ₁ : Fin eta → Fin D) (hσ₁ : sys.IsValidSpin dim σ₁)
    (hmin : ∀ σ, sys.IsValidSpin dim σ → Eg σ₁ ≤ Eg σ) :
    IsCoulombSpinKernelGridGroundEnergy sys D dim L m κ (Eg σ₁) := by
  let R := gridRelabelling eta (2 * (2 * m) + 1)
  constructor
  · intro Φ hΦ
    apply pi_lower_bound_of_components
    intro σ
    by_cases hv : sys.IsValidSpin dim σ
    · exact (mul_le_mul_of_nonneg_right (hmin σ hv) (sq_nonneg _)).trans
        ((hEg σ).1 (Φ σ) ((isSec_iff_isSignedSector _ _ _).mpr
          (ParticleRelabelling.IsCoulombSpinSector.component hΦ σ)))
    · rw [ParticleRelabelling.IsCoulombSpinSector.eq_zero_of_not_valid hΦ hv, norm_zero,
        inner_zero_left]
      simp
  · obtain ⟨u, hu, hn, hv⟩ := (hEg σ₁).2
    let A : CoulombGridSpinState eta D m := R.symmetrize sys.toCoulombParticles σ₁ u
    have hA : ‖A‖ ≠ 0 := R.symmetrize_norm_ne_zero sys.toCoulombParticles σ₁ hn
    have hS : IsCoulombGridSpinSector sys dim A :=
      R.symmetrize_isCoulombSpinSector sys.toCoulombParticles dim hσ₁
        ((isSec_iff_isSignedSector _ _ u).mp hu)
    refine ⟨((‖A‖⁻¹ : ℝ) : ℂ) • A, ParticleRelabelling.IsCoulombSpinSector.smul hS _,
      norm_inv_smul_self_eq_one hA, ?_⟩
    rw [map_smul, spinHpos_symmetrize sys hκe]
    exact (R.symmetrize_rayleigh sys.toCoulombParticles σ₁ hn).trans hv

/-- **Grid energy theorem for a Coulomb system on the spin-inclusive space, for every kernel of
the class `𝒦_K`**, with `dim s` spin states for the species `s`. The grid ground energy of
every kernel of the class on the physical spin-dependent grid states converges to the
continuum ground energy at the rate `K⁻³`, equivalently `N⁻¹`, with the same threshold and
constants as every exchange sector. -/
theorem periodicCoulombKernelGridError (sys : CoulombSystem eta ν) (D : ℕ) (dim : ℕ → ℕ)
    (hdim : ∀ a, 0 < dim (sys.species a) ∧ dim (sys.species a) ≤ D) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ Ψ : CoulombSpinL2 eta D,
      HasCoulombSpinGroundPair sys dim L Ψ E ∧
      |E| ≤ coulombGroundEnergyBudget sys L ∧
      ∀ m : ℕ, coulombGridThreshold sys L ≤ m → ∀ κ : Lat3 → ℝ,
        IsGridKernel (coulombCellAmplitude L) m κ →
        ∃ Eg : ℝ, IsCoulombSpinKernelGridGroundEnergy sys D dim L m κ Eg ∧
          |Eg - E| ≤ coulombGridErrorConstant sys L / ((2 * Real.pi / L) * (m : ℝ)) ^ 3 ∧
          |Eg - E| ≤ coulombGridBasisErrorConstant sys L / (((2 * m + 1) ^ 3 : ℕ) : ℝ) := by
  classical
  choose E ψ hPair hBudget hGrid using
    fun σ : Fin eta → Fin D => periodicCoulombSectorKernelGridError sys (sys.spinSectorLabel σ)
      (sys.spinSectorLabel_isAdmissible σ) L hL
  obtain ⟨σ₀, hσ₀, hmin⟩ := sys.exists_min_valid hdim E
  refine ⟨E σ₀, _, HasCoulombSpinGroundPair.of_sectors E ψ hPair σ₀ hσ₀ hmin,
    hBudget σ₀, ?_⟩
  intro m hm κ hκ
  choose Eg hEg hK hN using fun σ : Fin eta → Fin D => hGrid σ m hm κ hκ
  obtain ⟨σ₁, hσ₁, hmin₁⟩ := sys.exists_min_valid hdim Eg
  refine ⟨Eg σ₁, IsCoulombSpinKernelGridGroundEnergy.of_sectors hκ.even Eg hEg σ₁ hσ₁ hmin₁, ?_,
    ?_⟩
  · have h0 := abs_le.mp (hK σ₀)
    have h1 := abs_le.mp (hK σ₁)
    rw [abs_le]
    constructor
    · linarith [hmin σ₁ hσ₁, h1.1]
    · linarith [hmin₁ σ₀ hσ₀, h0.2]
  · have h0 := abs_le.mp (hN σ₀)
    have h1 := abs_le.mp (hN σ₁)
    rw [abs_le]
    constructor
    · linarith [hmin σ₁ hσ₁, h1.1]
    · linarith [hmin₁ σ₀ hσ₀, h0.2]

/-- **Grid energy theorem for a Coulomb system** (`thm:grid-energy`, the truncated kernel
`w_{≤2K}`) on the spin-inclusive space `L²((T³)^η; ⊗_a ℂ^{d_a})`, with `dim s` spin states for
the species `s`. The grid ground energy on the physical spin-dependent grid states converges
to the continuum ground energy at the rate `K⁻³`, equivalently `N⁻¹`, with the same threshold
and constants as every exchange sector. -/
theorem periodicCoulombGridError (sys : CoulombSystem eta ν) (D : ℕ) (dim : ℕ → ℕ)
    (hdim : ∀ a, 0 < dim (sys.species a) ∧ dim (sys.species a) ≤ D) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ Ψ : CoulombSpinL2 eta D,
      HasCoulombSpinGroundPair sys dim L Ψ E ∧
      |E| ≤ coulombGroundEnergyBudget sys L ∧
      ∀ m : ℕ, coulombGridThreshold sys L ≤ m →
        ∃ Eg : ℝ, IsCoulombSpinGridGroundEnergy sys D dim L m Eg ∧
          |Eg - E| ≤ coulombGridErrorConstant sys L / ((2 * Real.pi / L) * (m : ℝ)) ^ 3 ∧
          |Eg - E| ≤ coulombGridBasisErrorConstant sys L / (((2 * m + 1) ^ 3 : ℕ) : ℝ) := by
  obtain ⟨E, Ψ, hPair, hBud, hGrid⟩ := periodicCoulombKernelGridError sys D dim hdim L hL
  exact ⟨E, Ψ, hPair, hBud, fun m hm =>
    hGrid m hm _ (sharpKernel_isGridKernel (coulombCellAmplitude_pos hL).le m)⟩

/-! ### The Born--Oppenheimer problem -/

/-- The grid ground energy of the padded collocation method with `n' = 4m+1` points per
direction and the kernel with coefficients `κ`, in the exchange sector `lab` of the
Born--Oppenheimer problem: the Ritz energy of `Hpos` for electrons and the clamped nuclei on
grid functions that are antisymmetric under exchange of two registers with equal labels. -/
def IsMolecularFermionicKernelGridGroundEnergy (eta : ℕ) (lab : Fin eta → ℕ) (L : ℝ)
    (data : FiniteBONuclearData ν) (m : ℕ) (κ : Lat3 → ℝ) (Eg : ℝ) : Prop :=
  IsSecRitz (fun _ => -1) lab (Hpos (m := m) (RegParticles.electrons eta) (posNucleiOf data) κ
    (2 * Real.pi / L)) Eg

/-- The grid ground energy in the exchange sector `lab` of the Born--Oppenheimer problem for
the truncated kernel `w_{≤2K}`. -/
def IsMolecularFermionicGridGroundEnergy (eta : ℕ) (lab : Fin eta → ℕ) (L : ℝ)
    (data : FiniteBONuclearData ν) (m : ℕ) (Eg : ℝ) : Prop :=
  IsMolecularFermionicKernelGridGroundEnergy eta lab L data m
    (sharpKernel (coulombCellAmplitude L) m) Eg

/-- It is the grid ground energy of the system of electrons and clamped nuclei. -/
lemma isMolecularFermionicKernelGridGroundEnergy_iff (eta : ℕ) (lab : Fin eta → ℕ) (L : ℝ)
    (data : FiniteBONuclearData ν) (m : ℕ) (κ : Lat3 → ℝ) (Eg : ℝ) :
    IsMolecularFermionicKernelGridGroundEnergy eta lab L data m κ Eg ↔
      IsCoulombSectorKernelGridGroundEnergy (CoulombSystem.bo eta data) lab L m κ Eg := Iff.rfl

/-- The size threshold of the Born--Oppenheimer grid theorem: that of the system
of electrons and clamped nuclei. -/
noncomputable def gridThreshold (eta : ℕ) (data : FiniteBONuclearData ν) (L : ℝ) : ℕ :=
  coulombGridThreshold (CoulombSystem.bo eta data) L

/-- The error constant of the Born--Oppenheimer grid theorem. -/
noncomputable def gridErrorConstant (eta : ℕ) (data : FiniteBONuclearData ν) (L : ℝ) : ℝ :=
  coulombGridErrorConstant (CoulombSystem.bo eta data) L

/-- The error constant in basis-count form, `N = (2m+1)³`. -/
noncomputable def gridBasisErrorConstant (eta : ℕ) (data : FiniteBONuclearData ν) (L : ℝ) :
    ℝ :=
  coulombGridBasisErrorConstant (CoulombSystem.bo eta data) L

/-- **Grid energy theorem in an exchange sector** (Born--Oppenheimer case, every kernel of the
class `𝒦_K`).  In the exchange sector `lab`, the grid ground energy of every kernel of the
class converges to the continuum ground energy at the rate `K⁻³`, equivalently `N⁻¹` with
`N = (2m+1)³`. The threshold and constants do not depend on `lab` or on the kernel. -/
theorem periodicMolecularSectorKernelGridError (eta : ℕ) (lab : Fin eta → ℕ) (_heta : 0 < eta)
    (data : FiniteBONuclearData ν) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ psi : MolecularPositionL2 eta,
      HasMolecularFermionicGroundPair eta lab L data psi E ∧
      |E| ≤ molecularGroundEnergyBudget eta data L ∧
      ∀ m : ℕ, gridThreshold eta data L ≤ m → ∀ κ : Lat3 → ℝ,
        IsGridKernel (coulombCellAmplitude L) m κ →
        ∃ Eg : ℝ, IsMolecularFermionicKernelGridGroundEnergy eta lab L data m κ Eg ∧
          |Eg - E| ≤ gridErrorConstant eta data L / ((2 * Real.pi / L) * (m : ℝ)) ^ 3 ∧
          |Eg - E| ≤ gridBasisErrorConstant eta data L / (((2 * m + 1) ^ 3 : ℕ) : ℝ) := by
  obtain ⟨E, psi, hPair, hBud, hGrid⟩ :=
    periodicCoulombSectorKernelGridError (CoulombSystem.bo eta data) lab (fun _ _ _ => rfl) L hL
  refine ⟨E, psi, (hasCoulombSectorGroundPair_bo eta data lab L psi E).mp hPair, ?_, ?_⟩
  · rwa [coulombGroundEnergyBudget_bo] at hBud
  · intro m hm κ hκ
    obtain ⟨Eg, hEg, hK, hN⟩ := hGrid m hm κ hκ
    exact ⟨Eg, (isMolecularFermionicKernelGridGroundEnergy_iff eta lab L data m κ Eg).mpr hEg,
      hK, hN⟩

/-- **Grid energy theorem in an exchange sector** (`thm:grid-energy`, Born--Oppenheimer case,
the truncated kernel `w_{≤2K}`).  In the exchange sector `lab`, the truncated-kernel grid
ground energy converges to the continuum ground energy at the rate `K⁻³`, equivalently `N⁻¹`
with `N = (2m+1)³`. The threshold and constants do not depend on `lab`. -/
theorem periodicMolecularSectorGridError (eta : ℕ) (lab : Fin eta → ℕ) (_heta : 0 < eta)
    (data : FiniteBONuclearData ν) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ psi : MolecularPositionL2 eta,
      HasMolecularFermionicGroundPair eta lab L data psi E ∧
      |E| ≤ molecularGroundEnergyBudget eta data L ∧
      ∀ m : ℕ, gridThreshold eta data L ≤ m →
        ∃ Eg : ℝ, IsMolecularFermionicGridGroundEnergy eta lab L data m Eg ∧
          |Eg - E| ≤ gridErrorConstant eta data L / ((2 * Real.pi / L) * (m : ℝ)) ^ 3 ∧
          |Eg - E| ≤ gridBasisErrorConstant eta data L / (((2 * m + 1) ^ 3 : ℕ) : ℝ) := by
  obtain ⟨E, psi, hPair, hBud, hGrid⟩ :=
    periodicMolecularSectorKernelGridError eta lab _heta data L hL
  exact ⟨E, psi, hPair, hBud, fun m hm =>
    hGrid m hm _ (sharpKernel_isGridKernel (coulombCellAmplitude_pos hL).le m)⟩

/-- Spin-dependent grid states on the padded register: one grid function for each spin
configuration, with the squared norm summed over spins. -/
abbrev GridSpinState (eta m : ℕ) :=
  PiLp 2 (fun _ : SpinConfig eta => EuclideanSpace ℂ (RCfg eta m))

/-- Antisymmetry of a spin-dependent grid state under simultaneous exchange of the grid
positions and spins of two electrons. -/
def IsGridSpinFermionic {m : ℕ} (Φ : GridSpinState eta m) : Prop :=
  ∀ i j : Fin eta, i ≠ j → ∀ (σ : SpinConfig eta) (q : RCfg eta m),
    Φ (σ ∘ Equiv.swap i j) (swapCfg i j q) = -Φ σ q

/-- With two spin states per electron, the physical grid spin states of the
Born--Oppenheimer system are the antisymmetric ones. -/
lemma isGridSpinFermionic_iff (data : FiniteBONuclearData ν) {m : ℕ}
    (Φ : GridSpinState eta m) :
    IsGridSpinFermionic Φ ↔
      IsCoulombGridSpinSector (CoulombSystem.bo eta data) (fun _ => 2) Φ := by
  unfold IsCoulombGridSpinSector ParticleRelabelling.IsCoulombSpinSector
  constructor
  · intro h
    refine ⟨fun i j hij _ σ => ?_, fun σ a ha => absurd ha (not_le.mpr (σ a).isLt)⟩
    ext q
    change Φ (σ ∘ Equiv.swap i j) (swapCfg i j q) = (-1 : ℂ) * Φ σ q
    rw [h i j hij σ q, neg_one_mul]
  · rintro ⟨h, -⟩ i j hij σ q
    have := congrArg (fun v : EuclideanSpace ℂ (RCfg eta m) => v q) (h i j hij rfl σ)
    change Φ (σ ∘ Equiv.swap i j) (swapCfg i j q) = (-1 : ℂ) * Φ σ q at this
    rw [this, neg_one_mul]

/-- The grid ground energy on the electronic space for the kernel with coefficients `κ`: the
Ritz energy of the spin-independent grid Hamiltonian for electrons and the clamped nuclei on
spin-dependent grid states that are antisymmetric under simultaneous exchange of the grid
positions and spins of two electrons. -/
def IsMolecularSpinKernelGridGroundEnergy (eta : ℕ) (L : ℝ) (data : FiniteBONuclearData ν)
    (m : ℕ) (κ : Lat3 → ℝ) (Eg : ℝ) : Prop :=
  (∀ Φ : GridSpinState eta m, IsGridSpinFermionic Φ →
    Eg * ‖Φ‖ ^ 2 ≤ (inner ℂ Φ (spinHpos (RegParticles.electrons eta) (posNucleiOf data) κ
      (2 * Real.pi / L) Φ)).re) ∧
  ∃ Φ : GridSpinState eta m, IsGridSpinFermionic Φ ∧ ‖Φ‖ = 1 ∧
    (inner ℂ Φ (spinHpos (RegParticles.electrons eta) (posNucleiOf data) κ
      (2 * Real.pi / L) Φ)).re = Eg

/-- The grid ground energy on the electronic space for the truncated kernel `w_{≤2K}`. -/
def IsMolecularSpinGridGroundEnergy (eta : ℕ) (L : ℝ) (data : FiniteBONuclearData ν)
    (m : ℕ) (Eg : ℝ) : Prop :=
  IsMolecularSpinKernelGridGroundEnergy eta L data m (sharpKernel (coulombCellAmplitude L) m) Eg

/-- It is the grid ground energy of the system of electrons and clamped nuclei with two spin
states per electron. -/
lemma isMolecularSpinKernelGridGroundEnergy_iff (eta : ℕ) (L : ℝ)
    (data : FiniteBONuclearData ν) (m : ℕ) (κ : Lat3 → ℝ) (Eg : ℝ) :
    IsMolecularSpinKernelGridGroundEnergy eta L data m κ Eg ↔
      IsCoulombSpinKernelGridGroundEnergy (CoulombSystem.bo eta data) 2 (fun _ => 2) L m κ Eg := by
  unfold IsMolecularSpinKernelGridGroundEnergy IsCoulombSpinKernelGridGroundEnergy
  constructor
  · rintro ⟨hLow, Φ, hΦ, hn, hv⟩
    exact ⟨fun Ψ hΨ => hLow Ψ ((isGridSpinFermionic_iff data Ψ).mpr hΨ),
      Φ, (isGridSpinFermionic_iff data Φ).mp hΦ, hn, hv⟩
  · rintro ⟨hLow, Φ, hΦ, hn, hv⟩
    exact ⟨fun Ψ hΨ => hLow Ψ ((isGridSpinFermionic_iff data Ψ).mp hΨ),
      Φ, (isGridSpinFermionic_iff data Φ).mpr hΦ, hn, hv⟩

/-- **Grid energy theorem** (Born--Oppenheimer case, every kernel of the class `𝒦_K`) on the
physical electronic space `Λ^η(L²(T³) ⊗ ℂ²)`. The spin-inclusive grid ground energy of every
kernel of the class converges to the continuum ground energy at the rate `K⁻³`, equivalently
`N⁻¹` with `N = (2m+1)³`, with the same threshold and constants as every exchange sector. -/
theorem periodicMolecularKernelGridError (eta : ℕ) (_heta : 0 < eta)
    (data : FiniteBONuclearData ν) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ Ψ : MolecularSpinL2 eta,
      HasMolecularSpinGroundPair eta L data Ψ E ∧
      |E| ≤ molecularGroundEnergyBudget eta data L ∧
      ∀ m : ℕ, gridThreshold eta data L ≤ m → ∀ κ : Lat3 → ℝ,
        IsGridKernel (coulombCellAmplitude L) m κ →
        ∃ Eg : ℝ, IsMolecularSpinKernelGridGroundEnergy eta L data m κ Eg ∧
          |Eg - E| ≤ gridErrorConstant eta data L / ((2 * Real.pi / L) * (m : ℝ)) ^ 3 ∧
          |Eg - E| ≤ gridBasisErrorConstant eta data L / (((2 * m + 1) ^ 3 : ℕ) : ℝ) := by
  obtain ⟨E, Ψ, hPair, hBud, hGrid⟩ := periodicCoulombKernelGridError (CoulombSystem.bo eta data)
    2 (fun _ => 2) (CoulombSystem.bo_spinDim eta data) L hL
  refine ⟨E, Ψ, (hasCoulombSpinGroundPair_bo eta data L Ψ E).mp hPair, ?_, ?_⟩
  · rwa [coulombGroundEnergyBudget_bo] at hBud
  · intro m hm κ hκ
    obtain ⟨Eg, hEg, hK, hN⟩ := hGrid m hm κ hκ
    exact ⟨Eg, (isMolecularSpinKernelGridGroundEnergy_iff eta L data m κ Eg).mpr hEg, hK, hN⟩

/-- **Grid energy theorem** (`thm:grid-energy`, Born--Oppenheimer case, the truncated kernel
`w_{≤2K}`) on the physical electronic space `Λ^η(L²(T³) ⊗ ℂ²)`. The spin-inclusive
truncated-kernel grid ground energy converges to the continuum ground energy at the rate
`K⁻³`, equivalently `N⁻¹` with `N = (2m+1)³`, with the same threshold and constants as every
exchange sector. -/
theorem periodicMolecularGridError (eta : ℕ) (_heta : 0 < eta)
    (data : FiniteBONuclearData ν) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ Ψ : MolecularSpinL2 eta,
      HasMolecularSpinGroundPair eta L data Ψ E ∧
      |E| ≤ molecularGroundEnergyBudget eta data L ∧
      ∀ m : ℕ, gridThreshold eta data L ≤ m →
        ∃ Eg : ℝ, IsMolecularSpinGridGroundEnergy eta L data m Eg ∧
          |Eg - E| ≤ gridErrorConstant eta data L / ((2 * Real.pi / L) * (m : ℝ)) ^ 3 ∧
          |Eg - E| ≤ gridBasisErrorConstant eta data L / (((2 * m + 1) ^ 3 : ℕ) : ℝ) := by
  obtain ⟨E, Ψ, hPair, hBud, hGrid⟩ := periodicMolecularKernelGridError eta _heta data L hL
  exact ⟨E, Ψ, hPair, hBud, fun m hm =>
    hGrid m hm _ (sharpKernel_isGridKernel (coulombCellAmplitude_pos hL).le m)⟩

end Main

end PlaneWaveGrid

/-! ════════════════════════════════════════════════════════════════════
## Part `PolynomialBounds`
════════════════════════════════════════════════════════════════════ -/

/-!
# Polynomial bounds on the grid constants

The manuscript's `thm:grid-energy` states that the grid constant is polynomial in the particle
data. Here the error constant and the threshold of the grid theorem are bounded by polynomials
in `η`, the largest mass `m̄` and the charge weight `Q = 1 + Σ_a |q_a| + Z_tot` of milestone 151
of the release file, with factors in front that depend only on the cell side `L`:

* `coulombGridErrorConstant_le_poly`: the error constant is at most `C_L (1 + η³)⁴ m̄²⁷ Q⁴²`;
* `coulombGridThreshold_le_poly`: the threshold is at most `T'_L (1 + η)(1 + η³)² m̄⁸ Q²⁰`,
  the degrees of the cutoff threshold of milestone 151;
* `gridErrorConstant_le_poly`, `gridThreshold_le_poly`: the Born--Oppenheimer case, with
  `m̄ = 1` and `Q = 1 + η + Z_tot`.

The basis-count constant is `27 (L/(2π))³` times the error constant, by definition. The bounds
pass through the core constants: with the register coupling `Z = m̄ γ_L W ≤ γ_L m̄ Q²`
(`W` the coupling weight), `J₀ ≤ c_J m̄² Q⁴`, `C_form ≤ c_F m̄³ Q⁶`, the elliptic constant
`Ell(y) ≤ c_E P` for an energy `y ≤ c P` with `P ≥ m̄³ Q⁶`, and the energy budget
`E_b + 1 ≤ 2 (1 + G_L)(1 + η³) m̄ Q⁴` of milestone 151.
-/

set_option autoImplicit false

namespace PlaneWaveGrid

open Finset PlaneWaveCertificate

/-! ## Cell factors of the core constants -/

/-- The cell factor `c_J = 88192 γ²/g⁴ + 2` of the splitting radius `J₀`. -/
noncomputable def gridSplitCell (γ g : ℝ) : ℝ := 88192 * γ ^ 2 / g ^ 4 + 2

/-- The cell factor `c_F = 260·508 γ²/g² + 416·508² γ³/g⁴` of the form constant. -/
noncomputable def gridFormCell (γ g : ℝ) : ℝ :=
  260 * 508 * γ ^ 2 / g ^ 2 + 416 * 508 ^ 2 * γ ^ 3 / g ^ 4

/-- The cell factor `c_E(c) = 4/3 + 8c/(3g²) + 208 γ c_J/(3g²)` of the elliptic constant at an
energy with cell factor `c`. -/
noncomputable def gridEllCell (γ g c : ℝ) : ℝ :=
  4 / 3 + 8 * c / (3 * g ^ 2) + 208 * γ * gridSplitCell γ g / (3 * g ^ 2)

/-- The cell factor `c_B(c) = 52 γ c_J + g²/4 + c + c_F c_E(c)²` of the common energy bound
`E_big`, for an energy budget with cell factor `c`. -/
noncomputable def gridEnergyCell (γ g c : ℝ) : ℝ :=
  52 * γ * gridSplitCell γ g + g ^ 2 / 4 + c + gridFormCell γ g * gridEllCell γ g c ^ 2

section PolyArith

variable {γ g M Q Z : ℝ}

lemma gridSplitCell_nonneg (γ g : ℝ) : 0 ≤ gridSplitCell γ g := by
  unfold gridSplitCell
  positivity

lemma gridFormCell_nonneg (hγ : 0 ≤ γ) (g : ℝ) : 0 ≤ gridFormCell γ g := by
  unfold gridFormCell
  positivity

lemma gridEllCell_nonneg (hγ : 0 ≤ γ) (g : ℝ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ gridEllCell γ g c := by
  unfold gridEllCell
  have := gridSplitCell_nonneg γ g
  positivity

lemma gridEnergyCell_nonneg (hγ : 0 ≤ γ) (g : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ gridEnergyCell γ g c := by
  unfold gridEnergyCell
  have := gridSplitCell_nonneg γ g
  have := gridFormCell_nonneg hγ g
  positivity

/-- `J₀ ≤ c_J m̄² Q⁴` when `0 ≤ Z ≤ γ m̄ Q²`. -/
lemma J0g_le_poly (hg : 0 < g) (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hZ0 : 0 ≤ Z)
    (hZ : Z ≤ γ * M * Q ^ 2) : (J0g Z g : ℝ) ≤ gridSplitCell γ g * (M ^ 2 * Q ^ 4) := by
  have ha : 0 ≤ 1378 * (8 * Z / g ^ 2) ^ 2 := by positivity
  have hceil := Nat.ceil_lt_add_one ha
  have hJ : (J0g Z g : ℝ) = (Nat.ceil (1378 * (8 * Z / g ^ 2) ^ 2) : ℝ) + 1 := by
    unfold J0g
    push_cast
    ring
  have hMQ : 1 ≤ M ^ 2 * Q ^ 4 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM) (one_le_pow₀ hQ)
  have hZ2 : Z ^ 2 ≤ γ ^ 2 * (M ^ 2 * Q ^ 4) := by
    calc Z ^ 2 ≤ (γ * M * Q ^ 2) ^ 2 := pow_le_pow_left₀ hZ0 hZ 2
      _ = γ ^ 2 * (M ^ 2 * Q ^ 4) := by ring
  have hg4 : 0 < g ^ 4 := by positivity
  have he : 1378 * (8 * Z / g ^ 2) ^ 2 = 88192 * Z ^ 2 / g ^ 4 := by ring
  have h1 : 88192 * Z ^ 2 / g ^ 4 ≤ 88192 * γ ^ 2 / g ^ 4 * (M ^ 2 * Q ^ 4) := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hg4.le
    linarith [hZ2]
  rw [hJ]
  unfold gridSplitCell
  linarith [hceil, he, h1, hMQ]

/-- `Z J₀ ≤ γ c_J m̄³ Q⁶` when `0 ≤ Z ≤ γ m̄ Q²`. -/
lemma Z_mul_J0g_le_poly (hg : 0 < g) (hγ : 0 ≤ γ) (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hZ0 : 0 ≤ Z)
    (hZ : Z ≤ γ * M * Q ^ 2) :
    Z * (J0g Z g : ℝ) ≤ γ * gridSplitCell γ g * (M ^ 3 * Q ^ 6) := by
  have hJ := J0g_le_poly hg hM hQ hZ0 hZ
  have hJ0 : (0 : ℝ) ≤ J0g Z g := Nat.cast_nonneg _
  have hc := gridSplitCell_nonneg γ g
  calc Z * (J0g Z g : ℝ) ≤ (γ * M * Q ^ 2) * (gridSplitCell γ g * (M ^ 2 * Q ^ 4)) :=
        mul_le_mul hZ hJ hJ0 (by positivity)
    _ = γ * gridSplitCell γ g * (M ^ 3 * Q ^ 6) := by ring

/-- `C_form ≤ c_F m̄³ Q⁶` when `0 ≤ Z ≤ γ m̄ Q²`. -/
lemma Cform_le_poly (hg : 0 < g) (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hZ0 : 0 ≤ Z)
    (hZ : Z ≤ γ * M * Q ^ 2) : Cform Z g ≤ gridFormCell γ g * (M ^ 3 * Q ^ 6) := by
  have hZ2 : Z ^ 2 ≤ (γ * M * Q ^ 2) ^ 2 := pow_le_pow_left₀ hZ0 hZ 2
  have hZ3 : Z ^ 3 ≤ (γ * M * Q ^ 2) ^ 3 := pow_le_pow_left₀ hZ0 hZ 3
  have hMQ : M ^ 2 * Q ^ 4 ≤ M ^ 3 * Q ^ 6 := by
    have h1 : M ^ 2 ≤ M ^ 3 := pow_le_pow_right₀ hM (by norm_num)
    have h2 : Q ^ 4 ≤ Q ^ 6 := pow_le_pow_right₀ hQ (by norm_num)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hg2 : 0 < g ^ 2 := by positivity
  have hg4 : 0 < g ^ 4 := by positivity
  have hC : Cform Z g = 260 * 508 * Z ^ 2 / g ^ 2 + 416 * 508 ^ 2 * Z ^ 3 / g ^ 4 := by
    unfold Cform Cboot
    ring
  rw [hC]
  unfold gridFormCell
  have e1 : 260 * 508 * Z ^ 2 / g ^ 2 ≤ 260 * 508 * γ ^ 2 / g ^ 2 * (M ^ 3 * Q ^ 6) := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hg2.le
    have e : (γ * M * Q ^ 2) ^ 2 = γ ^ 2 * (M ^ 2 * Q ^ 4) := by ring
    linarith [mul_le_mul_of_nonneg_left hMQ (sq_nonneg γ)]
  have e2 : 416 * 508 ^ 2 * Z ^ 3 / g ^ 4 ≤ 416 * 508 ^ 2 * γ ^ 3 / g ^ 4 * (M ^ 3 * Q ^ 6) := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hg4.le
    have e : (γ * M * Q ^ 2) ^ 3 = γ ^ 3 * (M ^ 3 * Q ^ 6) := by ring
    linarith
  linarith

/-- `Ell(y) ≤ c_E(c) P` for an energy `y ≤ c P`, when `m̄³ Q⁶ ≤ P` and `0 ≤ Z ≤ γ m̄ Q²`. -/
lemma Ell_le_poly (hg : 0 < g) (hγ : 0 ≤ γ) (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hZ0 : 0 ≤ Z)
    (hZ : Z ≤ γ * M * Q ^ 2) {y c P : ℝ} (hP : M ^ 3 * Q ^ 6 ≤ P) (hy : y ≤ c * P) :
    Ell Z g y ≤ gridEllCell γ g c * P := by
  have hZJ := Z_mul_J0g_le_poly hg hγ hM hQ hZ0 hZ
  have hMQ1 : 1 ≤ M ^ 3 * Q ^ 6 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM) (one_le_pow₀ hQ)
  have hP1 : 1 ≤ P := hMQ1.trans hP
  have hc0 := gridSplitCell_nonneg γ g
  have hZJ' : Z * (J0g Z g : ℝ) ≤ γ * gridSplitCell γ g * P :=
    hZJ.trans (mul_le_mul_of_nonneg_left hP (by positivity))
  have hg2 : 0 < 3 * g ^ 2 := by positivity
  have e : Ell Z g y =
      4 / 3 + 8 * y / (3 * g ^ 2) + 208 * (Z * (J0g Z g : ℝ)) / (3 * g ^ 2) := by
    unfold Ell
    field_simp
    ring
  rw [e]
  unfold gridEllCell
  have h1 : 8 * y / (3 * g ^ 2) ≤ 8 * c / (3 * g ^ 2) * P := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hg2.le
    linarith
  have h2 : 208 * (Z * (J0g Z g : ℝ)) / (3 * g ^ 2) ≤
      208 * γ * gridSplitCell γ g / (3 * g ^ 2) * P := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hg2.le
    linarith
  linarith

/-- `E_big ≤ c_B(c) x² m̄¹¹ Q¹⁸` for an energy budget `0 ≤ E_b ≤ c x m̄ Q⁴` with `x ≥ 1`, when
`0 ≤ Z ≤ γ m̄ Q²`. -/
lemma Ebig_le_poly (hg : 0 < g) (hγ : 0 ≤ γ) (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hZ0 : 0 ≤ Z)
    (hZ : Z ≤ γ * M * Q ^ 2) {x c Eb : ℝ} (hx : 1 ≤ x) (hc : 0 ≤ c) (hEb0 : 0 ≤ Eb)
    (hEb : Eb ≤ c * (x * M * Q ^ 4)) :
    Ebig M Z g Eb ≤ gridEnergyCell γ g c * (x ^ 2 * M ^ 11 * Q ^ 18) := by
  set P := x ^ 2 * M ^ 11 * Q ^ 18 with hPdef
  set P1 := x * (M ^ 3 * Q ^ 6) with hP1def
  have hM0 : 0 ≤ M := by linarith
  have hMQ1 : 1 ≤ M ^ 3 * Q ^ 6 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM) (one_le_pow₀ hQ)
  have hP1P : M ^ 3 * Q ^ 6 ≤ P1 := le_mul_of_one_le_left (by positivity) hx
  have hxMQ : x * M * Q ^ 4 ≤ P1 := by
    have h1 : M ≤ M ^ 3 := le_self_pow₀ hM (by norm_num)
    have h2 : Q ^ 4 ≤ Q ^ 6 := pow_le_pow_right₀ hQ (by norm_num)
    calc x * M * Q ^ 4 = x * (M * Q ^ 4) := by ring
      _ ≤ x * (M ^ 3 * Q ^ 6) := by gcongr
  have hEbP1 : Eb ≤ c * P1 := hEb.trans (mul_le_mul_of_nonneg_left hxMQ hc)
  have hEll := Ell_le_poly hg hγ hM hQ hZ0 hZ hP1P hEbP1
  have hEll0 : 0 ≤ Ell Z g Eb := Ell_nonneg hZ0 hEb0
  have hCf := Cform_le_poly hg hM hQ hZ0 hZ
  have hcE := gridEllCell_nonneg hγ g hc
  have hcF := gridFormCell_nonneg hγ g
  have hcJ := gridSplitCell_nonneg γ g
  have hsq : (M * Ell Z g Eb) ^ 2 ≤ (M * (gridEllCell γ g c * P1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hEll hM0) 2
  have hT2 : Cform Z g * (M * Ell Z g Eb) ^ 2 ≤
      gridFormCell γ g * gridEllCell γ g c ^ 2 * P := by
    calc Cform Z g * (M * Ell Z g Eb) ^ 2
        ≤ (gridFormCell γ g * (M ^ 3 * Q ^ 6)) * (M * (gridEllCell γ g c * P1)) ^ 2 :=
          mul_le_mul hCf hsq (sq_nonneg _) (by positivity)
      _ = gridFormCell γ g * gridEllCell γ g c ^ 2 * P := by rw [hPdef, hP1def]; ring
  have hMQP : M ^ 3 * Q ^ 6 ≤ P := by
    have h1 : 1 ≤ x ^ 2 := one_le_pow₀ hx
    have h2 : M ^ 3 ≤ M ^ 11 := pow_le_pow_right₀ hM (by norm_num)
    have h3 : Q ^ 6 ≤ Q ^ 18 := pow_le_pow_right₀ hQ (by norm_num)
    calc M ^ 3 * Q ^ 6 = 1 * M ^ 3 * Q ^ 6 := by ring
      _ ≤ x ^ 2 * M ^ 11 * Q ^ 18 := by gcongr
  have hP1 : 1 ≤ P := hMQ1.trans hMQP
  have hZJ := Z_mul_J0g_le_poly hg hγ hM hQ hZ0 hZ
  have hT1 : 52 * Z * (J0g Z g : ℝ) + g ^ 2 / 4 ≤
      (52 * γ * gridSplitCell γ g + g ^ 2 / 4) * P := by
    have h1 : Z * (J0g Z g : ℝ) ≤ γ * gridSplitCell γ g * P :=
      hZJ.trans (mul_le_mul_of_nonneg_left hMQP (by positivity))
    have h2 : g ^ 2 / 4 ≤ g ^ 2 / 4 * P := le_mul_of_one_le_right (by positivity) hP1
    linarith
  have hEbP : Eb ≤ c * P := by
    refine hEbP1.trans (mul_le_mul_of_nonneg_left ?_ hc)
    calc P1 = x * (M ^ 3 * Q ^ 6) := rfl
      _ ≤ x * x * (M ^ 3 * Q ^ 6) := by
          have : x ≤ x * x := le_mul_of_one_le_right (by linarith) hx
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ P := by
          have h2 : M ^ 3 ≤ M ^ 11 := pow_le_pow_right₀ hM (by norm_num)
          have h3 : Q ^ 6 ≤ Q ^ 18 := pow_le_pow_right₀ hQ (by norm_num)
          rw [hPdef]
          calc x * x * (M ^ 3 * Q ^ 6) = x ^ 2 * M ^ 3 * Q ^ 6 := by ring
            _ ≤ x ^ 2 * M ^ 11 * Q ^ 18 := by gcongr
  have hP0 : 0 ≤ P := by linarith
  unfold Ebig gridEnergyCell
  apply max_le
  · linarith [mul_nonneg hc hP0, mul_nonneg (mul_nonneg hcF (sq_nonneg (gridEllCell γ g c))) hP0]
  · have hA : 0 ≤ (52 * γ * gridSplitCell γ g + g ^ 2 / 4) * P := by positivity
    linarith

/-- `C_grid ≤ c_F c_E(c_B(c))² x⁴ m̄²⁷ Q⁴²` for an energy budget `0 ≤ E_b ≤ c x m̄ Q⁴` with
`x ≥ 1`, when `0 ≤ Z ≤ γ m̄ Q²`. -/
lemma Cgrid_le_poly (hg : 0 < g) (hγ : 0 ≤ γ) (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hZ0 : 0 ≤ Z)
    (hZ : Z ≤ γ * M * Q ^ 2) {x c Eb : ℝ} (hx : 1 ≤ x) (hc : 0 ≤ c) (hEb0 : 0 ≤ Eb)
    (hEb : Eb ≤ c * (x * M * Q ^ 4)) :
    Cgrid M Z g Eb ≤ gridFormCell γ g * gridEllCell γ g (gridEnergyCell γ g c) ^ 2 *
      (x ^ 4 * M ^ 27 * Q ^ 42) := by
  have hB := Ebig_le_poly hg hγ hM hQ hZ0 hZ hx hc hEb0 hEb
  have hM0 : 0 ≤ M := by linarith
  have hMQP : M ^ 3 * Q ^ 6 ≤ x ^ 2 * M ^ 11 * Q ^ 18 := by
    have h1 : 1 ≤ x ^ 2 := one_le_pow₀ hx
    have h2 : M ^ 3 ≤ M ^ 11 := pow_le_pow_right₀ hM (by norm_num)
    have h3 : Q ^ 6 ≤ Q ^ 18 := pow_le_pow_right₀ hQ (by norm_num)
    calc M ^ 3 * Q ^ 6 = 1 * M ^ 3 * Q ^ 6 := by ring
      _ ≤ x ^ 2 * M ^ 11 * Q ^ 18 := by gcongr
  have hEll := Ell_le_poly hg hγ hM hQ hZ0 hZ hMQP hB
  have hEll0 : 0 ≤ Ell Z g (Ebig M Z g Eb) := Ell_nonneg hZ0 (Ebig_nonneg hZ0)
  have hCf := Cform_le_poly hg hM hQ hZ0 hZ
  have hcF := gridFormCell_nonneg hγ g
  have hsq : (M * Ell Z g (Ebig M Z g Eb)) ^ 2 ≤
      (M * (gridEllCell γ g (gridEnergyCell γ g c) * (x ^ 2 * M ^ 11 * Q ^ 18))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hEll hM0) 2
  unfold Cgrid
  calc Cform Z g * (M * Ell Z g (Ebig M Z g Eb)) ^ 2
      ≤ (gridFormCell γ g * (M ^ 3 * Q ^ 6)) *
          (M * (gridEllCell γ g (gridEnergyCell γ g c) * (x ^ 2 * M ^ 11 * Q ^ 18))) ^ 2 :=
        mul_le_mul hCf hsq (sq_nonneg _) (by positivity)
    _ = gridFormCell γ g * gridEllCell γ g (gridEnergyCell γ g c) ^ 2 *
          (x ^ 4 * M ^ 27 * Q ^ 42) := by ring

end PolyArith

/-! ## The constants of a Coulomb system -/

section CoulombBounds

variable {eta : ℕ} {ν : Type*} [Fintype ν]

/-- The register coupling `Σ_t |c_t| γ_t` of a Coulomb system is `γ W`, with the coupling
weight `W = Σ_{a<b} |q_a q_b| + (Σ_a |q_a|) Z_tot` of the release file. -/
lemma Zc_regParticlesOf (sys : CoulombSystem eta ν) (gamma : ℝ) :
    Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData gamma =
      gamma * sys.couplingWeight := by
  unfold Zc CoulombSystem.couplingWeight
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, mul_add, Finset.mul_sum,
    FiniteBONuclearData.totalCharge, Finset.sum_mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun pr _ => ?_
    simp only [RegParticles.tcoef, coupling, regParticlesOf_charge]
    ring
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [RegParticles.tcoef, coupling, regParticlesOf_charge, abs_neg]
    simp only [posNucleiOf, PosNuclei.toNucData]
    ring

/-- The coupling of the register potential is `m̄ γ_L W ≤ γ_L m̄ Q²`. -/
lemma coulombGridCoupling_le (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    coulombGridCoupling sys L ≤ coulombCellAmplitude L * sys.maxMass * sys.chargeWeight ^ 2 := by
  have hγ := (coulombCellAmplitude_pos hL).le
  have hM := sys.maxMass_pos.le
  unfold coulombGridCoupling
  rw [Zc_regParticlesOf]
  calc sys.maxMass * (coulombCellAmplitude L * sys.couplingWeight)
      ≤ sys.maxMass * (coulombCellAmplitude L * sys.chargeWeight ^ 2) := by
        gcongr
        exact sys.couplingWeight_le
    _ = coulombCellAmplitude L * sys.maxMass * sys.chargeWeight ^ 2 := by ring

lemma coulombGridCoupling_nonneg (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    0 ≤ coulombGridCoupling sys L :=
  mul_nonneg sys.maxMass_pos.le (Zc_nonneg (coulombCellAmplitude_pos hL).le)

/-- The grid energy budget is at most `2 (1 + G_L) (1 + η³) m̄ Q⁴`. -/
lemma coulombGridEnergyBudget_le (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    coulombGridEnergyBudget sys L ≤
      2 * (1 + coulombBudgetCellFactor L) *
        ((1 + (eta : ℝ) ^ 3) * sys.maxMass * sys.chargeWeight ^ 4) := by
  have h := coulombGroundEnergyBudget_add_one_le sys L hL
  unfold coulombGridEnergyBudget
  linarith

lemma coulombGridEnergyBudget_nonneg (sys : CoulombSystem eta ν) (L : ℝ) :
    0 ≤ coulombGridEnergyBudget sys L := by
  unfold coulombGridEnergyBudget
  have := coulombGroundEnergyBudget_nonneg sys L
  linarith

/-- The cell factor of the grid error constant, `512 g³ c_F c_E(c_B)² + 4 F_L (1 + G_L)³` with
`c_B = c_B(2 (1 + G_L))`, `g = 2π/L` and `γ_L = 1/(πL)`; it depends only on `L`. -/
noncomputable def coulombGridCellFactor (L : ℝ) : ℝ :=
  512 * (2 * Real.pi / L) ^ 3 * gridFormCell (coulombCellAmplitude L) (2 * Real.pi / L) *
      gridEllCell (coulombCellAmplitude L) (2 * Real.pi / L)
        (gridEnergyCell (coulombCellAmplitude L) (2 * Real.pi / L)
          (2 * (1 + coulombBudgetCellFactor L))) ^ 2 +
    4 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3

/-- `η² ≤ 1 + η³`. -/
lemma sq_le_one_add_cube (eta : ℕ) : (eta : ℝ) ^ 2 ≤ 1 + (eta : ℝ) ^ 3 := by
  rcases le_or_gt (eta : ℝ) 1 with h | h
  · have h1 : (eta : ℝ) ^ 2 ≤ 1 := pow_le_one₀ (Nat.cast_nonneg eta) h
    have h2 : (0 : ℝ) ≤ (eta : ℝ) ^ 3 := by positivity
    linarith
  · have h1 : (eta : ℝ) ^ 2 ≤ (eta : ℝ) ^ 3 := pow_le_pow_right₀ h.le (by norm_num)
    linarith

/-- The error constant of the grid theorem is bounded by a polynomial in `η`, `m̄` and the
charge weight `Q`: `C_L (1 + η³)⁴ m̄²⁷ Q⁴²`. -/
theorem coulombGridErrorConstant_le_poly (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    coulombGridErrorConstant sys L ≤
      coulombGridCellFactor L * (1 + (eta : ℝ) ^ 3) ^ 4 * sys.maxMass ^ 27 *
        sys.chargeWeight ^ 42 := by
  have hg : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hM : 1 ≤ sys.maxMass := sys.one_le_maxMass
  have hQ : 1 ≤ sys.chargeWeight := sys.one_le_chargeWeight
  have hx : 1 ≤ 1 + (eta : ℝ) ^ 3 := by
    have : (0 : ℝ) ≤ (eta : ℝ) ^ 3 := by positivity
    linarith
  have hG : 0 ≤ coulombBudgetCellFactor L := coulombBudgetCellFactor_nonneg L
  have hc : 0 ≤ 2 * (1 + coulombBudgetCellFactor L) := by positivity
  have hCg := Cgrid_le_poly hg hγ hM hQ (coulombGridCoupling_nonneg sys L hL)
    (coulombGridCoupling_le sys L hL) hx hc (coulombGridEnergyBudget_nonneg sys L)
    (coulombGridEnergyBudget_le sys L hL)
  have hCd := coulombDataCubicErrorConstant_le_coarse sys L hL
  have hη2 := sq_le_one_add_cube eta
  have hF : 0 ≤ coulombPolyCellFactor L := coulombPolyCellFactor_nonneg L
  set x := 1 + (eta : ℝ) ^ 3 with hxdef
  set M := sys.maxMass
  set Q := sys.chargeWeight
  set F := coulombPolyCellFactor L
  set G := coulombBudgetCellFactor L
  have hData : coulombDataCubicErrorConstant sys L / 8 ≤
      4 * F * (1 + G) ^ 3 * (x ^ 4 * M ^ 27 * Q ^ 42) := by
    have h1 : (eta : ℝ) ^ 2 * x ^ 3 ≤ x ^ 4 := by
      calc (eta : ℝ) ^ 2 * x ^ 3 ≤ x * x ^ 3 := by gcongr
        _ = x ^ 4 := by ring
    have h2 : M ^ 10 ≤ M ^ 27 := pow_le_pow_right₀ hM (by norm_num)
    have h3 : Q ^ 26 ≤ Q ^ 42 := pow_le_pow_right₀ hQ (by norm_num)
    calc coulombDataCubicErrorConstant sys L / 8
        ≤ 32 * F * (1 + G) ^ 3 * (eta : ℝ) ^ 2 * M ^ 10 * Q ^ 26 * x ^ 3 / 8 := by gcongr
      _ = 4 * F * (1 + G) ^ 3 * ((eta : ℝ) ^ 2 * x ^ 3 * M ^ 10 * Q ^ 26) := by ring
      _ ≤ 4 * F * (1 + G) ^ 3 * (x ^ 4 * M ^ 27 * Q ^ 42) := by gcongr
  have hg3 : 0 ≤ 512 * (2 * Real.pi / L) ^ 3 := by positivity
  have hCg' := mul_le_mul_of_nonneg_left hCg hg3
  unfold coulombGridErrorConstant coulombGridCellFactor
  linarith [hCg', hData]

/-- The cell factor of the grid threshold, `T_L + (1 + 32 F_L)(1 + G_L)/(2g) + 8 (1 + c_B)/g + 14`
with `c_B = c_B(2 (1 + G_L))` and `g = 2π/L`; it depends only on `L`. -/
noncomputable def coulombGridThresholdCellFactor (L : ℝ) : ℝ :=
  coulombThresholdCellFactor L +
    (1 + 32 * coulombPolyCellFactor L) * (1 + coulombBudgetCellFactor L) /
      (2 * (2 * Real.pi / L)) +
    8 * (1 + gridEnergyCell (coulombCellAmplitude L) (2 * Real.pi / L)
      (2 * (1 + coulombBudgetCellFactor L))) / (2 * Real.pi / L) + 14

/-- The threshold of the grid theorem is bounded by a polynomial in `η`, `m̄` and `Q` of the
degrees of the cutoff threshold of milestone 151: `T'_L (1 + η)(1 + η³)² m̄⁸ Q²⁰`. -/
theorem coulombGridThreshold_le_poly (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    (coulombGridThreshold sys L : ℝ) ≤
      coulombGridThresholdCellFactor L * (1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 *
        sys.maxMass ^ 8 * sys.chargeWeight ^ 20 := by
  have hg : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hM : 1 ≤ sys.maxMass := sys.one_le_maxMass
  have hQ : 1 ≤ sys.chargeWeight := sys.one_le_chargeWeight
  have hη0 : (0 : ℝ) ≤ eta := Nat.cast_nonneg eta
  have hx : 1 ≤ 1 + (eta : ℝ) ^ 3 := by
    have : (0 : ℝ) ≤ (eta : ℝ) ^ 3 := by positivity
    linarith
  have hG : 0 ≤ coulombBudgetCellFactor L := coulombBudgetCellFactor_nonneg L
  have hc : 0 ≤ 2 * (1 + coulombBudgetCellFactor L) := by positivity
  have hZ0 := coulombGridCoupling_nonneg sys L hL
  have hBig := Ebig_le_poly hg hγ hM hQ hZ0 (coulombGridCoupling_le sys L hL) hx hc
    (coulombGridEnergyBudget_nonneg sys L) (coulombGridEnergyBudget_le sys L hL)
  have hThr := coulombDataCubicThreshold_le_poly sys L hL
  have hCd := coulombDataCubicErrorConstant_le_coarse sys L hL
  have hCd0 := coulombDataCubicErrorConstant_nonneg sys L
  have hF : 0 ≤ coulombPolyCellFactor L := coulombPolyCellFactor_nonneg L
  have hB0 : 0 ≤ gridEnergyCell (coulombCellAmplitude L) (2 * Real.pi / L)
      (2 * (1 + coulombBudgetCellFactor L)) := gridEnergyCell_nonneg hγ _ hc
  have hT' : coulombGridThresholdCellFactor L * (1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 *
        sys.maxMass ^ 8 * sys.chargeWeight ^ 20 =
      (coulombThresholdCellFactor L +
        (1 + 32 * coulombPolyCellFactor L) * (1 + coulombBudgetCellFactor L) /
          (2 * (2 * Real.pi / L)) +
        8 * (1 + gridEnergyCell (coulombCellAmplitude L) (2 * Real.pi / L)
          (2 * (1 + coulombBudgetCellFactor L))) / (2 * Real.pi / L) + 14) *
      ((1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 * sys.maxMass ^ 8 * sys.chargeWeight ^ 20) := by
    unfold coulombGridThresholdCellFactor
    ring
  rw [hT']
  unfold coulombGridThreshold
  push_cast
  set g := 2 * Real.pi / L with hgdef
  set x := 1 + (eta : ℝ) ^ 3 with hxdef
  set M := sys.maxMass
  set Q := sys.chargeWeight
  set F := coulombPolyCellFactor L
  set G := coulombBudgetCellFactor L
  set B := gridEnergyCell (coulombCellAmplitude L) g (2 * (1 + G))
  set C := coulombDataCubicErrorConstant sys L
  set P := (1 + (eta : ℝ)) * x ^ 2 * M ^ 8 * Q ^ 20 with hPdef
  have hM0 : 0 ≤ M := by linarith
  -- monomials below `P`
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
  have hxx : x ≤ x ^ 2 := le_self_pow₀ hx (by norm_num)
  have hM4 : M ^ 4 ≤ M ^ 8 := pow_le_pow_right₀ hM (by norm_num)
  have hM6 : M ^ 6 ≤ M ^ 8 := pow_le_pow_right₀ hM (by norm_num)
  have hQ9 : Q ^ 9 ≤ Q ^ 20 := pow_le_pow_right₀ hQ (by norm_num)
  have h1η : 1 ≤ 1 + (eta : ℝ) := by linarith
  have hyP : (1 + (eta : ℝ)) * x * M ^ 4 * Q ^ 9 ≤ P := by
    rw [hPdef]
    gcongr
  have hwP : x * M ^ 6 * Q ^ 9 ≤ P := by
    rw [hPdef]
    calc x * M ^ 6 * Q ^ 9 = 1 * x * M ^ 6 * Q ^ 9 := by ring
      _ ≤ (1 + (eta : ℝ)) * x ^ 2 * M ^ 8 * Q ^ 20 := by gcongr
  have hP1 : 1 ≤ P := by
    have h1 : (1 : ℝ) ≤ x * M ^ 6 * Q ^ 9 := by
      have := one_le_pow₀ (n := 6) hM
      have := one_le_pow₀ (n := 9) hQ
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ x * M ^ 6 * Q ^ 9 := by gcongr
    linarith
  have hηP : (eta : ℝ) ≤ P := by
    have : (eta : ℝ) ≤ (1 + (eta : ℝ)) * 1 := by linarith
    calc (eta : ℝ) ≤ (1 + (eta : ℝ)) * 1 := this
      _ ≤ (1 + (eta : ℝ)) * (x ^ 2 * M ^ 8 * Q ^ 20) := by
          gcongr
          have := one_le_pow₀ (n := 8) hM
          have := one_le_pow₀ (n := 20) hQ
          calc (1 : ℝ) = 1 * 1 * 1 := by ring
            _ ≤ x ^ 2 * M ^ 8 * Q ^ 20 := by gcongr
      _ = P := by rw [hPdef]; ring
  -- the cutoff threshold
  have ha : (coulombDataCubicThreshold sys L : ℝ) ≤ coulombThresholdCellFactor L * P := by
    refine hThr.trans (le_of_eq ?_)
    rw [hPdef]
    ring
  -- the cube-root term
  have hroot : C ^ ((1 : ℝ) / 3) ≤
      (1 + 32 * F) * (1 + G) * ((1 + (eta : ℝ)) * x * M ^ 4 * Q ^ 9) := by
    set y := (1 + 32 * F) * (1 + G) * ((1 + (eta : ℝ)) * x * M ^ 4 * Q ^ 9) with hydef
    have hy0 : 0 ≤ y := by positivity
    have hCy : C ≤ y ^ 3 := by
      refine hCd.trans ?_
      have h1 : 32 * F ≤ (1 + 32 * F) ^ 3 := by
        have h0 : 1 ≤ 1 + 32 * F := by linarith
        calc 32 * F ≤ 1 + 32 * F := by linarith
          _ ≤ (1 + 32 * F) ^ 3 := le_self_pow₀ h0 (by norm_num)
      have h2 : (eta : ℝ) ^ 2 ≤ (1 + (eta : ℝ)) ^ 3 := by
        calc (eta : ℝ) ^ 2 ≤ (1 + (eta : ℝ)) ^ 2 := by gcongr; linarith
          _ ≤ (1 + (eta : ℝ)) ^ 3 := pow_le_pow_right₀ h1η (by norm_num)
      have h3 : M ^ 10 ≤ M ^ 12 := pow_le_pow_right₀ hM (by norm_num)
      have h4 : Q ^ 26 ≤ Q ^ 27 := pow_le_pow_right₀ hQ (by norm_num)
      calc 32 * F * (1 + G) ^ 3 * (eta : ℝ) ^ 2 * M ^ 10 * Q ^ 26 * x ^ 3
          ≤ (1 + 32 * F) ^ 3 * (1 + G) ^ 3 * (1 + (eta : ℝ)) ^ 3 * M ^ 12 * Q ^ 27 * x ^ 3 := by
            gcongr
        _ = y ^ 3 := by rw [hydef]; ring
    calc C ^ ((1 : ℝ) / 3) ≤ (y ^ 3) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hCd0 hCy (by norm_num)
      _ = y := by
          rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast hy0 (by norm_num)
  have hcc : ((Nat.ceil (C ^ ((1 : ℝ) / 3) / (2 * g)) : ℕ) : ℝ) ≤
      (1 + 32 * F) * (1 + G) / (2 * g) * P + 1 := by
    have h0 : 0 ≤ C ^ ((1 : ℝ) / 3) / (2 * g) := by
      have := Real.rpow_nonneg hCd0 ((1 : ℝ) / 3)
      positivity
    have h1 := Nat.ceil_lt_add_one h0
    have h2 : C ^ ((1 : ℝ) / 3) / (2 * g) ≤ (1 + 32 * F) * (1 + G) / (2 * g) * P := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc C ^ ((1 : ℝ) / 3)
          ≤ (1 + 32 * F) * (1 + G) * ((1 + (eta : ℝ)) * x * M ^ 4 * Q ^ 9) := hroot
        _ ≤ (1 + 32 * F) * (1 + G) * P := by gcongr
    linarith
  -- the bootstrap term
  have hdd : ((Nat.ceil (2 * Real.sqrt (M * Ebig M (coulombGridCoupling sys L) g
      (coulombGridEnergyBudget sys L)) / g) : ℕ) : ℝ) ≤ 2 * (1 + B) / g * P + 1 := by
    have hsqrt : Real.sqrt (M * Ebig M (coulombGridCoupling sys L) g
        (coulombGridEnergyBudget sys L)) ≤ (1 + B) * (x * M ^ 6 * Q ^ 9) := by
      have hw0 : 0 ≤ (1 + B) * (x * M ^ 6 * Q ^ 9) := by positivity
      rw [← Real.sqrt_sq hw0]
      apply Real.sqrt_le_sqrt
      have hB2 : B ≤ (1 + B) ^ 2 := by linarith [sq_nonneg B]
      calc M * Ebig M (coulombGridCoupling sys L) g (coulombGridEnergyBudget sys L)
          ≤ M * (B * (x ^ 2 * M ^ 11 * Q ^ 18)) := mul_le_mul_of_nonneg_left hBig hM0
        _ = B * (x * M ^ 6 * Q ^ 9) ^ 2 := by ring
        _ ≤ (1 + B) ^ 2 * (x * M ^ 6 * Q ^ 9) ^ 2 := by gcongr
        _ = ((1 + B) * (x * M ^ 6 * Q ^ 9)) ^ 2 := by ring
    have h0 : 0 ≤ 2 * Real.sqrt (M * Ebig M (coulombGridCoupling sys L) g
        (coulombGridEnergyBudget sys L)) / g := by positivity
    have h1 := Nat.ceil_lt_add_one h0
    have h2 : 2 * Real.sqrt (M * Ebig M (coulombGridCoupling sys L) g
        (coulombGridEnergyBudget sys L)) / g ≤ 2 * (1 + B) / g * P := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hg.le
      calc 2 * Real.sqrt (M * Ebig M (coulombGridCoupling sys L) g
            (coulombGridEnergyBudget sys L))
          ≤ 2 * ((1 + B) * (x * M ^ 6 * Q ^ 9)) := by linarith
        _ ≤ 2 * (1 + B) * P := by
            have h3 : (1 + B) * (x * M ^ 6 * Q ^ 9) ≤ (1 + B) * P :=
              mul_le_mul_of_nonneg_left hwP (by linarith)
            linarith
    linarith
  -- assembly
  have hTP : 0 ≤ coulombThresholdCellFactor L * P := le_trans (Nat.cast_nonneg _) ha
  have hcP : 0 ≤ (1 + 32 * F) * (1 + G) / (2 * g) * P := by positivity
  have hdP : 0 ≤ 2 * (1 + B) / g * P := by positivity
  have hdd4 : 4 * ((Nat.ceil (2 * Real.sqrt (M * Ebig M (coulombGridCoupling sys L) g
      (coulombGridEnergyBudget sys L)) / g) : ℕ) : ℝ) ≤ 8 * (1 + B) / g * P + 4 := by
    have e : 8 * (1 + B) / g * P = 4 * (2 * (1 + B) / g * P) := by ring
    linarith
  calc _ ≤ (coulombThresholdCellFactor L * P + P + ((1 + 32 * F) * (1 + G) / (2 * g) * P + 1) +
          (8 * (1 + B) / g * P + 4)) + 8 := by
        gcongr
        refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
        · linarith
        · linarith
        · linarith
        · linarith
    _ ≤ (coulombThresholdCellFactor L + (1 + 32 * F) * (1 + G) / (2 * g) +
          8 * (1 + B) / g + 14) * P := by
        linarith

/-! ## The Born--Oppenheimer constants -/

/-- The error constant of the Born--Oppenheimer grid theorem is bounded by a polynomial in `η`
and `Z_tot`: `C_L (1 + η³)⁴ (1 + η + Z_tot)⁴²`. -/
theorem gridErrorConstant_le_poly (eta : ℕ) (data : FiniteBONuclearData ν) (L : ℝ)
    (hL : 0 < L) :
    gridErrorConstant eta data L ≤
      coulombGridCellFactor L * (1 + (eta : ℝ) ^ 3) ^ 4 *
        (1 + eta + data.totalCharge) ^ 42 := by
  have h := coulombGridErrorConstant_le_poly (CoulombSystem.bo eta data) L hL
  rw [CoulombSystem.maxMass_bo, CoulombSystem.chargeWeight_bo] at h
  simpa [gridErrorConstant] using h

/-- The threshold of the Born--Oppenheimer grid theorem is bounded by a polynomial in `η` and
`Z_tot`: `T'_L (1 + η)(1 + η³)² (1 + η + Z_tot)²⁰`. -/
theorem gridThreshold_le_poly (eta : ℕ) (data : FiniteBONuclearData ν) (L : ℝ) (hL : 0 < L) :
    (gridThreshold eta data L : ℝ) ≤
      coulombGridThresholdCellFactor L * (1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 *
        (1 + eta + data.totalCharge) ^ 20 := by
  have h := coulombGridThreshold_le_poly (CoulombSystem.bo eta data) L hL
  rw [CoulombSystem.maxMass_bo, CoulombSystem.chargeWeight_bo] at h
  simpa [gridThreshold] using h

end CoulombBounds

end PlaneWaveGrid

/-! ════════════════════════════════════════════════════════════════════
## Part `FullKernel`
════════════════════════════════════════════════════════════════════ -/

/-!
Full-kernel collocation, `prop:fullkernel` (namespace `PlaneWaveFullKernel`; former development
files `dev/DevFK1.lean` to `dev/DevFK7.lean`).
-/

-- BEGIN SOURCE dev/DevFK1.lean
-- SHA256 86fe135aba266f2e0ad9820d2d4156f62719992b979ccffc2b258d69e613db5a
section DevFK1

/-!
# Full-kernel collocation (`prop:fullkernel`): the alias kernel and the full Hamiltonian

`prop:fullkernel` treats the collocation, on the padded register (radius `2m`, `n' = 4m+1`
points per direction), of the *maximal* band-limited kernel
`w_{≤4K}(y) = Σ_{0 < ‖ν‖∞ ≤ 4m} (γ/|ν|²) e^{2πi ν·y}` (Fourier support the full difference
set, transfers up to `4K`).  At the grid points the mode `ν` only sees `ν mod n'`, so in the
momentum basis of the register the collocated pair and nuclear terms are cyclic transfers whose
coefficient at the cyclic transfer `d` is the *folded* coefficient (`foldK`)

  `Σ_{‖ν‖∞ ≤ 4m, ν ≡ d (mod n')} k(ν)`,

with `k = kee γ` (pairs) or `k = knuc D γ ℓ` (nuclei, where the phase is that of `ν`, not of the
centred representative of `d`).  The term `ν = gl d` is the coefficient of the sharp kernel
`w_{≤2K}` of the grid files (`sharpKernel γ m`); the others (at most seven congruent modes)
form the *alias* coefficient (`aliasK`).  Each congruent mode beyond the zone has a component of
modulus at least `n' - 2m = 2m+1`, so it contributes at most `c/(2m+1)²` (`c = γ` for pairs,
`ζ_ℓ γ` for nuclei), and the alias coefficient is at most `8 c/(2m+1)²`.  So

  `H_full = H_grid(w_{≤2K}) + V_alias`   (`HfullMom_eq`),

and with the core's identity `H_grid = H_gal + Δ` (`Hgrid_eq`),
`H_full = P H P + R_full` with `R_full = Δ + V_alias` (`HfullMom_eq_gal`): no transfer is
dropped.

This section sets up grid Hamiltonians with arbitrary coefficient functions (`genTerm`, `vGen`,
`Hgen`; the core's `Hgrid` is the instance `kgr κ`, `kgn D κ`, `Hgen_grid`), their Hermiticity,
exchange symmetry, invariance under relabellings, and operator and tail bounds under a
Coulomb-type coefficient bound (`genRegHam`), and the fold and alias coefficients with their
bounds: at most eight congruent transfers (`card_fiber_le`), `|alias| ≤ 8 c/(2m+1)²`
(`norm_aliasK_le`), the Coulomb-type bounds `|alias| ≤ 24 c/|ν|²` and `|fold| ≤ 25 c/|ν|²`
(`aliasK_kernelBound`, `foldK_kernelBound`), the vanishing at zero transfer and the symmetries.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace PlaneWaveFullKernel

open PlaneWaveGrid

noncomputable section

/-! ## Grid Hamiltonians with arbitrary coefficients -/

section Generic

variable {ν : Type*} [Fintype ν] (eta m : ℕ)

/-- Grid terms with pair coefficient `kp` and nuclear coefficients `kn`: cyclic transfers, the
coefficient evaluated at the centred transfer. -/
def genTerm (kp : Lat3 → ℂ) (kn : ν → Lat3 → ℂ) :
    Term eta ν → RCfg eta m → RCfg eta m → ℂ
  | Sum.inl pr => tk (gRel2 pr.1.1 pr.1.2) (gTau pr.1.1) kp
  | Sum.inr il => tk (Spec1 il.1) (gTau il.1) (kn il.2)

/-- The potential kernel `Σ_t c_t (term t)`. -/
def vGen (P : RegParticles eta) (kp : Lat3 → ℂ) (kn : ν → Lat3 → ℂ) (q p : RCfg eta m) : ℂ :=
  ∑ t, (P.tcoef t : ℂ) * genTerm eta m kp kn t q p

/-- The grid Hamiltonian with coefficients `kp`, `kn`. -/
def Hgen (P : RegParticles eta) (kp : Lat3 → ℂ) (kn : ν → Lat3 → ℂ) (g : ℝ) :
    EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  wMul (kinT eta m P g) + kOp (vGen eta m P kp kn)

variable {eta m}

lemma genTerm_grid (D : NucData ν) (κ : Lat3 → ℝ) :
    genTerm eta m (kgr κ) (kgn D κ) = gridTerm eta m D κ := by
  funext t
  cases t <;> rfl

lemma vGen_grid (P : RegParticles eta) (D : NucData ν) (κ : Lat3 → ℝ) :
    vGen eta m P (kgr κ) (kgn D κ) = vGridK eta m P D κ := by
  funext q p
  simp only [vGen, vGridK, genTerm_grid]

lemma Hgen_grid (P : RegParticles eta) (D : NucData ν) (κ : Lat3 → ℝ) (g : ℝ) :
    Hgen eta m P (kgr κ) (kgn D κ) g = Hgrid eta m P D κ g := by
  simp only [Hgen, Hgrid, vGen_grid]

lemma tk_add_kernel {ι : Type*} [Fintype ι] [DecidableEq ι] (rel : ι → ι → Prop)
    (tau : ι → ι → Lat3) (k1 k2 : Lat3 → ℂ) (q p : ι) :
    tk rel tau (k1 + k2) q p = tk rel tau k1 q p + tk rel tau k2 q p := by
  by_cases h : rel q p
  · rw [tk_of_rel h, tk_of_rel h, tk_of_rel h, Pi.add_apply]
  · rw [tk_of_not_rel h, tk_of_not_rel h, tk_of_not_rel h, add_zero]

lemma genTerm_add (kp kp' : Lat3 → ℂ) (kn kn' : ν → Lat3 → ℂ) (t : Term eta ν)
    (q p : RCfg eta m) :
    genTerm eta m (kp + kp') (kn + kn') t q p =
      genTerm eta m kp kn t q p + genTerm eta m kp' kn' t q p := by
  cases t with
  | inl pr => exact tk_add_kernel _ _ _ _ q p
  | inr il => exact tk_add_kernel _ _ _ _ q p

lemma vGen_add (P : RegParticles eta) (kp kp' : Lat3 → ℂ) (kn kn' : ν → Lat3 → ℂ) :
    vGen eta m P (kp + kp') (kn + kn') = vGen eta m P kp kn + vGen eta m P kp' kn' := by
  funext q p
  simp only [vGen, Pi.add_apply, genTerm_add, mul_add, Finset.sum_add_distrib]

lemma kOp_vGen_eq (P : RegParticles eta) (kp : Lat3 → ℂ) (kn : ν → Lat3 → ℂ)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    kOp (vGen eta m P kp kn) u = ∑ t, (P.tcoef t : ℂ) • kOp (genTerm eta m kp kn t) u :=
  kOp_coef_sum (P := P) (genTerm eta m kp kn) u

/-! ### Hermiticity and exchange symmetry -/

lemma vGen_herm (P : RegParticles eta) {kp : Lat3 → ℂ} {kn : ν → Lat3 → ℂ}
    (hkp : ∀ x, kp (-x) = conj (kp x)) (hkn : ∀ l x, kn l (-x) = conj (kn l x))
    (q p : RCfg eta m) :
    vGen eta m P kp kn p q = conj (vGen eta m P kp kn q p) := by
  unfold vGen
  rw [map_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  cases t with
  | inl pr => exact tk_herm (fun q p h => gRel2_symm' _ _ q p h) (gTau_antisymm _) hkp q p
  | inr il =>
    exact tk_herm (fun q p h => spec1_symm' _ q p h) (gTau_antisymm _) (hkn il.2) q p

/-- The kernel of an even pair coefficient is invariant under a relabelling of the registers
that preserves the charges. -/
lemma vGen_perm (P : RegParticles eta) {kp : Lat3 → ℂ} (kn : ν → Lat3 → ℂ)
    (hkpe : ∀ x, kp (-x) = kp x) (π : Equiv.Perm (Fin eta))
    (hπ : ∀ k, P.charge (π k) = P.charge k) (q p : RCfg eta m) :
    vGen eta m P kp kn (q ∘ π) (p ∘ π) = vGen eta m P kp kn q p := by
  unfold vGen
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · simp only [genTerm, RegParticles.tcoef]
    have h := pairs_sum_symm_C (fun i j => ((P.charge i * P.charge j : ℝ) : ℂ) *
        tk (gRel2 i j) (gTau i) kp q p)
      (fun i j => by rw [mul_comm (P.charge i), gPair_comm hkpe i j q p]) π
    rw [← h]
    refine sum_congr rfl fun pr _ => ?_
    simp only [hπ]
    congr 1
    exact tk_swap_congr (gRel2_perm π _ _ q p) rfl
  · simp only [genTerm, RegParticles.tcoef]
    rw [← Equiv.sum_comp (Equiv.prodCongr π.symm (Equiv.refl ν))]
    refine sum_congr rfl fun il _ => ?_
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply]
    rw [charge_symm_apply hπ]
    congr 1
    refine tk_swap_congr ?_ ?_
    · rw [spec1_perm, Equiv.apply_symm_apply]
    · simp only [gTau, Function.comp_apply, Equiv.apply_symm_apply]

lemma Hgen_isSymmetric (P : RegParticles eta) {kp : Lat3 → ℂ} {kn : ν → Lat3 → ℂ}
    (hkp : ∀ x, kp (-x) = conj (kp x)) (hkn : ∀ l x, kn l (-x) = conj (kn l x)) (g : ℝ) :
    (Hgen eta m P kp kn g).IsSymmetric :=
  (wMul_isSymmetric _).add (kOp_isSymmetric _ (vGen_herm P hkp hkn))

lemma Hgen_sec (P : RegParticles eta) {kp : Lat3 → ℂ} (kn : ν → Lat3 → ℂ)
    (hkpe : ∀ x, kp (-x) = kp x) (g : ℝ) {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ}
    (hP : ∀ a b, lab a = lab b → P.mass a = P.mass b ∧ P.charge a = P.charge b)
    (u : EuclideanSpace ℂ (RCfg eta m)) (hu : IsSec sgn lab u) :
    IsSec sgn lab (Hgen eta m P kp kn g u) := by
  intro a b hab hlab q
  have h1 := wMul_preserves_sec (kinT eta m P g)
    (fun a b _ hl q => kinT_perm (Equiv.swap a b) (swap_invariant (hP a b hl).1) q) u hu
    a b hab hlab q
  have h2 := kOp_preserves_sec (vGen eta m P kp kn)
    (fun a b _ hl q p => vGen_perm P kn hkpe (Equiv.swap a b) (swap_invariant (hP a b hl).2) q p)
    u hu a b hab hlab q
  simp only [Hgen, LinearMap.add_apply, PiLp.add_apply]
  rw [h1, h2]
  ring

/-- A grid Hamiltonian with an even pair coefficient commutes with every relabelling of the
registers that preserves the masses and charges. -/
lemma Hgen_gridPermute (P : RegParticles eta) {kp : Lat3 → ℂ} (kn : ν → Lat3 → ℂ)
    (hkpe : ∀ x, kp (-x) = kp x) (g : ℝ) (π : Equiv.Perm (Fin eta))
    (hπ : ∀ k, P.mass (π k) = P.mass k ∧ P.charge (π k) = P.charge k)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    Hgen eta m P kp kn g (gridPermute π u) = gridPermute π (Hgen eta m P kp kn g u) := by
  simp only [Hgen, LinearMap.add_apply, map_add]
  rw [wMul_gridPermute _ _ (fun q => kinT_perm π (fun k => (hπ k).1) q),
    kOp_gridPermute _ _ (fun q p => vGen_perm P kn hkpe π (fun k => (hπ k).2) q p)]

/-! ### Operator and tail bounds under a Coulomb-type coefficient bound -/

variable {D : NucData ν} {gamma : ℝ}

lemma genTerm_op (hg : 0 ≤ gamma) {kp : Lat3 → ℂ} {kn : ν → Lat3 → ℂ}
    (hkp : KernelBound kp gamma) (hkn : ∀ l, KernelBound (kn l) (D.charge l * gamma))
    (t : Term eta ν) (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖kOp (genTerm eta m kp kn t) u‖ ≤ coupling eta D gamma t * (26 * J) * ‖u‖ +
      coupling eta D gamma t * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  have hc := coupling_nonneg (D := D) hg t
  cases t with
  | inl pr =>
    have h := norm_kOp_tk_le hkp hg (gRel2_rowInj pr.1.1 pr.1.2)
      (gRel2_colInj pr.1.1 pr.1.2) (gSlice2_data pr.1.1 pr.1.2) J hJ u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))
  | inr il =>
    have h := norm_kOp_tk_le (hkn il.2) (mul_nonneg (D.charge_nonneg il.2) hg)
      (spec1_rowInj_g il.1) (spec1_colInj_g il.1) (slice1_data il.1) J hJ u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))

lemma genTerm_tail (hg : 0 ≤ gamma) {kp : Lat3 → ℂ} {kn : ν → Lat3 → ℂ}
    (hkp : KernelBound kp gamma) (hkn : ∀ l, KernelBound (kn l) (D.charge l * gamma))
    (t : Term eta ν) (J T : ℕ) (hJ : 1 ≤ J) (hJT : J ≤ T) (hT : T ≤ 2 * m) (r : Fin eta)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) (kOp (genTerm eta m kp kn t) u)‖ ≤
      coupling eta D gamma t * (26 * J) * ‖maskOp (High (T - J) r) u‖ +
      coupling eta D gamma t * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  have hc := coupling_nonneg (D := D) hg t
  cases t with
  | inl pr =>
    have h := norm_mask_kOp_tk_le hkp hg (gRel2_rowInj pr.1.1 pr.1.2)
      (gRel2_colInj pr.1.1 pr.1.2) (gSlice2_data pr.1.1 pr.1.2) J hJ (High T r)
      (High (T - J) r) (fun q p hr hd hq => gRel2_lowDich pr.1.1 pr.1.2 J T hJT hT r q p hr hd hq) u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))
  | inr il =>
    have h := norm_mask_kOp_tk_le (hkn il.2) (mul_nonneg (D.charge_nonneg il.2) hg)
      (spec1_rowInj_g il.1) (spec1_colInj_g il.1) (slice1_data il.1) J hJ (High T r)
      (High (T - J) r) (fun q p hr hd hq => spec1_lowDich_g il.1 J T hJT hT r q p hr hd hq) u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))

lemma vGen_op (P : RegParticles eta) (hg : 0 ≤ gamma) {kp : Lat3 → ℂ} {kn : ν → Lat3 → ℂ}
    (hkp : KernelBound kp gamma) (hkn : ∀ l, KernelBound (kn l) (D.charge l * gamma))
    (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖kOp (vGen eta m P kp kn) u‖ ≤ Zc P D gamma * (26 * J) * ‖u‖ +
      Zc P D gamma * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  rw [kOp_vGen_eq]
  refine (norm_sum_le _ _).trans ?_
  have := sum_coupling_bound (P := P) (D := D) (gamma := gamma)
    (fun t => ‖(P.tcoef t : ℂ) • kOp (genTerm eta m kp kn t) u‖) ((26 * J) * ‖u‖)
    (Real.sqrt (1378 / J) * ‖wMul wTot u‖)
    (fun t => (norm_coef_smul_le _ _ (genTerm_op (D := D) hg hkp hkn t J hJ u)).trans
      (le_of_eq (by ring)))
  linarith

lemma vGen_tail (P : RegParticles eta) (hg : 0 ≤ gamma) {kp : Lat3 → ℂ} {kn : ν → Lat3 → ℂ}
    (hkp : KernelBound kp gamma) (hkn : ∀ l, KernelBound (kn l) (D.charge l * gamma))
    (J T : ℕ) (hJ : 1 ≤ J) (hJT : J ≤ T) (hT : T ≤ 2 * m) (r : Fin eta)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) (kOp (vGen eta m P kp kn) u)‖ ≤
      Zc P D gamma * (26 * J) * ‖maskOp (High (T - J) r) u‖ +
      Zc P D gamma * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  rw [kOp_vGen_eq, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have := sum_coupling_bound (P := P) (D := D) (gamma := gamma)
    (fun t => ‖maskOp (High T r) ((P.tcoef t : ℂ) • kOp (genTerm eta m kp kn t) u)‖)
    ((26 * J) * ‖maskOp (High (T - J) r) u‖) (Real.sqrt (1378 / J) * ‖wMul wTot u‖)
    (fun t => by
      rw [LinearMap.map_smul]
      exact (norm_coef_smul_le _ _
        (genTerm_tail (D := D) hg hkp hkn t J T hJ hJT hT r u)).trans (le_of_eq (by ring)))
  linarith

/-- A grid Hamiltonian with Coulomb-type coefficients as a register Hamiltonian
(mass-weighted weight, coupling `m̄ Z_c`). -/
def genRegHam (P : RegParticles eta) (D : NucData ν) (hgamma : 0 ≤ gamma) {kp : Lat3 → ℂ}
    {kn : ν → Lat3 → ℂ} (hkp : KernelBound kp gamma)
    (hkn : ∀ l, KernelBound (kn l) (D.charge l * gamma)) {g : ℝ} (hg : 0 < g) :
    RegHam (RCfg eta m) where
  W := wM P
  kin := kinT eta m P g
  V := kOp (vGen eta m P kp kn)
  g := g
  g_pos := hg
  kin_eq := fun _ => rfl
  W_ge_one := wM_ge_one P
  Z := P.maxMass * Zc P D gamma
  Z_nonneg := mul_nonneg P.maxMass_pos.le (Zc_nonneg hgamma)
  J0 := J0g (P.maxMass * Zc P D gamma) g
  J0_pos := J0g_pos _ _
  small := J0g_small (mul_nonneg P.maxMass_pos.le (Zc_nonneg hgamma)) hg
  op_bound := fun u => op_bound_mass P u (Zc_nonneg hgamma) _
    (vGen_op P hgamma hkp hkn _ (J0g_pos _ _) u)

/-- The coupling is linear in the amplitude. -/
lemma Zc_smul (P : RegParticles eta) (D : NucData ν) (a gamma : ℝ) :
    Zc P D (a * gamma) = a * Zc P D gamma := by
  unfold Zc
  rw [Finset.mul_sum]
  refine sum_congr rfl fun t _ => ?_
  cases t with
  | inl pr => simp only [coupling]; ring
  | inr il => simp only [coupling]; ring

end Generic

/-! ## The fold and alias coefficients of the maximal kernel -/

section Fold

variable {m : ℕ}

/-- The integer transfers of `S` congruent to `x` modulo `n' = 4m+1`, componentwise. -/
def fiber (m : ℕ) (S : Finset Lat3) (x : Lat3) : Finset Lat3 :=
  S.filter fun nu => castLat (n := 2 * (2 * m) + 1) nu = castLat x

lemma mem_fiber {S : Finset Lat3} {x nu : Lat3} :
    nu ∈ fiber m S x ↔ nu ∈ S ∧ castLat (n := 2 * (2 * m) + 1) nu = castLat x := by
  simp only [fiber, Finset.mem_filter]

/-- The folded coefficient at the cyclic transfer of `x` (`‖x‖∞ ≤ 2m`): the sum of `k ν` over the
transfers `‖ν‖∞ ≤ 4m` of the maximal kernel congruent to `x` modulo `4m+1`. -/
def foldK (m : ℕ) (k : Lat3 → ℂ) (x : Lat3) : ℂ :=
  if InBox (2 * m) x then ∑ nu ∈ fiber m (PlaneWaveGrid.box (4 * m)) x, k nu else 0

/-- The alias coefficient: the same sum over the congruent transfers beyond the register zone,
`2m < ‖ν‖∞ ≤ 4m`. -/
def aliasK (m : ℕ) (k : Lat3 → ℂ) (x : Lat3) : ℂ :=
  if InBox (2 * m) x then
    ∑ nu ∈ fiber m (PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) x, k nu
  else 0

/-- Two integers of modulus at most `4m` with the same sign and the same residue modulo
`4m+1` are equal. -/
lemma eq_of_cast_eq_of_sign {a b : ℤ} (ha : |a| ≤ ((4 * m : ℕ) : ℤ))
    (hb : |b| ≤ ((4 * m : ℕ) : ℤ))
    (hcast : ((a : ℤ) : ZMod (2 * (2 * m) + 1)) = ((b : ℤ) : ZMod (2 * (2 * m) + 1)))
    (hsign : a < 0 ↔ b < 0) : a = b := by
  have hdvd : ((2 * (2 * m) + 1 : ℕ) : ℤ) ∣ b - a :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a b _).mp hcast
  have hlt : |b - a| < ((2 * (2 * m) + 1 : ℕ) : ℤ) := by
    rw [abs_le] at ha hb
    rw [abs_lt]
    push_cast at ha hb ⊢
    by_cases h : a < 0
    · have hb' := hsign.mp h
      constructor <;> omega
    · have hb' : ¬ b < 0 := fun h' => h (hsign.mpr h')
      constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  omega

/-- At most eight transfers of the maximal zone are congruent to a given one (two per
component). -/
lemma card_fiber_le (x : Lat3) : (fiber m (PlaneWaveGrid.box (4 * m)) x).card ≤ 8 := by
  have h := Finset.card_le_card_of_injOn (s := fiber m (PlaneWaveGrid.box (4 * m)) x)
    (t := (Finset.univ : Finset (Fin 3 → Bool))) (fun nu c => decide (nu c < 0))
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
  · have hu : (Finset.univ : Finset (Fin 3 → Bool)).card = 8 := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      norm_num
    rw [hu] at h
    exact h
  · intro nu hnu nu' hnu' heq
    rw [Finset.mem_coe, mem_fiber, mem_box] at hnu hnu'
    funext c
    have hs := congrFun heq c
    simp only [decide_eq_decide] at hs
    have hc : castLat (n := 2 * (2 * m) + 1) nu c = castLat (n := 2 * (2 * m) + 1) nu' c := by
      rw [hnu.2, hnu'.2]
    exact eq_of_cast_eq_of_sign (hnu.1 c) (hnu'.1 c) hc hs

lemma fiber_alias_subset (x : Lat3) :
    fiber m (PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) x ⊆
      fiber m (PlaneWaveGrid.box (4 * m)) x :=
  Finset.filter_subset_filter _ Finset.sdiff_subset

lemma card_fiber_alias_le (x : Lat3) :
    (fiber m (PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) x).card ≤ 8 :=
  (Finset.card_le_card (fiber_alias_subset x)).trans (card_fiber_le x)

/-- On the register zone the only congruent transfer is the transfer itself. -/
lemma fiber_box_two {x : Lat3} (hx : InBox (2 * m) x) :
    fiber m (PlaneWaveGrid.box (2 * m)) x = {x} := by
  ext nu
  rw [mem_fiber, mem_box, Finset.mem_singleton]
  constructor
  · rintro ⟨hnu, hc⟩
    have h1 : gl (castLat (n := 2 * (2 * m) + 1) nu) = nu := gl_ofLat hnu
    have h2 : gl (castLat (n := 2 * (2 * m) + 1) x) = x := gl_ofLat hx
    rw [← h1, ← h2, hc]
  · rintro rfl
    exact ⟨hx, rfl⟩

/-- The fold is the coefficient of the sharp kernel plus the alias coefficient. -/
lemma foldK_eq (k : Lat3 → ℂ) (x : Lat3) :
    foldK m k x = (if InBox (2 * m) x then k x else 0) + aliasK m k x := by
  unfold foldK aliasK
  split_ifs with hx
  · have hsplit : fiber m (PlaneWaveGrid.box (4 * m)) x =
        fiber m (PlaneWaveGrid.box (2 * m)) x ∪
          fiber m (PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) x := by
      unfold fiber
      rw [← Finset.filter_union, Finset.union_sdiff_of_subset (box_mono (by omega))]
    have hdisj : Disjoint (fiber m (PlaneWaveGrid.box (2 * m)) x)
        (fiber m (PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) x) := by
      unfold fiber
      exact Finset.disjoint_filter_filter Finset.disjoint_sdiff
    rw [hsplit, Finset.sum_union hdisj, fiber_box_two hx, Finset.sum_singleton]
  · simp

/-- No transfer beyond the register zone is congruent to zero. -/
lemma fiber_alias_zero : fiber m (PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) 0 = ∅ := by
  ext nu
  simp only [mem_fiber, Finset.mem_sdiff, mem_box, Finset.notMem_empty, iff_false, not_and]
  rintro ⟨h4, h2⟩ hc
  apply h2
  have hz : nu = 0 := by
    funext c
    have hcc : ((nu c : ℤ) : ZMod (2 * (2 * m) + 1)) = 0 := by
      have := congrFun hc c
      simpa [castLat] using this
    have hdvd : ((2 * (2 * m) + 1 : ℕ) : ℤ) ∣ nu c :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcc
    have hlt : |nu c| < ((2 * (2 * m) + 1 : ℕ) : ℤ) := by
      have := h4 c
      push_cast at this ⊢
      omega
    simpa using Int.eq_zero_of_abs_lt_dvd hdvd hlt
  rw [hz]
  intro c
  simp

lemma aliasK_zero (k : Lat3 → ℂ) : aliasK m k 0 = 0 := by
  unfold aliasK
  rw [fiber_alias_zero]
  simp

/-- Each alias coefficient is at most `8 c/(2m+1)²` for coefficients bounded by `c/|ν|²`. -/
lemma norm_aliasK_le {k : Lat3 → ℂ} {c : ℝ} (hk : KernelBound k c) (hc : 0 ≤ c) (x : Lat3) :
    ‖aliasK m k x‖ ≤ 8 * c / (2 * (m : ℝ) + 1) ^ 2 := by
  have hpos : 0 < (2 * (m : ℝ) + 1) ^ 2 := by positivity
  unfold aliasK
  split_ifs with hx
  · refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ nu ∈ fiber m (PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) x,
        ‖k nu‖ ≤ c / (2 * (m : ℝ) + 1) ^ 2 := by
      intro nu hnu
      rw [mem_fiber, Finset.mem_sdiff, mem_box, mem_box] at hnu
      have h := coul_le_of_not_inBox hnu.1.2
      push_cast at h
      calc ‖k nu‖ ≤ c * coul nu := hk nu
        _ ≤ c * (1 / (2 * (m : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left h hc
        _ = c / (2 * (m : ℝ) + 1) ^ 2 := by ring
    have hcard :
        ((fiber m (PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) x).card : ℝ) ≤ 8 := by
      exact_mod_cast card_fiber_alias_le x
    calc ∑ nu ∈ fiber m (PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) x, ‖k nu‖
        ≤ ∑ _nu ∈ fiber m (PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) x,
            c / (2 * (m : ℝ) + 1) ^ 2 :=
          sum_le_sum h1
      _ = ((fiber m (PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) x).card : ℝ) *
            (c / (2 * (m : ℝ) + 1) ^ 2) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 8 * (c / (2 * (m : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (div_nonneg hc hpos.le)
      _ = 8 * c / (2 * (m : ℝ) + 1) ^ 2 := by ring
  · rw [norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hc) hpos.le

/-- On the register zone, `1/|x|² ≥ 1/(12 m²)` away from zero. -/
lemma coul_ge_of_inBox {x : Lat3} (hx : InBox (2 * m) x) (hx0 : x ≠ 0) :
    1 / (12 * (m : ℝ) ^ 2) ≤ coul x := by
  have hn : nsq x ≤ 12 * (m : ℝ) ^ 2 := by
    rw [nsq_eq_sum, Fin.sum_univ_three]
    have hc : ∀ c : Fin 3, ((x c : ℤ) : ℝ) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by
      intro c
      have h1 : |((x c : ℤ) : ℝ)| ≤ 2 * (m : ℝ) := by
        have := hx c
        rw [← Int.cast_abs]
        exact_mod_cast this
      have h2 : ((x c : ℤ) : ℝ) ^ 2 = |((x c : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
      rw [h2]
      have h3 : 0 ≤ |((x c : ℤ) : ℝ)| := abs_nonneg _
      nlinarith
    linarith [hc 0, hc 1, hc 2]
  have hpos : 0 < nsq x := by
    by_contra h
    push Not at h
    have h0 : nsq x = 0 := le_antisymm h (nsq_nonneg x)
    apply hx0
    funext c
    have h1 := sq_le_nsq x c
    rw [h0] at h1
    have h2 : ((x c : ℤ) : ℝ) = 0 := by nlinarith [sq_nonneg ((x c : ℤ) : ℝ)]
    exact_mod_cast h2
  unfold coul
  exact one_div_le_one_div_of_le hpos hn

/-- The alias coefficients satisfy the Coulomb-type bound `24 c/|ν|²`. -/
lemma aliasK_kernelBound {k : Lat3 → ℂ} {c : ℝ} (hk : KernelBound k c) (hc : 0 ≤ c) :
    KernelBound (aliasK m k) (24 * c) := by
  intro x
  by_cases hx : InBox (2 * m) x
  · by_cases hx0 : x = 0
    · subst hx0
      rw [aliasK_zero, norm_zero]
      exact mul_nonneg (by positivity) (coul_nonneg _)
    · have hm : 1 ≤ m := by
        by_contra h
        have hm0 : m = 0 := by omega
        subst hm0
        exact hx0 (inBox_zero_iff.mp (by simpa using hx))
      have h1 := norm_aliasK_le (m := m) hk hc x
      have h2 := coul_ge_of_inBox hx hx0
      have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have h3 : 8 * c / (2 * (m : ℝ) + 1) ^ 2 ≤ 24 * c * (1 / (12 * (m : ℝ) ^ 2)) := by
        have e : 24 * c * (1 / (12 * (m : ℝ) ^ 2)) = 2 * c / (m : ℝ) ^ 2 := by
          field_simp
          ring
        rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hc (by positivity : (0 : ℝ) ≤ 4 * m + 1)]
      calc ‖aliasK m k x‖ ≤ 8 * c / (2 * (m : ℝ) + 1) ^ 2 := h1
        _ ≤ 24 * c * (1 / (12 * (m : ℝ) ^ 2)) := h3
        _ ≤ 24 * c * coul x := mul_le_mul_of_nonneg_left h2 (by positivity)
  · unfold aliasK
    rw [if_neg hx, norm_zero]
    exact mul_nonneg (by positivity) (coul_nonneg _)

/-- The folded coefficients satisfy the Coulomb-type bound `25 c/|ν|²`. -/
lemma foldK_kernelBound {k : Lat3 → ℂ} {c : ℝ} (hk : KernelBound k c) (hc : 0 ≤ c) :
    KernelBound (foldK m k) (25 * c) := by
  intro x
  rw [foldK_eq]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(if InBox (2 * m) x then k x else 0 : ℂ)‖ ≤ c * coul x := by
    split_ifs
    · exact hk x
    · rw [norm_zero]; exact mul_nonneg hc (coul_nonneg x)
  have h2 := aliasK_kernelBound (m := m) hk hc x
  linarith

/-! ### Symmetries -/

lemma castLat_neg {n : ℕ} (nu : Lat3) : castLat (n := n) (-nu) = -castLat nu := by
  funext c
  simp [castLat]

lemma sum_fiber_neg (S : Finset Lat3) (hS : ∀ nu, nu ∈ S → -nu ∈ S) (k : Lat3 → ℂ)
    (x : Lat3) : ∑ nu ∈ fiber m S (-x), k nu = ∑ nu ∈ fiber m S x, k (-nu) := by
  refine Finset.sum_nbij' (fun nu => -nu) (fun nu => -nu) ?_ ?_ ?_ ?_ ?_
  · intro nu hnu
    rw [mem_fiber] at hnu ⊢
    refine ⟨hS nu hnu.1, ?_⟩
    rw [castLat_neg, hnu.2, castLat_neg, neg_neg]
  · intro nu hnu
    rw [mem_fiber] at hnu ⊢
    refine ⟨hS nu hnu.1, ?_⟩
    rw [castLat_neg, hnu.2, castLat_neg]
  · intro nu _; simp
  · intro nu _; simp
  · intro nu _; simp

lemma box_sdiff_neg (nu : Lat3) (h : nu ∈ PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m)) :
    -nu ∈ PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m) := by
  rw [Finset.mem_sdiff, mem_box, mem_box] at h ⊢
  exact ⟨inBox_neg_iff.mpr h.1, fun h' => h.2 (inBox_neg_iff.mp h')⟩

lemma aliasK_neg_conj {k : Lat3 → ℂ} (hk : ∀ nu, k (-nu) = conj (k nu)) (x : Lat3) :
    aliasK m k (-x) = conj (aliasK m k x) := by
  unfold aliasK
  by_cases hx : InBox (2 * m) x
  · rw [if_pos (inBox_neg_iff.mpr hx), if_pos hx, sum_fiber_neg _ box_sdiff_neg k x, map_sum]
    exact sum_congr rfl fun nu _ => hk nu
  · rw [if_neg (fun h => hx (inBox_neg_iff.mp h)), if_neg hx, map_zero]

lemma aliasK_neg {k : Lat3 → ℂ} (hk : ∀ nu, k (-nu) = k nu) (x : Lat3) :
    aliasK m k (-x) = aliasK m k x := by
  unfold aliasK
  by_cases hx : InBox (2 * m) x
  · rw [if_pos (inBox_neg_iff.mpr hx), if_pos hx, sum_fiber_neg _ box_sdiff_neg k x]
    exact sum_congr rfl fun nu _ => hk nu
  · rw [if_neg (fun h => hx (inBox_neg_iff.mp h)), if_neg hx]

lemma foldK_neg_conj {k : Lat3 → ℂ} (hk : ∀ nu, k (-nu) = conj (k nu)) (x : Lat3) :
    foldK m k (-x) = conj (foldK m k x) := by
  rw [foldK_eq, foldK_eq, aliasK_neg_conj hk, map_add]
  congr 1
  by_cases hx : InBox (2 * m) x
  · rw [if_pos (inBox_neg_iff.mpr hx), if_pos hx, hk]
  · rw [if_neg (fun h => hx (inBox_neg_iff.mp h)), if_neg hx, map_zero]

lemma foldK_neg {k : Lat3 → ℂ} (hk : ∀ nu, k (-nu) = k nu) (x : Lat3) :
    foldK m k (-x) = foldK m k x := by
  rw [foldK_eq, foldK_eq, aliasK_neg hk]
  congr 1
  by_cases hx : InBox (2 * m) x
  · rw [if_pos (inBox_neg_iff.mpr hx), if_pos hx, hk]
  · rw [if_neg (fun h => hx (inBox_neg_iff.mp h)), if_neg hx]

lemma kee_neg_conj (gamma : ℝ) (nu : Lat3) : kee gamma (-nu) = conj (kee gamma nu) := by
  rw [kee_neg, kee_conj]

end Fold

/-! ## The full-kernel Hamiltonian in the momentum basis -/

section Full

variable {ν : Type*} [Fintype ν] {eta : ℕ} (m : ℕ)

lemma foldK_kee_eq (gamma : ℝ) :
    foldK m (kee gamma) = kgr (sharpKernel gamma m) + aliasK m (kee gamma) := by
  funext x
  rw [foldK_eq, Pi.add_apply]
  congr 1
  unfold kgr sharpKernel kee
  split_ifs <;> simp

lemma foldK_knuc_eq (D : NucData ν) (gamma : ℝ) (l : ν) :
    foldK m (knuc D gamma l) = kgn D (sharpKernel gamma m) l + aliasK m (knuc D gamma l) := by
  funext x
  rw [foldK_eq, Pi.add_apply]
  congr 1
  unfold kgn kgr sharpKernel knuc kee
  split_ifs <;> simp

variable (eta)

/-- The full-kernel collocation Hamiltonian in the momentum basis of the register: the
kinetic multiplier and the cyclic transfers with the folded coefficients of the maximal kernel
`w_{≤4K}` (pairs and nuclei). -/
def HfullMom (P : RegParticles eta) (D : NucData ν) (gamma g : ℝ) :
    EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  Hgen eta m P (foldK m (kee gamma)) (fun l => foldK m (knuc D gamma l)) g

/-- The alias potential `V_alias`: the cyclic transfers with the alias coefficients. -/
def vAlias (P : RegParticles eta) (D : NucData ν) (gamma : ℝ) : RCfg eta m → RCfg eta m → ℂ :=
  vGen eta m P (aliasK m (kee gamma)) (fun l => aliasK m (knuc D gamma l))

variable {eta m}

lemma vFold_eq (P : RegParticles eta) (D : NucData ν) (gamma : ℝ) :
    vGen eta m P (foldK m (kee gamma)) (fun l => foldK m (knuc D gamma l)) =
      vGridK eta m P D (sharpKernel gamma m) + vAlias eta m P D gamma := by
  have h1 : (fun l => foldK m (knuc D gamma l)) =
      kgn D (sharpKernel gamma m) + (fun l => aliasK m (knuc D gamma l)) := by
    funext l x
    rw [foldK_knuc_eq]
    rfl
  rw [foldK_kee_eq, h1, vGen_add, vGen_grid]
  rfl

/-- **The full-kernel Hamiltonian is the sharp-kernel grid Hamiltonian plus the alias
potential.** -/
lemma HfullMom_eq (P : RegParticles eta) (D : NucData ν) (gamma g : ℝ)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    HfullMom eta m P D gamma g u =
      Hgrid eta m P D (sharpKernel gamma m) g u + kOp (vAlias eta m P D gamma) u := by
  simp only [HfullMom, Hgen, Hgrid, LinearMap.add_apply]
  rw [vFold_eq, kOp_add, LinearMap.add_apply]
  abel

/-- **`H_full = P H P + R_full`** with `R_full = Δ + V_alias` (`Δ = R - D` of the sharp
kernel): no transfer is dropped. -/
lemma HfullMom_eq_gal (P : RegParticles eta) (D : NucData ν) (gamma g : ℝ)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    HfullMom eta m P D gamma g u = Hgal eta m P D gamma g u +
      (Delta eta m P D gamma (sharpKernel gamma m) u + kOp (vAlias eta m P D gamma) u) := by
  rw [HfullMom_eq, Hgrid_eq (gamma := gamma)]
  abel

variable {gamma : ℝ}

lemma foldK_kee_bound (hg : 0 ≤ gamma) : KernelBound (foldK m (kee gamma)) (25 * gamma) :=
  foldK_kernelBound (kee_bound hg) hg

lemma foldK_knuc_bound (D : NucData ν) (hg : 0 ≤ gamma) (l : ν) :
    KernelBound (foldK m (knuc D gamma l)) (D.charge l * (25 * gamma)) := by
  intro x
  have h := foldK_kernelBound (m := m) (knuc_bound D hg l) (mul_nonneg (D.charge_nonneg l) hg) x
  calc ‖foldK m (knuc D gamma l) x‖ ≤ 25 * (D.charge l * gamma) * coul x := h
    _ = D.charge l * (25 * gamma) * coul x := by ring

lemma HfullMom_isSymmetric (P : RegParticles eta) (D : NucData ν) (gamma g : ℝ) :
    (HfullMom eta m P D gamma g).IsSymmetric :=
  Hgen_isSymmetric P (foldK_neg_conj (kee_neg_conj gamma))
    (fun l => foldK_neg_conj (knuc_neg D gamma l)) g

lemma HfullMom_sec (P : RegParticles eta) (D : NucData ν) (gamma g : ℝ) {sgn : Fin eta → ℂ}
    {lab : Fin eta → ℕ}
    (hP : ∀ a b, lab a = lab b → P.mass a = P.mass b ∧ P.charge a = P.charge b)
    (u : EuclideanSpace ℂ (RCfg eta m)) (hu : IsSec sgn lab u) :
    IsSec sgn lab (HfullMom eta m P D gamma g u) :=
  Hgen_sec P _ (foldK_neg (kee_neg gamma)) g hP u hu

/-- The full-kernel Hamiltonian commutes with every relabelling of the registers that
preserves the masses and charges. -/
lemma HfullMom_gridPermute (P : RegParticles eta) (D : NucData ν) (gamma g : ℝ)
    (π : Equiv.Perm (Fin eta))
    (hπ : ∀ k, P.mass (π k) = P.mass k ∧ P.charge (π k) = P.charge k)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    HfullMom eta m P D gamma g (gridPermute π u) =
      gridPermute π (HfullMom eta m P D gamma g u) :=
  Hgen_gridPermute P _ (foldK_neg (kee_neg gamma)) g π hπ u

/-- The full-kernel Hamiltonian as a register Hamiltonian, with the coupling of the amplitude
`25 γ` (the folded coefficients are at most `25 γ/|ν|²`). -/
def fullRegHam (P : RegParticles eta) (D : NucData ν) (hgamma : 0 ≤ gamma) {g : ℝ}
    (hg : 0 < g) : RegHam (RCfg eta m) :=
  genRegHam (m := m) P D (by positivity : (0 : ℝ) ≤ 25 * gamma) (foldK_kee_bound (m := m) hgamma)
    (foldK_knuc_bound (m := m) D hgamma) hg

/-- Tail bound of the full potential (amplitude `25 γ`), for thresholds in the register. -/
lemma vFull_tail (P : RegParticles eta) (D : NucData ν) (hgamma : 0 ≤ gamma) (J T : ℕ)
    (hJ : 1 ≤ J) (hJT : J ≤ T) (hT : T ≤ 2 * m) (r : Fin eta)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r)
        (kOp (vGen eta m P (foldK m (kee gamma)) (fun l => foldK m (knuc D gamma l))) u)‖ ≤
      Zc P D (25 * gamma) * (26 * J) * ‖maskOp (High (T - J) r) u‖ +
      Zc P D (25 * gamma) * Real.sqrt (1378 / J) * ‖wMul wTot u‖ :=
  vGen_tail P (by positivity) (foldK_kee_bound hgamma) (foldK_knuc_bound D hgamma) J T hJ hJT hT
    r u

end Full

end

end PlaneWaveFullKernel

end DevFK1
-- END SOURCE dev/DevFK1.lean

-- BEGIN SOURCE dev/DevFK2.lean
-- SHA256 3da10e6630a379e69fb1e853625b37b79fc1b74b11974c469bbb406b42c20b43
section DevFK2

/-!
# Full-kernel collocation: the position-space Hamiltonian and its fold identity

The collocation of the maximal band-limited kernel on the padded register: the kernel
`w_{≤4K}(y) = Σ_{0<‖ν‖∞ ≤ 4m} (γ/|ν|²) e^{2πi ν·y}` (`wKerFull`, transfers up to `4K`) sampled at
all particle separations and all particle–nucleus separations of the grid configuration
(`collPotFull`), with the kinetic multiplier through the DFT (`HposFull`).  At the grid points
the mode `ν` only sees `ν mod n'`, so summing the modes over the classes modulo `n'`
(`sum_box_four_fold`) gives the fold identity

  `dft ∘ H_full,pos = H_full ∘ dft`   (`dft_HposFull`),

with `H_full = HfullMom` the momentum operator of `DevFK1` (folded coefficients; for the
nuclei, the phase of each congruent mode).  Hence the position-space and momentum-space Ritz
energies of the full kernel coincide in every exchange sector (`isSecRitz_HposFull_iff`), and
the eigenvectors correspond under the DFT (`HposFull_eigen_iff`); `H_full,pos` commutes with
the relabellings that preserve masses and charges (`HposFull_gridPermute`).  For the record,
the kernel splits as the sharp kernel `w_{≤2K}` plus the band `2m < ‖ν‖∞ ≤ 4m`
(`wKerFull_eq`; not used in the proofs).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset UnitAddTorus

namespace PlaneWaveFullKernel

open PlaneWaveGrid

noncomputable section

section Position

variable {ν : Type*} [Fintype ν] {eta m : ℕ}

/-- The maximal band-limited kernel `w_{≤4K}` in unit-torus coordinates:
`Σ_{0 < ‖ν‖∞ ≤ 4m} (γ/|ν|²) e^{2πi ν·y}` (Fourier support the full difference set of the
register). -/
def wKerFull (gamma : ℝ) (m : ℕ) (y : UnitAddTorus (Fin 3)) : ℂ :=
  ∑ nu ∈ PlaneWaveGrid.box (4 * m), kee gamma nu * mFourier nu y

/-- The kernel `w_{≤4K}` is the sharp kernel `w_{≤2K}` plus the band `2m < ‖ν‖∞ ≤ 4m`. -/
lemma wKerFull_eq (gamma : ℝ) (m : ℕ) (y : UnitAddTorus (Fin 3)) :
    wKerFull gamma m y = wKer (sharpKernel gamma m) m y +
      ∑ nu ∈ PlaneWaveGrid.box (4 * m) \ PlaneWaveGrid.box (2 * m),
        kee gamma nu * mFourier nu y := by
  rw [wKerFull, ← Finset.sum_sdiff (box_mono (by omega : 2 * m ≤ 4 * m)), add_comm]
  congr 1
  rw [wKer]
  refine sum_congr rfl fun nu hnu => ?_
  rw [sharpKernel, if_pos (mem_box.mp hnu), kee]

/-- The collocated potential of the maximal kernel at the grid configuration `j`. -/
def collPotFull (P : RegParticles eta) (N : PosNuclei ν) (gamma : ℝ) (j : RCfg eta m) : ℂ :=
  (∑ pr : Pairs eta, ((P.charge pr.1.1 * P.charge pr.1.2 : ℝ) : ℂ) *
      wKerFull gamma m (gridPoint (j pr.1.1) - gridPoint (j pr.1.2))) +
    ∑ i : Fin eta, ∑ l : ν,
      ((P.charge i * N.charge l : ℝ) : ℂ) * wKerFull gamma m (gridPoint (j i) - N.position l)

/-- **The full-kernel collocation Hamiltonian** `H_full` on the padded register (`n' = 4m+1`
points per direction): kinetic multiplier through the DFT, potential by collocation of
`w_{≤4K}`. -/
def HposFull (P : RegParticles eta) (N : PosNuclei ν) (gamma g : ℝ) :
    EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  idft ∘ₗ wMul (kinT eta m P g) ∘ₗ dft + cMul (collPotFull (m := m) P N gamma)

/-- Summing the modes of the maximal zone over their classes modulo `n'`. -/
lemma sum_box_four_fold (c : Lat3 → ℂ) (y : Fin 3 → ZMod (2 * (2 * m) + 1)) :
    ∑ nu ∈ PlaneWaveGrid.box (4 * m), c nu * ech (dot3 (castLat nu) y) =
      ∑ d : GMode (2 * (2 * m) + 1), foldK m c (gl d) * ech (dot3 d y) := by
  classical
  rw [← Finset.sum_fiberwise (PlaneWaveGrid.box (4 * m)) (castLat (n := 2 * (2 * m) + 1))
    (fun nu => c nu * ech (dot3 (castLat nu) y))]
  refine sum_congr rfl fun d _ => ?_
  rw [foldK, if_pos (gl_inBox d), Finset.sum_mul]
  have hf : fiber m (PlaneWaveGrid.box (4 * m)) (gl d) =
      (PlaneWaveGrid.box (4 * m)).filter (fun nu => castLat (n := 2 * (2 * m) + 1) nu = d) := by
    unfold fiber
    rw [castLat_gl]
  rw [hf]
  refine sum_congr rfl fun nu hnu => ?_
  rw [(Finset.mem_filter.mp hnu).2]

lemma sum_box_neg (J : ℕ) (f : Lat3 → ℂ) :
    ∑ nu ∈ PlaneWaveGrid.box J, f (-nu) = ∑ nu ∈ PlaneWaveGrid.box J, f nu :=
  Finset.sum_nbij' (fun nu => -nu) (fun nu => -nu)
    (fun nu h => mem_box.mpr (inBox_neg_iff.mpr (by simpa using mem_box.mp h)))
    (fun nu h => mem_box.mpr (inBox_neg_iff.mpr (by simpa using mem_box.mp h)))
    (fun nu _ => neg_neg nu) (fun nu _ => neg_neg nu) (fun nu _ => rfl)

/-- A generic pair term against the characters. -/
lemma sum_chi_gpair_gen (kp : Lat3 → ℂ) {a b : Fin eta} (hab : a ≠ b) (q j : RCfg eta m) :
    ∑ p, chi p j * tk (gRel2 a b) (gTau a) kp q p =
      chi q j * ∑ d : GMode (2 * (2 * m) + 1), kp (gl d) * ech (dot3 d (j b - j a)) := by
  classical
  simp_rw [tk_gpair_eq_sum hab, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hl : ∀ d : GMode (2 * (2 * m) + 1), chi (shift2 a b d q) j * kp (gl d) =
      chi q j * (kp (gl d) * ech (dot3 d (j b - j a))) := by
    intro d
    rw [chi, dotC_shift2 hab, ech_add, ← chi]
    ring
  simp_rw [hl]

/-- A generic single-register term against the characters. -/
lemma sum_chi_gsing_gen (kn : Lat3 → ℂ) (a : Fin eta) (q j : RCfg eta m) :
    ∑ p, chi p j * tk (Spec1 a) (gTau a) kn q p =
      chi q j * ∑ d : GMode (2 * (2 * m) + 1), kn (gl d) * ech (-dot3 d (j a)) := by
  classical
  simp_rw [tk_gsing_eq_sum, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hl : ∀ d : GMode (2 * (2 * m) + 1), chi (shift1 a d q) j * kn (gl d) =
      chi q j * (kn (gl d) * ech (-dot3 d (j a))) := by
    intro d
    rw [chi, dotC_shift1, sub_eq_add_neg, ech_add, ← chi]
    ring
  simp_rw [hl]

/-- The pair fold: the folded pair coefficients against the characters are the samples of
`w_{≤4K}`. -/
lemma fold_pair (gamma : ℝ) (y z : Fin 3 → ZMod (2 * (2 * m) + 1)) :
    ∑ d : GMode (2 * (2 * m) + 1), foldK m (kee gamma) (gl d) * ech (dot3 d (z - y)) =
      wKerFull gamma m (gridPoint y - gridPoint z) := by
  rw [wKerFull]
  simp_rw [mFourier_sub_gridPoint]
  rw [sum_box_four_fold]
  rw [← Equiv.sum_comp (Equiv.neg (GMode (2 * (2 * m) + 1)))]
  refine sum_congr rfl fun d _ => ?_
  simp only [Equiv.neg_apply, gl_neg, foldK_neg (kee_neg gamma)]
  congr 2
  simp only [dot3, Pi.sub_apply, Pi.neg_apply]
  exact sum_congr rfl fun c _ => by ring

/-- The nuclear fold: the folded nuclear coefficients (the phase of each congruent mode)
against the characters are the samples of `-ζ_ℓ w_{≤4K}(· - R_ℓ)`. -/
lemma fold_nuc (N : PosNuclei ν) (gamma : ℝ) (l : ν) (y : Fin 3 → ZMod (2 * (2 * m) + 1)) :
    ∑ d : GMode (2 * (2 * m) + 1),
        foldK m (knuc N.toNucData gamma l) (gl d) * ech (-dot3 d y) =
      -(N.charge l : ℂ) * wKerFull gamma m (gridPoint y - N.position l) := by
  have h1 : -(N.charge l : ℂ) * wKerFull gamma m (gridPoint y - N.position l) =
      ∑ nu ∈ PlaneWaveGrid.box (4 * m),
        knuc N.toNucData gamma l nu * ech (dot3 (castLat nu) (-y)) := by
    rw [wKerFull, Finset.mul_sum]
    conv_rhs => rw [← sum_box_neg (4 * m)]
    refine sum_congr rfl fun nu _ => ?_
    rw [mFourier_sub_pos, castLat_neg]
    have e : dot3 (-castLat (n := 2 * (2 * m) + 1) nu) (-y) = dot3 (castLat nu) y := by
      simp only [dot3, Pi.neg_apply, neg_mul_neg]
    rw [e]
    simp only [knuc, PosNuclei.toNucData, kee_neg]
    ring
  rw [h1, sum_box_four_fold]
  refine sum_congr rfl fun d _ => ?_
  congr 2
  simp only [dot3, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- **Fold identity of the maximal kernel.** -/
lemma sum_chi_vFull (P : RegParticles eta) (N : PosNuclei ν) (gamma : ℝ) (q j : RCfg eta m) :
    ∑ p, chi p j *
        vGen eta m P (foldK m (kee gamma)) (fun l => foldK m (knuc N.toNucData gamma l)) q p =
      chi q j * collPotFull P N gamma j := by
  unfold vGen collPotFull
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Fintype.sum_sum_type, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine sum_congr rfl fun pr _ => ?_
    simp only [genTerm, RegParticles.tcoef]
    rw [sum_mul_coef, sum_chi_gpair_gen _ (ne_of_lt pr.2) q j, fold_pair]
    ring
  · rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun l _ => ?_
    simp only [genTerm, RegParticles.tcoef]
    rw [sum_mul_coef, sum_chi_gsing_gen _ i q j, fold_nuc]
    push_cast
    ring

lemma dft_cMul_full (P : RegParticles eta) (N : PosNuclei ν) (gamma : ℝ)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    dft (cMul (collPotFull P N gamma) u) =
      kOp (vGen eta m P (foldK m (kee gamma)) (fun l => foldK m (knuc N.toNucData gamma l)))
        (dft u) := by
  ext q
  simp only [dft, kOp_apply, cMul_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => ?_
  have h := sum_chi_vFull P N gamma q j
  calc collPotFull P N gamma j * u j * (chi q j / (Real.sqrt (Ncfg eta (2 * (2 * m) + 1)) : ℂ))
      = u j * (chi q j * collPotFull P N gamma j) /
          (Real.sqrt (Ncfg eta (2 * (2 * m) + 1)) : ℂ) := by ring
    _ = u j * (∑ p, chi p j * vGen eta m P (foldK m (kee gamma))
          (fun l => foldK m (knuc N.toNucData gamma l)) q p) /
          (Real.sqrt (Ncfg eta (2 * (2 * m) + 1)) : ℂ) := by rw [h]
    _ = ∑ p, u j * (chi p j / (Real.sqrt (Ncfg eta (2 * (2 * m) + 1)) : ℂ)) *
          vGen eta m P (foldK m (kee gamma)) (fun l => foldK m (knuc N.toNucData gamma l)) q p := by
        rw [Finset.mul_sum, Finset.sum_div]
        exact sum_congr rfl fun p _ => by ring

/-- **The DFT conjugates the position-space full-kernel Hamiltonian to the momentum
operator.** -/
lemma dft_HposFull (P : RegParticles eta) (N : PosNuclei ν) (gamma g : ℝ)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    dft (HposFull P N gamma g u) = HfullMom eta m P N.toNucData gamma g (dft u) := by
  simp only [HposFull, HfullMom, Hgen, LinearMap.add_apply, LinearMap.comp_apply, map_add,
    dft_idft, dft_cMul_full]

lemma inner_HposFull (P : RegParticles eta) (N : PosNuclei ν) (gamma g : ℝ)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    inner ℂ u (HposFull P N gamma g u) =
      inner ℂ (dft u) (HfullMom eta m P N.toNucData gamma g (dft u)) := by
  rw [← dft_HposFull, inner_dft_dft]

lemma dft_injective : Function.Injective
    (dft : EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m)) := by
  intro u v h
  rw [← idft_dft u, ← idft_dft v, h]

/-- Eigenvectors of the position-space and momentum-space full-kernel Hamiltonians correspond
under the DFT. -/
lemma HposFull_eigen_iff (P : RegParticles eta) (N : PosNuclei ν) (gamma g E : ℝ)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    HposFull P N gamma g u = (E : ℂ) • u ↔
      HfullMom eta m P N.toNucData gamma g (dft u) = (E : ℂ) • dft u := by
  constructor
  · intro h
    rw [← dft_HposFull, h, map_smul]
  · intro h
    apply dft_injective
    rw [dft_HposFull, h, map_smul]

/-- The position-space full-kernel Hamiltonian commutes with every relabelling of the registers
that preserves the masses and charges. -/
lemma HposFull_gridPermute (P : RegParticles eta) (N : PosNuclei ν) (gamma g : ℝ)
    (π : Equiv.Perm (Fin eta))
    (hπ : ∀ k, P.mass (π k) = P.mass k ∧ P.charge (π k) = P.charge k)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    HposFull P N gamma g (gridPermute π u) = gridPermute π (HposFull P N gamma g u) := by
  have hconj : ∀ v : EuclideanSpace ℂ (RCfg eta m),
      HposFull P N gamma g v = idft (HfullMom eta m P N.toNucData gamma g (dft v)) := by
    intro v
    rw [← dft_HposFull, idft_dft]
  rw [hconj, hconj, dft_gridPermute, HfullMom_gridPermute P _ gamma g π hπ, idft_gridPermute]

/-- **The position-space and momentum-space full-kernel Ritz energies coincide in every
exchange sector.** -/
theorem isSecRitz_HposFull_iff (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ) (P : RegParticles eta)
    (N : PosNuclei ν) (gamma g E : ℝ) :
    IsSecRitz sgn lab (HposFull (m := m) P N gamma g) E ↔
      IsSecRitz sgn lab (HfullMom eta m P N.toNucData gamma g) E := by
  constructor
  · rintro ⟨hlow, u, hu, hn, hv⟩
    refine ⟨fun c hc => ?_, dft u, dft_sec u hu, by rw [norm_dft, hn], ?_⟩
    · have h := hlow (idft c) (idft_sec c hc)
      rw [inner_HposFull, dft_idft] at h
      have hn' : ‖idft c‖ = ‖c‖ := by
        have := norm_dft (idft c); rw [dft_idft] at this; exact this.symm
      rwa [hn'] at h
    · rw [← inner_HposFull]; exact hv
  · rintro ⟨hlow, c, hc, hn, hv⟩
    refine ⟨fun u hu => ?_, idft c, idft_sec c hc, ?_, ?_⟩
    · have h := hlow (dft u) (dft_sec u hu)
      rw [norm_dft, ← inner_HposFull] at h
      exact h
    · have := norm_dft (idft c); rw [dft_idft] at this; rw [← this, hn]
    · rw [inner_HposFull, dft_idft]; exact hv

end Position

end

end PlaneWaveFullKernel

end DevFK2
-- END SOURCE dev/DevFK2.lean

-- BEGIN SOURCE dev/DevFK3.lean
-- SHA256 aa5639b3221c5b588c91741368bd1b35cb0da5844ef2eba67390ac59cb167717
section DevFK3

/-!
# Full-kernel collocation: the support identity and the alias form

The alias potential `V_alias` of `DevFK1` is a sum of cyclic shifts: for a pair term
`(a, b)` the coefficient of the cyclic transfer `d` multiplies the shift
`(S_ab(d) u)(q) = u(q - d e_a + d e_b)` (it maps the momentum state `|p⟩` to
`|p + d e_a - d e_b⟩`), and for a particle–nucleus term the one-register shift
`(S_a(d) u)(q) = u(q - d e_a)`.  So

  `⟨u, V_alias u⟩ = Σ_t c_t Σ_d alias_t(d) C_t(d; u)`   (`inner_vGen`),

with the cyclic correlations `C_t(d; u) = ⟨u, S_t(d) u⟩` (`corrPair`, `corrOne`, `termCorr`).
In the manuscript's convention `S_r(ν) φ_q = φ_{q - ν e_r}` (`eq:fourier-sign`), `S_ab(d)` is
`S_a(-d) S_b(d)`, so `C_ab(d; u)` is the cyclic pair correlation `C^cyc_ab(-d)` of the
manuscript; `C_a(d; u)` is a cyclic Fourier coefficient of the one-particle density of `a`.
Since `S_t(-d) = S_t(d)*`, `|C_t(-d; u)| = |C_t(d; u)|`, so sums of the moduli over `d ≠ 0` are
the same in either convention.  The alias coefficients vanish at `d = 0` and are at most
`8 c_t/(2m+1)²` (`DevFK1`).

**Support identity** (`not_inBox_sub`, `norm_corr_le_tail`): a cyclic shift by `d` with
`‖gl d‖∞ ≥ 2T + 1` maps every configuration whose register `a` lies in the box of radius `T`
to one whose register `a` lies outside it, wrapped or not.  Hence

  `|C_t(d; u)| ≤ 2 ‖u‖ t_a(T; u)`,  `t_a(T; u) = ‖1[‖k_a‖∞ > T] u‖`.

Grouping the transfers `d ≠ 0` in the shell pairs `2T < ‖gl d‖∞ ≤ 2T + 2` (at most
`208 (T+1)²` transfers each, `sum_modes_le_shells`), the bootstrapped tails
`t(T) ≤ B/(T² √T)` for `T ≥ T₀` give `Σ_{d ≠ 0} |C_t(d)| ≤ 208 T₀³ + 1872 B √m`
(`sum_corr_le_tails`), so

  `|⟨u, V_alias u⟩| ≤ Z_c · 8 (208 T₀³ + 1872 B √m)/(2m+1)² = O(K^{-3/2})`
  (`norm_inner_vAlias_le_tails`),

and under the summability `Σ_{d ≠ 0} |C_t(d; u)| ≤ C_ρ` for every term,
`|⟨u, V_alias u⟩| ≤ Z_c · 8 C_ρ/(2m+1)² = O(K^{-2})` (`norm_inner_vAlias_le_summable`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace PlaneWaveFullKernel

open PlaneWaveGrid

noncomputable section

/-! ## Shifts as permutations of the configurations -/

section Shifts

variable {eta M : ℕ}

lemma shift2_shift2_neg (a b : Fin eta) (d : GMode (2 * M + 1)) (q : GConfig eta (2 * M + 1)) :
    shift2 a b (-d) (shift2 a b d q) = q := by
  funext k
  by_cases hkb : k = b
  · subst hkb
    simp only [shift2, Function.update_self]
    abel
  · by_cases hka : k = a
    · subst hka
      simp only [shift2, Function.update_of_ne hkb, Function.update_self]
      abel
    · simp only [shift2, Function.update_of_ne hkb, Function.update_of_ne hka]

lemma shift2_neg_shift2 (a b : Fin eta) (d : GMode (2 * M + 1)) (q : GConfig eta (2 * M + 1)) :
    shift2 a b d (shift2 a b (-d) q) = q := by
  have h := shift2_shift2_neg a b (-d) q
  rwa [neg_neg] at h

/-- The pair shift as a permutation of the configurations. -/
def shift2Equiv (a b : Fin eta) (d : GMode (2 * M + 1)) :
    GConfig eta (2 * M + 1) ≃ GConfig eta (2 * M + 1) where
  toFun := shift2 a b d
  invFun := shift2 a b (-d)
  left_inv := shift2_shift2_neg a b d
  right_inv := shift2_neg_shift2 a b d

lemma shift1_shift1_neg (a : Fin eta) (d : GMode (2 * M + 1)) (q : GConfig eta (2 * M + 1)) :
    shift1 a (-d) (shift1 a d q) = q := by
  funext k
  by_cases hka : k = a
  · subst hka
    simp only [shift1, Function.update_self]
    abel
  · simp only [shift1, Function.update_of_ne hka]

lemma shift1_neg_shift1 (a : Fin eta) (d : GMode (2 * M + 1)) (q : GConfig eta (2 * M + 1)) :
    shift1 a d (shift1 a (-d) q) = q := by
  have h := shift1_shift1_neg a (-d) q
  rwa [neg_neg] at h

/-- The single-register shift as a permutation of the configurations. -/
def shift1Equiv (a : Fin eta) (d : GMode (2 * M + 1)) :
    GConfig eta (2 * M + 1) ≃ GConfig eta (2 * M + 1) where
  toFun := shift1 a d
  invFun := shift1 a (-d)
  left_inv := shift1_shift1_neg a d
  right_inv := shift1_neg_shift1 a d

/-- **Support identity, one component.** If the input lies in the box of radius `T` and the
cyclic transfer has a component of modulus beyond `2T`, the output lies outside the box of
radius `T`, wrapped or not. -/
lemma not_inBox_sub {x d : GMode (2 * M + 1)} {T : ℕ} (hx : InBox T (gl x))
    (hd : ¬ InBox (2 * T) (gl d)) : ¬ InBox T (gl (x - d)) := by
  simp only [InBox, not_forall, not_le] at hd ⊢
  obtain ⟨c, hc⟩ := hd
  refine ⟨c, ?_⟩
  have hxc := hx c
  obtain ⟨k, hk, he⟩ := valMinAbs_sub_decomp (x c) (d c)
  have hdb := valMinAbs_bounds (d c)
  have hvb := valMinAbs_bounds (x c - d c)
  simp only [gl, Pi.sub_apply] at hxc hc he ⊢
  push_cast at hc
  rw [abs_le] at hxc
  rw [lt_abs] at hc ⊢
  rcases hk with rfl | rfl | rfl <;> omega

end Shifts

/-! ## Cyclic correlations -/

section Correlations

variable {ι : Type*} [Fintype ι]

/-- A register vector composed with a permutation of the configurations. -/
def permVec (e : ι ≃ ι) (a : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun q => a (e q))

lemma norm_permVec (e : ι ≃ ι) (a : EuclideanSpace ℂ ι) : ‖permVec e a‖ = ‖a‖ := by
  have h : ‖permVec e a‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum]
    exact Equiv.sum_comp e (fun q => ‖a q‖ ^ 2)
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

lemma norm_sum_comp_mul_conj_le (e : ι ≃ ι) (a b : EuclideanSpace ℂ ι) :
    ‖∑ q, a (e q) * conj (b q)‖ ≤ ‖a‖ * ‖b‖ := by
  have h : ∑ q, a (e q) * conj (b q) = inner ℂ b (permVec e a) := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, permVec]
  rw [h]
  calc ‖inner ℂ b (permVec e a)‖ ≤ ‖b‖ * ‖permVec e a‖ := norm_inner_le_norm _ _
    _ = ‖a‖ * ‖b‖ := by rw [norm_permVec]; ring

/-- **The correlation of a shift that leaves a set's complement is controlled by the tail on
that set.** If the permutation `e` maps every configuration outside `P` into `P`, then
`|⟨u, S_e u⟩| ≤ 2 ‖u‖ ‖1_P u‖`. -/
lemma norm_corr_le_mask (u : EuclideanSpace ℂ ι) (e : ι ≃ ι) (P : ι → Prop)
    (h : ∀ q, ¬ P q → P (e q)) :
    ‖∑ q, u (e q) * conj (u q)‖ ≤ 2 * ‖u‖ * ‖maskOp P u‖ := by
  classical
  set v := maskOp P u with hv
  set w := maskOp (fun q => ¬ P q) u with hw
  have hvw : ∀ q, u q = v q + w q := by
    intro q
    by_cases hq : P q
    · rw [hv, hw, maskOp_apply_of P u hq, maskOp_apply_of_not (fun q => ¬ P q) u (not_not.mpr hq),
        add_zero]
    · rw [hv, hw, maskOp_apply_of_not P u hq, maskOp_apply_of (fun q => ¬ P q) u hq, zero_add]
  have hsplit : ∑ q, u (e q) * conj (u q) =
      ∑ q, v (e q) * conj (u q) + ∑ q, w (e q) * conj (v q) := by
    rw [← Finset.sum_add_distrib]
    refine sum_congr rfl fun q _ => ?_
    by_cases hq : P q
    · have h1 : v q = u q := by rw [hv, maskOp_apply_of P u hq]
      rw [h1, hvw (e q)]
      ring
    · have h1 : w (e q) = 0 := by
        rw [hw, maskOp_apply_of_not (fun q => ¬ P q) u (not_not.mpr (h q hq))]
      have h2 : v (e q) = u (e q) := by rw [hv, maskOp_apply_of P u (h q hq)]
      rw [h1, h2]
      ring
  have hwu : ‖w‖ ≤ ‖u‖ := norm_maskOp_le _ u
  rw [hsplit]
  calc ‖∑ q, v (e q) * conj (u q) + ∑ q, w (e q) * conj (v q)‖
      ≤ ‖∑ q, v (e q) * conj (u q)‖ + ‖∑ q, w (e q) * conj (v q)‖ := norm_add_le _ _
    _ ≤ ‖v‖ * ‖u‖ + ‖w‖ * ‖v‖ :=
        add_le_add (norm_sum_comp_mul_conj_le e v u) (norm_sum_comp_mul_conj_le e w v)
    _ ≤ ‖v‖ * ‖u‖ + ‖u‖ * ‖v‖ := by gcongr
    _ = 2 * ‖u‖ * ‖v‖ := by ring

end Correlations

section TermCorrelations

variable {ν : Type*} [Fintype ν] {eta m : ℕ}

/-- The cyclic pair correlation `⟨u, S_ab(d) u⟩` with `(S_ab(d) u)(q) = u(q - d e_a + d e_b)`;
in the manuscript's convention this is `C^cyc_ab(-d)` (and `|C^cyc_ab(-d)| = |C^cyc_ab(d)|`). -/
def corrPair (a b : Fin eta) (d : GMode (2 * (2 * m) + 1)) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ℂ :=
  ∑ q, u (shift2 a b d q) * conj (u q)

/-- The cyclic one-register correlation `⟨u, S_a(d) u⟩` with `(S_a(d) u)(q) = u(q - d e_a)`, a
cyclic Fourier coefficient of the one-particle density of `a`. -/
def corrOne (a : Fin eta) (d : GMode (2 * (2 * m) + 1)) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ℂ :=
  ∑ q, u (shift1 a d q) * conj (u q)

/-- The correlation of a term: the pair correlation of a particle pair, the one-register
correlation of the particle of a particle–nucleus term. -/
def termCorr : Term eta ν → GMode (2 * (2 * m) + 1) → EuclideanSpace ℂ (RCfg eta m) → ℂ
  | Sum.inl pr => corrPair pr.1.1 pr.1.2
  | Sum.inr il => corrOne il.1

/-- The register shifted by a term. -/
def termReg : Term eta ν → Fin eta
  | Sum.inl pr => pr.1.1
  | Sum.inr il => il.1

/-- The coefficient function of a term. -/
def termCoef (kp : Lat3 → ℂ) (kn : ν → Lat3 → ℂ) : Term eta ν → Lat3 → ℂ
  | Sum.inl _ => kp
  | Sum.inr il => kn il.2

/-- The summed correlations of a term over the nonzero cyclic transfers. -/
def corrSum (t : Term eta ν) (u : EuclideanSpace ℂ (RCfg eta m)) : ℝ :=
  ∑ d ∈ (univ : Finset (GMode (2 * (2 * m) + 1))).erase 0, ‖termCorr t d u‖

lemma termCorr_eq_shift (t : Term eta ν) (d : GMode (2 * (2 * m) + 1))
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ∃ e : RCfg eta m ≃ RCfg eta m, (∀ q, (e q) (termReg t) = q (termReg t) - d) ∧
      termCorr t d u = ∑ q, u (e q) * conj (u q) := by
  cases t with
  | inl pr =>
    exact ⟨shift2Equiv pr.1.1 pr.1.2 d, fun q => shift2_apply_a (ne_of_lt pr.2) d q, rfl⟩
  | inr il =>
    refine ⟨shift1Equiv il.1 d, fun q => ?_, rfl⟩
    change shift1 il.1 d q il.1 = q il.1 - d
    simp [shift1]

/-- **Support identity for the correlations.** -/
lemma norm_corr_le_tail (t : Term eta ν) {d : GMode (2 * (2 * m) + 1)} {T : ℕ}
    (hd : ¬ InBox (2 * T) (gl d)) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖termCorr t d u‖ ≤ 2 * ‖u‖ * ‖maskOp (High T (termReg t)) u‖ := by
  obtain ⟨e, he, hc⟩ := termCorr_eq_shift t d u
  rw [hc]
  refine norm_corr_le_mask u e _ fun q hq => ?_
  have hq' : InBox T (gl (q (termReg t))) := not_not.mp hq
  change ¬ InBox T (gl ((e q) (termReg t)))
  rw [he q]
  exact not_inBox_sub hq' hd

lemma norm_corr_le_one (t : Term eta ν) (d : GMode (2 * (2 * m) + 1))
    (u : EuclideanSpace ℂ (RCfg eta m)) : ‖termCorr t d u‖ ≤ ‖u‖ * ‖u‖ := by
  obtain ⟨e, -, hc⟩ := termCorr_eq_shift t d u
  rw [hc]
  exact norm_sum_comp_mul_conj_le e u u

/-- A grid pair term against a state, as a sum over the cyclic transfers. -/
lemma inner_kOp_gpair (kp : Lat3 → ℂ) {a b : Fin eta} (hab : a ≠ b)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    inner ℂ u (kOp (tk (gRel2 a b) (gTau a) kp) u) =
      ∑ d : GMode (2 * (2 * m) + 1), kp (gl d) * corrPair a b d u := by
  classical
  have h1 : ∀ q, (kOp (tk (gRel2 a b) (gTau a) kp) u) q =
      ∑ d : GMode (2 * (2 * m) + 1), u (shift2 a b d q) * kp (gl d) := by
    intro q
    rw [kOp_apply]
    simp_rw [tk_gpair_eq_sum hab, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [PiLp.inner_apply]
  simp_rw [RCLike.inner_apply, h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold corrPair
  simp_rw [Finset.mul_sum]
  exact sum_congr rfl fun d _ => sum_congr rfl fun q _ => by ring

/-- A grid single-register term against a state. -/
lemma inner_kOp_gsing (kn : Lat3 → ℂ) (a : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)) :
    inner ℂ u (kOp (tk (Spec1 a) (gTau a) kn) u) =
      ∑ d : GMode (2 * (2 * m) + 1), kn (gl d) * corrOne a d u := by
  classical
  have h1 : ∀ q, (kOp (tk (Spec1 a) (gTau a) kn) u) q =
      ∑ d : GMode (2 * (2 * m) + 1), u (shift1 a d q) * kn (gl d) := by
    intro q
    rw [kOp_apply]
    simp_rw [tk_gsing_eq_sum, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [PiLp.inner_apply]
  simp_rw [RCLike.inner_apply, h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold corrOne
  simp_rw [Finset.mul_sum]
  exact sum_congr rfl fun d _ => sum_congr rfl fun q _ => by ring

lemma inner_genTerm (kp : Lat3 → ℂ) (kn : ν → Lat3 → ℂ) (t : Term eta ν)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    inner ℂ u (kOp (genTerm eta m kp kn t) u) =
      ∑ d : GMode (2 * (2 * m) + 1), termCoef kp kn t (gl d) * termCorr t d u := by
  cases t with
  | inl pr => exact inner_kOp_gpair kp (ne_of_lt pr.2) u
  | inr il => exact inner_kOp_gsing (kn il.2) il.1 u

/-- **The potential against a state, as correlations.** -/
lemma inner_vGen (P : RegParticles eta) (kp : Lat3 → ℂ) (kn : ν → Lat3 → ℂ)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    inner ℂ u (kOp (vGen eta m P kp kn) u) =
      ∑ t, (P.tcoef t : ℂ) *
        ∑ d : GMode (2 * (2 * m) + 1), termCoef kp kn t (gl d) * termCorr t d u := by
  rw [kOp_vGen_eq, inner_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [inner_smul_right, inner_genTerm]

end TermCorrelations

/-! ## Shell sums -/

section ShellSums

/-- The real-valued version of the core's `sum_box_eq_sum_modes`. -/
lemma sum_box_eq_sum_modes_real {M : ℕ} (f : Lat3 → ℝ) :
    ∑ nu ∈ PlaneWaveGrid.box M, f nu = ∑ d : GMode (2 * M + 1), f (gl d) := by
  classical
  have himg : (Finset.univ.image (gl : GMode (2 * M + 1) → Lat3)) = PlaneWaveGrid.box M := by
    ext nu
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_box]
    constructor
    · rintro ⟨d, rfl⟩; exact gl_inBox d
    · intro h; exact ⟨ofLat nu, gl_ofLat h⟩
  rw [← himg, Finset.sum_image (fun x _ y _ h => gl_injective h)]

/-- Shell decomposition of a box sum with a bound on each shell. -/
lemma sum_box_le_shells (G : Lat3 → ℝ) (hG0 : G 0 = 0) (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hG : ∀ k x, ¬ InBox k x → G x ≤ c k) :
    ∀ J : ℕ, ∑ x ∈ PlaneWaveGrid.box J, G x ≤ ∑ k ∈ range J, 26 * ((k : ℝ) + 1) ^ 2 * c k := by
  intro J
  induction J with
  | zero =>
    have hb : PlaneWaveGrid.box 0 = {0} := by
      ext nu
      simp [mem_box, inBox_zero_iff]
    rw [hb, Finset.sum_singleton, hG0]
    simp
  | succ J ih =>
    rw [sum_box_succ, Finset.sum_range_succ]
    exact add_le_add ih (sum_shell_le G J (hc J) (hG J))

/-- Pairing the shells `2T` and `2T+1`. -/
lemma sum_shells_pair (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    ∀ m : ℕ, ∑ k ∈ range (2 * m), 26 * ((k : ℝ) + 1) ^ 2 * c (k / 2) ≤
      ∑ T ∈ range m, 208 * ((T : ℝ) + 1) ^ 2 * c T := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have h1 : (2 * m) / 2 = m := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h1, h2]
    have hcm := hc m
    have e : 26 * (((2 * m : ℕ) : ℝ) + 1) ^ 2 * c m + 26 * (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2 * c m ≤
        208 * ((m : ℝ) + 1) ^ 2 * c m := by
      push_cast
      nlinarith [mul_nonneg hcm (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
    linarith

/-- A function on the nonzero cyclic transfers bounded by `c T` beyond the box of radius `2T`
sums to at most `Σ_{T < m} 208 (T+1)² c T`. -/
lemma sum_modes_le_shells {m : ℕ} (F : GMode (2 * (2 * m) + 1) → ℝ) (hF0 : F 0 = 0)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hF : ∀ T d, ¬ InBox (2 * T) (gl d) → F d ≤ c T) :
    ∑ d, F d ≤ ∑ T ∈ range m, 208 * ((T : ℝ) + 1) ^ 2 * c T := by
  classical
  set G : Lat3 → ℝ := fun x => if InBox (2 * m) x then F (ofLat x) else 0 with hGdef
  have hsum : ∑ d, F d = ∑ x ∈ PlaneWaveGrid.box (2 * m), G x := by
    rw [sum_box_eq_sum_modes_real]
    refine sum_congr rfl fun d _ => ?_
    rw [hGdef]
    simp only [if_pos (gl_inBox d), ofLat_gl]
  have hG0 : G 0 = 0 := by
    rw [hGdef]
    simp only
    split_ifs
    · have : (ofLat (M := 2 * m) (0 : Lat3)) = 0 := by
        funext c; simp [ofLat]
      rw [this, hF0]
    · rfl
  have hG : ∀ k x, ¬ InBox k x → G x ≤ c (k / 2) := by
    intro k x hx
    rw [hGdef]
    simp only
    split_ifs with hxm
    · apply hF
      rw [gl_ofLat hxm]
      exact fun h => hx (h.mono (by omega))
    · exact hc _
  rw [hsum]
  exact (sum_box_le_shells G hG0 (fun k => c (k / 2)) (fun k => hc _) hG (2 * m)).trans
    (sum_shells_pair c hc m)

/-- `Σ_{T=1}^{n} 1/√T ≤ 2 √n` (the term `T = 0` is zero). -/
lemma sum_inv_sqrt_le : ∀ n : ℕ, ∑ T ∈ range (n + 1), 1 / Real.sqrt T ≤ 2 * Real.sqrt n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have ha := Real.sqrt_nonneg (n : ℝ)
    have hb : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have ha2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
    have hb2 : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have key : 2 * Real.sqrt (n : ℝ) + 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      rw [← sub_nonneg]
      have e : 2 * Real.sqrt ((n + 1 : ℕ) : ℝ) -
          (2 * Real.sqrt (n : ℝ) + 1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) =
          (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) ^ 2 / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
        field_simp
        nlinarith [ha2, hb2]
      rw [e]
      positivity
    linarith

/-- The shell sum with the bootstrapped tails. -/
lemma shell_tail_arith (m T0 : ℕ) (hT0 : 2 ≤ T0) {B : ℝ} (hB : 0 ≤ B) :
    ∑ T ∈ range m, 208 * ((T : ℝ) + 1) ^ 2 *
        (if T < T0 then 1 else 2 * B / ((T : ℝ) ^ 2 * Real.sqrt T)) ≤
      208 * (T0 : ℝ) ^ 3 + 1872 * B * Real.sqrt m := by
  have hsplit : ∀ T ∈ range m, 208 * ((T : ℝ) + 1) ^ 2 *
      (if T < T0 then 1 else 2 * B / ((T : ℝ) ^ 2 * Real.sqrt T)) ≤
      (if T < T0 then 208 * (T0 : ℝ) ^ 2 else 0) + 936 * B * (1 / Real.sqrt T) := by
    intro T _
    have hB' : 0 ≤ 936 * B * (1 / Real.sqrt T) := by positivity
    split_ifs with hT
    · have h1 : ((T : ℝ) + 1) ^ 2 ≤ (T0 : ℝ) ^ 2 := by
        have : (T : ℝ) + 1 ≤ T0 := by exact_mod_cast hT
        exact pow_le_pow_left₀ (by positivity) this 2
      nlinarith
    · push Not at hT
      have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT0.trans hT
      have hT0' : (0 : ℝ) < T := by linarith
      have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0'
      have hsq : (T : ℝ) + 1 ≤ 3 / 2 * T := by linarith
      have hsq2 : ((T : ℝ) + 1) ^ 2 ≤ 9 / 4 * (T : ℝ) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hsq 2
        nlinarith
      rw [zero_add]
      have e : 208 * ((T : ℝ) + 1) ^ 2 * (2 * B / ((T : ℝ) ^ 2 * Real.sqrt T)) =
          416 * B * (((T : ℝ) + 1) ^ 2 / (T : ℝ) ^ 2) * (1 / Real.sqrt T) := by
        field_simp
        ring
      rw [e]
      have h3 : ((T : ℝ) + 1) ^ 2 / (T : ℝ) ^ 2 ≤ 9 / 4 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have h4 : 0 ≤ 1 / Real.sqrt T := by positivity
      calc 416 * B * (((T : ℝ) + 1) ^ 2 / (T : ℝ) ^ 2) * (1 / Real.sqrt T)
          ≤ 416 * B * (9 / 4) * (1 / Real.sqrt T) := by gcongr
        _ = 936 * B * (1 / Real.sqrt T) := by ring
  refine (sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib]
  have hA : ∑ T ∈ range m, (if T < T0 then 208 * (T0 : ℝ) ^ 2 else 0) ≤ 208 * (T0 : ℝ) ^ 3 := by
    rw [← Finset.sum_filter]
    have hsub : (range m).filter (fun T => T < T0) ⊆ range T0 := by
      intro T hT
      simp only [Finset.mem_filter, Finset.mem_range] at hT ⊢
      exact hT.2
    calc ∑ T ∈ (range m).filter (fun T => T < T0), 208 * (T0 : ℝ) ^ 2
        ≤ ∑ T ∈ range T0, 208 * (T0 : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 208 * (T0 : ℝ) ^ 3 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hC : ∑ T ∈ range m, 936 * B * (1 / Real.sqrt T) ≤ 1872 * B * Real.sqrt m := by
    rw [← Finset.mul_sum]
    have h1 : ∑ T ∈ range m, 1 / Real.sqrt T ≤ ∑ T ∈ range (m + 1), 1 / Real.sqrt T :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ m))
        (fun _ _ _ => by positivity)
    have h2 := sum_inv_sqrt_le m
    have h3 : 0 ≤ 936 * B := by positivity
    calc 936 * B * ∑ T ∈ range m, 1 / Real.sqrt T ≤ 936 * B * (2 * Real.sqrt m) := by
          gcongr; exact h1.trans h2
      _ = 1872 * B * Real.sqrt m := by ring
  linarith

end ShellSums

/-! ## The alias form -/

section AliasForm

variable {ν : Type*} [Fintype ν] {eta m : ℕ}

/-- The correlations of a term, summed over the nonzero transfers, under bootstrapped tails. -/
lemma sum_corr_le_tails (t : Term eta ν) (u : EuclideanSpace ℂ (RCfg eta m)) (hu : ‖u‖ = 1)
    {T0 : ℕ} (hT0 : 2 ≤ T0) {B : ℝ} (hB : 0 ≤ B)
    (htail : ∀ T : ℕ, T0 ≤ T → T ≤ m → ∀ r,
      ‖maskOp (High T r) u‖ ≤ B / ((T : ℝ) ^ 2 * Real.sqrt T)) :
    ∑ d, (if d = 0 then 0 else ‖termCorr t d u‖) ≤
      208 * (T0 : ℝ) ^ 3 + 1872 * B * Real.sqrt m := by
  classical
  refine (sum_modes_le_shells (fun d => if d = 0 then 0 else ‖termCorr t d u‖) (by simp)
    (fun T => if T < T0 then 1 else 2 * B / ((T : ℝ) ^ 2 * Real.sqrt T))
    (fun k => by split_ifs <;> positivity) ?_).trans (shell_tail_arith m T0 hT0 hB)
  intro T d hd
  show (if d = 0 then 0 else ‖termCorr t d u‖) ≤
    (if T < T0 then 1 else 2 * B / ((T : ℝ) ^ 2 * Real.sqrt T))
  by_cases h0 : d = 0
  · rw [if_pos h0]
    split_ifs <;> positivity
  rw [if_neg h0]
  by_cases hT : T < T0
  · rw [if_pos hT]
    have := norm_corr_le_one t d u
    rw [hu, mul_one] at this
    exact this
  · rw [if_neg hT]
    push Not at hT
    have hTm : T ≤ m := by
      by_contra hcon
      push Not at hcon
      apply hd
      exact (gl_inBox d).mono (by omega)
    have h1 := norm_corr_le_tail t hd u
    rw [hu, mul_one] at h1
    have h2 := htail T hT hTm (termReg t)
    calc ‖termCorr t d u‖ ≤ 2 * ‖maskOp (High T (termReg t)) u‖ := h1
      _ ≤ 2 * (B / ((T : ℝ) ^ 2 * Real.sqrt T)) := by gcongr
      _ = 2 * B / ((T : ℝ) ^ 2 * Real.sqrt T) := by ring

lemma sum_ite_zero_eq_corrSum (t : Term eta ν) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ∑ d, (if d = 0 then 0 else ‖termCorr t d u‖) = corrSum t u := by
  classical
  unfold corrSum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : GMode (2 * (2 * m) + 1))), if_pos rfl,
    zero_add]
  refine sum_congr rfl fun d hd => ?_
  rw [if_neg (Finset.ne_of_mem_erase hd)]

/-- The coefficients of the alias potential. -/
lemma norm_termCoef_alias_le (D : NucData ν) {gamma : ℝ} (hg : 0 ≤ gamma) (t : Term eta ν)
    (x : Lat3) :
    ‖termCoef (aliasK m (kee gamma)) (fun l => aliasK m (knuc D gamma l)) t x‖ ≤
      coupling eta D gamma t * (8 / (2 * (m : ℝ) + 1) ^ 2) := by
  cases t with
  | inl pr =>
    have h := norm_aliasK_le (m := m) (kee_bound hg) hg x
    simp only [termCoef, coupling]
    calc ‖aliasK m (kee gamma) x‖ ≤ 8 * gamma / (2 * (m : ℝ) + 1) ^ 2 := h
      _ = gamma * (8 / (2 * (m : ℝ) + 1) ^ 2) := by ring
  | inr il =>
    have h := norm_aliasK_le (m := m) (knuc_bound D hg il.2)
      (mul_nonneg (D.charge_nonneg il.2) hg) x
    simp only [termCoef, coupling]
    calc ‖aliasK m (knuc D gamma il.2) x‖ ≤ 8 * (D.charge il.2 * gamma) / (2 * (m : ℝ) + 1) ^ 2 := h
      _ = D.charge il.2 * gamma * (8 / (2 * (m : ℝ) + 1) ^ 2) := by ring

lemma termCoef_alias_zero (D : NucData ν) (gamma : ℝ) (t : Term eta ν) :
    termCoef (aliasK m (kee gamma)) (fun l => aliasK m (knuc D gamma l)) t 0 = 0 := by
  cases t with
  | inl pr => exact aliasK_zero _
  | inr il => exact aliasK_zero _

lemma gl_zero' {M : ℕ} : gl (0 : GMode (2 * M + 1)) = 0 := by
  funext c
  simp [gl]

/-- The alias form in terms of the summed correlations of each term. -/
lemma norm_inner_vAlias_le (P : RegParticles eta) (D : NucData ν) {gamma : ℝ}
    (hg : 0 ≤ gamma) (u : EuclideanSpace ℂ (RCfg eta m)) {S : ℝ}
    (hS : ∀ t : Term eta ν, ∑ d, (if d = 0 then 0 else ‖termCorr t d u‖) ≤ S) :
    ‖inner ℂ u (kOp (vAlias eta m P D gamma) u)‖ ≤
      Zc P D gamma * (8 * S / (2 * (m : ℝ) + 1) ^ 2) := by
  classical
  have hm : (0 : ℝ) < (2 * (m : ℝ) + 1) ^ 2 := by positivity
  rw [vAlias, inner_vGen]
  refine (norm_sum_le _ _).trans ?_
  unfold Zc
  rw [Finset.sum_mul]
  refine sum_le_sum fun t _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc := coupling_nonneg (D := D) hg t
  have hk : 0 ≤ coupling eta D gamma t * (8 / (2 * (m : ℝ) + 1) ^ 2) := by positivity
  have hterm : ‖∑ d : GMode (2 * (2 * m) + 1),
      termCoef (aliasK m (kee gamma)) (fun l => aliasK m (knuc D gamma l)) t (gl d) *
        termCorr t d u‖ ≤ coupling eta D gamma t * (8 / (2 * (m : ℝ) + 1) ^ 2) * S := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ d : GMode (2 * (2 * m) + 1),
          ‖termCoef (aliasK m (kee gamma)) (fun l => aliasK m (knuc D gamma l)) t (gl d) *
            termCorr t d u‖
        ≤ ∑ d : GMode (2 * (2 * m) + 1), coupling eta D gamma t *
            (8 / (2 * (m : ℝ) + 1) ^ 2) * (if d = 0 then 0 else ‖termCorr t d u‖) := by
          refine sum_le_sum fun d _ => ?_
          rw [norm_mul]
          split_ifs with hd
          · subst hd
            rw [gl_zero', termCoef_alias_zero, norm_zero, zero_mul, mul_zero]
          · exact mul_le_mul_of_nonneg_right (norm_termCoef_alias_le D hg t _) (norm_nonneg _)
      _ = coupling eta D gamma t * (8 / (2 * (m : ℝ) + 1) ^ 2) *
            ∑ d : GMode (2 * (2 * m) + 1), (if d = 0 then 0 else ‖termCorr t d u‖) := by
          rw [Finset.mul_sum]
      _ ≤ coupling eta D gamma t * (8 / (2 * (m : ℝ) + 1) ^ 2) * S :=
          mul_le_mul_of_nonneg_left (hS t) hk
  calc |P.tcoef t| * ‖∑ d : GMode (2 * (2 * m) + 1),
        termCoef (aliasK m (kee gamma)) (fun l => aliasK m (knuc D gamma l)) t (gl d) *
          termCorr t d u‖
      ≤ |P.tcoef t| * (coupling eta D gamma t * (8 / (2 * (m : ℝ) + 1) ^ 2) * S) :=
        mul_le_mul_of_nonneg_left hterm (abs_nonneg _)
    _ = |P.tcoef t| * coupling eta D gamma t * (8 * S / (2 * (m : ℝ) + 1) ^ 2) := by ring

/-- **Alias form under bootstrapped tails** (`O(K^{-3/2})`): for a normalised state whose tails
beyond every threshold `T₀ ≤ T ≤ m` are at most `B/(T² √T)`,
`|⟨u, V_alias u⟩| ≤ Z_c · 8 (208 T₀³ + 1872 B √m)/(2m+1)²`. -/
theorem norm_inner_vAlias_le_tails (P : RegParticles eta) (D : NucData ν) {gamma : ℝ}
    (hg : 0 ≤ gamma) (u : EuclideanSpace ℂ (RCfg eta m)) (hu : ‖u‖ = 1) {T0 : ℕ}
    (hT0 : 2 ≤ T0) {B : ℝ} (hB : 0 ≤ B)
    (htail : ∀ T : ℕ, T0 ≤ T → T ≤ m → ∀ r,
      ‖maskOp (High T r) u‖ ≤ B / ((T : ℝ) ^ 2 * Real.sqrt T)) :
    ‖inner ℂ u (kOp (vAlias eta m P D gamma) u)‖ ≤
      Zc P D gamma * (8 * (208 * (T0 : ℝ) ^ 3 + 1872 * B * Real.sqrt m) /
        (2 * (m : ℝ) + 1) ^ 2) :=
  norm_inner_vAlias_le P D hg u (fun t => sum_corr_le_tails t u hu hT0 hB htail)

/-- **Alias form under correlation summability** (`O(K^{-2})`): if
`Σ_{d ≠ 0} |⟨u, S_t(d) u⟩| ≤ C_ρ` for every term, then
`|⟨u, V_alias u⟩| ≤ Z_c · 8 C_ρ/(2m+1)²`. -/
theorem norm_inner_vAlias_le_summable (P : RegParticles eta) (D : NucData ν) {gamma : ℝ}
    (hg : 0 ≤ gamma) (u : EuclideanSpace ℂ (RCfg eta m)) {Crho : ℝ}
    (hsum : ∀ t : Term eta ν, corrSum t u ≤ Crho) :
    ‖inner ℂ u (kOp (vAlias eta m P D gamma) u)‖ ≤
      Zc P D gamma * (8 * Crho / (2 * (m : ℝ) + 1) ^ 2) :=
  norm_inner_vAlias_le P D hg u (fun t => (sum_ite_zero_eq_corrSum t u).le.trans (hsum t))

end AliasForm

end

end PlaneWaveFullKernel

end DevFK3
-- END SOURCE dev/DevFK3.lean

-- BEGIN SOURCE dev/DevFK4.lean
-- SHA256 b41f56ecbaeceaf8c7b1b574985e00138145c816aef91d75a7e66524876f0eb3
section DevFK4

/-!
# Full-kernel collocation: the finite energy comparison with the Galerkin method

`H_full = P H P + R_full` with `R_full = Δ + V_alias` (`HfullMom_eq_gal`), so min–max in
both directions (`ritz_compare`) bounds `|E_full - E_gal|` by the larger of the forms of
`R_full` at the two ground states.  For each ground state:

* the elliptic estimate (`galRegHam`, `fullRegHam`: the full kernel has coefficients at most
  `25 γ/|ν|²`, so the Kato–Rellich and elliptic estimates hold with the coupling `25 m̄ Z_c`)
  bounds `‖wTot u‖`;
* the tail bootstrap holds at *every* threshold `T₀ ≤ T ≤ 2m` (`boot_tail` with the tail bounds
  `vGalK_tail` and `vFull_tail`), with `t_r(T; u) ≤ C_boot ‖wTot u‖/(T² √T)`;
* `Δ` is bounded by the core's form estimate at the threshold `s = m` (`Delta_form`,
  `form_arith`; the truncated kernel agrees with the Coulomb coefficients on the whole zone
  `‖ν‖∞ ≤ 2m`), `O(K^{-3})`;
* `V_alias` by the support identity and the shell sum (`norm_inner_vAlias_le_tails`),
  `O(K^{-3/2})`, or by the correlation summability (`norm_inner_vAlias_le_summable`),
  `O(C_ρ K^{-2})`.

The energy of the full-kernel ground state is bounded below by its elliptic lower bound and
above by `E_gal + |⟨u_gal, R_full u_gal⟩|`, which fixes its bootstrap threshold.  The result
(`full_galerkin_energy`):

  `|E_full - E_gal| ≤ C/(m √m)`,  and under summability `|E_full - E_gal| ≤ (C₁ + C₂ C_ρ)/m²`,

with explicit constants (`fkConst`, `fkConstImp`) depending only on `m̄`, `Z_c`, `g` and the
Galerkin energy budget.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace PlaneWaveFullKernel

open PlaneWaveGrid

noncomputable section

/-! ## Ground states and thresholds -/

section Ground

variable {eta n : ℕ} [NeZero n]

/-- A normalised ground state of `H` in the exchange sector `(sgn, lab)`: a normalised sector
eigenvector whose eigenvalue is the sector Ritz energy. -/
def IsSecGroundState (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ)
    (H : EuclideanSpace ℂ (GConfig eta n) →ₗ[ℂ] EuclideanSpace ℂ (GConfig eta n))
    (u : EuclideanSpace ℂ (GConfig eta n)) : Prop :=
  IsSec sgn lab u ∧ ‖u‖ = 1 ∧ ∃ E : ℝ, IsSecRitz sgn lab H E ∧ H u = (E : ℂ) • u

end Ground

section Constants

/-- The bootstrap threshold for energies at most `e`: `max 2 ⌈2 √(m̄ e)/g⌉`. -/
def bootThr (Mb g e : ℝ) : ℕ := max 2 (Nat.ceil (2 * Real.sqrt (Mb * e) / g))

lemma two_le_bootThr (Mb g e : ℝ) : 2 ≤ bootThr Mb g e := le_max_left _ _

lemma bootThr_spec {Mb g e : ℝ} (hM : 0 < Mb) (hg : 0 < g) (he : 0 ≤ e) {T : ℕ}
    (hT : bootThr Mb g e ≤ T) : e ≤ g ^ 2 / (4 * Mb) * ((T : ℝ) + 1) ^ 2 := by
  have h1 : 2 * Real.sqrt (Mb * e) / g ≤ T :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hT)
  rw [div_le_iff₀ hg] at h1
  have h2 : (2 * Real.sqrt (Mb * e)) ^ 2 ≤ ((T : ℝ) * g) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  rw [mul_pow, Real.sq_sqrt (by positivity)] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  nlinarith [sq_nonneg g]

lemma bootThr_mono {Mb g e e' : ℝ} (hM : 0 ≤ Mb) (hg : 0 < g) (hee : e ≤ e') :
    bootThr Mb g e ≤ bootThr Mb g e' := by
  unfold bootThr
  apply max_le_max le_rfl
  apply Nat.ceil_mono
  gcongr

variable (Mb Zc0 g Eb : ℝ)

/-- Coupling of the Galerkin register Hamiltonian, `m̄ Z_c`. -/
def fkZ : ℝ := Mb * Zc0

/-- Coupling of the full-kernel register Hamiltonian, `m̄ · 25 Z_c`. -/
def fkZf : ℝ := Mb * (25 * Zc0)

/-- Bound on `‖wTot u_gal‖`. -/
def fkXg : ℝ := Mb * Ell (fkZ Mb Zc0) g Eb

/-- Bootstrap threshold of the Galerkin ground state. -/
def fkT0g : ℕ := bootThr Mb g Eb

/-- Tail constant of the Galerkin ground state. -/
def fkBg : ℝ := Cboot (fkZ Mb Zc0) g * fkXg Mb Zc0 g Eb

/-- Shell constant of the Galerkin ground state. -/
def fkSg : ℝ := 208 * (fkT0g Mb g Eb : ℝ) ^ 3 + 1872 * fkBg Mb Zc0 g Eb

/-- Energy budget of the full-kernel ground state. -/
def fkEbf : ℝ := max (52 * fkZf Mb Zc0 * J0g (fkZf Mb Zc0) g + g ^ 2 / 4)
  (Eb + Cform (fkZ Mb Zc0) g * fkXg Mb Zc0 g Eb ^ 2 + 8 * Zc0 * fkSg Mb Zc0 g Eb)

/-- Bound on `‖wTot u_full‖`. -/
def fkXf : ℝ := Mb * Ell (fkZf Mb Zc0) g (fkEbf Mb Zc0 g Eb)

/-- Bootstrap threshold of the full-kernel ground state. -/
def fkT0f : ℕ := bootThr Mb g (fkEbf Mb Zc0 g Eb)

/-- Tail constant of the full-kernel ground state. -/
def fkBf : ℝ := Cboot (fkZf Mb Zc0) g * fkXf Mb Zc0 g Eb

/-- Shell constant of the full-kernel ground state. -/
def fkSf : ℝ := 208 * (fkT0f Mb Zc0 g Eb : ℝ) ^ 3 + 1872 * fkBf Mb Zc0 g Eb

/-- The form constant of `Δ` at both ground states. -/
def fkForm : ℝ :=
  Cform (fkZ Mb Zc0) g * fkXg Mb Zc0 g Eb ^ 2 + Cform (fkZf Mb Zc0) g * fkXf Mb Zc0 g Eb ^ 2

/-- The comparison constant: `|E_full - E_gal| ≤ fkConst/(m √m)`. -/
def fkConst : ℝ := fkForm Mb Zc0 g Eb + 2 * Zc0 * (fkSg Mb Zc0 g Eb + fkSf Mb Zc0 g Eb)

/-- The comparison constant under correlation summability:
`|E_full - E_gal| ≤ fkConstImp C_ρ/m²`. -/
def fkConstImp (Crho : ℝ) : ℝ := fkForm Mb Zc0 g Eb + 4 * Zc0 * Crho

variable {Mb Zc0 g Eb}

lemma fkZ_nonneg (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) : 0 ≤ fkZ Mb Zc0 := mul_nonneg hM hZ

lemma fkZf_nonneg (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) : 0 ≤ fkZf Mb Zc0 := by
  unfold fkZf; positivity

lemma fkXg_nonneg (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) (hEb : 0 ≤ Eb) : 0 ≤ fkXg Mb Zc0 g Eb :=
  mul_nonneg hM (Ell_nonneg (fkZ_nonneg hM hZ) hEb)

lemma fkBg_nonneg (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) (hEb : 0 ≤ Eb) : 0 ≤ fkBg Mb Zc0 g Eb :=
  mul_nonneg (Cboot_nonneg (fkZ_nonneg hM hZ)) (fkXg_nonneg hM hZ hEb)

lemma fkSg_nonneg (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) (hEb : 0 ≤ Eb) : 0 ≤ fkSg Mb Zc0 g Eb := by
  unfold fkSg
  have := fkBg_nonneg (g := g) hM hZ hEb
  positivity

lemma fkEbf_ge (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) (hEb : 0 ≤ Eb) : Eb ≤ fkEbf Mb Zc0 g Eb := by
  refine le_trans ?_ (le_max_right _ _)
  have h1 := Cform_nonneg (g := g) (fkZ_nonneg hM hZ)
  have h2 := fkSg_nonneg (g := g) hM hZ hEb
  have h3 : 0 ≤ Cform (fkZ Mb Zc0) g * fkXg Mb Zc0 g Eb ^ 2 := by positivity
  have h4 : 0 ≤ 8 * Zc0 * fkSg Mb Zc0 g Eb := by positivity
  linarith

lemma fkEbf_nonneg (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) (hEb : 0 ≤ Eb) : 0 ≤ fkEbf Mb Zc0 g Eb :=
  hEb.trans (fkEbf_ge hM hZ hEb)

lemma fkXf_nonneg (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) (hEb : 0 ≤ Eb) : 0 ≤ fkXf Mb Zc0 g Eb :=
  mul_nonneg hM (Ell_nonneg (fkZf_nonneg hM hZ) (fkEbf_nonneg hM hZ hEb))

lemma fkBf_nonneg (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) (hEb : 0 ≤ Eb) : 0 ≤ fkBf Mb Zc0 g Eb :=
  mul_nonneg (Cboot_nonneg (fkZf_nonneg hM hZ)) (fkXf_nonneg hM hZ hEb)

lemma fkSf_nonneg (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) (hEb : 0 ≤ Eb) : 0 ≤ fkSf Mb Zc0 g Eb := by
  unfold fkSf
  have := fkBf_nonneg (g := g) hM hZ hEb
  positivity

lemma fkForm_nonneg (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) : 0 ≤ fkForm Mb Zc0 g Eb := by
  unfold fkForm
  have h1 := Cform_nonneg (g := g) (fkZ_nonneg hM hZ)
  have h2 := Cform_nonneg (g := g) (fkZf_nonneg hM hZ)
  positivity

lemma fkConst_nonneg (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) (hEb : 0 ≤ Eb) :
    0 ≤ fkConst Mb Zc0 g Eb := by
  unfold fkConst
  have h1 := fkForm_nonneg (g := g) (Eb := Eb) hM hZ
  have h2 := fkSg_nonneg (g := g) hM hZ hEb
  have h3 := fkSf_nonneg (g := g) hM hZ hEb
  positivity

lemma fkT0g_le_fkT0f (hM : 0 ≤ Mb) (hZ : 0 ≤ Zc0) (hg : 0 < g) (hEb : 0 ≤ Eb) :
    fkT0g Mb g Eb ≤ fkT0f Mb Zc0 g Eb :=
  bootThr_mono hM hg (fkEbf_ge hM hZ hEb)

end Constants

/-! ## The form of `R_full` at a ground state -/

section Form

variable {ν : Type*} [Fintype ν] {eta : ℕ}

/-- The truncated kernel agrees with the Coulomb coefficients on the whole register zone, so it
is a grid kernel at the tail threshold `m`. -/
lemma sharpKernel_gridKernel {gamma : ℝ} (hgamma : 0 ≤ gamma) (m : ℕ) :
    GridKernel gamma m (sharpKernel gamma m) :=
  ⟨(sharpKernel_isGridKernel hgamma m).even, (sharpKernel_isGridKernel hgamma m).bound,
    fun x hx => by rw [sharpKernel, if_pos hx]⟩

/-- The form of `R_full = Δ + V_alias` at a state with tails bootstrapped at `m`: the `Δ`-part by
the core's form estimate at the tail threshold `s = m`, plus any bound `A` on the alias
part. -/
lemma norm_inner_Rfull_le (P : RegParticles eta) (D : NucData ν) {gamma g : ℝ}
    (hgamma : 0 ≤ gamma) {m : ℕ} (hm : 1 ≤ m) (u : EuclideanSpace ℂ (RCfg eta m))
    {Zu X : ℝ} (hZu : Zc P D gamma ≤ Zu) (hX : ‖wMul wTot u‖ ≤ X)
    (hs : ∀ r, ‖maskOp (High m r) u‖ ≤ Cboot Zu g * X / ((m : ℝ) ^ 2 * Real.sqrt m))
    {A : ℝ} (hA : ‖inner ℂ u (kOp (vAlias eta m P D gamma) u)‖ ≤ A) :
    ‖inner ℂ u (Delta eta m P D gamma (sharpKernel gamma m) u +
        kOp (vAlias eta m P D gamma) u)‖ ≤ Cform Zu g * X ^ 2 / (m : ℝ) ^ 3 + A := by
  have hms : m ≤ 8 * m := by omega
  have hκ : GridKernel gamma m (sharpKernel gamma m) := sharpKernel_gridKernel hgamma m
  have hZ0 : 0 ≤ Zc P D gamma := Zc_nonneg hgamma
  have hZu0 : 0 ≤ Zu := hZ0.trans hZu
  have hX0 : 0 ≤ X := (norm_nonneg _).trans hX
  set τ : ℝ := Cboot Zu g * X / ((m : ℝ) ^ 2 * Real.sqrt m) with hτdef
  have hτ0 : 0 ≤ τ := by
    have := Cboot_nonneg (g := g) hZu0
    positivity
  have hD := Delta_form (P := P) (D := D) hgamma hm le_rfl hκ u u hτ0 hτ0 hs hs
  have hA0 := formA_nonneg m m
  have hD2 : Zc P D gamma * (formA m m * (τ * ‖wMul wTot u‖ + τ * ‖wMul wTot u‖) +
      52 * m * (τ * τ)) ≤ Zu * (formA m m * (τ * X + τ * X) + 52 * m * (τ * τ)) := by
    have h1 : formA m m * (τ * ‖wMul wTot u‖ + τ * ‖wMul wTot u‖) + 52 * m * (τ * τ) ≤
        formA m m * (τ * X + τ * X) + 52 * m * (τ * τ) := by
      have : τ * ‖wMul wTot u‖ ≤ τ * X := mul_le_mul_of_nonneg_left hX hτ0
      gcongr
    have h2 : 0 ≤ formA m m * (τ * X + τ * X) + 52 * m * (τ * τ) := by positivity
    calc Zc P D gamma * (formA m m * (τ * ‖wMul wTot u‖ + τ * ‖wMul wTot u‖) +
          52 * m * (τ * τ)) ≤ Zc P D gamma * (formA m m * (τ * X + τ * X) + 52 * m * (τ * τ)) :=
          mul_le_mul_of_nonneg_left h1 hZ0
      _ ≤ Zu * (formA m m * (τ * X + τ * X) + 52 * m * (τ * τ)) :=
          mul_le_mul_of_nonneg_right hZu h2
  have hD3 := form_arith hZu0 hX0 hτ0 hm le_rfl hms le_rfl (g := g)
  rw [inner_add_right]
  exact (norm_add_le _ _).trans (add_le_add (hD.trans (hD2.trans hD3)) hA)

end Form

/-! ## Arithmetic -/

section Arith

lemma sqrt_le_self_nat {m : ℕ} (hm : 1 ≤ m) : Real.sqrt m ≤ m := by
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

lemma one_le_sqrt_nat {m : ℕ} (hm : 1 ≤ m) : 1 ≤ Real.sqrt m := by
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt h1

/-- `8 (a + b √m)/(2m+1)² ≤ 2 (a + b)/(m √m)`. -/
lemma alias_arith {m : ℕ} (hm : 1 ≤ m) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    8 * (a + b * Real.sqrt m) / (2 * (m : ℝ) + 1) ^ 2 ≤ 2 * (a + b) / ((m : ℝ) * Real.sqrt m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr1 := one_le_sqrt_nat hm
  have hrm := sqrt_le_self_nat hm
  have hr2 : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ a * (m : ℝ) * ((m : ℝ) - Real.sqrt m) :=
    mul_nonneg (mul_nonneg ha (by linarith)) (by linarith)
  nlinarith [mul_nonneg ha (by linarith : (0 : ℝ) ≤ m), mul_nonneg hb (by linarith : (0 : ℝ) ≤ m)]

/-- `8 (a + b √m)/(2m+1)² ≤ 8 (a + b)`. -/
lemma alias_arith0 {m : ℕ} (hm : 1 ≤ m) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    8 * (a + b * Real.sqrt m) / (2 * (m : ℝ) + 1) ^ 2 ≤ 8 * (a + b) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrm := sqrt_le_self_nat hm
  rw [div_le_iff₀ (by positivity)]
  have h2 : (1 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 := by nlinarith
  have h3 : Real.sqrt m ≤ (2 * (m : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h3 hb]

/-- `8 c/(2m+1)² ≤ 2 c/m²`. -/
lemma alias_arith2 {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 ≤ c) :
    8 * c / (2 * (m : ℝ) + 1) ^ 2 ≤ 2 * c / (m : ℝ) ^ 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hc (by linarith : (0 : ℝ) ≤ m)]

/-- `F/m³ ≤ F/(m √m)` for `m ≥ 1`. -/
lemma delta_arith {m : ℕ} (hm : 1 ≤ m) {F : ℝ} (hF : 0 ≤ F) :
    F / (m : ℝ) ^ 3 ≤ F / ((m : ℝ) * Real.sqrt m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrm := sqrt_le_self_nat hm
  have hr0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by positivity)
  apply div_le_div_of_nonneg_left hF (by positivity)
  have : Real.sqrt m ≤ (m : ℝ) ^ 2 := hrm.trans (by nlinarith)
  calc (m : ℝ) * Real.sqrt m ≤ (m : ℝ) * (m : ℝ) ^ 2 := by gcongr
    _ = (m : ℝ) ^ 3 := by ring

/-- `F/m³ ≤ F/m²` for `m ≥ 1`. -/
lemma delta_arith2 {m : ℕ} (hm : 1 ≤ m) {F : ℝ} (hF : 0 ≤ F) :
    F / (m : ℝ) ^ 3 ≤ F / (m : ℝ) ^ 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  apply div_le_div_of_nonneg_left hF (by positivity)
  nlinarith

/-- `F/m³ ≤ F` for `m ≥ 1`. -/
lemma delta_arith0 {m : ℕ} (hm : 1 ≤ m) {F : ℝ} (hF : 0 ≤ F) : F / (m : ℝ) ^ 3 ≤ F := by
  have hs : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact div_le_self hF (one_le_pow₀ hs)

end Arith

/-! ## The finite comparison -/

section Comparison

variable {ν : Type*} [Fintype ν] {eta : ℕ}

/-- **Finite full-kernel–Galerkin comparison.** For normalised sector ground states of the
register Galerkin Hamiltonian (`|E_gal| ≤ E_b`) and of the full-kernel Hamiltonian, on the
padded register of radius `2m` with `m` at or above the bootstrap threshold of the full-kernel
ground state,

  `|E_full - E_gal| ≤ fkConst/(m √m)`,

and, if the summed cyclic correlations `Σ_{d ≠ 0} |⟨u, S_t(d) u⟩|` of both ground states are at
most `C_ρ` for every term `t`, `|E_full - E_gal| ≤ fkConstImp C_ρ/m²`. -/
theorem full_galerkin_energy (P : RegParticles eta) (D : NucData ν) (sgn : Fin eta → ℂ)
    (lab : Fin eta → ℕ) {gamma g : ℝ} (hgamma : 0 ≤ gamma) (hg : 0 < g) {m : ℕ}
    {Eb : ℝ} (hsf : fkT0f P.maxMass (Zc P D gamma) g Eb ≤ m)
    {Eg : ℝ} (hEb : |Eg| ≤ Eb)
    (ug : EuclideanSpace ℂ (RCfg eta m)) (hug : IsSec sgn lab ug) (hng : ‖ug‖ = 1)
    (hEg : Hgal eta m P D gamma g ug = (Eg : ℂ) • ug)
    (hlowg : ∀ v, IsSec sgn lab v → Eg * ‖v‖ ^ 2 ≤ (inner ℂ v (Hgal eta m P D gamma g v)).re)
    {Ef : ℝ} (uf : EuclideanSpace ℂ (RCfg eta m)) (huf : IsSec sgn lab uf) (hnf : ‖uf‖ = 1)
    (hEf : HfullMom eta m P D gamma g uf = (Ef : ℂ) • uf)
    (hlowf : ∀ v, IsSec sgn lab v →
      Ef * ‖v‖ ^ 2 ≤ (inner ℂ v (HfullMom eta m P D gamma g v)).re) :
    |Ef - Eg| ≤ fkConst P.maxMass (Zc P D gamma) g Eb / ((m : ℝ) * Real.sqrt m) ∧
    ∀ Crho : ℝ, 0 ≤ Crho → (∀ t : Term eta ν, corrSum t ug ≤ Crho) →
      (∀ t : Term eta ν, corrSum t uf ≤ Crho) →
      |Ef - Eg| ≤ fkConstImp P.maxMass (Zc P D gamma) g Eb Crho / (m : ℝ) ^ 2 := by
  -- basic facts
  have hM1 : 1 ≤ P.maxMass := P.one_le_maxMass
  have hM0 : 0 < P.maxMass := P.maxMass_pos
  have hZ0 : 0 ≤ Zc P D gamma := Zc_nonneg hgamma
  have hEb0 : 0 ≤ Eb := (abs_nonneg _).trans hEb
  have hT0g2 : 2 ≤ fkT0g P.maxMass g Eb := two_le_bootThr _ _ _
  have hT0f2 : 2 ≤ fkT0f P.maxMass (Zc P D gamma) g Eb := two_le_bootThr _ _ _
  have hm1 : 1 ≤ m := by omega
  have hsg : fkT0g P.maxMass g Eb ≤ m :=
    (fkT0g_le_fkT0f hM0.le hZ0 hg hEb0).trans hsf
  have hZZ : Zc P D gamma ≤ fkZ P.maxMass (Zc P D gamma) := by
    unfold fkZ; nlinarith
  have hZZf : Zc P D gamma ≤ fkZf P.maxMass (Zc P D gamma) := by
    unfold fkZf; nlinarith
  have hZf : P.maxMass * Zc P D (25 * gamma) = fkZf P.maxMass (Zc P D gamma) := by
    rw [Zc_smul]; rfl
  -- Galerkin ground state: elliptic bound and tails at every threshold
  have hell_g := (galRegHam (P := P) (D := D) (m := m) hgamma hg).elliptic ug hng Eg hEg
  change ‖wMul (wM P) ug‖ ≤ Ell (fkZ P.maxMass (Zc P D gamma)) g |Eg| at hell_g
  have hXg : ‖wMul wTot ug‖ ≤ fkXg P.maxMass (Zc P D gamma) g Eb :=
    (norm_wMul_wTot_le P ug).trans (mul_le_mul_of_nonneg_left
      (hell_g.trans (Ell_mono (fkZ_nonneg hM0.le hZ0) hEb)) hM0.le)
  have htail_g : ∀ T : ℕ, fkT0g P.maxMass g Eb ≤ T → ∀ r,
      ‖maskOp (High T r) ug‖ ≤
        fkBg P.maxMass (Zc P D gamma) g Eb / ((T : ℝ) ^ 2 * Real.sqrt T) := by
    intro T hT r
    have hT2 : 2 ≤ T := hT0g2.trans hT
    have hEbT : |Eg| ≤ g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2 :=
      hEb.trans (bootThr_spec hM0 hg hEb0 hT)
    have h := boot_tail (P := P) (D := D) hgamma hg hT2 (kOp (vGalK eta m P D gamma))
      (fun r' u => vGalK_tail hgamma (T / 2) T (by omega) (Nat.div_le_self T 2) r' u)
      ug Eg hEg hEbT r
    refine h.trans ?_
    have hTpos : (0 : ℝ) < (T : ℝ) ^ 2 * Real.sqrt T := by
      have : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
      positivity
    have hCb : 0 ≤ Cboot (P.maxMass * Zc P D gamma) g :=
      Cboot_nonneg (mul_nonneg hM0.le hZ0)
    unfold fkBg
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hXg hCb) hTpos.le
  -- the alias form and the form of `R_full` at the Galerkin ground state
  have hAg := norm_inner_vAlias_le_tails P D hgamma ug hng hT0g2
    (fkBg_nonneg hM0.le hZ0 hEb0) (fun T hT _ r => htail_g T hT r)
  have hRg := norm_inner_Rfull_le P D hgamma hm1 ug hZZ hXg
    (fun r => htail_g m hsg r) hAg
  -- an `m`-independent bound
  have hRg0 : ‖inner ℂ ug (Delta eta m P D gamma (sharpKernel gamma m) ug +
      kOp (vAlias eta m P D gamma) ug)‖ ≤
      Cform (fkZ P.maxMass (Zc P D gamma)) g * fkXg P.maxMass (Zc P D gamma) g Eb ^ 2 +
        8 * Zc P D gamma * fkSg P.maxMass (Zc P D gamma) g Eb := by
    refine hRg.trans (add_le_add ?_ ?_)
    · exact delta_arith0 hm1 (mul_nonneg (Cform_nonneg (fkZ_nonneg hM0.le hZ0)) (sq_nonneg _))
    · have h := alias_arith0 hm1 (a := 208 * (fkT0g P.maxMass g Eb : ℝ) ^ 3)
        (b := 1872 * fkBg P.maxMass (Zc P D gamma) g Eb) (by positivity)
        (by have := fkBg_nonneg (g := g) hM0.le hZ0 hEb0; positivity)
      unfold fkSg
      calc Zc P D gamma * (8 * (208 * (fkT0g P.maxMass g Eb : ℝ) ^ 3 +
            1872 * fkBg P.maxMass (Zc P D gamma) g Eb * Real.sqrt m) / (2 * (m : ℝ) + 1) ^ 2)
          ≤ Zc P D gamma * (8 * (208 * (fkT0g P.maxMass g Eb : ℝ) ^ 3 +
            1872 * fkBg P.maxMass (Zc P D gamma) g Eb)) := by
            exact mul_le_mul_of_nonneg_left h hZ0
        _ = 8 * Zc P D gamma * (208 * (fkT0g P.maxMass g Eb : ℝ) ^ 3 +
            1872 * fkBg P.maxMass (Zc P D gamma) g Eb) := by ring
  -- the full-kernel ground energy is bounded above through the Galerkin ground state ...
  have hEf_up : Ef ≤ Eb + Cform (fkZ P.maxMass (Zc P D gamma)) g *
      fkXg P.maxMass (Zc P D gamma) g Eb ^ 2 +
        8 * Zc P D gamma * fkSg P.maxMass (Zc P D gamma) g Eb := by
    have h := hlowf ug hug
    rw [hng, one_pow, mul_one, HfullMom_eq_gal, inner_add_right, Complex.add_re,
      re_inner_eigen _ ug hng Eg hEg] at h
    have h2 := (Complex.re_le_norm _).trans hRg0
    have h3 := le_abs_self Eg
    linarith
  -- ... and below by its elliptic lower bound
  have hEf_low := (fullRegHam (m := m) P D hgamma hg).eigen_lower uf hnf Ef hEf
  change -(52 * (P.maxMass * Zc P D (25 * gamma)) * (J0g (P.maxMass * Zc P D (25 * gamma)) g : ℝ) +
    g ^ 2 / 4) ≤ Ef at hEf_low
  rw [hZf] at hEf_low
  have hEfb : |Ef| ≤ fkEbf P.maxMass (Zc P D gamma) g Eb := by
    rw [abs_le]
    unfold fkEbf
    constructor
    · have := le_max_left (52 * fkZf P.maxMass (Zc P D gamma) *
        (J0g (fkZf P.maxMass (Zc P D gamma)) g : ℝ) + g ^ 2 / 4)
        (Eb + Cform (fkZ P.maxMass (Zc P D gamma)) g * fkXg P.maxMass (Zc P D gamma) g Eb ^ 2 +
          8 * Zc P D gamma * fkSg P.maxMass (Zc P D gamma) g Eb)
      linarith
    · exact hEf_up.trans (le_max_right _ _)
  -- full-kernel ground state: elliptic bound and tails at every threshold up to `2m`
  have hell_f := (fullRegHam (m := m) P D hgamma hg).elliptic uf hnf Ef hEf
  change ‖wMul (wM P) uf‖ ≤ Ell (P.maxMass * Zc P D (25 * gamma)) g |Ef| at hell_f
  rw [hZf] at hell_f
  have hXf : ‖wMul wTot uf‖ ≤ fkXf P.maxMass (Zc P D gamma) g Eb :=
    (norm_wMul_wTot_le P uf).trans (mul_le_mul_of_nonneg_left
      (hell_f.trans (Ell_mono (fkZf_nonneg hM0.le hZ0) hEfb)) hM0.le)
  have htail_f : ∀ T : ℕ, fkT0f P.maxMass (Zc P D gamma) g Eb ≤ T → T ≤ 2 * m → ∀ r,
      ‖maskOp (High T r) uf‖ ≤
        fkBf P.maxMass (Zc P D gamma) g Eb / ((T : ℝ) ^ 2 * Real.sqrt T) := by
    intro T hT hTm r
    have hT2 : 2 ≤ T := hT0f2.trans hT
    have hEbT : |Ef| ≤ g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2 :=
      hEfb.trans (bootThr_spec hM0 hg (fkEbf_nonneg hM0.le hZ0 hEb0) hT)
    have h := boot_tail (P := P) (D := D) (gamma := 25 * gamma) (by positivity) hg hT2
      (kOp (vGen eta m P (foldK m (kee gamma)) (fun l => foldK m (knuc D gamma l))))
      (fun r' u => vFull_tail P D hgamma (T / 2) T (by omega) (Nat.div_le_self T 2) hTm r' u)
      uf Ef hEf hEbT r
    rw [hZf] at h
    refine h.trans ?_
    have hTpos : (0 : ℝ) < (T : ℝ) ^ 2 * Real.sqrt T := by
      have : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
      positivity
    have hCb : 0 ≤ Cboot (fkZf P.maxMass (Zc P D gamma)) g :=
      Cboot_nonneg (fkZf_nonneg hM0.le hZ0)
    unfold fkBf
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hXf hCb) hTpos.le
  -- the alias form and the form of `R_full` at the full-kernel ground state
  have hAf := norm_inner_vAlias_le_tails P D hgamma uf hnf hT0f2
    (fkBf_nonneg hM0.le hZ0 hEb0) (fun T hT hTm r => htail_f T hT (by omega) r)
  have hRf := norm_inner_Rfull_le P D hgamma hm1 uf hZZf hXf
    (fun r => htail_f m hsf (by omega) r) hAf
  -- min--max in both directions
  have hΔ : ∀ v, HfullMom eta m P D gamma g v = Hgal eta m P D gamma g v +
      (Delta eta m P D gamma (sharpKernel gamma m) + kOp (vAlias eta m P D gamma)) v := by
    intro v
    rw [HfullMom_eq_gal, LinearMap.add_apply]
  have hcmp : ∀ ε : ℝ,
      ‖inner ℂ uf (Delta eta m P D gamma (sharpKernel gamma m) uf +
        kOp (vAlias eta m P D gamma) uf)‖ ≤ ε →
      ‖inner ℂ ug (Delta eta m P D gamma (sharpKernel gamma m) ug +
        kOp (vAlias eta m P D gamma) ug)‖ ≤ ε → |Ef - Eg| ≤ ε := by
    intro ε h1 h2
    refine ritz_compare (HfullMom eta m P D gamma g) (Hgal eta m P D gamma g)
      (Delta eta m P D gamma (sharpKernel gamma m) + kOp (vAlias eta m P D gamma)) hΔ
      {v | IsSec sgn lab v} Ef Eg (fun v hv => hlowf v hv) (fun v hv => hlowg v hv)
      uf ug huf hug hnf hng (re_inner_eigen _ uf hnf Ef hEf) (re_inner_eigen _ ug hng Eg hEg)
      ?_ ?_
    · rw [LinearMap.add_apply]; exact h1
    · rw [LinearMap.add_apply]; exact h2
  -- nonnegative pieces
  have hFg : 0 ≤ Cform (fkZ P.maxMass (Zc P D gamma)) g * fkXg P.maxMass (Zc P D gamma) g Eb ^ 2 :=
    mul_nonneg (Cform_nonneg (fkZ_nonneg hM0.le hZ0)) (sq_nonneg _)
  have hFf : 0 ≤ Cform (fkZf P.maxMass (Zc P D gamma)) g * fkXf P.maxMass (Zc P D gamma) g Eb ^ 2 :=
    mul_nonneg (Cform_nonneg (fkZf_nonneg hM0.le hZ0)) (sq_nonneg _)
  have hBg := fkBg_nonneg (g := g) hM0.le hZ0 hEb0
  have hBf := fkBf_nonneg (g := g) hM0.le hZ0 hEb0
  refine ⟨?_, ?_⟩
  · -- the unconditional bound
    have hg1 := delta_arith hm1 hFg
    have hf1 := delta_arith hm1 hFf
    have hg2 := alias_arith hm1 (a := 208 * (fkT0g P.maxMass g Eb : ℝ) ^ 3)
      (b := 1872 * fkBg P.maxMass (Zc P D gamma) g Eb) (by positivity) (by positivity)
    have hf2 := alias_arith hm1 (a := 208 * (fkT0f P.maxMass (Zc P D gamma) g Eb : ℝ) ^ 3)
      (b := 1872 * fkBf P.maxMass (Zc P D gamma) g Eb) (by positivity) (by positivity)
    have hg3 := mul_le_mul_of_nonneg_left hg2 hZ0
    have hf3 := mul_le_mul_of_nonneg_left hf2 hZ0
    have hsum : Cform (fkZ P.maxMass (Zc P D gamma)) g * fkXg P.maxMass (Zc P D gamma) g Eb ^ 2 /
          (m : ℝ) ^ 3 +
        Zc P D gamma * (8 * (208 * (fkT0g P.maxMass g Eb : ℝ) ^ 3 +
          1872 * fkBg P.maxMass (Zc P D gamma) g Eb * Real.sqrt m) / (2 * (m : ℝ) + 1) ^ 2) +
        (Cform (fkZf P.maxMass (Zc P D gamma)) g * fkXf P.maxMass (Zc P D gamma) g Eb ^ 2 /
          (m : ℝ) ^ 3 +
        Zc P D gamma * (8 * (208 * (fkT0f P.maxMass (Zc P D gamma) g Eb : ℝ) ^ 3 +
          1872 * fkBf P.maxMass (Zc P D gamma) g Eb * Real.sqrt m) / (2 * (m : ℝ) + 1) ^ 2)) ≤
        fkConst P.maxMass (Zc P D gamma) g Eb / ((m : ℝ) * Real.sqrt m) := by
      have e : fkConst P.maxMass (Zc P D gamma) g Eb / ((m : ℝ) * Real.sqrt m) =
          (Cform (fkZ P.maxMass (Zc P D gamma)) g *
            fkXg P.maxMass (Zc P D gamma) g Eb ^ 2) / ((m : ℝ) * Real.sqrt m) +
          Zc P D gamma * (2 * (208 * (fkT0g P.maxMass g Eb : ℝ) ^ 3 +
            1872 * fkBg P.maxMass (Zc P D gamma) g Eb) / ((m : ℝ) * Real.sqrt m)) +
          ((Cform (fkZf P.maxMass (Zc P D gamma)) g *
            fkXf P.maxMass (Zc P D gamma) g Eb ^ 2) / ((m : ℝ) * Real.sqrt m) +
          Zc P D gamma * (2 * (208 * (fkT0f P.maxMass (Zc P D gamma) g Eb : ℝ) ^ 3 +
            1872 * fkBf P.maxMass (Zc P D gamma) g Eb) / ((m : ℝ) * Real.sqrt m))) := by
        unfold fkConst fkForm fkSg fkSf
        ring
      rw [e]
      linarith
    exact hcmp _ (hRf.trans (le_add_of_nonneg_left (by
        have := norm_nonneg (inner ℂ ug (Delta eta m P D gamma (sharpKernel gamma m) ug +
          kOp (vAlias eta m P D gamma) ug))
        linarith)))
      (hRg.trans (le_add_of_nonneg_right (by
        have := norm_nonneg (inner ℂ uf (Delta eta m P D gamma (sharpKernel gamma m) uf +
          kOp (vAlias eta m P D gamma) uf))
        linarith))) |>.trans hsum
  · -- the bound under correlation summability
    intro Crho hC0 hsumg hsumf
    have hAg' := norm_inner_vAlias_le_summable P D hgamma ug hsumg
    have hAf' := norm_inner_vAlias_le_summable P D hgamma uf hsumf
    have hRg' := norm_inner_Rfull_le P D hgamma hm1 ug hZZ hXg
      (fun r => htail_g m hsg r) hAg'
    have hRf' := norm_inner_Rfull_le P D hgamma hm1 uf hZZf hXf
      (fun r => htail_f m hsf (by omega) r) hAf'
    have hg1 := delta_arith2 hm1 hFg
    have hf1 := delta_arith2 hm1 hFf
    have hc2 := mul_le_mul_of_nonneg_left (alias_arith2 hm1 hC0) hZ0
    have hsum : Cform (fkZ P.maxMass (Zc P D gamma)) g * fkXg P.maxMass (Zc P D gamma) g Eb ^ 2 /
          (m : ℝ) ^ 3 + Zc P D gamma * (8 * Crho / (2 * (m : ℝ) + 1) ^ 2) +
        (Cform (fkZf P.maxMass (Zc P D gamma)) g * fkXf P.maxMass (Zc P D gamma) g Eb ^ 2 /
          (m : ℝ) ^ 3 + Zc P D gamma * (8 * Crho / (2 * (m : ℝ) + 1) ^ 2)) ≤
        fkConstImp P.maxMass (Zc P D gamma) g Eb Crho / (m : ℝ) ^ 2 := by
      have e : fkConstImp P.maxMass (Zc P D gamma) g Eb Crho / (m : ℝ) ^ 2 =
          (Cform (fkZ P.maxMass (Zc P D gamma)) g *
            fkXg P.maxMass (Zc P D gamma) g Eb ^ 2) / (m : ℝ) ^ 2 +
          Zc P D gamma * (2 * Crho / (m : ℝ) ^ 2) +
          ((Cform (fkZf P.maxMass (Zc P D gamma)) g *
            fkXf P.maxMass (Zc P D gamma) g Eb ^ 2) / (m : ℝ) ^ 2 +
          Zc P D gamma * (2 * Crho / (m : ℝ) ^ 2)) := by
        unfold fkConstImp fkForm
        ring
      rw [e]
      linarith
    exact hcmp _ (hRf'.trans (le_add_of_nonneg_left (by
        have := norm_nonneg (inner ℂ ug (Delta eta m P D gamma (sharpKernel gamma m) ug +
          kOp (vAlias eta m P D gamma) ug))
        linarith)))
      (hRg'.trans (le_add_of_nonneg_right (by
        have := norm_nonneg (inner ℂ uf (Delta eta m P D gamma (sharpKernel gamma m) uf +
          kOp (vAlias eta m P D gamma) uf))
        linarith))) |>.trans hsum

end Comparison

end

end PlaneWaveFullKernel

end DevFK4
-- END SOURCE dev/DevFK4.lean

-- BEGIN SOURCE dev/DevFK5.lean
-- SHA256 69b2c8725b67ebed0bee8e516269c498b2373a7c0eb12f816774eeec6a767db3
section DevFK5

/-!
# Full-kernel collocation for Coulomb systems: `prop:fullkernel`

For a periodic Coulomb system in the exchange sector of an admissible labelling, the
collocation of the maximal band-limited kernel `w_{≤4K}` on the padded register
(`n' = 4m+1` points per direction, `K = (2π/L) m`, `HposFull`) has a sector Ritz energy
`E_full` with (`periodicCoulombSectorFullKernelError`)

  `|E_full - E| ≤ C / K^{3/2}`   and   `|E_full - E| ≤ C' / N_reg^{1/2}`,
  `N_reg = (4m+1)³` (register modes),

for every `m` above a threshold, where `E` is the ground energy of the certificate.  Under
the summability of the cyclic correlations of the relevant ground states,

  `Σ_{d ≠ 0} |⟨u, S_t(d) u⟩| ≤ C_ρ`  for every pair and particle–nucleus term `t`,

for a sector ground state `u` of the Galerkin Hamiltonian `P H P` at cutoff `2K` and for the
DFT of a sector ground state of `H_full` (`FullKernelCorrSummable`), the bound improves to

  `|E_full - E| ≤ (A₁ + A₂ C_ρ)/K²`   and   `≤ 25 (A₁ + A₂ C_ρ)/(g² N_reg^{2/3})`.

The proof: `H_full = P H P + R_full` (`HfullMom_eq_gal`); the finite comparison
`full_galerkin_energy` bounds `|E_full - E_gal|` by `C/(m √m)` (or `(C₁ + C₂ C_ρ)/m²`), and the
certificate's cubic error at cutoff `2K` bounds `0 ≤ E_gal - E ≤ C_cub/(2K)³`; the
position-space and momentum-space Ritz energies coincide by the fold identity
(`isSecRitz_HposFull_iff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace PlaneWaveFullKernel

open PlaneWaveGrid PlaneWaveCertificate

noncomputable section

section Definitions

variable {eta : ℕ} {ν : Type*} [Fintype ν]

/-- The full-kernel ground energy of a Coulomb system in the exchange sector `lab`: the Ritz
energy of the collocation of the maximal band-limited kernel `w_{≤4K}` on the padded register
(`n' = 4m+1` points per direction, `K = (2π/L) m`). -/
def IsCoulombSectorFullKernelGroundEnergy (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (L : ℝ) (m : ℕ) (Ef : ℝ) : Prop :=
  IsSecRitz sys.sign lab (HposFull (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei)
    (coulombCellAmplitude L) (2 * Real.pi / L)) Ef

/-- **Cyclic correlation summability** for the relevant ground states, with constant `C_ρ`: a
normalised sector ground state `u` of the register Galerkin Hamiltonian `P H P` (cutoff `2K`)
and a normalised sector ground state `ψ` of the full-kernel collocation Hamiltonian whose
cyclic correlations `⟨·, S_t(d) ·⟩` (in the momentum basis of the register; for `ψ`, of its
DFT) satisfy `Σ_{d ≠ 0} |⟨u, S_t(d) u⟩| ≤ C_ρ` for every term `t`: every pair `(a, b)` (the
cyclic pair correlations `C^cyc_ab` of the manuscript, with `d ↦ -d`, `corrPair`) and every
particle–nucleus term (`S_t(d)` the shift of register `a` alone: the cyclic Fourier
coefficients of the one-particle density of `a`, `corrOne`).  The particle–nucleus clause is
an addition to the manuscript's pair hypothesis, needed because the nuclear alias terms couple
to the one-particle densities; it is vacuous without clamped nuclei. -/
def FullKernelCorrSummable (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ) (L : ℝ) (m : ℕ)
    (Crho : ℝ) : Prop :=
  (∃ u : EuclideanSpace ℂ (RCfg eta m),
      IsSecGroundState sys.sign lab (Hgal eta m (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) (2 * Real.pi / L)) u ∧
      ∀ t : Term eta ν, corrSum t u ≤ Crho) ∧
  (∃ ψ : EuclideanSpace ℂ (RCfg eta m),
      IsSecGroundState sys.sign lab (HposFull (m := m) (regParticlesOf sys)
        (posNucleiOf sys.nuclei) (coulombCellAmplitude L) (2 * Real.pi / L)) ψ ∧
      ∀ t : Term eta ν, corrSum t (dft ψ) ≤ Crho)

/-- The total coupling `Z_c` of a Coulomb system on the register. -/
def fullKernelZc (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)

/-- The size threshold of the full-kernel theorem: the larger of the threshold of the grid
theorem (which contains the cutoff, sector and energy-budget conditions used here) and the
bootstrap threshold of the full-kernel ground state. -/
def fullKernelThreshold (sys : CoulombSystem eta ν) (L : ℝ) : ℕ :=
  max (coulombGridThreshold sys L)
    (fkT0f sys.maxMass (fullKernelZc sys L) (2 * Real.pi / L) (coulombGridEnergyBudget sys L))

/-- The error constant `C` of `|E_full - E| ≤ C/K^{3/2}`. -/
def fullKernelErrorConstant (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  fkConst sys.maxMass (fullKernelZc sys L) (2 * Real.pi / L) (coulombGridEnergyBudget sys L) *
      ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L)) +
    coulombDataCubicErrorConstant sys L / (8 * ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L)))

/-- The error constant `C'` of `|E_full - E| ≤ C'/N_reg^{1/2}`. -/
def fullKernelBasisErrorConstant (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  Real.sqrt 125 * fullKernelErrorConstant sys L /
    ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L))

/-- The constant `A₁` of `|E_full - E| ≤ (A₁ + A₂ C_ρ)/K²`. -/
def fullKernelImpConstant₁ (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  (2 * Real.pi / L) ^ 2 * (fkForm sys.maxMass (fullKernelZc sys L) (2 * Real.pi / L)
      (coulombGridEnergyBudget sys L)) +
    coulombDataCubicErrorConstant sys L / (8 * (2 * Real.pi / L))

/-- The constant `A₂` of `|E_full - E| ≤ (A₁ + A₂ C_ρ)/K²`. -/
def fullKernelImpConstant₂ (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  4 * (2 * Real.pi / L) ^ 2 * fullKernelZc sys L

end Definitions

/-! ## Arithmetic -/

section Arith

lemma sqrt_mul_self_nat (m : ℕ) : Real.sqrt (((m : ℝ)) ^ 3) = (m : ℝ) * Real.sqrt m := by
  rw [show ((m : ℝ)) ^ 3 = (m : ℝ) ^ 2 * m by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]

/-- `C₁/(m √m) + C₂/(8 (g m)³) ≤ (C₁ g √g + C₂/(8 g √g))/((g m) √(g m))`. -/
lemma final_arith {g : ℝ} (hg : 0 < g) {m : ℕ} (hm : 1 ≤ m) {C1 C2 : ℝ} (hC2 : 0 ≤ C2) :
    C1 / ((m : ℝ) * Real.sqrt m) + C2 / (8 * (g * m) ^ 3) ≤
      (C1 * (g * Real.sqrt g) + C2 / (8 * (g * Real.sqrt g))) /
        ((g * m) * Real.sqrt (g * m)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsg2 : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg.le
  have hsm2 : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (by positivity)
  have hsplit : Real.sqrt (g * m) = Real.sqrt g * Real.sqrt m := Real.sqrt_mul hg.le _
  rw [hsplit, add_div]
  have hK : (g * m) * (Real.sqrt g * Real.sqrt m) = (g * Real.sqrt g) * (m * Real.sqrt m) := by
    ring
  have hgs : 0 < g * Real.sqrt g := by positivity
  have hms : 0 < (m : ℝ) * Real.sqrt m := by positivity
  refine add_le_add (le_of_eq ?_) ?_
  · rw [hK]
    field_simp
  · rw [div_div, hK]
    apply div_le_div_of_nonneg_left hC2 (by positivity)
    -- `8 (g √g)((g √g)(m √m)) ≤ 8 (g m)³`
    have hmsm : (m : ℝ) * Real.sqrt m ≤ (m : ℝ) ^ 3 := by
      have h1 : Real.sqrt (m : ℝ) ≤ m := sqrt_le_self_nat hm
      have h2 : Real.sqrt (m : ℝ) ≤ (m : ℝ) ^ 2 := h1.trans (by nlinarith)
      calc (m : ℝ) * Real.sqrt m ≤ (m : ℝ) * (m : ℝ) ^ 2 := by gcongr
        _ = (m : ℝ) ^ 3 := by ring
    have hgg : (g * Real.sqrt g) * (g * Real.sqrt g) = g ^ 3 := by nlinarith
    calc 8 * (g * Real.sqrt g) * ((g * Real.sqrt g) * (m * Real.sqrt m))
        = 8 * g ^ 3 * (m * Real.sqrt m) := by rw [← hgg]; ring
      _ ≤ 8 * g ^ 3 * (m : ℝ) ^ 3 := by gcongr
      _ = 8 * (g * m) ^ 3 := by ring

/-- `C/((g m) √(g m)) ≤ √125 C/(g √g)/√((4m+1)³)`. -/
lemma basis_arith {g : ℝ} (hg : 0 < g) {m : ℕ} (hm : 1 ≤ m) {C : ℝ} (hC : 0 ≤ C) :
    C / ((g * m) * Real.sqrt (g * m)) ≤
      Real.sqrt 125 * C / (g * Real.sqrt g) / Real.sqrt (((4 * m + 1) ^ 3 : ℕ) : ℝ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsplit : Real.sqrt (g * m) = Real.sqrt g * Real.sqrt m := Real.sqrt_mul hg.le _
  have hN : Real.sqrt (((4 * m + 1) ^ 3 : ℕ) : ℝ) ≤ Real.sqrt 125 * ((m : ℝ) * Real.sqrt m) := by
    rw [← sqrt_mul_self_nat, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    push_cast
    have : 4 * (m : ℝ) + 1 ≤ 5 * m := by linarith
    calc (4 * (m : ℝ) + 1) ^ 3 ≤ (5 * (m : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
      _ = 125 * (m : ℝ) ^ 3 := by ring
  have hNpos : 0 < Real.sqrt (((4 * m + 1) ^ 3 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  rw [hsplit, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h125 : 0 ≤ Real.sqrt 125 := Real.sqrt_nonneg _
  calc C * ((g * Real.sqrt g) * Real.sqrt (((4 * m + 1) ^ 3 : ℕ) : ℝ))
      ≤ C * ((g * Real.sqrt g) * (Real.sqrt 125 * ((m : ℝ) * Real.sqrt m))) := by gcongr
    _ = Real.sqrt 125 * C * ((g * m) * (Real.sqrt g * Real.sqrt m)) := by ring

/-- `C₁/m² + C₂/(8 (g m)³) ≤ (g² C₁ + C₂/(8 g))/(g m)²`. -/
lemma final_arith2 {g : ℝ} (hg : 0 < g) {m : ℕ} (hm : 1 ≤ m) {C1 C2 : ℝ} (hC2 : 0 ≤ C2) :
    C1 / (m : ℝ) ^ 2 + C2 / (8 * (g * m) ^ 3) ≤ (g ^ 2 * C1 + C2 / (8 * g)) / (g * m) ^ 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [add_div]
  refine add_le_add (le_of_eq ?_) ?_
  · field_simp
  · rw [div_div]
    apply div_le_div_of_nonneg_left hC2 (by positivity)
    have : 8 * g * (g * m) ^ 2 ≤ 8 * g * (g * m) ^ 2 * m :=
      le_mul_of_one_le_right (by positivity) hm1
    calc 8 * g * (g * m) ^ 2 ≤ 8 * g * (g * m) ^ 2 * m := this
      _ = 8 * (g * m) ^ 3 := by ring

lemma rpow_two_thirds_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ 3) ^ ((2 : ℝ) / 3) = x ^ 2 := by
  rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
  norm_num

/-- `A/(g m)² ≤ 25 A/(g² N^{2/3})` with `N = (4m+1)³`. -/
lemma basis_arith2 {g : ℝ} (hg : 0 < g) {m : ℕ} (hm : 1 ≤ m) {A : ℝ} (hA : 0 ≤ A) :
    A / (g * m) ^ 2 ≤ 25 * A / g ^ 2 / (((4 * m + 1) ^ 3 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : (((4 * m + 1) ^ 3 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) = (4 * (m : ℝ) + 1) ^ 2 := by
    push_cast
    exact rpow_two_thirds_cube _ (by positivity)
  rw [hN, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (4 * (m : ℝ) + 1) ^ 2 ≤ 25 * (m : ℝ) ^ 2 := by nlinarith
  calc A * (g ^ 2 * (4 * (m : ℝ) + 1) ^ 2) ≤ A * (g ^ 2 * (25 * (m : ℝ) ^ 2)) := by gcongr
    _ = 25 * A * (g * m) ^ 2 := by ring

end Arith

/-! ## The theorem -/

section Main

variable {eta : ℕ} {ν : Type*} [Fintype ν]

lemma isSecRitz_unique {n : ℕ} [NeZero n] {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ}
    {H : EuclideanSpace ℂ (GConfig eta n) →ₗ[ℂ] EuclideanSpace ℂ (GConfig eta n)} {E E' : ℝ}
    (h : IsSecRitz sgn lab H E) (h' : IsSecRitz sgn lab H E') : E = E' := by
  obtain ⟨hl, u, hu, hn, hv⟩ := h
  obtain ⟨hl', u', hu', hn', hv'⟩ := h'
  exact ritz_unique H {v | IsSec sgn lab v} E E' hl hl' u u' hu hu' hn hn' hv hv'

/-- **`prop:fullkernel`.**  In the exchange sector of an admissible labelling `lab`, for every
`m` at or above `fullKernelThreshold`, the full-kernel collocation (maximal band-limited kernel
`w_{≤4K}`, `n' = 4m+1` points per direction, `K = (2π/L) m`) has a sector Ritz energy `E_full`
with `|E_full - E| ≤ C/K^{3/2}` and `|E_full - E| ≤ C'/N_reg^{1/2}`, `N_reg = (4m+1)³`, and,
under the cyclic correlation summability of the relevant ground states with constant `C_ρ`,
`|E_full - E| ≤ (A₁ + A₂ C_ρ)/K²` and `≤ 25 (A₁ + A₂ C_ρ)/(g² N_reg^{2/3})`. -/
theorem periodicCoulombSectorFullKernelError (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ psi : MolecularPositionL2 eta,
      HasCoulombSectorGroundPair sys lab L psi E ∧
      |E| ≤ coulombGroundEnergyBudget sys L ∧
      ∀ m : ℕ, fullKernelThreshold sys L ≤ m →
        ∃ Ef : ℝ, IsCoulombSectorFullKernelGroundEnergy sys lab L m Ef ∧
          |Ef - E| ≤ fullKernelErrorConstant sys L /
            (((2 * Real.pi / L) * m) * Real.sqrt ((2 * Real.pi / L) * m)) ∧
          |Ef - E| ≤ fullKernelBasisErrorConstant sys L /
            Real.sqrt (((4 * m + 1) ^ 3 : ℕ) : ℝ) ∧
          ∀ Crho : ℝ, 0 ≤ Crho → FullKernelCorrSummable sys lab L m Crho →
            |Ef - E| ≤ (fullKernelImpConstant₁ sys L + fullKernelImpConstant₂ sys L * Crho) /
              ((2 * Real.pi / L) * m) ^ 2 ∧
            |Ef - E| ≤ 25 * (fullKernelImpConstant₁ sys L + fullKernelImpConstant₂ sys L * Crho) /
              (2 * Real.pi / L) ^ 2 / (((4 * m + 1) ^ 3 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨E, psi, hPair, hEbud, hCubic⟩ := coulomb_sector_data_cubic_error sys lab hlab L hL
  refine ⟨E, psi, hPair, hEbud, ?_⟩
  intro m hm
  -- consequences of the threshold
  have hgrid : coulombGridThreshold sys L ≤ m := (le_max_left _ _).trans hm
  have hfull : fkT0f sys.maxMass (fullKernelZc sys L) (2 * Real.pi / L)
      (coulombGridEnergyBudget sys L) ≤ m := (le_max_right _ _).trans hm
  have hthr := hgrid
  unfold coulombGridThreshold at hthr
  have hm8 : 8 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hmcub : coulombDataCubicThreshold sys L ≤ 2 * m := by omega
  have hmeta : eta ≤ m := by omega
  have hmroot : Nat.ceil (coulombDataCubicErrorConstant sys L ^ ((1 : ℝ) / 3) /
      (2 * (2 * Real.pi / L))) ≤ m := by omega
  -- the Galerkin energy at cutoff `2K`
  obtain ⟨H, hKernel, -⟩ := exists_coulombFourierH2Operator sys L
    molecularCanonicalUnitHardyConstant hL canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨EN, hEN, _hcard, hNonneg, hRate, _hNRate⟩ := hCubic (2 * m) hmcub
  have hcont := (isCoulombSectorCubicGroundEnergy_iff_physicalGalerkinBridge
    sys lab L hL H hKernel _ EN).mp hEN
  have hLne : L ≠ 0 := hL.ne'
  have hfin := continuum_sector_cubic_ground_to_finite
    (coulombPhysicalGalerkinBridge sys lab L hL H hKernel) _ EN (2 * m) (2 * m)
    (by rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hLne]) le_rfl hcont
  have hgal := galRitz_of_cubic sys lab m L hL EN hfin
  -- abbreviations
  set g : ℝ := 2 * Real.pi / L with hgdef
  have hg : 0 < g := by positivity
  set γ : ℝ := coulombCellAmplitude L with hγdef
  have hγ : 0 ≤ γ := (coulombCellAmplitude_pos hL).le
  set P := regParticlesOf sys with hPdef
  set D := (posNucleiOf sys.nuclei).toNucData with hDdef
  set Eb : ℝ := coulombGridEnergyBudget sys L with hEbdef
  set Ccub : ℝ := coulombDataCubicErrorConstant sys L with hCcubdef
  have hCcub : 0 ≤ Ccub := coulombDataCubicErrorConstant_nonneg sys L
  -- the cutoff error at `2K` is at most one, so `|E_N| ≤ E_b`
  have hroot : Ccub ^ ((1 : ℝ) / 3) ≤ g * ((2 * m : ℕ) : ℝ) := by
    have h1 : Ccub ^ ((1 : ℝ) / 3) / (2 * g) ≤ m :=
      (Nat.le_ceil _).trans (by exact_mod_cast hmroot)
    rw [div_le_iff₀ (by positivity)] at h1
    push_cast
    linarith
  have hcube : Ccub ≤ (g * ((2 * m : ℕ) : ℝ)) ^ 3 := by
    have h1 : (Ccub ^ ((1 : ℝ) / 3)) ^ 3 = Ccub := by
      rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow hCcub (by norm_num)
    calc Ccub = (Ccub ^ ((1 : ℝ) / 3)) ^ 3 := h1.symm
      _ ≤ (g * ((2 * m : ℕ) : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hCcub _) hroot 3
  have h2m : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * m)
  have hENE : EN - E ≤ 1 :=
    hRate.trans ((div_le_one (by positivity)).mpr hcube)
  have hEb : |EN| ≤ Eb := by
    have h1 : |EN| ≤ |E| + 1 := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le E]
      · linarith [le_abs_self E]
    have h2 : Eb = coulombGroundEnergyBudget sys L + 1 := rfl
    rw [h2]
    linarith
  have hrate' : EN - E ≤ Ccub / (8 * (g * m) ^ 3) := by
    refine hRate.trans (le_of_eq ?_)
    push_cast
    ring
  -- ground states of the Galerkin and full-kernel Hamiltonians in the sector
  have hNZ := exists_nonzero_sec sys hlab m hmeta
  have hP : ∀ a b, lab a = lab b → P.mass a = P.mass b ∧ P.charge a = P.charge b :=
    fun a b h => ⟨sys.mass_eq a b (hlab a b h), sys.charge_eq a b (hlab a b h)⟩
  set F := secSubmodule eta (2 * (2 * m) + 1) sys.sign lab
  have hNZ' : ∃ u, u ∈ F ∧ u ≠ 0 := hNZ
  obtain ⟨E2, u2, hu2F, hu2n, hu2E, hu2low⟩ := exists_ground_eigenpair_on_invariant'
    (Hgal eta m P D γ g) Hgal_isSymmetric F (fun u hu => Hgal_sec hP u hu) hNZ'
  obtain ⟨E1, u1, hu1F, hu1n, hu1E, hu1low⟩ := exists_ground_eigenpair_on_invariant'
    (HfullMom eta m P D γ g) (HfullMom_isSymmetric P D γ g) F
    (fun u hu => HfullMom_sec P D γ g hP u hu) hNZ'
  have hRitz2 : IsSecRitz sys.sign lab (Hgal eta m P D γ g) E2 :=
    ⟨fun v hv => hu2low v hv, u2, hu2F, hu2n, re_inner_eigen _ u2 hu2n E2 hu2E⟩
  have hE2 : E2 = EN := isSecRitz_unique hRitz2 hgal
  rw [hE2] at hu2E hu2low
  have hRitz1 : IsSecRitz sys.sign lab (HfullMom eta m P D γ g) E1 :=
    ⟨fun v hv => hu1low v hv, u1, hu1F, hu1n, re_inner_eigen _ u1 hu1n E1 hu1E⟩
  have hpos : IsCoulombSectorFullKernelGroundEnergy sys lab L m E1 :=
    (isSecRitz_HposFull_iff sys.sign lab P (posNucleiOf sys.nuclei) γ g E1).mpr hRitz1
  -- the finite comparison
  have hsf : fkT0f P.maxMass (Zc P D γ) g Eb ≤ m := hfull
  have hcmp := full_galerkin_energy P D sys.sign lab hγ hg hsf hEb u2 hu2F hu2n hu2E
    (fun v hv => hu2low v hv) u1 hu1F hu1n hu1E (fun v hv => hu1low v hv)
  have hM0 : 0 < P.maxMass := P.maxMass_pos
  have hZ0 : 0 ≤ Zc P D γ := Zc_nonneg hγ
  have hEb0 : 0 ≤ Eb := (abs_nonneg _).trans hEb
  have hC0 : 0 ≤ fkConst P.maxMass (Zc P D γ) g Eb := fkConst_nonneg hM0.le hZ0 hEb0
  -- the bound `C/K^{3/2}`
  have hK : |E1 - E| ≤ fullKernelErrorConstant sys L / ((g * m) * Real.sqrt (g * m)) := by
    have h1 : |E1 - E| ≤ |E1 - EN| + (EN - E) := by
      have := abs_sub_le E1 EN E
      rwa [abs_of_nonneg hNonneg] at this
    have h2 := final_arith hg hm1 (C1 := fkConst P.maxMass (Zc P D γ) g Eb) hCcub
    have e : fullKernelErrorConstant sys L =
        fkConst P.maxMass (Zc P D γ) g Eb * (g * Real.sqrt g) + Ccub / (8 * (g * Real.sqrt g)) :=
      rfl
    rw [e]
    linarith [hcmp.1]
  refine ⟨E1, hpos, hK, ?_, ?_⟩
  · -- the basis-count form
    have hCe : 0 ≤ fullKernelErrorConstant sys L := by
      have e : fullKernelErrorConstant sys L =
          fkConst P.maxMass (Zc P D γ) g Eb * (g * Real.sqrt g) +
            Ccub / (8 * (g * Real.sqrt g)) := rfl
      rw [e]
      have : 0 < g * Real.sqrt g := by positivity
      positivity
    exact hK.trans (basis_arith hg hm1 hCe)
  · -- the bound under correlation summability
    intro Crho hCrho hsum
    obtain ⟨⟨ug, ⟨hugS, hugn, Eg', hgR, hgE⟩, hsumg⟩, ⟨ψ, ⟨hψS, hψn, Ef', hfR, hfE⟩, hsumf⟩⟩ :=
      hsum
    have hEg' : Eg' = EN := isSecRitz_unique hgR hgal
    rw [hEg'] at hgR hgE
    have hfR' := (isSecRitz_HposFull_iff sys.sign lab P (posNucleiOf sys.nuclei) γ g Ef').mp hfR
    have hEf' : Ef' = E1 := isSecRitz_unique hfR' hRitz1
    rw [hEf'] at hfR' hfE
    have hfE' := (HposFull_eigen_iff P (posNucleiOf sys.nuclei) γ g E1 ψ).mp hfE
    have hcmp2 := full_galerkin_energy P D sys.sign lab hγ hg hsf hEb ug hugS hugn hgE
      (fun v hv => hgR.1 v hv) (dft ψ) (dft_sec ψ hψS) (by rw [norm_dft, hψn]) hfE'
      (fun v hv => hfR'.1 v hv)
    have hb := hcmp2.2 Crho hCrho hsumg hsumf
    have h1 : |E1 - E| ≤ |E1 - EN| + (EN - E) := by
      have := abs_sub_le E1 EN E
      rwa [abs_of_nonneg hNonneg] at this
    have h2 := final_arith2 hg hm1 (C1 := fkConstImp P.maxMass (Zc P D γ) g Eb Crho) hCcub
    have e₁ : fullKernelImpConstant₁ sys L =
        g ^ 2 * fkForm P.maxMass (Zc P D γ) g Eb + Ccub / (8 * g) := rfl
    have e₂ : fullKernelImpConstant₂ sys L = 4 * g ^ 2 * Zc P D γ := rfl
    have e : fullKernelImpConstant₁ sys L + fullKernelImpConstant₂ sys L * Crho =
        g ^ 2 * fkConstImp P.maxMass (Zc P D γ) g Eb Crho + Ccub / (8 * g) := by
      rw [e₁, e₂]
      unfold fkConstImp
      ring
    have hKK : |E1 - E| ≤ (fullKernelImpConstant₁ sys L + fullKernelImpConstant₂ sys L * Crho) /
        (g * m) ^ 2 := by
      rw [e]
      linarith
    refine ⟨hKK, hKK.trans (basis_arith2 hg hm1 ?_)⟩
    rw [e]
    have := fkForm_nonneg (g := g) (Eb := Eb) hM0.le hZ0
    unfold fkConstImp
    positivity

/-- **The summability hypothesis is satisfiable at every single size** (its content is the
uniformity of `C_ρ` in `m`): for every `m ≥ η` some `C_ρ ≥ 0` works. -/
theorem fullKernelCorrSummable_exists (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ}
    (hlab : sys.IsAdmissible lab) (L : ℝ) (m : ℕ) (hm : eta ≤ m) :
    ∃ Crho : ℝ, 0 ≤ Crho ∧ FullKernelCorrSummable sys lab L m Crho := by
  set g : ℝ := 2 * Real.pi / L
  set γ : ℝ := coulombCellAmplitude L
  set P := regParticlesOf sys
  set D := (posNucleiOf sys.nuclei).toNucData
  have hNZ := exists_nonzero_sec sys hlab m hm
  have hP : ∀ a b, lab a = lab b → P.mass a = P.mass b ∧ P.charge a = P.charge b :=
    fun a b h => ⟨sys.mass_eq a b (hlab a b h), sys.charge_eq a b (hlab a b h)⟩
  set F := secSubmodule eta (2 * (2 * m) + 1) sys.sign lab
  have hNZ' : ∃ u, u ∈ F ∧ u ≠ 0 := hNZ
  obtain ⟨E2, u2, hu2F, hu2n, hu2E, hu2low⟩ := exists_ground_eigenpair_on_invariant'
    (Hgal eta m P D γ g) Hgal_isSymmetric F (fun u hu => Hgal_sec hP u hu) hNZ'
  obtain ⟨E1, u1, hu1F, hu1n, hu1E, hu1low⟩ := exists_ground_eigenpair_on_invariant'
    (HfullMom eta m P D γ g) (HfullMom_isSymmetric P D γ g) F
    (fun u hu => HfullMom_sec P D γ g hP u hu) hNZ'
  have hRitz2 : IsSecRitz sys.sign lab (Hgal eta m P D γ g) E2 :=
    ⟨fun v hv => hu2low v hv, u2, hu2F, hu2n, re_inner_eigen _ u2 hu2n E2 hu2E⟩
  have hRitz1 : IsSecRitz sys.sign lab (HfullMom eta m P D γ g) E1 :=
    ⟨fun v hv => hu1low v hv, u1, hu1F, hu1n, re_inner_eigen _ u1 hu1n E1 hu1E⟩
  set ψ := idft u1 with hψ
  have hdψ : dft ψ = u1 := dft_idft u1
  have hψE : HposFull (m := m) P (posNucleiOf sys.nuclei) γ g ψ = (E1 : ℂ) • ψ :=
    (HposFull_eigen_iff P (posNucleiOf sys.nuclei) γ g E1 ψ).mpr (by rw [hdψ]; exact hu1E)
  have hψn : ‖ψ‖ = 1 := by
    have := norm_dft ψ
    rw [hdψ, hu1n] at this
    exact this.symm
  set C : ℝ := ∑ t : Term eta ν, (corrSum t u2 + corrSum t u1) with hC
  have hcs : ∀ (t : Term eta ν) (u : EuclideanSpace ℂ (RCfg eta m)), 0 ≤ corrSum t u :=
    fun t u => sum_nonneg fun d _ => norm_nonneg _
  have hle : ∀ t : Term eta ν, corrSum t u2 + corrSum t u1 ≤ C := fun t =>
    Finset.single_le_sum (f := fun t => corrSum t u2 + corrSum t u1)
      (fun t _ => add_nonneg (hcs t u2) (hcs t u1)) (Finset.mem_univ t)
  refine ⟨C, sum_nonneg fun t _ => add_nonneg (hcs t u2) (hcs t u1), ?_, ?_⟩
  · refine ⟨u2, ⟨hu2F, hu2n, E2, hRitz2, hu2E⟩, fun t => ?_⟩
    linarith [hle t, hcs t u1]
  · refine ⟨ψ, ⟨idft_sec u1 hu1F, hψn, E1,
      (isSecRitz_HposFull_iff sys.sign lab P (posNucleiOf sys.nuclei) γ g E1).mpr hRitz1, hψE⟩,
      fun t => ?_⟩
    rw [hdψ]
    linarith [hle t, hcs t u2]

end Main

end

end PlaneWaveFullKernel

end DevFK5
-- END SOURCE dev/DevFK5.lean

-- BEGIN SOURCE dev/DevFK6.lean
-- SHA256 fad8c5d6cb13508bd62f1f06e42454fabe500f9aa0add68dec366ef4a689ead7
section DevFK6

/-!
# Full-kernel collocation on the spin-inclusive space and in the Born–Oppenheimer case

The manuscript's exchange sector is that of states symmetric or antisymmetric under the
simultaneous exchange of positions and spins.  As for the grid theorem of the grid files
(`periodicCoulombKernelGridError`), the full-kernel theorem on the spin-inclusive space
`L²((T³)^η; ⊗_a ℂ^{d_a})` follows from the theorem in every spin sector
(`periodicCoulombSectorFullKernelError`): the spin-independent full-kernel Hamiltonian
(`spinHposFull`, `HposFull` on each spin component) commutes with the symmetrisation within
species (`spinHposFull_symmetrize`, from `HposFull_gridPermute`), so its ground energy on the
physical spin-dependent grid states is the least sector energy over the valid spin patterns
(`IsCoulombSpinFullKernelGroundEnergy.of_sectors`), and the bounds carry over with the same
threshold and constants (`periodicCoulombFullKernelError`).  The improved bound assumes the
correlation summability in the valid spin sectors that hold a ground state, of the continuum
problem (sector energy `E`) or of the collocation (sector energy `E_full`); the proof uses one
sector of each kind.  The Born–Oppenheimer statements (electrons and clamped nuclei, the
electronic space `Λ^η(L²(T³) ⊗ ℂ²)` and its exchange sectors) are the instances at
`CoulombSystem.bo eta data` (`periodicMolecularSectorFullKernelError`,
`periodicMolecularFullKernelError`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace PlaneWaveFullKernel

open PlaneWaveGrid PlaneWaveCertificate

noncomputable section

section Spin

variable {eta : ℕ} {ν : Type*} [Fintype ν]

/-- The spin-independent full-kernel collocation Hamiltonian: `HposFull` on each spin
component. -/
def spinHposFull {S : Type*} [Fintype S] {m : ℕ} (P : RegParticles eta) (N : PosNuclei ν)
    (gamma g : ℝ) :
    PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m)) →ₗ[ℂ]
      PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m)) where
  toFun Φ := WithLp.toLp 2 (fun σ => HposFull P N gamma g (Φ σ))
  map_add' := by
    intro Φ Ψ
    apply PiLp.ext
    intro σ
    change HposFull P N gamma g ((Φ + Ψ) σ) =
      HposFull P N gamma g (Φ σ) + HposFull P N gamma g (Ψ σ)
    rw [PiLp.add_apply, map_add]
  map_smul' := by
    intro c Φ
    apply PiLp.ext
    intro σ
    change HposFull P N gamma g ((c • Φ) σ) = c • HposFull P N gamma g (Φ σ)
    rw [PiLp.smul_apply, map_smul]

lemma spinHposFull_apply {S : Type*} [Fintype S] {m : ℕ} (P : RegParticles eta)
    (N : PosNuclei ν) (gamma g : ℝ) (Φ : PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m)))
    (σ : S) : spinHposFull P N gamma g Φ σ = HposFull P N gamma g (Φ σ) := rfl

/-- The full-kernel ground energy of a Coulomb system on the spin-inclusive space: the Ritz
energy of the spin-independent full-kernel collocation Hamiltonian on the physical
spin-dependent grid states. -/
def IsCoulombSpinFullKernelGroundEnergy (sys : CoulombSystem eta ν) (D : ℕ) (dim : ℕ → ℕ)
    (L : ℝ) (m : ℕ) (Ef : ℝ) : Prop :=
  (∀ Φ : CoulombGridSpinState eta D m, IsCoulombGridSpinSector sys dim Φ →
    Ef * ‖Φ‖ ^ 2 ≤ (inner ℂ Φ (spinHposFull (regParticlesOf sys) (posNucleiOf sys.nuclei)
      (coulombCellAmplitude L) (2 * Real.pi / L) Φ)).re) ∧
  ∃ Φ : CoulombGridSpinState eta D m, IsCoulombGridSpinSector sys dim Φ ∧ ‖Φ‖ = 1 ∧
    (inner ℂ Φ (spinHposFull (regParticlesOf sys) (posNucleiOf sys.nuclei)
      (coulombCellAmplitude L) (2 * Real.pi / L) Φ)).re = Ef

/-- Symmetrisation within species commutes with the spin-independent full-kernel
Hamiltonian. -/
lemma spinHposFull_symmetrize (sys : CoulombSystem eta ν) (gamma g : ℝ) {D m : ℕ}
    (σ₀ : Fin eta → Fin D) (u : EuclideanSpace ℂ (RCfg eta m)) :
    spinHposFull (regParticlesOf sys) (posNucleiOf sys.nuclei) gamma g
        ((gridRelabelling eta (2 * (2 * m) + 1)).symmetrize sys.toCoulombParticles σ₀ u) =
      (gridRelabelling eta (2 * (2 * m) + 1)).symmetrize sys.toCoulombParticles σ₀
        (HposFull (regParticlesOf sys) (posNucleiOf sys.nuclei) gamma g u) := by
  apply PiLp.ext
  intro σ
  rw [spinHposFull_apply]
  exact ((gridRelabelling eta (2 * (2 * m) + 1)).symmetrize_rel sys.toCoulombParticles
    (Rel := fun f h => h = HposFull (regParticlesOf sys) (posNucleiOf sys.nuclei) gamma g f)
    (fun π hπ f h hfh => by
      rw [hfh]
      exact (HposFull_gridPermute (regParticlesOf sys) (posNucleiOf sys.nuclei) gamma g π
        (fun k => ⟨hπ.mass k, hπ.charge k⟩) f).symm)
    (fun c f h hfh => by rw [hfh, map_smul])
    σ₀ (f := u) (h := HposFull (regParticlesOf sys) (posNucleiOf sys.nuclei) gamma g u) rfl
    σ).symm

/-- The lowest full-kernel energy over the sectors of the valid spin patterns is the full-kernel
ground energy on the spin-inclusive space. -/
theorem IsCoulombSpinFullKernelGroundEnergy.of_sectors {sys : CoulombSystem eta ν} {D : ℕ}
    {dim : ℕ → ℕ} {L : ℝ} {m : ℕ} (Ef : (Fin eta → Fin D) → ℝ)
    (hEf : ∀ σ, IsCoulombSectorFullKernelGroundEnergy sys (sys.spinSectorLabel σ) L m (Ef σ))
    (σ₁ : Fin eta → Fin D) (hσ₁ : sys.IsValidSpin dim σ₁)
    (hmin : ∀ σ, sys.IsValidSpin dim σ → Ef σ₁ ≤ Ef σ) :
    IsCoulombSpinFullKernelGroundEnergy sys D dim L m (Ef σ₁) := by
  let R := gridRelabelling eta (2 * (2 * m) + 1)
  constructor
  · intro Φ hΦ
    apply pi_lower_bound_of_components
    intro σ
    by_cases hv : sys.IsValidSpin dim σ
    · exact (mul_le_mul_of_nonneg_right (hmin σ hv) (sq_nonneg _)).trans
        ((hEf σ).1 (Φ σ) ((isSec_iff_isSignedSector _ _ _).mpr
          (ParticleRelabelling.IsCoulombSpinSector.component hΦ σ)))
    · rw [ParticleRelabelling.IsCoulombSpinSector.eq_zero_of_not_valid hΦ hv, norm_zero,
        inner_zero_left]
      simp
  · obtain ⟨u, hu, hn, hv⟩ := (hEf σ₁).2
    let A : CoulombGridSpinState eta D m := R.symmetrize sys.toCoulombParticles σ₁ u
    have hA : ‖A‖ ≠ 0 := R.symmetrize_norm_ne_zero sys.toCoulombParticles σ₁ hn
    have hS : IsCoulombGridSpinSector sys dim A :=
      R.symmetrize_isCoulombSpinSector sys.toCoulombParticles dim hσ₁
        ((isSec_iff_isSignedSector _ _ u).mp hu)
    refine ⟨((‖A‖⁻¹ : ℝ) : ℂ) • A, ParticleRelabelling.IsCoulombSpinSector.smul hS _,
      norm_inv_smul_self_eq_one hA, ?_⟩
    rw [map_smul, spinHposFull_symmetrize sys]
    exact (R.symmetrize_rayleigh sys.toCoulombParticles σ₁ hn).trans hv

/-- If `x₁ ≤ x₀`, `y₀ ≤ y₁`, `|x₀ - y₀| ≤ A` and `|x₁ - y₁| ≤ B`, then `|x₁ - y₀| ≤ max A B`
(applied to the least sector energies `x₁ = E_full(σ₁)` and `y₀ = E(σ₀)`). -/
private lemma abs_sub_min_le {A B : ℝ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₁ ≤ x₀) (hy : y₀ ≤ y₁)
    (h0 : |x₀ - y₀| ≤ A) (h1 : |x₁ - y₁| ≤ B) : |x₁ - y₀| ≤ max A B := by
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  rw [abs_le]
  constructor
  · have := le_max_right A B
    linarith
  · have := le_max_left A B
    linarith

/-- **`prop:fullkernel` on the spin-inclusive space**, with `dim s` spin states for the
species `s`: the full-kernel ground energy on the physical spin-dependent grid states satisfies
the bounds of `periodicCoulombSectorFullKernelError` with the same threshold and constants; the
improved bound holds if the correlation summability holds in every valid spin sector that holds
a ground state, of the continuum problem (sector ground energy `E`) or of the collocation
(sector energy `E_full`). -/
theorem periodicCoulombFullKernelError (sys : CoulombSystem eta ν) (D : ℕ) (dim : ℕ → ℕ)
    (hdim : ∀ a, 0 < dim (sys.species a) ∧ dim (sys.species a) ≤ D) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ Ψ : CoulombSpinL2 eta D,
      HasCoulombSpinGroundPair sys dim L Ψ E ∧
      |E| ≤ coulombGroundEnergyBudget sys L ∧
      ∀ m : ℕ, fullKernelThreshold sys L ≤ m →
        ∃ Ef : ℝ, IsCoulombSpinFullKernelGroundEnergy sys D dim L m Ef ∧
          |Ef - E| ≤ fullKernelErrorConstant sys L /
            (((2 * Real.pi / L) * m) * Real.sqrt ((2 * Real.pi / L) * m)) ∧
          |Ef - E| ≤ fullKernelBasisErrorConstant sys L /
            Real.sqrt (((4 * m + 1) ^ 3 : ℕ) : ℝ) ∧
          ∀ Crho : ℝ, 0 ≤ Crho →
            (∀ σ : Fin eta → Fin D, sys.IsValidSpin dim σ →
              ((∃ psi, HasCoulombSectorGroundPair sys (sys.spinSectorLabel σ) L psi E) ∨
                IsCoulombSectorFullKernelGroundEnergy sys (sys.spinSectorLabel σ) L m Ef) →
              FullKernelCorrSummable sys (sys.spinSectorLabel σ) L m Crho) →
            |Ef - E| ≤ (fullKernelImpConstant₁ sys L + fullKernelImpConstant₂ sys L * Crho) /
              ((2 * Real.pi / L) * m) ^ 2 ∧
            |Ef - E| ≤ 25 * (fullKernelImpConstant₁ sys L + fullKernelImpConstant₂ sys L * Crho) /
              (2 * Real.pi / L) ^ 2 / (((4 * m + 1) ^ 3 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := by
  classical
  choose E ψ hPair hBudget hFull using
    fun σ : Fin eta → Fin D => periodicCoulombSectorFullKernelError sys (sys.spinSectorLabel σ)
      (sys.spinSectorLabel_isAdmissible σ) L hL
  obtain ⟨σ₀, hσ₀, hmin⟩ := sys.exists_min_valid hdim E
  refine ⟨E σ₀, _, HasCoulombSpinGroundPair.of_sectors E ψ hPair σ₀ hσ₀ hmin,
    hBudget σ₀, ?_⟩
  intro m hm
  choose Ef hEf hK hN hImp using fun σ : Fin eta → Fin D => hFull σ m hm
  obtain ⟨σ₁, hσ₁, hmin₁⟩ := sys.exists_min_valid hdim Ef
  have hx := hmin₁ σ₀ hσ₀
  have hy := hmin σ₁ hσ₁
  refine ⟨Ef σ₁, IsCoulombSpinFullKernelGroundEnergy.of_sectors Ef hEf σ₁ hσ₁ hmin₁, ?_, ?_, ?_⟩
  · have := abs_sub_min_le hx hy (hK σ₀) (hK σ₁)
    rwa [max_self] at this
  · have := abs_sub_min_le hx hy (hN σ₀) (hN σ₁)
    rwa [max_self] at this
  · intro Crho hC hS
    have h0 := hImp σ₀ Crho hC (hS σ₀ hσ₀ (Or.inl ⟨ψ σ₀, hPair σ₀⟩))
    have h1 := hImp σ₁ Crho hC (hS σ₁ hσ₁ (Or.inr (hEf σ₁)))
    constructor
    · have := abs_sub_min_le hx hy h0.1 h1.1
      rwa [max_self] at this
    · have := abs_sub_min_le hx hy h0.2 h1.2
      rwa [max_self] at this

end Spin

/-! ## The Born–Oppenheimer problem -/

section BO

variable {ν : Type*} [Fintype ν]

/-- The full-kernel ground energy in the exchange sector `lab` of the Born–Oppenheimer problem:
the Ritz energy of the full-kernel collocation Hamiltonian for electrons and the clamped nuclei
on grid functions antisymmetric under exchange of two registers with equal labels. -/
def IsMolecularFermionicFullKernelGroundEnergy (eta : ℕ) (lab : Fin eta → ℕ) (L : ℝ)
    (data : FiniteBONuclearData ν) (m : ℕ) (Ef : ℝ) : Prop :=
  IsSecRitz (fun _ => -1) lab (HposFull (m := m) (RegParticles.electrons eta) (posNucleiOf data)
    (coulombCellAmplitude L) (2 * Real.pi / L)) Ef

lemma isMolecularFermionicFullKernelGroundEnergy_iff (eta : ℕ) (lab : Fin eta → ℕ) (L : ℝ)
    (data : FiniteBONuclearData ν) (m : ℕ) (Ef : ℝ) :
    IsMolecularFermionicFullKernelGroundEnergy eta lab L data m Ef ↔
      IsCoulombSectorFullKernelGroundEnergy (CoulombSystem.bo eta data) lab L m Ef := Iff.rfl

/-- **`prop:fullkernel` in an exchange sector, Born–Oppenheimer case** (electrons and clamped
nuclei), with the threshold and constants of the system `CoulombSystem.bo eta data`. -/
theorem periodicMolecularSectorFullKernelError (eta : ℕ) (lab : Fin eta → ℕ) (_heta : 0 < eta)
    (data : FiniteBONuclearData ν) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ psi : MolecularPositionL2 eta,
      HasMolecularFermionicGroundPair eta lab L data psi E ∧
      |E| ≤ molecularGroundEnergyBudget eta data L ∧
      ∀ m : ℕ, fullKernelThreshold (CoulombSystem.bo eta data) L ≤ m →
        ∃ Ef : ℝ, IsMolecularFermionicFullKernelGroundEnergy eta lab L data m Ef ∧
          |Ef - E| ≤ fullKernelErrorConstant (CoulombSystem.bo eta data) L /
            (((2 * Real.pi / L) * m) * Real.sqrt ((2 * Real.pi / L) * m)) ∧
          |Ef - E| ≤ fullKernelBasisErrorConstant (CoulombSystem.bo eta data) L /
            Real.sqrt (((4 * m + 1) ^ 3 : ℕ) : ℝ) ∧
          ∀ Crho : ℝ, 0 ≤ Crho →
            FullKernelCorrSummable (CoulombSystem.bo eta data) lab L m Crho →
            |Ef - E| ≤ (fullKernelImpConstant₁ (CoulombSystem.bo eta data) L +
                fullKernelImpConstant₂ (CoulombSystem.bo eta data) L * Crho) /
              ((2 * Real.pi / L) * m) ^ 2 ∧
            |Ef - E| ≤ 25 * (fullKernelImpConstant₁ (CoulombSystem.bo eta data) L +
                fullKernelImpConstant₂ (CoulombSystem.bo eta data) L * Crho) /
              (2 * Real.pi / L) ^ 2 / (((4 * m + 1) ^ 3 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨E, psi, hPair, hBud, hFull⟩ :=
    periodicCoulombSectorFullKernelError (CoulombSystem.bo eta data) lab (fun _ _ _ => rfl) L hL
  refine ⟨E, psi, (hasCoulombSectorGroundPair_bo eta data lab L psi E).mp hPair, ?_, ?_⟩
  · rwa [coulombGroundEnergyBudget_bo] at hBud
  · intro m hm
    obtain ⟨Ef, hEf, hK, hN, hImp⟩ := hFull m hm
    exact ⟨Ef, (isMolecularFermionicFullKernelGroundEnergy_iff eta lab L data m Ef).mpr hEf,
      hK, hN, hImp⟩

/-- The full-kernel ground energy of electrons and clamped nuclei with two spin states per
electron: the Ritz energy of the spin-independent full-kernel Hamiltonian on spin-dependent grid
states that are antisymmetric under simultaneous exchange of the grid positions and spins of two
electrons. -/
def IsMolecularSpinFullKernelGroundEnergy (eta : ℕ) (L : ℝ) (data : FiniteBONuclearData ν)
    (m : ℕ) (Ef : ℝ) : Prop :=
  (∀ Φ : GridSpinState eta m, IsGridSpinFermionic Φ →
    Ef * ‖Φ‖ ^ 2 ≤ (inner ℂ Φ (spinHposFull (RegParticles.electrons eta) (posNucleiOf data)
      (coulombCellAmplitude L) (2 * Real.pi / L) Φ)).re) ∧
  ∃ Φ : GridSpinState eta m, IsGridSpinFermionic Φ ∧ ‖Φ‖ = 1 ∧
    (inner ℂ Φ (spinHposFull (RegParticles.electrons eta) (posNucleiOf data)
      (coulombCellAmplitude L) (2 * Real.pi / L) Φ)).re = Ef

lemma isMolecularSpinFullKernelGroundEnergy_iff (eta : ℕ) (L : ℝ)
    (data : FiniteBONuclearData ν) (m : ℕ) (Ef : ℝ) :
    IsMolecularSpinFullKernelGroundEnergy eta L data m Ef ↔
      IsCoulombSpinFullKernelGroundEnergy (CoulombSystem.bo eta data) 2 (fun _ => 2) L m Ef := by
  unfold IsMolecularSpinFullKernelGroundEnergy IsCoulombSpinFullKernelGroundEnergy
  constructor
  · rintro ⟨hLow, Φ, hΦ, hn, hv⟩
    exact ⟨fun Ψ hΨ => hLow Ψ ((isGridSpinFermionic_iff data Ψ).mpr hΨ),
      Φ, (isGridSpinFermionic_iff data Φ).mp hΦ, hn, hv⟩
  · rintro ⟨hLow, Φ, hΦ, hn, hv⟩
    exact ⟨fun Ψ hΨ => hLow Ψ ((isGridSpinFermionic_iff data Ψ).mp hΨ),
      Φ, (isGridSpinFermionic_iff data Φ).mpr hΦ, hn, hv⟩

/-- **`prop:fullkernel`, Born–Oppenheimer case, on the physical electronic space**
`Λ^η(L²(T³) ⊗ ℂ²)`; the improved bound holds if the correlation summability holds in every spin
sector that holds a ground state, of the continuum problem or of the collocation (every spin
pattern is valid here). -/
theorem periodicMolecularFullKernelError (eta : ℕ) (_heta : 0 < eta)
    (data : FiniteBONuclearData ν) (L : ℝ) (hL : 0 < L) :
    ∃ E : ℝ, ∃ Ψ : MolecularSpinL2 eta,
      HasMolecularSpinGroundPair eta L data Ψ E ∧
      |E| ≤ molecularGroundEnergyBudget eta data L ∧
      ∀ m : ℕ, fullKernelThreshold (CoulombSystem.bo eta data) L ≤ m →
        ∃ Ef : ℝ, IsMolecularSpinFullKernelGroundEnergy eta L data m Ef ∧
          |Ef - E| ≤ fullKernelErrorConstant (CoulombSystem.bo eta data) L /
            (((2 * Real.pi / L) * m) * Real.sqrt ((2 * Real.pi / L) * m)) ∧
          |Ef - E| ≤ fullKernelBasisErrorConstant (CoulombSystem.bo eta data) L /
            Real.sqrt (((4 * m + 1) ^ 3 : ℕ) : ℝ) ∧
          ∀ Crho : ℝ, 0 ≤ Crho →
            (∀ σ : Fin eta → Fin 2,
              ((∃ psi, HasMolecularFermionicGroundPair eta
                  ((CoulombSystem.bo eta data).spinSectorLabel σ) L data psi E) ∨
                IsMolecularFermionicFullKernelGroundEnergy eta
                  ((CoulombSystem.bo eta data).spinSectorLabel σ) L data m Ef) →
              FullKernelCorrSummable (CoulombSystem.bo eta data)
                ((CoulombSystem.bo eta data).spinSectorLabel σ) L m Crho) →
            |Ef - E| ≤ (fullKernelImpConstant₁ (CoulombSystem.bo eta data) L +
                fullKernelImpConstant₂ (CoulombSystem.bo eta data) L * Crho) /
              ((2 * Real.pi / L) * m) ^ 2 ∧
            |Ef - E| ≤ 25 * (fullKernelImpConstant₁ (CoulombSystem.bo eta data) L +
                fullKernelImpConstant₂ (CoulombSystem.bo eta data) L * Crho) /
              (2 * Real.pi / L) ^ 2 / (((4 * m + 1) ^ 3 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨E, Ψ, hPair, hBud, hFull⟩ := periodicCoulombFullKernelError (CoulombSystem.bo eta data)
    2 (fun _ => 2) (CoulombSystem.bo_spinDim eta data) L hL
  refine ⟨E, Ψ, (hasCoulombSpinGroundPair_bo eta data L Ψ E).mp hPair, ?_, ?_⟩
  · rwa [coulombGroundEnergyBudget_bo] at hBud
  · intro m hm
    obtain ⟨Ef, hEf, hK, hN, hImp⟩ := hFull m hm
    refine ⟨Ef, (isMolecularSpinFullKernelGroundEnergy_iff eta L data m Ef).mpr hEf, hK, hN,
      fun Crho hC hS => hImp Crho hC fun σ _ hσ => hS σ ?_⟩
    rcases hσ with ⟨psi, hp⟩ | hf
    · exact Or.inl ⟨psi, (hasCoulombSectorGroundPair_bo eta data _ L psi E).mp hp⟩
    · exact Or.inr hf

end BO

end

end PlaneWaveFullKernel

end DevFK6
-- END SOURCE dev/DevFK6.lean

-- BEGIN SOURCE dev/DevFK7.lean
-- SHA256 2072b5d3f20d77179b6ba4b008789d1befc8f71347be05acefaf1c907b14a56f
section DevFK7

/-!
# Full-kernel collocation: polynomial bounds on the constants

The manuscript states `prop:fullkernel` "with constants as in Theorem `thm:grid-energy`", whose
constant is polynomial in the particle data.  Here the constants and the threshold of the
full-kernel theorem are bounded by powers of the single variable

  `Y = (1 + η³) m̄ Q²`   (`fullKernelPolyVar`),

`Q = 1 + Σ_a |q_a| + Z_tot` the charge weight of the certificate, with factors in front that
depend only on the cell side `L` (through `g = 2π/L`, the kernel amplitude `γ_L = 1/(π L)` and
the certificate's cell factors):

* `fullKernelErrorConstant_le_poly`, `fullKernelBasisErrorConstant_le_poly`: `C ≤ c_L Y²⁷`,
  `C' ≤ c'_L Y²⁷`;
* `fullKernelThreshold_le_poly`: the threshold is at most `t_L Y¹²`;
* `fullKernelImpConstant₁_le_poly`, `fullKernelImpConstant₂_le_poly`: `A₁ ≤ a_L Y²⁷`,
  `A₂ ≤ 4 g² γ_L Y`;
* the Born–Oppenheimer case with `m̄ = 1`, `Q = 1 + η + Z_tot` (`…_bo`).

In the same variable the grid files' bounds for `thm:grid-energy` read `C_grid ≤ c_L Y²⁷` and
`T_grid ≤ 2 t'_L Y¹²` (`coulombGridErrorConstant_le_polyVar`,
`coulombGridThreshold_le_polyVar`), so the full-kernel constants have the degrees of the
truncated-kernel ones.  The single variable is coarser than the grid files' separate powers
(`(1 + η³)⁴ m̄²⁷ Q⁴²` for `C_grid`); the degrees are not optimised.  The chain reuses the
grid files' bounds of the core constants (`Ell_le_poly`, `Cform_le_poly`,
`Z_mul_J0g_le_poly`) at `m̄ = Y`, `Q = 1`, and bounds the bootstrap thresholds through
`√(m̄ E_b)` (`bootThr_le`): `T₀ ≤ τ Y²` for the Galerkin ground state and `T₀ ≤ τ Y⁶` for the
full-kernel ground state, whose cube enters the shell sum (`208 T₀³`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace PlaneWaveFullKernel

open PlaneWaveGrid PlaneWaveCertificate

noncomputable section

/-! ## Cell factors

The suffix `G` refers to the Galerkin ground state, `F` to the full-kernel ground state (as
`fkT0g`, `fkT0f` of DevFK4). -/

section Cells

variable (γ g c₀ : ℝ)

/-- Elliptic cell factor of the Galerkin ground state. -/
def fkEllG : ℝ := gridEllCell γ g c₀

/-- Bootstrap-threshold cell factor of the Galerkin ground state. -/
def fkTauG : ℝ := 3 + 2 * Real.sqrt c₀ / g

/-- Shell cell factor of the Galerkin ground state. -/
def fkSigG : ℝ := 208 * fkTauG g c₀ ^ 3 + 1872 * (508 * γ / g ^ 2 * fkEllG γ g c₀)

/-- Energy-budget cell factor of the full-kernel ground state. -/
def fkEpsF : ℝ := 52 * (25 * γ) * gridSplitCell (25 * γ) g + g ^ 2 / 4 + c₀ +
  gridFormCell γ g * fkEllG γ g c₀ ^ 2 + 8 * γ * fkSigG γ g c₀

/-- Elliptic cell factor of the full-kernel ground state. -/
def fkEllF : ℝ := gridEllCell (25 * γ) g (fkEpsF γ g c₀)

/-- Bootstrap-threshold cell factor of the full-kernel ground state. -/
def fkTauF : ℝ := 3 + 2 * Real.sqrt (fkEpsF γ g c₀) / g

/-- Shell cell factor of the full-kernel ground state. -/
def fkSigF : ℝ := 208 * fkTauF γ g c₀ ^ 3 + 1872 * (508 * (25 * γ) / g ^ 2 * fkEllF γ g c₀)

/-- Form cell factor. -/
def fkPhi : ℝ :=
  gridFormCell γ g * fkEllG γ g c₀ ^ 2 + gridFormCell (25 * γ) g * fkEllF γ g c₀ ^ 2

/-- Comparison cell factor. -/
def fkKappa : ℝ := fkPhi γ g c₀ + 2 * γ * (fkSigG γ g c₀ + fkSigF γ g c₀)

variable {γ g c₀}

lemma fkEllG_nonneg (hγ : 0 ≤ γ) (hc : 0 ≤ c₀) : 0 ≤ fkEllG γ g c₀ :=
  gridEllCell_nonneg hγ g hc

lemma fkTauG_nonneg (hg : 0 < g) : 0 ≤ fkTauG g c₀ := by
  unfold fkTauG; positivity

lemma fkSigG_nonneg (hγ : 0 ≤ γ) (hg : 0 < g) (hc : 0 ≤ c₀) : 0 ≤ fkSigG γ g c₀ := by
  unfold fkSigG
  have := fkTauG_nonneg (c₀ := c₀) hg
  have := fkEllG_nonneg (g := g) hγ hc
  positivity

lemma fkEpsF_nonneg (hγ : 0 ≤ γ) (hg : 0 < g) (hc : 0 ≤ c₀) : 0 ≤ fkEpsF γ g c₀ := by
  unfold fkEpsF
  have := gridSplitCell_nonneg (25 * γ) g
  have := gridFormCell_nonneg hγ g
  have := fkEllG_nonneg (g := g) hγ hc
  have := fkSigG_nonneg hγ hg hc
  positivity

lemma fkEllF_nonneg (hγ : 0 ≤ γ) (hg : 0 < g) (hc : 0 ≤ c₀) : 0 ≤ fkEllF γ g c₀ :=
  gridEllCell_nonneg (by positivity) g (fkEpsF_nonneg hγ hg hc)

lemma fkTauF_nonneg (hg : 0 < g) : 0 ≤ fkTauF γ g c₀ := by
  unfold fkTauF; positivity

lemma fkSigF_nonneg (hγ : 0 ≤ γ) (hg : 0 < g) (hc : 0 ≤ c₀) : 0 ≤ fkSigF γ g c₀ := by
  unfold fkSigF
  have := fkTauF_nonneg (γ := γ) (c₀ := c₀) hg
  have := fkEllF_nonneg hγ hg hc
  positivity

lemma fkPhi_nonneg (hγ : 0 ≤ γ) : 0 ≤ fkPhi γ g c₀ := by
  unfold fkPhi
  have := gridFormCell_nonneg hγ g
  have := gridFormCell_nonneg (by positivity : (0 : ℝ) ≤ 25 * γ) g
  positivity

lemma fkKappa_nonneg (hγ : 0 ≤ γ) (hg : 0 < g) (hc : 0 ≤ c₀) : 0 ≤ fkKappa γ g c₀ := by
  unfold fkKappa
  have := fkPhi_nonneg (g := g) (c₀ := c₀) hγ
  have := fkSigG_nonneg hγ hg hc
  have := fkSigF_nonneg hγ hg hc
  positivity

end Cells

/-! ## The chain of bounds -/

section Chain

variable {M Zc0 g Eb γ c₀ Y : ℝ}

/-- The bootstrap threshold is at most `(3 + 2 √c/g) P` when `M e ≤ c P²`, `P ≥ 1`. -/
lemma bootThr_le (hg : 0 < g) {e c P : ℝ} (hc : 0 ≤ c) (hP : 1 ≤ P) (hMe : M * e ≤ c * P ^ 2) :
    (bootThr M g e : ℝ) ≤ (3 + 2 * Real.sqrt c / g) * P := by
  set y : ℝ := 2 * Real.sqrt (M * e) / g with hy
  have hy0 : 0 ≤ y := by positivity
  have hceil : ((Nat.ceil y : ℕ) : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one hy0).le
  have hP0 : 0 ≤ P := by linarith
  have hsq : Real.sqrt (M * e) ≤ Real.sqrt c * P := by
    calc Real.sqrt (M * e) ≤ Real.sqrt (c * P ^ 2) := Real.sqrt_le_sqrt hMe
      _ = Real.sqrt c * P := by rw [Real.sqrt_mul hc, Real.sqrt_sq hP0]
  have hyb : y ≤ 2 * Real.sqrt c / g * P := by
    rw [hy, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hg.le
    linarith
  have hB : (bootThr M g e : ℝ) ≤ 3 + y := by
    unfold bootThr
    rw [Nat.cast_max]
    apply max_le
    · push_cast; linarith
    · linarith
  have h3 : (3 : ℝ) ≤ 3 * P := by linarith
  calc (bootThr M g e : ℝ) ≤ 3 + y := hB
    _ ≤ 3 * P + 2 * Real.sqrt c / g * P := by linarith
    _ = (3 + 2 * Real.sqrt c / g) * P := by ring

lemma yPow_mono (hY : 1 ≤ Y) {a b : ℕ} (hab : a ≤ b) : Y ^ a ≤ Y ^ b :=
  pow_le_pow_right₀ hY hab

/-- **The full-kernel constants are polynomial in `Y`.** If `1 ≤ M ≤ Y`, `M Z_c ≤ γ Y` and
`0 ≤ E_b ≤ c₀ Y²`, then `fkForm ≤ φ Y²⁷`, `fkConst ≤ κ Y²⁷` and the bootstrap threshold of the
full-kernel ground state is at most `τ_F Y⁶`. -/
theorem fk_poly (hg : 0 < g) (hγ : 0 ≤ γ) (hc₀ : 0 ≤ c₀) (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hZ0 : 0 ≤ Zc0) (hZ : M * Zc0 ≤ γ * Y) (hEb0 : 0 ≤ Eb) (hEb : Eb ≤ c₀ * Y ^ 2) :
    fkForm M Zc0 g Eb ≤ fkPhi γ g c₀ * Y ^ 27 ∧
    fkConst M Zc0 g Eb ≤ fkKappa γ g c₀ * Y ^ 27 ∧
    (fkT0f M Zc0 g Eb : ℝ) ≤ fkTauF γ g c₀ * Y ^ 6 := by
  have hY : 1 ≤ Y := hM.trans hMY
  have hY0 : 0 ≤ Y := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hZc : Zc0 ≤ γ * Y := le_trans (le_mul_of_one_le_left hZ0 hM) hZ
  have hQ1 : (1 : ℝ) ≤ 1 := le_rfl
  have hγ25 : 0 ≤ 25 * γ := by positivity
  have hEG := fkEllG_nonneg (g := g) hγ hc₀
  have hTG := fkTauG_nonneg (c₀ := c₀) hg
  have hSG := fkSigG_nonneg hγ hg hc₀
  have hEp := fkEpsF_nonneg hγ hg hc₀
  have hEF := fkEllF_nonneg hγ hg hc₀
  have hTF := fkTauF_nonneg (γ := γ) (c₀ := c₀) hg
  have hSF := fkSigF_nonneg hγ hg hc₀
  -- the couplings
  have hZg0 : 0 ≤ fkZ M Zc0 := fkZ_nonneg hM0 hZ0
  have hZg : fkZ M Zc0 ≤ γ * Y * 1 ^ 2 := by unfold fkZ; rw [one_pow, mul_one]; exact hZ
  have hZf0 : 0 ≤ fkZf M Zc0 := fkZf_nonneg hM0 hZ0
  have hZf : fkZf M Zc0 ≤ 25 * γ * Y * 1 ^ 2 := by
    unfold fkZf; rw [one_pow, mul_one]; linarith
  -- powers of `Y`
  have hL3 : Y ^ 3 * 1 ^ 6 ≤ Y ^ 3 := by rw [one_pow, mul_one]
  have hL2_3 : Y ^ 2 ≤ Y ^ 3 := yPow_mono hY (by norm_num)
  -- the Galerkin ground state
  have hEll1 : Ell (fkZ M Zc0) g Eb ≤ gridEllCell γ g c₀ * Y ^ 3 :=
    Ell_le_poly hg hγ hY hQ1 hZg0 hZg hL3 (hEb.trans (mul_le_mul_of_nonneg_left hL2_3 hc₀))
  have hEll1' : 0 ≤ Ell (fkZ M Zc0) g Eb := Ell_nonneg hZg0 hEb0
  have hXg : fkXg M Zc0 g Eb ≤ fkEllG γ g c₀ * Y ^ 4 := by
    unfold fkXg fkEllG
    calc M * Ell (fkZ M Zc0) g Eb ≤ Y * (gridEllCell γ g c₀ * Y ^ 3) :=
          mul_le_mul hMY hEll1 hEll1' hY0
      _ = gridEllCell γ g c₀ * Y ^ 4 := by ring
  have hXg0 : 0 ≤ fkXg M Zc0 g Eb := fkXg_nonneg hM0 hZ0 hEb0
  have hT0g : (fkT0g M g Eb : ℝ) ≤ fkTauG g c₀ * Y ^ 2 := by
    unfold fkT0g fkTauG
    refine bootThr_le hg hc₀ (one_le_pow₀ hY) ?_
    calc M * Eb ≤ Y * (c₀ * Y ^ 2) := mul_le_mul hMY hEb hEb0 hY0
      _ = c₀ * Y ^ 3 := by ring
      _ ≤ c₀ * Y ^ 4 := mul_le_mul_of_nonneg_left (yPow_mono hY (by norm_num)) hc₀
      _ = c₀ * (Y ^ 2) ^ 2 := by ring
  have hCbg : Cboot (fkZ M Zc0) g ≤ 508 * γ / g ^ 2 * Y := by
    unfold Cboot
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := hZg
    rw [one_pow, mul_one] at this
    linarith
  have hBg : fkBg M Zc0 g Eb ≤ 508 * γ / g ^ 2 * fkEllG γ g c₀ * Y ^ 5 := by
    unfold fkBg
    calc Cboot (fkZ M Zc0) g * fkXg M Zc0 g Eb ≤ (508 * γ / g ^ 2 * Y) * (fkEllG γ g c₀ * Y ^ 4) :=
          mul_le_mul hCbg hXg hXg0 (by positivity)
      _ = 508 * γ / g ^ 2 * fkEllG γ g c₀ * Y ^ 5 := by ring
  have hSg : fkSg M Zc0 g Eb ≤ fkSigG γ g c₀ * Y ^ 6 := by
    unfold fkSg fkSigG
    have h1 : (fkT0g M g Eb : ℝ) ^ 3 ≤ (fkTauG g c₀ * Y ^ 2) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hT0g 3
    have h2 : (fkTauG g c₀ * Y ^ 2) ^ 3 = fkTauG g c₀ ^ 3 * Y ^ 6 := by ring
    have h3 : 508 * γ / g ^ 2 * fkEllG γ g c₀ * Y ^ 5 ≤ 508 * γ / g ^ 2 * fkEllG γ g c₀ * Y ^ 6 :=
      mul_le_mul_of_nonneg_left (yPow_mono hY (by norm_num)) (by positivity)
    linarith
  -- the energy budget of the full-kernel ground state
  have hFg : Cform (fkZ M Zc0) g ≤ gridFormCell γ g * (Y ^ 3 * 1 ^ 6) :=
    Cform_le_poly hg hY hQ1 hZg0 hZg
  have hEbf : fkEbf M Zc0 g Eb ≤ fkEpsF γ g c₀ * Y ^ 11 := by
    unfold fkEbf fkEpsF
    have hJ : fkZf M Zc0 * (J0g (fkZf M Zc0) g : ℝ) ≤
        25 * γ * gridSplitCell (25 * γ) g * (Y ^ 3 * 1 ^ 6) :=
      Z_mul_J0g_le_poly hg hγ25 hY hQ1 hZf0 hZf
    rw [one_pow, mul_one] at hJ hFg
    have hL3_11 : Y ^ 3 ≤ Y ^ 11 := yPow_mono hY (by norm_num)
    have hL2_11 : Y ^ 2 ≤ Y ^ 11 := yPow_mono hY (by norm_num)
    have hL7_11 : Y ^ 7 ≤ Y ^ 11 := yPow_mono hY (by norm_num)
    have hL0_11 : 1 ≤ Y ^ 11 := one_le_pow₀ hY
    have hcJ := gridSplitCell_nonneg (25 * γ) g
    have hcF := gridFormCell_nonneg hγ g
    -- first argument of the maximum
    have hA : 52 * fkZf M Zc0 * (J0g (fkZf M Zc0) g : ℝ) + g ^ 2 / 4 ≤
        (52 * (25 * γ) * gridSplitCell (25 * γ) g + g ^ 2 / 4) * Y ^ 11 := by
      have h1 : 52 * fkZf M Zc0 * (J0g (fkZf M Zc0) g : ℝ) ≤
          52 * (25 * γ * gridSplitCell (25 * γ) g * Y ^ 3) := by linarith
      have h2 : 25 * γ * gridSplitCell (25 * γ) g * Y ^ 3 ≤
          25 * γ * gridSplitCell (25 * γ) g * Y ^ 11 :=
        mul_le_mul_of_nonneg_left hL3_11 (by positivity)
      have h3 : g ^ 2 / 4 ≤ g ^ 2 / 4 * Y ^ 11 := le_mul_of_one_le_right (by positivity) hL0_11
      linarith
    -- second argument of the maximum
    have hB : Eb + Cform (fkZ M Zc0) g * fkXg M Zc0 g Eb ^ 2 + 8 * Zc0 * fkSg M Zc0 g Eb ≤
        (c₀ + gridFormCell γ g * fkEllG γ g c₀ ^ 2 + 8 * γ * fkSigG γ g c₀) * Y ^ 11 := by
      have h1 : Eb ≤ c₀ * Y ^ 11 := hEb.trans (mul_le_mul_of_nonneg_left hL2_11 hc₀)
      have hX2 : fkXg M Zc0 g Eb ^ 2 ≤ (fkEllG γ g c₀ * Y ^ 4) ^ 2 :=
        pow_le_pow_left₀ hXg0 hXg 2
      have h2 : Cform (fkZ M Zc0) g * fkXg M Zc0 g Eb ^ 2 ≤
          gridFormCell γ g * fkEllG γ g c₀ ^ 2 * Y ^ 11 := by
        calc Cform (fkZ M Zc0) g * fkXg M Zc0 g Eb ^ 2
            ≤ (gridFormCell γ g * Y ^ 3) * (fkEllG γ g c₀ * Y ^ 4) ^ 2 :=
              mul_le_mul hFg hX2 (sq_nonneg _) (by positivity)
          _ = gridFormCell γ g * fkEllG γ g c₀ ^ 2 * Y ^ 11 := by ring
      have hSg0 := fkSg_nonneg (g := g) hM0 hZ0 hEb0
      have h3 : 8 * Zc0 * fkSg M Zc0 g Eb ≤ 8 * γ * fkSigG γ g c₀ * Y ^ 11 := by
        calc 8 * Zc0 * fkSg M Zc0 g Eb ≤ 8 * (γ * Y) * (fkSigG γ g c₀ * Y ^ 6) := by
              apply mul_le_mul _ hSg hSg0 (by positivity)
              linarith
          _ = 8 * γ * fkSigG γ g c₀ * Y ^ 7 := by ring
          _ ≤ 8 * γ * fkSigG γ g c₀ * Y ^ 11 :=
              mul_le_mul_of_nonneg_left hL7_11 (by positivity)
      linarith
    have hP11 : (0 : ℝ) ≤ Y ^ 11 := by positivity
    have hB0 : 0 ≤ (c₀ + gridFormCell γ g * fkEllG γ g c₀ ^ 2 + 8 * γ * fkSigG γ g c₀) * Y ^ 11 :=
      mul_nonneg (by positivity) hP11
    have hA0 : 0 ≤ (52 * (25 * γ) * gridSplitCell (25 * γ) g + g ^ 2 / 4) * Y ^ 11 :=
      mul_nonneg (by positivity) hP11
    apply max_le
    · linarith
    · linarith
  have hEbf0 : 0 ≤ fkEbf M Zc0 g Eb := fkEbf_nonneg hM0 hZ0 hEb0
  -- the full-kernel ground state
  have hL3_11 : Y ^ 3 * 1 ^ 6 ≤ Y ^ 11 := by
    rw [one_pow, mul_one]; exact yPow_mono hY (by norm_num)
  have hEll2 : Ell (fkZf M Zc0) g (fkEbf M Zc0 g Eb) ≤
      gridEllCell (25 * γ) g (fkEpsF γ g c₀) * Y ^ 11 :=
    Ell_le_poly hg hγ25 hY hQ1 hZf0 hZf hL3_11 hEbf
  have hEll2' : 0 ≤ Ell (fkZf M Zc0) g (fkEbf M Zc0 g Eb) := Ell_nonneg hZf0 hEbf0
  have hXf : fkXf M Zc0 g Eb ≤ fkEllF γ g c₀ * Y ^ 12 := by
    unfold fkXf fkEllF
    calc M * Ell (fkZf M Zc0) g (fkEbf M Zc0 g Eb)
        ≤ Y * (gridEllCell (25 * γ) g (fkEpsF γ g c₀) * Y ^ 11) :=
          mul_le_mul hMY hEll2 hEll2' hY0
      _ = gridEllCell (25 * γ) g (fkEpsF γ g c₀) * Y ^ 12 := by ring
  have hXf0 : 0 ≤ fkXf M Zc0 g Eb := fkXf_nonneg hM0 hZ0 hEb0
  have hT0f : (fkT0f M Zc0 g Eb : ℝ) ≤ fkTauF γ g c₀ * Y ^ 6 := by
    unfold fkT0f fkTauF
    refine bootThr_le hg hEp (one_le_pow₀ hY) ?_
    calc M * fkEbf M Zc0 g Eb ≤ Y * (fkEpsF γ g c₀ * Y ^ 11) :=
          mul_le_mul hMY hEbf hEbf0 hY0
      _ = fkEpsF γ g c₀ * (Y ^ 6) ^ 2 := by ring
  have hCbf : Cboot (fkZf M Zc0) g ≤ 508 * (25 * γ) / g ^ 2 * Y := by
    unfold Cboot
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := hZf
    rw [one_pow, mul_one] at this
    linarith
  have hBf : fkBf M Zc0 g Eb ≤ 508 * (25 * γ) / g ^ 2 * fkEllF γ g c₀ * Y ^ 13 := by
    unfold fkBf
    calc Cboot (fkZf M Zc0) g * fkXf M Zc0 g Eb
        ≤ (508 * (25 * γ) / g ^ 2 * Y) * (fkEllF γ g c₀ * Y ^ 12) :=
          mul_le_mul hCbf hXf hXf0 (by positivity)
      _ = 508 * (25 * γ) / g ^ 2 * fkEllF γ g c₀ * Y ^ 13 := by ring
  have hSf : fkSf M Zc0 g Eb ≤ fkSigF γ g c₀ * Y ^ 18 := by
    unfold fkSf fkSigF
    have h1 : (fkT0f M Zc0 g Eb : ℝ) ^ 3 ≤ (fkTauF γ g c₀ * Y ^ 6) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hT0f 3
    have h2 : (fkTauF γ g c₀ * Y ^ 6) ^ 3 = fkTauF γ g c₀ ^ 3 * Y ^ 18 := by ring
    have h3 : 508 * (25 * γ) / g ^ 2 * fkEllF γ g c₀ * Y ^ 13 ≤
        508 * (25 * γ) / g ^ 2 * fkEllF γ g c₀ * Y ^ 18 :=
      mul_le_mul_of_nonneg_left (yPow_mono hY (by norm_num)) (by positivity)
    have := hBf
    linarith
  -- the form constant
  have hForm : fkForm M Zc0 g Eb ≤ fkPhi γ g c₀ * Y ^ 27 := by
    unfold fkForm fkPhi
    have hFf : Cform (fkZf M Zc0) g ≤ gridFormCell (25 * γ) g * (Y ^ 3 * 1 ^ 6) :=
      Cform_le_poly hg hY hQ1 hZf0 hZf
    rw [one_pow, mul_one] at hFg hFf
    have hX2g : fkXg M Zc0 g Eb ^ 2 ≤ (fkEllG γ g c₀ * Y ^ 4) ^ 2 := pow_le_pow_left₀ hXg0 hXg 2
    have hX2f : fkXf M Zc0 g Eb ^ 2 ≤ (fkEllF γ g c₀ * Y ^ 12) ^ 2 :=
      pow_le_pow_left₀ hXf0 hXf 2
    have hcF := gridFormCell_nonneg hγ g
    have hcF' := gridFormCell_nonneg hγ25 g
    have h1 : Cform (fkZ M Zc0) g * fkXg M Zc0 g Eb ^ 2 ≤
        gridFormCell γ g * fkEllG γ g c₀ ^ 2 * Y ^ 27 := by
      calc Cform (fkZ M Zc0) g * fkXg M Zc0 g Eb ^ 2
          ≤ (gridFormCell γ g * Y ^ 3) * (fkEllG γ g c₀ * Y ^ 4) ^ 2 :=
            mul_le_mul hFg hX2g (sq_nonneg _) (by positivity)
        _ = gridFormCell γ g * fkEllG γ g c₀ ^ 2 * Y ^ 11 := by ring
        _ ≤ gridFormCell γ g * fkEllG γ g c₀ ^ 2 * Y ^ 27 :=
            mul_le_mul_of_nonneg_left (yPow_mono hY (by norm_num)) (by positivity)
    have h2 : Cform (fkZf M Zc0) g * fkXf M Zc0 g Eb ^ 2 ≤
        gridFormCell (25 * γ) g * fkEllF γ g c₀ ^ 2 * Y ^ 27 := by
      calc Cform (fkZf M Zc0) g * fkXf M Zc0 g Eb ^ 2
          ≤ (gridFormCell (25 * γ) g * Y ^ 3) * (fkEllF γ g c₀ * Y ^ 12) ^ 2 :=
            mul_le_mul hFf hX2f (sq_nonneg _) (by positivity)
        _ = gridFormCell (25 * γ) g * fkEllF γ g c₀ ^ 2 * Y ^ 27 := by ring
    linarith
  refine ⟨hForm, ?_, hT0f⟩
  -- the comparison constant
  unfold fkConst fkKappa
  have hSg0 := fkSg_nonneg (g := g) hM0 hZ0 hEb0
  have hSf0 := fkSf_nonneg (g := g) hM0 hZ0 hEb0
  have h2 : 2 * Zc0 * (fkSg M Zc0 g Eb + fkSf M Zc0 g Eb) ≤
      2 * γ * (fkSigG γ g c₀ + fkSigF γ g c₀) * Y ^ 27 := by
    have hS : fkSg M Zc0 g Eb + fkSf M Zc0 g Eb ≤ (fkSigG γ g c₀ + fkSigF γ g c₀) * Y ^ 26 := by
      have h6 : fkSigG γ g c₀ * Y ^ 6 ≤ fkSigG γ g c₀ * Y ^ 26 :=
        mul_le_mul_of_nonneg_left (yPow_mono hY (by norm_num)) hSG
      have h18 : fkSigF γ g c₀ * Y ^ 18 ≤ fkSigF γ g c₀ * Y ^ 26 :=
        mul_le_mul_of_nonneg_left (yPow_mono hY (by norm_num)) hSF
      linarith
    calc 2 * Zc0 * (fkSg M Zc0 g Eb + fkSf M Zc0 g Eb)
        ≤ 2 * (γ * Y) * ((fkSigG γ g c₀ + fkSigF γ g c₀) * Y ^ 26) := by
          apply mul_le_mul _ hS (by positivity) (by positivity)
          linarith
      _ = 2 * γ * (fkSigG γ g c₀ + fkSigF γ g c₀) * Y ^ 27 := by ring
  linarith

end Chain

/-! ## Coulomb systems -/

section Coulomb

variable {eta : ℕ} {ν : Type*} [Fintype ν]

/-- The polynomial variable `Y = (1 + η³) m̄ Q²` of a Coulomb system. -/
def fullKernelPolyVar (sys : CoulombSystem eta ν) : ℝ :=
  (1 + (eta : ℝ) ^ 3) * sys.maxMass * sys.chargeWeight ^ 2

/-- The cell factor of the full-kernel error constant (it depends only on `L`). -/
def fullKernelCellFactor (L : ℝ) : ℝ :=
  fkKappa (coulombCellAmplitude L) (2 * Real.pi / L) (2 * (1 + coulombBudgetCellFactor L)) *
      ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L)) +
    32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 /
      (8 * ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L)))

/-- The cell factor of the full-kernel threshold. -/
def fullKernelThresholdCellFactor (L : ℝ) : ℝ :=
  2 * coulombGridThresholdCellFactor L +
    fkTauF (coulombCellAmplitude L) (2 * Real.pi / L) (2 * (1 + coulombBudgetCellFactor L))

/-- The cell factor of the constant `A₁` of the improved bound. -/
def fullKernelImpCellFactor₁ (L : ℝ) : ℝ :=
  (2 * Real.pi / L) ^ 2 *
      fkPhi (coulombCellAmplitude L) (2 * Real.pi / L) (2 * (1 + coulombBudgetCellFactor L)) +
    32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 / (8 * (2 * Real.pi / L))

lemma one_le_fullKernelPolyVar (sys : CoulombSystem eta ν) : 1 ≤ fullKernelPolyVar sys := by
  have hM := sys.one_le_maxMass
  have hQ := sys.one_le_chargeWeight
  have hx : 1 ≤ 1 + (eta : ℝ) ^ 3 := by
    have : (0 : ℝ) ≤ (eta : ℝ) ^ 3 := by positivity
    linarith
  unfold fullKernelPolyVar
  have hQ2 : 1 ≤ sys.chargeWeight ^ 2 := one_le_pow₀ hQ
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ (1 + (eta : ℝ) ^ 3) * sys.maxMass * sys.chargeWeight ^ 2 := by gcongr

/-- The hypotheses of `fk_poly` for a Coulomb system (and `Z_c ≤ γ_L Y`). -/
lemma fk_poly_hyps (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    sys.maxMass ≤ fullKernelPolyVar sys ∧
    sys.maxMass * fullKernelZc sys L ≤ coulombCellAmplitude L * fullKernelPolyVar sys ∧
    fullKernelZc sys L ≤ coulombCellAmplitude L * fullKernelPolyVar sys ∧
    coulombGridEnergyBudget sys L ≤
      2 * (1 + coulombBudgetCellFactor L) * fullKernelPolyVar sys ^ 2 := by
  have hM := sys.one_le_maxMass
  have hQ := sys.one_le_chargeWeight
  have hγ := (coulombCellAmplitude_pos hL).le
  have hx : 1 ≤ 1 + (eta : ℝ) ^ 3 := by
    have : (0 : ℝ) ≤ (eta : ℝ) ^ 3 := by positivity
    linarith
  have hQ2 : 1 ≤ sys.chargeWeight ^ 2 := one_le_pow₀ hQ
  have hZc : fullKernelZc sys L ≤ coulombCellAmplitude L * sys.chargeWeight ^ 2 := by
    unfold fullKernelZc
    rw [Zc_regParticlesOf]
    exact mul_le_mul_of_nonneg_left sys.couplingWeight_le hγ
  have hMQ : sys.maxMass * sys.chargeWeight ^ 2 ≤ fullKernelPolyVar sys := by
    unfold fullKernelPolyVar
    calc sys.maxMass * sys.chargeWeight ^ 2 = 1 * sys.maxMass * sys.chargeWeight ^ 2 := by ring
      _ ≤ (1 + (eta : ℝ) ^ 3) * sys.maxMass * sys.chargeWeight ^ 2 := by gcongr
  have hQ2L : sys.chargeWeight ^ 2 ≤ fullKernelPolyVar sys :=
    le_trans (le_mul_of_one_le_left (by positivity) hM) hMQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (le_mul_of_one_le_right (by linarith) hQ2).trans hMQ
  · calc sys.maxMass * fullKernelZc sys L
        ≤ sys.maxMass * (coulombCellAmplitude L * sys.chargeWeight ^ 2) :=
          mul_le_mul_of_nonneg_left hZc (by linarith)
      _ = coulombCellAmplitude L * (sys.maxMass * sys.chargeWeight ^ 2) := by ring
      _ ≤ coulombCellAmplitude L * fullKernelPolyVar sys := mul_le_mul_of_nonneg_left hMQ hγ
  · exact hZc.trans (mul_le_mul_of_nonneg_left hQ2L hγ)
  · have h1 := coulombGridEnergyBudget_le sys L hL
    have hG := coulombBudgetCellFactor_nonneg L
    have h2 : (1 + (eta : ℝ) ^ 3) * sys.maxMass * sys.chargeWeight ^ 4 ≤
        fullKernelPolyVar sys ^ 2 := by
      unfold fullKernelPolyVar
      have h3 : (1 + (eta : ℝ) ^ 3) ≤ (1 + (eta : ℝ) ^ 3) ^ 2 := le_self_pow₀ hx (by norm_num)
      have h4 : sys.maxMass ≤ sys.maxMass ^ 2 := le_self_pow₀ hM (by norm_num)
      calc (1 + (eta : ℝ) ^ 3) * sys.maxMass * sys.chargeWeight ^ 4
          ≤ (1 + (eta : ℝ) ^ 3) ^ 2 * sys.maxMass ^ 2 * sys.chargeWeight ^ 4 := by gcongr
        _ = ((1 + (eta : ℝ) ^ 3) * sys.maxMass * sys.chargeWeight ^ 2) ^ 2 := by ring
    calc coulombGridEnergyBudget sys L
        ≤ 2 * (1 + coulombBudgetCellFactor L) *
          ((1 + (eta : ℝ) ^ 3) * sys.maxMass * sys.chargeWeight ^ 4) := h1
      _ ≤ 2 * (1 + coulombBudgetCellFactor L) * fullKernelPolyVar sys ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The cubic cutoff constant is at most `32 F_L (1 + G_L)³ Y¹³`. -/
lemma coulombDataCubicErrorConstant_le_polyVar (sys : CoulombSystem eta ν) (L : ℝ)
    (hL : 0 < L) :
    coulombDataCubicErrorConstant sys L ≤
      32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 *
        fullKernelPolyVar sys ^ 13 := by
  have h := coulombDataCubicErrorConstant_le_coarse sys L hL
  have hM := sys.one_le_maxMass
  have hQ := sys.one_le_chargeWeight
  have hF := coulombPolyCellFactor_nonneg L
  have hG := coulombBudgetCellFactor_nonneg L
  have hx : 1 ≤ 1 + (eta : ℝ) ^ 3 := by
    have : (0 : ℝ) ≤ (eta : ℝ) ^ 3 := by positivity
    linarith
  have hη2 := sq_le_one_add_cube eta
  refine h.trans ?_
  have hmon : (eta : ℝ) ^ 2 * sys.maxMass ^ 10 * sys.chargeWeight ^ 26 * (1 + (eta : ℝ) ^ 3) ^ 3 ≤
      fullKernelPolyVar sys ^ 13 := by
    unfold fullKernelPolyVar
    have h1 : (1 + (eta : ℝ) ^ 3) * (1 + (eta : ℝ) ^ 3) ^ 3 ≤ (1 + (eta : ℝ) ^ 3) ^ 13 := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ hx (by norm_num)
    have h2 : sys.maxMass ^ 10 ≤ sys.maxMass ^ 13 := pow_le_pow_right₀ hM (by norm_num)
    calc (eta : ℝ) ^ 2 * sys.maxMass ^ 10 * sys.chargeWeight ^ 26 * (1 + (eta : ℝ) ^ 3) ^ 3
        ≤ (1 + (eta : ℝ) ^ 3) * sys.maxMass ^ 13 * sys.chargeWeight ^ 26 *
            (1 + (eta : ℝ) ^ 3) ^ 3 := by gcongr
      _ = ((1 + (eta : ℝ) ^ 3) * (1 + (eta : ℝ) ^ 3) ^ 3) * sys.maxMass ^ 13 *
            sys.chargeWeight ^ 26 := by ring
      _ ≤ (1 + (eta : ℝ) ^ 3) ^ 13 * sys.maxMass ^ 13 * sys.chargeWeight ^ 26 := by gcongr
      _ = ((1 + (eta : ℝ) ^ 3) * sys.maxMass * sys.chargeWeight ^ 2) ^ 13 := by ring
  calc 32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 * (eta : ℝ) ^ 2 *
        sys.maxMass ^ 10 * sys.chargeWeight ^ 26 * (1 + (eta : ℝ) ^ 3) ^ 3
      = 32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 *
          ((eta : ℝ) ^ 2 * sys.maxMass ^ 10 * sys.chargeWeight ^ 26 *
            (1 + (eta : ℝ) ^ 3) ^ 3) := by ring
    _ ≤ 32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 *
          fullKernelPolyVar sys ^ 13 :=
        mul_le_mul_of_nonneg_left hmon (by positivity)

/-! ### Comparison with the grid files' bounds for `thm:grid-energy` -/

lemma coulombGridCellFactor_nonneg (L : ℝ) (hL : 0 < L) : 0 ≤ coulombGridCellFactor L := by
  have hγ := (coulombCellAmplitude_pos hL).le
  have := gridFormCell_nonneg hγ (2 * Real.pi / L)
  have := coulombPolyCellFactor_nonneg L
  have := coulombBudgetCellFactor_nonneg L
  unfold coulombGridCellFactor
  positivity

/-- The grid files' error constant of `thm:grid-energy` in the variable `Y`:
`C_grid ≤ c_L Y²⁷` (from `coulombGridErrorConstant_le_poly`). -/
theorem coulombGridErrorConstant_le_polyVar (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    coulombGridErrorConstant sys L ≤ coulombGridCellFactor L * fullKernelPolyVar sys ^ 27 := by
  have h := coulombGridErrorConstant_le_poly sys L hL
  have hc := coulombGridCellFactor_nonneg L hL
  have hM := sys.one_le_maxMass
  have hQ := sys.one_le_chargeWeight
  have hx : 1 ≤ 1 + (eta : ℝ) ^ 3 := by
    have : (0 : ℝ) ≤ (eta : ℝ) ^ 3 := by positivity
    linarith
  refine h.trans ?_
  have h1 : (1 + (eta : ℝ) ^ 3) ^ 4 ≤ (1 + (eta : ℝ) ^ 3) ^ 27 :=
    pow_le_pow_right₀ hx (by norm_num)
  have h2 : sys.chargeWeight ^ 42 ≤ sys.chargeWeight ^ 54 := pow_le_pow_right₀ hQ (by norm_num)
  calc coulombGridCellFactor L * (1 + (eta : ℝ) ^ 3) ^ 4 * sys.maxMass ^ 27 *
        sys.chargeWeight ^ 42
      ≤ coulombGridCellFactor L * (1 + (eta : ℝ) ^ 3) ^ 27 * sys.maxMass ^ 27 *
        sys.chargeWeight ^ 54 := by gcongr
    _ = coulombGridCellFactor L * fullKernelPolyVar sys ^ 27 := by
        unfold fullKernelPolyVar; ring

/-- The grid files' threshold of `thm:grid-energy` in the variable `Y`:
`T_grid ≤ 2 t'_L Y¹²` (from `coulombGridThreshold_le_poly`). -/
theorem coulombGridThreshold_le_polyVar (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    (coulombGridThreshold sys L : ℝ) ≤
      2 * coulombGridThresholdCellFactor L * fullKernelPolyVar sys ^ 12 := by
  have hGT := coulombGridThreshold_le_poly sys L hL
  have hM := sys.one_le_maxMass
  have hQ := sys.one_le_chargeWeight
  have hx : 1 ≤ 1 + (eta : ℝ) ^ 3 := by
    have : (0 : ℝ) ≤ (eta : ℝ) ^ 3 := by positivity
    linarith
  have hη : 1 + (eta : ℝ) ≤ 2 * (1 + (eta : ℝ) ^ 3) := by
    have := sq_le_one_add_cube eta
    have hη0 : (0 : ℝ) ≤ eta := Nat.cast_nonneg eta
    have h3 : (0 : ℝ) ≤ (eta : ℝ) ^ 3 := by positivity
    linarith [sq_nonneg ((eta : ℝ) - 1)]
  have hT0 : 0 ≤ coulombGridThresholdCellFactor L := by
    have := (Nat.cast_nonneg (coulombGridThreshold sys L) : (0 : ℝ) ≤ _).trans hGT
    by_contra hneg
    push Not at hneg
    have hpos : 0 < (1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 * sys.maxMass ^ 8 *
        sys.chargeWeight ^ 20 := by positivity
    have : coulombGridThresholdCellFactor L * (1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 *
        sys.maxMass ^ 8 * sys.chargeWeight ^ 20 < 0 := by
      have e : coulombGridThresholdCellFactor L * (1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 *
          sys.maxMass ^ 8 * sys.chargeWeight ^ 20 = coulombGridThresholdCellFactor L *
          ((1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 * sys.maxMass ^ 8 *
            sys.chargeWeight ^ 20) := by ring
      rw [e]
      exact mul_neg_of_neg_of_pos hneg hpos
    linarith
  have hmon : (1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 * sys.maxMass ^ 8 *
      sys.chargeWeight ^ 20 ≤ 2 * fullKernelPolyVar sys ^ 12 := by
    unfold fullKernelPolyVar
    have h5 : (1 + (eta : ℝ) ^ 3) ^ 3 ≤ (1 + (eta : ℝ) ^ 3) ^ 12 :=
      pow_le_pow_right₀ hx (by norm_num)
    have h6 : sys.maxMass ^ 8 ≤ sys.maxMass ^ 12 := pow_le_pow_right₀ hM (by norm_num)
    have h7 : sys.chargeWeight ^ 20 ≤ sys.chargeWeight ^ 24 :=
      pow_le_pow_right₀ hQ (by norm_num)
    calc (1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 * sys.maxMass ^ 8 * sys.chargeWeight ^ 20
        ≤ (2 * (1 + (eta : ℝ) ^ 3)) * (1 + (eta : ℝ) ^ 3) ^ 2 * sys.maxMass ^ 12 *
            sys.chargeWeight ^ 24 := by gcongr
      _ = 2 * ((1 + (eta : ℝ) ^ 3) ^ 3 * sys.maxMass ^ 12 * sys.chargeWeight ^ 24) := by ring
      _ ≤ 2 * ((1 + (eta : ℝ) ^ 3) ^ 12 * sys.maxMass ^ 12 * sys.chargeWeight ^ 24) := by
          gcongr
      _ = 2 * ((1 + (eta : ℝ) ^ 3) * sys.maxMass * sys.chargeWeight ^ 2) ^ 12 := by ring
  calc (coulombGridThreshold sys L : ℝ)
      ≤ coulombGridThresholdCellFactor L * (1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 *
        sys.maxMass ^ 8 * sys.chargeWeight ^ 20 := hGT
    _ = coulombGridThresholdCellFactor L * ((1 + (eta : ℝ)) * (1 + (eta : ℝ) ^ 3) ^ 2 *
        sys.maxMass ^ 8 * sys.chargeWeight ^ 20) := by ring
    _ ≤ coulombGridThresholdCellFactor L * (2 * fullKernelPolyVar sys ^ 12) :=
        mul_le_mul_of_nonneg_left hmon hT0
    _ = 2 * coulombGridThresholdCellFactor L * fullKernelPolyVar sys ^ 12 := by ring

/-! ### The full-kernel constants -/

/-- **The error constant of the full-kernel theorem is polynomial**:
`C ≤ c_L ((1 + η³) m̄ Q²)²⁷`. -/
theorem fullKernelErrorConstant_le_poly (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    fullKernelErrorConstant sys L ≤ fullKernelCellFactor L * fullKernelPolyVar sys ^ 27 := by
  obtain ⟨h1, h2, -, h4⟩ := fk_poly_hyps sys L hL
  have hg : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have hγ := (coulombCellAmplitude_pos hL).le
  have hG := coulombBudgetCellFactor_nonneg L
  have hF := coulombPolyCellFactor_nonneg L
  have hZ0 : 0 ≤ fullKernelZc sys L := Zc_nonneg hγ
  have hP := (fk_poly hg hγ (by positivity : (0 : ℝ) ≤ 2 * (1 + coulombBudgetCellFactor L))
    sys.one_le_maxMass h1 hZ0 h2 (coulombGridEnergyBudget_nonneg sys L) h4).2.1
  have hC := coulombDataCubicErrorConstant_le_polyVar sys L hL
  have hY := one_le_fullKernelPolyVar sys
  have hgs : 0 < (2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L) := by
    have := Real.sqrt_pos.mpr hg
    positivity
  have h13 : fullKernelPolyVar sys ^ 13 ≤ fullKernelPolyVar sys ^ 27 :=
    pow_le_pow_right₀ hY (by norm_num)
  have hc0 : 0 ≤ 32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 := by
    positivity
  unfold fullKernelErrorConstant fullKernelCellFactor
  have hA : fkConst sys.maxMass (fullKernelZc sys L) (2 * Real.pi / L)
      (coulombGridEnergyBudget sys L) * ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L)) ≤
      fkKappa (coulombCellAmplitude L) (2 * Real.pi / L) (2 * (1 + coulombBudgetCellFactor L)) *
        fullKernelPolyVar sys ^ 27 * ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L)) :=
    mul_le_mul_of_nonneg_right hP hgs.le
  have hB : coulombDataCubicErrorConstant sys L /
      (8 * ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L))) ≤
      32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 /
        (8 * ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L))) * fullKernelPolyVar sys ^ 27 := by
    calc coulombDataCubicErrorConstant sys L /
          (8 * ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L)))
        ≤ 32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 *
            fullKernelPolyVar sys ^ 27 /
          (8 * ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L))) :=
          div_le_div_of_nonneg_right (hC.trans (mul_le_mul_of_nonneg_left h13 hc0))
            (by positivity)
      _ = _ := by ring
  linarith

/-- The basis-size error constant: `C' ≤ (√125/(g √g)) c_L Y²⁷`. -/
theorem fullKernelBasisErrorConstant_le_poly (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    fullKernelBasisErrorConstant sys L ≤
      Real.sqrt 125 * fullKernelCellFactor L /
        ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L)) * fullKernelPolyVar sys ^ 27 := by
  have hg : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have hgs : 0 < (2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L) := by
    have := Real.sqrt_pos.mpr hg
    positivity
  have h := fullKernelErrorConstant_le_poly sys L hL
  unfold fullKernelBasisErrorConstant
  calc Real.sqrt 125 * fullKernelErrorConstant sys L /
        ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L))
      ≤ Real.sqrt 125 * (fullKernelCellFactor L * fullKernelPolyVar sys ^ 27) /
        ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L)) := by gcongr
    _ = _ := by ring

/-- **The threshold of the full-kernel theorem is polynomial**:
`T ≤ t_L ((1 + η³) m̄ Q²)¹²`. -/
theorem fullKernelThreshold_le_poly (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    (fullKernelThreshold sys L : ℝ) ≤
      fullKernelThresholdCellFactor L * fullKernelPolyVar sys ^ 12 := by
  obtain ⟨h1, h2, -, h4⟩ := fk_poly_hyps sys L hL
  have hg : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have hγ := (coulombCellAmplitude_pos hL).le
  have hG := coulombBudgetCellFactor_nonneg L
  have hZ0 : 0 ≤ fullKernelZc sys L := Zc_nonneg hγ
  have hc₀ : (0 : ℝ) ≤ 2 * (1 + coulombBudgetCellFactor L) := by positivity
  have hT := (fk_poly hg hγ hc₀ sys.one_le_maxMass h1 hZ0 h2
    (coulombGridEnergyBudget_nonneg sys L) h4).2.2
  have hGT' := coulombGridThreshold_le_polyVar sys L hL
  have hY := one_le_fullKernelPolyVar sys
  have hτ := fkTauF_nonneg (γ := coulombCellAmplitude L)
    (c₀ := 2 * (1 + coulombBudgetCellFactor L)) hg
  have hT6 : fkTauF (coulombCellAmplitude L) (2 * Real.pi / L)
      (2 * (1 + coulombBudgetCellFactor L)) * fullKernelPolyVar sys ^ 6 ≤
      fkTauF (coulombCellAmplitude L) (2 * Real.pi / L)
        (2 * (1 + coulombBudgetCellFactor L)) * fullKernelPolyVar sys ^ 12 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY (by norm_num)) hτ
  have hT2 : 0 ≤ fkTauF (coulombCellAmplitude L) (2 * Real.pi / L)
      (2 * (1 + coulombBudgetCellFactor L)) * fullKernelPolyVar sys ^ 12 := by
    have : (0 : ℝ) ≤ fullKernelPolyVar sys := by linarith
    positivity
  have hGT0 : 0 ≤ 2 * coulombGridThresholdCellFactor L * fullKernelPolyVar sys ^ 12 :=
    (Nat.cast_nonneg _).trans hGT'
  unfold fullKernelThreshold fullKernelThresholdCellFactor
  rw [Nat.cast_max]
  apply max_le
  · linarith
  · linarith

/-- **The constant `A₁` of the improved bound is polynomial**: `A₁ ≤ a_L ((1 + η³) m̄ Q²)²⁷`. -/
theorem fullKernelImpConstant₁_le_poly (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    fullKernelImpConstant₁ sys L ≤ fullKernelImpCellFactor₁ L * fullKernelPolyVar sys ^ 27 := by
  obtain ⟨h1, h2, -, h4⟩ := fk_poly_hyps sys L hL
  have hg : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have hγ := (coulombCellAmplitude_pos hL).le
  have hG := coulombBudgetCellFactor_nonneg L
  have hF := coulombPolyCellFactor_nonneg L
  have hZ0 : 0 ≤ fullKernelZc sys L := Zc_nonneg hγ
  have hP := (fk_poly hg hγ (by positivity : (0 : ℝ) ≤ 2 * (1 + coulombBudgetCellFactor L))
    sys.one_le_maxMass h1 hZ0 h2 (coulombGridEnergyBudget_nonneg sys L) h4).1
  have hC := coulombDataCubicErrorConstant_le_polyVar sys L hL
  have hY := one_le_fullKernelPolyVar sys
  have h13 : fullKernelPolyVar sys ^ 13 ≤ fullKernelPolyVar sys ^ 27 :=
    pow_le_pow_right₀ hY (by norm_num)
  have hc0 : 0 ≤ 32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 := by
    positivity
  unfold fullKernelImpConstant₁ fullKernelImpCellFactor₁
  have hA : (2 * Real.pi / L) ^ 2 * fkForm sys.maxMass (fullKernelZc sys L) (2 * Real.pi / L)
      (coulombGridEnergyBudget sys L) ≤ (2 * Real.pi / L) ^ 2 *
        (fkPhi (coulombCellAmplitude L) (2 * Real.pi / L) (2 * (1 + coulombBudgetCellFactor L)) *
          fullKernelPolyVar sys ^ 27) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have hB : coulombDataCubicErrorConstant sys L / (8 * (2 * Real.pi / L)) ≤
      32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 /
        (8 * (2 * Real.pi / L)) * fullKernelPolyVar sys ^ 27 := by
    calc coulombDataCubicErrorConstant sys L / (8 * (2 * Real.pi / L))
        ≤ 32 * coulombPolyCellFactor L * (1 + coulombBudgetCellFactor L) ^ 3 *
            fullKernelPolyVar sys ^ 27 / (8 * (2 * Real.pi / L)) :=
          div_le_div_of_nonneg_right (hC.trans (mul_le_mul_of_nonneg_left h13 hc0))
            (by positivity)
      _ = _ := by ring
  linarith

/-- **The constant `A₂` of the improved bound is polynomial**: `A₂ ≤ 4 g² γ_L Y`. -/
theorem fullKernelImpConstant₂_le_poly (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    fullKernelImpConstant₂ sys L ≤
      4 * (2 * Real.pi / L) ^ 2 * coulombCellAmplitude L * fullKernelPolyVar sys := by
  obtain ⟨-, -, h3, -⟩ := fk_poly_hyps sys L hL
  unfold fullKernelImpConstant₂
  have : 0 ≤ 4 * (2 * Real.pi / L) ^ 2 := by positivity
  calc 4 * (2 * Real.pi / L) ^ 2 * fullKernelZc sys L
      ≤ 4 * (2 * Real.pi / L) ^ 2 * (coulombCellAmplitude L * fullKernelPolyVar sys) :=
        mul_le_mul_of_nonneg_left h3 this
    _ = 4 * (2 * Real.pi / L) ^ 2 * coulombCellAmplitude L * fullKernelPolyVar sys := by ring

/-! ### The Born–Oppenheimer case -/

/-- `Y` for electrons and clamped nuclei: `(1 + η³)(1 + η + Z_tot)²`. -/
lemma fullKernelPolyVar_bo (eta : ℕ) (data : FiniteBONuclearData ν) :
    fullKernelPolyVar (CoulombSystem.bo eta data) =
      (1 + (eta : ℝ) ^ 3) * (1 + eta + data.totalCharge) ^ 2 := by
  unfold fullKernelPolyVar
  rw [CoulombSystem.maxMass_bo, CoulombSystem.chargeWeight_bo, mul_one]

/-- The Born–Oppenheimer error constant: `C ≤ c_L ((1 + η³)(1 + η + Z_tot)²)²⁷`. -/
theorem fullKernelErrorConstant_le_poly_bo (eta : ℕ) (data : FiniteBONuclearData ν) (L : ℝ)
    (hL : 0 < L) :
    fullKernelErrorConstant (CoulombSystem.bo eta data) L ≤
      fullKernelCellFactor L * ((1 + (eta : ℝ) ^ 3) * (1 + eta + data.totalCharge) ^ 2) ^ 27 := by
  rw [← fullKernelPolyVar_bo]
  exact fullKernelErrorConstant_le_poly _ L hL

/-- The Born–Oppenheimer basis-size error constant:
`C' ≤ (√125/(g √g)) c_L ((1 + η³)(1 + η + Z_tot)²)²⁷`. -/
theorem fullKernelBasisErrorConstant_le_poly_bo (eta : ℕ) (data : FiniteBONuclearData ν)
    (L : ℝ) (hL : 0 < L) :
    fullKernelBasisErrorConstant (CoulombSystem.bo eta data) L ≤
      Real.sqrt 125 * fullKernelCellFactor L /
        ((2 * Real.pi / L) * Real.sqrt (2 * Real.pi / L)) *
        ((1 + (eta : ℝ) ^ 3) * (1 + eta + data.totalCharge) ^ 2) ^ 27 := by
  rw [← fullKernelPolyVar_bo]
  exact fullKernelBasisErrorConstant_le_poly _ L hL

/-- The Born–Oppenheimer threshold: `T ≤ t_L ((1 + η³)(1 + η + Z_tot)²)¹²`. -/
theorem fullKernelThreshold_le_poly_bo (eta : ℕ) (data : FiniteBONuclearData ν) (L : ℝ)
    (hL : 0 < L) :
    (fullKernelThreshold (CoulombSystem.bo eta data) L : ℝ) ≤
      fullKernelThresholdCellFactor L *
        ((1 + (eta : ℝ) ^ 3) * (1 + eta + data.totalCharge) ^ 2) ^ 12 := by
  rw [← fullKernelPolyVar_bo]
  exact fullKernelThreshold_le_poly _ L hL

/-- The Born–Oppenheimer constant `A₁`: `A₁ ≤ a_L ((1 + η³)(1 + η + Z_tot)²)²⁷`. -/
theorem fullKernelImpConstant₁_le_poly_bo (eta : ℕ) (data : FiniteBONuclearData ν) (L : ℝ)
    (hL : 0 < L) :
    fullKernelImpConstant₁ (CoulombSystem.bo eta data) L ≤
      fullKernelImpCellFactor₁ L *
        ((1 + (eta : ℝ) ^ 3) * (1 + eta + data.totalCharge) ^ 2) ^ 27 := by
  rw [← fullKernelPolyVar_bo]
  exact fullKernelImpConstant₁_le_poly _ L hL

/-- The Born–Oppenheimer constant `A₂`: `A₂ ≤ 4 g² γ_L (1 + η³)(1 + η + Z_tot)²`. -/
theorem fullKernelImpConstant₂_le_poly_bo (eta : ℕ) (data : FiniteBONuclearData ν) (L : ℝ)
    (hL : 0 < L) :
    fullKernelImpConstant₂ (CoulombSystem.bo eta data) L ≤
      4 * (2 * Real.pi / L) ^ 2 * coulombCellAmplitude L *
        ((1 + (eta : ℝ) ^ 3) * (1 + eta + data.totalCharge) ^ 2) := by
  rw [← fullKernelPolyVar_bo]
  exact fullKernelImpConstant₂_le_poly _ L hL

end Coulomb

end

end PlaneWaveFullKernel

end DevFK7
-- END SOURCE dev/DevFK7.lean

/-! ════════════════════════════════════════════════════════════════════
## Part `GridDynamics`
════════════════════════════════════════════════════════════════════ -/

/-!
The grid dynamics: `lem:grid-obs`, `lem:grid-traj`, `prop:grid-dyn`, `lem:grid-KR2`,
`lem:grid-data2`, `lem:grid-obs2` and `thm:grid-dyn-sharp` (namespace `PlaneWaveGridDynamics`;
former development files `dev/DevGD1.lean` to `dev/DevGD7.lean` and `dev/DevGS1.lean` to
`dev/DevGS6.lean`).
-/

-- BEGIN SOURCE dev/DevGD1.lean
-- SHA256 6b33e6fa33d44a66a2895ba188783a5becee2b4770d20add1d4ab421e6bfe594
section DevGD1

/-!
# Grid dynamics: the collocated observable on the register

The grid method of `sec:grid-def` (padded register with `n' = 4m + 1` points per direction,
register radius `2m`, effective resolution `K = g m`) implements the observable `χ(x_a)` as the
operator diagonal in the grid basis with entries `χ(x_{j_a})` (`lem:grid-obs`).  In the momentum
basis of the register (`RCfg eta m`, which is the certificate's cube of radius `2m` through
`regUnitary`) this operator is the *cyclic* convolution

  `(O_g u)(q) = Σ_ν χ̂(ν) u(q + ν e_a)`   (the momentum of register `a` added modulo `n'`),

`gridObs`, while the Galerkin compression `P χ(x_a) P` is the same sum with the translation
restricted to the register zone (`galObs`, `regCoeff_convOp`).  The difference consists of the
wrap terms; each translation by `ν` with `‖ν‖∞ ≤ m` wraps only between momenta that both lie
beyond `m` in register `a`, so (`eq:obs-form`)

  `|⟪v, (O_g - P χ P) u⟫| ≤ C_χ t_a(m; u) t_a(m; v) + τ_χ(m) ‖u‖ ‖v‖`

(`norm_inner_gridObs_sub_galObs_le`, `norm_inner_wrapObs_le`), with `C_χ = Σ_ν |χ̂(ν)|`, the
sup-norm tails `t_a(m; ·)` beyond `m` (that is beyond `K`) and the coefficient tail
`τ_χ(m) = Σ_{‖ν‖∞ > m} |χ̂(ν)|`.  The regularity estimate `eq:obs-theta` holds with the
mass-weighted weight `wM` of the grid core:
`‖wM (O_g v)‖ ≤ (2 + 12 m̄) C_χ ‖wM v‖ + 14 D'_χ ‖v‖` with the coefficient moment
`D'_χ = Σ_ν |ν|² |χ̂(ν)|` (`momTwo`, lattice units; not the manuscript's `D_χ`)
(`norm_wM_gridObs_le`); the wrapped content needs no separate tail term, since `m² t_a(m; v)` is
already bounded by `m̄ ‖wM v‖`.  For a real `χ` both operators are symmetric.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace PlaneWaveGridDynamics

open PlaneWaveGrid

/-! ## Register translations -/

section Shifts

variable {eta m : ℕ}

/-- The modes of the padded register of radius `2m`. -/
abbrev RMode (m : ℕ) := GMode (2 * (2 * m) + 1)

/-- Shift of the momentum of register `a` by `μ`, cyclically. -/
def cfgShift (a : Fin eta) (μ : RMode m) (q : RCfg eta m) : RCfg eta m :=
  Function.update q a (q a + μ)

@[simp] lemma cfgShift_self (a : Fin eta) (μ : RMode m) (q : RCfg eta m) :
    cfgShift a μ q a = q a + μ := by
  simp [cfgShift]

lemma cfgShift_ne {a b : Fin eta} (h : b ≠ a) (μ : RMode m) (q : RCfg eta m) :
    cfgShift a μ q b = q b := by
  simp [cfgShift, Function.update_of_ne h]

lemma cfgShift_cfgShift (a : Fin eta) (μ μ' : RMode m) (q : RCfg eta m) :
    cfgShift a μ (cfgShift a μ' q) = cfgShift a (μ' + μ) q := by
  funext b
  by_cases h : b = a
  · subst h
    simp [add_assoc]
  · rw [cfgShift_ne h, cfgShift_ne h, cfgShift_ne h]

lemma cfgShift_zero (a : Fin eta) (q : RCfg eta m) : cfgShift a 0 q = q := by
  funext b
  by_cases h : b = a
  · subst h
    simp
  · rw [cfgShift_ne h]

/-- The shift as an equivalence of configurations. -/
def cfgShiftEquiv (a : Fin eta) (μ : RMode m) : RCfg eta m ≃ RCfg eta m where
  toFun := cfgShift a μ
  invFun := cfgShift a (-μ)
  left_inv q := by
    show cfgShift a (-μ) (cfgShift a μ q) = q
    rw [cfgShift_cfgShift, add_neg_cancel, cfgShift_zero]
  right_inv q := by
    show cfgShift a μ (cfgShift a (-μ) q) = q
    rw [cfgShift_cfgShift, neg_add_cancel, cfgShift_zero]

/-- The cyclic translation of register `a` by `ν`: `(cycShift a ν u)(q) = u(q + ν e_a)`. -/
noncomputable def cycShift (a : Fin eta) (ν : Lat3) :
    EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cfgShiftEquiv a (-(ofLat ν)))

lemma cycShift_apply (a : Fin eta) (ν : Lat3) (u : EuclideanSpace ℂ (RCfg eta m))
    (q : RCfg eta m) : cycShift a ν u q = u (cfgShift a (ofLat ν) q) := by
  simp [cycShift, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    cfgShiftEquiv]

/-- The cyclic translation as a bounded operator. -/
noncomputable def cycCLM (a : Fin eta) (ν : Lat3) :
    EuclideanSpace ℂ (RCfg eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  (cycShift a ν).toLinearIsometry.toContinuousLinearMap

lemma cycCLM_apply (a : Fin eta) (ν : Lat3) (u : EuclideanSpace ℂ (RCfg eta m))
    (q : RCfg eta m) : cycCLM a ν u q = u (cfgShift a (ofLat ν) q) :=
  cycShift_apply a ν u q

lemma norm_cycCLM_le (a : Fin eta) (ν : Lat3) : ‖cycCLM (m := m) a ν‖ ≤ 1 :=
  (cycShift a ν).toLinearIsometry.norm_toContinuousLinearMap_le

lemma norm_cycCLM_apply (a : Fin eta) (ν : Lat3) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖cycCLM a ν u‖ = ‖u‖ :=
  (cycShift a ν).norm_map u

end Shifts

/-! ## Masks as bounded operators -/

section Masks

variable {ι : Type*} [Fintype ι]

/-- The restriction to a set of configurations, as a bounded operator. -/
noncomputable def maskCLM (P : ι → Prop) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap (maskOp P)

lemma maskCLM_apply (P : ι → Prop) (u : EuclideanSpace ℂ ι) : maskCLM P u = maskOp P u := rfl

lemma norm_maskCLM_le (P : ι → Prop) : ‖maskCLM (ι := ι) P‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul, maskCLM_apply]
    exact norm_maskOp_le P u

end Masks

/-! ## The grid observable and its Galerkin compression -/

section Observable

variable {eta m : ℕ}

/-- **The collocated observable** `χ(x_a)` of the grid in the momentum basis of the register:
`Σ_ν χ̂(ν)` times the cyclic translation by `ν` of register `a`. -/
noncomputable def gridObs (a : Fin eta) (c : Lat3 → ℂ) :
    EuclideanSpace ℂ (RCfg eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  ∑' ν, c ν • cycCLM a ν

/-- No wrap: the translated momentum of register `a` stays in the register zone. -/
def NoWrap (a : Fin eta) (ν : Lat3) (q : RCfg eta m) : Prop := InBox (2 * m) (gl (q a) + ν)

instance (a : Fin eta) (ν : Lat3) (q : RCfg eta m) : Decidable (NoWrap a ν q) := by
  unfold NoWrap; infer_instance

/-- The non-cyclic translation of register `a` by `ν`, restricted to the register zone. -/
noncomputable def linCLM (a : Fin eta) (ν : Lat3) :
    EuclideanSpace ℂ (RCfg eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  (maskCLM (NoWrap a ν)).comp (cycCLM a ν)

/-- The wrap part of the cyclic translation. -/
noncomputable def wrapCLM (a : Fin eta) (ν : Lat3) :
    EuclideanSpace ℂ (RCfg eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  (maskCLM (fun q => ¬ NoWrap a ν q)).comp (cycCLM a ν)

lemma cycCLM_eq_lin_add_wrap (a : Fin eta) (ν : Lat3) :
    cycCLM (m := m) a ν = linCLM a ν + wrapCLM a ν := by
  ext u q
  simp only [linCLM, wrapCLM, add_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, maskCLM_apply, PiLp.add_apply]
  by_cases h : NoWrap a ν q
  · rw [maskOp_apply_of _ _ h, maskOp_apply_of_not (fun q => ¬ NoWrap a ν q) _ (not_not.mpr h),
      add_zero]
  · rw [maskOp_apply_of_not _ _ h, maskOp_apply_of (fun q => ¬ NoWrap a ν q) _ h, zero_add]

lemma norm_comp_mask_le {P : RCfg eta m → Prop}
    {T : EuclideanSpace ℂ (RCfg eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m)} (hT : ‖T‖ ≤ 1) :
    ‖(maskCLM P).comp T‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖maskCLM P‖ * ‖T‖ ≤ 1 * 1 :=
        mul_le_mul (norm_maskCLM_le P) hT (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma norm_linCLM_le (a : Fin eta) (ν : Lat3) : ‖linCLM (m := m) a ν‖ ≤ 1 :=
  norm_comp_mask_le (norm_cycCLM_le a ν)

lemma norm_wrapCLM_le (a : Fin eta) (ν : Lat3) : ‖wrapCLM (m := m) a ν‖ ≤ 1 :=
  norm_comp_mask_le (norm_cycCLM_le a ν)

/-- The Galerkin compression `P χ(x_a) P` on the register. -/
noncomputable def galObs (a : Fin eta) (c : Lat3 → ℂ) :
    EuclideanSpace ℂ (RCfg eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  ∑' ν, c ν • linCLM a ν

/-- The wrap operator `O_g - P χ P`. -/
noncomputable def wrapObs (a : Fin eta) (c : Lat3 → ℂ) :
    EuclideanSpace ℂ (RCfg eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  ∑' ν, c ν • wrapCLM a ν

variable {c : Lat3 → ℂ}

lemma summable_smul_of_norm_le_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (hc : Summable fun ν => ‖c ν‖) {T : Lat3 → F} (hT : ∀ ν, ‖T ν‖ ≤ 1) :
    Summable fun ν => c ν • T ν :=
  Summable.of_norm_bounded hc (fun ν => by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hT ν))

lemma hasSum_gridObs (a : Fin eta) (hc : Summable fun ν => ‖c ν‖) :
    HasSum (fun ν => c ν • cycCLM (m := m) a ν) (gridObs a c) :=
  (summable_smul_of_norm_le_one hc (norm_cycCLM_le a)).hasSum

lemma hasSum_galObs (a : Fin eta) (hc : Summable fun ν => ‖c ν‖) :
    HasSum (fun ν => c ν • linCLM (m := m) a ν) (galObs a c) :=
  (summable_smul_of_norm_le_one hc (norm_linCLM_le a)).hasSum

lemma hasSum_wrapObs (a : Fin eta) (hc : Summable fun ν => ‖c ν‖) :
    HasSum (fun ν => c ν • wrapCLM (m := m) a ν) (wrapObs a c) :=
  (summable_smul_of_norm_le_one hc (norm_wrapCLM_le a)).hasSum

lemma gridObs_eq_galObs_add_wrapObs (a : Fin eta) (hc : Summable fun ν => ‖c ν‖) :
    gridObs (m := m) a c = galObs a c + wrapObs a c := by
  have h := (hasSum_galObs (m := m) a hc).add (hasSum_wrapObs a hc)
  have e : (fun ν => c ν • linCLM (m := m) a ν + c ν • wrapCLM a ν) =
      fun ν => c ν • cycCLM a ν := by
    funext ν
    rw [cycCLM_eq_lin_add_wrap, smul_add]
  rw [e] at h
  exact (hasSum_gridObs a hc).unique h

lemma norm_gridObs_le (a : Fin eta) (hc : Summable fun ν => ‖c ν‖) :
    ‖gridObs (m := m) a c‖ ≤ ∑' ν, ‖c ν‖ :=
  (hasSum_gridObs a hc).norm_le_of_bounded hc.hasSum (fun ν => by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_cycCLM_le a ν))

lemma norm_galObs_le (a : Fin eta) (hc : Summable fun ν => ‖c ν‖) :
    ‖galObs (m := m) a c‖ ≤ ∑' ν, ‖c ν‖ :=
  (hasSum_galObs a hc).norm_le_of_bounded hc.hasSum (fun ν => by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_linCLM_le a ν))

/-- Evaluation of a convergent series of operators at a vector and a configuration. -/
lemma hasSum_eval {T : Lat3 → EuclideanSpace ℂ (RCfg eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m)}
    {S : EuclideanSpace ℂ (RCfg eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m)}
    (h : HasSum T S) (u : EuclideanSpace ℂ (RCfg eta m)) (q : RCfg eta m) :
    HasSum (fun ν => T ν u q) (S u q) :=
  h.mapL ((EuclideanSpace.proj q).comp (ContinuousLinearMap.apply ℂ _ u))

lemma gridObs_apply (a : Fin eta) (hc : Summable fun ν => ‖c ν‖)
    (u : EuclideanSpace ℂ (RCfg eta m)) (q : RCfg eta m) :
    gridObs a c u q = ∑' ν, c ν * u (cfgShift a (ofLat ν) q) := by
  refine ((hasSum_eval (hasSum_gridObs a hc) u q).tsum_eq.symm).trans ?_
  refine tsum_congr fun ν => ?_
  rw [smul_apply, PiLp.smul_apply, cycCLM_apply, smul_eq_mul]

/-- The adjoint of a cyclic translation is the opposite translation. -/
lemma inner_cycCLM (a : Fin eta) (ν : Lat3) (u v : EuclideanSpace ℂ (RCfg eta m)) :
    ⟪cycCLM a ν u, v⟫_ℂ = ⟪u, cycCLM a (-ν) v⟫_ℂ := by
  have h : cycCLM a ν (cycCLM a (-ν) v) = v := by
    ext q
    rw [cycCLM_apply, cycCLM_apply, cfgShift_cfgShift]
    have e : ofLat (M := 2 * m) ν + ofLat (-ν) = 0 := by
      rw [← ofLat_add, add_neg_cancel]
      funext k
      simp [ofLat]
    rw [e, cfgShift_zero]
  calc ⟪cycCLM a ν u, v⟫_ℂ = ⟪cycShift a ν u, cycShift a ν (cycCLM a (-ν) v)⟫_ℂ := by
        congr 1
        exact h.symm
    _ = ⟪u, cycCLM a (-ν) v⟫_ℂ := LinearIsometryEquiv.inner_map_map _ _ _

/-- **Symmetry.** For a real `χ` (`χ̂(-ν) = conj χ̂(ν)`) the grid observable is symmetric. -/
lemma gridObs_symm (a : Fin eta) (hc : Summable fun ν => ‖c ν‖)
    (hreal : ∀ ν, c (-ν) = conj (c ν)) (u v : EuclideanSpace ℂ (RCfg eta m)) :
    ⟪gridObs a c u, v⟫_ℂ = ⟪u, gridObs a c v⟫_ℂ := by
  set G : Lat3 → ℂ := fun μ => ⟪u, c μ • cycCLM a μ v⟫_ℂ
  have hR : HasSum G ⟪u, gridObs a c v⟫_ℂ :=
    ((hasSum_gridObs a hc).mapL (ContinuousLinearMap.apply ℂ _ v)).mapL (innerSL ℂ u)
  have hL0 : HasSum (fun ν => ⟪c ν • cycCLM a ν u, v⟫_ℂ) ⟪gridObs a c u, v⟫_ℂ := by
    have h1 := (((hasSum_gridObs (m := m) a hc).mapL (ContinuousLinearMap.apply ℂ _ u)).mapL
      (innerSL ℂ v)).star
    simp only [innerSL_apply_apply, ContinuousLinearMap.apply_apply] at h1
    have e : ∀ x : EuclideanSpace ℂ (RCfg eta m), star ⟪v, x⟫_ℂ = ⟪x, v⟫_ℂ :=
      fun x => inner_conj_symm x v
    simp only [e] at h1
    exact h1
  have hterm : (fun ν => ⟪c ν • cycCLM a ν u, v⟫_ℂ) = G ∘ (Equiv.neg Lat3) := by
    funext ν
    simp only [G, Function.comp_apply, Equiv.neg_apply]
    rw [inner_smul_left, inner_smul_right, inner_cycCLM, hreal]
  rw [hterm, (Equiv.neg Lat3).hasSum_iff] at hL0
  exact hL0.unique hR

/-! ### Arithmetic of the cyclic translation -/

lemma gl_add_ofLat (x : RMode m) (ν : Lat3) (h : InBox (2 * m) (gl x + ν)) :
    gl (x + ofLat ν) = gl x + ν := by
  have e : x + ofLat (M := 2 * m) ν = ofLat (gl x + ν) := by
    rw [ofLat_add, ofLat_gl]
  rw [e, gl_ofLat h]

/-- A wrapping translation by `|t| ≤ m` changes the centred representative by more than `2m`. -/
lemma wrap_component (z : ZMod (2 * (2 * m) + 1)) (t : ℤ) (ht : |t| ≤ m)
    (hw : (2 * m : ℤ) < |z.valMinAbs + t|) :
    (2 * m : ℤ) < |(z + (t : ZMod (2 * (2 * m) + 1))).valMinAbs - z.valMinAbs| := by
  obtain ⟨k, hk, he⟩ := valMinAbs_sub_decomp (M := 2 * m) (z + (t : ZMod (2 * (2 * m) + 1))) z
  have hsub : z + (t : ZMod (2 * (2 * m) + 1)) - z = (t : ZMod (2 * (2 * m) + 1)) := by ring
  have ht2 : |t| ≤ ((2 * m : ℕ) : ℤ) := by
    rw [abs_le] at ht ⊢
    push_cast
    constructor <;> omega
  rw [hsub, valMinAbs_intCast_of_abs_le t ht2] at he
  have hxb := valMinAbs_bounds (M := 2 * m) (z + (t : ZMod (2 * (2 * m) + 1)))
  have hzb := valMinAbs_bounds (M := 2 * m) z
  rw [abs_le] at ht
  rw [lt_abs] at hw ⊢
  push_cast at hxb hzb he
  rcases hk with rfl | rfl | rfl <;> omega

lemma wrap_far (x : RMode m) (ν : Lat3) (hν : InBox m ν) (hw : ¬ InBox (2 * m) (gl x + ν)) :
    ¬ InBox (2 * m) (gl (x + ofLat ν) - gl x) := by
  simp only [InBox, not_forall, not_le] at hw ⊢
  obtain ⟨c, hc⟩ := hw
  refine ⟨c, ?_⟩
  have h := wrap_component (x c) (ν c) (hν c) (by push_cast at hc ⊢; exact hc)
  have e : (gl (x + ofLat (M := 2 * m) ν) - gl x) c =
      (x c + ((ν c : ℤ) : ZMod (2 * (2 * m) + 1))).valMinAbs - (x c).valMinAbs := rfl
  push_cast
  rw [e]
  exact h

/-- **Strong wraps.** A translation by `‖ν‖∞ ≤ m` that wraps connects two momenta of register `a`
that both lie beyond `m`. -/
lemma high_of_wrap (a : Fin eta) {ν : Lat3} (hν : InBox m ν) {q : RCfg eta m}
    (hq : ¬ NoWrap a ν q) : High m a q ∧ High m a (cfgShift a (ofLat ν) q) := by
  have hd : InBox m (gl ((q a + ofLat ν) - q a)) := by
    rw [add_sub_cancel_left, gl_ofLat (hν.mono (by omega))]
    exact hν
  have h := strongWrap_lattice m (q a + ofLat ν) (q a) hd (wrap_far (q a) ν hν hq)
  refine ⟨h.2, ?_⟩
  show ¬ InBox m (gl (cfgShift a (ofLat ν) q a))
  rw [cfgShift_self]
  exact h.1

/-! ### The wrap form (`eq:obs-form`) -/

lemma inner_maskOp_right {ι : Type*} [Fintype ι] (P : ι → Prop) (u v : EuclideanSpace ℂ ι) :
    ⟪v, maskOp P u⟫_ℂ = ⟪maskOp P v, u⟫_ℂ := by
  classical
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine sum_congr rfl fun q _ => ?_
  by_cases h : P q
  · rw [maskOp_apply_of P u h, maskOp_apply_of P v h]
  · rw [maskOp_apply_of_not P u h, maskOp_apply_of_not P v h, inner_zero_left, inner_zero_right]

lemma maskOp_maskOp {ι : Type*} [Fintype ι] (P : ι → Prop) (u : EuclideanSpace ℂ ι) :
    maskOp P (maskOp P u) = maskOp P u := by
  classical
  ext q
  by_cases h : P q
  · rw [maskOp_apply_of P _ h, maskOp_apply_of P _ h]
  · rw [maskOp_apply_of_not P _ h, maskOp_apply_of_not P _ h]

/-- A strong wrap only sees the high parts of both states. -/
lemma wrapCLM_eq_high (a : Fin eta) {ν : Lat3} (hν : InBox m ν)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    wrapCLM a ν u = maskOp (High m a) (wrapCLM a ν (maskOp (High m a) u)) := by
  classical
  ext q
  simp only [wrapCLM, ContinuousLinearMap.coe_comp, Function.comp_apply, maskCLM_apply]
  by_cases hw : NoWrap a ν q
  · rw [maskOp_apply_of_not (fun q => ¬ NoWrap a ν q) _ (not_not.mpr hw)]
    by_cases hH : High m a q
    · rw [maskOp_apply_of _ _ hH, maskOp_apply_of_not (fun q => ¬ NoWrap a ν q) _
        (not_not.mpr hw)]
    · rw [maskOp_apply_of_not _ _ hH]
  · have hH := high_of_wrap a hν hw
    rw [maskOp_apply_of (fun q => ¬ NoWrap a ν q) _ hw, maskOp_apply_of _ _ hH.1,
      maskOp_apply_of (fun q => ¬ NoWrap a ν q) _ hw, cycCLM_apply, cycCLM_apply,
      maskOp_apply_of _ _ hH.2]

lemma norm_wrapCLM_le_high (a : Fin eta) {ν : Lat3} (hν : InBox m ν)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wrapCLM a ν u‖ ≤ ‖maskOp (High m a) u‖ := by
  rw [wrapCLM_eq_high a hν u]
  refine (norm_maskOp_le _ _).trans ?_
  exact ((wrapCLM a ν).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_wrapCLM_le a ν))

lemma norm_inner_wrapCLM_le (a : Fin eta) {ν : Lat3} (hν : InBox m ν)
    (u v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖⟪v, wrapCLM a ν u⟫_ℂ‖ ≤ ‖maskOp (High m a) v‖ * ‖maskOp (High m a) u‖ := by
  rw [wrapCLM_eq_high a hν u, inner_maskOp_right]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact ((wrapCLM a ν).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_wrapCLM_le a ν))

/-- The coefficient tail `τ_χ(m) = Σ_{‖ν‖∞ > m} |χ̂(ν)|` (sup norm). -/
noncomputable def supTail (c : Lat3 → ℂ) (m : ℕ) : ℝ := ∑' ν, if InBox m ν then 0 else ‖c ν‖

lemma summable_supTail_terms (hc : Summable fun ν => ‖c ν‖) (m : ℕ) :
    Summable fun ν => if InBox m ν then (0 : ℝ) else ‖c ν‖ :=
  Summable.of_nonneg_of_le (fun ν => by split_ifs <;> simp) (fun ν => by split_ifs <;> simp) hc

lemma supTail_nonneg (c : Lat3 → ℂ) (m : ℕ) : 0 ≤ supTail c m :=
  tsum_nonneg fun ν => by split_ifs <;> simp

/-- **The collocated observable: form error** (`lem:grid-obs`, `eq:obs-form`). -/
theorem norm_inner_wrapObs_le (a : Fin eta) (hc : Summable fun ν => ‖c ν‖)
    (u v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖⟪v, wrapObs a c u⟫_ℂ‖ ≤
      (∑' ν, ‖c ν‖) * (‖maskOp (High m a) v‖ * ‖maskOp (High m a) u‖) +
        supTail c m * (‖v‖ * ‖u‖) := by
  set A := ‖maskOp (High m a) v‖ * ‖maskOp (High m a) u‖
  set B := ‖v‖ * ‖u‖
  have hA : 0 ≤ A := by positivity
  have hS : HasSum (fun ν => ⟪v, c ν • wrapCLM a ν u⟫_ℂ) ⟪v, wrapObs a c u⟫_ℂ :=
    ((hasSum_wrapObs a hc).mapL (ContinuousLinearMap.apply ℂ _ u)).mapL (innerSL ℂ v)
  have hg : HasSum (fun ν => ‖c ν‖ * A + (if InBox m ν then (0 : ℝ) else ‖c ν‖) * B)
      ((∑' ν, ‖c ν‖) * A + supTail c m * B) :=
    (hc.hasSum.mul_right A).add ((summable_supTail_terms hc m).hasSum.mul_right B)
  refine hS.norm_le_of_bounded hg fun ν => ?_
  rw [inner_smul_right, norm_mul]
  by_cases hν : InBox m ν
  · rw [if_pos hν, zero_mul, add_zero]
    exact mul_le_mul_of_nonneg_left (norm_inner_wrapCLM_le a hν u v) (norm_nonneg _)
  · rw [if_neg hν]
    have h1 : ‖⟪v, wrapCLM a ν u⟫_ℂ‖ ≤ B := by
      refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact ((wrapCLM a ν).le_opNorm _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (norm_wrapCLM_le a ν))
    have h2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (c ν))
    have h3 : 0 ≤ ‖c ν‖ * A := mul_nonneg (norm_nonneg _) hA
    linarith

/-- The same in operator form: `O_g = P χ P + (wraps)`. -/
theorem norm_inner_gridObs_sub_galObs_le (a : Fin eta) (hc : Summable fun ν => ‖c ν‖)
    (u v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖⟪v, gridObs a c u⟫_ℂ - ⟪v, galObs a c u⟫_ℂ‖ ≤
      (∑' ν, ‖c ν‖) * (‖maskOp (High m a) v‖ * ‖maskOp (High m a) u‖) +
        supTail c m * (‖v‖ * ‖u‖) := by
  rw [gridObs_eq_galObs_add_wrapObs a hc, add_apply, inner_add_right, add_sub_cancel_left]
  exact norm_inner_wrapObs_le a hc u v

/-! ### Regularity of the collocated observable (`eq:obs-theta`) -/

lemma norm_le_of_pointwise {ι : Type*} [Fintype ι] {X Y : EuclideanSpace ℂ ι}
    (h : ∀ q, ‖X q‖ ≤ ‖Y q‖) : ‖X‖ ≤ ‖Y‖ := by
  have hsq : ‖X‖ ^ 2 ≤ ‖Y‖ ^ 2 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum]
    exact sum_le_sum fun q _ => pow_le_pow_left₀ (norm_nonneg _) (h q) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- The vector of absolute values. -/
noncomputable def absVec {ι : Type*} [Fintype ι] (X : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun q => ((‖X q‖ : ℝ) : ℂ)

lemma norm_absVec {ι : Type*} [Fintype ι] (X : EuclideanSpace ℂ ι) : ‖absVec X‖ = ‖X‖ := by
  have hsq : ‖absVec X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum]
    refine sum_congr rfl fun q _ => ?_
    simp [absVec]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- Minkowski for pointwise domination by a sum of three vectors. -/
lemma norm_le_add3_of_pointwise {ι : Type*} [Fintype ι] {X A B C : EuclideanSpace ℂ ι}
    (h : ∀ q, ‖X q‖ ≤ ‖A q‖ + ‖B q‖ + ‖C q‖) : ‖X‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
  have hpt : ∀ q, ‖X q‖ ≤ ‖(absVec A + absVec B + absVec C) q‖ := by
    intro q
    have e : (absVec A + absVec B + absVec C) q = ((‖A q‖ + ‖B q‖ + ‖C q‖ : ℝ) : ℂ) := by
      simp [absVec]
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact h q
  refine (norm_le_of_pointwise hpt).trans ?_
  refine (norm_add_le _ _).trans ?_
  rw [norm_absVec C]
  have := norm_add_le (absVec A) (absVec B)
  rw [norm_absVec, norm_absVec] at this
  linarith

lemma nsq_gl_le (x : RMode m) : nsq (gl x) ≤ 12 * (m : ℝ) ^ 2 := by
  have hb := gl_inBox (M := 2 * m) x
  have hc : ∀ c : Fin 3, ((gl x c : ℤ) : ℝ) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by
    intro c
    have h1 : |((gl x c : ℤ) : ℝ)| ≤ 2 * (m : ℝ) := by
      have h0 : |gl x c| ≤ ((2 * m : ℕ) : ℤ) := hb c
      have h2 : ((|gl x c| : ℤ) : ℝ) ≤ (((2 * m : ℕ) : ℤ) : ℝ) := Int.cast_le.mpr h0
      push_cast at h2
      exact h2
    have h3 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h3
    nlinarith
  rw [nsq_eq_sum, Fin.sum_univ_three]
  nlinarith [hc 0, hc 1, hc 2]

lemma nsq_sub_le (x y : Lat3) : nsq (x - y) ≤ 2 * nsq x + 2 * nsq y := by
  simp only [nsq, Pi.sub_apply]
  push_cast
  nlinarith [sq_nonneg (((x 0 : ℤ) : ℝ) + y 0), sq_nonneg (((x 1 : ℤ) : ℝ) + y 1),
    sq_nonneg (((x 2 : ℤ) : ℝ) + y 2)]

/-- The weight of an output against the weight of its translated input. -/
lemma wM_le_shift (P : RegParticles eta) (a : Fin eta) (ν : Lat3) (q : RCfg eta m) :
    wM P q ≤ 2 * wM P (cfgShift a (ofLat ν) q) + 2 * nsq ν +
      (if NoWrap a ν q then 0 else 12 * (m : ℝ) ^ 2) := by
  set p := cfgShift a (ofLat ν) q
  have hma := P.one_le_mass a
  have hmpos := P.mass_pos a
  have hsplit : ∀ r : RCfg eta m, wM P r =
      1 + nsq (gl (r a)) / P.mass a + ∑ b ∈ univ.erase a, nsq (gl (r b)) / P.mass b := by
    intro r
    unfold wM
    rw [← Finset.add_sum_erase _ _ (mem_univ a)]
    ring
  have hrest : ∑ b ∈ univ.erase a, nsq (gl (q b)) / P.mass b =
      ∑ b ∈ univ.erase a, nsq (gl (p b)) / P.mass b :=
    sum_congr rfl fun b hb => by simp only [p, cfgShift_ne (ne_of_mem_erase hb)]
  have hR0 : 0 ≤ ∑ b ∈ univ.erase a, nsq (gl (p b)) / P.mass b :=
    sum_nonneg fun b _ => div_nonneg (nsq_nonneg _) (P.mass_pos b).le
  have hpa : 0 ≤ nsq (gl (p a)) / P.mass a := div_nonneg (nsq_nonneg _) hmpos.le
  have hν := nsq_nonneg ν
  rw [hsplit q, hsplit p, hrest]
  by_cases hw : NoWrap a ν q
  · rw [if_pos hw, add_zero]
    have hpa' : gl (p a) = gl (q a) + ν := by
      show gl (cfgShift a (ofLat ν) q a) = _
      rw [cfgShift_self]
      exact gl_add_ofLat (q a) ν hw
    have hq : gl (q a) = gl (p a) - ν := by rw [hpa']; abel
    have h1 : nsq (gl (q a)) ≤ 2 * nsq (gl (p a)) + 2 * nsq ν := by
      rw [hq]; exact nsq_sub_le _ _
    have h2 : nsq (gl (q a)) / P.mass a ≤ 2 * (nsq (gl (p a)) / P.mass a) + 2 * nsq ν := by
      have h3 : nsq (gl (q a)) / P.mass a ≤ (2 * nsq (gl (p a)) + 2 * nsq ν) / P.mass a :=
        div_le_div_of_nonneg_right h1 hmpos.le
      have h4 : 2 * nsq ν / P.mass a ≤ 2 * nsq ν := div_le_self (by linarith) hma
      calc nsq (gl (q a)) / P.mass a ≤ (2 * nsq (gl (p a)) + 2 * nsq ν) / P.mass a := h3
        _ = 2 * (nsq (gl (p a)) / P.mass a) + 2 * nsq ν / P.mass a := by ring
        _ ≤ 2 * (nsq (gl (p a)) / P.mass a) + 2 * nsq ν := by linarith
    linarith
  · rw [if_neg hw]
    have h1 := nsq_gl_le (q a)
    have h2 : nsq (gl (q a)) / P.mass a ≤ 12 * (m : ℝ) ^ 2 :=
      (div_le_self (nsq_nonneg _) hma).trans h1
    linarith

/-- One translation: `‖wM (S_ν u)‖ ≤ 2 ‖wM u‖ + 2 |ν|² ‖u‖ + 12 m² ‖(wrap part) u‖`. -/
lemma norm_wM_cycCLM_le (P : RegParticles eta) (a : Fin eta) (ν : Lat3)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM P) (cycCLM a ν u)‖ ≤
      2 * ‖wMul (wM P) u‖ + 2 * nsq ν * ‖u‖ + 12 * (m : ℝ) ^ 2 * ‖wrapCLM a ν u‖ := by
  have hν2 : (0 : ℝ) ≤ 2 * nsq ν := mul_nonneg zero_le_two (nsq_nonneg ν)
  have hm12 : (0 : ℝ) ≤ 12 * (m : ℝ) ^ 2 := by positivity
  set A : EuclideanSpace ℂ (RCfg eta m) := ((2 : ℝ) : ℂ) • cycCLM a ν (wMul (wM P) u) with hA
  set B : EuclideanSpace ℂ (RCfg eta m) := ((2 * nsq ν : ℝ) : ℂ) • cycCLM a ν u with hB
  set C : EuclideanSpace ℂ (RCfg eta m) := ((12 * (m : ℝ) ^ 2 : ℝ) : ℂ) • wrapCLM a ν u with hC
  have hpt : ∀ q, ‖(wMul (wM P) (cycCLM a ν u)) q‖ ≤ ‖A q‖ + ‖B q‖ + ‖C q‖ := by
    intro q
    have hw := wM_le_shift P a ν q
    have hW0 : 0 ≤ wM P q := le_trans zero_le_one (wM_ge_one P q)
    have hWp : 0 ≤ wM P (cfgShift a (ofLat ν) q) := le_trans zero_le_one (wM_ge_one P _)
    have hx : 0 ≤ ‖u (cfgShift a (ofLat ν) q)‖ := norm_nonneg _
    have eX : ‖(wMul (wM P) (cycCLM a ν u)) q‖ = wM P q * ‖u (cfgShift a (ofLat ν) q)‖ := by
      rw [wMul_apply, cycCLM_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hW0]
    have eA : ‖A q‖ = 2 * (wM P (cfgShift a (ofLat ν) q) * ‖u (cfgShift a (ofLat ν) q)‖) := by
      rw [hA, PiLp.smul_apply, smul_eq_mul, cycCLM_apply, wMul_apply, norm_mul, norm_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg zero_le_two,
        Real.norm_of_nonneg hWp]
    have eB : ‖B q‖ = 2 * nsq ν * ‖u (cfgShift a (ofLat ν) q)‖ := by
      rw [hB, PiLp.smul_apply, smul_eq_mul, cycCLM_apply, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hν2]
    have eC : ‖C q‖ = (if NoWrap a ν q then 0 else 12 * (m : ℝ) ^ 2) *
        ‖u (cfgShift a (ofLat ν) q)‖ := by
      rw [hC, PiLp.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hm12]
      simp only [wrapCLM, ContinuousLinearMap.coe_comp, Function.comp_apply, maskCLM_apply]
      by_cases h : NoWrap a ν q
      · rw [maskOp_apply_of_not (fun q => ¬ NoWrap a ν q) _ (not_not.mpr h), if_pos h]
        simp
      · rw [maskOp_apply_of (fun q => ¬ NoWrap a ν q) _ h, if_neg h, cycCLM_apply]
    rw [eX, eA, eB, eC]
    have := mul_le_mul_of_nonneg_right hw hx
    nlinarith
  refine (norm_le_add3_of_pointwise hpt).trans (le_of_eq ?_)
  rw [hA, hB, hC, norm_smul, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg zero_le_two, Real.norm_of_nonneg hν2,
    Real.norm_of_nonneg hm12, norm_cycCLM_apply, norm_cycCLM_apply]

/-- `m² t_a(m; u) ≤ m̄ ‖wM u‖`: the high part is controlled by the weight. -/
lemma sq_mul_norm_high_le (P : RegParticles eta) (a : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)) :
    (m : ℝ) ^ 2 * ‖maskOp (High m a) u‖ ≤ P.maxMass * ‖wMul (wM P) u‖ := by
  have hM := P.maxMass_pos
  have hb : 0 < 1 + ((m : ℝ) + 1) ^ 2 / P.maxMass := by positivity
  have h := norm_maskOp_le_wMul (High m a) (wM P)
    (fun q => le_trans zero_le_one (wM_ge_one P q)) hb (fun q hq => wM_ge_of_high P hq) u
  have hX := norm_nonneg (wMul (wM P) u)
  have hfac : (m : ℝ) ^ 2 / (1 + ((m : ℝ) + 1) ^ 2 / P.maxMass) ≤ P.maxMass := by
    rw [div_le_iff₀ hb, mul_add, mul_one, mul_div_cancel₀ _ hM.ne']
    have e : ((m : ℝ) + 1) ^ 2 = (m : ℝ) ^ 2 + 2 * m + 1 := by ring
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  calc (m : ℝ) ^ 2 * ‖maskOp (High m a) u‖
      ≤ (m : ℝ) ^ 2 * (‖wMul (wM P) u‖ / (1 + ((m : ℝ) + 1) ^ 2 / P.maxMass)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (m : ℝ) ^ 2 / (1 + ((m : ℝ) + 1) ^ 2 / P.maxMass) * ‖wMul (wM P) u‖ := by ring
    _ ≤ P.maxMass * ‖wMul (wM P) u‖ := mul_le_mul_of_nonneg_right hfac hX

/-- The coefficient moment `D'_χ = Σ_ν |ν|² |χ̂(ν)|` (in lattice units; not the manuscript's
`D_χ = ‖∇χ‖∞ + ‖Δχ‖∞`). -/
noncomputable def momTwo (c : Lat3 → ℂ) : ℝ := ∑' ν, nsq ν * ‖c ν‖

/-- **The collocated observable: regularity** (`lem:grid-obs`, `eq:obs-theta`):
`‖wM (O_g u)‖ ≤ (2 + 12 m̄) C_χ ‖wM u‖ + 14 D'_χ ‖u‖`. -/
theorem norm_wM_gridObs_le (P : RegParticles eta) (a : Fin eta) (hc : Summable fun ν => ‖c ν‖)
    (hc2 : Summable fun ν => nsq ν * ‖c ν‖) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM P) (gridObs a c u)‖ ≤
      (2 + 12 * P.maxMass) * (∑' ν, ‖c ν‖) * ‖wMul (wM P) u‖ + 14 * momTwo c * ‖u‖ := by
  set W := LinearMap.toContinuousLinearMap (wMul (wM P) :
    EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m))
  have hS : HasSum (fun ν => c ν • W (cycCLM a ν u)) (W (gridObs a c u)) := by
    have h := ((hasSum_gridObs (m := m) a hc).mapL (ContinuousLinearMap.apply ℂ _ u)).mapL W
    simpa only [ContinuousLinearMap.apply_apply, smul_apply, map_smul] using h
  set X := ‖wMul (wM P) u‖
  set Hh := ‖maskOp (High m a) u‖
  have hX : 0 ≤ X := norm_nonneg _
  have hH : 0 ≤ Hh := norm_nonneg _
  have hg : HasSum (fun ν => ‖c ν‖ * (2 * X + 12 * (m : ℝ) ^ 2 * Hh) + 14 * (nsq ν * ‖c ν‖) * ‖u‖)
      ((∑' ν, ‖c ν‖) * (2 * X + 12 * (m : ℝ) ^ 2 * Hh) + 14 * momTwo c * ‖u‖) := by
    have h1 := hc.hasSum.mul_right (2 * X + 12 * (m : ℝ) ^ 2 * Hh)
    have h2 := (hc2.hasSum.mul_left 14).mul_right ‖u‖
    exact h1.add h2
  have hbound := hS.norm_le_of_bounded hg fun ν => by
    rw [norm_smul]
    have h1 := norm_wM_cycCLM_le P a ν u
    have hwrap : 12 * (m : ℝ) ^ 2 * ‖wrapCLM a ν u‖ ≤ 12 * (m : ℝ) ^ 2 * Hh + 12 * nsq ν * ‖u‖ := by
      by_cases hν : InBox m ν
      · have := norm_wrapCLM_le_high a hν u
        have h0 : 0 ≤ 12 * nsq ν * ‖u‖ := by have := nsq_nonneg ν; positivity
        nlinarith [sq_nonneg (m : ℝ)]
      · have hw1 : ‖wrapCLM a ν u‖ ≤ ‖u‖ := ((wrapCLM a ν).le_opNorm _).trans
          (mul_le_of_le_one_left (norm_nonneg _) (norm_wrapCLM_le a ν))
        have hn := nsq_ge_of_not_inBox hν
        have hm2 : (m : ℝ) ^ 2 ≤ nsq ν := by
          have e : ((m : ℝ) + 1) ^ 2 = (m : ℝ) ^ 2 + 2 * m + 1 := by ring
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith
        have h0 : 0 ≤ 12 * (m : ℝ) ^ 2 * Hh := by positivity
        have := mul_le_mul hm2 hw1 (norm_nonneg _) (nsq_nonneg ν)
        nlinarith
    have hc0 := norm_nonneg (c ν)
    have h2 : ‖W (cycCLM a ν u)‖ ≤ 2 * X + 12 * (m : ℝ) ^ 2 * Hh + 14 * nsq ν * ‖u‖ := by
      show ‖wMul (wM P) (cycCLM a ν u)‖ ≤ _
      have := nsq_nonneg ν
      nlinarith [norm_nonneg u]
    calc ‖c ν‖ * ‖W (cycCLM a ν u)‖
        ≤ ‖c ν‖ * (2 * X + 12 * (m : ℝ) ^ 2 * Hh + 14 * nsq ν * ‖u‖) :=
          mul_le_mul_of_nonneg_left h2 hc0
      _ = ‖c ν‖ * (2 * X + 12 * (m : ℝ) ^ 2 * Hh) + 14 * (nsq ν * ‖c ν‖) * ‖u‖ := by ring
  have hmH := sq_mul_norm_high_le P a u
  have hC0 : 0 ≤ ∑' ν, ‖c ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hfinal : (∑' ν, ‖c ν‖) * (2 * X + 12 * (m : ℝ) ^ 2 * Hh) ≤
      (2 + 12 * P.maxMass) * (∑' ν, ‖c ν‖) * X := by
    have : 2 * X + 12 * (m : ℝ) ^ 2 * Hh ≤ (2 + 12 * P.maxMass) * X := by nlinarith
    nlinarith
  show ‖W (gridObs a c u)‖ ≤ _
  linarith

end Observable

end PlaneWaveGridDynamics

end DevGD1
-- END SOURCE dev/DevGD1.lean

-- BEGIN SOURCE dev/DevGD2.lean
-- SHA256 f58b653109607d514e8f6aaad88ad926ab2187b1f86645226fe3c38c783b6a28
section DevGD2

/-!
# Grid dynamics: the grid propagator and the regularity of grid trajectories

`e^{-iH_grid t}` on the register is the finite-dimensional propagator of the symmetric grid
Hamiltonian (`Hgrid` of an even kernel; `exists_finitePropagator`).  The grid core proves the
Kato--Rellich bound of the collocated potential, packaged as the register Hamiltonian
`gridRegHam` (weight `wM`, coupling `Z = m̄ Z_c`, splitting radius `J₀ = J0g Z g`).  Here we add the
two directions of `lem:grid-KR`(iv) for every state, not only for eigenvectors:

* elliptic: `‖wM u‖ ≤ (4/3)(‖u‖ + (2/g²)(‖H u‖ + 26 Z J₀ ‖u‖))` (`RegHam.elliptic_gen`);
* forward: `‖H u‖ ≤ (5g²/8) ‖wM u‖ + 26 Z J₀ ‖u‖` (`RegHam.op_le`);

and their consequence for a unitary group that commutes with `H` (`lem:grid-traj`): the weight of
`e^{-iHt} u` is bounded uniformly in `t` by the graph norm of `u` (`RegHam.flow_le`).  Finally the
a priori shell bound `(T+1)² t_r(T; u) ≤ m̄ ‖wM u‖` (`sq_mul_norm_high_le_gen`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace PlaneWaveGridDynamics

open PlaneWaveGrid

section General

variable {ι : Type*} [Fintype ι] (H : RegHam ι)

/-- The kinetic part is at most `(g²/2)` times the weight. -/
lemma _root_.PlaneWaveGrid.RegHam.norm_kin_le (u : EuclideanSpace ℂ ι) :
    ‖wMul H.kin u‖ ≤ H.g ^ 2 / 2 * ‖wMul H.W u‖ := by
  have hg2 : 0 ≤ H.g ^ 2 / 2 := by positivity
  have h := norm_wMul_mono (w := H.kin) (w' := fun q => H.g ^ 2 / 2 * H.W q) H.kin_nonneg
    (fun q => by
      rw [H.kin_eq]
      have := H.W_ge_one q
      nlinarith) u
  have e : wMul (fun q => H.g ^ 2 / 2 * H.W q) u = ((H.g ^ 2 / 2 : ℝ) : ℂ) • wMul H.W u := by
    ext q
    simp only [wMul_apply, PiLp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg hg2] at h
  exact h

/-- **Forward graph-norm bound** (`lem:grid-KR`(iv)). -/
lemma _root_.PlaneWaveGrid.RegHam.op_le (u : EuclideanSpace ℂ ι) :
    ‖H.op u‖ ≤ 5 * H.g ^ 2 / 8 * ‖wMul H.W u‖ + 26 * H.Z * H.J0 * ‖u‖ := by
  have h1 := H.norm_kin_le u
  have hV := H.op_bound u
  have hs := H.small
  have hW := norm_nonneg (wMul H.W u)
  have h2 : H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖ ≤ H.g ^ 2 / 8 * ‖wMul H.W u‖ :=
    mul_le_mul_of_nonneg_right hs hW
  have h3 : ‖H.op u‖ ≤ ‖wMul H.kin u‖ + ‖H.V u‖ := by
    simp only [RegHam.op, LinearMap.add_apply]
    exact norm_add_le _ _
  have e : H.Z * (26 * H.J0) * ‖u‖ = 26 * H.Z * H.J0 * ‖u‖ := by ring
  linarith

/-- **Elliptic estimate for every state** (`lem:grid-KR`(iv)). -/
lemma _root_.PlaneWaveGrid.RegHam.elliptic_gen (u : EuclideanSpace ℂ ι) :
    ‖wMul H.W u‖ ≤ 4 / 3 * (‖u‖ + 2 / H.g ^ 2 * (‖H.op u‖ + 26 * H.Z * H.J0 * ‖u‖)) := by
  have hg2 : 0 < H.g ^ 2 := by have := H.g_pos; positivity
  have hkin : wMul H.kin u = H.op u - H.V u := by
    simp only [RegHam.op, LinearMap.add_apply]
    abel
  have h1 : ‖wMul H.kin u‖ ≤ ‖H.op u‖ + ‖H.V u‖ := by
    rw [hkin]
    exact norm_sub_le _ _
  have hV := H.op_bound u
  have h2 : ‖wMul H.W u‖ ≤ ‖u‖ + 2 / H.g ^ 2 * ‖wMul H.kin u‖ := by
    rw [H.wMul_W_eq u]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsmall := H.small
  have hX := norm_nonneg (wMul H.W u)
  have h4 : 2 / H.g ^ 2 * (H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖) ≤
      1 / 4 * ‖wMul H.W u‖ := by
    have : 2 / H.g ^ 2 * (H.Z * Real.sqrt (1378 / H.J0)) ≤ 1 / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hg2]
      linarith
    calc 2 / H.g ^ 2 * (H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖)
        = (2 / H.g ^ 2 * (H.Z * Real.sqrt (1378 / H.J0))) * ‖wMul H.W u‖ := by ring
      _ ≤ 1 / 4 * ‖wMul H.W u‖ := mul_le_mul_of_nonneg_right this hX
  have h3 : ‖wMul H.W u‖ ≤ ‖u‖ + 2 / H.g ^ 2 * (‖H.op u‖ + 26 * H.Z * H.J0 * ‖u‖) +
      2 / H.g ^ 2 * (H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖) := by
    have h5 : ‖wMul H.kin u‖ ≤ ‖H.op u‖ + 26 * H.Z * H.J0 * ‖u‖ +
        H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖ := by
      have e : H.Z * (26 * H.J0) * ‖u‖ = 26 * H.Z * H.J0 * ‖u‖ := by ring
      linarith
    have h6 : 2 / H.g ^ 2 * ‖wMul H.kin u‖ ≤ 2 / H.g ^ 2 * (‖H.op u‖ + 26 * H.Z * H.J0 * ‖u‖ +
        H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    linarith
  linarith

/-- **Regularity of a trajectory** (`lem:grid-traj`): for a unitary `U` commuting with `H` (each
member of a unitary group that commutes with `H`), the weight of `U u` is bounded by the graph
norm of `u`; the bound does not depend on `U`, so it is uniform in time. -/
lemma _root_.PlaneWaveGrid.RegHam.flow_le (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (hcomm : ∀ x, U (H.op x) = H.op (U x)) (u : EuclideanSpace ℂ ι) :
    ‖wMul H.W (U u)‖ ≤ 4 / 3 * (‖u‖ + 2 / H.g ^ 2 * (‖H.op u‖ + 26 * H.Z * H.J0 * ‖u‖)) := by
  have h := H.elliptic_gen (U u)
  rw [← hcomm, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
  exact h

/-- The same, in terms of the weight of `u`. -/
lemma _root_.PlaneWaveGrid.RegHam.flow_le_weight (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (hcomm : ∀ x, U (H.op x) = H.op (U x)) (u : EuclideanSpace ℂ ι) :
    ‖wMul H.W (U u)‖ ≤
      5 / 3 * ‖wMul H.W u‖ + 4 / 3 * (1 + 104 * H.Z * H.J0 / H.g ^ 2) * ‖u‖ := by
  have hg2 : 0 < H.g ^ 2 := by have := H.g_pos; positivity
  have h := H.flow_le U hcomm u
  have hop := H.op_le u
  have h2 : 2 / H.g ^ 2 * (‖H.op u‖ + 26 * H.Z * H.J0 * ‖u‖) ≤
      5 / 4 * ‖wMul H.W u‖ + 104 * H.Z * H.J0 / H.g ^ 2 * ‖u‖ := by
    have h3 : 2 / H.g ^ 2 * (‖H.op u‖ + 26 * H.Z * H.J0 * ‖u‖) ≤
        2 / H.g ^ 2 * (5 * H.g ^ 2 / 8 * ‖wMul H.W u‖ + 52 * H.Z * H.J0 * ‖u‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : 2 / H.g ^ 2 * (5 * H.g ^ 2 / 8 * ‖wMul H.W u‖ + 52 * H.Z * H.J0 * ‖u‖) =
        5 / 4 * ‖wMul H.W u‖ + 104 * H.Z * H.J0 / H.g ^ 2 * ‖u‖ := by
      have hg0 : H.g ≠ 0 := H.g_pos.ne'
      field_simp
      ring
    linarith
  calc ‖wMul H.W (U u)‖ ≤ 4 / 3 * (‖u‖ + 2 / H.g ^ 2 * (‖H.op u‖ + 26 * H.Z * H.J0 * ‖u‖)) := h
    _ ≤ 4 / 3 * (‖u‖ + (5 / 4 * ‖wMul H.W u‖ + 104 * H.Z * H.J0 / H.g ^ 2 * ‖u‖)) := by
        gcongr
    _ = 5 / 3 * ‖wMul H.W u‖ + 4 / 3 * (1 + 104 * H.Z * H.J0 / H.g ^ 2) * ‖u‖ := by ring

end General

/-! ## The grid Hamiltonian -/

section Grid

variable {ν : Type*} [Fintype ν] {eta m : ℕ} (P : RegParticles eta) (D : NucData ν) {gamma : ℝ}
  {κ : Lat3 → ℝ} {g : ℝ}

lemma gridRegHam_op (hgamma : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x) (hg : 0 < g) :
    (gridRegHam (eta := eta) (m := m) (P := P) (D := D) hgamma hκ hg).op =
        Hgrid eta m P D κ g := rfl

lemma gridRegHam_W (hgamma : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x) (hg : 0 < g) :
    (gridRegHam (eta := eta) (m := m) (P := P) (D := D) hgamma hκ hg).W = wM P := rfl

lemma gridRegHam_g (hgamma : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x) (hg : 0 < g) :
    (gridRegHam (eta := eta) (m := m) (P := P) (D := D) hgamma hκ hg).g = g := rfl

lemma gridRegHam_Z (hgamma : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x) (hg : 0 < g) :
    (gridRegHam (eta := eta) (m := m) (P := P) (D := D) hgamma hκ hg).Z = P.maxMass *
        Zc P D gamma := rfl

lemma gridRegHam_J0 (hgamma : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x) (hg : 0 < g) :
    (gridRegHam (eta := eta) (m := m) (P := P) (D := D) hgamma hκ hg).J0 =
      J0g (P.maxMass * Zc P D gamma) g := rfl

/-- The grid propagator `e^{-iH_grid t}` of an even kernel. -/
theorem exists_gridPropagator (hκe : ∀ x, κ (-x) = κ x) :
    ∃ U : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, U 0 x = x) ∧
      (∀ s t x, U (s + t) x = U s (U t x)) ∧
      (∀ x, Continuous fun t => U t x) ∧
      (∀ t x, U t (Hgrid eta m P D κ g x) = Hgrid eta m P D κ g (U t x)) ∧
      (∀ t x, HasDerivAt (fun s => U s x) (-(Complex.I • U t (Hgrid eta m P D κ g x))) t) ∧
      (∀ φ : ℝ → EuclideanSpace ℂ (RCfg eta m),
        (∀ t, HasDerivAt φ (-(Complex.I • Hgrid eta m P D κ g (φ t))) t) → ∀ t, φ t = U t (φ 0)) :=
  PlaneWaveDynamics.exists_finitePropagator (Hgrid_isSymmetric hκe)

end Grid

/-! ## The a priori shell bound -/

/-- `(T+1)² t_r(T; u) ≤ m̄ ‖wM u‖`. -/
lemma sq_mul_norm_high_le_gen {eta m : ℕ} (P : RegParticles eta) (T : ℕ) (r : Fin eta)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ((T : ℝ) + 1) ^ 2 * ‖maskOp (High T r) u‖ ≤ P.maxMass * ‖wMul (wM P) u‖ := by
  have hM := P.maxMass_pos
  have hb : 0 < 1 + ((T : ℝ) + 1) ^ 2 / P.maxMass := by positivity
  have h := norm_maskOp_le_wMul (High T r) (wM P)
    (fun q => le_trans zero_le_one (wM_ge_one P q)) hb (fun q hq => wM_ge_of_high P hq) u
  have hX := norm_nonneg (wMul (wM P) u)
  have hfac : ((T : ℝ) + 1) ^ 2 / (1 + ((T : ℝ) + 1) ^ 2 / P.maxMass) ≤ P.maxMass := by
    rw [div_le_iff₀ hb, mul_add, mul_one, mul_div_cancel₀ _ hM.ne']
    linarith
  calc ((T : ℝ) + 1) ^ 2 * ‖maskOp (High T r) u‖
      ≤ ((T : ℝ) + 1) ^ 2 * (‖wMul (wM P) u‖ / (1 + ((T : ℝ) + 1) ^ 2 / P.maxMass)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = ((T : ℝ) + 1) ^ 2 / (1 + ((T : ℝ) + 1) ^ 2 / P.maxMass) * ‖wMul (wM P) u‖ := by ring
    _ ≤ P.maxMass * ‖wMul (wM P) u‖ := mul_le_mul_of_nonneg_right hfac hX

/-- The mass-weighted weight is at most the total weight. -/
lemma norm_wM_le_wTot {eta m : ℕ} (P : RegParticles eta) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM P) u‖ ≤ ‖wMul wTot u‖ := by
  refine norm_wMul_mono (fun q => le_trans zero_le_one (wM_ge_one P q)) (fun q => ?_) u
  unfold wM wTot
  have : ∀ a ∈ (univ : Finset (Fin eta)), nsq (gl (q a)) / P.mass a ≤ nsq (gl (q a)) :=
    fun a _ => div_le_self (nsq_nonneg _) (P.one_le_mass a)
  linarith [Finset.sum_le_sum this]

end PlaneWaveGridDynamics

end DevGD2
-- END SOURCE dev/DevGD2.lean

-- BEGIN SOURCE dev/DevGD3.lean
-- SHA256 5e63e40a9b7b6c8722a1e8d7eeec274b0d8ff61169fba6bb07c85dfd2ae9e0e8
section DevGD3

/-!
# Grid dynamics: the register as the Galerkin cube of radius `2m`

The register of the grid method is the certificate's cube of radius `2m`, reindexed by
`regUnitary`.  Here we connect the continuum dynamics (states in `ℓ²` of the Fourier coefficients,
`H²` states in weighted coordinates) with the register:

* `regCoeff m x` is the register vector of the cube part `P x` of `x ∈ ℓ²`, and `regEmb m` is
  the zero extension back to `ℓ²` (`regCoeff_regEmb`, `regEmb_regCoeff`, `inner_regEmb_left`);
* the Galerkin compression of the convolution `χ(x_a)` is `galObs` (`regCoeff_convOp`), so that
  `⟪P ψ, χ(x_a) P ψ⟫ = ⟪a, galObs a`⟫ for `a = regCoeff m ψ`;
* the weights: the register weight of a continuum state is bounded by its `H²` norm
  (`norm_wTot_regCoeff_stateMap_le`), and the `H²` norm of the lift of a register vector by its
  register weight (`norm_cubeLift_regUnitary_le`);
* the sup-norm shells of the register are inside the Euclidean tails of the continuum
  (`norm_high_regCoeff_le`);
* the Galerkin compression of the Hamiltonian: `P H u = H_gal (P S u) + P W (1 - P) u` on the
  register (`regCoeff_H_eq`), and the source `P W (1 - P) u` pairs with a register vector `φ` as
  `⟪(1 - P) S u, (1 - P) W l⟫` with `l` the `H²` lift of `φ` (`inner_galSource`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace PlaneWaveGridDynamics

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics

/-! ## Register coefficients and the zero extension -/

section Coeff

variable {eta m : ℕ}

/-- The register coefficients of an `ℓ²` vector: its part in the cube of radius `2m`, reindexed
to the register. -/
noncomputable def regCoeff (m : ℕ) : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →L[ℂ]
    EuclideanSpace ℂ (RCfg eta m) :=
  (regUnitary eta (2 * m)).toLinearIsometry.toContinuousLinearMap.comp (extractCLM (2 * m))

lemma regCoeff_eq (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    regCoeff m x = regUnitary eta (2 * m) (extractCLM (2 * m) x) := rfl

lemma regCoeff_apply (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (q : RCfg eta m) :
    regCoeff m x q = x (liftCfg q) := by
  obtain ⟨p, rfl⟩ := (cfgEquiv eta (2 * m)).surjective q
  rw [regCoeff_eq, regUnitary_apply, liftCfg_cfgEquiv]
  rfl

lemma regUnitary_symm_apply (X : EuclideanSpace ℂ (RCfg eta m))
    (p : FourierConfig eta (FinitePlaneWaveMode (2 * m))) :
    (regUnitary eta (2 * m)).symm X p = X (cfgEquiv eta (2 * m) p) := by
  conv_rhs => rw [← (regUnitary eta (2 * m)).apply_symm_apply X]
  rw [regUnitary_apply]

/-- The zero extension of a register vector to `ℓ²`. -/
noncomputable def regEmb (m : ℕ) :
    EuclideanSpace ℂ (RCfg eta m) →ₗᵢ[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
  (finiteFourierLpIsometry eta (2 * m)).comp (regUnitary eta (2 * m)).symm.toLinearIsometry

lemma regEmb_eq (φ : EuclideanSpace ℂ (RCfg eta m)) :
    regEmb m φ = finiteFourierLpIsometry eta (2 * m) ((regUnitary eta (2 * m)).symm φ) := rfl

lemma regCoeff_regEmb (φ : EuclideanSpace ℂ (RCfg eta m)) : regCoeff m (regEmb m φ) = φ := by
  rw [regCoeff_eq, regEmb_eq, finiteFourierLpIsometry_apply, extract_embed,
    LinearIsometryEquiv.apply_symm_apply]

lemma regEmb_regCoeff (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    regEmb m (regCoeff m x) = molecularH2Truncate (2 * m) x := by
  rw [regCoeff_eq, regEmb_eq, LinearIsometryEquiv.symm_apply_apply, emb_extractCLM]

/-- The zero extension is the adjoint of the register coefficients. -/
lemma inner_regEmb_left (φ : EuclideanSpace ℂ (RCfg eta m))
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    ⟪regEmb m φ, x⟫_ℂ = ⟪φ, regCoeff m x⟫_ℂ := by
  rw [regEmb_eq, inner_emb_left, regCoeff_eq,
    ← LinearIsometryEquiv.inner_map_map (regUnitary eta (2 * m)),
    LinearIsometryEquiv.apply_symm_apply]

lemma regCoeff_truncate (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    regCoeff m (molecularH2Truncate (2 * m) x) = regCoeff m x := by
  rw [regCoeff_eq, regCoeff_eq, extract_truncate]

lemma norm_regCoeff_le (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    ‖regCoeff m x‖ ≤ ‖x‖ := by
  rw [regCoeff_eq, LinearIsometryEquiv.norm_map]
  exact norm_extractCLM_le _ x

lemma norm_regCoeff_of_truncate (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hx : molecularH2Truncate (2 * m) x = x) : ‖regCoeff m x‖ = ‖x‖ := by
  rw [← (regEmb m).norm_map, regEmb_regCoeff, hx]

/-- On the cube, inner products are register inner products. -/
lemma inner_regCoeff (x y : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hx : molecularH2Truncate (2 * m) x = x) :
    ⟪x, y⟫_ℂ = ⟪regCoeff m x, regCoeff m y⟫_ℂ := by
  calc ⟪x, y⟫_ℂ = ⟪regEmb m (regCoeff m x), y⟫_ℂ := by rw [regEmb_regCoeff, hx]
    _ = ⟪regCoeff m x, regCoeff m y⟫_ℂ := inner_regEmb_left _ _

lemma truncate_truncate' (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    molecularH2Truncate (2 * m) (molecularH2Truncate (2 * m) x) = molecularH2Truncate (2 * m) x :=
  truncate_truncate (2 * m) x

end Coeff

/-! ## The cube and the register boxes -/

section Cube

variable {eta m : ℕ}

lemma liftCfg_mem_cube (q : RCfg eta m) : liftCfg q ∈ fourierConfigCube eta (2 * m) := by
  obtain ⟨p, rfl⟩ := (cfgEquiv eta (2 * m)).surjective q
  rw [liftCfg_cfgEquiv]
  exact finiteConfigLatticeIndex_mem_cube eta (2 * m) p

lemma not_mem_cube_of_not_inBox {n : ℕ} {p : FourierConfig eta Lattice3} {a : Fin eta}
    (h : ¬ InBox n (p a)) : p ∉ fourierConfigCube eta n := by
  rw [mem_fourierConfigCube_iff]
  intro hp
  apply h
  intro c
  rw [abs_le]
  exact hp a c

/-- Outside the box of radius `T`, the Euclidean momentum exceeds `T`. -/
lemma lt_sqrt_of_not_inBox {g : ℝ} (hg : 0 < g) {T : ℕ} {x : Lat3} (h : ¬ InBox T x) :
    g * T < g * Real.sqrt (latticeNormSq x) := by
  have h1 := nsq_ge_of_not_inBox h
  have h2 : (T : ℝ) + 1 ≤ Real.sqrt (latticeNormSq x) := Real.le_sqrt_of_sq_le h1
  exact mul_lt_mul_of_pos_left (by linarith) hg

/-- **Shells against tails.** The register shell beyond `T` (sup norm) of the cube part of `x`
is at most the continuum tail of `x` beyond `g T` (Euclidean norm). -/
lemma norm_high_regCoeff_le {g : ℝ} (hg : 0 < g) (T : ℕ) (r : Fin eta)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    ‖maskOp (High T r) (regCoeff m x)‖ ≤ ‖tailMask g (g * T) r x‖ := by
  refine (norm_le_of_pointwise (Y := regCoeff m (tailMask g (g * T) r x)) fun q => ?_).trans
    (norm_regCoeff_le _)
  by_cases h : High T r q
  · have h' : g * T < g * Real.sqrt (latticeNormSq (liftCfg q r)) := lt_sqrt_of_not_inBox hg h
    rw [maskOp_apply_of _ _ h, regCoeff_apply, regCoeff_apply, tailMask_apply, if_pos h', one_mul]
  · rw [maskOp_apply_of_not _ _ h, norm_zero]
    exact norm_nonneg _

end Cube

/-! ## The Galerkin compression of the convolution -/

section Convolution

variable {eta m : ℕ} {c : Lat3 → ℂ}

lemma galObs_apply (a : Fin eta) (hc : Summable fun ν => ‖c ν‖)
    (u : EuclideanSpace ℂ (RCfg eta m)) (q : RCfg eta m) :
    galObs a c u q = ∑' ν, c ν * (if NoWrap a ν q then u (cfgShift a (ofLat ν) q) else 0) := by
  refine ((hasSum_eval (hasSum_galObs a hc) u q).tsum_eq.symm).trans ?_
  refine tsum_congr fun ν => ?_
  rw [smul_apply, PiLp.smul_apply, smul_eq_mul]
  congr 1
  simp only [linCLM, ContinuousLinearMap.coe_comp, Function.comp_apply, maskCLM_apply]
  by_cases h : NoWrap a ν q
  · rw [maskOp_apply_of _ _ h, if_pos h, cycCLM_apply]
  · rw [maskOp_apply_of_not _ _ h, if_neg h]

/-- Without wrap, the register translation is the lattice translation. -/
lemma liftCfg_cfgShift (a : Fin eta) (ν : Lat3) (q : RCfg eta m) (h : NoWrap a ν q) :
    liftCfg (cfgShift a (ofLat ν) q) = liftCfg q + Pi.single a ν := by
  funext b
  by_cases hb : b = a
  · subst hb
    show gl (cfgShift b (ofLat ν) q b) = gl (q b) + (Pi.single b ν : FourierConfig eta Lattice3) b
    rw [cfgShift_self, Pi.single_eq_same]
    exact gl_add_ofLat (q b) ν h
  · show gl (cfgShift a (ofLat ν) q b) = gl (q b) + (Pi.single a ν : FourierConfig eta Lattice3) b
    rw [cfgShift_ne hb, Pi.single_eq_of_ne hb, add_zero]

/-- **The Galerkin compression of `χ(x_a)`** is `galObs`: `P (O (P x)) = galObs (P x)` in
register coordinates. -/
theorem regCoeff_convOp (a : Fin eta) (hc : Summable fun ν => ‖c ν‖)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    regCoeff m (convOp a c (molecularH2Truncate (2 * m) x)) = galObs a c (regCoeff m x) := by
  ext q
  rw [regCoeff_apply, convOp_apply a hc, galObs_apply a hc]
  refine tsum_congr fun ν => ?_
  congr 1
  by_cases h : NoWrap a ν q
  · have hmem : liftCfg q + Pi.single a ν ∈ fourierConfigCube eta (2 * m) := by
      rw [← liftCfg_cfgShift a ν q h]
      exact liftCfg_mem_cube _
    rw [if_pos h, regCoeff_apply, liftCfg_cfgShift a ν q h, molecularH2Truncate_apply,
      cubicLatticeCoeffTruncate_eq_of_mem _ _ _ hmem]
  · have hnot : liftCfg q + Pi.single a ν ∉ fourierConfigCube eta (2 * m) := by
      apply not_mem_cube_of_not_inBox (a := a)
      show ¬ InBox (2 * m) (gl (q a) + (Pi.single a ν : FourierConfig eta Lattice3) a)
      rw [Pi.single_eq_same]
      exact h
    rw [if_neg h, molecularH2Truncate_apply,
        cubicLatticeCoeffTruncate_eq_zero_of_not_mem _ _ _ hnot]

/-- `⟪P x, O P x⟫ = ⟪a, galObs a⟫` for `a = regCoeff m x`. -/
theorem inner_truncate_convOp (a : Fin eta) (hc : Summable fun ν => ‖c ν‖)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    ⟪molecularH2Truncate (2 * m) x, convOp a c (molecularH2Truncate (2 * m) x)⟫_ℂ =
      ⟪regCoeff m x, galObs a c (regCoeff m x)⟫_ℂ := by
  rw [inner_regCoeff _ _ (truncate_truncate' x), regCoeff_convOp a hc, regCoeff_truncate]

end Convolution

/-! ## Weights -/

section Weights

variable {eta m : ℕ}

lemma wTot_eq (q : RCfg eta m) : wTot q = 1 + ∑ a, nsq (gl (q a)) := rfl

lemma h2Weight_liftCfg (g : ℝ) (q : RCfg eta m) :
    molecularFourierH2Weight eta g (liftCfg q) = 1 + g ^ 2 * ∑ a, nsq (gl (q a)) := by
  unfold molecularFourierH2Weight
  rw [Finset.mul_sum]
  rfl

lemma sum_nsq_nonneg (q : RCfg eta m) : 0 ≤ ∑ a, nsq (gl (q a)) :=
  sum_nonneg fun _ _ => nsq_nonneg _

/-- The register weight of a continuum state is at most `(1 + 1/g²)` times its `H²` norm. -/
lemma norm_wTot_regCoeff_stateMap_le {g : ℝ} (hg : 0 < g) (u : MolecularFourierH2 eta) :
    ‖wMul wTot (regCoeff m (molecularH2StateMap eta g u))‖ ≤ (1 + 1 / g ^ 2) * ‖u‖ := by
  have hc : (0 : ℝ) ≤ 1 + 1 / g ^ 2 := by positivity
  have hpt : ∀ q, ‖(wMul wTot (regCoeff m (molecularH2StateMap eta g u))) q‖ ≤
      ‖(((1 + 1 / g ^ 2 : ℝ) : ℂ) • regCoeff m u) q‖ := by
    intro q
    set X := ∑ a, nsq (gl (q a))
    have hX : 0 ≤ X := sum_nsq_nonneg q
    have hw : 0 < molecularFourierH2Weight eta g (liftCfg q) :=
      molecularFourierH2Weight_pos eta g _
    have hW0 : 0 ≤ wTot q := by rw [wTot_eq]; linarith
    have hratio : wTot q / molecularFourierH2Weight eta g (liftCfg q) ≤ 1 + 1 / g ^ 2 := by
      rw [div_le_iff₀ hw, h2Weight_liftCfg, wTot_eq]
      have hg2 : 0 < g ^ 2 := by positivity
      have e : (1 + 1 / g ^ 2) * (1 + g ^ 2 * X) = 1 + X + g ^ 2 * X + 1 / g ^ 2 := by
        field_simp
        ring
      rw [e]
      have : 0 ≤ g ^ 2 * X := by positivity
      have : 0 ≤ 1 / g ^ 2 := by positivity
      linarith
    rw [wMul_apply, regCoeff_apply, molecularH2StateMap_apply, molecularH2Coeff, PiLp.smul_apply,
      smul_eq_mul, regCoeff_apply, norm_mul, norm_mul, norm_div, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hW0, Real.norm_of_nonneg hw.le,
      Real.norm_of_nonneg hc]
    calc wTot q * (‖u (liftCfg q)‖ / molecularFourierH2Weight eta g (liftCfg q))
        = wTot q / molecularFourierH2Weight eta g (liftCfg q) * ‖u (liftCfg q)‖ := by ring
      _ ≤ (1 + 1 / g ^ 2) * ‖u (liftCfg q)‖ :=
          mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
  refine (norm_le_of_pointwise hpt).trans ?_
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (norm_regCoeff_le u) hc

/-- The `H²` lift of a register vector is the zero extension of its weighted version. -/
lemma cubeLift_regUnitary_symm (g : ℝ) (φ : EuclideanSpace ℂ (RCfg eta m)) :
    cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm φ) =
      regEmb m (wMul (fun q => molecularFourierH2Weight eta g (liftCfg q)) φ) := by
  rw [regEmb_eq, finiteFourierLpIsometry_apply]
  show finiteFourierLpEmbed eta (2 * m) (fun p =>
      (molecularFourierH2Weight eta g (finiteConfigLatticeIndex eta (2 * m) p) : ℂ) *
        ((regUnitary eta (2 * m)).symm φ) p) = _
  congr 1
  funext p
  rw [regUnitary_symm_apply, regUnitary_symm_apply, wMul_apply, liftCfg_cfgEquiv]

/-- The `H²` norm of the lift of a register vector is at most `(1 + g²)` times its register
weight. -/
lemma norm_cubeLift_regUnitary_le (g : ℝ) (φ : EuclideanSpace ℂ (RCfg eta m)) :
    ‖cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm φ)‖ ≤ (1 + g ^ 2) * ‖wMul wTot φ‖ := by
  rw [cubeLift_regUnitary_symm, LinearIsometry.norm_map]
  have hc : (0 : ℝ) ≤ 1 + g ^ 2 := by positivity
  have h := norm_wMul_mono (w := fun q => molecularFourierH2Weight eta g (liftCfg q))
    (w' := fun q => (1 + g ^ 2) * wTot q)
    (fun q => (molecularFourierH2Weight_pos eta g _).le)
    (fun q => by
      rw [h2Weight_liftCfg, wTot_eq]
      have hX := sum_nsq_nonneg q
      nlinarith [sq_nonneg g]) φ
  have e : wMul (fun q => (1 + g ^ 2) * wTot q) φ = ((1 + g ^ 2 : ℝ) : ℂ) • wMul wTot φ := by
    ext q
    simp only [wMul_apply, PiLp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc] at h
  exact h

end Weights

/-! ## The Galerkin compression of the Hamiltonian and its source -/

section Source

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (hL : 0 < L)

include hKernel hL in
/-- **Galerkin compression on the register.** `P H u = H_gal (P S u) + P W (1 - P) u`. -/
theorem regCoeff_H_eq (m : ℕ) (u : MolecularFourierH2 eta) :
    regCoeff m (H u) =
      Hgal eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
          (2 * Real.pi / L) (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u)) +
        regCoeff m (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
          (u - molecularH2Truncate (2 * m) u)) := by
  rw [regCoeff_eq, regCoeff_eq, regCoeff_eq, extract_H_eq sys L H hKernel (2 * m) u, map_add,
    Hgal_regUnitary sys m L hL]

include hKernel in
/-- **The Galerkin source against a register vector.** With `l` the `H²` lift of `φ`,
`⟪P W (1 - P) u, φ⟫ = ⟪(1 - P) S u, (1 - P) W l⟫`. -/
theorem inner_galSource (m : ℕ) (u : MolecularFourierH2 eta) (φ : EuclideanSpace ℂ (RCfg eta m)) :
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
  rw [h1, inner_extract_left, ← stateMap_cubeLift g (2 * m) ψ, ← potential_symm sys L H hKernel,
    hSx, inner_sub_truncate_left]

include hKernel in
lemma norm_inner_galSource_le (m : ℕ) (u : MolecularFourierH2 eta)
    (φ : EuclideanSpace ℂ (RCfg eta m)) :
    ‖⟪regCoeff m (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
        (u - molecularH2Truncate (2 * m) u)), φ⟫_ℂ‖ ≤
      ‖molecularH2StateMap eta (2 * Real.pi / L) u -
          molecularH2Truncate (2 * m) (molecularH2StateMap eta (2 * Real.pi / L) u)‖ *
        ‖coulombFourierPotentialH2 sys (2 * Real.pi / L) H
            (cubeLift (2 * Real.pi / L) (2 * m) ((regUnitary eta (2 * m)).symm φ)) -
          molecularH2Truncate (2 * m) (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
            (cubeLift (2 * Real.pi / L) (2 * m) ((regUnitary eta (2 * m)).symm φ)))‖ := by
  rw [inner_galSource sys L H hKernel m u φ]
  exact norm_inner_le_norm _ _

end Source

end PlaneWaveGridDynamics

end DevGD3
-- END SOURCE dev/DevGD3.lean

-- BEGIN SOURCE dev/DevGD4.lean
-- SHA256 e603d79a1130ae84799e377d0c5bd4e24c66f11b0a48eba672eb93cca031b518
section DevGD4

/-!
# Grid dynamics: the observable error of `prop:grid-dyn`

For a periodic Coulomb system, `ψ₀ = S u₀ ∈ D(H²)`, the exact state `ψ(t) = e^{-iHt} ψ₀`, the grid
state `ψ_g(t) = e^{-iH_grid t} P ψ₀` on the register of radius `2m` (`K = g m`, kernel of the class
`𝒦_K`), and the observable `χ(x_a)` (`convOp a χ̂` in the continuum, the collocated operator
`O_g = gridObs a χ̂` on the grid), the proof of `prop:grid-dyn` splits
`⟪ψ, χ ψ⟫ - ⟪ψ_g, O_g ψ_g⟫` with `a(t) = P ψ(t)` and `b(t) = ψ_g(t)` into

* (I) `⟪ψ, χ ψ⟫ - ⟪a, χ a⟫`: the never-projected tail at cutoff `2K` (`lem:chitail`);
* (II) `⟪a, χ a⟫ - ⟪a, O_g a⟫`: the form bound of the collocated observable (`eq:obs-form`);
* (III) `⟪a, O_g a⟫ - ⟪b, O_g b⟫ = ⟪a - b, O_g a⟫ + ⟪b, O_g (a - b)⟫`, two weak pairings of the
  in-band error `e = a - b` (no quadratic expansion), each bounded by duality against the backward
  grid flow (`grid_duality`).  The Duhamel source of `e` is `P W (1 - P) ψ` (the Galerkin source,
  `O(K^{-3})` against a regular state) plus `(D - R) P ψ` (the grid difference, `O(K^{-5/2})` by
  the form bound `Delta_form` with the tails at the threshold `⌊m/4⌋`).

The result (`grid_observable_error`) is an explicit bound which is
`O(K^{-5}) + O(t K^{-5/2}) + O(K^{-5/2}) τ_χ(K) + ‖ψ₀‖² τ_χ^∞(m)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset Set

namespace PlaneWaveGridDynamics

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics

/-! ## Generic algebra of expectations -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For a symmetric `O`, `⟪a, O a⟫ - ⟪b, O b⟫ = ⟪a - b, O a⟫ + ⟪b, O (a - b)⟫`: two weak pairings
of the error `a - b`. -/
lemma norm_inner_sub_inner_le (O : E →L[ℂ] E) (hO : ∀ x y, ⟪O x, y⟫_ℂ = ⟪x, O y⟫_ℂ) (a b : E) :
    ‖⟪a, O a⟫_ℂ - ⟪b, O b⟫_ℂ‖ ≤ ‖⟪a - b, O a⟫_ℂ‖ + ‖⟪a - b, O b⟫_ℂ‖ := by
  have e : ⟪a, O a⟫_ℂ - ⟪b, O b⟫_ℂ = ⟪a - b, O a⟫_ℂ + ⟪b, O (a - b)⟫_ℂ := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  have h2 : ‖⟪b, O (a - b)⟫_ℂ‖ = ‖⟪a - b, O b⟫_ℂ‖ := by
    rw [← hO, ← inner_conj_symm, RCLike.norm_conj]
  rw [e]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [h2]

/-- The projection error of an expectation:
`‖⟪ψ, O ψ⟫ - ⟪ψ - δ, O (ψ - δ)⟫‖ ≤ 2 ‖⟪δ, O ψ⟫‖ + ‖⟪δ, O δ⟫‖`. -/
lemma norm_inner_sub_proj_le (O : E →L[ℂ] E) (hO : ∀ x y, ⟪O x, y⟫_ℂ = ⟪x, O y⟫_ℂ) (ψ δ : E) :
    ‖⟪ψ, O ψ⟫_ℂ - ⟪ψ - δ, O (ψ - δ)⟫_ℂ‖ ≤ 2 * ‖⟪δ, O ψ⟫_ℂ‖ + ‖⟪δ, O δ⟫_ℂ‖ := by
  have e : ⟪ψ, O ψ⟫_ℂ - ⟪ψ - δ, O (ψ - δ)⟫_ℂ = ⟪ψ, O δ⟫_ℂ + ⟪δ, O ψ⟫_ℂ - ⟪δ, O δ⟫_ℂ := by
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  have h1 : ‖⟪ψ, O δ⟫_ℂ‖ = ‖⟪δ, O ψ⟫_ℂ‖ := by
    rw [← hO, ← inner_conj_symm, RCLike.norm_conj]
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := norm_add_le ⟪ψ, O δ⟫_ℂ ⟪δ, O ψ⟫_ℂ
  linarith

end Generic

/-! ## The grid flow -/

section Flow

variable {eta : ℕ} {ν : Type} [Fintype ν]

lemma maxMass_regParticlesOf (sys : CoulombSystem eta ν) :
    (regParticlesOf sys).maxMass = sys.maxMass := rfl

/-- The constant `(4/3)(1 + 104 Z J₀/g²)` of the regularity of grid trajectories
(`RegHam.flow_le_weight` for the grid Hamiltonian, `Z = m̄ Z_c`). -/
noncomputable def gridFlowConst (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  4 / 3 * (1 + 104 * coulombGridCoupling sys L *
    (J0g (coulombGridCoupling sys L) (2 * Real.pi / L) : ℝ) / (2 * Real.pi / L) ^ 2)

lemma gridFlowConst_nonneg (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) :
    0 ≤ gridFlowConst sys L := by
  unfold gridFlowConst
  have := coulombGridCoupling_nonneg sys L hL
  positivity

/-- **Regularity of grid trajectories** (`lem:grid-traj`): a unitary that commutes with the grid
Hamiltonian maps `v` to a state whose mass-weighted weight is at most
`(5/3) ‖wM v‖ + gridFlowConst ‖v‖`. -/
theorem norm_wM_gridFlow_le (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {m : ℕ}
    {κ : Lat3 → ℝ} (hκb : ∀ x, |κ x| ≤ coulombCellAmplitude L * coul x)
    (V : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hcomm : ∀ x, V (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (V x))
    (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM (regParticlesOf sys)) (V v)‖ ≤
      5 / 3 * ‖wMul (wM (regParticlesOf sys)) v‖ + gridFlowConst sys L * ‖v‖ := by
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hg : 0 < 2 * Real.pi / L := by positivity
  exact (gridRegHam (eta := eta) (m := m) (P := regParticlesOf sys)
    (D := (posNucleiOf sys.nuclei).toNucData) hγ hκb hg).flow_le_weight V hcomm v

/-- The backward grid flow of `O_g v`: its mass-weighted weight is at most
`(5/3)((2 + 12 m̄) C_χ X + 14 D'_χ S) + gridFlowConst · C_χ S` when `‖wM v‖ ≤ X` and `‖v‖ ≤ S`
(`D'_χ = momTwo χ`). -/
theorem norm_wM_gridFlow_gridObs_le (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {m : ℕ}
    {κ : Lat3 → ℝ} (hκb : ∀ x, |κ x| ≤ coulombCellAmplitude L * coul x)
    (V : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hcomm : ∀ x, V (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (V x))
    (a : Fin eta) {χ : Lat3 → ℂ} (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (v : EuclideanSpace ℂ (RCfg eta m)) {X S : ℝ}
    (hX : ‖wMul (wM (regParticlesOf sys)) v‖ ≤ X) (hS : ‖v‖ ≤ S) :
    ‖wMul (wM (regParticlesOf sys)) (V (gridObs a χ v))‖ ≤
      5 / 3 * ((2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * X + 14 * momTwo χ * S) +
        gridFlowConst sys L * ((∑' ν, ‖χ ν‖) * S) := by
  have hC : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hD : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hJ := gridFlowConst_nonneg sys hL
  have hM := sys.one_le_maxMass
  have h1 := norm_wM_gridFlow_le sys hL hκb V hcomm (gridObs a χ v)
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

/-! ## Duality on the grid -/

section Grid

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL in
/-- `P H u = H_grid (P S u) + (P W (1 - P) u - Δ (P S u))` on the register (`Δ = R - D`). -/
theorem regCoeff_H_eq_grid (m : ℕ) (κ : Lat3 → ℝ) (u : MolecularFourierH2 eta) :
    regCoeff m (H u) =
      Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L)
          (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u)) +
        (regCoeff m (coulombFourierPotentialH2 sys (2 * Real.pi / L) H
            (u - molecularH2Truncate (2 * m) u)) -
          Delta eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            (coulombCellAmplitude L) κ (regCoeff m
                (molecularH2StateMap eta (2 * Real.pi / L) u))) := by
  rw [regCoeff_H_eq sys L H hKernel hL m u, Hgrid_eq (gamma := coulombCellAmplitude L)]
  abel

include hKernel hL hPeriodic in
/-- **Duality on the grid** (`prop:grid-dyn`, term (III)). Let `a(t) = P ψ(t)` (register
coordinates) and `ψ_g(t) = e^{-iH_grid t} P ψ₀`. For every register vector `w` such that
`U_g(τ) w` has mass-weighted weight at most `W_φ` for every `τ` (in particular along the backward
flow), `|⟪a(t) - ψ_g(t), w⟫|` is at most `t` times
`(η t₂)(η C_tail(M_l) ρ₂) + Z_c (A(s₀, m)(t₄ m̄ W_φ + τ_φ X_a) + 52 m τ_φ t₄)`, with `t₂`, `t₄`
the bounds `tl` of the continuum tails:
the Galerkin source `P W (1 - P) ψ` against the `H²` lift of the flow (tails at `2K`,
`M_l = (1 + g²) m̄ W_φ`), plus the grid difference `Δ = R - D` against the flow (`Delta_form` at the
threshold `s₀ = ⌊m/4⌋`, with the tails `t₄` of `ψ` at `g s₀`, the a priori shell
`τ_φ = m̄ W_φ/(s₀+1)²` of the flow, and the register weight `X_a` of `a`). -/
theorem grid_duality (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ} (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (rho₂ rho₄ Blow Cs Bker : ℝ) (hK₄ : 1 ≤ (2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ))
    (hRho₂ : 0 ≤ rho₂) (hRhoScale₂ : rho₂ ^ 2 * ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) = 1)
    (hRho₄ : 0 ≤ rho₄) (hRhoScale₄ : rho₄ ^ 2 * ((2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ)) = 1)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (w : EuclideanSpace ℂ (RCfg eta m)) (Wφ : ℝ)
    (hW : ∀ τ, ‖wMul (wM (regParticlesOf sys)) (Ug τ w)‖ ≤ Wφ) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB sys L Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
    let tl : ℝ → ℝ → ℝ := fun K ρ =>
      (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    let s₀ : ℕ := m / 4
    let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (coulombCellAmplitude L)
    let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
    let τφ : ℝ := sys.maxMass * Wφ / ((s₀ : ℝ) + 1) ^ 2
    let t₂ : ℝ := tl (g * ((2 * m : ℕ) : ℝ)) rho₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) rho₄
    ‖⟪regCoeff m (U t (molecularH2StateMap eta g u₀)) -
        Ug t (regCoeff m (molecularH2StateMap eta g u₀)), w⟫_ℂ‖ ≤
      ((eta * t₂) * (eta * (Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂)) +
        Zg * (formA s₀ m * (t₄ * (sys.maxMass * Wφ) + τφ * Xa) + 52 * m * (τφ * t₄))) * t := by
  intro g b S0 Ξ₀ Ξ₁ M₀ Ct tl s₀ Zg Xa τφ t₂ t₄
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ b := relB_nonneg sys L Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
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
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM₀
  have htl0 : ∀ K ρ, 0 ≤ ρ → 0 ≤ tl K ρ := by
    intro K ρ hρ
    show 0 ≤ (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    have h1 : 0 ≤ 2 * sys.maxMass / K ^ 2 := div_nonneg (by linarith) (sq_nonneg K)
    exact mul_nonneg h1 (add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hCt₀ hρ))
  have ht₂0 : 0 ≤ t₂ := htl0 _ _ hRho₂
  have ht₄0 : 0 ≤ t₄ := htl0 _ _ hRho₄
  have hZg : 0 ≤ Zg := Zc_nonneg hγ
  have hτφ0 : 0 ≤ τφ := by positivity
  -- the trajectory and its Duhamel equation on the register
  choose u hu1 hu2 using fun s => hgraph s u₀
  have ha : ∀ s, HasDerivAt (fun s => regCoeff m (U s (molecularH2StateMap eta g u₀)))
      (-(Complex.I • (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ g
          (regCoeff m (U s (molecularH2StateMap eta g u₀))) +
        (regCoeff m (coulombFourierPotentialH2 sys g H (u s - molecularH2Truncate (2 * m) (u s))) -
          Delta eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            (coulombCellAmplitude L) κ (regCoeff m (U s (molecularH2StateMap eta g u₀))))))) s := by
    intro s
    have h1 := ((regCoeff (eta := eta) m).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
      (hderiv s u₀)
    refine h1.congr_deriv ?_
    rw [ContinuousLinearMap.coe_restrictScalars', map_neg, map_smul, ← hu2 s,
      regCoeff_H_eq_grid sys L H hKernel hL m κ (u s), hu1 s]
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
    have hT := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC (u s)
    rw [hu1 s, LinearIsometryEquiv.norm_map] at h
    rw [hu1 s, hu2 s, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hT
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    show ‖molecularH2StateMap eta g u₀‖ + 2 * ‖coulombFourierKineticH2 sys g (u s)‖ ≤ S0 + 2 * Ξ₀
    linarith
  -- (i) the Galerkin source against the lift of the flow
  have hi : ‖⟪regCoeff m (coulombFourierPotentialH2 sys g H
      (u s - molecularH2Truncate (2 * m) (u s))),
      φ⟫_ℂ‖ ≤ (eta * t₂) * (eta * (Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂)) := by
    refine (norm_inner_galSource_le sys L H hKernel m (u s) φ).trans ?_
    have hδ : ‖molecularH2StateMap eta g (u s) -
        molecularH2Truncate (2 * m) (molecularH2StateMap eta g (u s))‖ ≤ eta * t₂ := by
      refine (norm_sub_truncate_le hg (2 * m) _).trans ?_
      have htl := fun c => (tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph c
        (g * ((2 * m : ℕ) : ℝ)) rho₂ Blow Cs Bker hK₂ hRho₂ hRhoScale₂ hBlow hCs hBker hK₂2g
        hAmplitude hBkerScale hCsScale u₀ v₀ huv s (u s) (hu1 s) (hu2 s)).2
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
            sum_le_sum fun c _ => potential_tail_le sys L H hKernel Hunit hL hPeriodic c _ rho₂
              Blow Cs Bker _ hK₂ hRho₂ hRhoScale₂ hBlow hCs hBker hMl hK₂2g hAmplitude hBkerScale
              hCsScale _ hl
        _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hΛ0 : 0 ≤ eta * (Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
        (finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hMl) hRho₂)
    exact mul_le_mul hδ hΛ (norm_nonneg _) (by positivity)
  -- (ii) the grid difference against the flow
  have hii : ‖⟪Delta eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) κ (regCoeff m (U s (molecularH2StateMap eta g u₀))), φ⟫_ℂ‖ ≤
      Zg * (formA s₀ m * (t₄ * (sys.maxMass * Wφ) + τφ * Xa) + 52 * m * (τφ * t₄)) := by
    rw [← inner_conj_symm, RCLike.norm_conj]
    have hτu : ∀ r, ‖maskOp (High s₀ r) (regCoeff m
        (U s (molecularH2StateMap eta g u₀)))‖ ≤ t₄ := by
      intro r
      rw [← hu1 s]
      exact (norm_high_regCoeff_le hg s₀ r _).trans (tails_at_time sys L H hKernel Hunit hL
        hPeriodic hC U hgraph r (g * (s₀ : ℝ)) rho₄ Blow Cs Bker hK₄' hRho₄ hRhoScale₄ hBlow hCs
        hBker hK₄2g hAmplitude hBkerScale hCsScale u₀ v₀ huv s (u s) (hu1 s) (hu2 s)).2
    have hτv : ∀ r, ‖maskOp (High s₀ r) φ‖ ≤ τφ := by
      intro r
      have h := sq_mul_norm_high_le_gen (regParticlesOf sys) s₀ r φ
      have hpos : (0 : ℝ) < ((s₀ : ℝ) + 1) ^ 2 := by positivity
      show ‖maskOp (High s₀ r) φ‖ ≤ sys.maxMass * Wφ / ((s₀ : ℝ) + 1) ^ 2
      rw [le_div_iff₀ hpos]
      have h2 := mul_le_mul_of_nonneg_left hφW (by linarith : (0 : ℝ) ≤ sys.maxMass)
      have h3 : ((s₀ : ℝ) + 1) ^ 2 * ‖maskOp (High s₀ r) φ‖ ≤
          sys.maxMass * ‖wMul (wM (regParticlesOf sys)) φ‖ := h
      linarith
    have hD := Delta_form (P := regParticlesOf sys) (D := (posNucleiOf sys.nuclei).toNucData) hγ
      (by omega : 1 ≤ s₀) hs₀m hκ.gridKernel (regCoeff m (U s (molecularH2StateMap eta g u₀))) φ
      ht₄0 hτφ0 hτu hτv
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

include hKernel hL hPeriodic in
/-- **Observable error on the grid** (`prop:grid-dyn`, Fourier side, explicit form). For
`ψ₀ = S u₀ ∈ D(H²)` (`H u₀ = S v₀`), the exact state `ψ(t) = U t ψ₀`, the grid state
`ψ_g(t) = e^{-iH_grid t} P ψ₀` on the register of radius `2m` (`m ≥ 8`, `K = g m`, a real, even
kernel of the class `𝒦_K`), and a real `χ` with `Σ |χ̂| < ∞` and `D'_χ = Σ |ν|² |χ̂(ν)| < ∞`,
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫|` is at most
`2 δ (C_χ t₁ + τ_χ ‖ψ₀‖ + ‖O‖ δ) + ‖O‖ δ²` (term (I), `δ = η t₂`)
`+ C_χ t₁² + τ_χ^∞(m) ‖ψ₀‖²` (term (II))
`+ 2 t B_d` (term (III), `grid_duality` with the regularity budget `W` of the backward flows),
where `t₁, t₂, t₄` are the bounds `tl` of the continuum tails at `K`, `2K` and `g ⌊m/4⌋`,
`τ_χ = Σ_{g|ν| > K} |χ̂(ν)|` and `τ_χ^∞(m) = Σ_{‖ν‖∞ > m} |χ̂(ν)|`. -/
theorem grid_observable_error (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ} (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (rho₁ rho₂ rho₄ Blow Cs Bker : ℝ) (hK₄ : 1 ≤ (2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ))
    (hRho₁ : 0 ≤ rho₁) (hRhoScale₁ : rho₁ ^ 2 * ((2 * Real.pi / L) * (m : ℝ)) = 1)
    (hRho₂ : 0 ≤ rho₂) (hRhoScale₂ : rho₂ ^ 2 * ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) = 1)
    (hRho₄ : 0 ≤ rho₄) (hRhoScale₄ : rho₄ ^ 2 * ((2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ)) = 1)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (a : Fin eta) (χ : Lattice3 → ℂ) (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (hreal : ∀ ν, χ (-ν) = conj (χ ν))
    {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB sys L Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
    let tl : ℝ → ℝ → ℝ := fun K ρ =>
      (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    let s₀ : ℕ := m / 4
    let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (coulombCellAmplitude L)
    let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
    let CO : ℝ := ‖convOp (eta := eta) a χ‖
    let Cχ : ℝ := ∑' ν, ‖χ ν‖
    let τχ : ℝ := ∑' ν, if g * (m : ℝ) < g * Real.sqrt (latticeNormSq ν) then ‖χ ν‖ else 0
    let cJ : ℝ := gridFlowConst sys L
    let Xb : ℝ := 5 / 3 * Xa + cJ * S0
    let W : ℝ := 5 / 3 * ((2 + 12 * sys.maxMass) * Cχ * Xb + 14 * momTwo χ * S0) + cJ * (Cχ * S0)
    let τφ : ℝ := sys.maxMass * W / ((s₀ : ℝ) + 1) ^ 2
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
  intro g b S0 Ξ₀ Ξ₁ M₀ Ct tl s₀ Zg Xa CO Cχ τχ cJ Xb W τφ t₁ t₂ t₄ δ Bd ψg
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ b := relB_nonneg sys L Hunit hC
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
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM₀
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
  have hcJ : 0 ≤ cJ := gridFlowConst_nonneg sys hL
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
    have h := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u
    rw [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
    exact h
  have hu₀_le : ‖u₀‖ ≤ M₀ :=
    hnorm_le u₀ rfl (kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u₀)
  -- the tails at `K` and `2K`
  have ht₁ : ∀ c, ‖tailMask g (g * (m : ℝ)) c (molecularH2StateMap eta g u)‖ ≤ t₁ := fun c =>
    (tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph c (g * (m : ℝ)) rho₁ Blow Cs
      Bker hK₁ hRho₁ hRhoScale₁ hBlow hCs hBker hK₁2g hAmplitude hBkerScale hCsScale u₀ v₀ huv t u
      hu1 hu2).2
  have ht₂ : ∀ c, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖ ≤ t₂ :=
    fun c => (tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph c
      (g * ((2 * m : ℕ) : ℝ)) rho₂ Blow Cs Bker hK₂ hRho₂ hRhoScale₂ hBlow hCs hBker hK₂2g
      hAmplitude hBkerScale hCsScale u₀ v₀ huv t u hu1 hu2).2
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
    refine (norm_wM_gridFlow_le sys hL hκ.bound (Ug t) (hgcomm t) _).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left ha₀ (by norm_num))
      (mul_le_mul_of_nonneg_left haS₀ hcJ)
  have hbS : ‖ψg‖ ≤ S0 := by
    show ‖Ug t (regCoeff m (molecularH2StateMap eta g u₀))‖ ≤ S0
    rw [LinearIsometryEquiv.norm_map]
    exact haS₀
  have hWa : ∀ τ, ‖wMul (wM (regParticlesOf sys))
      (Ug τ (gridObs a χ (regCoeff m (molecularH2StateMap eta g u))))‖ ≤ W := fun τ =>
    norm_wM_gridFlow_gridObs_le sys hL hκ.bound (Ug τ) (hgcomm τ) a hχ1 hχ2 _ haT hA
  have hWb : ∀ τ, ‖wMul (wM (regParticlesOf sys)) (Ug τ (gridObs a χ ψg))‖ ≤ W := fun τ =>
    norm_wM_gridFlow_gridObs_le sys hL hκ.bound (Ug τ) (hgcomm τ) a hχ1 hχ2 _ hbT hbS
  have he : regCoeff m (molecularH2StateMap eta g u) - ψg =
      regCoeff m (U t (molecularH2StateMap eta g u₀)) -
        Ug t (regCoeff m (molecularH2StateMap eta g u₀)) := by
    rw [hψ]
  have hd1 : ‖⟪regCoeff m (molecularH2StateMap eta g u) - ψg,
      gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ‖ ≤ Bd * t := by
    have h := grid_duality sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph hderiv m hm hκ Ug hg0
      hgcomm hgderiv rho₂ rho₄ Blow Cs Bker hK₄ hRho₂ hRhoScale₂ hRho₄ hRhoScale₄ hBlow hCs hBker
      hAmplitude hBkerScale hCsScale u₀ v₀ huv _ W hWa ht
    rw [he]
    exact h
  have hd2 : ‖⟪regCoeff m (molecularH2StateMap eta g u) - ψg, gridObs a χ ψg⟫_ℂ‖ ≤ Bd * t := by
    have h := grid_duality sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph hderiv m hm hκ Ug hg0
      hgcomm hgderiv rho₂ rho₄ Blow Cs Bker hK₄ hRho₂ hRhoScale₂ hRho₄ hRhoScale₄ hBlow hCs hBker
      hAmplitude hBkerScale hCsScale u₀ v₀ huv _ W hWb ht
    rw [he]
    exact h
  have hIII : ‖⟪regCoeff m (molecularH2StateMap eta g u),
        gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ - ⟪ψg, gridObs a χ ψg⟫_ℂ‖ ≤
      2 * (Bd * t) :=
    (norm_inner_sub_inner_le (gridObs a χ) hOg _ _).trans (by linarith)
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
  refine (norm_add₃_le).trans ?_
  linarith

end Grid

end PlaneWaveGridDynamics

end DevGD4
-- END SOURCE dev/DevGD4.lean

-- BEGIN SOURCE dev/DevGD5.lean
-- SHA256 d02480ee18e3a498a2ef34d609c47fd2a0cc10dd64e1b72dbaa681d2846550fd
section DevGD5

/-!
# Grid dynamics: the rates of `prop:grid-dyn`

With `ρ = K^{-1/2}`, `K = g m`, and the tails of the continuum taken at `K`, `2K` and `g ⌊m/4⌋`
(with their own `ρ`'s), the explicit bound of `grid_observable_error` is at most

  `A₁ K^{-5} + A₂ t K^{-5/2} + A₃ K^{-5/2} τ_χ(K) + ‖ψ₀‖² τ_χ^∞(m)`

with constants `(A₁, A₂, A₃) = gridConsts` that depend on the system, the cell, `χ` and the norms
`‖ψ₀‖, ‖H ψ₀‖, ‖H² ψ₀‖`, but not on `m` (that is `K`) or `t` (`grid_observable_rate`).  The only
conditions are `m ≥ 8` and `K ≥ 8`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset Set

namespace PlaneWaveGridDynamics

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics

/-! ## Arithmetic of the rates -/

section Arith

/-- The tail `(2m̄/K'²)((2m̄/K'²) Ξ₁ + C ρ')` at a threshold `K' ≥ K/c` (with `ρ'² K' = 1`) is at
most `2m̄c² (2m̄c² Ξ₁ + c C) ρ⁵`, `ρ = K^{-1/2}`. -/
lemma tl_rate {mm Ξ₁ C K K' ρ ρ' c : ℝ} (hmm : 0 ≤ mm) (hΞ : 0 ≤ Ξ₁) (hC : 0 ≤ C) (hc : 1 ≤ c)
    (hρ : 0 ≤ ρ) (hρK : ρ ^ 2 * K = 1) (hK : 1 ≤ K) (hK' : K ≤ c * K') (hρ' : 0 ≤ ρ')
    (hρK' : ρ' ^ 2 * K' = 1) :
    (2 * mm / K' ^ 2) * ((2 * mm / K' ^ 2) * Ξ₁ + C * ρ') ≤
      2 * mm * c ^ 2 * (2 * mm * c ^ 2 * Ξ₁ + c * C) * ρ ^ 5 := by
  have hKpos : 0 < K := by linarith
  have hc0 : 0 < c := by linarith
  have hK'pos : 0 < K' := by
    by_contra h
    push Not at h
    have : c * K' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0.le h
    linarith
  have hρ2 : ρ ^ 2 = 1 / K := by
    field_simp
    linarith
  have h1 : 1 / K' ≤ c / K := by
    rw [div_le_div_iff₀ hK'pos hKpos]
    linarith
  have hinv : 1 / K' ^ 2 ≤ c ^ 2 * ρ ^ 4 := by
    have h2 : (1 / K') ^ 2 ≤ (c / K) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have e1 : (1 / K') ^ 2 = 1 / K' ^ 2 := by ring
    have e2 : (c / K) ^ 2 = c ^ 2 * ρ ^ 4 := by
      rw [show ρ ^ 4 = (ρ ^ 2) ^ 2 by ring, hρ2]
      ring
    rw [← e1, ← e2]
    exact h2
  have hρ'le : ρ' ≤ c * ρ := by
    have h3 : ρ' ^ 2 ≤ (c * ρ) ^ 2 := by
      have e3 : ρ' ^ 2 = 1 / K' := by
        field_simp
        linarith
      rw [e3, mul_pow, hρ2]
      have h4 : c / K ≤ c ^ 2 * (1 / K) := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (by nlinarith) hKpos.le
      linarith
    exact (pow_le_pow_iff_left₀ hρ' (by positivity) two_ne_zero).mp h3
  have hρ1 : ρ ≤ 1 := by
    have h5 : ρ ^ 2 ≤ 1 := by
      rw [hρ2, div_le_one hKpos]
      exact hK
    nlinarith
  have hρ4 : ρ ^ 4 ≤ ρ := by
    calc ρ ^ 4 = ρ * ρ ^ 3 := by ring
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hρ hρ1) hρ
      _ = ρ := mul_one ρ
  have hA : 2 * mm / K' ^ 2 ≤ 2 * mm * c ^ 2 * ρ ^ 4 := by
    calc 2 * mm / K' ^ 2 = 2 * mm * (1 / K' ^ 2) := by ring
      _ ≤ 2 * mm * (c ^ 2 * ρ ^ 4) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * mm * c ^ 2 * ρ ^ 4 := by ring
  have hA0 : 0 ≤ 2 * mm / K' ^ 2 := by positivity
  have hB : (2 * mm / K' ^ 2) * Ξ₁ + C * ρ' ≤ (2 * mm * c ^ 2 * Ξ₁ + c * C) * ρ := by
    have h6 : (2 * mm / K' ^ 2) * Ξ₁ ≤ 2 * mm * c ^ 2 * Ξ₁ * ρ := by
      calc (2 * mm / K' ^ 2) * Ξ₁ ≤ (2 * mm * c ^ 2 * ρ ^ 4) * Ξ₁ :=
            mul_le_mul_of_nonneg_right hA hΞ
        _ = 2 * mm * c ^ 2 * Ξ₁ * ρ ^ 4 := by ring
        _ ≤ 2 * mm * c ^ 2 * Ξ₁ * ρ := mul_le_mul_of_nonneg_left hρ4 (by positivity)
    have h7 : C * ρ' ≤ c * C * ρ := by
      calc C * ρ' ≤ C * (c * ρ) := mul_le_mul_of_nonneg_left hρ'le hC
        _ = c * C * ρ := by ring
    have e : (2 * mm * c ^ 2 * Ξ₁ + c * C) * ρ = 2 * mm * c ^ 2 * Ξ₁ * ρ + c * C * ρ := by ring
    rw [e]
    exact add_le_add h6 h7
  have hB0 : 0 ≤ (2 * mm / K' ^ 2) * Ξ₁ + C * ρ' := by positivity
  calc (2 * mm / K' ^ 2) * ((2 * mm / K' ^ 2) * Ξ₁ + C * ρ')
      ≤ (2 * mm * c ^ 2 * ρ ^ 4) * ((2 * mm * c ^ 2 * Ξ₁ + c * C) * ρ) :=
        mul_le_mul hA hB hB0 (by positivity)
    _ = 2 * mm * c ^ 2 * (2 * mm * c ^ 2 * Ξ₁ + c * C) * ρ ^ 5 := by ring

/-- The form constant at the threshold `⌊m/4⌋`: `A(⌊m/4⌋, m) ≤ 4 √(5512 g) ρ` when
`ρ² g m = 1` and `m ≥ 8`. -/
lemma formA_rate {g ρ : ℝ} {m : ℕ} (hg : 0 < g) (hρ : 0 ≤ ρ) (hm : 8 ≤ m)
    (hρK : ρ ^ 2 * (g * (m : ℝ)) = 1) :
    formA (m / 4) m ≤ 4 * Real.sqrt (5512 * g) * ρ := by
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hs0 : (0 : ℝ) < ((m / 4 : ℕ) : ℝ) := by
    have : 0 < m / 4 := by omega
    exact_mod_cast this
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hX : 0 ≤ g * ρ ^ 2 := by positivity
  have hkey : Real.sqrt (5512 * g * ρ ^ 2) = Real.sqrt (5512 * g) * ρ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hρ]
  have h1 : Real.sqrt (1378 / (2 * ((m / 4 : ℕ) : ℝ))) ≤ Real.sqrt (5512 * g * ρ ^ 2) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ g * ρ ^ 2 * (8 * ((m / 4 : ℕ) : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hs hX
      nlinarith
    nlinarith
  have h2 : Real.sqrt (1378 / (m : ℝ)) ≤ Real.sqrt (5512 * g * ρ ^ 2) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hm0]
    nlinarith
  unfold formA
  rw [hkey] at h1 h2
  linarith

/-- `1/(⌊m/4⌋ + 1)² ≤ 64 g² ρ⁴` and `m/(⌊m/4⌋ + 1)² ≤ 64 g ρ²` when `ρ² g m = 1`, `m ≥ 8`. -/
lemma shell_rate {g ρ : ℝ} {m : ℕ} (hg : 0 < g) (hm : 8 ≤ m)
    (hρK : ρ ^ 2 * (g * (m : ℝ)) = 1) :
    1 / (((m / 4 : ℕ) : ℝ) + 1) ^ 2 ≤ 64 * g ^ 2 * ρ ^ 4 ∧
      (m : ℝ) / (((m / 4 : ℕ) : ℝ) + 1) ^ 2 ≤ 64 * g * ρ ^ 2 := by
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hs0 : (0 : ℝ) ≤ ((m / 4 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) < (((m / 4 : ℕ) : ℝ) + 1) ^ 2 := by positivity
  have hX : 0 ≤ g * ρ ^ 2 := by positivity
  have hY : 1 ≤ g * ρ ^ 2 * (8 * (((m / 4 : ℕ) : ℝ) + 1)) := by
    have h := mul_le_mul_of_nonneg_left (show (m : ℝ) ≤ 8 * (((m / 4 : ℕ) : ℝ) + 1) by linarith) hX
    nlinarith
  constructor
  · rw [div_le_iff₀ hp]
    have h2 : 1 ≤ (g * ρ ^ 2 * (8 * (((m / 4 : ℕ) : ℝ) + 1))) ^ 2 := by nlinarith
    nlinarith
  · rw [div_le_iff₀ hp]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h3 : (m : ℝ) ^ 2 ≤ 64 * (((m / 4 : ℕ) : ℝ) + 1) ^ 2 := by nlinarith
    have h4 : g * ρ ^ 2 * (m : ℝ) ^ 2 ≤ g * ρ ^ 2 * (64 * (((m / 4 : ℕ) : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left h3 hX
    have e : g * ρ ^ 2 * (m : ℝ) ^ 2 = (m : ℝ) := by
      have : g * ρ ^ 2 * (m : ℝ) = 1 := by linarith
      calc g * ρ ^ 2 * (m : ℝ) ^ 2 = (g * ρ ^ 2 * (m : ℝ)) * (m : ℝ) := by ring
        _ = (m : ℝ) := by rw [this, one_mul]
    nlinarith

/-- Terms (I) and (II): `≤ A₁ ρ¹⁰ + A₃ ρ⁵ τ_χ + ‖ψ₀‖² τ_χ^∞`. -/
lemma rate_arith_I {η δ t₁ t₂ τ₁ Cχ CO τχ S0 sT ρ : ℝ} (hη : 0 ≤ η) (hτ₁ : 0 ≤ τ₁)
    (hδ : δ = η * t₂) (ht₁ : t₁ ≤ τ₁ * ρ ^ 5) (ht₂ : t₂ ≤ τ₁ * ρ ^ 5) (ht₁0 : 0 ≤ t₁)
    (ht₂0 : 0 ≤ t₂) (hCχ : 0 ≤ Cχ) (hCO : 0 ≤ CO) (hτχ : 0 ≤ τχ) (hS0 : 0 ≤ S0) (hρ : 0 ≤ ρ) :
    (2 * (δ * (Cχ * t₁ + τχ * S0 + CO * δ)) + CO * δ ^ 2) + (Cχ * (t₁ * t₁) + sT * (S0 * S0)) ≤
      (2 * (η * τ₁) * (Cχ * τ₁ + CO * (η * τ₁)) + CO * (η * τ₁) ^ 2 + Cχ * τ₁ ^ 2) * ρ ^ 10 +
        2 * (η * τ₁) * S0 * ρ ^ 5 * τχ + S0 ^ 2 * sT := by
  have hρ5 : 0 ≤ ρ ^ 5 := by positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδ' : δ ≤ (η * τ₁) * ρ ^ 5 := by
    rw [hδ]
    calc η * t₂ ≤ η * (τ₁ * ρ ^ 5) := mul_le_mul_of_nonneg_left ht₂ hη
      _ = (η * τ₁) * ρ ^ 5 := by ring
  have hin : Cχ * t₁ + τχ * S0 + CO * δ ≤ Cχ * (τ₁ * ρ ^ 5) + τχ * S0 + CO * ((η * τ₁) * ρ ^ 5) :=
    add_le_add (add_le_add (mul_le_mul_of_nonneg_left ht₁ hCχ) le_rfl)
      (mul_le_mul_of_nonneg_left hδ' hCO)
  have h1 : δ * (Cχ * t₁ + τχ * S0 + CO * δ) ≤
      ((η * τ₁) * ρ ^ 5) * (Cχ * (τ₁ * ρ ^ 5) + τχ * S0 + CO * ((η * τ₁) * ρ ^ 5)) :=
    mul_le_mul hδ' hin (by positivity) (by positivity)
  have h2 : CO * δ ^ 2 ≤ CO * ((η * τ₁) * ρ ^ 5) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0 hδ' 2) hCO
  have h3 : Cχ * (t₁ * t₁) ≤ Cχ * ((τ₁ * ρ ^ 5) * (τ₁ * ρ ^ 5)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul ht₁ ht₁ ht₁0 (by positivity)) hCχ
  have e : 2 * (((η * τ₁) * ρ ^ 5) * (Cχ * (τ₁ * ρ ^ 5) + τχ * S0 + CO * ((η * τ₁) * ρ ^ 5))) +
      CO * ((η * τ₁) * ρ ^ 5) ^ 2 + (Cχ * ((τ₁ * ρ ^ 5) * (τ₁ * ρ ^ 5)) + sT * (S0 * S0)) =
      (2 * (η * τ₁) * (Cχ * τ₁ + CO * (η * τ₁)) + CO * (η * τ₁) ^ 2 + Cχ * τ₁ ^ 2) * ρ ^ 10 +
        2 * (η * τ₁) * S0 * ρ ^ 5 * τχ + S0 ^ 2 * sT := by ring
  linarith

/-- Term (III): `2 t B_d ≤ A₂ t ρ⁵`. -/
lemma rate_arith_III {η t₂ τ₁ ρ ρ₂ CtL Zg fA cF t₄ β₄ mm W τφ Xa g m t : ℝ} (hη : 0 ≤ η)
    (hτ₁ : 0 ≤ τ₁) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (ht₂ : t₂ ≤ τ₁ * ρ ^ 5)
    (hρ₂ : ρ₂ ≤ ρ) (hρ₂0 : 0 ≤ ρ₂) (hCtL : 0 ≤ CtL) (hZg : 0 ≤ Zg) (hfA : fA ≤ cF * ρ)
    (hfA0 : 0 ≤ fA) (ht₄ : t₄ ≤ β₄ * ρ ^ 5) (ht₄0 : 0 ≤ t₄) (hmW : 0 ≤ mm * W)
    (hτφ : τφ ≤ 64 * g ^ 2 * ρ ^ 4 * (mm * W)) (hτφ0 : 0 ≤ τφ)
    (hmτ : m * τφ ≤ 64 * g * ρ ^ 2 * (mm * W)) (hXa : 0 ≤ Xa) (hg : 0 ≤ g) (ht : 0 ≤ t)
    (hβ₄ : 0 ≤ β₄) (hcF0 : 0 ≤ cF) :
    2 * (((η * t₂) * (η * (CtL * ρ₂)) +
        Zg * (fA * (t₄ * (mm * W) + τφ * Xa) + 52 * m * (τφ * t₄))) * t) ≤
      2 * (η * (η * τ₁) * CtL + Zg * (mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)) *
        t * ρ ^ 5 := by
  have hcF : 0 ≤ cF * ρ := hfA0.trans hfA
  have hρ5 : 0 ≤ ρ ^ 5 := by positivity
  have hρ6 : ρ ^ 6 ≤ ρ ^ 5 := pow_le_pow_of_le_one hρ hρ1 (by norm_num)
  have hρ7 : ρ ^ 7 ≤ ρ ^ 5 := pow_le_pow_of_le_one hρ hρ1 (by norm_num)
  -- the Galerkin source
  have hG : (η * t₂) * (η * (CtL * ρ₂)) ≤ η * (η * τ₁) * CtL * ρ ^ 5 := by
    have h1 : η * t₂ ≤ η * (τ₁ * ρ ^ 5) := mul_le_mul_of_nonneg_left ht₂ hη
    have h2 : η * (CtL * ρ₂) ≤ η * (CtL * ρ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hρ₂ hCtL) hη
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : η * (τ₁ * ρ ^ 5) * (η * (CtL * ρ)) = η * (η * τ₁) * CtL * ρ ^ 6 := by ring
    have h5 : η * (η * τ₁) * CtL * ρ ^ 6 ≤ η * (η * τ₁) * CtL * ρ ^ 5 :=
      mul_le_mul_of_nonneg_left hρ6 (by positivity)
    linarith
  -- the grid difference
  have hD1 : fA * (t₄ * (mm * W) + τφ * Xa) ≤
      (mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa) * ρ ^ 5 := by
    have h1 : t₄ * (mm * W) + τφ * Xa ≤ β₄ * ρ ^ 5 * (mm * W) + 64 * g ^ 2 * ρ ^ 4 *
        (mm * W) * Xa :=
      add_le_add (mul_le_mul_of_nonneg_right ht₄ hmW) (mul_le_mul_of_nonneg_right hτφ hXa)
    have h2 := mul_le_mul hfA h1 (by positivity) hcF
    have e : cF * ρ * (β₄ * ρ ^ 5 * (mm * W) + 64 * g ^ 2 * ρ ^ 4 * (mm * W) * Xa) =
        (mm * W) * (cF * β₄) * ρ ^ 6 + (mm * W) * (64 * cF * g ^ 2 * Xa) * ρ ^ 5 := by ring
    have h3 : (mm * W) * (cF * β₄) * ρ ^ 6 ≤ (mm * W) * (cF * β₄) * ρ ^ 5 :=
      mul_le_mul_of_nonneg_left hρ6 (by positivity)
    have e2 : (mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa) * ρ ^ 5 =
        (mm * W) * (cF * β₄) * ρ ^ 5 + (mm * W) * (64 * cF * g ^ 2 * Xa) * ρ ^ 5 := by ring
    linarith
  have hD2 : 52 * m * (τφ * t₄) ≤ (mm * W) * (3328 * g * β₄) * ρ ^ 5 := by
    have h1 : 52 * m * (τφ * t₄) = 52 * (m * τφ) * t₄ := by ring
    have h2 : 52 * (m * τφ) * t₄ ≤ 52 * (64 * g * ρ ^ 2 * (mm * W)) * (β₄ * ρ ^ 5) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hmτ (by norm_num)) ht₄ ht₄0 (by positivity)
    have e : 52 * (64 * g * ρ ^ 2 * (mm * W)) * (β₄ * ρ ^ 5) = (mm * W) *
        (3328 * g * β₄) * ρ ^ 7 := by
      ring
    have h3 : (mm * W) * (3328 * g * β₄) * ρ ^ 7 ≤ (mm * W) * (3328 * g * β₄) * ρ ^ 5 :=
      mul_le_mul_of_nonneg_left hρ7 (by positivity)
    linarith
  have hB : (η * t₂) * (η * (CtL * ρ₂)) + Zg * (fA * (t₄ * (mm * W) + τφ * Xa) + 52 * m * (τφ * t₄))
      ≤ (η * (η * τ₁) * CtL + Zg * (mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)) *
        ρ ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left (add_le_add hD1 hD2) hZg
    have e : Zg * ((mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa) * ρ ^ 5 +
        (mm * W) * (3328 * g * β₄) * ρ ^ 5) =
        Zg * (mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄) * ρ ^ 5 := by ring
    have e2 : (η * (η * τ₁) * CtL + Zg * (mm * W) *
        (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)) *
        ρ ^ 5 = η * (η * τ₁) * CtL * ρ ^ 5 +
          Zg * (mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄) * ρ ^ 5 := by ring
    linarith
  have h := mul_le_mul_of_nonneg_right hB ht
  have e : (η * (η * τ₁) * CtL + Zg * (mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)) *
      ρ ^ 5 * t = (η * (η * τ₁) * CtL + Zg * (mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa +
        3328 * g * β₄)) * t * ρ ^ 5 := by ring
  linarith

/-- **The rates of `prop:grid-dyn`.** The explicit bound of `grid_observable_error`, at
`ρ = K^{-1/2}` (`K = g m`) and `ρ₂ = (2K)^{-1/2}`, `ρ₄ = (g⌊m/4⌋)^{-1/2}`, is at most
`A₁ K^{-5} + A₂ t K^{-5/2} + A₃ K^{-5/2} τ_χ + S0² τ^∞` for `m ≥ 8` and `K ≥ 8`. -/
lemma grid_rate_arith {η mm Ξ₁ C₀ g t S0 sT Cχ CO τχ Zg Xa W : ℝ} {m : ℕ} {Ct : ℝ → ℝ}
    (hη : 0 ≤ η) (hmm : 1 ≤ mm) (hΞ₁ : 0 ≤ Ξ₁) (hC₀ : 0 ≤ C₀) (hg : 0 < g) (hm : 8 ≤ m)
    (hK : 8 ≤ g * m) (ht : 0 ≤ t) (hS0 : 0 ≤ S0) (hCχ : 0 ≤ Cχ) (hCO : 0 ≤ CO)
    (hτχ : 0 ≤ τχ) (hZg : 0 ≤ Zg) (hXa : 0 ≤ Xa) (hW : 0 ≤ W) (hCt : ∀ M, 0 ≤ M → 0 ≤ Ct M) :
    let K : ℝ := g * m
    let tl : ℝ → ℝ → ℝ := fun K ρ => (2 * mm / K ^ 2) * ((2 * mm / K ^ 2) * Ξ₁ + C₀ * ρ)
    let ρ : ℝ := Real.sqrt (1 / K)
    let ρ₂ : ℝ := Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))
    let ρ₄ : ℝ := Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))
    let s₀ : ℕ := m / 4
    let τφ : ℝ := mm * W / ((s₀ : ℝ) + 1) ^ 2
    let t₁ : ℝ := tl (g * (m : ℝ)) ρ
    let t₂ : ℝ := tl (g * ((2 * m : ℕ) : ℝ)) ρ₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) ρ₄
    let δ : ℝ := η * t₂
    let Bd : ℝ := (η * t₂) * (η * (Ct ((1 + g ^ 2) * (mm * W)) * ρ₂)) +
      Zg * (formA s₀ m * (t₄ * (mm * W) + τφ * Xa) + 52 * m * (τφ * t₄))
    let τ₁ : ℝ := 2 * mm * (2 * mm * Ξ₁ + C₀)
    let β₄ : ℝ := 128 * mm * (128 * mm * Ξ₁ + 8 * C₀)
    let δ₁ : ℝ := η * τ₁
    let cF : ℝ := 4 * Real.sqrt (5512 * g)
    (2 * (δ * (Cχ * t₁ + τχ * S0 + CO * δ)) + CO * δ ^ 2) + (Cχ * (t₁ * t₁) + sT * (S0 * S0)) +
        2 * (Bd * t) ≤
      (2 * δ₁ * (Cχ * τ₁ + CO * δ₁) + CO * δ₁ ^ 2 + Cχ * τ₁ ^ 2) * (1 / K) ^ 5 +
        2 * (η * δ₁ * Ct ((1 + g ^ 2) * (mm * W)) +
          Zg * (mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)) * t *
          Real.sqrt (1 / K) ^ 5 +
        2 * δ₁ * S0 * Real.sqrt (1 / K) ^ 5 * τχ + S0 ^ 2 * sT := by
  intro K tl ρ ρ₂ ρ₄ s₀ τφ t₁ t₂ t₄ δ Bd τ₁ β₄ δ₁ cF
  have hmm0 : 0 ≤ mm := by linarith
  have hKpos : 0 < K := by show 0 < g * (m : ℝ); linarith
  have hK1 : 1 ≤ K := by show 1 ≤ g * (m : ℝ); linarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρK : ρ ^ 2 * K = 1 := by
    show Real.sqrt (1 / K) ^ 2 * K = 1
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hρ2 : ρ ^ 2 = 1 / K := Real.sq_sqrt (by positivity)
  have hρ1 : ρ ≤ 1 := by
    have h5 : ρ ^ 2 ≤ 1 := by
      rw [hρ2, div_le_one hKpos]
      exact hK1
    nlinarith
  have hρK' : ρ ^ 2 * (g * (m : ℝ)) = 1 := hρK
  -- the cube `2m` and the threshold `⌊m/4⌋`
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hK₂pos : 0 < g * ((2 * m : ℕ) : ℝ) := by rw [h2m]; positivity
  have hK₂ : K ≤ 1 * (g * ((2 * m : ℕ) : ℝ)) := by
    show g * (m : ℝ) ≤ 1 * (g * ((2 * m : ℕ) : ℝ))
    rw [h2m]
    nlinarith
  have hρ₂0 : 0 ≤ ρ₂ := Real.sqrt_nonneg _
  have hρ₂K : ρ₂ ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1 := by
    show Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hρ₂ρ : ρ₂ ≤ ρ := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hK₂pos hKpos]
    have := hK₂
    linarith
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hs0 : (0 : ℝ) < ((m / 4 : ℕ) : ℝ) := by
    have : 0 < m / 4 := by omega
    exact_mod_cast this
  have hK₄pos : 0 < g * ((m / 4 : ℕ) : ℝ) := by positivity
  have hK₄ : K ≤ 8 * (g * (s₀ : ℝ)) := by
    show g * (m : ℝ) ≤ 8 * (g * ((m / 4 : ℕ) : ℝ))
    nlinarith
  have hρ₄0 : 0 ≤ ρ₄ := Real.sqrt_nonneg _
  have hρ₄K : ρ₄ ^ 2 * (g * (s₀ : ℝ)) = 1 := by
    show Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ))) ^ 2 * (g * ((m / 4 : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  -- the tails
  have hτ₁0 : 0 ≤ τ₁ := by positivity
  have hβ₄0 : 0 ≤ β₄ := by positivity
  have ht₁ : t₁ ≤ τ₁ * ρ ^ 5 := by
    have h := tl_rate (c := 1) hmm0 hΞ₁ hC₀ le_rfl hρ0 hρK hK1 (by linarith) hρ0 hρK
    have e : 2 * mm * 1 ^ 2 * (2 * mm * 1 ^ 2 * Ξ₁ + 1 * C₀) * ρ ^ 5 = τ₁ * ρ ^ 5 := by
      show _ = 2 * mm * (2 * mm * Ξ₁ + C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have ht₂ : t₂ ≤ τ₁ * ρ ^ 5 := by
    have h := tl_rate (c := 1) hmm0 hΞ₁ hC₀ le_rfl hρ0 hρK hK1 hK₂ hρ₂0 hρ₂K
    have e : 2 * mm * 1 ^ 2 * (2 * mm * 1 ^ 2 * Ξ₁ + 1 * C₀) * ρ ^ 5 = τ₁ * ρ ^ 5 := by
      show _ = 2 * mm * (2 * mm * Ξ₁ + C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have ht₄ : t₄ ≤ β₄ * ρ ^ 5 := by
    have h := tl_rate (c := 8) hmm0 hΞ₁ hC₀ (by norm_num) hρ0 hρK hK1 hK₄ hρ₄0 hρ₄K
    have e : 2 * mm * 8 ^ 2 * (2 * mm * 8 ^ 2 * Ξ₁ + 8 * C₀) * ρ ^ 5 = β₄ * ρ ^ 5 := by
      show _ = 128 * mm * (128 * mm * Ξ₁ + 8 * C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have htl0 : ∀ K' ρ', 0 ≤ ρ' → 0 ≤ tl K' ρ' := by
    intro K' ρ' hρ'
    show 0 ≤ (2 * mm / K' ^ 2) * ((2 * mm / K' ^ 2) * Ξ₁ + C₀ * ρ')
    have h1 : 0 ≤ 2 * mm / K' ^ 2 := div_nonneg (by linarith) (sq_nonneg K')
    exact mul_nonneg h1 (add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hC₀ hρ'))
  have ht₁0 : 0 ≤ t₁ := htl0 _ _ hρ0
  have ht₂0 : 0 ≤ t₂ := htl0 _ _ hρ₂0
  have ht₄0 : 0 ≤ t₄ := htl0 _ _ hρ₄0
  -- the form constant and the shells
  have hfA : formA s₀ m ≤ cF * ρ := formA_rate hg hρ0 hm hρK'
  have hsh := shell_rate hg hm hρK'
  have hmW : 0 ≤ mm * W := by positivity
  have hτφ : τφ ≤ 64 * g ^ 2 * ρ ^ 4 * (mm * W) := by
    have e : τφ = (mm * W) * (1 / ((s₀ : ℝ) + 1) ^ 2) := by
      show mm * W / ((s₀ : ℝ) + 1) ^ 2 = _
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsh.1 hmW
    linarith
  have hτφ0 : 0 ≤ τφ := by positivity
  have hmτ : (m : ℝ) * τφ ≤ 64 * g * ρ ^ 2 * (mm * W) := by
    have e : (m : ℝ) * τφ = (mm * W) * ((m : ℝ) / ((s₀ : ℝ) + 1) ^ 2) := by
      show (m : ℝ) * (mm * W / ((s₀ : ℝ) + 1) ^ 2) = _
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsh.2 hmW
    linarith
  have hcF0 : 0 ≤ cF := by positivity
  have hCtL : 0 ≤ Ct ((1 + g ^ 2) * (mm * W)) := hCt _ (by positivity)
  -- the two pieces
  have hI := rate_arith_I (sT := sT) hη hτ₁0 rfl ht₁ ht₂ ht₁0 ht₂0 hCχ hCO hτχ hS0 hρ0
  have hIII := rate_arith_III (m := (m : ℝ)) (Xa := Xa) hη hτ₁0 hρ0 hρ1 ht₂ hρ₂ρ hρ₂0 hCtL hZg hfA
    (formA_nonneg s₀ m) ht₄ ht₄0 hmW hτφ hτφ0 hmτ hXa hg.le ht hβ₄0 hcF0
  have hρ10 : ρ ^ 10 = (1 / K) ^ 5 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, pow_mul, hρ2]
  rw [hρ10] at hI
  show _ ≤ _ + _ * t * ρ ^ 5 + 2 * δ₁ * S0 * ρ ^ 5 * τχ + S0 ^ 2 * sT
  linarith

end Arith

/-! ## The rates for the Coulomb system -/

section Rates

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- The constants `(A₁, A₂, A₃)` of `prop:grid-dyn`, as functions of the scalar data
`s0 = ‖ψ₀‖`, `hu = ‖H ψ₀‖`, `hs = ‖H ψ₀‖` (the decoded state of `H ψ₀`) and `hv = ‖H² ψ₀‖`; they do
not depend on `m` (that is `K`) or on `t`. -/
noncomputable def gridConsts (sys : CoulombSystem eta ν) (L Hunit Blow Cs Bker : ℝ) (a : Fin eta)
    (χ : Lattice3 → ℂ) (s0 hu hs hv : ℝ) : ℝ × ℝ × ℝ :=
  let g : ℝ := 2 * Real.pi / L
  let b : ℝ := relB sys L Hunit
  let S0 : ℝ := s0
  let Ξ₀ : ℝ := 2 * hu + 2 * b * S0
  let Ξ₁ : ℝ := 2 * hv + 2 * b * hs
  let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
  let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
  let τ₁ : ℝ := 2 * sys.maxMass * (2 * sys.maxMass * Ξ₁ + Ct M₀)
  let β₄ : ℝ := 128 * sys.maxMass * (128 * sys.maxMass * Ξ₁ + 8 * Ct M₀)
  let δ₁ : ℝ := eta * τ₁
  let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
  let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
  let CO : ℝ := ‖convOp (eta := eta) a χ‖
  let Cχ : ℝ := ∑' ν, ‖χ ν‖
  let cJ : ℝ := gridFlowConst sys L
  let Xb : ℝ := 5 / 3 * Xa + cJ * S0
  let W : ℝ := 5 / 3 * ((2 + 12 * sys.maxMass) * Cχ * Xb + 14 * momTwo χ * S0) + cJ * (Cχ * S0)
  let cF : ℝ := 4 * Real.sqrt (5512 * g)
  (2 * δ₁ * (Cχ * τ₁ + CO * δ₁) + CO * δ₁ ^ 2 + Cχ * τ₁ ^ 2,
    2 * (eta * δ₁ * Ct ((1 + g ^ 2) * (sys.maxMass * W)) +
      Zg * (sys.maxMass * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)),
    2 * δ₁ * S0)

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **`prop:grid-dyn`, rates (Fourier side).** For `m ≥ 8` and `K = g m ≥ 8`,
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤ A₁ K^{-5} + A₂ t K^{-5/2} + A₃ K^{-5/2} τ_χ(K)
+ ‖ψ₀‖² τ_χ^∞(m)`, with `(A₁, A₂, A₃) = gridConsts` (independent of `K` and `t`),
`τ_χ(K) = Σ_{g|ν| > K} |χ̂(ν)|` and `τ_χ^∞(m) = Σ_{‖ν‖∞ > m} |χ̂(ν)|`. -/
theorem grid_observable_rate (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (Blow Cs Bker : ℝ) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (a : Fin eta) (χ : Lattice3 → ℂ) (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (hreal : ∀ ν, χ (-ν) = conj (χ ν))
    {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridConsts sys L Hunit Blow Cs Bker a χ ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then ‖χ ν‖ else 0
    let ψg := Ug t (regCoeff m (molecularH2StateMap eta g u₀))
    ‖⟪U t (molecularH2StateMap eta g u₀), convOp a χ (U t (molecularH2StateMap eta g u₀))⟫_ℂ -
        ⟪ψg, gridObs a χ ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * Real.sqrt (1 / K) ^ 5 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖molecularH2StateMap eta g u₀‖ ^ 2 * supTail χ m := by
  intro g K A τχ ψg
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
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
  have hΞ₀ : 0 ≤ 2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖ := by
    positivity
  have hΞ₁ : 0 ≤ 2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖ := by
    positivity
  have hCt : ∀ M, 0 ≤ M → 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M :=
    fun M hM' => finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM'
  have hM₀ : 0 ≤ sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖)) := by positivity
  have hCχ : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hτχ : 0 ≤ τχ := tsum_nonneg fun ν => by split_ifs <;> simp
  have hZg : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg hγ
  have hcJ : 0 ≤ gridFlowConst sys L := gridFlowConst_nonneg sys hL
  have hD : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hXa : 0 ≤ (1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))) := by positivity
  have hW : 0 ≤ 5 / 3 * ((2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) *
      (5 / 3 * ((1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
        2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖)))) +
        gridFlowConst sys L * ‖molecularH2StateMap eta g u₀‖) +
      14 * momTwo χ * ‖molecularH2StateMap eta g u₀‖) +
      gridFlowConst sys L * ((∑' ν, ‖χ ν‖) * ‖molecularH2StateMap eta g u₀‖) := by positivity
  refine (grid_observable_error sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph hderiv m hm hκ Ug
    hg0 hgcomm hgderiv (Real.sqrt (1 / (g * (m : ℝ))))
    (Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))) (Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))) Blow Cs
    Bker hK₄ (Real.sqrt_nonneg _) (hscale _ hKpos) (Real.sqrt_nonneg _) (hscale _ hK₂pos)
    (Real.sqrt_nonneg _) (hscale _ hK₄pos) hBlow hCs hBker hAmplitude hBkerScale hCsScale u₀ v₀
    huv a χ hχ1 hχ2 hreal ht).trans ?_
  exact grid_rate_arith (η := (eta : ℝ)) (mm := sys.maxMass)
    (Ξ₁ := 2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖)
    (C₀ := finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
      (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
        2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))))
    (g := g) (t := t) (S0 := ‖molecularH2StateMap eta g u₀‖) (sT := supTail χ m)
    (Cχ := ∑' ν, ‖χ ν‖) (CO := ‖convOp (eta := eta) a χ‖) (τχ := τχ)
    (Zg := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L))
    (m := m) (Ct := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M)
    (Nat.cast_nonneg eta) hM hΞ₁ (hCt _ hM₀) hg hm hK ht hS0 hCχ (norm_nonneg _) hτχ hZg hXa hW hCt

end Rates

end PlaneWaveGridDynamics

end DevGD5
-- END SOURCE dev/DevGD5.lean

-- BEGIN SOURCE dev/DevGD6.lean
-- SHA256 cacde78eb0a36de7b7bf570086520777a4b37c0689fd64e7620f2e28fe336c5f
section DevGD6

/-!
# Grid dynamics: `prop:grid-dyn` in position space

The grid method works with grid values: the grid Hamiltonian `Hpos` of the grid files (kinetic
energy through the DFT, collocated potential of the truncated kernel) and the collocated
observable `O_g`, the diagonal operator with entries `χ(x_{j_a})` on register `a` (`posObs`).  The
DFT conjugates them to the momentum-basis operators of the register: `dft ∘ Hpos = Hgrid ∘ dft`
(`dft_Hpos`, grid core) and `dft ∘ O_g = gridObs a χ̂ ∘ dft` (`dft_posObs`, the fold identity of
the observable: `χ(x_j) e^{2πi q·j/n'} = Σ_ν χ̂(ν) e^{2πi (q + ν e_a)·j/n'}`).  So the grid
propagator in position space is `e^{-iHpos t} = dft⁻¹ e^{-iHgrid t} dft` (`posConj`,
`exists_posPropagator`) and the
grid expectations of `O_g` are the register expectations of `gridObs`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset Set

namespace PlaneWaveGridDynamics

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics UnitAddTorus

noncomputable section

local instance unitAddCircleMeasureSpaceForGrid : MeasureTheory.MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

/-! ## The collocated observable -/

section Observable

variable {eta m : ℕ}

/-- **The collocated observable** `O_g`: the diagonal grid operator with entries `χ(x_{j_a})` on
register `a`. -/
def posObs (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) :
    EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  cMul (fun j => χ (gridPoint (j a)))

lemma posObs_apply (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (u : EuclideanSpace ℂ (RCfg eta m)) (j : RCfg eta m) :
    posObs a χ u j = χ (gridPoint (j a)) * u j := rfl

lemma cfgShift_eq_add (a : Fin eta) (μ : RMode m) (q : RCfg eta m) :
    cfgShift a μ q = q + Pi.single a μ := by
  funext b
  by_cases hb : b = a
  · subst hb
    simp [cfgShift]
  · simp [cfgShift, hb]

lemma dotC_cfgShift (a : Fin eta) (μ : RMode m) (q j : RCfg eta m) :
    dotC (cfgShift a μ q) j = dotC q j + dot3 μ (j a) := by
  classical
  rw [cfgShift_eq_add]
  have hlin : ∀ x y : RCfg eta m, dotC (x + y) j = dotC x j + dotC y j := by
    intro x y
    simp only [dotC, dot3, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsingle : dotC (Pi.single a μ : RCfg eta m) j = dot3 μ (j a) := by
    rw [dotC, Finset.sum_eq_single a]
    · simp
    · intro k _ hk
      simp [hk, dot3]
    · simp
  rw [hlin, hsingle]

/-- Multiplying a plane wave of the grid by `e^{2πi ν·x_{j_a}}` translates its momentum. -/
lemma chi_cfgShift (a : Fin eta) (ν : Lat3) (q j : RCfg eta m) :
    chi (cfgShift a (ofLat ν) q) j = chi q j * mFourier ν (gridPoint (j a)) := by
  rw [chi, dotC_cfgShift, ech_add, ← chi, mFourier_gridPoint]
  rfl

/-- **Fold identity of the observable.** The DFT conjugates the collocated observable to the
cyclic convolution `gridObs a χ̂` of the register. -/
theorem dft_posObs (a : Fin eta) {χ : C(UnitAddTorus (Fin 3), ℂ)}
    (hχ : Summable fun ν => ‖mFourierCoeff χ ν‖) (u : EuclideanSpace ℂ (RCfg eta m)) :
    dft (posObs a χ u) = gridObs a (mFourierCoeff χ) (dft u) := by
  ext q
  rw [gridObs_apply a hχ]
  set N : ℂ := (Real.sqrt (Ncfg eta (2 * (2 * m) + 1)) : ℂ)
  have hj : ∀ j : RCfg eta m, HasSum
      (fun ν => (mFourierCoeff χ ν * mFourier ν (gridPoint (j a))) * (u j * (chi q j / N)))
      (χ (gridPoint (j a)) * (u j * (chi q j / N))) := by
    intro j
    have h := hasSum_mFourier_series_apply_of_summable hχ.of_norm (gridPoint (j a))
    simp only [smul_eq_mul] at h
    exact h.mul_right _
  have hsum := hasSum_sum (s := (univ : Finset (RCfg eta m))) (fun j _ => hj j)
  have hL : (dft (posObs a χ u)) q = ∑ j, χ (gridPoint (j a)) * (u j * (chi q j / N)) := by
    simp only [dft, kOp_apply, posObs_apply]
    exact sum_congr rfl fun j _ => by ring
  rw [hL, ← hsum.tsum_eq]
  refine tsum_congr fun ν => ?_
  simp only [dft, kOp_apply]
  rw [Finset.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [chi_cfgShift]
  ring

end Observable

/-! ## The DFT as a unitary and the position-space grid propagator -/

section Propagator

variable {eta m : ℕ}

/-- The DFT of the register as a unitary. -/
def dftLIE : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m) where
  toFun := dft
  invFun := idft
  map_add' := map_add dft
  map_smul' := map_smul dft
  left_inv := idft_dft
  right_inv := dft_idft
  norm_map' := norm_dft

lemma dftLIE_apply (u : EuclideanSpace ℂ (RCfg eta m)) : dftLIE u = dft u := rfl

lemma dftLIE_symm_apply (u : EuclideanSpace ℂ (RCfg eta m)) : dftLIE.symm u = idft u := rfl

/-- The position-space version `dft⁻¹ ∘ V ∘ dft` of a register unitary `V`. -/
def posConj (V : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)) :
    EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  (dftLIE.trans V).trans dftLIE.symm

lemma posConj_apply (V : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (u : EuclideanSpace ℂ (RCfg eta m)) : posConj V u = idft (V (dft u)) := rfl

lemma dft_posConj (V : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (u : EuclideanSpace ℂ (RCfg eta m)) : dft (posConj V u) = V (dft u) := by
  rw [posConj_apply, dft_idft]

variable {ν : Type*} [Fintype ν]

/-- **The grid propagator in position space** `e^{-iHpos t}` of an even kernel: a unitary group,
strongly continuous, commuting with `Hpos` and solving the Schrödinger equation; its DFT is the
register propagator `e^{-iHgrid t}`. -/
theorem exists_posPropagator (P : RegParticles eta) (Nn : PosNuclei ν) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x) (g : ℝ) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧
      (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hgrid eta m P Nn.toNucData κ g x) = Hgrid eta m P Nn.toNucData κ g (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m P Nn.toNucData κ g x))) t) ∧
      (∀ x, posConj (Ug 0) x = x) ∧
      (∀ s t x, posConj (Ug (s + t)) x = posConj (Ug s) (posConj (Ug t) x)) ∧
      (∀ x, Continuous fun t => posConj (Ug t) x) ∧
      (∀ t x, posConj (Ug t) (Hpos P Nn κ g x) = Hpos P Nn κ g (posConj (Ug t) x)) ∧
      (∀ t x, HasDerivAt (fun s => posConj (Ug s) x)
        (-(Complex.I • posConj (Ug t) (Hpos P Nn κ g x))) t) := by
  obtain ⟨Ug, h0, hadd, hcont, hcomm, hderiv, -⟩ :=
    exists_gridPropagator (eta := eta) (m := m) (P := P) (D := Nn.toNucData) (g := g) hκe
  refine ⟨Ug, h0, hadd, hcont, hcomm, hderiv, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [posConj_apply, h0, idft_dft]
  · intro s t x
    rw [posConj_apply, posConj_apply, posConj_apply, dft_idft, hadd]
  · intro x
    have hc : Continuous fun t => Ug t (dft x) := hcont (dft x)
    exact (LinearMap.continuous_of_finiteDimensional (idft :
      EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] _)).comp hc
  · intro t x
    have h1 : dft (Hpos P Nn κ g x) = Hgrid eta m P Nn.toNucData κ g (dft x) :=
        dft_Hpos P Nn hκe g x
    have h2 : dft (Hpos P Nn κ g (posConj (Ug t) x)) =
        Hgrid eta m P Nn.toNucData κ g (Ug t (dft x)) := by
      rw [dft_Hpos P Nn hκe g, dft_posConj]
    rw [posConj_apply, h1, hcomm, ← h2, idft_dft]
  · intro t x
    have h := ((LinearMap.toContinuousLinearMap (idft :
      EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] _)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
        (hderiv t (dft x))
    refine h.congr_deriv ?_
    rw [ContinuousLinearMap.coe_restrictScalars', LinearMap.coe_toContinuousLinearMap', map_neg,
      map_smul, posConj_apply, dft_Hpos P Nn hκe g]

end Propagator

/-! ## `prop:grid-dyn` in position space -/

section PositionTheorem

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **Observable error on the grid, position space** (`prop:grid-dyn`). Let `U t` be unitaries on
`L²((T³)^η)` with `U 0 = 1` that preserve the graph of the Coulomb Hamiltonian and solve the
Schrödinger equation on it (the propagator `e^{-iHt}`), and `U_g` the register propagator of the
grid Hamiltonian of a real, even kernel of the class `𝒦_K` (`IsGridKernel`; `K = 2πm/L`, register
radius `2m`,
`n' = 4m + 1` grid points per direction), so that `dft⁻¹ U_g(t) dft = e^{-iH_pos t}`. For
`ψ₀ ∈ D(H²)` (`H ψ₀ = h₀`, `H h₀ = h₁`), a register `a`, a real continuous `χ` with
`Σ_ν |χ̂(ν)| < ∞` and `Σ_ν |ν|² |χ̂(ν)| < ∞`, the grid state
`ψ_g(t) = e^{-iH_pos t} P ψ₀` (`P ψ₀` sampled on the grid, unitarily normalised) and the
collocated observable `O_g = χ(x_{j_a})`: for `m ≥ 8`, `K ≥ 8` and `t ≥ 0`,
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤
  A₁ K^{-5} + A₂ t K^{-5/2} + A₃ K^{-5/2} τ_χ(K) + ‖ψ₀‖² τ_χ^∞(m)`
with `(A₁, A₂, A₃) = gridConsts` at the canonical constants of the cell, independent of `K` and
`t`. -/
theorem grid_observable_position (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (ψ₀ h₀ h₁ : MolecularPositionL2 eta) (hψ₀ : HasCoulombHamiltonian sys L ψ₀ h₀)
    (hh₀ : HasCoulombHamiltonian sys L h₀ h₁)
    (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχ1 : Summable fun ν => ‖mFourierCoeff χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖mFourierCoeff χ ν‖)
    (hreal : ∀ y, conj (χ y) = χ y) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridConsts sys L molecularCanonicalUnitHardyConstant (molecularCanonicalLowConstant L)
      (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L) a
      (mFourierCoeff χ) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then ‖mFourierCoeff χ ν‖ else 0
    let ψg := posConj (Ug t) (idft (regCoeff m ((physMap eta).symm ψ₀)))
    ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a χ ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * Real.sqrt (1 / K) ^ 5 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖ψ₀‖ ^ 2 * supTail (mFourierCoeff χ) m := by
  intro g K A τχ ψg
  have hPeriodic := canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨H, hKernel, -⟩ := exists_coulombFourierH2Operator sys L
      molecularCanonicalUnitHardyConstant
    hL hPeriodic
  have hiff := hasCoulombHamiltonian_iff_phys sys L hL H hKernel
  -- the propagator on the Fourier side
  set UF : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
    fun s => ((physMap eta).trans (U s)).trans (physMap eta).symm with hUFdef
  have hUF : ∀ s x, UF s x = (physMap eta).symm (U s (physMap eta x)) := fun s x => rfl
  have h0F : ∀ x, UF 0 x = x := by
    intro x
    rw [hUF, hU0, LinearIsometryEquiv.symm_apply_apply]
  have hgraphF : ∀ s u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        UF s (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = UF s (H u) := by
    intro s u
    obtain ⟨u', h1, h2⟩ := (hiff _ _).mp (hUgraph s _ _ ((hiff _ _).mpr ⟨u, rfl, rfl⟩))
    refine ⟨u', ?_, ?_⟩
    · rw [hUF, ← h1, LinearIsometryEquiv.symm_apply_apply]
    · rw [hUF, ← h2, LinearIsometryEquiv.symm_apply_apply]
  have hderivF : ∀ s u, HasDerivAt (fun r => UF r (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • UF s (H u))) s := by
    intro s u
    have h := hUderiv s _ _ ((hiff _ _).mpr ⟨u, rfl, rfl⟩)
    have h2 := (((physMap eta).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt s h
    simp only [ContinuousLinearMap.coe_restrictScalars'] at h2
    rw [map_neg, map_smul] at h2
    exact h2
  -- the initial state in `D(H²)`
  obtain ⟨u₀, hu₀1, hu₀2⟩ := (hiff ψ₀ h₀).mp hψ₀
  obtain ⟨v₀, hv₀1, hv₀2⟩ := (hiff h₀ h₁).mp hh₀
  have huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀ :=
    (physMap eta).injective (hu₀2.trans hv₀1.symm)
  have hx₀ : (physMap eta).symm ψ₀ = molecularH2StateMap eta (2 * Real.pi / L) u₀ := by
    rw [← hu₀1, LinearIsometryEquiv.symm_apply_apply]
  -- the continuum expectation on the Fourier side
  have hO : ∀ x, ⟪physMap eta x, mulCLM (regFun a χ) (physMap eta x)⟫_ℂ =
      ⟪x, convOp a (mFourierCoeff χ) x⟫_ℂ := by
    intro x
    rw [← physMap_mulCLM a hχ1 x, ← LinearIsometryEquiv.inner_map_map (physMap eta),
      LinearIsometryEquiv.apply_symm_apply]
  have hψt : U t ψ₀ = physMap eta (UF t (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    rw [hUF, LinearIsometryEquiv.apply_symm_apply, hu₀1]
  -- the grid expectation on the register
  have hdψ : dft ψg = Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    show dft (posConj (Ug t) (idft (regCoeff m ((physMap eta).symm ψ₀)))) = _
    rw [dft_posConj, dft_idft, hx₀]
  have hψg : ⟪ψg, posObs a χ ψg⟫_ℂ =
      ⟪Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)),
        gridObs a (mFourierCoeff χ) (Ug t
            (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)))⟫_ℂ := by
    rw [← inner_dft_dft ψg, dft_posObs a hχ1, hdψ]
  rw [hψt, hO, hψg]
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  have h := grid_observable_rate sys L H hKernel molecularCanonicalUnitHardyConstant hL hPeriodic
    (finiteCoulombPhysicalMassConstant_nonneg _ _ _) UF h0F hgraphF hderivF m hm hK hκ Ug hg0
    hgcomm hgderiv _ _ _ hBlow hCs hBker hLow hKernelScale hSobolev u₀ v₀ huv a (mFourierCoeff χ)
    hχ1 hχ2 (fun ν => mFourierCoeff_neg_of_real hreal ν) ht
  dsimp only at h
  have e1 : ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ = ‖ψ₀‖ := by
    rw [← hu₀1, LinearIsometryEquiv.norm_map]
  have e2 : ‖H u₀‖ = ‖h₀‖ := by rw [← hu₀2, LinearIsometryEquiv.norm_map]
  have e3 : ‖molecularH2StateMap eta (2 * Real.pi / L) v₀‖ = ‖h₀‖ := by
    rw [← hv₀1, LinearIsometryEquiv.norm_map]
  have e4 : ‖H v₀‖ = ‖h₁‖ := by rw [← hv₀2, LinearIsometryEquiv.norm_map]
  rw [e1, e2, e3, e4] at h
  exact h

end PositionTheorem

/-! ## `(Hχ)` and the final form of `prop:grid-dyn` -/

section Final

variable {eta : ℕ} {ν : Type} [Fintype ν]

lemma inBox_iff_supNorm_le (m : ℕ) (x : Lat3) : InBox m x ↔ latticeSupNorm x ≤ m := by
  unfold InBox latticeSupNorm
  simp only [max_le_iff]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have := h 0; exact_mod_cast this
    · have := h 1; exact_mod_cast this
    · have := h 2; exact_mod_cast this
  · rintro ⟨⟨h0, h1⟩, h2⟩ c
    fin_cases c
    · exact_mod_cast h0
    · exact_mod_cast h1
    · exact_mod_cast h2

/-- Under `(Hχ)` the sup-norm coefficient tail beyond `m` is at most `C_{χ,M} K^{-M}`,
`K = g m ≥ 1`. -/
lemma supTail_le_of_HChi {g : ℝ} (hg : 0 < g) {c : Lattice3 → ℂ} {CM : ℕ → ℝ}
    (hc : HChi g c CM) {M : ℕ} (hM : 1 ≤ M) {m : ℕ} (hK : 1 ≤ g * m) :
    supTail c m ≤ CM M * (1 / (g * m)) ^ M := by
  have e : supTail c m = ∑' x, if g * m < g * latticeSupNorm x then ‖c x‖ else 0 := by
    unfold supTail
    refine tsum_congr fun x => ?_
    by_cases hx : InBox m x
    · have h1 := (inBox_iff_supNorm_le m x).mp hx
      have h2 : ¬ g * m < g * latticeSupNorm x := by
        push Not
        exact mul_le_mul_of_nonneg_left h1 hg.le
      rw [if_pos hx, if_neg h2]
    · have h1 : ¬ latticeSupNorm x ≤ m := fun h => hx ((inBox_iff_supNorm_le m x).mpr h)
      push Not at h1
      rw [if_neg hx, if_pos (mul_lt_mul_of_pos_left h1 hg)]
  have hK0 : 0 < g * m := by linarith
  have h := hc.2 M hM (g * m) hK
  rw [e]
  have hpow : 0 < (g * m) ^ M := pow_pos hK0 M
  rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpow, mul_comm]
  exact h

/-- Under `(Hχ)` the Euclidean coefficient tail beyond `K ≥ √3` is at most
`(√3)^M C_{χ,M} K^{-M}`. -/
lemma tail_le_of_HChi {g : ℝ} (hg : 0 < g) {c : Lattice3 → ℂ} {CM : ℕ → ℝ}
    (hc : HChi g c CM) {M : ℕ} (hM : 1 ≤ M) {K : ℝ} (hK : Real.sqrt 3 ≤ K) :
    (∑' x, if K < g * Real.sqrt (latticeNormSq x) then ‖c x‖ else 0) ≤
      Real.sqrt 3 ^ M * CM M * (1 / K) ^ M := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hK0 : 0 < K := lt_of_lt_of_le h3 hK
  have hρ : 1 ≤ K / Real.sqrt 3 := by
    rw [le_div_iff₀ h3]
    linarith
  have h1 := tail_le_supTail hc.1 hg.le K
  have h2 := hc.2 M hM (K / Real.sqrt 3) hρ
  have hpow : 0 < (K / Real.sqrt 3) ^ M := pow_pos (by positivity) M
  have h4 : (∑' x, if K / Real.sqrt 3 < g * latticeSupNorm x then ‖c x‖ else 0) ≤
      CM M / (K / Real.sqrt 3) ^ M := by
    rw [le_div_iff₀ hpow, mul_comm]
    exact h2
  have e : CM M / (K / Real.sqrt 3) ^ M = Real.sqrt 3 ^ M * CM M * (1 / K) ^ M := by
    rw [div_pow, one_div, inv_pow]
    field_simp
  linarith

lemma CM_nonneg_of_HChi {g : ℝ} {c : Lattice3 → ℂ} {CM : ℕ → ℝ} (hc : HChi g c CM) {M : ℕ}
    (hM : 1 ≤ M) : 0 ≤ CM M := by
  have h1 := hc.2 M hM 1 le_rfl
  have hnn : 0 ≤ (∑' x, if (1 : ℝ) < g * latticeSupNorm x then ‖c x‖ else 0) :=
    tsum_nonneg fun _ => by split_ifs <;> simp
  rw [one_pow, one_mul] at h1
  exact hnn.trans h1

/-- `(Hχ)` gives the second moment `Σ_ν |ν|² |χ̂(ν)| < ∞`. -/
lemma summable_nsq_of_HChi {g : ℝ} (hg : 0 < g) {c : Lattice3 → ℂ} {CM : ℕ → ℝ}
    (hc : HChi g c CM) : Summable fun x => nsq x * ‖c x‖ := by
  have hw := summable_weighted_of_decay hc.1 hg (CM 6) (hc.2 6 (by norm_num))
  refine Summable.of_nonneg_of_le (fun x => mul_nonneg (nsq_nonneg x) (norm_nonneg _))
    (fun x => ?_) (hw.mul_left (1 / g ^ 2))
  have hg2 : 0 < g ^ 2 := by positivity
  have hn := nsq_nonneg x
  have hcx := norm_nonneg (c x)
  have e : 1 / g ^ 2 * ((1 + g ^ 2 * latticeNormSq x) * ‖c x‖) =
      ‖c x‖ / g ^ 2 + nsq x * ‖c x‖ := by
    rw [← nsq_eq_latticeNormSq]
    field_simp
  rw [e]
  have : 0 ≤ ‖c x‖ / g ^ 2 := by positivity
  linarith

lemma gridConsts_nonneg_three (sys : CoulombSystem eta ν) (L Hunit Blow Cs Bker : ℝ)
    (a : Fin eta) (χ : Lattice3 → ℂ) (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    {s0 hu hs hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    0 ≤ (gridConsts sys L Hunit Blow Cs Bker a χ s0 hu hs hv).2.2 := by
  have hb := relB_nonneg sys L Hunit hC
  have hM := sys.one_le_maxMass
  have hκ : 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
      (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB sys L Hunit * s0))) :=
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker (by positivity)
  simp only [gridConsts]
  positivity

/-- **`prop:grid-dyn`** (truncated-kernel grid method, observable after evolution). For a
periodic Coulomb system there is a propagator `U` (`e^{-iHt}`) on `L²((T³)^η)` (unitary group,
strongly continuous, preserving the graph of the Hamiltonian, solving the Schrödinger equation on
it, and the only evolution that does), and for every register radius `2m` and every real, even
kernel `κ` of the class `𝒦_K` (`IsGridKernel`, `K = 2πm/L`) a grid propagator `U_g`
(`e^{-iH_pos t}` on the grid values, `n' = 4m + 1` points per direction), such that: for every
`ψ₀ ∈ D(H²)` (`H ψ₀ = h₀`, `H h₀ = h₁`), register `a` and real continuous `χ` satisfying `(Hχ)`,
with the constants `(A₁, A₂, A₃) = gridConsts` at `(‖ψ₀‖, ‖h₀‖, ‖h₀‖, ‖h₁‖)`, which do not depend
on `m` or `t`: for `m ≥ 8`, `K ≥ 8` and `t ≥ 0`, the grid state `ψ_g(t) = e^{-iH_pos t} P ψ₀`
and the collocated observable `O_g = χ(x_{j_a})` satisfy (`eq:grid-dyn` without the trivial
`min {1, ·}`, which is `thm_grid_dyn_min`)
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤
  (A₁ + (A₃ 3^{5/2} + ‖ψ₀‖²) C_{χ,5}) K^{-5} + A₂ t K^{-5/2}`.
With `N = (2m+1)³`, `K^{-1} ≤ (3L/2π) N^{-1/3}` (`inv_K_le_basis`), so the bound is
`O(N^{-5/3} + t N^{-5/6})`. -/
theorem thm_grid_dyn (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    ∃ U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, Continuous fun t => U t ψ) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasCoulombHamiltonian sys L (U t f) (U t h)) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) ∧
      (∀ φ ζ : ℝ → MolecularPositionL2 eta, (∀ t, HasCoulombHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
        (∀ x, Continuous fun t => Ug t x) ∧
        (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t x)) ∧
        (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
        ∀ ψ₀ h₀ h₁ : MolecularPositionL2 eta, HasCoulombHamiltonian sys L ψ₀ h₀ →
          HasCoulombHamiltonian sys L h₀ h₁ →
          ∀ (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (CM : ℕ → ℝ),
          HChi (2 * Real.pi / L) (mFourierCoeff χ) CM →
          (∀ y, conj (χ y) = χ y) →
          let A := gridConsts sys L molecularCanonicalUnitHardyConstant
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) a (mFourierCoeff χ) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let ψg := Ug t (idft (regCoeff m ((physMap eta).symm ψ₀)))
            ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a χ ψg⟫_ℂ‖ ≤
              (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
                A.2.1 * t * Real.sqrt (1 / K) ^ 5 := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, -, -⟩ := exists_coulombPropagator sys L hL
  refine ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, fun m κ hκ => ?_⟩
  obtain ⟨Ur, hr0, -, -, hrcomm, hrderiv, hp0, hpadd, hpcont, hpcomm, hpderiv⟩ :=
    exists_posPropagator (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) hκ.even
      (2 * Real.pi / L)
  refine ⟨fun t => posConj (Ur t), hp0, hpadd, hpcont, hpcomm, hpderiv, ?_⟩
  intro ψ₀ h₀ h₁ hψ₀ hh₀ a χ CM hc hreal A hm hK t ht K ψg
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hχ1 := hc.1
  have hχ2 := summable_nsq_of_HChi hg hc
  have h := grid_observable_position sys L hL U h0 hgraph hderiv m hm hK hκ Ur hr0 hrcomm hrderiv
    ψ₀ h₀ h₁ hψ₀ hh₀ a χ hχ1 hχ2 hreal ht
  obtain ⟨hBlow, hCs, hBker, -⟩ := molecularCanonicalTailConstants_spec L hL
  have hA₃ : 0 ≤ A.2.2 :=
    gridConsts_nonneg_three sys L _ _ _ _ a _ (finiteCoulombPhysicalMassConstant_nonneg _ _ _)
      hBlow hCs hBker (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have hK' : (8 : ℝ) ≤ K := hK
  have hKpos : 0 < K := by linarith
  have hsqrt3 : Real.sqrt 3 ≤ K := by
    have : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    linarith
  have hC5 := CM_nonneg_of_HChi hc (M := 5) (by norm_num)
  have htail := tail_le_of_HChi hg hc (M := 5) (by norm_num) hsqrt3
  have hsup := supTail_le_of_HChi hg hc (M := 5) (by norm_num) (m := m) (by linarith)
  have hρ1 : Real.sqrt (1 / K) ^ 5 ≤ 1 := by
    have h1 : 1 / K ≤ 1 := by rw [div_le_one hKpos]; linarith
    have h2 : Real.sqrt (1 / K) ≤ 1 := by
      have := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_one] at this
    exact pow_le_one₀ (Real.sqrt_nonneg _) h2
  have hρ0 : 0 ≤ Real.sqrt (1 / K) ^ 5 := by positivity
  have hτ : A.2.2 * Real.sqrt (1 / K) ^ 5 *
      (∑' x, if K < (2 * Real.pi / L) * Real.sqrt (latticeNormSq x) then
        ‖mFourierCoeff χ x‖ else 0) ≤ A.2.2 * Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left htail (mul_nonneg hA₃ hρ0)
    have h2 : A.2.2 * Real.sqrt (1 / K) ^ 5 * (Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5) ≤
        A.2.2 * 1 * (Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ1 hA₃)
      positivity
    have e : A.2.2 * 1 * (Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5) =
        A.2.2 * Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5 := by ring
    linarith
  have hs : ‖ψ₀‖ ^ 2 * supTail (mFourierCoeff χ) m ≤ ‖ψ₀‖ ^ 2 * (CM 5 * (1 / K) ^ 5) :=
    mul_le_mul_of_nonneg_left hsup (by positivity)
  have e : (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
      A.2.1 * t * Real.sqrt (1 / K) ^ 5 = A.1 * (1 / K) ^ 5 + A.2.1 * t * Real.sqrt (1 / K) ^ 5 +
        A.2.2 * Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5 + ‖ψ₀‖ ^ 2 * (CM 5 * (1 / K) ^ 5) := by ring
  rw [e]
  exact h.trans (by linarith)

/-- The basis-count form: `K^{-1} ≤ (3/g)(2m+1)^{-1}`, that is `K^{-1} ≤ (3L/2π) N^{-1/3}` with
`N = (2m+1)³`. -/
lemma inv_K_le_basis {g : ℝ} (hg : 0 < g) {m : ℕ} (hm : 1 ≤ m) :
    1 / (g * m) ≤ 3 / g * (1 / (2 * (m : ℝ) + 1)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The collocated observable of a function with `|χ| ≤ 1` is a contraction. -/
lemma norm_posObs_le {m : ℕ} (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχb : ∀ y, ‖χ y‖ ≤ 1) (u : EuclideanSpace ℂ (RCfg eta m)) : ‖posObs a χ u‖ ≤ ‖u‖ :=
  norm_le_of_pointwise fun j => by
    rw [posObs_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχb _)

/-- **The normalised grid state** (`cor:norm` at cutoff `2K`). Under the hypotheses of
`grid_observable_position`, with `‖ψ₀‖ = 1`, `|χ| ≤ 1` and `P ψ₀ ≠ 0`, the normalised grid state
`ψ̃_g(t) = ψ_g(t)/‖P ψ₀‖` satisfies the same bound up to `‖(1 - P) ψ₀‖² ≤ (δ₁ K^{-5/2})²`. -/
theorem grid_observable_normalised (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (ψ₀ h₀ h₁ : MolecularPositionL2 eta) (hψ₀ : HasCoulombHamiltonian sys L ψ₀ h₀)
    (hh₀ : HasCoulombHamiltonian sys L h₀ h₁) (hnorm : ‖ψ₀‖ = 1)
    (hP : regCoeff m ((physMap eta).symm ψ₀) ≠ 0)
    (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχ1 : Summable fun ν => ‖mFourierCoeff χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖mFourierCoeff χ ν‖)
    (hreal : ∀ y, conj (χ y) = χ y) (hχb : ∀ y, ‖χ y‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridConsts sys L molecularCanonicalUnitHardyConstant (molecularCanonicalLowConstant L)
      (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L) a
      (mFourierCoeff χ) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then ‖mFourierCoeff χ ν‖ else 0
    let δ₁ : ℝ := obsTailConst sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
    let c : ℝ := ‖regCoeff m ((physMap eta).symm ψ₀)‖
    let ψg := posConj (Ug t) (idft (regCoeff m ((physMap eta).symm ψ₀)))
    let ψgt := ((c : ℂ)⁻¹) • ψg
    ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψgt, posObs a χ ψgt⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * Real.sqrt (1 / K) ^ 5 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖ψ₀‖ ^ 2 * supTail (mFourierCoeff χ) m + (δ₁ * Real.sqrt (1 / K) ^ 5) ^ 2 := by
  intro g K A τχ δ₁ c ψg ψgt
  have hmain := grid_observable_position sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
    hgderiv ψ₀ h₀ h₁ hψ₀ hh₀ a χ hχ1 hχ2 hreal ht
  set x₀ := (physMap eta).symm ψ₀ with hx₀def
  have hg : 0 < g := by positivity
  -- the normalisation
  have hc : ‖ψg‖ = c := by
    show ‖posConj (Ug t) (idft (regCoeff m x₀))‖ = ‖regCoeff m x₀‖
    rw [LinearIsometryEquiv.norm_map, ← dftLIE_symm_apply, LinearIsometryEquiv.norm_map]
  have hc0 : 0 < c := norm_pos_iff.mpr hP
  have hx₀ : ‖x₀‖ = 1 := by rw [hx₀def, LinearIsometryEquiv.norm_map]; exact hnorm
  have hc1 : c ≤ 1 := by
    rw [← hx₀]
    exact norm_regCoeff_le x₀
  set O : EuclideanSpace ℂ (RCfg eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
    LinearMap.toContinuousLinearMap (posObs a χ) with hOdef
  have hO1 : ‖O‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul]
    exact norm_posObs_le a χ hχb u
  have hnormal : ‖⟪ψgt, posObs a χ ψgt⟫_ℂ - ⟪ψg, posObs a χ ψg⟫_ℂ‖ ≤ 1 - c ^ 2 :=
    norm_inner_normalize_sub_le O hO1 ψg hc hc0 hc1
  -- `1 - c² = ‖(1 - P) ψ₀‖²`
  have hPx : ‖regCoeff m x₀‖ = ‖molecularH2Truncate (2 * m) x₀‖ := by
    rw [← (regEmb m).norm_map, regEmb_regCoeff]
  have hpyth : 1 - c ^ 2 = ‖x₀ - molecularH2Truncate (2 * m) x₀‖ ^ 2 := by
    have := norm_sq_truncate_add (2 * m) x₀
    rw [hx₀] at this
    show 1 - ‖regCoeff m x₀‖ ^ 2 = _
    rw [hPx]
    linarith
  -- the tail of the initial state at cutoff `2K`
  have hPeriodic := canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨H, hKernel, -⟩ := exists_coulombFourierH2Operator sys L
      molecularCanonicalUnitHardyConstant
    hL hPeriodic
  have hiff := hasCoulombHamiltonian_iff_phys sys L hL H hKernel
  obtain ⟨u₀, hu₀1, hu₀2⟩ := (hiff ψ₀ h₀).mp hψ₀
  obtain ⟨v₀, hv₀1, hv₀2⟩ := (hiff h₀ h₁).mp hh₀
  have huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀ :=
    (physMap eta).injective (hu₀2.trans hv₀1.symm)
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  have hK' : (8 : ℝ) ≤ g * (m : ℝ) := hK
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hK2 : 2 ≤ g * ((2 * m : ℕ) : ℝ) := by rw [h2m]; linarith
  have h2gK : 2 * g ≤ g * ((2 * m : ℕ) : ℝ) := by
    rw [h2m]
    have : (8 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hK₂pos : 0 < g * ((2 * m : ℕ) : ℝ) := by linarith
  have hρ₂ : Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have htail := initial_tail_le sys L H hKernel molecularCanonicalUnitHardyConstant hL hPeriodic
    (finiteCoulombPhysicalMassConstant_nonneg _ _ _) (2 * m) _ _ _ _ hK2 (Real.sqrt_nonneg _) hρ₂
    hBlow hCs hBker h2gK hLow hKernelScale hSobolev u₀ v₀ huv
  have hx₀u : x₀ = molecularH2StateMap eta (2 * Real.pi / L) u₀ := by
    rw [hx₀def, ← hu₀1, LinearIsometryEquiv.symm_apply_apply]
  have e1 : ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ = ‖ψ₀‖ := by
    rw [← hu₀1, LinearIsometryEquiv.norm_map]
  have e2 : ‖H u₀‖ = ‖h₀‖ := by rw [← hu₀2, LinearIsometryEquiv.norm_map]
  have e3 : ‖molecularH2StateMap eta (2 * Real.pi / L) v₀‖ = ‖h₀‖ := by
    rw [← hv₀1, LinearIsometryEquiv.norm_map]
  have e4 : ‖H v₀‖ = ‖h₁‖ := by rw [← hv₀2, LinearIsometryEquiv.norm_map]
  rw [e1, e2, e3, e4, ← hx₀u] at htail
  have hδ0 : 0 ≤ δ₁ := by
    have hb := relB_nonneg sys L molecularCanonicalUnitHardyConstant
      (finiteCoulombPhysicalMassConstant_nonneg _ _ _)
    have hM := sys.one_le_maxMass
    have hκ' : 0 ≤ finiteCoulombPhysicalTailConstant sys L molecularCanonicalUnitHardyConstant
        (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
        (molecularCanonicalKernelConstant L) (sys.maxMass * (‖ψ₀‖ + 2 * (2 * ‖h₀‖ +
          2 * relB sys L molecularCanonicalUnitHardyConstant * ‖ψ₀‖))) :=
      finiteCoulombPhysicalTailConstant_nonneg sys L _ hBlow hCs hBker (by positivity)
    simp only [δ₁, obsTailConst]
    positivity
  have hρle : Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ≤ Real.sqrt (1 / K) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hK₂pos (by show 0 < g * (m : ℝ); linarith), h2m, one_mul, one_mul]
    show g * (m : ℝ) ≤ g * (2 * (m : ℝ))
    have e : g * (2 * (m : ℝ)) = 2 * (g * m) := by ring
    rw [e]
    linarith
  have htail' : ‖x₀ - molecularH2Truncate (2 * m) x₀‖ ≤ δ₁ * Real.sqrt (1 / K) ^ 5 :=
    htail.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) hρle 5) hδ0)
  have htail2 : ‖x₀ - molecularH2Truncate (2 * m) x₀‖ ^ 2 ≤ (δ₁ * Real.sqrt (1 / K) ^ 5) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htail' 2
  -- combine
  have htri := norm_sub_le_norm_sub_add_norm_sub
    ⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ ⟪ψg, posObs a χ ψg⟫_ℂ ⟪ψgt, posObs a χ ψgt⟫_ℂ
  have hswap : ‖⟪ψg, posObs a χ ψg⟫_ℂ - ⟪ψgt, posObs a χ ψgt⟫_ℂ‖ =
      ‖⟪ψgt, posObs a χ ψgt⟫_ℂ - ⟪ψg, posObs a χ ψg⟫_ℂ‖ := norm_sub_rev _ _
  have hmain' : ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a χ ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * Real.sqrt (1 / K) ^ 5 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖ψ₀‖ ^ 2 * supTail (mFourierCoeff χ) m := hmain
  linarith

end Final

end

end PlaneWaveGridDynamics

end DevGD6
-- END SOURCE dev/DevGD6.lean

-- BEGIN SOURCE dev/DevGD7.lean
-- SHA256 35366394ee03cce78704fc8fc585c6c43996bb479b8d896f5853cd2ac4167bb3
section DevGD7

/-!
# Grid dynamics: the trivial bound of `eq:grid-dyn`

For a `[0,1]`-valued `χ` and `‖ψ₀‖ ≤ 1`, both expectations of `prop:grid-dyn` lie in `[0, 1]`:
the continuum one because `⟪f, χ(x_a) f⟫ = ∫ χ(x_a) |f|²` (`inner_mulCLM_mem`), the grid one
because `⟪u, O_g u⟫ = Σ_j χ(x_{j_a}) |u_j|²` (`inner_posObs_mem`), and the grid state has norm
`‖P ψ₀‖ ≤ 1`.  So their difference is at most `1`, and `eq:grid-dyn` holds with the
`min {1, ·}` of the manuscript (`thm_grid_dyn_min`).

`grid_normalisation_threshold`: the threshold of `cor:norm` at cutoff `2K` for the normalised grid
state of `grid_observable_normalised` (`(δ₁ K^{-5/2})² ≤ 1/2` gives `‖P ψ₀‖² ≥ 1/2`, from
`coulomb_normalisation_threshold` at cutoff `2K`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset Set MeasureTheory

namespace PlaneWaveGridDynamics

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics UnitAddTorus

noncomputable section

local instance unitAddCircleMeasureSpaceForMin : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

/-- A complex number in `[0, c]`: zero imaginary part and real part in `[0, c]`. -/
def InUnitSeg (z : ℂ) (c : ℝ) : Prop := z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ c

lemma norm_sub_le_of_inUnitSeg {z w : ℂ} {c d : ℝ} (hz : InUnitSeg z c) (hw : InUnitSeg w d)
    (hc : c ≤ 1) (hd : d ≤ 1) : ‖z - w‖ ≤ 1 := by
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨hw0, hw1, hw2⟩ := hw
  have e : z - w = ((z.re - w.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hz0, hw0]
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- `⟪z, c z⟫ = Re c · |z|²` for a real `c`. -/
lemma inner_mul_self_real {c : ℂ} (hc : c.im = 0) (z : ℂ) :
    ⟪z, c * z⟫_ℂ = ((c.re * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  have hcr : c = ((c.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hc])
  calc ⟪z, c * z⟫_ℂ = c * z * (starRingEnd ℂ) z := RCLike.inner_apply _ _
    _ = c * (z * (starRingEnd ℂ) z) := by ring
    _ = ((c.re : ℝ) : ℂ) * (((‖z‖ : ℝ) : ℂ) ^ 2) := by
        rw [Complex.mul_conj']
        exact congrArg (· * _) hcr
    _ = ((c.re * ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring

variable {eta : ℕ}

/-- For a multiplier with values in `[0, 1]`, `⟪f, G f⟫ ∈ [0, ‖f‖²]`. -/
theorem inner_mulCLM_mem (G : C(MolecularPositionTorus eta, ℂ))
    (hG : ∀ x, (G x).im = 0 ∧ 0 ≤ (G x).re ∧ (G x).re ≤ 1) (f : MolecularPositionL2 eta) :
    InUnitSeg ⟪f, mulCLM G f⟫_ℂ (‖f‖ ^ 2) := by
  have hpt : ∀ x, ⟪f x, G x * f x⟫_ℂ = (((G x).re * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    exact inner_mul_self_real (hG x).1 (f x)
  have hae : (fun x => ⟪f x, (mulCLM G f) x⟫_ℂ) =ᵐ[volume]
      fun x => (((G x).re * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [mulCLM_ae G f] with x hx
    rw [hx, hpt x]
  have hself : (fun x => ⟪f x, f x⟫_ℂ) = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hint : Integrable (fun x => ‖f x‖ ^ 2) (volume : Measure (MolecularPositionTorus eta)) :=
    (Lp.memLp f).integrable_norm_pow two_ne_zero
  have hint2 : Integrable (fun x => (G x).re * ‖f x‖ ^ 2)
      (volume : Measure (MolecularPositionTorus eta)) := by
    refine hint.bdd_mul (c := 1) ?_ ?_
    · exact (Complex.continuous_re.comp G.continuous).aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [(hG x).2.1, (hG x).2.2]
  have hnorm : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def (𝕜 := ℂ), hself, integral_complex_ofReal]
    simp
  rw [MeasureTheory.L2.inner_def (𝕜 := ℂ), integral_congr_ae hae, integral_complex_ofReal]
  refine ⟨Complex.ofReal_im _, ?_, ?_⟩
  · rw [Complex.ofReal_re]
    exact integral_nonneg fun x => mul_nonneg (hG x).2.1 (sq_nonneg _)
  · rw [Complex.ofReal_re, hnorm]
    refine integral_mono hint2 hint fun x => ?_
    have h1 := (hG x).2.2
    have h2 := sq_nonneg ‖f x‖
    nlinarith

/-- For `χ` with values in `[0, 1]`, `⟪u, O_g u⟫ ∈ [0, ‖u‖²]`. -/
theorem inner_posObs_mem {m : ℕ} (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχ : ∀ y, (χ y).im = 0 ∧ 0 ≤ (χ y).re ∧ (χ y).re ≤ 1) (u : EuclideanSpace ℂ (RCfg eta m)) :
    InUnitSeg ⟪u, posObs a χ u⟫_ℂ (‖u‖ ^ 2) := by
  have hpt : ∀ j : RCfg eta m, ⟪u j, posObs a χ u j⟫_ℂ =
      (((χ (gridPoint (j a))).re * ‖u j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [posObs_apply]
    exact inner_mul_self_real (hχ _).1 (u j)
  have hsum : ⟪u, posObs a χ u⟫_ℂ = ((∑ j, (χ (gridPoint (j a))).re * ‖u j‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.inner_apply]
    simp_rw [hpt]
    push_cast
    rfl
  rw [hsum]
  refine ⟨Complex.ofReal_im _, ?_, ?_⟩
  · rw [Complex.ofReal_re]
    exact sum_nonneg fun j _ => mul_nonneg (hχ _).2.1 (sq_nonneg _)
  · rw [Complex.ofReal_re, EuclideanSpace.norm_eq, Real.sq_sqrt (sum_nonneg fun j _ => sq_nonneg _)]
    refine sum_le_sum fun j _ => ?_
    have h1 := (hχ (gridPoint (j a))).2.2
    have h2 := sq_nonneg ‖u j‖
    nlinarith

lemma regFun_mem (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχ : ∀ y, (χ y).im = 0 ∧ 0 ≤ (χ y).re ∧ (χ y).re ≤ 1) (x : MolecularPositionTorus eta) :
    ((regFun a χ) x).im = 0 ∧ 0 ≤ ((regFun a χ) x).re ∧ ((regFun a χ) x).re ≤ 1 :=
  hχ _

variable {ν : Type} [Fintype ν]

/-- **`eq:grid-dyn` with the trivial bound** (`prop:grid-dyn`). Under the hypotheses of
`thm_grid_dyn`, for a `[0,1]`-valued `χ` and `‖ψ₀‖ = 1`,
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤ min {1, C [K^{-5} + t K^{-5/2}]}`, with
`C [K^{-5} + t K^{-5/2}]` the bound of `thm_grid_dyn`. -/
theorem thm_grid_dyn_min (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    ∃ U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, Continuous fun t => U t ψ) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasCoulombHamiltonian sys L (U t f) (U t h)) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) ∧
      (∀ φ ζ : ℝ → MolecularPositionL2 eta, (∀ t, HasCoulombHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
        (∀ x, Continuous fun t => Ug t x) ∧
        (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t x)) ∧
        (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
        ∀ ψ₀ h₀ h₁ : MolecularPositionL2 eta, HasCoulombHamiltonian sys L ψ₀ h₀ →
          HasCoulombHamiltonian sys L h₀ h₁ → ‖ψ₀‖ = 1 →
          ∀ (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (CM : ℕ → ℝ),
          HChi (2 * Real.pi / L) (mFourierCoeff χ) CM →
          (∀ y, (χ y).im = 0 ∧ 0 ≤ (χ y).re ∧ (χ y).re ≤ 1) →
          let A := gridConsts sys L molecularCanonicalUnitHardyConstant
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) a (mFourierCoeff χ) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let ψg := Ug t (idft (regCoeff m ((physMap eta).symm ψ₀)))
            ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a χ ψg⟫_ℂ‖ ≤
              min 1 ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
                A.2.1 * t * Real.sqrt (1 / K) ^ 5) := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, hrest⟩ := thm_grid_dyn sys L hL
  refine ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, fun m κ hκ => ?_⟩
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := hrest m κ hκ
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro ψ₀ h₀ h₁ hψ₀ hh₀ hnorm a χ CM hc hχ A hm hK t ht K ψg
  have hreal : ∀ y, conj (χ y) = χ y := fun y => by
    apply Complex.ext
    · simp
    · simp [(hχ y).1]
  have h := hbound ψ₀ h₀ h₁ hψ₀ hh₀ a χ CM hc hreal hm hK t ht
  refine le_min ?_ h
  -- both expectations lie in `[0, 1]`
  have h1 : InUnitSeg ⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ (‖U t ψ₀‖ ^ 2) :=
    inner_mulCLM_mem (regFun a χ) (regFun_mem a χ hχ) (U t ψ₀)
  have h2 : InUnitSeg ⟪ψg, posObs a χ ψg⟫_ℂ (‖ψg‖ ^ 2) := inner_posObs_mem a χ hχ ψg
  have hUt : ‖U t ψ₀‖ ^ 2 ≤ 1 := by rw [LinearIsometryEquiv.norm_map, hnorm]; norm_num
  have hψg : ‖ψg‖ ^ 2 ≤ 1 := by
    have e : ‖ψg‖ = ‖regCoeff m ((physMap eta).symm ψ₀)‖ := by
      show ‖Ug t (idft (regCoeff m ((physMap eta).symm ψ₀)))‖ = _
      rw [LinearIsometryEquiv.norm_map, ← dftLIE_symm_apply, LinearIsometryEquiv.norm_map]
    have h3 : ‖regCoeff m ((physMap eta).symm ψ₀)‖ ≤ 1 := by
      refine (norm_regCoeff_le _).trans ?_
      rw [LinearIsometryEquiv.norm_map, hnorm]
    rw [e]
    have h4 := norm_nonneg (regCoeff m ((physMap eta).symm ψ₀))
    nlinarith
  exact norm_sub_le_of_inUnitSeg h1 h2 hUt hψg

end

/-! ## The threshold of `cor:norm` on the grid -/

section Threshold

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- The tail constant `δ₁` with the canonical constants is nonnegative for nonnegative data. -/
lemma obsTailConst_canonical_nonneg (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    {s0 hu hs hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    0 ≤ obsTailConst sys L molecularCanonicalUnitHardyConstant (molecularCanonicalLowConstant L)
      (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L) s0 hu hs hv := by
  obtain ⟨hBlow, hCs, hBker, -⟩ := molecularCanonicalTailConstants_spec L hL
  have hb := relB_nonneg sys L molecularCanonicalUnitHardyConstant
    (finiteCoulombPhysicalMassConstant_nonneg _ _ _)
  have hM := sys.one_le_maxMass
  have hκ' : 0 ≤ finiteCoulombPhysicalTailConstant sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) (sys.maxMass * (s0 + 2 * (2 * hu +
        2 * relB sys L molecularCanonicalUnitHardyConstant * s0))) :=
    finiteCoulombPhysicalTailConstant_nonneg sys L _ hBlow hCs hBker (by positivity)
  rw [obsTailConst]
  positivity

/-- **The threshold of `cor:norm` on the grid.** For `‖ψ₀‖ = 1`, `ψ₀ ∈ D(H²)`, `m ≥ 8` and
`K = 2πm/L ≥ 8`, as soon as `(δ₁ K^{-5/2})² ≤ 1/2`, the grid datum of `grid_observable_normalised`
(the register coefficients of `P ψ₀`, `P` at cutoff `2K`) satisfies `‖P ψ₀‖² ≥ 1/2`; in particular
it is not zero (`coulomb_normalisation_threshold` at cutoff `2K`). -/
theorem grid_normalisation_threshold (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) (m : ℕ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) (ψ₀ h₀ h₁ : MolecularPositionL2 eta)
    (hψ₀ : HasCoulombHamiltonian sys L ψ₀ h₀) (hh₀ : HasCoulombHamiltonian sys L h₀ h₁)
    (hnorm : ‖ψ₀‖ = 1)
    (hthr : (obsTailConst sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖ *
        Real.sqrt (1 / ((2 * Real.pi / L) * m)) ^ 5) ^ 2 ≤ 1 / 2) :
    1 / 2 ≤ ‖regCoeff m ((physMap eta).symm ψ₀)‖ ^ 2 ∧ regCoeff m ((physMap eta).symm ψ₀) ≠ 0 := by
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  set δ₁ := obsTailConst sys L molecularCanonicalUnitHardyConstant
    (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
    (molecularCanonicalKernelConstant L) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖ with hδ₁
  have hδ0 : 0 ≤ δ₁ := obsTailConst_canonical_nonneg sys L hL (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _)
  set g : ℝ := 2 * Real.pi / L with hgdef
  have hg : 0 < g := by positivity
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hK2 : 2 ≤ g * ((2 * m : ℕ) : ℝ) := by rw [h2m]; linarith
  have h2gK : 2 * g ≤ g * ((2 * m : ℕ) : ℝ) := by
    rw [h2m]
    have : (8 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hK₂pos : 0 < g * ((2 * m : ℕ) : ℝ) := by linarith
  have hρ₂ : Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1 := by
    rw [Real.sq_sqrt (by positivity)]
    exact one_div_mul_cancel hK₂pos.ne'
  have hρle : Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ≤ Real.sqrt (1 / (g * m)) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hK₂pos (by show 0 < g * (m : ℝ); linarith), h2m, one_mul, one_mul]
    have e : g * (2 * (m : ℝ)) = 2 * (g * m) := by ring
    rw [e]
    linarith
  have h2 : δ₁ * Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 5 ≤ δ₁ * Real.sqrt (1 / (g * m)) ^ 5 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hρle 5) hδ0
  have hthr' : (δ₁ * Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 5) ^ 2 ≤ 1 / 2 :=
    (pow_le_pow_left₀ (mul_nonneg hδ0 (pow_nonneg (Real.sqrt_nonneg _) 5)) h2 2).trans hthr
  obtain ⟨hhalf, -⟩ := coulomb_normalisation_threshold sys L hL (2 * m) _ _ _ _ hK2
    (Real.sqrt_nonneg _) hρ₂ hBlow hCs hBker h2gK hLow hKernelScale hSobolev ψ₀ h₀ h₁ hψ₀ hh₀
    hnorm hthr'
  have hPx : ‖regCoeff m ((physMap eta).symm ψ₀)‖ =
      ‖molecularH2Truncate (2 * m) ((physMap eta).symm ψ₀)‖ := by
    rw [← (regEmb m).norm_map, regEmb_regCoeff]
  rw [← hPx] at hhalf
  refine ⟨hhalf, fun h0 => ?_⟩
  rw [h0, norm_zero] at hhalf
  norm_num at hhalf

end Threshold

end PlaneWaveGridDynamics

end DevGD7
-- END SOURCE dev/DevGD7.lean

-- BEGIN SOURCE dev/DevGS1.lean
-- SHA256 c027f5ea0469de7d5dc6ca8c8e4da9a66a0b7587b9f02c87982ef0b88f7ce2dc
section DevGS1

/-!
# Grid dynamics: the weighted Kato--Rellich bound of the grid potential

Toward `thm:grid-dyn-sharp`: the second-order estimates of `lem:grid-KR2` need the weight of the
grid potential applied to a state, `‖W (V u)‖` with the mass-weighted weight `W = wM`
(`eq:wKR`).  On the register the transfer `τ` of a grid term changes the momentum of one register
cyclically; the centred representative is the shortest representative, so

  `|gl(x + y)| ≤ |gl x + gl y|`  and  `W q ≤ 2 W p + 4 |τ|²`

for every connected pair, *wraps included* (`nsq_gl_add_le`, `wM_le_of_gRel2`,
`wM_le_of_spec1`).  The first part `2 W p` gives the Kato--Rellich bound of the potential applied
to `W u`, with a small coefficient on the second moment `‖W² u‖`; the second part has the
coefficients `|κ(τ)| |τ|² ≤ γ` on the support `‖τ‖∞ ≤ 2m` of the kernel, whose column `ℓ²` sums
are at most `γ² (4m+1)³` — the truncation is what makes them finite — and the slice-Young
inequality gives `4 √53 γ (4m+1)^{3/2} ‖wTot u‖` (the factor `4` from `4 |τ|²`), the growth
`K^{3/2}` of `lem:grid-KR2` (`norm_wM_vGridK_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace PlaneWaveGridDynamics

open PlaneWaveGrid

/-! ## The centred representative is the shortest -/

section Centred

variable {M : ℕ}

lemma abs_gl_add_le (x y : GMode (2 * M + 1)) (c : Fin 3) :
    |gl (x + y) c| ≤ |gl x c + gl y c| := by
  have he : ((gl (x + y) c : ℤ) : ZMod (2 * M + 1)) =
      ((gl x c + gl y c : ℤ) : ZMod (2 * M + 1)) := by
    simp only [gl, Pi.add_apply, Int.cast_add, ZMod.coe_valMinAbs]
  have h := ZMod.natAbs_min_of_le_div_two (2 * M + 1) (gl (x + y) c) (gl x c + gl y c) he
    (ZMod.natAbs_valMinAbs_le _)
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  exact_mod_cast h

lemma nsq_add_le (x y : Lat3) : nsq (x + y) ≤ 2 * nsq x + 2 * nsq y := by
  simp only [nsq, Pi.add_apply]
  push_cast
  nlinarith [sq_nonneg (((x 0 : ℤ) : ℝ) - y 0), sq_nonneg (((x 1 : ℤ) : ℝ) - y 1),
    sq_nonneg (((x 2 : ℤ) : ℝ) - y 2)]

/-- `|gl (x + y)|² ≤ 2 |gl x|² + 2 |gl y|²`, wraps included. -/
lemma nsq_gl_add_le (x y : GMode (2 * M + 1)) :
    nsq (gl (x + y)) ≤ 2 * nsq (gl x) + 2 * nsq (gl y) := by
  have h : nsq (gl (x + y)) ≤ nsq (gl x + gl y) := by
    rw [nsq_eq_sum, nsq_eq_sum]
    refine sum_le_sum fun c _ => ?_
    have h1 := abs_gl_add_le x y c
    have h2 : |((gl (x + y) c : ℤ) : ℝ)| ≤ |(((gl x + gl y) c : ℤ) : ℝ)| := by
      simp only [Pi.add_apply]
      exact_mod_cast h1
    rw [← sq_abs (((gl (x + y) c : ℤ) : ℝ)), ← sq_abs ((((gl x + gl y) c : ℤ) : ℝ))]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  exact h.trans (nsq_add_le _ _)

end Centred

/-! ## The weight across a transfer -/

section Weight

variable {eta m : ℕ}

lemma wM_split (P : RegParticles eta) (i : Fin eta) (q : RCfg eta m) :
    wM P q = 1 + nsq (gl (q i)) / P.mass i + ∑ k ∈ univ.erase i, nsq (gl (q k)) / P.mass k := by
  unfold wM
  rw [← Finset.add_sum_erase _ _ (mem_univ i)]
  ring

/-- Across a one-register transfer: `W q ≤ 2 W p + 2 |τ|²`. -/
lemma wM_le_of_spec1 (P : RegParticles eta) {i : Fin eta} {q p : RCfg eta m} (h : Spec1 i q p) :
    wM P q ≤ 2 * wM P p + 2 * nsq (gTau i q p) := by
  have h1 : nsq (gl (q i)) ≤ 2 * nsq (gl (p i)) + 2 * nsq (gTau i q p) := by
    have h0 := nsq_gl_add_le (p i) (q i - p i)
    rw [add_sub_cancel] at h0
    simpa only [gTau] using h0
  have hm := P.one_le_mass i
  have hmpos := P.mass_pos i
  have hτ := nsq_nonneg (gTau i q p)
  have h2 : nsq (gl (q i)) / P.mass i ≤ 2 * (nsq (gl (p i)) / P.mass i) + 2 * nsq (gTau i q p) := by
    have h3 : nsq (gl (q i)) / P.mass i ≤ (2 * nsq (gl (p i)) + 2 * nsq (gTau i q p)) / P.mass i :=
      div_le_div_of_nonneg_right h1 hmpos.le
    have h4 : 2 * nsq (gTau i q p) / P.mass i ≤ 2 * nsq (gTau i q p) :=
      div_le_self (by positivity) hm
    calc nsq (gl (q i)) / P.mass i ≤ (2 * nsq (gl (p i)) + 2 * nsq (gTau i q p)) / P.mass i := h3
      _ = 2 * (nsq (gl (p i)) / P.mass i) + 2 * nsq (gTau i q p) / P.mass i := by ring
      _ ≤ _ := by linarith
  have hrest : ∑ k ∈ univ.erase i, nsq (gl (q k)) / P.mass k =
      ∑ k ∈ univ.erase i, nsq (gl (p k)) / P.mass k :=
    sum_congr rfl fun k hk => by rw [h k (ne_of_mem_erase hk)]
  have hR0 : 0 ≤ ∑ k ∈ univ.erase i, nsq (gl (p k)) / P.mass k :=
    sum_nonneg fun k _ => div_nonneg (nsq_nonneg _) (P.mass_pos k).le
  have hp0 : 0 ≤ nsq (gl (p i)) / P.mass i := div_nonneg (nsq_nonneg _) hmpos.le
  rw [wM_split P i q, wM_split P i p, hrest]
  linarith

/-- Across a pair transfer: `W q ≤ 2 W p + 4 |τ|²`. -/
lemma wM_le_of_gRel2 (P : RegParticles eta) {i j : Fin eta} (hij : i ≠ j) {q p : RCfg eta m}
    (h : gRel2 i j q p) : wM P q ≤ 2 * wM P p + 4 * nsq (gTau i q p) := by
  have hqj : q j - p j = -(q i - p i) := by
    have := h.2
    linear_combination this
  have hi : nsq (gl (q i)) ≤ 2 * nsq (gl (p i)) + 2 * nsq (gTau i q p) := by
    have h0 := nsq_gl_add_le (p i) (q i - p i)
    rw [add_sub_cancel] at h0
    simpa only [gTau] using h0
  have hj : nsq (gl (q j)) ≤ 2 * nsq (gl (p j)) + 2 * nsq (gTau i q p) := by
    have h0 := nsq_gl_add_le (p j) (q j - p j)
    rw [add_sub_cancel, hqj, gl_neg, nsq_neg] at h0
    simpa only [gTau] using h0
  have hmi := P.one_le_mass i
  have hmj := P.one_le_mass j
  have hτ := nsq_nonneg (gTau i q p)
  have hdiv : ∀ (k : Fin eta) (a b : ℝ), 0 ≤ b → a ≤ 2 * nsq (gl (p k)) + 2 * b →
      a / P.mass k ≤ 2 * (nsq (gl (p k)) / P.mass k) + 2 * b := by
    intro k a b hb hab
    have hmk := P.one_le_mass k
    have hmpos := P.mass_pos k
    have h3 : a / P.mass k ≤ (2 * nsq (gl (p k)) + 2 * b) / P.mass k :=
      div_le_div_of_nonneg_right hab hmpos.le
    have h4 : 2 * b / P.mass k ≤ 2 * b := div_le_self (by positivity) hmk
    calc a / P.mass k ≤ (2 * nsq (gl (p k)) + 2 * b) / P.mass k := h3
      _ = 2 * (nsq (gl (p k)) / P.mass k) + 2 * b / P.mass k := by ring
      _ ≤ _ := by linarith
  have h1 := hdiv i _ _ hτ hi
  have h2 := hdiv j _ _ hτ hj
  -- split off `i` and `j`
  have hsplit : ∀ r : RCfg eta m, wM P r = 1 + nsq (gl (r i)) / P.mass i +
      nsq (gl (r j)) / P.mass j + ∑ k ∈ (univ.erase i).erase j, nsq (gl (r k)) / P.mass k := by
    intro r
    rw [wM_split P i r, ← Finset.add_sum_erase _ _ (mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩)]
    ring
  have hrest : ∑ k ∈ (univ.erase i).erase j, nsq (gl (q k)) / P.mass k =
      ∑ k ∈ (univ.erase i).erase j, nsq (gl (p k)) / P.mass k :=
    sum_congr rfl fun k hk => by
      have hkj := ne_of_mem_erase hk
      have hki := ne_of_mem_erase (mem_of_mem_erase hk)
      rw [h.1 k hki hkj]
  have hR0 : 0 ≤ ∑ k ∈ (univ.erase i).erase j, nsq (gl (p k)) / P.mass k :=
    sum_nonneg fun k _ => div_nonneg (nsq_nonneg _) (P.mass_pos k).le
  have hpi : 0 ≤ nsq (gl (p i)) / P.mass i := div_nonneg (nsq_nonneg _) (P.mass_pos i).le
  have hpj : 0 ≤ nsq (gl (p j)) / P.mass j := div_nonneg (nsq_nonneg _) (P.mass_pos j).le
  rw [hsplit q, hsplit p, hrest]
  linarith

end Weight

/-! ## The weighted transfer bound -/

section Transfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {rel : ι → ι → Prop} {tau : ι → ι → Lat3} {kappa : Lat3 → ℂ} {c : ℝ}

lemma norm_wMul_absVec (w : ι → ℝ) (hw : ∀ q, 0 ≤ w q) (u : EuclideanSpace ℂ ι) :
    ‖wMul w (absVec u)‖ = ‖wMul w u‖ := by
  have hsq : ‖wMul w (absVec u)‖ ^ 2 = ‖wMul w u‖ ^ 2 := by
    rw [norm_wMul_sq w hw, norm_wMul_sq w hw]
    refine sum_congr rfl fun q _ => ?_
    simp [absVec]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- Minkowski for pointwise domination by a combination of two vectors. -/
lemma norm_le_add2_of_pointwise {X A B : EuclideanSpace ℂ ι} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ q, ‖X q‖ ≤ a * ‖A q‖ + b * ‖B q‖) : ‖X‖ ≤ a * ‖A‖ + b * ‖B‖ := by
  have h3 := norm_le_add3_of_pointwise (X := X) (A := ((a : ℝ) : ℂ) • A) (B := ((b : ℝ) : ℂ) • B)
    (C := 0) (fun q => by
      simp only [PiLp.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, PiLp.zero_apply, norm_zero, add_zero]
      exact h q)
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha,
    Real.norm_of_nonneg hb, norm_zero, add_zero] at h3
  exact h3

/-- **Weighted transfer bound.** For a transfer kernel with coefficients bounded by `c coul`,
supported in the box of radius `R`, on whose connected pairs `W q ≤ 2 W p + A |τ|²`:
`‖W (K u)‖ ≤ 2 (c 26J ‖W u‖ + c √(1378/J) ‖σ (W u)‖) + A c √(53 (2R+1)³) ‖σ u‖`, with the slice
weight `σ`. -/
lemma norm_wMul_kOp_tk_le (hk : KernelBound kappa c) (hc : 0 ≤ c) (hrow : RowInj rel tau)
    (hcol : ColInj rel tau) {σ : Type*} [DecidableEq σ] {S : ι → σ} {X : ι → Lat3}
    (hS : SliceData rel S X) {W : ι → ℝ} (hW0 : ∀ q, 0 ≤ W q) {A : ℝ} (hA : 0 ≤ A)
    (hWcomp : ∀ q p, rel q p → W q ≤ 2 * W p + A * nsq (tau q p))
    {R : ℕ} (hsupp : ∀ x, ¬ InBox R x → kappa x = 0) (J : ℕ) (hJ : 1 ≤ J)
    (u : EuclideanSpace ℂ ι) :
    ‖wMul W (kOp (tk rel tau kappa) u)‖ ≤
      2 * (c * (26 * J) * ‖wMul W u‖ + c * Real.sqrt (1378 / J) *
        ‖wMul (sliceWeight X) (wMul W u)‖) +
        A * (c * Real.sqrt (53 * (2 * R + 1) ^ 3)) * ‖wMul (sliceWeight X) u‖ := by
  classical
  set k1 : Lat3 → ℂ := fun x => ((‖kappa x‖ : ℝ) : ℂ) with hk1
  set k2 : Lat3 → ℂ := fun x => ((‖kappa x‖ * nsq x : ℝ) : ℂ) with hk2
  set Y1 := kOp (tk rel tau k1) (absVec (wMul W u)) with hY1
  set Y2 := kOp (tk rel tau k2) (absVec u) with hY2
  -- the entries of `Y1`, `Y2` are nonnegative reals
  have hY1q : ∀ q, ‖Y1 q‖ = ∑ p, ‖tk rel tau kappa q p‖ * (W p * ‖u p‖) := by
    intro q
    have e : Y1 q = ((∑ p, ‖tk rel tau kappa q p‖ * (W p * ‖u p‖) : ℝ) : ℂ) := by
      rw [hY1, kOp_apply]
      push_cast
      refine sum_congr rfl fun p _ => ?_
      by_cases hr : rel q p
      · rw [tk_of_rel hr, tk_of_rel hr]
        simp only [absVec, wMul_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hW0 p),
          k1]
        push_cast
        ring
      · rw [tk_of_not_rel hr, tk_of_not_rel hr]
        simp
    rw [e, Complex.norm_real, Real.norm_of_nonneg]
    exact sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (mul_nonneg (hW0 p) (norm_nonneg _))
  have hY2q : ∀ q, ‖Y2 q‖ = ∑ p, ‖tk rel tau kappa q p‖ * nsq (tau q p) * ‖u p‖ := by
    intro q
    have e : Y2 q = ((∑ p, ‖tk rel tau kappa q p‖ * nsq (tau q p) * ‖u p‖ : ℝ) : ℂ) := by
      rw [hY2, kOp_apply]
      push_cast
      refine sum_congr rfl fun p _ => ?_
      by_cases hr : rel q p
      · rw [tk_of_rel hr, tk_of_rel hr]
        simp only [absVec, k2]
        push_cast
        ring
      · rw [tk_of_not_rel hr, tk_of_not_rel hr]
        simp
    rw [e, Complex.norm_real, Real.norm_of_nonneg]
    exact sum_nonneg fun p _ => mul_nonneg (mul_nonneg (norm_nonneg _) (nsq_nonneg _))
      (norm_nonneg _)
  -- pointwise domination
  have hpt : ∀ q, ‖(wMul W (kOp (tk rel tau kappa) u)) q‖ ≤ 2 * ‖Y1 q‖ + A * ‖Y2 q‖ := by
    intro q
    rw [hY1q, hY2q, wMul_apply, kOp_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hW0 q),
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hW0 q)).trans ?_
    rw [Finset.mul_sum]
    refine sum_le_sum fun p _ => ?_
    rw [norm_mul]
    by_cases hr : rel q p
    · have hw := hWcomp q p hr
      have h0 : 0 ≤ ‖tk rel tau kappa q p‖ * ‖u p‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc W q * (‖u p‖ * ‖tk rel tau kappa q p‖)
          = W q * (‖tk rel tau kappa q p‖ * ‖u p‖) := by ring
        _ ≤ (2 * W p + A * nsq (tau q p)) * (‖tk rel tau kappa q p‖ * ‖u p‖) :=
            mul_le_mul_of_nonneg_right hw h0
        _ = 2 * (‖tk rel tau kappa q p‖ * (W p * ‖u p‖)) +
            A * (‖tk rel tau kappa q p‖ * nsq (tau q p) * ‖u p‖) := by ring
    · rw [tk_of_not_rel hr, norm_zero]
      simp
  refine (norm_le_add2_of_pointwise (by norm_num) hA hpt).trans ?_
  -- the first vector: the Kato--Rellich bound for `|κ|` applied to `|W u|`
  have hk1b : KernelBound k1 c := fun x => by
    rw [hk1, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact hk x
  have h1 := norm_kOp_tk_le hk1b hc hrow hcol hS J hJ (absVec (wMul W u))
  rw [norm_absVec, norm_wMul_absVec _ (fun q => (sliceWeight_pos X q).le)] at h1
  -- the second vector: slice-Young with the column sums `c² (2R+1)³`
  have hsupp2 : ∀ q p, tk rel tau k2 q p ≠ 0 → rel q p := fun q p h => rel_of_tk_ne_zero h
  have hcol2 : ∀ p, ∑ q, ‖tk rel tau k2 q p‖ ^ 2 ≤ c ^ 2 * (2 * R + 1) ^ 3 := by
    intro p
    rw [sum_col_eq rel tau k2 p (fun z => ‖z‖ ^ 2) (by simp)]
    set s := univ.filter fun q => rel q p
    have hterm : ∀ q ∈ s, ‖k2 (tau q p)‖ ^ 2 ≤
        (if InBox R (tau q p) then c ^ 2 else 0) := by
      intro q _
      by_cases hb : InBox R (tau q p)
      · rw [if_pos hb]
        simp only [hk2]
        rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (nsq_nonneg _))]
        have hkb := hk (tau q p)
        have hcn : coul (tau q p) * nsq (tau q p) ≤ 1 := by
          unfold coul
          by_cases h0 : nsq (tau q p) = 0
          · rw [h0]; norm_num
          · rw [one_div, inv_mul_cancel₀ h0]
        have h3 : ‖kappa (tau q p)‖ * nsq (tau q p) ≤ c := by
          calc ‖kappa (tau q p)‖ * nsq (tau q p) ≤ c * coul (tau q p) * nsq (tau q p) :=
                mul_le_mul_of_nonneg_right hkb (nsq_nonneg _)
            _ = c * (coul (tau q p) * nsq (tau q p)) := by ring
            _ ≤ c * 1 := mul_le_mul_of_nonneg_left hcn hc
            _ = c := mul_one c
        exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (nsq_nonneg _)) h3 2
      · rw [if_neg hb]
        simp [hk2, hsupp _ hb]
    calc ∑ q ∈ s, ‖k2 (tau q p)‖ ^ 2 ≤ ∑ q ∈ s, (if InBox R (tau q p) then c ^ 2 else 0) :=
          sum_le_sum hterm
      _ ≤ ∑ x ∈ PlaneWaveGrid.box R, c ^ 2 := by
          rw [← Finset.sum_filter]
          refine sum_comp_le_of_injOn _ (fun q => tau q p) ?_ (fun _ => c ^ 2)
            (PlaneWaveGrid.box R) ?_ (fun _ _ => sq_nonneg c)
          · intro q hq q' hq' h
            exact hcol q q' p (mem_filter.mp (mem_filter.mp hq).1).2
              (mem_filter.mp (mem_filter.mp hq').1).2 h
          · intro q hq
            exact mem_box.mpr (mem_filter.mp hq).2
      _ = c ^ 2 * (2 * R + 1) ^ 3 := by
          rw [sum_const, card_box, nsmul_eq_mul]
          push_cast
          ring
  have h2sq := kOp_sq_le_slice hS (tk rel tau k2) hsupp2 hcol2 (fun p => ‖u p‖)
    (fun _ => norm_nonneg _)
  have hY2sq : ‖Y2‖ ^ 2 ≤ (c * Real.sqrt (53 * (2 * R + 1) ^ 3) *
      ‖wMul (sliceWeight X) u‖) ^ 2 := by
    rw [norm_sq_eq_sum]
    have e1 : ∑ q, ‖Y2 q‖ ^ 2 = ∑ q, (∑ p, ‖tk rel tau k2 q p‖ * ‖u p‖) ^ 2 := by
      refine sum_congr rfl fun q _ => ?_
      rw [hY2q]
      congr 1
      refine sum_congr rfl fun p _ => ?_
      by_cases hr : rel q p
      · rw [tk_of_rel hr, tk_of_rel hr]
        simp only [hk2]
        rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (nsq_nonneg _))]
      · rw [tk_of_not_rel hr, tk_of_not_rel hr]
        simp
    rw [e1]
    refine h2sq.trans (le_of_eq ?_)
    rw [← norm_wMul_sq _ (fun q => (sliceWeight_pos X q).le) u, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity)]
    ring
  have hY2 : ‖Y2‖ ≤ c * Real.sqrt (53 * (2 * R + 1) ^ 3) * ‖wMul (sliceWeight X) u‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hY2sq
  have := mul_le_mul_of_nonneg_left hY2 hA
  have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
  linarith

end Transfer

/-! ## The grid potential -/

section Grid

variable {ν : Type*} [Fintype ν] {eta m : ℕ} (P : RegParticles eta) (D : NucData ν)
  {gamma : ℝ} {κ : Lat3 → ℝ}

/-- The weighted bound of one grid term. -/
lemma norm_wM_gridTerm_le (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0) (t : Term eta ν) (J : ℕ) (hJ : 1 ≤ J)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM P) (kOp (gridTerm eta m D κ t) u)‖ ≤
      coupling eta D gamma t * (2 * (26 * J) * ‖wMul (wM P) u‖ +
        2 * Real.sqrt (1378 / J) * ‖wMul wTot (wMul (wM P) u)‖ +
        4 * Real.sqrt (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) * ‖wMul wTot u‖) := by
  have hc := coupling_nonneg (D := D) hg t
  have hW0 : ∀ q : RCfg eta m, 0 ≤ wM P q := fun q => le_trans zero_le_one (wM_ge_one P q)
  cases t with
  | inl pr =>
    have hsupp' : ∀ x, ¬ InBox (2 * m) x → kgr κ x = 0 := fun x hx => by
      simp [kgr, hsupp x hx]
    have h := norm_wMul_kOp_tk_le (kgr_bound hκ) hg (gRel2_rowInj pr.1.1 pr.1.2)
      (gRel2_colInj pr.1.1 pr.1.2) (gSlice2_data pr.1.1 pr.1.2) hW0 (A := 4) (by norm_num)
      (fun q p h => wM_le_of_gRel2 P (ne_of_lt pr.2) h) hsupp' J hJ u
    have hs1 := norm_wMul_slice_le pr.1.1 (wMul (wM P) u)
    have hs2 := norm_wMul_slice_le pr.1.1 u
    simp only [gridTerm, coupling]
    have hJ0 : (0 : ℝ) ≤ 26 * J := by positivity
    have e1 := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hg (Real.sqrt_nonneg (1378 / J)))
    have e2 := mul_le_mul_of_nonneg_left hs2
      (mul_nonneg hg (Real.sqrt_nonneg (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3)))
    nlinarith [norm_nonneg (wMul (wM P) u)]
  | inr il =>
    have hc' : 0 ≤ D.charge il.2 * gamma := mul_nonneg (D.charge_nonneg il.2) hg
    have hsupp' : ∀ x, ¬ InBox (2 * m) x → kgn D κ il.2 x = 0 := fun x hx => by
      simp [kgn, kgr, hsupp x hx]
    have h := norm_wMul_kOp_tk_le (kgn_bound D hκ il.2) hc' (spec1_rowInj_g il.1)
      (spec1_colInj_g il.1) (slice1_data il.1) hW0 (A := 4) (by norm_num)
      (fun q p h => (wM_le_of_spec1 P h).trans (by linarith [nsq_nonneg (gTau il.1 q p)]))
      hsupp' J hJ u
    have hs1 := norm_wMul_slice_le il.1 (wMul (wM P) u)
    have hs2 := norm_wMul_slice_le il.1 u
    simp only [gridTerm, coupling]
    have e1 := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hc' (Real.sqrt_nonneg (1378 / J)))
    have e2 := mul_le_mul_of_nonneg_left hs2
      (mul_nonneg hc' (Real.sqrt_nonneg (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3)))
    nlinarith [norm_nonneg (wMul (wM P) u)]

/-- **Weighted Kato--Rellich bound of the grid potential** (`lem:grid-KR2`(b), `eq:wKR`):
`‖W (V u)‖ ≤ Z_c (52 J ‖W u‖ + 2 √(1378/J) ‖wTot (W u)‖ + 4 √53 (4m+1)^{3/2} ‖wTot u‖)` for a
kernel of the class `𝒦_K` (bounded by `γ/|ν|²`, supported in `‖ν‖∞ ≤ 2m`). -/
theorem norm_wM_vGridK_le (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0) (J : ℕ) (hJ : 1 ≤ J)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM P) (kOp (vGridK eta m P D κ) u)‖ ≤
      Zc P D gamma * (2 * (26 * J) * ‖wMul (wM P) u‖ +
        2 * Real.sqrt (1378 / J) * ‖wMul wTot (wMul (wM P) u)‖ +
        4 * Real.sqrt (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) * ‖wMul wTot u‖) := by
  rw [kOp_vGridK_eq, map_sum]
  refine (norm_sum_le _ _).trans ?_
  unfold Zc
  rw [Finset.sum_mul]
  refine sum_le_sum fun t _ => ?_
  rw [LinearMap.map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_wM_gridTerm_le P D hg hκ hsupp t J hJ u) (abs_nonneg _)

end Grid

/-! ## Second-order estimates of the grid Hamiltonian -/

section SecondOrder

variable {ν : Type*} [Fintype ν] {eta m : ℕ} (P : RegParticles eta) (D : NucData ν)
  {gamma : ℝ} {κ : Lat3 → ℝ} {g : ℝ}

/-- The constant `Z_c (52 J₀ + 4 √53 m̄ (4m+1)^{3/2})` of the second-order estimates, with the
grid splitting radius `J₀ = J0g (m̄ Z_c) g`; it grows like `K^{3/2}`. -/
noncomputable def secondConst (P : RegParticles eta) (D : NucData ν) (gamma g : ℝ) (m : ℕ) : ℝ :=
  Zc P D gamma * (52 * (J0g (P.maxMass * Zc P D gamma) g : ℝ) +
    4 * Real.sqrt (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) * P.maxMass)

lemma secondConst_nonneg (hg : 0 ≤ gamma) : 0 ≤ secondConst P D gamma g m := by
  unfold secondConst
  have := Zc_nonneg (P := P) (D := D) hg
  have := P.maxMass_pos
  positivity

/-- `eq:wKR` with the splitting radius `J₀`: `‖W (V u)‖ ≤ (g²/4) ‖W² u‖ + C₂ ‖W u‖`. -/
lemma norm_wM_vGridK_le_second (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0) (hgpos : 0 < g)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM P) (kOp (vGridK eta m P D κ) u)‖ ≤
      g ^ 2 / 4 * ‖wMul (wM P) (wMul (wM P) u)‖ + secondConst P D gamma g m * ‖wMul (wM P) u‖ := by
  set J := J0g (P.maxMass * Zc P D gamma) g
  have hZ := Zc_nonneg (P := P) (D := D) hg
  have hM := P.maxMass_pos
  have h := norm_wM_vGridK_le P D hg hκ hsupp J (J0g_pos _ _) u
  have hsmall := J0g_small (mul_nonneg hM.le hZ) hgpos
  have h1 := norm_wMul_wTot_le P (wMul (wM P) u)
  have h2 := norm_wMul_wTot_le P u
  set X := ‖wMul (wM P) (wMul (wM P) u)‖
  set Y := ‖wMul (wM P) u‖
  have hX := norm_nonneg (wMul (wM P) (wMul (wM P) u))
  have hY := norm_nonneg (wMul (wM P) u)
  have hs0 := Real.sqrt_nonneg (1378 / (J : ℝ))
  have hs1 := Real.sqrt_nonneg (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3)
  have e1 : Zc P D gamma * (2 * Real.sqrt (1378 / J) * ‖wMul wTot (wMul (wM P) u)‖) ≤
      g ^ 2 / 4 * X := by
    calc Zc P D gamma * (2 * Real.sqrt (1378 / J) * ‖wMul wTot (wMul (wM P) u)‖)
        ≤ Zc P D gamma * (2 * Real.sqrt (1378 / J) * (P.maxMass * X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) hZ
      _ = 2 * ((P.maxMass * Zc P D gamma) * Real.sqrt (1378 / J)) * X := by ring
      _ ≤ 2 * (g ^ 2 / 8) * X := by
          apply mul_le_mul_of_nonneg_right _ hX
          linarith
      _ = g ^ 2 / 4 * X := by ring
  have e2 : Zc P D gamma * (4 * Real.sqrt (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) *
      ‖wMul wTot u‖) ≤ Zc P D gamma * (4 * Real.sqrt (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) *
        (P.maxMass * Y)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) hZ
  have e3 : secondConst P D gamma g m * Y = Zc P D gamma * (2 * (26 * (J : ℝ)) * Y) +
      Zc P D gamma * (4 * Real.sqrt (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) * (P.maxMass * Y)) := by
    simp only [secondConst, J]
    ring
  have e4 : Zc P D gamma * (2 * (26 * (J : ℝ)) * Y + 2 * Real.sqrt (1378 / J) *
      ‖wMul wTot (wMul (wM P) u)‖ + 4 * Real.sqrt (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) *
        ‖wMul wTot u‖) = Zc P D gamma * (2 * (26 * (J : ℝ)) * Y) +
      Zc P D gamma * (2 * Real.sqrt (1378 / J) * ‖wMul wTot (wMul (wM P) u)‖) +
      Zc P D gamma * (4 * Real.sqrt (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) * ‖wMul wTot u‖) := by
    ring
  linarith

/-- `W² u = W u + (2/g²)(W (H u) - W (V u))`. -/
lemma wM_wM_eq (hgpos : 0 < g) (u : EuclideanSpace ℂ (RCfg eta m)) :
    wMul (wM P) (wMul (wM P) u) = wMul (wM P) u +
      ((2 / g ^ 2 : ℝ) : ℂ) • (wMul (wM P) (Hgrid eta m P D κ g u) -
        wMul (wM P) (kOp (vGridK eta m P D κ) u)) := by
  have hg0 : g ≠ 0 := hgpos.ne'
  ext q
  simp only [wMul_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Hgrid,
    LinearMap.add_apply, kinT]
  have e : (2 / g ^ 2) * (g ^ 2 / 2 * (wM P q - 1)) = wM P q - 1 := by
    field_simp
  have e' : ((2 / g ^ 2 : ℝ) : ℂ) * ((g ^ 2 / 2 * (wM P q - 1) : ℝ) : ℂ) =
      ((wM P q - 1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, e]
  calc ((wM P q : ℝ) : ℂ) * (((wM P q : ℝ) : ℂ) * u q)
      = ((wM P q : ℝ) : ℂ) * u q + ((wM P q : ℝ) : ℂ) * u q * ((wM P q - 1 : ℝ) : ℂ) := by
        push_cast; ring
    _ = _ := by
        rw [← e']
        ring

/-- **Second-order elliptic estimate** (`lem:grid-KR2`(c), `eq:ell2` with `‖W (H u)‖` in place
of `‖H² u‖`):
`‖W² u‖ ≤ 2 ‖W u‖ + (4/g²) ‖W (H u)‖ + (4/g²) C₂ ‖W u‖`, with `C₂ = secondConst = O(K^{3/2})`. -/
theorem second_elliptic (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0) (hgpos : 0 < g)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM P) (wMul (wM P) u)‖ ≤ 2 * ‖wMul (wM P) u‖ +
      4 / g ^ 2 * ‖wMul (wM P) (Hgrid eta m P D κ g u)‖ +
      4 / g ^ 2 * secondConst P D gamma g m * ‖wMul (wM P) u‖ := by
  have hg2 : 0 < g ^ 2 := by positivity
  have hV := norm_wM_vGridK_le_second P D hg hκ hsupp hgpos u
  have h := congrArg norm (wM_wM_eq P D (κ := κ) hgpos u)
  have h1 : ‖wMul (wM P) (wMul (wM P) u)‖ ≤ ‖wMul (wM P) u‖ +
      2 / g ^ 2 * (‖wMul (wM P) (Hgrid eta m P D κ g u)‖ +
        ‖wMul (wM P) (kOp (vGridK eta m P D κ) u)‖) := by
    rw [h]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
  have h2 : 2 / g ^ 2 * (g ^ 2 / 4 * ‖wMul (wM P) (wMul (wM P) u)‖) =
      1 / 2 * ‖wMul (wM P) (wMul (wM P) u)‖ := by
    field_simp
    ring
  have h3 := mul_le_mul_of_nonneg_left hV (by positivity : (0 : ℝ) ≤ 2 / g ^ 2)
  have e : 4 / g ^ 2 = 2 * (2 / g ^ 2) := by ring
  rw [e]
  nlinarith [norm_nonneg (wMul (wM P) (Hgrid eta m P D κ g u))]

/-- `‖W (H w)‖ ≤ (3g²/4) ‖W² w‖ + C₂ ‖W w‖`. -/
theorem norm_wM_Hgrid_le (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0) (hgpos : 0 < g)
    (w : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM P) (Hgrid eta m P D κ g w)‖ ≤
      3 * g ^ 2 / 4 * ‖wMul (wM P) (wMul (wM P) w)‖ + secondConst P D gamma g m *
          ‖wMul (wM P) w‖ := by
  have hV := norm_wM_vGridK_le_second P D hg hκ hsupp hgpos w
  have hT : ‖wMul (wM P) (wMul (kinT eta m P g) w)‖ ≤ g ^ 2 / 2 *
      ‖wMul (wM P) (wMul (wM P) w)‖ := by
    have hW0 : ∀ q : RCfg eta m, 0 ≤ wM P q := fun q => le_trans zero_le_one (wM_ge_one P q)
    have hpt : ∀ q, ‖(wMul (wM P) (wMul (kinT eta m P g) w)) q‖ ≤
        ‖((((g ^ 2 / 2 : ℝ) : ℂ)) • wMul (wM P) (wMul (wM P) w)) q‖ := by
      intro q
      simp only [wMul_apply, PiLp.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (hW0 q), Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ g ^ 2 / 2)]
      have hk0 : 0 ≤ kinT eta m P g q := by
        unfold kinT
        have := wM_ge_one P q
        have : 0 ≤ g ^ 2 := sq_nonneg g
        nlinarith
      rw [Real.norm_of_nonneg hk0]
      have hk : kinT eta m P g q ≤ g ^ 2 / 2 * wM P q := by
        unfold kinT
        have := sq_nonneg g
        nlinarith
      have hx := norm_nonneg (w q)
      have := hW0 q
      nlinarith [mul_le_mul_of_nonneg_left hk (mul_nonneg (hW0 q) hx)]
    refine (norm_le_of_pointwise hpt).trans (le_of_eq ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsplit : wMul (wM P) (Hgrid eta m P D κ g w) =
      wMul (wM P) (wMul (kinT eta m P g) w) + wMul (wM P) (kOp (vGridK eta m P D κ) w) := by
    rw [Hgrid, LinearMap.add_apply, map_add]
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- **Second-order forward bound:** `‖H² w‖ ≤ (5g²/8)((3g²/4) ‖W² w‖ + C₂ ‖W w‖) + 26 Z J₀ ‖H w‖`.
-/
theorem second_forward (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0) (hgpos : 0 < g)
    (w : EuclideanSpace ℂ (RCfg eta m)) :
    ‖Hgrid eta m P D κ g (Hgrid eta m P D κ g w)‖ ≤
      5 * g ^ 2 / 8 * (3 * g ^ 2 / 4 * ‖wMul (wM P) (wMul (wM P) w)‖ +
        secondConst P D gamma g m * ‖wMul (wM P) w‖) +
      26 * (P.maxMass * Zc P D gamma) * (J0g (P.maxMass * Zc P D gamma) g : ℝ) *
        ‖Hgrid eta m P D κ g w‖ := by
  have h := (gridRegHam (eta := eta) (m := m) (P := P) (D := D) hg hκ hgpos).op_le
    (Hgrid eta m P D κ g w)
  have h2 := norm_wM_Hgrid_le P D hg hκ hsupp hgpos w
  have hg2 : 0 ≤ 5 * g ^ 2 / 8 := by positivity
  calc ‖Hgrid eta m P D κ g (Hgrid eta m P D κ g w)‖
      ≤ 5 * g ^ 2 / 8 * ‖wMul (wM P) (Hgrid eta m P D κ g w)‖ +
        26 * (P.maxMass * Zc P D gamma) * (J0g (P.maxMass * Zc P D gamma) g : ℝ) *
          ‖Hgrid eta m P D κ g w‖ := h
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h2 hg2) le_rfl

end SecondOrder

end PlaneWaveGridDynamics

end DevGS1
-- END SOURCE dev/DevGS1.lean

-- BEGIN SOURCE dev/DevGS2.lean
-- SHA256 aa302886c57dfbbbd79fe2c050c882ee2227a7876aab8f8a05f792c2e96161ad
section DevGS2

/-!
# Grid dynamics: the second kinetic moment of the projected trajectory

`lem:grid-data2`, first bound: `X(P ψ(t)) ≤ C Ξ K^{3/2}` uniformly in `t`, where
`X(a) = ‖W² a‖` is the second moment with the mass-weighted weight `W = wM` of the register.  The
weighted tails of `ψ(t)` hold at every threshold `λ`: `‖1_{g|p_r| > λ} T u‖ ≤ B(λ) = O(λ^{-1/2})`
(`tails_at_time`).  A layer-cake decomposition over the integer thresholds `k ≤ 4m`,
`|p_r|⁴ ≤ Σ_{k < |p_r|} ((k+1)⁴ - k⁴)`, gives
`Σ_q |q_r|⁴ |(T u)(q)|² ≤ Σ_{k ≤ 4m} ((k+1)⁴ - k⁴) ‖1_{|q_r| > k} T u‖²` (`layer_sum_le`); the
layers `k ≥ k₀` are at most `B(gk)²` and the first `k₀` at most `Ξ₀²`, so the sum is `O(m³)`
(`layer_bound`), the growth of a truncated fourth-derivative norm over the Coulomb cusp; then
`X(P ψ(t)) = O(m^{3/2})` (`second_moment_regCoeff_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace PlaneWaveGridDynamics

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics

/-! ## The layer cake -/

section Layer

/-- The layer cake for the fourth power: for `0 ≤ x ≤ N + 1`,
`x⁴ ≤ Σ_{k ≤ N, k < x} ((k+1)⁴ - k⁴)`. -/
lemma pow_four_le_layer {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : x ≤ N + 1) :
    x ^ 4 ≤ ∑ k ∈ range (N + 1),
      if (k : ℝ) < x then (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) else 0 := by
  set n := ⌈x⌉₊ with hndef
  have hn : n ≤ N + 1 := by
    rw [hndef, Nat.ceil_le]
    exact_mod_cast hN
  have hfilter : (range (N + 1)).filter (fun k : ℕ => (k : ℝ) < x) = range n := by
    ext k
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨_, hk⟩
      exact Nat.lt_ceil.mpr hk
    · intro hk
      exact ⟨lt_of_lt_of_le hk hn, Nat.lt_ceil.mp hk⟩
  rw [← sum_filter, hfilter]
  have e : ∑ k ∈ range n, (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) = (n : ℝ) ^ 4 := by
    have h := Finset.sum_range_sub (fun k : ℕ => ((k : ℝ)) ^ 4) n
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
    rw [h]
    ring
  rw [e]
  exact pow_le_pow_left₀ hx (Nat.le_ceil x) 4

lemma layer_weight_le {k : ℕ} (hk : 1 ≤ k) : ((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4 ≤ 15 *
    (k : ℝ) ^ 3 := by
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [sq_nonneg ((k : ℝ) - 1), mul_le_mul h1 h1 zero_le_one (by linarith)]

lemma layer_weight_nonneg (k : ℕ) : 0 ≤ ((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4 := by
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : (k : ℝ) ^ 4 ≤ ((k : ℝ) + 1) ^ 4 := pow_le_pow_left₀ h0 (by linarith) 4
  linarith

end Layer

/-! ## The register sum -/

section Register

variable {eta m : ℕ}

/-- The register shells at the integer thresholds: `|gl(q_r)| > k` (Euclidean norm). -/
def Shell (r : Fin eta) (k : ℕ) (q : RCfg eta m) : Prop := (k : ℝ) < Real.sqrt (nsq (gl (q r)))

/-- **Layer cake on the register:**
`Σ_q |q_r|⁴ ‖F q‖² ≤ Σ_{k ≤ 4m} ((k+1)⁴ - k⁴) ‖1_{|q_r| > k} F‖²`. -/
lemma layer_sum_le (r : Fin eta) (F : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (fun q => nsq (gl (q r))) F‖ ^ 2 ≤
      ∑ k ∈ range (4 * m + 1), (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * ‖maskOp (Shell r k) F‖ ^ 2 := by
  classical
  rw [norm_wMul_sq _ (fun q => nsq_nonneg _)]
  have hpt : ∀ q : RCfg eta m, (nsq (gl (q r)) * ‖F q‖) ^ 2 ≤
      ∑ k ∈ range (4 * m + 1), (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
        (if Shell r k q then ‖F q‖ ^ 2 else 0) := by
    intro q
    have hx : 0 ≤ Real.sqrt (nsq (gl (q r))) := Real.sqrt_nonneg _
    have hN : Real.sqrt (nsq (gl (q r))) ≤ ((4 * m : ℕ) : ℝ) + 1 := by
      have h1 := nsq_gl_le (q r)
      have h2 : Real.sqrt (nsq (gl (q r))) ≤ Real.sqrt (12 * (m : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
      have h3 : Real.sqrt (12 * (m : ℝ) ^ 2) ≤ 4 * (m : ℝ) := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [sq_nonneg (m : ℝ)]
      push_cast
      linarith
    have hl := pow_four_le_layer hx hN
    have e : (nsq (gl (q r)) * ‖F q‖) ^ 2 = Real.sqrt (nsq (gl (q r))) ^ 4 * ‖F q‖ ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (nsq_nonneg _)]
      ring
    rw [e]
    calc Real.sqrt (nsq (gl (q r))) ^ 4 * ‖F q‖ ^ 2
        ≤ (∑ k ∈ range (4 * m + 1), if (k : ℝ) < Real.sqrt (nsq (gl (q r))) then
            (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) else 0) * ‖F q‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hl (sq_nonneg _)
      _ = ∑ k ∈ range (4 * m + 1), (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
            (if Shell r k q then ‖F q‖ ^ 2 else 0) := by
          rw [Finset.sum_mul]
          refine sum_congr rfl fun k _ => ?_
          unfold Shell
          split_ifs <;> ring
  calc ∑ q, (nsq (gl (q r)) * ‖F q‖) ^ 2
      ≤ ∑ q, ∑ k ∈ range (4 * m + 1), (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
          (if Shell r k q then ‖F q‖ ^ 2 else 0) := sum_le_sum fun q _ => hpt q
    _ = ∑ k ∈ range (4 * m + 1), (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) *
          ∑ q, (if Shell r k q then ‖F q‖ ^ 2 else 0) := by
        rw [Finset.sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ = _ := by
        refine sum_congr rfl fun k _ => ?_
        congr 1
        rw [norm_sq_eq_sum]
        refine sum_congr rfl fun q _ => ?_
        by_cases h : Shell r k q
        · rw [if_pos h, maskOp_apply_of _ _ h]
        · rw [if_neg h, maskOp_apply_of_not _ _ h, norm_zero]
          norm_num

/-- The shells of the cube part are inside the continuum tails. -/
lemma norm_shell_regCoeff_le {g : ℝ} (hg : 0 < g) (r : Fin eta) (k : ℕ)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    ‖maskOp (Shell r k) (regCoeff m x)‖ ≤ ‖tailMask g (g * k) r x‖ := by
  refine (norm_le_of_pointwise (Y := regCoeff m (tailMask g (g * k) r x)) fun q => ?_).trans
    (norm_regCoeff_le _)
  by_cases h : Shell r k q
  · have h' : g * k < g * Real.sqrt (latticeNormSq (liftCfg q r)) :=
      mul_lt_mul_of_pos_left h hg
    rw [maskOp_apply_of _ _ h, regCoeff_apply, regCoeff_apply, tailMask_apply, if_pos h', one_mul]
  · rw [maskOp_apply_of_not _ _ h, norm_zero]
    exact norm_nonneg _


/-- `(a + b)² ≤ 2a² + 2b²`. -/
lemma sq_add_le_two_sq (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- One layer above the threshold: if `x ≤ B(gk) = (2M/(gk)²) Ξ₁ + C₀ (gk)^{-1/2}` and
`1 ≤ k ≤ N + 1`, then `((k+1)⁴ - k⁴) x² ≤ 120 M² Ξ₁²/g⁴ + (30 C₀²/g) (N+1)²`. -/
lemma layer_term_le {k : ℕ} (hk : 1 ≤ k) {N g M Ξ₁ C₀ x : ℝ} (hg : 0 < g) (hx : 0 ≤ x)
    (hxB : x ≤ (2 * M / (g * k) ^ 2) * Ξ₁ + C₀ * Real.sqrt (1 / (g * k)))
    (hkN : (k : ℝ) ≤ N + 1) :
    (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * x ^ 2 ≤
      120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 4 + 30 * C₀ ^ 2 / g * (N + 1) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hgk : 0 < g * k := mul_pos hg hk0
  have hgne : g ≠ 0 := hg.ne'
  have hkne : (k : ℝ) ≠ 0 := hk0.ne'
  have hBsq : ((2 * M / (g * k) ^ 2) * Ξ₁ + C₀ * Real.sqrt (1 / (g * k))) ^ 2 ≤
      8 * M ^ 2 * Ξ₁ ^ 2 / (g * k) ^ 4 + 2 * C₀ ^ 2 / (g * k) := by
    have hs : Real.sqrt (1 / (g * k)) ^ 2 = 1 / (g * k) := Real.sq_sqrt (by positivity)
    have e1 := sq_add_le_two_sq ((2 * M / (g * k) ^ 2) * Ξ₁) (C₀ * Real.sqrt (1 / (g * k)))
    have e2 : 2 * ((2 * M / (g * k) ^ 2) * Ξ₁) ^ 2 = 8 * M ^ 2 * Ξ₁ ^ 2 / (g * k) ^ 4 := by
      field_simp
      ring
    have e3 : 2 * (C₀ * Real.sqrt (1 / (g * k))) ^ 2 = 2 * C₀ ^ 2 / (g * k) := by
      rw [mul_pow, hs]
      ring
    linarith
  have hx2 : x ^ 2 ≤ 8 * M ^ 2 * Ξ₁ ^ 2 / (g * k) ^ 4 + 2 * C₀ ^ 2 / (g * k) :=
    (pow_le_pow_left₀ hx hxB 2).trans hBsq
  have hwk := layer_weight_le hk
  calc (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * x ^ 2
      ≤ (15 * (k : ℝ) ^ 3) * (8 * M ^ 2 * Ξ₁ ^ 2 / (g * k) ^ 4 + 2 * C₀ ^ 2 / (g * k)) :=
        mul_le_mul hwk hx2 (sq_nonneg _) (by positivity)
    _ = 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 4 / k + 30 * C₀ ^ 2 / g * (k : ℝ) ^ 2 := by
        field_simp
        ring
    _ ≤ 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 4 + 30 * C₀ ^ 2 / g * (N + 1) ^ 2 := by
        have h3 : 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 4 / k ≤ 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 4 :=
          div_le_self (by positivity) hk1
        have h4 : (k : ℝ) ^ 2 ≤ (N + 1) ^ 2 := pow_le_pow_left₀ hk0.le hkN 2
        have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 30 * C₀ ^ 2 / g)
        linarith

/-- The layer sum: the `k₀` low layers cost at most `k₀⁴ A` and each of the `N + 1` high layers at
most `B + C (N+1)²`. -/
lemma layer_sum_arith (N k₀ : ℕ) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∑ k ∈ range (N + 1), (if k < k₀ then (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A
      else B + C * ((N : ℝ) + 1) ^ 2) ≤ ((k₀ : ℝ) ^ 4 * A + B + C) * ((N : ℝ) + 1) ^ 3 := by
  have hc : 0 ≤ B + C * ((N : ℝ) + 1) ^ 2 := by positivity
  have hsplit : ∀ k ∈ range (N + 1),
      (if k < k₀ then (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A else B + C * ((N : ℝ) + 1) ^ 2) ≤
      (if k < k₀ then (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A else 0) +
        (B + C * ((N : ℝ) + 1) ^ 2) := by
    intro k _
    split_ifs
    · linarith
    · linarith
  refine (sum_le_sum hsplit).trans ?_
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have hlow : ∑ k ∈ range (N + 1),
      (if k < k₀ then (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A else 0) ≤ (k₀ : ℝ) ^ 4 * A := by
    rw [← sum_filter]
    calc ∑ k ∈ (range (N + 1)).filter (· < k₀), (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A
        ≤ ∑ k ∈ range k₀, (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ =>
            mul_nonneg (layer_weight_nonneg k) hA
          intro k hk
          exact mem_range.mpr (mem_filter.mp hk).2
      _ = (k₀ : ℝ) ^ 4 * A := by
          rw [← Finset.sum_mul]
          have h := Finset.sum_range_sub (fun k : ℕ => ((k : ℝ)) ^ 4) k₀
          simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
          rw [h]
          ring
  rw [Nat.cast_succ]
  have hn1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hn3 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 3 := one_le_pow₀ hn1
  have hn2 : (N : ℝ) + 1 ≤ ((N : ℝ) + 1) ^ 3 := by
    calc (N : ℝ) + 1 = ((N : ℝ) + 1) * 1 := by ring
      _ ≤ ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hn1) (by linarith)
      _ = ((N : ℝ) + 1) ^ 3 := by ring
  have i1 : (k₀ : ℝ) ^ 4 * A ≤ (k₀ : ℝ) ^ 4 * A * ((N : ℝ) + 1) ^ 3 :=
    le_mul_of_one_le_right (by positivity) hn3
  have i2 : ((N : ℝ) + 1) * B ≤ ((N : ℝ) + 1) ^ 3 * B := mul_le_mul_of_nonneg_right hn2 hB
  have e3 : ((N : ℝ) + 1) * (B + C * ((N : ℝ) + 1) ^ 2) =
      ((N : ℝ) + 1) * B + C * ((N : ℝ) + 1) ^ 3 := by ring
  have e4 : ((k₀ : ℝ) ^ 4 * A + B + C) * ((N : ℝ) + 1) ^ 3 =
      (k₀ : ℝ) ^ 4 * A * ((N : ℝ) + 1) ^ 3 + ((N : ℝ) + 1) ^ 3 * B + C * ((N : ℝ) + 1) ^ 3 := by
    ring
  rw [e3, e4]
  linarith

/-- **The layer bound for one register coordinate:** if every shell of `F` is at most `Ξ₀` and the
shells beyond `k₀` are at most `B(gk) = (2M/(gk)²) Ξ₁ + C₀ (gk)^{-1/2}`, then
`‖|q_r|² F‖ ≤ √Q (4m+1)^{3/2}` with `Q = k₀⁴ Ξ₀² + 120 M² Ξ₁²/g⁴ + 30 C₀²/g`. -/
lemma layer_bound {m : ℕ} (r : Fin eta) (F : EuclideanSpace ℂ (RCfg eta m)) {g M Ξ₀ Ξ₁ C₀ : ℝ}
    (hg : 0 < g) (k₀ : ℕ) (hk₀ : 1 ≤ k₀)
    (hlow : ∀ k : ℕ, ‖maskOp (Shell r k) F‖ ≤ Ξ₀)
    (hhigh : ∀ k : ℕ, k₀ ≤ k → ‖maskOp (Shell r k) F‖ ≤
      (2 * M / (g * k) ^ 2) * Ξ₁ + C₀ * Real.sqrt (1 / (g * k))) :
    ‖wMul (fun q => nsq (gl (q r))) F‖ ≤
      Real.sqrt ((k₀ : ℝ) ^ 4 * Ξ₀ ^ 2 + 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 4 + 30 * C₀ ^ 2 / g) *
        Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 := by
  have h1 := layer_sum_le r F
  have hterm : ∀ k ∈ range (4 * m + 1),
      (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * ‖maskOp (Shell r k) F‖ ^ 2 ≤
      (if k < k₀ then (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * Ξ₀ ^ 2 else
        120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 4 + 30 * C₀ ^ 2 / g * (((4 * m : ℕ) : ℝ) + 1) ^ 2) := by
    intro k hk
    by_cases hkk : k < k₀
    · rw [if_pos hkk]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hlow k) 2)
        (layer_weight_nonneg k)
    · rw [if_neg hkk]
      have hkk' : k₀ ≤ k := not_lt.mp hkk
      have hkN : (k : ℝ) ≤ ((4 * m : ℕ) : ℝ) + 1 := by
        have h := mem_range.mp hk
        have h' : (k : ℝ) < ((4 * m + 1 : ℕ) : ℝ) := by exact_mod_cast h
        rw [Nat.cast_succ] at h'
        linarith
      exact layer_term_le (hk₀.trans hkk') hg (norm_nonneg _) (hhigh k hkk') hkN
  have h2 := (sum_le_sum hterm).trans (layer_sum_arith (4 * m) k₀ (sq_nonneg Ξ₀)
    (by positivity : (0 : ℝ) ≤ 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 4)
    (by positivity : (0 : ℝ) ≤ 30 * C₀ ^ 2 / g))
  have hQ0 : 0 ≤ (k₀ : ℝ) ^ 4 * Ξ₀ ^ 2 + 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 4 + 30 * C₀ ^ 2 / g := by
    positivity
  have h3 : ‖wMul (fun q => nsq (gl (q r))) F‖ ^ 2 ≤
      (Real.sqrt ((k₀ : ℝ) ^ 4 * Ξ₀ ^ 2 + 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 4 + 30 * C₀ ^ 2 / g) *
        Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3) ^ 2 := by
    refine (h1.trans h2).trans (le_of_eq ?_)
    rw [mul_pow, Real.sq_sqrt hQ0, ← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul,
      Real.sq_sqrt (by positivity)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

/-- `‖wTot F‖ ≤ ‖F‖ + Σ_r ‖|q_r|² F‖`. -/
lemma norm_wTot_le_layers {m : ℕ} (F : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul wTot F‖ ≤ ‖F‖ + ∑ r : Fin eta, ‖wMul (fun q => nsq (gl (q r))) F‖ := by
  have e : wMul wTot F = F + ∑ r : Fin eta, wMul (fun q => nsq (gl (q r))) F := by
    ext q
    simp only [wMul_apply, PiLp.add_apply, wTot]
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    simp only [wMul_apply]
    push_cast
    rw [add_mul, one_mul, Finset.sum_mul]
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))

/-- The assembly of the second moment on the register from the pointwise bound, the norms, and the
layer bounds. -/
lemma second_moment_assemble {m : ℕ} (P : RegParticles eta) (a F : EuclideanSpace ℂ (RCfg eta m))
    {g S0 Ξ₀ R : ℝ} (hg : 0 < g)
    (hpt : ∀ q, ‖(wMul (wM P) (wMul (wM P) a)) q‖ ≤
      ‖a q‖ + 2 / g ^ 2 * ‖F q‖ + 2 / g ^ 2 * ‖(wMul wTot F) q‖)
    (ha : ‖a‖ ≤ S0) (hF : ‖F‖ ≤ Ξ₀)
    (hlayer : ∀ r : Fin eta, ‖wMul (fun q => nsq (gl (q r))) F‖ ≤ R) :
    ‖wMul (wM P) (wMul (wM P) a)‖ ≤ S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * R) := by
  have hg2 : (0 : ℝ) ≤ 2 / g ^ 2 := by positivity
  have h4 := norm_le_add3_of_pointwise (X := wMul (wM P) (wMul (wM P) a)) (A := a)
    (B := ((2 / g ^ 2 : ℝ) : ℂ) • F) (C := ((2 / g ^ 2 : ℝ) : ℂ) • wMul wTot F) (fun q => by
      simp only [PiLp.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hg2]
      exact hpt q)
  rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hg2] at h4
  have hsum : ∑ r : Fin eta, ‖wMul (fun q => nsq (gl (q r))) F‖ ≤ eta * R := by
    calc ∑ r : Fin eta, ‖wMul (fun q => nsq (gl (q r))) F‖ ≤ ∑ _r : Fin eta, R :=
          sum_le_sum fun r _ => hlayer r
      _ = eta * R := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h5 := mul_le_mul_of_nonneg_left ((norm_wTot_le_layers F).trans (add_le_add hF hsum)) hg2
  have h6 := mul_le_mul_of_nonneg_left hF hg2
  have e : 4 / g ^ 2 * Ξ₀ = 2 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * Ξ₀ := by ring
  linarith

end Register

/-! ## The second moment of the projected trajectory -/

section Continuum

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

/-- The register weight against the kinetic symbol: `W² |c| ≤ |c| + (2/g²)(|T c| + wTot |T c|)`
at the lifted configurations. -/
lemma norm_wM_sq_regCoeff_le_pt {g : ℝ} (hg : 0 < g) (m : ℕ) (u : MolecularFourierH2 eta)
    (q : RCfg eta m) :
    ‖(wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys))
        (regCoeff m (molecularH2StateMap eta g u)))) q‖ ≤
      ‖(regCoeff m (molecularH2StateMap eta g u)) q‖ +
        2 / g ^ 2 * ‖(regCoeff m (coulombFourierKineticH2 sys g u)) q‖ +
        2 / g ^ 2 * ‖(wMul wTot (regCoeff m (coulombFourierKineticH2 sys g u))) q‖ := by
  set P := regParticlesOf sys
  set c : ℂ := molecularH2Coeff g u (liftCfg q)
  have hW0 : 0 ≤ wM P q := le_trans zero_le_one (wM_ge_one P q)
  have hkin : coulombKineticEnergySymbol sys g (liftCfg q) = g ^ 2 / 2 * (wM P q - 1) := by
    unfold coulombKineticEnergySymbol wM
    rw [add_sub_cancel_left, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun r _ => ?_
    simp only [liftCfg, nsq_eq_latticeNormSq]
    rw [show P.mass r = sys.mass r from rfl]
    ring
  have hk0 : 0 ≤ g ^ 2 / 2 * (wM P q - 1) := by
    have := wM_ge_one P q
    have := sq_nonneg g
    positivity
  have hT : (regCoeff m (coulombFourierKineticH2 sys g u)) q =
      ((g ^ 2 / 2 * (wM P q - 1) : ℝ) : ℂ) * c := by
    rw [regCoeff_apply, coulombFourierKineticH2_apply, hkin]
  have hS : (regCoeff m (molecularH2StateMap eta g u)) q = c := by
    rw [regCoeff_apply, molecularH2StateMap_apply]
  have hWT : wM P q ≤ wTot q := by
    unfold wM wTot
    have : ∀ a ∈ (univ : Finset (Fin eta)), nsq (gl (q a)) / P.mass a ≤ nsq (gl (q a)) :=
      fun a _ => div_le_self (nsq_nonneg _) (P.one_le_mass a)
    linarith [Finset.sum_le_sum this]
  rw [wMul_apply, wMul_apply, wMul_apply, hT, hS]
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hW0, Real.norm_of_nonneg hk0,
    Real.norm_of_nonneg (le_trans zero_le_one (wTot_ge_one q))]
  have hg2 : 0 < g ^ 2 := by positivity
  have e : wM P q * (wM P q * ‖c‖) = ‖c‖ + 2 / g ^ 2 * (g ^ 2 / 2 * (wM P q - 1) * ‖c‖) +
      2 / g ^ 2 * (wM P q * (g ^ 2 / 2 * (wM P q - 1) * ‖c‖)) := by
    field_simp
    ring
  rw [e]
  have hX : 0 ≤ g ^ 2 / 2 * (wM P q - 1) * ‖c‖ := mul_nonneg hk0 (norm_nonneg _)
  have h1 : wM P q * (g ^ 2 / 2 * (wM P q - 1) * ‖c‖) ≤
      wTot q * (g ^ 2 / 2 * (wM P q - 1) * ‖c‖) := mul_le_mul_of_nonneg_right hWT hX
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 / g ^ 2)
  linarith

include hKernel hL hPeriodic in
/-- **The second kinetic moment of the projected trajectory** (`lem:grid-data2`, `eq:data2`): for
`ψ(t) = S u`, `‖W² P ψ(t)‖ ≤ ‖ψ₀‖ + (4/g²) Ξ₀ + (2/g²) η √Q (4m+1)^{3/2}` uniformly in `t`, where
`Q = k₀⁴ Ξ₀² + 120 m̄² Ξ₁²/g⁴ + 30 C_tail(M₀)²/g` (`k₀ ≥ 2` with `g k₀ ≥ 1` the first threshold of
the layer cake at which the bootstrapped tails are used). -/
theorem second_moment_regCoeff_le (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (m : ℕ) (Blow Cs Bker : ℝ) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (t : ℝ) (u : MolecularFourierH2 eta)
    (hu1 : molecularH2StateMap eta (2 * Real.pi / L) u =
      U t (molecularH2StateMap eta (2 * Real.pi / L) u₀))
    (hu2 : H u = U t (H u₀)) (k₀ : ℕ) (hk₀ : 2 ≤ k₀) (hk₀g : 1 ≤ (2 * Real.pi / L) * k₀) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB sys L Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let C₀ : ℝ := finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M₀
    let Q : ℝ := (k₀ : ℝ) ^ 4 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 / g ^ 4 + 30 * C₀ ^ 2 / g
    ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys))
        (regCoeff m (molecularH2StateMap eta g u)))‖ ≤
      S0 + 4 / g ^ 2 * Ξ₀ +
        2 / g ^ 2 * (eta * (Real.sqrt Q * Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3)) := by
  intro g b S0 Ξ₀ Ξ₁ M₀ C₀ Q
  have hb : 0 ≤ b := relB_nonneg sys L Hunit hC
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
    have h := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u
    rw [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
    exact h
  have hhigh : ∀ r : Fin eta, ∀ k : ℕ, k₀ ≤ k →
      ‖maskOp (Shell r k) (regCoeff m (coulombFourierKineticH2 sys g u))‖ ≤
        (2 * sys.maxMass / (g * k) ^ 2) * Ξ₁ + C₀ * Real.sqrt (1 / (g * k)) := by
    intro r k hkk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (le_trans hk₀ hkk)
    have hgk1 : 1 ≤ g * k :=
      hk₀g.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hkk) hg.le)
    have hgk2 : 2 * g ≤ g * k := by
      rw [mul_comm 2 g]
      exact mul_le_mul_of_nonneg_left hk2 hg.le
    have hgkpos : 0 < g * k := by linarith
    have hρ : Real.sqrt (1 / (g * k)) ^ 2 * (g * k) = 1 := by
      rw [Real.sq_sqrt (div_nonneg zero_le_one hgkpos.le), div_mul_cancel₀ 1 hgkpos.ne']
    exact (norm_shell_regCoeff_le hg r k _).trans
      (tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph r (g * k)
        (Real.sqrt (1 / (g * k))) Blow Cs Bker hgk1 (Real.sqrt_nonneg _) hρ hBlow hCs hBker hgk2
        hAmplitude hBkerScale hCsScale u₀ v₀ huv t u hu1 hu2).1
  have hlow : ∀ r : Fin eta, ∀ k : ℕ,
      ‖maskOp (Shell r k) (regCoeff m (coulombFourierKineticH2 sys g u))‖ ≤ Ξ₀ := fun r k =>
    (norm_shell_regCoeff_le hg r k _).trans ((norm_tailMask_apply_le g (g * k) r _).trans hTu)
  exact second_moment_assemble (regParticlesOf sys) _ _ hg
    (norm_wM_sq_regCoeff_le_pt sys hg m u) ((norm_regCoeff_le _).trans hSu.le)
    ((norm_regCoeff_le _).trans hTu)
    (fun r => layer_bound r _ hg k₀ (by omega) (hlow r) (hhigh r))

end Continuum

end PlaneWaveGridDynamics

end DevGS2
-- END SOURCE dev/DevGS2.lean

-- BEGIN SOURCE dev/DevGS3.lean
-- SHA256 98f7105d089818600ed478e75a76573c87566e60e85cdae08ff3381bdec19bee
section DevGS3

/-!
# Grid dynamics: second moments of smeared states and of grid trajectories

Toward `thm:grid-dyn-sharp` (`lem:grid-obs2` and the second-moment budget of the backward flows),
with the second moment `X(u) = ‖W² u‖` of the mass-weighted weight `W = wM`:

* the collocated observable: `X(O_g u) ≤ 8 C_χ X(u) + 8 D⁽⁴⁾_χ ‖u‖` with
  `D⁽⁴⁾_χ = Σ_ν |ν|⁴ |χ̂(ν)|` (`norm_wM_sq_gridObs_le`); the centred representative is the
  shortest representative, so a cyclic translation by `ν` obeys `W q ≤ 2 W p + 2 |ν|²` with no wrap
  term (`wM_le_cyc`);
* grid trajectories: `X(V w) ≤ flow2(X(w), ‖W w‖, ‖w‖)` for every unitary `V` that commutes with
  `H_grid` (`norm_wM_sq_gridFlow_le`), from the second-order elliptic estimate at `V w` and the
  first-order trajectory bound applied to `H_grid w` (this is where the conservation
  `‖H_grid² V w‖ = ‖H_grid² w‖` enters, with the forward graph bound of `H_grid w`; no separate
  second-order forward bound is needed);
  the budget grows like `K^{3/2}` through `secondConst ≤ σ (4m+1)^{3/2}` (`secondConst_le`), and
  `flow2` is sub-homogeneous in that growth (`flow2_le_mul`);
* the double kinetic division `(T+1)⁴ t_r(T; u) ≤ m̄² X(u)` (`sq_sq_mul_norm_high_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace PlaneWaveGridDynamics

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics

/-! ## The centred representative is shorter than every lift -/

section Centred

variable {M : ℕ}

/-- `|gl x| ≤ |t|` componentwise for every integer lift `t` of `x`. -/
lemma abs_gl_le_of_cast (x : GMode (2 * M + 1)) (t : Lat3)
    (h : ∀ c, x c = ((t c : ℤ) : ZMod (2 * M + 1))) (c : Fin 3) : |gl x c| ≤ |t c| := by
  have he : ((gl x c : ℤ) : ZMod (2 * M + 1)) = ((t c : ℤ) : ZMod (2 * M + 1)) := by
    simp only [gl, ZMod.coe_valMinAbs]
    exact h c
  have h' := ZMod.natAbs_min_of_le_div_two (2 * M + 1) (gl x c) (t c) he
    (ZMod.natAbs_valMinAbs_le _)
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  exact_mod_cast h'

lemma nsq_gl_le_of_cast (x : GMode (2 * M + 1)) (t : Lat3)
    (h : ∀ c, x c = ((t c : ℤ) : ZMod (2 * M + 1))) : nsq (gl x) ≤ nsq t := by
  rw [nsq_eq_sum, nsq_eq_sum]
  refine sum_le_sum fun c _ => ?_
  have h1 := abs_gl_le_of_cast x t h c
  have h2 : |((gl x c : ℤ) : ℝ)| ≤ |((t c : ℤ) : ℝ)| := by exact_mod_cast h1
  rw [← sq_abs ((gl x c : ℤ) : ℝ), ← sq_abs ((t c : ℤ) : ℝ)]
  exact pow_le_pow_left₀ (abs_nonneg _) h2 2

end Centred

/-! ## The collocated observable -/

section Observable

variable {eta m : ℕ}

/-- The weight across a cyclic translation of register `a`, wraps included:
`W q ≤ 2 W p + 2 |ν|²` for `p = q + ν`. -/
lemma wM_le_cyc (P : RegParticles eta) (a : Fin eta) (ν : Lat3) (q : RCfg eta m) :
    wM P q ≤ 2 * wM P (cfgShift a (ofLat ν) q) + 2 * nsq ν := by
  have hma := P.one_le_mass a
  have hmpos := P.mass_pos a
  have hrest : ∑ b ∈ univ.erase a, nsq (gl (q b)) / P.mass b =
      ∑ b ∈ univ.erase a, nsq (gl (cfgShift a (ofLat ν) q b)) / P.mass b :=
    sum_congr rfl fun b hb => by rw [cfgShift_ne (ne_of_mem_erase hb)]
  have hR0 : 0 ≤ ∑ b ∈ univ.erase a, nsq (gl (cfgShift a (ofLat ν) q b)) / P.mass b :=
    sum_nonneg fun b _ => div_nonneg (nsq_nonneg _) (P.mass_pos b).le
  have hpa : 0 ≤ nsq (gl (cfgShift a (ofLat ν) q a)) / P.mass a :=
    div_nonneg (nsq_nonneg _) hmpos.le
  have hν := nsq_nonneg ν
  have h1 : nsq (gl (q a)) ≤ 2 * nsq (gl (cfgShift a (ofLat ν) q a)) + 2 * nsq ν := by
    have hcast : ∀ c, q a c =
        (((gl (cfgShift a (ofLat ν) q a) - ν) c : ℤ) : ZMod (2 * (2 * m) + 1)) := by
      intro c
      rw [cfgShift_self]
      simp only [Pi.sub_apply, Int.cast_sub, gl, ZMod.coe_valMinAbs, Pi.add_apply, ofLat]
      ring
    exact (nsq_gl_le_of_cast (q a) _ hcast).trans (nsq_sub_le _ _)
  have h2 : nsq (gl (q a)) / P.mass a ≤
      2 * (nsq (gl (cfgShift a (ofLat ν) q a)) / P.mass a) + 2 * nsq ν := by
    have h3 : nsq (gl (q a)) / P.mass a ≤
        (2 * nsq (gl (cfgShift a (ofLat ν) q a)) + 2 * nsq ν) / P.mass a :=
      div_le_div_of_nonneg_right h1 hmpos.le
    have h4 : 2 * nsq ν / P.mass a ≤ 2 * nsq ν := div_le_self (by linarith) hma
    have e : (2 * nsq (gl (cfgShift a (ofLat ν) q a)) + 2 * nsq ν) / P.mass a =
        2 * (nsq (gl (cfgShift a (ofLat ν) q a)) / P.mass a) + 2 * nsq ν / P.mass a := by ring
    linarith
  rw [wM_split P a q, wM_split P a (cfgShift a (ofLat ν) q), hrest]
  linarith

/-- One translation, second moment: `X(S_ν u) ≤ 8 X(u) + 8 |ν|⁴ ‖u‖`. -/
lemma norm_wM_sq_cycCLM_le (P : RegParticles eta) (a : Fin eta) (ν : Lat3)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM P) (wMul (wM P) (cycCLM a ν u))‖ ≤
      8 * ‖wMul (wM P) (wMul (wM P) u)‖ + 8 * nsq ν ^ 2 * ‖u‖ := by
  have hpt : ∀ q, ‖(wMul (wM P) (wMul (wM P) (cycCLM a ν u))) q‖ ≤
      8 * ‖(cycCLM a ν (wMul (wM P) (wMul (wM P) u))) q‖ +
        8 * nsq ν ^ 2 * ‖(cycCLM a ν u) q‖ := by
    intro q
    have hw := wM_le_cyc P a ν q
    have hW0 : 0 ≤ wM P q := le_trans zero_le_one (wM_ge_one P q)
    have hWp : 0 ≤ wM P (cfgShift a (ofLat ν) q) := le_trans zero_le_one (wM_ge_one P _)
    simp only [wMul_apply, cycCLM_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hW0,
      Real.norm_of_nonneg hWp]
    have hsq : wM P q ^ 2 ≤ 8 * wM P (cfgShift a (ofLat ν) q) ^ 2 + 8 * nsq ν ^ 2 := by
      calc wM P q ^ 2 ≤ (2 * wM P (cfgShift a (ofLat ν) q) + 2 * nsq ν) ^ 2 :=
            pow_le_pow_left₀ hW0 hw 2
        _ ≤ 8 * wM P (cfgShift a (ofLat ν) q) ^ 2 + 8 * nsq ν ^ 2 := by
            nlinarith [sq_nonneg (wM P (cfgShift a (ofLat ν) q) - nsq ν)]
    have hx := norm_nonneg (u (cfgShift a (ofLat ν) q))
    have e1 : wM P q * (wM P q * ‖u (cfgShift a (ofLat ν) q)‖) =
        wM P q ^ 2 * ‖u (cfgShift a (ofLat ν) q)‖ := by ring
    have e2 : 8 * (wM P (cfgShift a (ofLat ν) q) * (wM P (cfgShift a (ofLat ν) q) *
        ‖u (cfgShift a (ofLat ν) q)‖)) + 8 * nsq ν ^ 2 * ‖u (cfgShift a (ofLat ν) q)‖ =
        (8 * wM P (cfgShift a (ofLat ν) q) ^ 2 + 8 * nsq ν ^ 2) *
          ‖u (cfgShift a (ofLat ν) q)‖ := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hsq hx
  refine (norm_le_add2_of_pointwise (by norm_num) (by positivity) hpt).trans (le_of_eq ?_)
  rw [norm_cycCLM_apply, norm_cycCLM_apply]

/-- The fourth coefficient moment `D⁽⁴⁾_χ = Σ_ν |ν|⁴ |χ̂(ν)|` (in lattice units; the Fourier
counterpart of the manuscript's `D_χ^{(4)}`). -/
noncomputable def momFour (c : Lat3 → ℂ) : ℝ := ∑' ν, nsq ν ^ 2 * ‖c ν‖

lemma momFour_nonneg (c : Lat3 → ℂ) : 0 ≤ momFour c :=
  tsum_nonneg fun _ => mul_nonneg (sq_nonneg _) (norm_nonneg _)

/-- **The collocated observable: second moment** (`lem:grid-obs2`):
`X(O_g u) ≤ 8 C_χ X(u) + 8 D⁽⁴⁾_χ ‖u‖`. -/
theorem norm_wM_sq_gridObs_le (P : RegParticles eta) (a : Fin eta) {c : Lat3 → ℂ}
    (hc : Summable fun ν => ‖c ν‖) (hc4 : Summable fun ν => nsq ν ^ 2 * ‖c ν‖)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM P) (wMul (wM P) (gridObs a c u))‖ ≤
      8 * (∑' ν, ‖c ν‖) * ‖wMul (wM P) (wMul (wM P) u)‖ + 8 * momFour c * ‖u‖ := by
  set W := LinearMap.toContinuousLinearMap ((wMul (wM P)).comp (wMul (wM P)) :
    EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m))
  have hS : HasSum (fun ν => c ν • W (cycCLM a ν u)) (W (gridObs a c u)) := by
    have h := ((hasSum_gridObs (m := m) a hc).mapL (ContinuousLinearMap.apply ℂ _ u)).mapL W
    simpa only [ContinuousLinearMap.apply_apply, smul_apply, map_smul] using h
  set X := ‖wMul (wM P) (wMul (wM P) u)‖
  have hg : HasSum (fun ν => ‖c ν‖ * (8 * X) + 8 * (nsq ν ^ 2 * ‖c ν‖) * ‖u‖)
      ((∑' ν, ‖c ν‖) * (8 * X) + 8 * momFour c * ‖u‖) := by
    have h1 := hc.hasSum.mul_right (8 * X)
    have h2 := (hc4.hasSum.mul_left 8).mul_right ‖u‖
    exact h1.add h2
  have hbound := hS.norm_le_of_bounded hg fun ν => by
    rw [norm_smul]
    have h1 : ‖W (cycCLM a ν u)‖ ≤ 8 * X + 8 * nsq ν ^ 2 * ‖u‖ := norm_wM_sq_cycCLM_le P a ν u
    calc ‖c ν‖ * ‖W (cycCLM a ν u)‖ ≤ ‖c ν‖ * (8 * X + 8 * nsq ν ^ 2 * ‖u‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖c ν‖ * (8 * X) + 8 * (nsq ν ^ 2 * ‖c ν‖) * ‖u‖ := by ring
  show ‖W (gridObs a c u)‖ ≤ _
  have e : (∑' ν, ‖c ν‖) * (8 * X) = 8 * (∑' ν, ‖c ν‖) * X := by ring
  linarith

end Observable

/-! ## The double kinetic division -/

section Shell

variable {eta m : ℕ}

lemma maskOp_wMul_comm {ι : Type*} [Fintype ι] (Pr : ι → Prop) (w : ι → ℝ)
    (u : EuclideanSpace ℂ ι) : maskOp Pr (wMul w u) = wMul w (maskOp Pr u) := by
  ext q
  by_cases h : Pr q
  · rw [maskOp_apply_of _ _ h, wMul_apply, wMul_apply, maskOp_apply_of _ _ h]
  · rw [maskOp_apply_of_not _ _ h, wMul_apply, maskOp_apply_of_not _ _ h, mul_zero]

/-- **The double kinetic division:** `(T+1)⁴ t_r(T; u) ≤ m̄² X(u)`. -/
lemma sq_sq_mul_norm_high_le (P : RegParticles eta) (T : ℕ) (r : Fin eta)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ((T : ℝ) + 1) ^ 4 * ‖maskOp (High T r) u‖ ≤
      P.maxMass ^ 2 * ‖wMul (wM P) (wMul (wM P) u)‖ := by
  have hM := P.maxMass_pos
  have h1 := sq_mul_norm_high_le_gen P T r (maskOp (High T r) u)
  rw [maskOp_maskOp] at h1
  have h2 := sq_mul_norm_high_le_gen P T r (wMul (wM P) u)
  rw [maskOp_wMul_comm] at h2
  have hT : (0 : ℝ) ≤ ((T : ℝ) + 1) ^ 2 := by positivity
  calc ((T : ℝ) + 1) ^ 4 * ‖maskOp (High T r) u‖
      = ((T : ℝ) + 1) ^ 2 * (((T : ℝ) + 1) ^ 2 * ‖maskOp (High T r) u‖) := by ring
    _ ≤ ((T : ℝ) + 1) ^ 2 * (P.maxMass * ‖wMul (wM P) (maskOp (High T r) u)‖) :=
        mul_le_mul_of_nonneg_left h1 hT
    _ = P.maxMass * (((T : ℝ) + 1) ^ 2 * ‖wMul (wM P) (maskOp (High T r) u)‖) := by ring
    _ ≤ P.maxMass * (P.maxMass * ‖wMul (wM P) (wMul (wM P) u)‖) :=
        mul_le_mul_of_nonneg_left h2 hM.le
    _ = P.maxMass ^ 2 * ‖wMul (wM P) (wMul (wM P) u)‖ := by ring

end Shell

/-! ## Second moments of grid trajectories -/

section Budget

/-- The second-moment budget of a grid trajectory: with `X(w) ≤ X`, `‖W w‖ ≤ Y`, `‖w‖ ≤ S`, the
constant `c_J` of the first-order trajectory bound, `c_H = 26 Z J₀` of the forward graph bound and
`s_c = secondConst`, `X(V w) ≤ flow2 g c_J c_H s_c X Y S` (`norm_wM_sq_gridFlow_le`). -/
noncomputable def flow2 (g cJ cH sc X Y S : ℝ) : ℝ :=
  (2 + 4 / g ^ 2 * sc) * (5 / 3 * Y + cJ * S) + 5 * X + 20 / (3 * g ^ 2) * sc * Y +
    4 / g ^ 2 * cJ * (5 * g ^ 2 / 8 * Y + cH * S)

lemma flow2_nonneg {g cJ cH sc X Y S : ℝ} (hcJ : 0 ≤ cJ) (hcH : 0 ≤ cH) (hsc : 0 ≤ sc)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hS : 0 ≤ S) : 0 ≤ flow2 g cJ cH sc X Y S := by
  unfold flow2
  positivity

/-- The assembly of `flow2` from the five ingredient bounds. -/
lemma flow2_of_bounds {g cJ cH sc X Y S XV WV WHV WH HW : ℝ} (hg : 0 < g) (hsc : 0 ≤ sc)
    (hcJ : 0 ≤ cJ) (h1 : XV ≤ 2 * WV + 4 / g ^ 2 * WHV + 4 / g ^ 2 * sc * WV)
    (h2 : WV ≤ 5 / 3 * Y + cJ * S) (h4 : WHV ≤ 5 / 3 * WH + cJ * HW)
    (h5 : WH ≤ 3 * g ^ 2 / 4 * X + sc * Y) (h8 : HW ≤ 5 * g ^ 2 / 8 * Y + cH * S) :
    XV ≤ flow2 g cJ cH sc X Y S := by
  have hg2 : (0 : ℝ) < g ^ 2 := by positivity
  have hg4 : (0 : ℝ) ≤ 4 / g ^ 2 := by positivity
  have h9 : WHV ≤ 5 / 3 * (3 * g ^ 2 / 4 * X + sc * Y) + cJ * (5 * g ^ 2 / 8 * Y + cH * S) :=
    h4.trans (add_le_add (mul_le_mul_of_nonneg_left h5 (by norm_num))
      (mul_le_mul_of_nonneg_left h8 hcJ))
  have h10 := mul_le_mul_of_nonneg_left h9 hg4
  have h11 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 + 4 / g ^ 2 * sc)
  have e1 : 4 / g ^ 2 * (5 / 3 * (3 * g ^ 2 / 4 * X + sc * Y) + cJ * (5 * g ^ 2 / 8 * Y + cH * S)) =
      5 * X + 20 / (3 * g ^ 2) * sc * Y + 4 / g ^ 2 * cJ * (5 * g ^ 2 / 8 * Y + cH * S) := by
    field_simp
    ring
  have e2 : 2 * WV + 4 / g ^ 2 * sc * WV = (2 + 4 / g ^ 2 * sc) * WV := by ring
  unfold flow2
  linarith

lemma flow2_mono {g cJ cH sc X Y S X' Y' S' : ℝ} (hcJ : 0 ≤ cJ) (hcH : 0 ≤ cH) (hsc : 0 ≤ sc)
    (hX : X ≤ X') (hY : Y ≤ Y') (hS : S ≤ S') :
    flow2 g cJ cH sc X Y S ≤ flow2 g cJ cH sc X' Y' S' := by
  unfold flow2
  have h1 : 5 / 3 * Y + cJ * S ≤ 5 / 3 * Y' + cJ * S' := by
    have := mul_le_mul_of_nonneg_left hS hcJ
    linarith
  have h2 : 5 * g ^ 2 / 8 * Y + cH * S ≤ 5 * g ^ 2 / 8 * Y' + cH * S' := by
    have := mul_le_mul_of_nonneg_left hS hcH
    have := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 5 * g ^ 2 / 8)
    linarith
  have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 + 4 / g ^ 2 * sc)
  have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 / g ^ 2 * cJ)
  have h5 := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 20 / (3 * g ^ 2) * sc)
  linarith

/-- `flow2` is sub-homogeneous in the growth: if `s_c ≤ σ r` and `X ≤ x r` with `r ≥ 1`, then
`flow2(s_c; X) ≤ r flow2(σ; x)`. -/
lemma flow2_le_mul {g cJ cH sc σ X x Y S r : ℝ} (hcJ : 0 ≤ cJ) (hcH : 0 ≤ cH) (hY : 0 ≤ Y)
    (hS : 0 ≤ S) (hr : 1 ≤ r) (hscσ : sc ≤ σ * r) (hXx : X ≤ x * r) :
    flow2 g cJ cH sc X Y S ≤ r * flow2 g cJ cH σ x Y S := by
  unfold flow2
  have hr0 : 0 ≤ r := by linarith
  have hA : 0 ≤ 5 / 3 * Y + cJ * S := by positivity
  have hB : 0 ≤ 4 / g ^ 2 * cJ * (5 * g ^ 2 / 8 * Y + cH * S) := by positivity
  have hg4 : (0 : ℝ) ≤ 4 / g ^ 2 := by positivity
  have hg20 : (0 : ℝ) ≤ 20 / (3 * g ^ 2) := by positivity
  have h1 : 2 + 4 / g ^ 2 * sc ≤ r * (2 + 4 / g ^ 2 * σ) := by
    have h := mul_le_mul_of_nonneg_left hscσ hg4
    have e : r * (2 + 4 / g ^ 2 * σ) = 2 * r + 4 / g ^ 2 * (σ * r) := by ring
    rw [e]
    linarith
  have h1' := mul_le_mul_of_nonneg_right h1 hA
  have h2 : 20 / (3 * g ^ 2) * sc * Y ≤ r * (20 / (3 * g ^ 2) * σ * Y) := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscσ hg20) hY
    have e : r * (20 / (3 * g ^ 2) * σ * Y) = 20 / (3 * g ^ 2) * (σ * r) * Y := by ring
    rw [e]
    exact h
  have h3 : 4 / g ^ 2 * cJ * (5 * g ^ 2 / 8 * Y + cH * S) ≤
      r * (4 / g ^ 2 * cJ * (5 * g ^ 2 / 8 * Y + cH * S)) := le_mul_of_one_le_left hB hr
  have h4 : 5 * X ≤ r * (5 * x) := by
    have e : r * (5 * x) = 5 * (x * r) := by ring
    rw [e]
    linarith
  have e : r * ((2 + 4 / g ^ 2 * σ) * (5 / 3 * Y + cJ * S) + 5 * x +
      20 / (3 * g ^ 2) * σ * Y + 4 / g ^ 2 * cJ * (5 * g ^ 2 / 8 * Y + cH * S)) =
      r * (2 + 4 / g ^ 2 * σ) * (5 / 3 * Y + cJ * S) + r * (5 * x) +
        r * (20 / (3 * g ^ 2) * σ * Y) + r * (4 / g ^ 2 * cJ * (5 * g ^ 2 / 8 * Y + cH * S)) := by
    ring
  rw [e]
  linarith

lemma sqrt_pow_three {y : ℝ} (hy : 0 ≤ y) : Real.sqrt (y ^ 3) = Real.sqrt y ^ 3 := by
  have e : y ^ 3 = (Real.sqrt y ^ 3) ^ 2 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt hy]
  rw [e, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) 3)]

lemma one_le_sqrt_pow_three (m : ℕ) : 1 ≤ Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 := by
  have h0 : (1 : ℝ) ≤ ((4 * m : ℕ) : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (4 * m)
    linarith
  have h1 : 1 ≤ Real.sqrt (((4 * m : ℕ) : ℝ) + 1) :=
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (((4 * m : ℕ) : ℝ) + 1) := Real.sqrt_le_sqrt h0
  exact one_le_pow₀ h1

variable {ν : Type*} [Fintype ν] {eta : ℕ}

/-- `secondConst ≤ σ (4m+1)^{3/2}` with `σ = Z_c (52 J₀ + 4 √53 m̄)`, independent of `m`. -/
lemma secondConst_le (P : RegParticles eta) (D : NucData ν) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (g : ℝ) (m : ℕ) :
    secondConst P D gamma g m ≤
      Zc P D gamma * (52 * (J0g (P.maxMass * Zc P D gamma) g : ℝ) +
        4 * Real.sqrt 53 * P.maxMass) * Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 := by
  have hZ := Zc_nonneg (P := P) (D := D) hgamma
  have hM := P.maxMass_pos
  have hr := one_le_sqrt_pow_three m
  have e1 : (2 * ((2 * m : ℕ) : ℝ) + 1) = ((4 * m : ℕ) : ℝ) + 1 := by push_cast; ring
  have e2 : Real.sqrt (53 * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) =
      Real.sqrt 53 * Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 := by
    rw [e1, Real.sqrt_mul (by norm_num), sqrt_pow_three (by positivity)]
  unfold secondConst
  rw [e2]
  have hJ : (0 : ℝ) ≤ 52 * (J0g (P.maxMass * Zc P D gamma) g : ℝ) := by positivity
  have h1 : 52 * (J0g (P.maxMass * Zc P D gamma) g : ℝ) ≤
      52 * (J0g (P.maxMass * Zc P D gamma) g : ℝ) * Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 :=
    le_mul_of_one_le_right hJ hr
  have e3 : Zc P D gamma * (52 * (J0g (P.maxMass * Zc P D gamma) g : ℝ) +
      4 * Real.sqrt 53 * P.maxMass) * Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 =
      Zc P D gamma * (52 * (J0g (P.maxMass * Zc P D gamma) g : ℝ) *
        Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 +
        4 * (Real.sqrt 53 * Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3) * P.maxMass) := by ring
  rw [e3]
  refine mul_le_mul_of_nonneg_left ?_ hZ
  linarith

end Budget

section Flow

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **Second moment of a grid trajectory** (`lem:grid-data2` for `ψ_g(t)`, and the backward flows
in the proof of `thm:grid-dyn-sharp`): for a unitary `V` that commutes with the grid Hamiltonian,
`X(V w) ≤ flow2(X(w), ‖W w‖, ‖w‖)`; the bound does not depend on `V`, so it is uniform in time. -/
theorem norm_wM_sq_gridFlow_le (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {m : ℕ}
    {κ : Lat3 → ℝ} (hκb : ∀ x, |κ x| ≤ coulombCellAmplitude L * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0)
    (V : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hcomm : ∀ x, V (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (V x))
    (w : EuclideanSpace ℂ (RCfg eta m)) {X Y S : ℝ}
    (hX : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) w)‖ ≤ X)
    (hY : ‖wMul (wM (regParticlesOf sys)) w‖ ≤ Y) (hS : ‖w‖ ≤ S) :
    ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) (V w))‖ ≤
      flow2 (2 * Real.pi / L) (gridFlowConst sys L)
        (26 * coulombGridCoupling sys L * (J0g (coulombGridCoupling sys L) (2 * Real.pi / L) : ℝ))
        (secondConst (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
          (coulombCellAmplitude L) (2 * Real.pi / L) m) X Y S := by
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hsc : 0 ≤ secondConst (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) (2 * Real.pi / L) m := secondConst_nonneg _ _ hγ
  have hcJ := gridFlowConst_nonneg sys hL
  have hcH : 0 ≤ 26 * coulombGridCoupling sys L *
      (J0g (coulombGridCoupling sys L) (2 * Real.pi / L) : ℝ) := by
    have := coulombGridCoupling_nonneg sys L hL
    positivity
  have h1 := second_elliptic (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData hγ hκb hsupp
    hg (V w)
  have h2 : ‖wMul (wM (regParticlesOf sys)) (V w)‖ ≤ 5 / 3 * Y + gridFlowConst sys L * S := by
    have h := norm_wM_gridFlow_le sys hL hκb V hcomm w
    have h3 := mul_le_mul_of_nonneg_left hY (by norm_num : (0 : ℝ) ≤ 5 / 3)
    have h4 := mul_le_mul_of_nonneg_left hS hcJ
    linarith
  have h4 : ‖wMul (wM (regParticlesOf sys)) (Hgrid eta m (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) (V w))‖ ≤
      5 / 3 * ‖wMul (wM (regParticlesOf sys)) (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) w)‖ +
      gridFlowConst sys L * ‖Hgrid eta m (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) w‖ := by
    rw [← hcomm]
    exact norm_wM_gridFlow_le sys hL hκb V hcomm _
  have h5 : ‖wMul (wM (regParticlesOf sys)) (Hgrid eta m (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) w)‖ ≤
      3 * (2 * Real.pi / L) ^ 2 / 4 * X + secondConst (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) (2 * Real.pi / L) m * Y := by
    have h := norm_wM_Hgrid_le (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData hγ hκb
      hsupp hg w
    have h6 := mul_le_mul_of_nonneg_left hX
        (by positivity : (0 : ℝ) ≤ 3 * (2 * Real.pi / L) ^ 2 / 4)
    have h7 := mul_le_mul_of_nonneg_left hY hsc
    linarith
  have h8 : ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) w‖ ≤ 5 * (2 * Real.pi / L) ^ 2 / 8 * Y +
        26 * coulombGridCoupling sys L *
          (J0g (coulombGridCoupling sys L) (2 * Real.pi / L) : ℝ) * S := by
    have h := (gridRegHam (eta := eta) (m := m) (P := regParticlesOf sys)
      (D := (posNucleiOf sys.nuclei).toNucData) hγ hκb hg).op_le w
    have h6 := mul_le_mul_of_nonneg_left hY
        (by positivity : (0 : ℝ) ≤ 5 * (2 * Real.pi / L) ^ 2 / 8)
    have h7 := mul_le_mul_of_nonneg_left hS hcH
    exact h.trans (add_le_add h6 h7)
  exact flow2_of_bounds hg hsc hcJ h1 h2 h4 h5 h8

end Flow

end PlaneWaveGridDynamics

end DevGS3
-- END SOURCE dev/DevGS3.lean

-- BEGIN SOURCE dev/DevGS4.lean
-- SHA256 5475002cc2d281fd3b6a6bb50ab6ab48933eedd84605c9eca0fa289e03301b99
section DevGS4

/-!
# Grid dynamics: the observable error of `thm:grid-dyn-sharp`

Only the source pairings of `prop:grid-dyn` improve (`thm:grid-dyn-sharp`): the duality of
`grid_duality` is run with the shell `τ_φ` of the backward flows as a parameter
(`grid_duality_shell`), and the second moments supply the double kinetic division
`τ_φ = m̄² r Φ/(⌊m/4⌋+1)⁴` (`sq_sq_mul_norm_high_le`), where `r Φ`, `r = (4m+1)^{3/2}`, bounds the
second moments of the backward flows of the smeared states uniformly in time:

* `X(P ψ(t)) ≤ ξ r` (`second_moment_regCoeff_le`, `lem:grid-data2`), also at `t = 0`;
* `X(ψ_g(t)) ≤ r F`, `F = flow2(σ; ξ, X_a, ‖ψ₀‖)` (`norm_wM_sq_gridFlow_le`, `flow2_le_mul`);
* `X(O_g v) ≤ r o`, `o = 8 C_χ F + 8 D⁽⁴⁾_χ ‖ψ₀‖`, for `v ∈ {P ψ(t), ψ_g(t)}` (`lem:grid-obs2`);
* `X(U_g(τ) O_g v) ≤ r Φ`, `Φ = flow2(σ; o, W_o, C_χ ‖ψ₀‖)` (`shell_gridFlow_gridObs_le`).

The constants `ξ, F, o, Φ` do not depend on `m`, so `τ_φ = O(K^{-5/2})`, and every source pairs at
the energy rate `K^{-3}` (`grid_observable_error_sharp`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset Set

namespace PlaneWaveGridDynamics

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics

lemma le_flow2 {g cJ cH sc X Y S : ℝ} (hcJ : 0 ≤ cJ) (hcH : 0 ≤ cH) (hsc : 0 ≤ sc)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hS : 0 ≤ S) : X ≤ flow2 g cJ cH sc X Y S := by
  unfold flow2
  have h1 : 0 ≤ (2 + 4 / g ^ 2 * sc) * (5 / 3 * Y + cJ * S) := by positivity
  have h2 : 0 ≤ 20 / (3 * g ^ 2) * sc * Y := by positivity
  have h3 : 0 ≤ 4 / g ^ 2 * cJ * (5 * g ^ 2 / 8 * Y + cH * S) := by positivity
  linarith

/-! ## The shells of the backward flows of the smeared states -/

section Shells

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **The shells of the backward flows** (`thm:grid-dyn-sharp`): if `X(v) ≤ r F`, `‖W v‖ ≤ X_b` and
`‖v‖ ≤ S₀`, then for every time `τ` and register `r'`,
`(⌊m/4⌋+1)⁴ ‖1_{|q_{r'}|∞ > ⌊m/4⌋} U_g(τ) O_g v‖ ≤ m̄² r Φ` with
`Φ = flow2(σ; 8 C_χ F + 8 D⁽⁴⁾_χ S₀, (2 + 12 m̄) C_χ X_b + 14 D'_χ S₀, C_χ S₀)`, whenever
`secondConst ≤ σ r` and `r ≥ 1`. -/
theorem shell_gridFlow_gridObs_le (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {m : ℕ}
    {κ : Lat3 → ℝ} (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
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
      (coulombCellAmplitude L) (2 * Real.pi / L) m ≤ σ * r) (τ : ℝ) (r' : Fin eta) :
    (((m / 4 : ℕ) : ℝ) + 1) ^ 4 * ‖maskOp (High (m / 4) r') (V τ (gridObs a χ v))‖ ≤
      sys.maxMass ^ 2 * (r * flow2 (2 * Real.pi / L) (gridFlowConst sys L)
        (26 * coulombGridCoupling sys L * (J0g (coulombGridCoupling sys L) (2 * Real.pi / L) : ℝ))
        σ (8 * (∑' ν, ‖χ ν‖) * F + 8 * momFour χ * S0)
        ((2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * Xb + 14 * momTwo χ * S0)
        ((∑' ν, ‖χ ν‖) * S0)) := by
  have hM := sys.one_le_maxMass
  have hCχ : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hD2 : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hD4 := momFour_nonneg χ
  have hcJ := gridFlowConst_nonneg sys hL
  have hcH : 0 ≤ 26 * coulombGridCoupling sys L *
      (J0g (coulombGridCoupling sys L) (2 * Real.pi / L) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (coulombGridCoupling_nonneg sys L hL)) (Nat.cast_nonneg _)
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
  have hflow := norm_wM_sq_gridFlow_le sys hL hκ.bound hκ.support (V τ) (hcomm τ) _ hXo hWo hSo
  have hWo0 : 0 ≤ (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * Xb + 14 * momTwo χ * S0 :=
    add_nonneg (mul_nonneg (mul_nonneg (by linarith) hCχ) hXb) (mul_nonneg (by positivity) hS0)
  have hhom := flow2_le_mul (g := 2 * Real.pi / L)
    (x := 8 * (∑' ν, ‖χ ν‖) * F + 8 * momFour χ * S0) hcJ hcH hWo0 (mul_nonneg hCχ hS0) hr hsc
    le_rfl
  have hsh := sq_sq_mul_norm_high_le (regParticlesOf sys) (m / 4) r' (V τ (gridObs a χ v))
  exact hsh.trans (mul_le_mul_of_nonneg_left (hflow.trans hhom) (sq_nonneg _))

end Shells

/-! ## The sharp observable error -/

section Grid

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **Duality on the grid, with the flow shell as a parameter** (`thm:grid-dyn-sharp`): the
statement of `grid_duality` for every bound `τ_φ` of the shells `‖1_{|q_r|∞ > ⌊m/4⌋} U_g(τ) w‖`
of the flow, instead of the a priori shell `m̄ W_φ/(⌊m/4⌋+1)²`: `|⟪a(t) - ψ_g(t), w⟫|` is at most
`t` times `(η t₂)(η C_tail(M_l) ρ₂) + Z_c (A(s₀, m)(t₄ m̄ W_φ + τ_φ X_a) + 52 m τ_φ t₄)`. -/
theorem grid_duality_shell (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ} (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (rho₂ rho₄ Blow Cs Bker : ℝ) (hK₄ : 1 ≤ (2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ))
    (hRho₂ : 0 ≤ rho₂) (hRhoScale₂ : rho₂ ^ 2 * ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) = 1)
    (hRho₄ : 0 ≤ rho₄) (hRhoScale₄ : rho₄ ^ 2 * ((2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ)) = 1)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (w : EuclideanSpace ℂ (RCfg eta m)) (Wφ τφ : ℝ)
    (hW : ∀ τ, ‖wMul (wM (regParticlesOf sys)) (Ug τ w)‖ ≤ Wφ) (hτφ0 : 0 ≤ τφ)
    (hτ : ∀ τ r, ‖maskOp (High (m / 4) r) (Ug τ w)‖ ≤ τφ) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB sys L Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
    let tl : ℝ → ℝ → ℝ := fun K ρ =>
      (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    let s₀ : ℕ := m / 4
    let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (coulombCellAmplitude L)
    let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
    let t₂ : ℝ := tl (g * ((2 * m : ℕ) : ℝ)) rho₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) rho₄
    ‖⟪regCoeff m (U t (molecularH2StateMap eta g u₀)) -
        Ug t (regCoeff m (molecularH2StateMap eta g u₀)), w⟫_ℂ‖ ≤
      ((eta * t₂) * (eta * (Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂)) +
        Zg * (formA s₀ m * (t₄ * (sys.maxMass * Wφ) + τφ * Xa) + 52 * m * (τφ * t₄))) * t := by
  intro g b S0 Ξ₀ Ξ₁ M₀ Ct tl s₀ Zg Xa t₂ t₄
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ b := relB_nonneg sys L Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
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
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM₀
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
          Delta eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            (coulombCellAmplitude L) κ (regCoeff m (U s (molecularH2StateMap eta g u₀))))))) s := by
    intro s
    have h1 := ((regCoeff (eta := eta) m).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
      (hderiv s u₀)
    refine h1.congr_deriv ?_
    rw [ContinuousLinearMap.coe_restrictScalars', map_neg, map_smul, ← hu2 s,
      regCoeff_H_eq_grid sys L H hKernel hL m κ (u s), hu1 s]
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
    have hT := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC (u s)
    rw [hu1 s, LinearIsometryEquiv.norm_map] at h
    rw [hu1 s, hu2 s, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hT
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    show ‖molecularH2StateMap eta g u₀‖ + 2 * ‖coulombFourierKineticH2 sys g (u s)‖ ≤ S0 + 2 * Ξ₀
    linarith
  -- (i) the Galerkin source against the lift of the flow
  have hi : ‖⟪regCoeff m (coulombFourierPotentialH2 sys g H
      (u s - molecularH2Truncate (2 * m) (u s))),
      φ⟫_ℂ‖ ≤ (eta * t₂) * (eta * (Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂)) := by
    refine (norm_inner_galSource_le sys L H hKernel m (u s) φ).trans ?_
    have hδ : ‖molecularH2StateMap eta g (u s) -
        molecularH2Truncate (2 * m) (molecularH2StateMap eta g (u s))‖ ≤ eta * t₂ := by
      refine (norm_sub_truncate_le hg (2 * m) _).trans ?_
      have htl := fun c => (tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph c
        (g * ((2 * m : ℕ) : ℝ)) rho₂ Blow Cs Bker hK₂ hRho₂ hRhoScale₂ hBlow hCs hBker hK₂2g
        hAmplitude hBkerScale hCsScale u₀ v₀ huv s (u s) (hu1 s) (hu2 s)).2
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
            sum_le_sum fun c _ => potential_tail_le sys L H hKernel Hunit hL hPeriodic c _ rho₂
              Blow Cs Bker _ hK₂ hRho₂ hRhoScale₂ hBlow hCs hBker hMl hK₂2g hAmplitude hBkerScale
              hCsScale _ hl
        _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hΛ0 : 0 ≤ eta * (Ct ((1 + g ^ 2) * (sys.maxMass * Wφ)) * rho₂) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
        (finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hMl) hRho₂)
    exact mul_le_mul hδ hΛ (norm_nonneg _) (by positivity)
  -- (ii) the grid difference against the flow
  have hii : ‖⟪Delta eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) κ (regCoeff m (U s (molecularH2StateMap eta g u₀))), φ⟫_ℂ‖ ≤
      Zg * (formA s₀ m * (t₄ * (sys.maxMass * Wφ) + τφ * Xa) + 52 * m * (τφ * t₄)) := by
    rw [← inner_conj_symm, RCLike.norm_conj]
    have hτu : ∀ r, ‖maskOp (High s₀ r) (regCoeff m
        (U s (molecularH2StateMap eta g u₀)))‖ ≤ t₄ := by
      intro r
      rw [← hu1 s]
      exact (norm_high_regCoeff_le hg s₀ r _).trans (tails_at_time sys L H hKernel Hunit hL
        hPeriodic hC U hgraph r (g * (s₀ : ℝ)) rho₄ Blow Cs Bker hK₄' hRho₄ hRhoScale₄ hBlow hCs
        hBker hK₄2g hAmplitude hBkerScale hCsScale u₀ v₀ huv s (u s) (hu1 s) (hu2 s)).2
    have hτv : ∀ r, ‖maskOp (High s₀ r) φ‖ ≤ τφ := fun r => hτ (s - t) r
    have hD := Delta_form (P := regParticlesOf sys) (D := (posNucleiOf sys.nuclei).toNucData) hγ
      (by omega : 1 ≤ s₀) hs₀m hκ.gridKernel (regCoeff m (U s (molecularH2StateMap eta g u₀))) φ
      ht₄0 hτφ0 hτu hτv
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

include hKernel hL hPeriodic in
-- the whole proof of `grid_observable_error` plus the second-moment budget: twice the default
set_option maxHeartbeats 400000 in
/-- **Observable error on the grid, sharp** (`thm:grid-dyn-sharp`, Fourier side, explicit form).
The setting of `grid_observable_error`, with in addition `D⁽⁴⁾_χ = Σ |ν|⁴ |χ̂(ν)| < ∞` and a first
layer-cake threshold `k₀ ≥ 2` with `g k₀ ≥ 1`: `|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫|` is at
most `2 δ (C_χ t₁ + τ_χ ‖ψ₀‖ + ‖O‖ δ) + ‖O‖ δ²` (term (I)) `+ C_χ t₁² + τ_χ^∞(m) ‖ψ₀‖²` (term (II))
`+ 2 t B_d` (term (III)), where `B_d` is the bound of `grid_duality_shell` at the shell
`τ_φ = m̄² r Φ/(⌊m/4⌋+1)⁴` given by the double kinetic division of the second moments
`X(U_g(τ) O_g v) ≤ r Φ` of the backward flows, `r = (4m+1)^{3/2}`: here
`ξ = ‖ψ₀‖ + (4/g²) Ξ₀ + (2/g²) η √Q` (`second_moment_regCoeff_le`), `F = flow2(σ; ξ, X_a, ‖ψ₀‖)`
bounds `X(v)/r` for `v ∈ {P ψ(t), ψ_g(t)}`, `o = 8 C_χ F + 8 D⁽⁴⁾_χ ‖ψ₀‖` bounds `X(O_g v)/r`
(`lem:grid-obs2`), and `Φ = flow2(σ; o, W_o, C_χ ‖ψ₀‖)`; none of `ξ, F, o, Φ` depends on `m`. -/
theorem grid_observable_error_sharp (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ} (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (rho₁ rho₂ rho₄ Blow Cs Bker : ℝ) (hK₄ : 1 ≤ (2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ))
    (hRho₁ : 0 ≤ rho₁) (hRhoScale₁ : rho₁ ^ 2 * ((2 * Real.pi / L) * (m : ℝ)) = 1)
    (hRho₂ : 0 ≤ rho₂) (hRhoScale₂ : rho₂ ^ 2 * ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) = 1)
    (hRho₄ : 0 ≤ rho₄) (hRhoScale₄ : rho₄ ^ 2 * ((2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ)) = 1)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (a : Fin eta) (χ : Lattice3 → ℂ) (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (hχ4 : Summable fun ν => nsq ν ^ 2 * ‖χ ν‖)
    (hreal : ∀ ν, χ (-ν) = conj (χ ν)) (k₀ : ℕ) (hk₀ : 2 ≤ k₀)
    (hk₀g : 1 ≤ (2 * Real.pi / L) * k₀) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB sys L Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
    let tl : ℝ → ℝ → ℝ := fun K ρ =>
      (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    let s₀ : ℕ := m / 4
    let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (coulombCellAmplitude L)
    let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
    let CO : ℝ := ‖convOp (eta := eta) a χ‖
    let Cχ : ℝ := ∑' ν, ‖χ ν‖
    let τχ : ℝ := ∑' ν, if g * (m : ℝ) < g * Real.sqrt (latticeNormSq ν) then ‖χ ν‖ else 0
    let cJ : ℝ := gridFlowConst sys L
    let Xb : ℝ := 5 / 3 * Xa + cJ * S0
    let W : ℝ := 5 / 3 * ((2 + 12 * sys.maxMass) * Cχ * Xb + 14 * momTwo χ * S0) + cJ * (Cχ * S0)
    let Q : ℝ := (k₀ : ℝ) ^ 4 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 / g ^ 4 + 30 * Ct M₀ ^ 2 / g
    let r : ℝ := Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3
    let cH : ℝ := 26 * coulombGridCoupling sys L * (J0g (coulombGridCoupling sys L) g : ℝ)
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
  have hb : 0 ≤ b := relB_nonneg sys L Hunit hC
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
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM₀
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
  have hcJ : 0 ≤ cJ := gridFlowConst_nonneg sys hL
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
    have h := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u
    rw [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
    exact h
  have hu₀_le : ‖u₀‖ ≤ M₀ :=
    hnorm_le u₀ rfl (kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u₀)
  -- the tails at `K` and `2K`
  have ht₁ : ∀ c, ‖tailMask g (g * (m : ℝ)) c (molecularH2StateMap eta g u)‖ ≤ t₁ := fun c =>
    (tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph c (g * (m : ℝ)) rho₁ Blow Cs
      Bker hK₁ hRho₁ hRhoScale₁ hBlow hCs hBker hK₁2g hAmplitude hBkerScale hCsScale u₀ v₀ huv t u
      hu1 hu2).2
  have ht₂ : ∀ c, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖ ≤ t₂ :=
    fun c => (tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph c
      (g * ((2 * m : ℕ) : ℝ)) rho₂ Blow Cs Bker hK₂ hRho₂ hRhoScale₂ hBlow hCs hBker hK₂2g
      hAmplitude hBkerScale hCsScale u₀ v₀ huv t u hu1 hu2).2
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
    refine (norm_wM_gridFlow_le sys hL hκ.bound (Ug t) (hgcomm t) _).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left ha₀ (by norm_num))
      (mul_le_mul_of_nonneg_left haS₀ hcJ)
  have hbS : ‖ψg‖ ≤ S0 := by
    show ‖Ug t (regCoeff m (molecularH2StateMap eta g u₀))‖ ≤ S0
    rw [LinearIsometryEquiv.norm_map]
    exact haS₀
  have hWa : ∀ τ, ‖wMul (wM (regParticlesOf sys))
      (Ug τ (gridObs a χ (regCoeff m (molecularH2StateMap eta g u))))‖ ≤ W := fun τ =>
    norm_wM_gridFlow_gridObs_le sys hL hκ.bound (Ug τ) (hgcomm τ) a hχ1 hχ2 _ haT hA
  have hWb : ∀ τ, ‖wMul (wM (regParticlesOf sys)) (Ug τ (gridObs a χ ψg))‖ ≤ W := fun τ =>
    norm_wM_gridFlow_gridObs_le sys hL hκ.bound (Ug τ) (hgcomm τ) a hχ1 hχ2 _ hbT hbS
  -- the sharp shells: second moments of the backward flows and the double kinetic division
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hr : 1 ≤ r := one_le_sqrt_pow_three m
  have hr0 : 0 ≤ r := by linarith
  have hZg : 0 ≤ Zg := Zc_nonneg hγ
  have hσ0 : 0 ≤ σ := mul_nonneg hZg (by positivity)
  have hcH : 0 ≤ cH :=
    mul_nonneg (mul_nonneg (by norm_num) (coulombGridCoupling_nonneg sys L hL)) (Nat.cast_nonneg _)
  have hsc : secondConst (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) g m ≤ σ * r :=
    secondConst_le (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData hγ g m
  have hX2 : ∀ (s : ℝ) (x : MolecularFourierH2 eta),
      molecularH2StateMap eta g x = U s (molecularH2StateMap eta g u₀) → H x = U s (H u₀) →
      ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys))
        (regCoeff m (molecularH2StateMap eta g x)))‖ ≤ ξ * r := by
    intro s x hx1 hx2
    have h : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys))
        (regCoeff m (molecularH2StateMap eta g x)))‖ ≤
        S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * (Real.sqrt Q * r)) :=
      second_moment_regCoeff_le sys L H hKernel Hunit hL hPeriodic hC U hgraph m Blow Cs Bker hBlow
        hCs hBker hAmplitude hBkerScale hCsScale u₀ v₀ huv s x hx1 hx2 k₀ hk₀ hk₀g
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
    have h := norm_wM_sq_gridFlow_le sys hL hκ.bound hκ.support (Ug t) (hgcomm t) _ h0' ha₀ haS₀
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
    have h := shell_gridFlow_gridObs_le sys hL hκ Ug hgcomm a hχ1 hχ2 hχ4 v hr hXv hYv hSv hXb0
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
    have h := grid_duality_shell sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph
        hderiv m hm hκ Ug hg0
      hgcomm hgderiv rho₂ rho₄ Blow Cs Bker hK₄ hRho₂ hRhoScale₂ hRho₄ hRhoScale₄ hBlow hCs hBker
      hAmplitude hBkerScale hCsScale u₀ v₀ huv _ W τφ hWa hτφ0 hτa ht
    rw [he]
    exact h
  have hd2 : ‖⟪regCoeff m (molecularH2StateMap eta g u) - ψg, gridObs a χ ψg⟫_ℂ‖ ≤ Bd * t := by
    have h := grid_duality_shell sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph
        hderiv m hm hκ Ug hg0
      hgcomm hgderiv rho₂ rho₄ Blow Cs Bker hK₄ hRho₂ hRhoScale₂ hRho₄ hRhoScale₄ hBlow hCs hBker
      hAmplitude hBkerScale hCsScale u₀ v₀ huv _ W τφ hWb hτφ0 hτb ht
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

end PlaneWaveGridDynamics

end DevGS4
-- END SOURCE dev/DevGS4.lean

-- BEGIN SOURCE dev/DevGS5.lean
-- SHA256 927ac37a6467aa8f2e1bf99ca964d48bce83b5c5467843bf0f931183f6b90c26
section DevGS5

/-!
# Grid dynamics: the rates of `thm:grid-dyn-sharp`

With `ρ = K^{-1/2}` (`K = g m`), the explicit bound of `grid_observable_error_sharp` is at most

  `A₁ K^{-5} + A₂ t K^{-3} + A₃ K^{-5/2} τ_χ(K) + ‖ψ₀‖² τ_χ^∞(m)`

with constants `(A₁, A₂, A₃) = gridConstsSharp` that do not depend on `m` (that is `K`) or `t`
(`grid_observable_rate_sharp`).  The double kinetic division gives the flow shell
`τ_φ = m̄² r Φ/(⌊m/4⌋+1)⁴ ≤ T g² ρ⁵` with `T = 3072 m̄² Φ √g` (`shell_rate_sharp`, from
`r = (4m+1)^{3/2} ≤ 12 m^{3/2}` and `⌊m/4⌋ + 1 > m/4`), and every source of term (III) then pairs
at `ρ⁶ = K^{-3}` (`rate_arith_III_sharp`).  The first threshold of the layer cake is
`k₀ = max 2 ⌈1/g⌉` (`kZero`), so `Φ = gridPhi` depends only on the data.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset Set

namespace PlaneWaveGridDynamics

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics

/-! ## Arithmetic of the sharp rates -/

section Arith

/-- The first threshold of the layer cake: `k₀ = max 2 ⌈1/g⌉`, so `k₀ ≥ 2` and `g k₀ ≥ 1`. -/
noncomputable def kZero (g : ℝ) : ℕ := max 2 ⌈1 / g⌉₊

lemma two_le_kZero (g : ℝ) : 2 ≤ kZero g := le_max_left _ _

lemma one_le_mul_kZero {g : ℝ} (hg : 0 < g) : 1 ≤ g * (kZero g : ℝ) := by
  have h1 : 1 / g ≤ (kZero g : ℝ) := by
    have h2 : 1 / g ≤ (⌈1 / g⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈1 / g⌉₊ : ℝ) ≤ (kZero g : ℝ) := by
      exact_mod_cast le_max_right 2 ⌈1 / g⌉₊
    linarith
  calc (1 : ℝ) = g * (1 / g) := by field_simp
    _ ≤ g * (kZero g : ℝ) := mul_le_mul_of_nonneg_left h1 hg.le

/-- **The sharp shells:** with `r = (4m+1)^{3/2}` and `s₀ = ⌊m/4⌋`, `r/(s₀+1)⁴ ≤ 3072 g² √g ρ⁵`
and `m r/(s₀+1)⁴ ≤ 3072 g √g ρ³` when `ρ² g m = 1` and `m ≥ 8`. -/
lemma shell_rate_sharp {g ρ : ℝ} {m : ℕ} (hg : 0 < g) (hρ : 0 ≤ ρ) (hm : 8 ≤ m)
    (hρK : ρ ^ 2 * (g * (m : ℝ)) = 1) :
    Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 / (((m / 4 : ℕ) : ℝ) + 1) ^ 4 ≤
        3072 * (g ^ 2 * Real.sqrt g) * ρ ^ 5 ∧
      (m : ℝ) * (Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 / (((m / 4 : ℕ) : ℝ) + 1) ^ 4) ≤
        3072 * (g * Real.sqrt g) * ρ ^ 3 := by
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
  have hsm2 : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt hm0.le
  have hsg2 : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg.le
  -- `ρ √g √m = 1`
  have hkey : ρ * Real.sqrt g * Real.sqrt (m : ℝ) = 1 := by
    have h1 : (ρ * Real.sqrt g * Real.sqrt (m : ℝ)) ^ 2 = 1 := by
      rw [mul_pow, mul_pow, hsg2, hsm2]
      linarith
    have h2 : 0 ≤ ρ * Real.sqrt g * Real.sqrt (m : ℝ) := by positivity
    have h3 := Real.sqrt_sq h2
    rw [h1, Real.sqrt_one] at h3
    exact h3.symm
  -- `r ≤ 12 m^{3/2}`
  have hr : Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 ≤ 12 * Real.sqrt (m : ℝ) ^ 3 := by
    have h1 : Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ≤ Real.sqrt 5 * Real.sqrt (m : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt
      have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      push_cast
      linarith
    have h5 : Real.sqrt 5 ≤ 12 / 5 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have h53 : Real.sqrt 5 ^ 3 ≤ 12 := by
      have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      calc Real.sqrt 5 ^ 3 = Real.sqrt 5 ^ 2 * Real.sqrt 5 := by ring
        _ = 5 * Real.sqrt 5 := by rw [hsq]
        _ ≤ 5 * (12 / 5) := by linarith
        _ = 12 := by norm_num
    calc Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 ≤ (Real.sqrt 5 * Real.sqrt (m : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 3
      _ = Real.sqrt 5 ^ 3 * Real.sqrt (m : ℝ) ^ 3 := by ring
      _ ≤ 12 * Real.sqrt (m : ℝ) ^ 3 := mul_le_mul_of_nonneg_right h53 (by positivity)
  -- `(s₀ + 1)⁴ ≥ m⁴/256`
  have hs : (m : ℝ) ≤ 4 * (((m / 4 : ℕ) : ℝ) + 1) := by
    have : m ≤ 4 * (m / 4 + 1) := by omega
    have h' : ((m : ℕ) : ℝ) ≤ ((4 * (m / 4 + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    linarith
  have hp : (0 : ℝ) < (((m / 4 : ℕ) : ℝ) + 1) ^ 4 := by positivity
  have hs4 : Real.sqrt (m : ℝ) ^ 8 ≤ 256 * (((m / 4 : ℕ) : ℝ) + 1) ^ 4 := by
    have e : Real.sqrt (m : ℝ) ^ 8 = (m : ℝ) ^ 4 := by
      rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, hsm2]
    rw [e]
    calc (m : ℝ) ^ 4 ≤ (4 * (((m / 4 : ℕ) : ℝ) + 1)) ^ 4 := pow_le_pow_left₀ hm0.le hs 4
      _ = 256 * (((m / 4 : ℕ) : ℝ) + 1) ^ 4 := by ring
  -- `r/(s₀+1)⁴ ≤ 3072 m^{-5/2}`
  have hq : Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 / (((m / 4 : ℕ) : ℝ) + 1) ^ 4 ≤
      3072 / Real.sqrt (m : ℝ) ^ 5 := by
    rw [div_le_div_iff₀ hp (by positivity)]
    calc Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 * Real.sqrt (m : ℝ) ^ 5
        ≤ 12 * Real.sqrt (m : ℝ) ^ 3 * Real.sqrt (m : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right hr (by positivity)
      _ = 12 * Real.sqrt (m : ℝ) ^ 8 := by ring
      _ ≤ 12 * (256 * (((m / 4 : ℕ) : ℝ) + 1) ^ 4) :=
          mul_le_mul_of_nonneg_left hs4 (by norm_num)
      _ = 3072 * (((m / 4 : ℕ) : ℝ) + 1) ^ 4 := by ring
  -- `m^{-1/2} = ρ √g`
  have hinv : 1 / Real.sqrt (m : ℝ) = ρ * Real.sqrt g := by
    rw [div_eq_iff hsm.ne']
    exact hkey.symm
  constructor
  · calc _ ≤ 3072 / Real.sqrt (m : ℝ) ^ 5 := hq
      _ = 3072 * (1 / Real.sqrt (m : ℝ)) ^ 5 := by ring
      _ = 3072 * (ρ * Real.sqrt g) ^ 5 := by rw [hinv]
      _ = 3072 * (Real.sqrt g ^ 2 * Real.sqrt g ^ 2 * Real.sqrt g) * ρ ^ 5 := by ring
      _ = 3072 * (g ^ 2 * Real.sqrt g) * ρ ^ 5 := by rw [hsg2]; ring
  · calc (m : ℝ) * (Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 / (((m / 4 : ℕ) : ℝ) + 1) ^ 4)
        ≤ (m : ℝ) * (3072 / Real.sqrt (m : ℝ) ^ 5) := mul_le_mul_of_nonneg_left hq hm0.le
      _ = Real.sqrt (m : ℝ) ^ 2 * (3072 / Real.sqrt (m : ℝ) ^ 5) := by rw [hsm2]
      _ = 3072 * (1 / Real.sqrt (m : ℝ)) ^ 3 := by
          have hsm' : Real.sqrt (m : ℝ) ≠ 0 := hsm.ne'
          field_simp
      _ = 3072 * (ρ * Real.sqrt g) ^ 3 := by rw [hinv]
      _ = 3072 * (Real.sqrt g ^ 2 * Real.sqrt g) * ρ ^ 3 := by ring
      _ = 3072 * (g * Real.sqrt g) * ρ ^ 3 := by rw [hsg2]

/-- Term (III), sharp: `2 t B_d ≤ A₂ t ρ⁶` when the flow shell is `τ_φ ≤ T g² ρ⁵` and
`m τ_φ ≤ T g ρ³`. -/
lemma rate_arith_III_sharp {η t₂ τ₁ ρ ρ₂ CtL Zg fA cF t₄ β₄ mm W τφ T Xa g m t : ℝ} (hη : 0 ≤ η)
    (hτ₁ : 0 ≤ τ₁) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (ht₂ : t₂ ≤ τ₁ * ρ ^ 5)
    (hρ₂ : ρ₂ ≤ ρ) (hρ₂0 : 0 ≤ ρ₂) (hCtL : 0 ≤ CtL) (hZg : 0 ≤ Zg) (hfA : fA ≤ cF * ρ)
    (hfA0 : 0 ≤ fA) (ht₄ : t₄ ≤ β₄ * ρ ^ 5) (ht₄0 : 0 ≤ t₄) (hmW : 0 ≤ mm * W)
    (hτφ : τφ ≤ T * g ^ 2 * ρ ^ 5) (hτφ0 : 0 ≤ τφ)
    (hmτ : m * τφ ≤ T * g * ρ ^ 3) (hXa : 0 ≤ Xa) (hg : 0 ≤ g) (ht : 0 ≤ t)
    (hβ₄ : 0 ≤ β₄) (hT : 0 ≤ T) :
    2 * (((η * t₂) * (η * (CtL * ρ₂)) +
        Zg * (fA * (t₄ * (mm * W) + τφ * Xa) + 52 * m * (τφ * t₄))) * t) ≤
      2 * (η * (η * τ₁) * CtL +
        Zg * (cF * β₄ * (mm * W) + cF * T * g ^ 2 * Xa + 52 * T * g * β₄)) * t * ρ ^ 6 := by
  have hcF : 0 ≤ cF * ρ := hfA0.trans hfA
  have hρ8 : ρ ^ 8 ≤ ρ ^ 6 := pow_le_pow_of_le_one hρ hρ1 (by norm_num)
  -- the Galerkin source
  have hG : (η * t₂) * (η * (CtL * ρ₂)) ≤ η * (η * τ₁) * CtL * ρ ^ 6 := by
    have h1 : η * t₂ ≤ η * (τ₁ * ρ ^ 5) := mul_le_mul_of_nonneg_left ht₂ hη
    have h2 : η * (CtL * ρ₂) ≤ η * (CtL * ρ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hρ₂ hCtL) hη
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : η * (τ₁ * ρ ^ 5) * (η * (CtL * ρ)) = η * (η * τ₁) * CtL * ρ ^ 6 := by ring
    linarith
  -- the grid difference
  have hD1 : fA * (t₄ * (mm * W) + τφ * Xa) ≤
      (cF * β₄ * (mm * W) + cF * T * g ^ 2 * Xa) * ρ ^ 6 := by
    have h1 : t₄ * (mm * W) + τφ * Xa ≤ β₄ * ρ ^ 5 * (mm * W) + T * g ^ 2 * ρ ^ 5 * Xa :=
      add_le_add (mul_le_mul_of_nonneg_right ht₄ hmW) (mul_le_mul_of_nonneg_right hτφ hXa)
    have h2 := mul_le_mul hfA h1 (by positivity) hcF
    have e : cF * ρ * (β₄ * ρ ^ 5 * (mm * W) + T * g ^ 2 * ρ ^ 5 * Xa) =
        (cF * β₄ * (mm * W) + cF * T * g ^ 2 * Xa) * ρ ^ 6 := by ring
    linarith
  have hD2 : 52 * m * (τφ * t₄) ≤ 52 * T * g * β₄ * ρ ^ 6 := by
    have h1 : 52 * m * (τφ * t₄) = 52 * (m * τφ) * t₄ := by ring
    have h2 : 52 * (m * τφ) * t₄ ≤ 52 * (T * g * ρ ^ 3) * (β₄ * ρ ^ 5) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmτ (by norm_num)) ht₄ ht₄0 (by positivity)
    have e : 52 * (T * g * ρ ^ 3) * (β₄ * ρ ^ 5) = 52 * T * g * β₄ * ρ ^ 8 := by ring
    have h3 : 52 * T * g * β₄ * ρ ^ 8 ≤ 52 * T * g * β₄ * ρ ^ 6 :=
      mul_le_mul_of_nonneg_left hρ8 (by positivity)
    linarith
  have hB : (η * t₂) * (η * (CtL * ρ₂)) +
      Zg * (fA * (t₄ * (mm * W) + τφ * Xa) + 52 * m * (τφ * t₄)) ≤
      (η * (η * τ₁) * CtL +
        Zg * (cF * β₄ * (mm * W) + cF * T * g ^ 2 * Xa + 52 * T * g * β₄)) * ρ ^ 6 := by
    have h1 := mul_le_mul_of_nonneg_left (add_le_add hD1 hD2) hZg
    have e : Zg * ((cF * β₄ * (mm * W) + cF * T * g ^ 2 * Xa) * ρ ^ 6 +
        52 * T * g * β₄ * ρ ^ 6) =
        Zg * (cF * β₄ * (mm * W) + cF * T * g ^ 2 * Xa + 52 * T * g * β₄) * ρ ^ 6 := by ring
    have e2 : (η * (η * τ₁) * CtL +
        Zg * (cF * β₄ * (mm * W) + cF * T * g ^ 2 * Xa + 52 * T * g * β₄)) * ρ ^ 6 =
        η * (η * τ₁) * CtL * ρ ^ 6 +
          Zg * (cF * β₄ * (mm * W) + cF * T * g ^ 2 * Xa + 52 * T * g * β₄) * ρ ^ 6 := by ring
    linarith
  have h := mul_le_mul_of_nonneg_right hB ht
  have e : (η * (η * τ₁) * CtL +
      Zg * (cF * β₄ * (mm * W) + cF * T * g ^ 2 * Xa + 52 * T * g * β₄)) * ρ ^ 6 * t =
      (η * (η * τ₁) * CtL +
        Zg * (cF * β₄ * (mm * W) + cF * T * g ^ 2 * Xa + 52 * T * g * β₄)) * t * ρ ^ 6 := by ring
  linarith

/-- **The rates of `thm:grid-dyn-sharp`.** The explicit bound of `grid_observable_error_sharp`, at
`ρ = K^{-1/2}` (`K = g m`), `ρ₂ = (2K)^{-1/2}`, `ρ₄ = (g⌊m/4⌋)^{-1/2}` and the flow shell
`τ_φ = m̄² r Φ/(⌊m/4⌋+1)⁴` (`r = (4m+1)^{3/2}`), is at most
`A₁ K^{-5} + A₂ t K^{-3} + A₃ K^{-5/2} τ_χ + S0² τ^∞` for `m ≥ 8` and `K ≥ 8`. -/
lemma grid_rate_arith_sharp {η mm Ξ₁ C₀ g t S0 sT Cχ CO τχ Zg Xa W Φ : ℝ} {m : ℕ} {Ct : ℝ → ℝ}
    (hη : 0 ≤ η) (hmm : 1 ≤ mm) (hΞ₁ : 0 ≤ Ξ₁) (hC₀ : 0 ≤ C₀) (hg : 0 < g) (hm : 8 ≤ m)
    (hK : 8 ≤ g * m) (ht : 0 ≤ t) (hS0 : 0 ≤ S0) (hCχ : 0 ≤ Cχ) (hCO : 0 ≤ CO)
    (hτχ : 0 ≤ τχ) (hZg : 0 ≤ Zg) (hXa : 0 ≤ Xa) (hW : 0 ≤ W) (hCt : ∀ M, 0 ≤ M → 0 ≤ Ct M)
    (hΦ : 0 ≤ Φ) :
    let K : ℝ := g * m
    let tl : ℝ → ℝ → ℝ := fun K ρ => (2 * mm / K ^ 2) * ((2 * mm / K ^ 2) * Ξ₁ + C₀ * ρ)
    let ρ : ℝ := Real.sqrt (1 / K)
    let ρ₂ : ℝ := Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))
    let ρ₄ : ℝ := Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))
    let s₀ : ℕ := m / 4
    let r : ℝ := Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3
    let τφ : ℝ := mm ^ 2 * (r * Φ) / ((s₀ : ℝ) + 1) ^ 4
    let t₁ : ℝ := tl (g * (m : ℝ)) ρ
    let t₂ : ℝ := tl (g * ((2 * m : ℕ) : ℝ)) ρ₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) ρ₄
    let δ : ℝ := η * t₂
    let Bd : ℝ := (η * t₂) * (η * (Ct ((1 + g ^ 2) * (mm * W)) * ρ₂)) +
      Zg * (formA s₀ m * (t₄ * (mm * W) + τφ * Xa) + 52 * m * (τφ * t₄))
    let τ₁ : ℝ := 2 * mm * (2 * mm * Ξ₁ + C₀)
    let β₄ : ℝ := 128 * mm * (128 * mm * Ξ₁ + 8 * C₀)
    let δ₁ : ℝ := η * τ₁
    let cF : ℝ := 4 * Real.sqrt (5512 * g)
    let T : ℝ := 3072 * mm ^ 2 * Φ * Real.sqrt g
    (2 * (δ * (Cχ * t₁ + τχ * S0 + CO * δ)) + CO * δ ^ 2) + (Cχ * (t₁ * t₁) + sT * (S0 * S0)) +
        2 * (Bd * t) ≤
      (2 * δ₁ * (Cχ * τ₁ + CO * δ₁) + CO * δ₁ ^ 2 + Cχ * τ₁ ^ 2) * (1 / K) ^ 5 +
        2 * (η * δ₁ * Ct ((1 + g ^ 2) * (mm * W)) +
          Zg * (cF * β₄ * (mm * W) + cF * T * g ^ 2 * Xa + 52 * T * g * β₄)) * t * (1 / K) ^ 3 +
        2 * δ₁ * S0 * Real.sqrt (1 / K) ^ 5 * τχ + S0 ^ 2 * sT := by
  intro K tl ρ ρ₂ ρ₄ s₀ r τφ t₁ t₂ t₄ δ Bd τ₁ β₄ δ₁ cF T
  have hmm0 : 0 ≤ mm := by linarith
  have hKpos : 0 < K := by show 0 < g * (m : ℝ); linarith
  have hK1 : 1 ≤ K := by show 1 ≤ g * (m : ℝ); linarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρK : ρ ^ 2 * K = 1 := by
    show Real.sqrt (1 / K) ^ 2 * K = 1
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hρ2 : ρ ^ 2 = 1 / K := Real.sq_sqrt (by positivity)
  have hρ1 : ρ ≤ 1 := by
    have h5 : ρ ^ 2 ≤ 1 := by
      rw [hρ2, div_le_one hKpos]
      exact hK1
    nlinarith
  have hρK' : ρ ^ 2 * (g * (m : ℝ)) = 1 := hρK
  -- the cube `2m` and the threshold `⌊m/4⌋`
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hK₂pos : 0 < g * ((2 * m : ℕ) : ℝ) := by rw [h2m]; positivity
  have hK₂ : K ≤ 1 * (g * ((2 * m : ℕ) : ℝ)) := by
    show g * (m : ℝ) ≤ 1 * (g * ((2 * m : ℕ) : ℝ))
    rw [h2m]
    nlinarith
  have hρ₂0 : 0 ≤ ρ₂ := Real.sqrt_nonneg _
  have hρ₂K : ρ₂ ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1 := by
    show Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hρ₂ρ : ρ₂ ≤ ρ := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hK₂pos hKpos]
    have := hK₂
    linarith
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hs0 : (0 : ℝ) < ((m / 4 : ℕ) : ℝ) := by
    have : 0 < m / 4 := by omega
    exact_mod_cast this
  have hK₄pos : 0 < g * ((m / 4 : ℕ) : ℝ) := by positivity
  have hK₄ : K ≤ 8 * (g * (s₀ : ℝ)) := by
    show g * (m : ℝ) ≤ 8 * (g * ((m / 4 : ℕ) : ℝ))
    nlinarith
  have hρ₄0 : 0 ≤ ρ₄ := Real.sqrt_nonneg _
  have hρ₄K : ρ₄ ^ 2 * (g * (s₀ : ℝ)) = 1 := by
    show Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ))) ^ 2 * (g * ((m / 4 : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  -- the tails
  have hτ₁0 : 0 ≤ τ₁ := by positivity
  have hβ₄0 : 0 ≤ β₄ := by positivity
  have ht₁ : t₁ ≤ τ₁ * ρ ^ 5 := by
    have h := tl_rate (c := 1) hmm0 hΞ₁ hC₀ le_rfl hρ0 hρK hK1 (by linarith) hρ0 hρK
    have e : 2 * mm * 1 ^ 2 * (2 * mm * 1 ^ 2 * Ξ₁ + 1 * C₀) * ρ ^ 5 = τ₁ * ρ ^ 5 := by
      show _ = 2 * mm * (2 * mm * Ξ₁ + C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have ht₂ : t₂ ≤ τ₁ * ρ ^ 5 := by
    have h := tl_rate (c := 1) hmm0 hΞ₁ hC₀ le_rfl hρ0 hρK hK1 hK₂ hρ₂0 hρ₂K
    have e : 2 * mm * 1 ^ 2 * (2 * mm * 1 ^ 2 * Ξ₁ + 1 * C₀) * ρ ^ 5 = τ₁ * ρ ^ 5 := by
      show _ = 2 * mm * (2 * mm * Ξ₁ + C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have ht₄ : t₄ ≤ β₄ * ρ ^ 5 := by
    have h := tl_rate (c := 8) hmm0 hΞ₁ hC₀ (by norm_num) hρ0 hρK hK1 hK₄ hρ₄0 hρ₄K
    have e : 2 * mm * 8 ^ 2 * (2 * mm * 8 ^ 2 * Ξ₁ + 8 * C₀) * ρ ^ 5 = β₄ * ρ ^ 5 := by
      show _ = 128 * mm * (128 * mm * Ξ₁ + 8 * C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have htl0 : ∀ K' ρ', 0 ≤ ρ' → 0 ≤ tl K' ρ' := by
    intro K' ρ' hρ'
    show 0 ≤ (2 * mm / K' ^ 2) * ((2 * mm / K' ^ 2) * Ξ₁ + C₀ * ρ')
    have h1 : 0 ≤ 2 * mm / K' ^ 2 := div_nonneg (by linarith) (sq_nonneg K')
    exact mul_nonneg h1 (add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hC₀ hρ'))
  have ht₁0 : 0 ≤ t₁ := htl0 _ _ hρ0
  have ht₂0 : 0 ≤ t₂ := htl0 _ _ hρ₂0
  have ht₄0 : 0 ≤ t₄ := htl0 _ _ hρ₄0
  -- the form constant and the shells
  have hfA : formA s₀ m ≤ cF * ρ := formA_rate hg hρ0 hm hρK'
  have hsh := shell_rate_sharp hg hρ0 hm hρK'
  have hmW : 0 ≤ mm * W := by positivity
  have hT0 : 0 ≤ T := by positivity
  have hr0 : 0 ≤ r := pow_nonneg (Real.sqrt_nonneg _) 3
  have hsh1 : r / ((s₀ : ℝ) + 1) ^ 4 ≤ 3072 * (g ^ 2 * Real.sqrt g) * ρ ^ 5 := hsh.1
  have hsh2 : (m : ℝ) * (r / ((s₀ : ℝ) + 1) ^ 4) ≤ 3072 * (g * Real.sqrt g) * ρ ^ 3 := hsh.2
  have hmΦ : 0 ≤ mm ^ 2 * Φ := mul_nonneg (sq_nonneg _) hΦ
  have hτφ : τφ ≤ T * g ^ 2 * ρ ^ 5 := by
    have e : τφ = (mm ^ 2 * Φ) * (r / ((s₀ : ℝ) + 1) ^ 4) := by
      show mm ^ 2 * (r * Φ) / ((s₀ : ℝ) + 1) ^ 4 = _
      ring
    rw [e]
    have h := mul_le_mul_of_nonneg_left hsh1 hmΦ
    have e2 : mm ^ 2 * Φ * (3072 * (g ^ 2 * Real.sqrt g) * ρ ^ 5) = T * g ^ 2 * ρ ^ 5 := by
      show _ = 3072 * mm ^ 2 * Φ * Real.sqrt g * g ^ 2 * ρ ^ 5
      ring
    linarith
  have hτφ0 : 0 ≤ τφ :=
    div_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hr0 hΦ)) (by positivity)
  have hmτ : (m : ℝ) * τφ ≤ T * g * ρ ^ 3 := by
    have e : (m : ℝ) * τφ = (mm ^ 2 * Φ) * ((m : ℝ) * (r / ((s₀ : ℝ) + 1) ^ 4)) := by
      show (m : ℝ) * (mm ^ 2 * (r * Φ) / ((s₀ : ℝ) + 1) ^ 4) = _
      ring
    rw [e]
    have h := mul_le_mul_of_nonneg_left hsh2 hmΦ
    have e2 : mm ^ 2 * Φ * (3072 * (g * Real.sqrt g) * ρ ^ 3) = T * g * ρ ^ 3 := by
      show _ = 3072 * mm ^ 2 * Φ * Real.sqrt g * g * ρ ^ 3
      ring
    linarith
  have hCtL : 0 ≤ Ct ((1 + g ^ 2) * (mm * W)) := hCt _ (by positivity)
  -- the two pieces
  have hI := rate_arith_I (sT := sT) hη hτ₁0 rfl ht₁ ht₂ ht₁0 ht₂0 hCχ hCO hτχ hS0 hρ0
  have hIII := rate_arith_III_sharp (m := (m : ℝ)) (Xa := Xa) hη hτ₁0 hρ0 hρ1 ht₂ hρ₂ρ hρ₂0 hCtL hZg
    hfA (formA_nonneg s₀ m) ht₄ ht₄0 hmW hτφ hτφ0 hmτ hXa hg.le ht hβ₄0 hT0
  have hρ10 : ρ ^ 10 = (1 / K) ^ 5 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, pow_mul, hρ2]
  have hρ6 : ρ ^ 6 = (1 / K) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hρ2]
  rw [hρ10] at hI
  rw [hρ6] at hIII
  show _ ≤ _ + _ * t * (1 / K) ^ 3 + 2 * δ₁ * S0 * ρ ^ 5 * τχ + S0 ^ 2 * sT
  linarith

end Arith

/-! ## The sharp rates for the Coulomb system -/

section Rates

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- The second-moment constant `Φ` of the backward flows of the smeared states
(`grid_observable_error_sharp`) at the threshold `k₀ = kZero g`, as a function of the scalar data
`s0 = ‖ψ₀‖`, `hu = ‖H ψ₀‖`, `hs = ‖H ψ₀‖` (the decoded state of `H ψ₀`) and `hv = ‖H² ψ₀‖`; it does
not depend on `m` or `t`. -/
noncomputable def gridPhi (sys : CoulombSystem eta ν) (L Hunit Blow Cs Bker : ℝ)
    (χ : Lattice3 → ℂ) (s0 hu hs hv : ℝ) : ℝ :=
  let g : ℝ := 2 * Real.pi / L
  let b : ℝ := relB sys L Hunit
  let S0 : ℝ := s0
  let Ξ₀ : ℝ := 2 * hu + 2 * b * S0
  let Ξ₁ : ℝ := 2 * hv + 2 * b * hs
  let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
  let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
  let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
  let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
  let Cχ : ℝ := ∑' ν, ‖χ ν‖
  let cJ : ℝ := gridFlowConst sys L
  let Xb : ℝ := 5 / 3 * Xa + cJ * S0
  let Q : ℝ := ((kZero g : ℕ) : ℝ) ^ 4 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 / g ^ 4 +
    30 * Ct M₀ ^ 2 / g
  let cH : ℝ := 26 * coulombGridCoupling sys L * (J0g (coulombGridCoupling sys L) g : ℝ)
  let σ : ℝ := Zg * (52 * (J0g (sys.maxMass * Zg) g : ℝ) + 4 * Real.sqrt 53 * sys.maxMass)
  let ξ : ℝ := S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * Real.sqrt Q)
  let F : ℝ := flow2 g cJ cH σ ξ Xa S0
  let Wo : ℝ := (2 + 12 * sys.maxMass) * Cχ * Xb + 14 * momTwo χ * S0
  let o : ℝ := 8 * Cχ * F + 8 * momFour χ * S0
  flow2 g cJ cH σ o Wo (Cχ * S0)

lemma gridPhi_nonneg (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (Hunit Blow Cs Bker : ℝ)
    (χ : Lattice3 → ℂ) (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    {s0 hu hs hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) :
    0 ≤ gridPhi sys L Hunit Blow Cs Bker χ s0 hu hs hv := by
  have hb := relB_nonneg sys L Hunit hC
  have hM := sys.one_le_maxMass
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hZ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg hγ
  have hcJ := gridFlowConst_nonneg sys hL
  have hcH : 0 ≤ 26 * coulombGridCoupling sys L *
      (J0g (coulombGridCoupling sys L) (2 * Real.pi / L) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (coulombGridCoupling_nonneg sys L hL)) (Nat.cast_nonneg _)
  have hCχ : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hD2 : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hD4 := momFour_nonneg χ
  have hσ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) * (52 * (J0g (sys.maxMass * Zc (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (2 * Real.pi / L) : ℝ) +
        4 * Real.sqrt 53 * sys.maxMass) := by positivity
  have hΞ₀ : 0 ≤ 2 * hu + 2 * relB sys L Hunit * s0 := by positivity
  have hXa : 0 ≤ (1 + 1 / (2 * Real.pi / L) ^ 2) *
      (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB sys L Hunit * s0))) := by positivity
  have hXb : 0 ≤ 5 / 3 * ((1 + 1 / (2 * Real.pi / L) ^ 2) *
      (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB sys L Hunit * s0)))) +
      gridFlowConst sys L * s0 := by positivity
  show 0 ≤ flow2 _ _ _ _ _ _ _
  refine flow2_nonneg hcJ hcH hσ ?_ ?_ (mul_nonneg hCχ h0)
  · refine add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCχ) ?_)
      (mul_nonneg (mul_nonneg (by norm_num) hD4) h0)
    refine flow2_nonneg hcJ hcH hσ ?_ hXa h0
    have hQ : 0 ≤ (2 : ℝ) / (2 * Real.pi / L) ^ 2 * (eta * Real.sqrt
        (((kZero (2 * Real.pi / L) : ℕ) : ℝ) ^ 4 * (2 * hu + 2 * relB sys L Hunit * s0) ^ 2 +
          120 * sys.maxMass ^ 2 * (2 * hv + 2 * relB sys L Hunit * hs) ^ 2 /
            (2 * Real.pi / L) ^ 4 +
          30 * finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
            (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB sys L Hunit * s0))) ^ 2 /
            (2 * Real.pi / L))) :=
      mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    have hX0 : 0 ≤ 4 / (2 * Real.pi / L) ^ 2 * (2 * hu + 2 * relB sys L Hunit * s0) :=
      mul_nonneg (by positivity) hΞ₀
    exact add_nonneg (add_nonneg h0 hX0) hQ
  · exact add_nonneg (mul_nonneg (mul_nonneg (by linarith) hCχ) hXb)
      (mul_nonneg (mul_nonneg (by norm_num) hD2) h0)

/-- The constants `(A₁, A₂, A₃)` of `thm:grid-dyn-sharp`, as functions of the scalar data
`s0 = ‖ψ₀‖`, `hu = ‖H ψ₀‖`, `hs = ‖H ψ₀‖` (the decoded state of `H ψ₀`) and `hv = ‖H² ψ₀‖`; they do
not depend on `m` (that is `K`) or on `t`.  Only `A₂` differs from `gridConsts`: the flow shell
enters through `T = 3072 m̄² Φ √g`, `Φ = gridPhi`. -/
noncomputable def gridConstsSharp (sys : CoulombSystem eta ν) (L Hunit Blow Cs Bker : ℝ)
    (a : Fin eta) (χ : Lattice3 → ℂ) (s0 hu hs hv : ℝ) : ℝ × ℝ × ℝ :=
  let g : ℝ := 2 * Real.pi / L
  let b : ℝ := relB sys L Hunit
  let S0 : ℝ := s0
  let Ξ₀ : ℝ := 2 * hu + 2 * b * S0
  let Ξ₁ : ℝ := 2 * hv + 2 * b * hs
  let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
  let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
  let τ₁ : ℝ := 2 * sys.maxMass * (2 * sys.maxMass * Ξ₁ + Ct M₀)
  let β₄ : ℝ := 128 * sys.maxMass * (128 * sys.maxMass * Ξ₁ + 8 * Ct M₀)
  let δ₁ : ℝ := eta * τ₁
  let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
  let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
  let CO : ℝ := ‖convOp (eta := eta) a χ‖
  let Cχ : ℝ := ∑' ν, ‖χ ν‖
  let cJ : ℝ := gridFlowConst sys L
  let Xb : ℝ := 5 / 3 * Xa + cJ * S0
  let W : ℝ := 5 / 3 * ((2 + 12 * sys.maxMass) * Cχ * Xb + 14 * momTwo χ * S0) + cJ * (Cχ * S0)
  let cF : ℝ := 4 * Real.sqrt (5512 * g)
  let T : ℝ := 3072 * sys.maxMass ^ 2 * gridPhi sys L Hunit Blow Cs Bker χ s0 hu hs hv *
    Real.sqrt g
  (2 * δ₁ * (Cχ * τ₁ + CO * δ₁) + CO * δ₁ ^ 2 + Cχ * τ₁ ^ 2,
    2 * (eta * δ₁ * Ct ((1 + g ^ 2) * (sys.maxMass * W)) +
      Zg * (cF * β₄ * (sys.maxMass * W) + cF * T * g ^ 2 * Xa + 52 * T * g * β₄)),
    2 * δ₁ * S0)

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **`thm:grid-dyn-sharp`, rates (Fourier side).** For `m ≥ 8` and `K = g m ≥ 8`, and `χ` with
in addition `D⁽⁴⁾_χ = Σ |ν|⁴ |χ̂(ν)| < ∞`,
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤ A₁ K^{-5} + A₂ t K^{-3} + A₃ K^{-5/2} τ_χ(K)
+ ‖ψ₀‖² τ_χ^∞(m)`, with `(A₁, A₂, A₃) = gridConstsSharp` (independent of `K` and `t`): the energy
rate `t K^{-3}` of the Galerkin method (`thm:dyn`). -/
theorem grid_observable_rate_sharp (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (Blow Cs Bker : ℝ) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (a : Fin eta) (χ : Lattice3 → ℂ) (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (hχ4 : Summable fun ν => nsq ν ^ 2 * ‖χ ν‖)
    (hreal : ∀ ν, χ (-ν) = conj (χ ν))
    {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridConstsSharp sys L Hunit Blow Cs Bker a χ ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then ‖χ ν‖ else 0
    let ψg := Ug t (regCoeff m (molecularH2StateMap eta g u₀))
    ‖⟪U t (molecularH2StateMap eta g u₀), convOp a χ (U t (molecularH2StateMap eta g u₀))⟫_ℂ -
        ⟪ψg, gridObs a χ ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖molecularH2StateMap eta g u₀‖ ^ 2 * supTail χ m := by
  intro g K A τχ ψg
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
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
  have hΞ₀ : 0 ≤ 2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖ := by
    positivity
  have hΞ₁ : 0 ≤ 2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖ := by
    positivity
  have hCt : ∀ M, 0 ≤ M → 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M :=
    fun M hM' => finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM'
  have hM₀ : 0 ≤ sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖)) := by positivity
  have hCχ : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hτχ : 0 ≤ τχ := tsum_nonneg fun ν => by split_ifs <;> simp
  have hZg : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg hγ
  have hcJ : 0 ≤ gridFlowConst sys L := gridFlowConst_nonneg sys hL
  have hD : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hXa : 0 ≤ (1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))) := by positivity
  have hW : 0 ≤ 5 / 3 * ((2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) *
      (5 / 3 * ((1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
        2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖)))) +
        gridFlowConst sys L * ‖molecularH2StateMap eta g u₀‖) +
      14 * momTwo χ * ‖molecularH2StateMap eta g u₀‖) +
      gridFlowConst sys L * ((∑' ν, ‖χ ν‖) * ‖molecularH2StateMap eta g u₀‖) := by positivity
  have hΦ := gridPhi_nonneg sys hL Hunit Blow Cs Bker χ hC
      (norm_nonneg (molecularH2StateMap eta g u₀))
    (norm_nonneg (H u₀)) (hs := ‖molecularH2StateMap eta g v₀‖) (hv := ‖H v₀‖)
  refine (grid_observable_error_sharp sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph
      hderiv m hm hκ Ug
    hg0 hgcomm hgderiv (Real.sqrt (1 / (g * (m : ℝ))))
    (Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))) (Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))) Blow Cs
    Bker hK₄ (Real.sqrt_nonneg _) (hscale _ hKpos) (Real.sqrt_nonneg _) (hscale _ hK₂pos)
    (Real.sqrt_nonneg _) (hscale _ hK₄pos) hBlow hCs hBker hAmplitude hBkerScale hCsScale u₀ v₀
    huv a χ hχ1 hχ2 hχ4 hreal (kZero g) (two_le_kZero g) (one_le_mul_kZero hg) ht).trans ?_
  exact grid_rate_arith_sharp (η := (eta : ℝ)) (mm := sys.maxMass)
    (Φ := gridPhi sys L Hunit Blow Cs Bker χ ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖)
    (Ξ₁ := 2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖)
    (C₀ := finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
      (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
        2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))))
    (g := g) (t := t) (S0 := ‖molecularH2StateMap eta g u₀‖) (sT := supTail χ m)
    (Cχ := ∑' ν, ‖χ ν‖) (CO := ‖convOp (eta := eta) a χ‖) (τχ := τχ)
    (Zg := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L))
    (m := m) (Ct := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M)
    (Nat.cast_nonneg eta) hM hΞ₁ (hCt _ hM₀) hg hm hK ht hS0 hCχ (norm_nonneg _) hτχ hZg hXa hW hCt
    hΦ

end Rates

end PlaneWaveGridDynamics

end DevGS5
-- END SOURCE dev/DevGS5.lean

-- BEGIN SOURCE dev/DevGS6.lean
-- SHA256 ef6bc77748cf8d77b74399740ee26563523a54db513e91e3da2082de5571eb0b
section DevGS6

/-!
# Grid dynamics: `thm:grid-dyn-sharp` in position space and under `(Hχ)`

The position-space form of the sharp rates (`grid_observable_position_sharp`: the grid propagator
`e^{-iH_pos t} = dft⁻¹ e^{-iH_grid t} dft` and the collocated observable `O_g = χ(x_{j_a})`, as in
`grid_observable_position`), and the final form under `(Hχ)`: the decay of the coefficient tails at
`M = 8` gives the fourth moment `D⁽⁴⁾_χ = Σ |ν|⁴ |χ̂(ν)| < ∞` (`summable_nsq_sq_of_HChi`), the
Fourier counterpart of the manuscript's `D_χ^{(4)}`, so `thm:grid-dyn-sharp` holds under `(Hχ)` with
the bound `C [K^{-5} + t K^{-3}] = O(N^{-5/3} + t N^{-1})` (`thm_grid_dyn_sharp`), and with the
trivial `min {1, ·}` for `[0,1]`-valued `χ` and `‖ψ₀‖ = 1` (`thm_grid_dyn_sharp_min`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset Set MeasureTheory

namespace PlaneWaveGridDynamics

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics UnitAddTorus

noncomputable section

local instance unitAddCircleMeasureSpaceForSharp : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

/-! ## `(Hχ)` gives the fourth moment -/

section Decay

/-- **`(Hχ)` at `M = 8` implies the fourth weighted summability.** If
`ρ⁸ Σ_{g‖ν‖∞ > ρ} |χ̂(ν)| ≤ C₈` for every `ρ ≥ 1`, then `Σ_ν (1 + g² |ν|²)² |χ̂(ν)| < ∞`. -/
theorem summable_weighted4_of_decay {χ : Lattice3 → ℂ} (hχ : Summable fun ν => ‖χ ν‖) {g : ℝ}
    (hg : 0 < g) (C8 : ℝ) (hHχ : ∀ ρ : ℝ, 1 ≤ ρ →
      ρ ^ 8 * (∑' ν, if ρ < g * latticeSupNorm ν then ‖χ ν‖ else 0) ≤ C8) :
    Summable fun ν => (1 + g ^ 2 * latticeNormSq ν) ^ 2 * ‖χ ν‖ := by
  have htail_summable : ∀ ρ : ℝ, Summable fun ν => if ρ < g * latticeSupNorm ν then ‖χ ν‖ else 0 :=
    fun ρ => Summable.of_nonneg_of_le (fun ν => by split_ifs <;> simp)
      (fun ν => by split_ifs <;> simp) hχ
  have hC8 : 0 ≤ C8 := by
    have h := hHχ 1 le_rfl
    have h0 : 0 ≤ ∑' ν, if (1 : ℝ) < g * latticeSupNorm ν then ‖χ ν‖ else 0 :=
      tsum_nonneg fun ν => by split_ifs <;> simp
    linarith [show (1 : ℝ) ^ 8 = 1 by norm_num]
  have hg4 : 0 < g ^ 4 := by positivity
  refine Summable.of_nonneg_of_le (fun ν => mul_nonneg (sq_nonneg _) (norm_nonneg _))
    (fun ν => ?_)
    ((hχ.mul_left 169).add (summable_inv_latticeNormSq_sq.mul_left (36864 * C8 / g ^ 4)))
  have hs := latticeSupNorm_nonneg ν
  have hsq := latticeNormSq_le_sup ν
  have hn := latticeNormSq_nonneg ν
  have hχν := norm_nonneg (χ ν)
  have hinv : 0 ≤ 36864 * C8 / g ^ 4 * (1 / latticeNormSq ν ^ 2) := by positivity
  by_cases hν : g * latticeSupNorm ν ≤ 2
  · -- low modes
    have h1 : g ^ 2 * latticeNormSq ν ≤ 12 := by
      have : g ^ 2 * latticeNormSq ν ≤ 3 * (g * latticeSupNorm ν) ^ 2 := by
        nlinarith [sq_nonneg g]
      nlinarith [mul_nonneg hg.le hs]
    have h2 : (1 + g ^ 2 * latticeNormSq ν) ^ 2 ≤ 169 := by
      have h0 : 0 ≤ 1 + g ^ 2 * latticeNormSq ν := by positivity
      calc (1 + g ^ 2 * latticeNormSq ν) ^ 2 ≤ 13 ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
        _ = 169 := by norm_num
    have : (1 + g ^ 2 * latticeNormSq ν) ^ 2 * ‖χ ν‖ ≤ 169 * ‖χ ν‖ :=
      mul_le_mul_of_nonneg_right h2 hχν
    linarith
  · -- high modes: one term of the tail at `ρ = g ‖ν‖∞ / 2`
    push Not at hν
    set ρ := g * latticeSupNorm ν / 2 with hρ
    have hρ1 : 1 ≤ ρ := by rw [hρ]; linarith
    have hρpos : 0 < ρ := by linarith
    have hmem : ρ < g * latticeSupNorm ν := by rw [hρ]; linarith
    have hone : ‖χ ν‖ ≤ ∑' ν', if ρ < g * latticeSupNorm ν' then ‖χ ν'‖ else 0 := by
      have := (htail_summable ρ).le_tsum ν (fun j _ => by split_ifs <;> simp)
      simpa [hmem] using this
    have hdecay : ρ ^ 8 * ‖χ ν‖ ≤ C8 :=
      (mul_le_mul_of_nonneg_left hone (by positivity)).trans (hHχ ρ hρ1)
    -- `(1 + g² |ν|²)² ≤ (4 (g ‖ν‖∞)²)² = 256 ρ⁴`
    have hweight : 1 + g ^ 2 * latticeNormSq ν ≤ 16 * ρ ^ 2 := by
      have : g ^ 2 * latticeNormSq ν ≤ 3 * (g * latticeSupNorm ν) ^ 2 := by
        nlinarith [sq_nonneg g]
      have h2 : g * latticeSupNorm ν = 2 * ρ := by rw [hρ]; ring
      rw [h2] at this
      nlinarith
    have hweight2 : (1 + g ^ 2 * latticeNormSq ν) ^ 2 ≤ 256 * ρ ^ 4 := by
      have h0 : 0 ≤ 1 + g ^ 2 * latticeNormSq ν := by positivity
      calc (1 + g ^ 2 * latticeNormSq ν) ^ 2 ≤ (16 * ρ ^ 2) ^ 2 := pow_le_pow_left₀ h0 hweight 2
        _ = 256 * ρ ^ 4 := by ring
    -- `|ν|⁴ ≤ 9 ‖ν‖∞⁴ = 9 (2ρ/g)⁴`
    have hnpos : 0 < latticeNormSq ν := by
      have : 0 < latticeSupNorm ν := by
        by_contra h0
        push Not at h0
        have : latticeSupNorm ν = 0 := le_antisymm h0 hs
        rw [this, mul_zero] at hν
        linarith
      by_contra h0
      push Not at h0
      have hz : latticeNormSq ν = 0 := le_antisymm h0 hn
      have hc : ∀ j : Fin 3, ((ν j : ℤ) : ℝ) = 0 := by
        intro j
        have := lattice_coordinate_sq_le_latticeNormSq ν j
        rw [hz] at this
        exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
      have : latticeSupNorm ν = 0 := by
        unfold latticeSupNorm
        rw [hc 0, hc 1, hc 2]
        simp
      linarith
    have hq : latticeNormSq ν ^ 2 * g ^ 4 ≤ 144 * ρ ^ 4 := by
      have h2 : g * latticeSupNorm ν = 2 * ρ := by rw [hρ]; ring
      have h3 : (g ^ 2 * latticeNormSq ν) ≤ 3 * (2 * ρ) ^ 2 := by
        rw [← h2]
        nlinarith [sq_nonneg g]
      have h4 : (g ^ 2 * latticeNormSq ν) ^ 2 ≤ (3 * (2 * ρ) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h3 2
      nlinarith
    -- combine: `(1 + g²|ν|²)² |χ̂| ≤ 256 ρ⁴ · C₈/ρ⁸ = 256 C₈/ρ⁴ ≤ 36864 C₈/(g⁴ |ν|⁴)`
    have hχρ : ‖χ ν‖ ≤ C8 / ρ ^ 8 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hfinal : (1 + g ^ 2 * latticeNormSq ν) ^ 2 * ‖χ ν‖ ≤
        36864 * C8 / g ^ 4 * (1 / latticeNormSq ν ^ 2) := by
      calc (1 + g ^ 2 * latticeNormSq ν) ^ 2 * ‖χ ν‖ ≤ 256 * ρ ^ 4 * (C8 / ρ ^ 8) :=
            mul_le_mul hweight2 hχρ hχν (by positivity)
        _ = 256 * C8 / ρ ^ 4 := by field_simp
        _ ≤ 36864 * C8 / g ^ 4 * (1 / latticeNormSq ν ^ 2) := by
            rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
            have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 256 * C8)
            nlinarith
    linarith

/-- `(Hχ)` gives the fourth moment `D⁽⁴⁾_χ = Σ_ν |ν|⁴ |χ̂(ν)| < ∞` (decay at `M = 8`). -/
lemma summable_nsq_sq_of_HChi {g : ℝ} (hg : 0 < g) {c : Lattice3 → ℂ} {CM : ℕ → ℝ}
    (hc : HChi g c CM) : Summable fun x => nsq x ^ 2 * ‖c x‖ := by
  have hw := summable_weighted4_of_decay hc.1 hg (CM 8) (hc.2 8 (by norm_num))
  refine Summable.of_nonneg_of_le (fun x => mul_nonneg (sq_nonneg _) (norm_nonneg _))
    (fun x => ?_) (hw.mul_left (1 / g ^ 4))
  have hg4 : 0 < g ^ 4 := by positivity
  have hn := nsq_nonneg x
  have hcx := norm_nonneg (c x)
  rw [← nsq_eq_latticeNormSq x]
  have h1 : g ^ 4 * nsq x ^ 2 ≤ (1 + g ^ 2 * nsq x) ^ 2 := by
    have h0 : 0 ≤ g ^ 2 * nsq x := by positivity
    have h2 : (g ^ 2 * nsq x) ^ 2 ≤ (1 + g ^ 2 * nsq x) ^ 2 :=
      pow_le_pow_left₀ h0 (by linarith) 2
    calc g ^ 4 * nsq x ^ 2 = (g ^ 2 * nsq x) ^ 2 := by ring
      _ ≤ _ := h2
  calc nsq x ^ 2 * ‖c x‖ = 1 / g ^ 4 * (g ^ 4 * nsq x ^ 2 * ‖c x‖) := by
        rw [← mul_assoc, ← mul_assoc, one_div, inv_mul_cancel₀ hg4.ne', one_mul]
    _ ≤ 1 / g ^ 4 * ((1 + g ^ 2 * nsq x) ^ 2 * ‖c x‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hcx) (by positivity)

end Decay

/-! ## `thm:grid-dyn-sharp` in position space -/

section PositionTheorem

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **Observable error on the grid, position space, sharp** (`thm:grid-dyn-sharp`). The setting of
`grid_observable_position`, with in addition `D⁽⁴⁾_χ = Σ_ν |ν|⁴ |χ̂(ν)| < ∞`: for `m ≥ 8`, `K ≥ 8`
and `t ≥ 0`,
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤
  A₁ K^{-5} + A₂ t K^{-3} + A₃ K^{-5/2} τ_χ(K) + ‖ψ₀‖² τ_χ^∞(m)`
with `(A₁, A₂, A₃) = gridConstsSharp` at the canonical constants of the cell, independent of `K`
and `t`. -/
theorem grid_observable_position_sharp (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (ψ₀ h₀ h₁ : MolecularPositionL2 eta) (hψ₀ : HasCoulombHamiltonian sys L ψ₀ h₀)
    (hh₀ : HasCoulombHamiltonian sys L h₀ h₁)
    (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχ1 : Summable fun ν => ‖mFourierCoeff χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖mFourierCoeff χ ν‖)
    (hχ4 : Summable fun ν => nsq ν ^ 2 * ‖mFourierCoeff χ ν‖)
    (hreal : ∀ y, conj (χ y) = χ y) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridConstsSharp sys L molecularCanonicalUnitHardyConstant
        (molecularCanonicalLowConstant L)
      (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L) a
      (mFourierCoeff χ) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then ‖mFourierCoeff χ ν‖ else 0
    let ψg := posConj (Ug t) (idft (regCoeff m ((physMap eta).symm ψ₀)))
    ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a χ ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖ψ₀‖ ^ 2 * supTail (mFourierCoeff χ) m := by
  intro g K A τχ ψg
  have hPeriodic := canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨H, hKernel, -⟩ := exists_coulombFourierH2Operator sys L
      molecularCanonicalUnitHardyConstant
    hL hPeriodic
  have hiff := hasCoulombHamiltonian_iff_phys sys L hL H hKernel
  -- the propagator on the Fourier side
  set UF : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
    fun s => ((physMap eta).trans (U s)).trans (physMap eta).symm with hUFdef
  have hUF : ∀ s x, UF s x = (physMap eta).symm (U s (physMap eta x)) := fun s x => rfl
  have h0F : ∀ x, UF 0 x = x := by
    intro x
    rw [hUF, hU0, LinearIsometryEquiv.symm_apply_apply]
  have hgraphF : ∀ s u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        UF s (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = UF s (H u) := by
    intro s u
    obtain ⟨u', h1, h2⟩ := (hiff _ _).mp (hUgraph s _ _ ((hiff _ _).mpr ⟨u, rfl, rfl⟩))
    refine ⟨u', ?_, ?_⟩
    · rw [hUF, ← h1, LinearIsometryEquiv.symm_apply_apply]
    · rw [hUF, ← h2, LinearIsometryEquiv.symm_apply_apply]
  have hderivF : ∀ s u, HasDerivAt (fun r => UF r (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • UF s (H u))) s := by
    intro s u
    have h := hUderiv s _ _ ((hiff _ _).mpr ⟨u, rfl, rfl⟩)
    have h2 := (((physMap eta).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt s h
    simp only [ContinuousLinearMap.coe_restrictScalars'] at h2
    rw [map_neg, map_smul] at h2
    exact h2
  -- the initial state in `D(H²)`
  obtain ⟨u₀, hu₀1, hu₀2⟩ := (hiff ψ₀ h₀).mp hψ₀
  obtain ⟨v₀, hv₀1, hv₀2⟩ := (hiff h₀ h₁).mp hh₀
  have huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀ :=
    (physMap eta).injective (hu₀2.trans hv₀1.symm)
  have hx₀ : (physMap eta).symm ψ₀ = molecularH2StateMap eta (2 * Real.pi / L) u₀ := by
    rw [← hu₀1, LinearIsometryEquiv.symm_apply_apply]
  -- the continuum expectation on the Fourier side
  have hO : ∀ x, ⟪physMap eta x, mulCLM (regFun a χ) (physMap eta x)⟫_ℂ =
      ⟪x, convOp a (mFourierCoeff χ) x⟫_ℂ := by
    intro x
    rw [← physMap_mulCLM a hχ1 x, ← LinearIsometryEquiv.inner_map_map (physMap eta),
      LinearIsometryEquiv.apply_symm_apply]
  have hψt : U t ψ₀ = physMap eta (UF t (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    rw [hUF, LinearIsometryEquiv.apply_symm_apply, hu₀1]
  -- the grid expectation on the register
  have hdψ : dft ψg = Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    show dft (posConj (Ug t) (idft (regCoeff m ((physMap eta).symm ψ₀)))) = _
    rw [dft_posConj, dft_idft, hx₀]
  have hψg : ⟪ψg, posObs a χ ψg⟫_ℂ =
      ⟪Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)),
        gridObs a (mFourierCoeff χ) (Ug t
            (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)))⟫_ℂ := by
    rw [← inner_dft_dft ψg, dft_posObs a hχ1, hdψ]
  rw [hψt, hO, hψg]
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  have h := grid_observable_rate_sharp sys L H hKernel
      molecularCanonicalUnitHardyConstant hL hPeriodic
    (finiteCoulombPhysicalMassConstant_nonneg _ _ _) UF h0F hgraphF hderivF m hm hK hκ Ug hg0
    hgcomm hgderiv _ _ _ hBlow hCs hBker hLow hKernelScale hSobolev u₀ v₀ huv a (mFourierCoeff χ)
    hχ1 hχ2 hχ4 (fun ν => mFourierCoeff_neg_of_real hreal ν) ht
  dsimp only at h
  have e1 : ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ = ‖ψ₀‖ := by
    rw [← hu₀1, LinearIsometryEquiv.norm_map]
  have e2 : ‖H u₀‖ = ‖h₀‖ := by rw [← hu₀2, LinearIsometryEquiv.norm_map]
  have e3 : ‖molecularH2StateMap eta (2 * Real.pi / L) v₀‖ = ‖h₀‖ := by
    rw [← hv₀1, LinearIsometryEquiv.norm_map]
  have e4 : ‖H v₀‖ = ‖h₁‖ := by rw [← hv₀2, LinearIsometryEquiv.norm_map]
  rw [e1, e2, e3, e4] at h
  exact h

end PositionTheorem

/-! ## `(Hχ)` and the final form of `thm:grid-dyn-sharp` -/

section Final

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **`thm:grid-dyn-sharp`** (truncated-kernel grid method: energy-rate secular bound). For a
periodic Coulomb system there is a propagator `U` (`e^{-iHt}`) on `L²((T³)^η)` (unitary group,
strongly continuous, preserving the graph of the Hamiltonian, solving the Schrödinger equation on
it, and the only evolution that does), and for every register radius `2m` and every real, even
kernel `κ` of the class `𝒦_K` (`IsGridKernel`, `K = 2πm/L`) a grid propagator `U_g`
(`e^{-iH_pos t}` on the grid values, `n' = 4m + 1` points per direction), such that: for every
`ψ₀ ∈ D(H²)` (`H ψ₀ = h₀`, `H h₀ = h₁`), register `a` and real continuous `χ` satisfying `(Hχ)`,
with the constants `(A₁, A₂, A₃) = gridConstsSharp` at `(‖ψ₀‖, ‖h₀‖, ‖h₀‖, ‖h₁‖)`, which do not
depend on `m` or `t`: for `m ≥ 8`, `K ≥ 8` and `t ≥ 0`, the grid state
`ψ_g(t) = e^{-iH_pos t} P ψ₀` and the collocated observable `O_g = χ(x_{j_a})` satisfy
(`eq:grid-dyn-sharp` without the trivial `min {1, ·}`, which is `thm_grid_dyn_sharp_min`)
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤
  (A₁ + (A₃ 3^{5/2} + ‖ψ₀‖²) C_{χ,5}) K^{-5} + A₂ t K^{-3}`.
With `N = (2m+1)³`, `K^{-1} ≤ (3L/2π) N^{-1/3}` (`inv_K_le_basis`), so the bound is
`O(N^{-5/3} + t N^{-1})`: the energy-rate secular coefficient of the Galerkin method. The
fourth-derivative control `D_χ^{(4)}` of the manuscript enters through `D⁽⁴⁾_χ = Σ |ν|⁴ |χ̂(ν)|`,
which `(Hχ)` makes finite (`summable_nsq_sq_of_HChi`). -/
theorem thm_grid_dyn_sharp (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    ∃ U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, Continuous fun t => U t ψ) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasCoulombHamiltonian sys L (U t f) (U t h)) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) ∧
      (∀ φ ζ : ℝ → MolecularPositionL2 eta, (∀ t, HasCoulombHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
        (∀ x, Continuous fun t => Ug t x) ∧
        (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t x)) ∧
        (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
        ∀ ψ₀ h₀ h₁ : MolecularPositionL2 eta, HasCoulombHamiltonian sys L ψ₀ h₀ →
          HasCoulombHamiltonian sys L h₀ h₁ →
          ∀ (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (CM : ℕ → ℝ),
          HChi (2 * Real.pi / L) (mFourierCoeff χ) CM →
          (∀ y, conj (χ y) = χ y) →
          let A := gridConstsSharp sys L molecularCanonicalUnitHardyConstant
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) a (mFourierCoeff χ) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let ψg := Ug t (idft (regCoeff m ((physMap eta).symm ψ₀)))
            ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a χ ψg⟫_ℂ‖ ≤
              (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
                A.2.1 * t * (1 / K) ^ 3 := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, -, -⟩ := exists_coulombPropagator sys L hL
  refine ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, fun m κ hκ => ?_⟩
  obtain ⟨Ur, hr0, -, -, hrcomm, hrderiv, hp0, hpadd, hpcont, hpcomm, hpderiv⟩ :=
    exists_posPropagator (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) hκ.even
      (2 * Real.pi / L)
  refine ⟨fun t => posConj (Ur t), hp0, hpadd, hpcont, hpcomm, hpderiv, ?_⟩
  intro ψ₀ h₀ h₁ hψ₀ hh₀ a χ CM hc hreal A hm hK t ht K ψg
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hχ1 := hc.1
  have hχ2 := summable_nsq_of_HChi hg hc
  have hχ4 := summable_nsq_sq_of_HChi hg hc
  have h := grid_observable_position_sharp sys L hL U h0 hgraph hderiv m hm hK hκ Ur hr0 hrcomm
    hrderiv ψ₀ h₀ h₁ hψ₀ hh₀ a χ hχ1 hχ2 hχ4 hreal ht
  obtain ⟨hBlow, hCs, hBker, -⟩ := molecularCanonicalTailConstants_spec L hL
  have hA₃ : 0 ≤ A.2.2 :=
    gridConsts_nonneg_three sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) a (mFourierCoeff χ)
      (finiteCoulombPhysicalMassConstant_nonneg _ _ _)
      hBlow hCs hBker (norm_nonneg ψ₀) (norm_nonneg h₀) (norm_nonneg h₀) (norm_nonneg h₁)
  have hK' : (8 : ℝ) ≤ K := hK
  have hKpos : 0 < K := by linarith
  have hsqrt3 : Real.sqrt 3 ≤ K := by
    have : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    linarith
  have hC5 := CM_nonneg_of_HChi hc (M := 5) (by norm_num)
  have htail := tail_le_of_HChi hg hc (M := 5) (by norm_num) hsqrt3
  have hsup := supTail_le_of_HChi hg hc (M := 5) (by norm_num) (m := m) (by linarith)
  have hρ1 : Real.sqrt (1 / K) ^ 5 ≤ 1 := by
    have h1 : 1 / K ≤ 1 := by rw [div_le_one hKpos]; linarith
    have h2 : Real.sqrt (1 / K) ≤ 1 := by
      have := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_one] at this
    exact pow_le_one₀ (Real.sqrt_nonneg _) h2
  have hρ0 : 0 ≤ Real.sqrt (1 / K) ^ 5 := by positivity
  have hτ : A.2.2 * Real.sqrt (1 / K) ^ 5 *
      (∑' x, if K < (2 * Real.pi / L) * Real.sqrt (latticeNormSq x) then
        ‖mFourierCoeff χ x‖ else 0) ≤ A.2.2 * Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left htail (mul_nonneg hA₃ hρ0)
    have h2 : A.2.2 * Real.sqrt (1 / K) ^ 5 * (Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5) ≤
        A.2.2 * 1 * (Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ1 hA₃)
      positivity
    have e : A.2.2 * 1 * (Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5) =
        A.2.2 * Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5 := by ring
    linarith
  have hs : ‖ψ₀‖ ^ 2 * supTail (mFourierCoeff χ) m ≤ ‖ψ₀‖ ^ 2 * (CM 5 * (1 / K) ^ 5) :=
    mul_le_mul_of_nonneg_left hsup (by positivity)
  have e : (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
      A.2.1 * t * (1 / K) ^ 3 = A.1 * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3 +
        A.2.2 * Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5 + ‖ψ₀‖ ^ 2 * (CM 5 * (1 / K) ^ 5) := by ring
  rw [e]
  exact h.trans (by linarith)

/-- **`eq:grid-dyn-sharp` with the trivial bound** (`thm:grid-dyn-sharp`). Under the hypotheses
of `thm_grid_dyn_sharp`, for a `[0,1]`-valued `χ` and `‖ψ₀‖ = 1`,
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤ min {1, C [K^{-5} + t K^{-3}]}`, with
`C [K^{-5} + t K^{-3}]` the bound of `thm_grid_dyn_sharp`. -/
theorem thm_grid_dyn_sharp_min (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    ∃ U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, Continuous fun t => U t ψ) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasCoulombHamiltonian sys L (U t f) (U t h)) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) ∧
      (∀ φ ζ : ℝ → MolecularPositionL2 eta, (∀ t, HasCoulombHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
        (∀ x, Continuous fun t => Ug t x) ∧
        (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t x)) ∧
        (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
        ∀ ψ₀ h₀ h₁ : MolecularPositionL2 eta, HasCoulombHamiltonian sys L ψ₀ h₀ →
          HasCoulombHamiltonian sys L h₀ h₁ → ‖ψ₀‖ = 1 →
          ∀ (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (CM : ℕ → ℝ),
          HChi (2 * Real.pi / L) (mFourierCoeff χ) CM →
          (∀ y, (χ y).im = 0 ∧ 0 ≤ (χ y).re ∧ (χ y).re ≤ 1) →
          let A := gridConstsSharp sys L molecularCanonicalUnitHardyConstant
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) a (mFourierCoeff χ) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let ψg := Ug t (idft (regCoeff m ((physMap eta).symm ψ₀)))
            ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a χ ψg⟫_ℂ‖ ≤
              min 1 ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
                A.2.1 * t * (1 / K) ^ 3) := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, hrest⟩ := thm_grid_dyn_sharp sys L hL
  refine ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, fun m κ hκ => ?_⟩
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := hrest m κ hκ
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro ψ₀ h₀ h₁ hψ₀ hh₀ hnorm a χ CM hc hχ A hm hK t ht K ψg
  have hreal : ∀ y, conj (χ y) = χ y := fun y => by
    apply Complex.ext
    · simp
    · simp [(hχ y).1]
  have h := hbound ψ₀ h₀ h₁ hψ₀ hh₀ a χ CM hc hreal hm hK t ht
  refine le_min ?_ h
  -- both expectations lie in `[0, 1]`
  have h1 : InUnitSeg ⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ (‖U t ψ₀‖ ^ 2) :=
    inner_mulCLM_mem (regFun a χ) (regFun_mem a χ hχ) (U t ψ₀)
  have h2 : InUnitSeg ⟪ψg, posObs a χ ψg⟫_ℂ (‖ψg‖ ^ 2) := inner_posObs_mem a χ hχ ψg
  have hUt : ‖U t ψ₀‖ ^ 2 ≤ 1 := by rw [LinearIsometryEquiv.norm_map, hnorm]; norm_num
  have hψg : ‖ψg‖ ^ 2 ≤ 1 := by
    have e : ‖ψg‖ = ‖regCoeff m ((physMap eta).symm ψ₀)‖ := by
      show ‖Ug t (idft (regCoeff m ((physMap eta).symm ψ₀)))‖ = _
      rw [LinearIsometryEquiv.norm_map, ← dftLIE_symm_apply, LinearIsometryEquiv.norm_map]
    have h3 : ‖regCoeff m ((physMap eta).symm ψ₀)‖ ≤ 1 := by
      refine (norm_regCoeff_le _).trans ?_
      rw [LinearIsometryEquiv.norm_map, hnorm]
    rw [e]
    have h4 := norm_nonneg (regCoeff m ((physMap eta).symm ψ₀))
    nlinarith
  exact norm_sub_le_of_inUnitSeg h1 h2 hUt hψg

end Final

end

end PlaneWaveGridDynamics

end DevGS6
-- END SOURCE dev/DevGS6.lean

/-! ════════════════════════════════════════════════════════════════════
## Part `KineticGrid`
════════════════════════════════════════════════════════════════════ -/

/-!
The kinetic energy under the grid evolution: `prop:mult-grid`, `lem:grid-tails`, and the grid forms
of `thm:mult-cap`, `cor:stopping` and `cor:stopping2` (namespace `PlaneWaveKinetic`; former
development files `dev/DevK7.lean` to `dev/DevK12.lean`).
-/

-- BEGIN SOURCE dev/DevK7.lean
-- SHA256 ca95731096c8eb9ae10d95df3d0fdc750635d04627b0a074ce1d90d0d26f5913
section DevK7

/-!
# Kinetic-energy observable under the grid evolution: `prop:mult-grid`

On the register of radius `2m` (`K = g m`, kernel of the class `𝒦_K`) the kinetic energy `A_r`
of a particle is applied exactly, as the diagonal multiplier `regKinSym` in the momentum basis of
the register (in position space: through the DFT). Its expectation in a register vector is
`regExpect`. With `a(t) = P ψ(t)` (register coordinates) and `ψ_g(t) = e^{-iH_grid t} P ψ₀`:

* (I) the projection term at cutoff `2K`: `⟨ψ, A_r ψ⟩ - ⟨P ψ, A_r P ψ⟩ = ⟨δ, A_r δ⟩` is one-signed
  and at most `(η t₂)(η B₂)` (`lem:mult-basic` at `2K`); on the cube, `⟨P ψ, A_r P ψ⟩` is the
  register expectation of `a(t)` (`expect_truncate_eq_reg`), so there is no collocation term;
* (III) `⟨a, A_r a⟩ - ⟨ψ_g, A_r ψ_g⟩ = Re⟪a - ψ_g, A_r a⟫ + Re⟪a - ψ_g, A_r ψ_g⟫`
  (`regExpect_sub_le`), each pairing bounded by duality against the backward grid flow of
  `A_r v` (`grid_duality`). Its regularity: `‖W A_r v‖ ≤ (g²/2) X(v)` (`norm_wM_regKin_le`) with
  the second moments `X(v) ≤ r F`, `r = (4m+1)^{3/2}`, of `lem:grid-data2`
  (`second_moment_regCoeff_le` for `P ψ(t)`, `norm_wM_sq_gridFlow_le` for `ψ_g(t)`), so the flow
  budget is `W = O(K^{3/2})` and the a priori shell `m̄ W/(⌊m/4⌋+1)² = O(K^{-1/2})`.

`grid_kinetic_error` is the explicit bound; its rate `O(K^{-3} + t K^{-1})` is derived in DevK8.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate lp ENNReal Topology
open Filter Set

namespace PlaneWaveKinetic

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The kinetic energy on the register -/

section Register

variable (sys : CoulombSystem eta ν) (g : ℝ) {m : ℕ}

/-- The kinetic energy `A_r` on the register, in its momentum basis: the symbol
`|g gl(q_r)|²/(2 m_r)` of `A_r` at the lattice point `liftCfg q` of the register configuration. -/
noncomputable def regKinSym (r : Fin eta) (q : RCfg eta m) : ℝ := regSymbol sys g r (liftCfg q)

omit [Fintype ν] in
lemma regKinSym_nonneg (r : Fin eta) (q : RCfg eta m) : 0 ≤ regKinSym sys g r q :=
  regSymbol_nonneg sys g r _

/-- The expectation `⟨x, A_r x⟩ = Σ_q A_r(q) |x_q|²` of the kinetic energy in a register vector. -/
noncomputable def regExpect (r : Fin eta) (x : EuclideanSpace ℂ (RCfg eta m)) : ℝ :=
  ∑ q, regKinSym sys g r q * ‖x q‖ ^ 2

omit [Fintype ν] in
lemma regExpect_nonneg (r : Fin eta) (x : EuclideanSpace ℂ (RCfg eta m)) :
    0 ≤ regExpect sys g r x :=
  Finset.sum_nonneg fun q _ => mul_nonneg (regKinSym_nonneg sys g r q) (sq_nonneg _)

lemma inner_wMul_self {ι : Type*} [Fintype ι] (w : ι → ℝ) (x : EuclideanSpace ℂ ι) :
    ⟪x, wMul w x⟫_ℂ = ((∑ q, w q * ‖x q‖ ^ 2 : ℝ) : ℂ) := by
  rw [PiLp.inner_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [wMul_apply, RCLike.inner_apply, mul_comm, conj_mul_ofReal_mul]

lemma inner_wMul_symm {ι : Type*} [Fintype ι] (w : ι → ℝ) (x y : EuclideanSpace ℂ ι) :
    ⟪wMul w x, y⟫_ℂ = ⟪x, wMul w y⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [wMul_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

omit [Fintype ν] in
/-- **The register difference as two pairings**: for register vectors `a`, `b`,
`|⟨a, A_r a⟩ - ⟨b, A_r b⟩| ≤ ‖⟪a - b, A_r a⟫‖ + ‖⟪a - b, A_r b⟫‖`. -/
lemma regExpect_sub_le (r : Fin eta) (a b : EuclideanSpace ℂ (RCfg eta m)) :
    |regExpect sys g r a - regExpect sys g r b| ≤
      ‖⟪a - b, wMul (regKinSym sys g r) a⟫_ℂ‖ + ‖⟪a - b, wMul (regKinSym sys g r) b⟫_ℂ‖ := by
  set O := wMul (regKinSym (m := m) sys g r)
  have h1 : ⟪a, O a⟫_ℂ - ⟪b, O b⟫_ℂ = ⟪a - b, O a⟫_ℂ + ⟪b, O (a - b)⟫_ℂ := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  have h2 : ‖⟪b, O (a - b)⟫_ℂ‖ = ‖⟪a - b, O b⟫_ℂ‖ := by
    rw [← inner_wMul_symm, ← inner_conj_symm, RCLike.norm_conj]
  have hE : ((regExpect sys g r a - regExpect sys g r b : ℝ) : ℂ) = ⟪a, O a⟫_ℂ - ⟪b, O b⟫_ℂ := by
    rw [Complex.ofReal_sub, regExpect, regExpect, inner_wMul_self, inner_wMul_self]
  have h3 := congrArg norm hE
  rw [Complex.norm_real, Real.norm_eq_abs] at h3
  rw [h3, h1]
  exact (norm_add_le _ _).trans (le_of_eq (by rw [h2]))

omit [Fintype ν] in
/-- The kinetic energy commutes with the register coefficients:
`P A_r u = A_r (P S u)` on the register. -/
lemma regCoeff_h2_regKin (r : Fin eta) (u : MolecularFourierH2 eta) :
    regCoeff m ((regKin sys g r).h2 u) =
      wMul (regKinSym sys g r) (regCoeff m (molecularH2StateMap eta g u)) := by
  ext q
  rw [regCoeff_apply, KinMult.h2_apply, wMul_apply, regCoeff_apply, molecularH2StateMap_apply]
  rfl

omit [Fintype ν] in
/-- **No collocation term**: on the cube of radius `2m` the expectation of `A_r` is the register
expectation of the register coefficients. -/
lemma expect_truncate_eq_reg (r : Fin eta) (u : MolecularFourierH2 eta) :
    (regKin sys g r).expect (molecularH2StateMap eta g (molecularH2Truncate (2 * m) u)) =
      regExpect sys g r (regCoeff m (molecularH2StateMap eta g u)) := by
  apply Complex.ofReal_injective
  rw [← (regKin sys g r).inner_stateMap_h2_self, regExpect, ← inner_wMul_self,
    stateMap_truncate, (regKin sys g r).h2_truncate,
    inner_regCoeff (m := m) _ _ (truncate_truncate' _), regCoeff_truncate, regCoeff_truncate,
    regCoeff_h2_regKin]

omit [Fintype ν] in
lemma regKinSym_le (r : Fin eta) (q : RCfg eta m) :
    regKinSym sys g r q ≤ g ^ 2 / 2 * (wM (regParticlesOf sys) q - 1) := by
  have h1 : nsq (gl (q r)) / sys.mass r ≤ ∑ a, nsq (gl (q a)) / (regParticlesOf sys).mass a :=
    Finset.single_le_sum (f := fun a => nsq (gl (q a)) / (regParticlesOf sys).mass a)
      (fun a _ => div_nonneg (nsq_nonneg _) ((regParticlesOf sys).mass_pos a).le)
      (Finset.mem_univ r)
  have e : regKinSym sys g r q = g ^ 2 / 2 * (nsq (gl (q r)) / sys.mass r) := by
    unfold regKinSym regSymbol
    have : latticeNormSq (liftCfg q r) = nsq (gl (q r)) := rfl
    rw [this]
    ring
  have e2 : wM (regParticlesOf sys) q - 1 = ∑ a, nsq (gl (q a)) / (regParticlesOf sys).mass a := by
    unfold wM
    ring
  rw [e, e2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

omit [Fintype ν] in
/-- `‖A_r v‖ ≤ (g²/2) ‖W v‖` on the register. -/
lemma norm_regKin_le (r : Fin eta) (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (regKinSym sys g r) v‖ ≤ g ^ 2 / 2 * ‖wMul (wM (regParticlesOf sys)) v‖ := by
  have hc : (0 : ℝ) ≤ g ^ 2 / 2 := by positivity
  refine (norm_le_of_pointwise (Y := ((g ^ 2 / 2 : ℝ) : ℂ) • wMul (wM (regParticlesOf sys)) v)
    fun q => ?_).trans ?_
  · rw [wMul_apply, PiLp.smul_apply, smul_eq_mul, wMul_apply, norm_mul, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (regKinSym_nonneg sys g r q), Real.norm_of_nonneg hc,
      Real.norm_of_nonneg (le_trans zero_le_one (wM_ge_one _ q)), ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have := regKinSym_le sys g r q
    nlinarith
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]

omit [Fintype ν] in
/-- `‖W A_r v‖ ≤ (g²/2) ‖W² v‖` on the register: the regularity of the smeared state is that of
the second kinetic moment. -/
lemma norm_wM_regKin_le (r : Fin eta) (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys g r) v)‖ ≤
      g ^ 2 / 2 * ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) v)‖ := by
  have hc : (0 : ℝ) ≤ g ^ 2 / 2 := by positivity
  refine (norm_le_of_pointwise (Y := ((g ^ 2 / 2 : ℝ) : ℂ) •
    wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) v)) fun q => ?_).trans ?_
  · have hW := le_trans zero_le_one (wM_ge_one (regParticlesOf sys) q)
    rw [wMul_apply, wMul_apply, PiLp.smul_apply, smul_eq_mul, wMul_apply, wMul_apply, norm_mul,
      norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (regKinSym_nonneg sys g r q),
      Real.norm_of_nonneg hc, Real.norm_of_nonneg hW]
    have h1 := regKinSym_le sys g r q
    have h2 : regKinSym sys g r q ≤ g ^ 2 / 2 * wM (regParticlesOf sys) q := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hW
    have h4 := mul_le_mul_of_nonneg_right h3 (norm_nonneg (v q))
    calc wM (regParticlesOf sys) q * (regKinSym sys g r q * ‖v q‖)
        = wM (regParticlesOf sys) q * regKinSym sys g r q * ‖v q‖ := by ring
      _ ≤ wM (regParticlesOf sys) q * (g ^ 2 / 2 * wM (regParticlesOf sys) q) * ‖v q‖ := h4
      _ = g ^ 2 / 2 * (wM (regParticlesOf sys) q * (wM (regParticlesOf sys) q * ‖v q‖)) := by
          ring
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]

end Register

/-! ## The explicit bound -/

section Grid

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **The kinetic energy under the grid evolution** (`prop:mult-grid`, Fourier side, explicit
form). For `ψ₀ = S u₀ ∈ D(H²)` (`H u₀ = S v₀`), the exact state `ψ(t) = U t ψ₀`, the grid state
`ψ_g(t) = e^{-iH_grid t} P ψ₀` on the register of radius `2m` (`m ≥ 8`, `K = g m`, a real, even
kernel of the class `𝒦_K`), and a particle `r`,
`|⟨ψ(t), A_r ψ(t)⟩ - ⟨ψ_g(t), A_r ψ_g(t)⟩| ≤ (η t₂)(η B₂) + 2 t B_d`: the projection term at
`2K` (`t₂`, `B₂` the state and kinetic tails of `ψ(t)` at `2K`), plus the two pairings of
`grid_duality` with the flow budget `W = (5/3)(g²/2) r F + c_J (g²/2) X_b`, where
`r = (4m+1)^{3/2}`, `F = flow2(σ; ξ, X_a, ‖ψ₀‖)` bounds the second moments `X(v)/r` of
`v ∈ {P ψ(t), ψ_g(t)}` and `X_b = (5/3) X_a + c_J ‖ψ₀‖` their weights. -/
theorem grid_kinetic_error (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ} (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (rho₂ rho₄ Blow Cs Bker : ℝ) (hK₄ : 1 ≤ (2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ))
    (hRho₂ : 0 ≤ rho₂) (hRhoScale₂ : rho₂ ^ 2 * ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) = 1)
    (hRho₄ : 0 ≤ rho₄) (hRhoScale₄ : rho₄ ^ 2 * ((2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ)) = 1)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (r : Fin eta) (k₀ : ℕ) (hk₀ : 2 ≤ k₀) (hk₀g : 1 ≤ (2 * Real.pi / L) * k₀) {t : ℝ}
    (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB sys L Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
    let tl : ℝ → ℝ → ℝ := fun K ρ =>
      (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    let s₀ : ℕ := m / 4
    let Zg : ℝ :=
      Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
    let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
    let cJ : ℝ := gridFlowConst sys L
    let Xb : ℝ := 5 / 3 * Xa + cJ * S0
    let Q : ℝ := (k₀ : ℝ) ^ 4 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 / g ^ 4 + 30 * Ct M₀ ^ 2 / g
    let rr : ℝ := Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3
    let cH : ℝ := 26 * coulombGridCoupling sys L * (J0g (coulombGridCoupling sys L) g : ℝ)
    let σ : ℝ := Zg * (52 * (J0g (sys.maxMass * Zg) g : ℝ) + 4 * Real.sqrt 53 * sys.maxMass)
    let ξ : ℝ := S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * Real.sqrt Q)
    let F : ℝ := flow2 g cJ cH σ ξ Xa S0
    let W : ℝ := 5 / 3 * (g ^ 2 / 2 * (rr * F)) + cJ * (g ^ 2 / 2 * Xb)
    let τφ : ℝ := sys.maxMass * W / ((s₀ : ℝ) + 1) ^ 2
    let K₂ : ℝ := g * ((2 * m : ℕ) : ℝ)
    let B₂ : ℝ := (2 * sys.maxMass / K₂ ^ 2) * Ξ₁ + Ct M₀ * rho₂
    let t₂ : ℝ := tl K₂ rho₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) rho₄
    let Bd : ℝ := (eta * t₂) * (eta * (Ct ((1 + g ^ 2) * (sys.maxMass * W)) * rho₂)) +
      Zg * (formA s₀ m * (t₄ * (sys.maxMass * W) + τφ * Xa) + 52 * m * (τφ * t₄))
    let ψg := Ug t (regCoeff m (molecularH2StateMap eta g u₀))
    |(regKin sys g r).expect (U t (molecularH2StateMap eta g u₀)) - regExpect sys g r ψg| ≤
      (eta * t₂) * (eta * B₂) + 2 * (Bd * t) := by
  intro g b S0 Ξ₀ Ξ₁ M₀ Ct tl s₀ Zg Xa cJ Xb Q rr cH σ ξ F W τφ K₂ B₂ t₂ t₄ Bd ψg
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ b := relB_nonneg sys L Hunit hC
  have hg : 0 < g := by positivity
  have hs₀m : s₀ ≤ m := Nat.div_le_self m 4
  have hs₀mr : (s₀ : ℝ) ≤ m := by exact_mod_cast hs₀m
  have hK₁ : 1 ≤ g * (m : ℝ) :=
    (show 1 ≤ g * (s₀ : ℝ) from hK₄).trans (mul_le_mul_of_nonneg_left hs₀mr hg.le)
  have hs₀2 : (2 : ℝ) ≤ s₀ := by
    have : 2 ≤ s₀ := by show 2 ≤ m / 4; omega
    exact_mod_cast this
  have hK₁2g : 2 * g ≤ g * (m : ℝ) := by
    have := mul_le_mul_of_nonneg_left hs₀mr hg.le
    nlinarith
  have hm2m : (m : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by push_cast; linarith
  have hK₂ : 1 ≤ K₂ := hK₁.trans (mul_le_mul_of_nonneg_left hm2m hg.le)
  have hK₂2g : 2 * g ≤ K₂ := hK₁2g.trans (mul_le_mul_of_nonneg_left hm2m hg.le)
  have hS0 : 0 ≤ S0 := norm_nonneg _
  have hΞ₀ : 0 ≤ Ξ₀ := add_nonneg (mul_nonneg zero_le_two (norm_nonneg _))
    (mul_nonneg (mul_nonneg zero_le_two hb) hS0)
  have hM₀ : 0 ≤ M₀ := mul_nonneg (by linarith) (add_nonneg hS0 (mul_nonneg zero_le_two hΞ₀))
  have hcJ : 0 ≤ cJ := gridFlowConst_nonneg sys hL
  have hXa : 0 ≤ Xa := mul_nonneg (by positivity) hM₀
  have hg2 : (0 : ℝ) ≤ g ^ 2 / 2 := by positivity
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
    have h := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u
    rw [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
    exact h
  have hu₀_le : ‖u₀‖ ≤ M₀ :=
    hnorm_le u₀ rfl (kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u₀)
  -- (I): the projection term at cutoff `2K`
  have htl := fun c => tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph c K₂ rho₂ Blow
    Cs Bker hK₂ hRho₂ hRhoScale₂ hBlow hCs hBker hK₂2g hAmplitude hBkerScale hCsScale u₀ v₀ huv t
    u hu1 hu2
  have hδS : ‖molecularH2StateMap eta g u -
      molecularH2Truncate (2 * m) (molecularH2StateMap eta g u)‖ ≤ eta * t₂ := by
    refine (norm_sub_truncate_le hg (2 * m) _).trans ?_
    calc ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖
        ≤ ∑ _c : Fin eta, t₂ := Finset.sum_le_sum fun c _ => (htl c).2
      _ = eta * t₂ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hδT : ‖coulombFourierKineticH2 sys g u -
      molecularH2Truncate (2 * m) (coulombFourierKineticH2 sys g u)‖ ≤ eta * B₂ := by
    refine (norm_sub_truncate_le hg (2 * m) _).trans ?_
    calc ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (coulombFourierKineticH2 sys g u)‖
        ≤ ∑ _c : Fin eta, B₂ := Finset.sum_le_sum fun c _ => (htl c).1
      _ = eta * B₂ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have ht₂0 : 0 ≤ eta * t₂ := (norm_nonneg _).trans hδS
  have hI : (regKin sys g r).expect (molecularH2StateMap eta g (u - molecularH2Truncate (2 * m) u))
      ≤ (eta * t₂) * (eta * B₂) :=
    ((regKin sys g r).expect_tail_le (2 * m) u).trans
      (mul_le_mul hδS hδT (norm_nonneg _) ht₂0)
  have hI0 := (regKin sys g r).expect_tail_nonneg (2 * m) u
  -- (III): the in-band error, by duality against the backward grid flows of `A_r v`
  set a := regCoeff m (molecularH2StateMap eta g u) with hadef
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hZg : 0 ≤ Zg := Zc_nonneg hγ
  have hr : 1 ≤ rr := one_le_sqrt_pow_three m
  have hr0 : 0 ≤ rr := by linarith
  have hσ0 : 0 ≤ σ := mul_nonneg hZg (by positivity)
  have hcH : 0 ≤ cH :=
    mul_nonneg (mul_nonneg (by norm_num) (coulombGridCoupling_nonneg sys L hL)) (Nat.cast_nonneg _)
  have hsc : secondConst (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) g m ≤ σ * rr :=
    secondConst_le (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData hγ g m
  have hX2 : ∀ (s : ℝ) (x : MolecularFourierH2 eta),
      molecularH2StateMap eta g x = U s (molecularH2StateMap eta g u₀) → H x = U s (H u₀) →
      ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys))
        (regCoeff m (molecularH2StateMap eta g x)))‖ ≤ ξ * rr := by
    intro s x hx1 hx2
    have h : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys))
        (regCoeff m (molecularH2StateMap eta g x)))‖ ≤
        S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * (Real.sqrt Q * rr)) :=
      second_moment_regCoeff_le sys L H hKernel Hunit hL hPeriodic hC U hgraph m Blow Cs Bker hBlow
        hCs hBker hAmplitude hBkerScale hCsScale u₀ v₀ huv s x hx1 hx2 k₀ hk₀ hk₀g
    refine h.trans ?_
    have h1 : S0 ≤ S0 * rr := le_mul_of_one_le_right hS0 hr
    have h2 : 4 / g ^ 2 * Ξ₀ ≤ 4 / g ^ 2 * Ξ₀ * rr :=
      le_mul_of_one_le_right (mul_nonneg (by positivity) hΞ₀) hr
    have e : (S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * Real.sqrt Q)) * rr =
        S0 * rr + 4 / g ^ 2 * Ξ₀ * rr + 2 / g ^ 2 * (eta * (Real.sqrt Q * rr)) := by ring
    show _ ≤ (S0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * Real.sqrt Q)) * rr
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
  -- the second moments and weights of `a(t)` and `ψ_g(t)`
  have hXaT : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) a)‖ ≤ rr * F :=
    ((hX2 t u hu1 hu2).trans (mul_le_mul_of_nonneg_right hξF hr0)).trans_eq (mul_comm _ _)
  have ha₀ : ‖wMul (wM (regParticlesOf sys)) (regCoeff m (molecularH2StateMap eta g u₀))‖ ≤ Xa :=
    (norm_wM_le_wTot (regParticlesOf sys) _).trans ((norm_wTot_regCoeff_stateMap_le hg u₀).trans
      (mul_le_mul_of_nonneg_left hu₀_le (by positivity)))
  have haS₀ : ‖regCoeff m (molecularH2StateMap eta g u₀)‖ ≤ S0 := norm_regCoeff_le _
  have haT : ‖wMul (wM (regParticlesOf sys)) a‖ ≤ Xb := by
    have h : ‖wMul (wM (regParticlesOf sys)) a‖ ≤ Xa :=
      (norm_wM_le_wTot (regParticlesOf sys) _).trans ((norm_wTot_regCoeff_stateMap_le hg u).trans
        (mul_le_mul_of_nonneg_left hu_le (by positivity)))
    show _ ≤ 5 / 3 * Xa + cJ * S0
    have : 0 ≤ cJ * S0 := mul_nonneg hcJ hS0
    linarith
  have hbT : ‖wMul (wM (regParticlesOf sys)) ψg‖ ≤ Xb := by
    refine (norm_wM_gridFlow_le sys hL hκ.bound (Ug t) (hgcomm t) _).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left ha₀ (by norm_num))
      (mul_le_mul_of_nonneg_left haS₀ hcJ)
  have hXbT : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) ψg)‖ ≤ rr * F := by
    have h0' := hX2 0 u₀ (h0 _).symm (h0 _).symm
    have h := norm_wM_sq_gridFlow_le sys hL hκ.bound hκ.support (Ug t) (hgcomm t) _ h0' ha₀ haS₀
    exact h.trans (flow2_le_mul hcJ hcH hXa hS0 hr hsc le_rfl)
  -- the flow budget of the smeared states
  have hWv : ∀ v : EuclideanSpace ℂ (RCfg eta m),
      ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) v)‖ ≤ rr * F →
      ‖wMul (wM (regParticlesOf sys)) v‖ ≤ Xb →
      ∀ τ, ‖wMul (wM (regParticlesOf sys)) (Ug τ (wMul (regKinSym sys g r) v))‖ ≤ W := by
    intro v hXv hYv τ
    refine (norm_wM_gridFlow_le sys hL hκ.bound (Ug τ) (hgcomm τ) _).trans ?_
    have h1 := (norm_wM_regKin_le sys g r v).trans (mul_le_mul_of_nonneg_left hXv hg2)
    have h2 := (norm_regKin_le sys g r v).trans (mul_le_mul_of_nonneg_left hYv hg2)
    exact add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
      (mul_le_mul_of_nonneg_left h2 hcJ)
  have he : a - ψg = regCoeff m (U t (molecularH2StateMap eta g u₀)) -
      Ug t (regCoeff m (molecularH2StateMap eta g u₀)) := by
    rw [hψ]
  have hd1 : ‖⟪a - ψg, wMul (regKinSym sys g r) a⟫_ℂ‖ ≤ Bd * t := by
    have h := grid_duality sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph hderiv m hm hκ Ug hg0
      hgcomm hgderiv rho₂ rho₄ Blow Cs Bker hK₄ hRho₂ hRhoScale₂ hRho₄ hRhoScale₄ hBlow hCs hBker
      hAmplitude hBkerScale hCsScale u₀ v₀ huv _ W (hWv a hXaT haT) ht
    rw [he]
    exact h
  have hd2 : ‖⟪a - ψg, wMul (regKinSym sys g r) ψg⟫_ℂ‖ ≤ Bd * t := by
    have h := grid_duality sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph hderiv m hm hκ Ug hg0
      hgcomm hgderiv rho₂ rho₄ Blow Cs Bker hK₄ hRho₂ hRhoScale₂ hRho₄ hRhoScale₄ hBlow hCs hBker
      hAmplitude hBkerScale hCsScale u₀ v₀ huv _ W (hWv ψg hXbT hbT) ht
    rw [he]
    exact h
  have hIII : |regExpect sys g r a - regExpect sys g r ψg| ≤ 2 * (Bd * t) :=
    (regExpect_sub_le sys g r a ψg).trans ((add_le_add hd1 hd2).trans_eq (by ring))
  -- assembly
  have hsplit := (regKin sys g r).expect_split (2 * m) u
  rw [expect_truncate_eq_reg sys g r u] at hsplit
  rw [hψ, hsplit]
  have e : regExpect sys g r a +
      (regKin sys g r).expect (molecularH2StateMap eta g (u - molecularH2Truncate (2 * m) u)) -
        regExpect sys g r ψg =
      (regKin sys g r).expect (molecularH2StateMap eta g (u - molecularH2Truncate (2 * m) u)) +
        (regExpect sys g r a - regExpect sys g r ψg) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg hI0]
  exact add_le_add hI hIII

end Grid

end PlaneWaveKinetic

end DevK7
-- END SOURCE dev/DevK7.lean

-- BEGIN SOURCE dev/DevK8.lean
-- SHA256 766778dabfd8299050136c203f8b26c12a3f1bf60fa80547831b53846084eb18
section DevK8

/-!
# `prop:mult-grid` and `cor:stopping` (grid route): rates, position space, propagators

With `ρ = K^{-1/2}` (`K = g m`), the explicit bound of `grid_kinetic_error` is at most
`A₁ K^{-3} + A₂ t K^{-1}` (`kin_grid_rate_arith`, `grid_kinetic_rate`): the projection term at
`2K` is `O(ρ⁶)`; the pairings are `rate_arith_III` of `prop:grid-dyn` with the flow budget
`W ≤ (4m+1)^{3/2} W₁`, which is linear in the bound (`Ct` is linear), and
`(4m+1)^{3/2} ρ³ ≤ (5/g)^{3/2}` (`rr_rho_le`), so `W ρ⁵ = O(ρ²) = O(K^{-1})`.

In position space the kinetic energy on the grid is applied through the DFT (`posKinExpect`,
`⟨ψ, dft⁻¹ A_r dft ψ⟩`), which is the register expectation of the DFT of the grid values
(`grid_kinetic_position`, and `thm_mult_grid` with its propagators). The secant-slope estimator of
the stopping power then deviates by at most `(A₂ K^{-1} + 2 A₁ K^{-3}/T)/v_p` (`stopping_grid`,
`cor:stopping`, grid route).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate lp ENNReal Topology
open Filter Set

namespace PlaneWaveKinetic

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Arithmetic -/

section Arith

/-- `(4m+1)^{3/2} ρ³ ≤ (5/g)^{3/2}` when `ρ² g m = 1` and `m ≥ 1`. -/
lemma rr_rho_le {g ρ : ℝ} {m : ℕ} (hg : 0 < g) (hρ : 0 ≤ ρ) (hm : 1 ≤ m)
    (hρK : ρ ^ 2 * (g * (m : ℝ)) = 1) :
    Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 * ρ ^ 3 ≤ Real.sqrt (5 / g) ^ 3 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have e : Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 * ρ ^ 3 =
      Real.sqrt ((((4 * m : ℕ) : ℝ) + 1) * ρ ^ 2) ^ 3 := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hρ, mul_pow]
  rw [e]
  apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ hg]
  have hgρ : 0 ≤ ρ ^ 2 * g := mul_nonneg (sq_nonneg ρ) hg.le
  have h1 : ρ ^ 2 * g ≤ 1 := by
    calc ρ ^ 2 * g = ρ ^ 2 * g * 1 := (mul_one _).symm
      _ ≤ ρ ^ 2 * g * m := mul_le_mul_of_nonneg_left hm1 hgρ
      _ = 1 := by rw [← hρK]; ring
  have e : ((((4 * m : ℕ) : ℝ) + 1) * ρ ^ 2) * g = 4 * (ρ ^ 2 * (g * (m : ℝ))) + ρ ^ 2 * g := by
    push_cast
    ring
  rw [e, hρK]
  linarith

/-- **The rates of `prop:mult-grid`.** The explicit bound of `grid_kinetic_error`, at
`ρ₂ = (2K)^{-1/2}`, `ρ₄ = (g⌊m/4⌋)^{-1/2}`, for a flow budget `W ≤ (4m+1)^{3/2} W₁` and a linear
tail constant `Ct M = M C₁`, is at most `A₁ K^{-3} + A₂ t K^{-1}` for `m ≥ 8` and `K = g m ≥ 8`. -/
lemma kin_grid_rate_arith {η mm Ξ₁ C₀ C1 g t Zg Xa W W₁ : ℝ} {m : ℕ} {Ct : ℝ → ℝ}
    (hη : 0 ≤ η) (hmm : 1 ≤ mm) (hΞ₁ : 0 ≤ Ξ₁) (hC₀ : 0 ≤ C₀) (hg : 0 < g) (hm : 8 ≤ m)
    (hK : 8 ≤ g * m) (ht : 0 ≤ t) (hZg : 0 ≤ Zg) (hXa : 0 ≤ Xa) (hW : 0 ≤ W)
    (hWr : W ≤ Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 * W₁) (hCt : ∀ M, Ct M = M * C1)
    (hC1 : 0 ≤ C1) :
    let K : ℝ := g * m
    let tl : ℝ → ℝ → ℝ := fun K ρ => (2 * mm / K ^ 2) * ((2 * mm / K ^ 2) * Ξ₁ + C₀ * ρ)
    let ρ₂ : ℝ := Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))
    let ρ₄ : ℝ := Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))
    let s₀ : ℕ := m / 4
    let τφ : ℝ := mm * W / ((s₀ : ℝ) + 1) ^ 2
    let K₂ : ℝ := g * ((2 * m : ℕ) : ℝ)
    let B₂ : ℝ := (2 * mm / K₂ ^ 2) * Ξ₁ + C₀ * ρ₂
    let t₂ : ℝ := tl K₂ ρ₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) ρ₄
    let Bd : ℝ := (η * t₂) * (η * (Ct ((1 + g ^ 2) * (mm * W)) * ρ₂)) +
      Zg * (formA s₀ m * (t₄ * (mm * W) + τφ * Xa) + 52 * m * (τφ * t₄))
    let τ₁ : ℝ := 2 * mm * (2 * mm * Ξ₁ + C₀)
    let β₄ : ℝ := 128 * mm * (128 * mm * Ξ₁ + 8 * C₀)
    let cF : ℝ := 4 * Real.sqrt (5512 * g)
    let Γ : ℝ := η * (η * τ₁) * ((1 + g ^ 2) * C1) +
      Zg * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)
    (η * t₂) * (η * B₂) + 2 * (Bd * t) ≤
      (η ^ 2 * τ₁ * (2 * mm * Ξ₁ + C₀)) * (1 / K) ^ 3 +
        (2 * mm * W₁ * Γ * Real.sqrt (5 / g) ^ 3) * t * (1 / K) := by
  intro K tl ρ₂ ρ₄ s₀ τφ K₂ B₂ t₂ t₄ Bd τ₁ β₄ cF Γ
  set ρ := Real.sqrt (1 / K) with hρdef
  have hmm0 : 0 ≤ mm := by linarith
  have hKpos : 0 < K := by show 0 < g * (m : ℝ); linarith
  have hK1 : 1 ≤ K := by show 1 ≤ g * (m : ℝ); linarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = 1 / K := Real.sq_sqrt (one_div_nonneg.mpr hKpos.le)
  have hρK : ρ ^ 2 * K = 1 := by rw [hρ2]; field_simp
  have hρ1 : ρ ≤ 1 := by
    have h5 : ρ ^ 2 ≤ 1 := by
      rw [hρ2, div_le_one hKpos]
      exact hK1
    exact (pow_le_one_iff_of_nonneg hρ0 two_ne_zero).mp h5
  have hρK' : ρ ^ 2 * (g * (m : ℝ)) = 1 := hρK
  -- the cube `2m` and the threshold `⌊m/4⌋`
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hK₂pos : 0 < K₂ := by show 0 < g * ((2 * m : ℕ) : ℝ); rw [h2m]; positivity
  have hK₂ : K ≤ 1 * K₂ := by
    show g * (m : ℝ) ≤ 1 * (g * ((2 * m : ℕ) : ℝ))
    rw [h2m, one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) hg.le
  have hρ₂0 : 0 ≤ ρ₂ := Real.sqrt_nonneg _
  have hρ₂K : ρ₂ ^ 2 * K₂ = 1 := by
    show Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hρ₂ρ : ρ₂ ≤ ρ := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hK₂pos hKpos]
    linarith
  have hs0 : (0 : ℝ) < ((m / 4 : ℕ) : ℝ) := by
    have : 0 < m / 4 := by omega
    exact_mod_cast this
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hK₄pos : 0 < g * ((m / 4 : ℕ) : ℝ) := mul_pos hg hs0
  have hK₄ : K ≤ 8 * (g * (s₀ : ℝ)) := by
    show g * (m : ℝ) ≤ 8 * (g * ((m / 4 : ℕ) : ℝ))
    calc g * (m : ℝ) ≤ g * (8 * ((m / 4 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hs hg.le
      _ = 8 * (g * ((m / 4 : ℕ) : ℝ)) := by ring
  have hρ₄0 : 0 ≤ ρ₄ := Real.sqrt_nonneg _
  have hρ₄K : ρ₄ ^ 2 * (g * (s₀ : ℝ)) = 1 := by
    show Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ))) ^ 2 * (g * ((m / 4 : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (one_div_nonneg.mpr hK₄pos.le)]
    field_simp
  -- the tails
  have h2mm : 0 ≤ 2 * mm := mul_nonneg zero_le_two hmm0
  have hX₁ : 0 ≤ 2 * mm * Ξ₁ + C₀ := add_nonneg (mul_nonneg h2mm hΞ₁) hC₀
  have hτ₁0 : 0 ≤ τ₁ := mul_nonneg h2mm hX₁
  have hβ₄0 : 0 ≤ β₄ := mul_nonneg (mul_nonneg (by norm_num) hmm0)
    (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hmm0) hΞ₁) (mul_nonneg (by norm_num) hC₀))
  have ht₂ : t₂ ≤ τ₁ * ρ ^ 5 := by
    have h := tl_rate (c := 1) hmm0 hΞ₁ hC₀ le_rfl hρ0 hρK hK1 hK₂ hρ₂0 hρ₂K
    have e : 2 * mm * 1 ^ 2 * (2 * mm * 1 ^ 2 * Ξ₁ + 1 * C₀) * ρ ^ 5 = τ₁ * ρ ^ 5 := by
      show _ = 2 * mm * (2 * mm * Ξ₁ + C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have ht₄ : t₄ ≤ β₄ * ρ ^ 5 := by
    have h := tl_rate (c := 8) hmm0 hΞ₁ hC₀ (by norm_num) hρ0 hρK hK1 hK₄ hρ₄0 hρ₄K
    have e : 2 * mm * 8 ^ 2 * (2 * mm * 8 ^ 2 * Ξ₁ + 8 * C₀) * ρ ^ 5 = β₄ * ρ ^ 5 := by
      show _ = 128 * mm * (128 * mm * Ξ₁ + 8 * C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have htl0 : ∀ K' ρ', 0 ≤ ρ' → 0 ≤ tl K' ρ' := by
    intro K' ρ' hρ'
    show 0 ≤ (2 * mm / K' ^ 2) * ((2 * mm / K' ^ 2) * Ξ₁ + C₀ * ρ')
    have h1 : 0 ≤ 2 * mm / K' ^ 2 := div_nonneg (by linarith) (sq_nonneg K')
    exact mul_nonneg h1 (add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hC₀ hρ'))
  have ht₂0 : 0 ≤ t₂ := htl0 _ _ hρ₂0
  have ht₄0 : 0 ≤ t₄ := htl0 _ _ hρ₄0
  -- (I): the projection term
  have hB₂ : B₂ ≤ (2 * mm * Ξ₁ + C₀) * ρ := by
    have hinv : 2 * mm / K₂ ^ 2 ≤ 2 * mm * ρ := by
      have h1 : 1 / K₂ ^ 2 ≤ ρ ^ 4 := by
        have h2 : 1 / K₂ ≤ 1 / K := one_div_le_one_div_of_le hKpos (by linarith)
        have h3 : (1 / K₂) ^ 2 ≤ (1 / K) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
        have e1 : (1 / K₂) ^ 2 = 1 / K₂ ^ 2 := by ring
        have e2 : ρ ^ 4 = (1 / K) ^ 2 := by rw [show ρ ^ 4 = (ρ ^ 2) ^ 2 by ring, hρ2]
        rw [← e1, e2]
        exact h3
      have h4 : ρ ^ 4 ≤ ρ := by
        calc ρ ^ 4 = ρ * ρ ^ 3 := by ring
          _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hρ0 hρ1) hρ0
          _ = ρ := mul_one ρ
      calc 2 * mm / K₂ ^ 2 = 2 * mm * (1 / K₂ ^ 2) := by ring
        _ ≤ 2 * mm * ρ := mul_le_mul_of_nonneg_left (h1.trans h4) h2mm
    have h1 := mul_le_mul_of_nonneg_right hinv hΞ₁
    have h2 := mul_le_mul_of_nonneg_left hρ₂ρ hC₀
    show (2 * mm / K₂ ^ 2) * Ξ₁ + C₀ * ρ₂ ≤ (2 * mm * Ξ₁ + C₀) * ρ
    have e : (2 * mm * Ξ₁ + C₀) * ρ = 2 * mm * ρ * Ξ₁ + C₀ * ρ := by ring
    rw [e]
    exact add_le_add h1 h2
  have hB₂0 : 0 ≤ B₂ := by
    show 0 ≤ (2 * mm / K₂ ^ 2) * Ξ₁ + C₀ * ρ₂
    have h1 : 0 ≤ 2 * mm / K₂ ^ 2 := div_nonneg (by linarith) (sq_nonneg K₂)
    exact add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hC₀ hρ₂0)
  have hI : (η * t₂) * (η * B₂) ≤ (η ^ 2 * τ₁ * (2 * mm * Ξ₁ + C₀)) * (1 / K) ^ 3 := by
    have h1 : (η * t₂) * (η * B₂) ≤ (η * (τ₁ * ρ ^ 5)) * (η * ((2 * mm * Ξ₁ + C₀) * ρ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ht₂ hη) (mul_le_mul_of_nonneg_left hB₂ hη)
        (mul_nonneg hη hB₂0) (mul_nonneg hη (mul_nonneg hτ₁0 (pow_nonneg hρ0 5)))
    have hρ6 : ρ ^ 6 = (1 / K) ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hρ2]
    have e : (η * (τ₁ * ρ ^ 5)) * (η * ((2 * mm * Ξ₁ + C₀) * ρ)) =
        (η ^ 2 * τ₁ * (2 * mm * Ξ₁ + C₀)) * ρ ^ 6 := by ring
    rw [e, hρ6] at h1
    exact h1
  -- (III): the pairings
  have hfA : formA s₀ m ≤ cF * ρ := formA_rate hg hρ0 hm hρK'
  have hsh := shell_rate hg hm hρK'
  have hmW : 0 ≤ mm * W := mul_nonneg hmm0 hW
  have hτφ : τφ ≤ 64 * g ^ 2 * ρ ^ 4 * (mm * W) := by
    have e : τφ = (mm * W) * (1 / ((s₀ : ℝ) + 1) ^ 2) := by
      show mm * W / ((s₀ : ℝ) + 1) ^ 2 = _
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsh.1 hmW
    linarith
  have hτφ0 : 0 ≤ τφ := div_nonneg hmW (sq_nonneg _)
  have hmτ : (m : ℝ) * τφ ≤ 64 * g * ρ ^ 2 * (mm * W) := by
    have e : (m : ℝ) * τφ = (mm * W) * ((m : ℝ) / ((s₀ : ℝ) + 1) ^ 2) := by
      show (m : ℝ) * (mm * W / ((s₀ : ℝ) + 1) ^ 2) = _
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsh.2 hmW
    linarith
  have hcF0 : 0 ≤ cF := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hg1 : 0 ≤ 1 + g ^ 2 := add_nonneg zero_le_one (sq_nonneg g)
  have hCtL : 0 ≤ Ct ((1 + g ^ 2) * (mm * W)) := by
    rw [hCt]
    exact mul_nonneg (mul_nonneg hg1 hmW) hC1
  have hIII := rate_arith_III (m := (m : ℝ)) (Xa := Xa) hη hτ₁0 hρ0 hρ1 ht₂ hρ₂ρ hρ₂0 hCtL hZg hfA
    (formA_nonneg s₀ m) ht₄ ht₄0 hmW hτφ hτφ0 hmτ hXa hg.le ht hβ₄0 hcF0
  have hΓ0 : 0 ≤ Γ := add_nonneg
    (mul_nonneg (mul_nonneg hη (mul_nonneg hη hτ₁0)) (mul_nonneg hg1 hC1))
    (mul_nonneg hZg (add_nonneg (add_nonneg (mul_nonneg hcF0 hβ₄0)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcF0) (sq_nonneg g)) hXa))
      (mul_nonneg (mul_nonneg (by norm_num) hg.le) hβ₄0)))
  have hrr : 1 ≤ Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 := one_le_sqrt_pow_three m
  have hW₁ : 0 ≤ W₁ := by
    by_contra h
    push Not at h
    have : Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 * W₁ < 0 :=
      mul_neg_of_pos_of_neg (by linarith) h
    linarith
  have hrrρ := rr_rho_le hg hρ0 (by omega : 1 ≤ m) hρK'
  have e1 : 2 * (η * (η * τ₁) * Ct ((1 + g ^ 2) * (mm * W)) +
      Zg * (mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)) * t * ρ ^ 5 =
      2 * mm * Γ * t * (W * ρ ^ 5) := by
    rw [hCt]
    ring
  have h3 : W * ρ ^ 5 ≤ W₁ * Real.sqrt (5 / g) ^ 3 * ρ ^ 2 := by
    calc W * ρ ^ 5 ≤ (Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 * W₁) * ρ ^ 5 :=
          mul_le_mul_of_nonneg_right hWr (pow_nonneg hρ0 5)
      _ = W₁ * (Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 * ρ ^ 3) * ρ ^ 2 := by ring
      _ ≤ W₁ * Real.sqrt (5 / g) ^ 3 * ρ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrrρ hW₁) (sq_nonneg ρ)
  have h4 : 2 * mm * Γ * t * (W * ρ ^ 5) ≤
      (2 * mm * W₁ * Γ * Real.sqrt (5 / g) ^ 3) * t * (1 / K) := by
    have h5 := mul_le_mul_of_nonneg_left h3 (mul_nonneg (mul_nonneg h2mm hΓ0) ht)
    have e2 : 2 * mm * Γ * t * (W₁ * Real.sqrt (5 / g) ^ 3 * ρ ^ 2) =
        (2 * mm * W₁ * Γ * Real.sqrt (5 / g) ^ 3) * t * (1 / K) := by
      rw [hρ2]
      ring
    linarith
  rw [e1] at hIII
  linarith

end Arith

/-! ## The constants and the rates for the Coulomb system -/

section Rates

/-- The constants `(A₁, A₂)` of `prop:mult-grid` for the data norms `‖ψ₀‖ = s0`, `‖H ψ₀‖ = hu`,
`‖H ψ₀‖ = hs` (the decoded state of `H ψ₀`) and `‖H² ψ₀‖ = hv`; they do not depend on the
register `m` (that is `K`), on the kernel or on `t`. -/
noncomputable def gridKinConsts (sys : CoulombSystem eta ν) (L Hunit Blow Cs Bker : ℝ)
    (s0 hu hs hv : ℝ) : ℝ × ℝ :=
  let g : ℝ := 2 * Real.pi / L
  let b : ℝ := relB sys L Hunit
  let Ξ₀ : ℝ := 2 * hu + 2 * b * s0
  let Ξ₁ : ℝ := 2 * hv + 2 * b * hs
  let M₀ : ℝ := sys.maxMass * (s0 + 2 * Ξ₀)
  let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
  let C₀ : ℝ := Ct M₀
  let τ₁ : ℝ := 2 * sys.maxMass * (2 * sys.maxMass * Ξ₁ + C₀)
  let β₄ : ℝ := 128 * sys.maxMass * (128 * sys.maxMass * Ξ₁ + 8 * C₀)
  let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
  let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
  let cJ : ℝ := gridFlowConst sys L
  let Xb : ℝ := 5 / 3 * Xa + cJ * s0
  let Q : ℝ := ((kZero g : ℕ) : ℝ) ^ 4 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 / g ^ 4 +
    30 * C₀ ^ 2 / g
  let cH : ℝ := 26 * coulombGridCoupling sys L * (J0g (coulombGridCoupling sys L) g : ℝ)
  let σ : ℝ := Zg * (52 * (J0g (sys.maxMass * Zg) g : ℝ) + 4 * Real.sqrt 53 * sys.maxMass)
  let ξ : ℝ := s0 + 4 / g ^ 2 * Ξ₀ + 2 / g ^ 2 * (eta * Real.sqrt Q)
  let F : ℝ := flow2 g cJ cH σ ξ Xa s0
  let W₁ : ℝ := 5 / 3 * (g ^ 2 / 2 * F) + cJ * (g ^ 2 / 2 * Xb)
  let cF : ℝ := 4 * Real.sqrt (5512 * g)
  let Γ : ℝ := eta * (eta * τ₁) * ((1 + g ^ 2) * Ct 1) +
    Zg * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)
  ((eta : ℝ) ^ 2 * τ₁ * (2 * sys.maxMass * Ξ₁ + C₀),
    2 * sys.maxMass * W₁ * Γ * Real.sqrt (5 / g) ^ 3)

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **`prop:mult-grid`, rates (Fourier side).** For `m ≥ 8` and `K = g m ≥ 8`,
`|⟨ψ(t), A_r ψ(t)⟩ - ⟨ψ_g(t), A_r ψ_g(t)⟩| ≤ A₁ K^{-3} + A₂ t K^{-1}`, with
`(A₁, A₂) = gridKinConsts` (independent of `K`, the kernel and `t`). -/
theorem grid_kinetic_rate (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (Blow Cs Bker : ℝ) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (r : Fin eta) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridKinConsts sys L Hunit Blow Cs Bker ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖
    let ψg := Ug t (regCoeff m (molecularH2StateMap eta g u₀))
    |(regKin sys g r).expect (U t (molecularH2StateMap eta g u₀)) - regExpect sys g r ψg| ≤
      A.1 * (1 / K) ^ 3 + A.2 * t * (1 / K) := by
  intro g K A ψg
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hK' : (8 : ℝ) ≤ g * (m : ℝ) := hK
  have hK₄ : 1 ≤ g * ((m / 4 : ℕ) : ℝ) := by
    have : g * (m : ℝ) ≤ 8 * (g * ((m / 4 : ℕ) : ℝ)) := by nlinarith
    linarith
  have hKpos : 0 < g * (m : ℝ) := by linarith
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
  have hΞ₀ : 0 ≤ 2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖ :=
    add_nonneg (mul_nonneg zero_le_two (norm_nonneg _))
      (mul_nonneg (mul_nonneg zero_le_two hb) hS0)
  have hΞ₁ : 0 ≤ 2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖ :=
    add_nonneg (mul_nonneg zero_le_two (norm_nonneg _))
      (mul_nonneg (mul_nonneg zero_le_two hb) (norm_nonneg _))
  have hCt : ∀ M, 0 ≤ M → 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M :=
    fun M hM' => finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM'
  have hM₀ : 0 ≤ sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖)) :=
    mul_nonneg (by linarith) (add_nonneg hS0 (mul_nonneg zero_le_two hΞ₀))
  have hZg : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg hγ
  have hcJ : 0 ≤ gridFlowConst sys L := gridFlowConst_nonneg sys hL
  have hXa : 0 ≤ (1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))) :=
    mul_nonneg (by positivity) hM₀
  -- the flow budget
  set Q : ℝ := ((kZero g : ℕ) : ℝ) ^ 4 *
      (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖) ^ 2 +
      120 * sys.maxMass ^ 2 *
        (2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖) ^ 2 / g ^ 4 +
      30 * finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
        (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
          2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))) ^ 2 / g
    with hQdef
  set Zg := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
    with hZgdef
  set cJ := gridFlowConst sys L with hcJdef
  set cH : ℝ := 26 * coulombGridCoupling sys L * (J0g (coulombGridCoupling sys L) g : ℝ)
    with hcHdef
  set σ : ℝ := Zg * (52 * (J0g (sys.maxMass * Zg) g : ℝ) + 4 * Real.sqrt 53 * sys.maxMass)
    with hσdef
  set Xa := (1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))) with hXadef
  set Xb := 5 / 3 * Xa + cJ * ‖molecularH2StateMap eta g u₀‖ with hXbdef
  set ξ : ℝ := ‖molecularH2StateMap eta g u₀‖ +
      4 / g ^ 2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖) +
      2 / g ^ 2 * (eta * Real.sqrt Q) with hξdef
  set F := flow2 g cJ cH σ ξ Xa ‖molecularH2StateMap eta g u₀‖ with hFdef
  set rr := Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 with hrrdef
  have hcH : 0 ≤ cH :=
    mul_nonneg (mul_nonneg (by norm_num) (coulombGridCoupling_nonneg sys L hL)) (Nat.cast_nonneg _)
  have hσ0 : 0 ≤ σ := mul_nonneg hZg (by positivity)
  have hξ0 : 0 ≤ ξ := add_nonneg (add_nonneg hS0 (mul_nonneg (by positivity) hΞ₀))
    (mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)))
  have hF0 : 0 ≤ F := flow2_nonneg hcJ hcH hσ0 hξ0 hXa hS0
  have hXb0 : 0 ≤ Xb := add_nonneg (mul_nonneg (by norm_num) hXa) (mul_nonneg hcJ hS0)
  have hrr : 1 ≤ rr := one_le_sqrt_pow_three m
  have hg2 : (0 : ℝ) ≤ g ^ 2 / 2 := by positivity
  have hW0 : 0 ≤ 5 / 3 * (g ^ 2 / 2 * (rr * F)) + cJ * (g ^ 2 / 2 * Xb) :=
    add_nonneg (mul_nonneg (by norm_num) (mul_nonneg hg2 (mul_nonneg (by linarith) hF0)))
      (mul_nonneg hcJ (mul_nonneg hg2 hXb0))
  have hWr : 5 / 3 * (g ^ 2 / 2 * (rr * F)) + cJ * (g ^ 2 / 2 * Xb) ≤
      rr * (5 / 3 * (g ^ 2 / 2 * F) + cJ * (g ^ 2 / 2 * Xb)) := by
    have h1 : cJ * (g ^ 2 / 2 * Xb) ≤ rr * (cJ * (g ^ 2 / 2 * Xb)) :=
      le_mul_of_one_le_left (mul_nonneg hcJ (mul_nonneg hg2 hXb0)) hrr
    have e : rr * (5 / 3 * (g ^ 2 / 2 * F) + cJ * (g ^ 2 / 2 * Xb)) =
        5 / 3 * (g ^ 2 / 2 * (rr * F)) + rr * (cJ * (g ^ 2 / 2 * Xb)) := by ring
    rw [e]
    linarith
  refine (grid_kinetic_error sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph hderiv m hm hκ Ug
    hg0 hgcomm hgderiv (Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))))
    (Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))) Blow Cs Bker hK₄ (Real.sqrt_nonneg _)
    (hscale _ hK₂pos) (Real.sqrt_nonneg _) (hscale _ hK₄pos) hBlow hCs hBker hAmplitude
    hBkerScale hCsScale u₀ v₀ huv r (kZero g) (two_le_kZero g) (one_le_mul_kZero hg) ht).trans ?_
  exact kin_grid_rate_arith (η := (eta : ℝ)) (mm := sys.maxMass)
    (Ξ₁ := 2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖)
    (C₀ := finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
      (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
        2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))))
    (C1 := finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker 1)
    (g := g) (t := t) (Zg := Zg) (Xa := Xa)
    (W := 5 / 3 * (g ^ 2 / 2 * (rr * F)) + cJ * (g ^ 2 / 2 * Xb))
    (W₁ := 5 / 3 * (g ^ 2 / 2 * F) + cJ * (g ^ 2 / 2 * Xb)) (m := m)
    (Ct := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M)
    (Nat.cast_nonneg eta) hM hΞ₁ (hCt _ hM₀) hg hm hK ht hZg hXa hW0 hWr
    (fun M => tailConstant_linear sys L Hunit Blow Cs Bker M) (hCt 1 zero_le_one)

end Rates

/-! ## Position space -/

section Position

variable {m : ℕ}

/-- The kinetic energy `A_r` on the position grid, applied through the DFT (the QFT): the
expectation `⟨ψ, dft⁻¹ A_r dft ψ⟩` of the grid values `ψ` (`posKinExpect_eq_inner`). -/
noncomputable def posKinExpect (sys : CoulombSystem eta ν) (g : ℝ) (r : Fin eta)
    (ψ : EuclideanSpace ℂ (RCfg eta m)) : ℝ :=
  regExpect sys g r (dft ψ)

omit [Fintype ν] in
lemma posKinExpect_eq_inner (sys : CoulombSystem eta ν) (g : ℝ) (r : Fin eta)
    (ψ : EuclideanSpace ℂ (RCfg eta m)) :
    (posKinExpect sys g r ψ : ℂ) = ⟪ψ, idft (wMul (regKinSym sys g r) (dft ψ))⟫_ℂ := by
  rw [posKinExpect, regExpect, ← inner_wMul_self, ← inner_dft_dft ψ, dft_idft]

/-- **`prop:mult-grid` in position space.** Let `U t` be unitaries on `L²((T³)^η)` with `U 0 = 1`
that preserve the graph of the Coulomb Hamiltonian and solve the Schrödinger equation on it, and
`U_g` the register propagator of the grid Hamiltonian of a real, even kernel of the class `𝒦_K`
(`K = 2πm/L`, register radius `2m`), so that `dft⁻¹ U_g(t) dft = e^{-iH_pos t}`. For
`ψ₀ ∈ D(H²)` (`H ψ₀ = h₀`, `H h₀ = h₁`), a particle `r`, the grid state
`ψ_g(t) = e^{-iH_pos t} P ψ₀` (`P ψ₀` sampled on the grid, unitarily normalised) and the kinetic
energy `A_r` applied through the DFT: for `m ≥ 8`, `K ≥ 8` and `t ≥ 0`,
`|⟨ψ(t), A_r ψ(t)⟩ - ⟨ψ_g(t), A_r ψ_g(t)⟩| ≤ A₁ K^{-3} + A₂ t K^{-1}` with
`(A₁, A₂) = gridKinConsts` at the canonical constants of the cell, independent of `K` and `t`. -/
theorem grid_kinetic_position (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (ψ₀ h₀ h₁ : MolecularPositionL2 eta) (hψ₀ : HasCoulombHamiltonian sys L ψ₀ h₀)
    (hh₀ : HasCoulombHamiltonian sys L h₀ h₁) (r : Fin eta) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridKinConsts sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
    let ψg := posConj (Ug t) (idft (regCoeff m ((physMap eta).symm ψ₀)))
    |(regKin sys g r).posExpect (U t ψ₀) - posKinExpect sys g r ψg| ≤
      A.1 * (1 / K) ^ 3 + A.2 * t * (1 / K) := by
  intro g K A ψg
  have hPeriodic := canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨H, hKernel, -⟩ :=
    exists_coulombFourierH2Operator sys L molecularCanonicalUnitHardyConstant hL hPeriodic
  have hiff := hasCoulombHamiltonian_iff_phys sys L hL H hKernel
  -- the propagator on the Fourier side
  set UF : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
    fun s => ((physMap eta).trans (U s)).trans (physMap eta).symm with hUFdef
  have hUF : ∀ s x, UF s x = (physMap eta).symm (U s (physMap eta x)) := fun s x => rfl
  have h0F : ∀ x, UF 0 x = x := by
    intro x
    rw [hUF, hU0, LinearIsometryEquiv.symm_apply_apply]
  have hgraphF : ∀ s u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        UF s (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = UF s (H u) := by
    intro s u
    obtain ⟨u', h1, h2⟩ := (hiff _ _).mp (hUgraph s _ _ ((hiff _ _).mpr ⟨u, rfl, rfl⟩))
    refine ⟨u', ?_, ?_⟩
    · rw [hUF, ← h1, LinearIsometryEquiv.symm_apply_apply]
    · rw [hUF, ← h2, LinearIsometryEquiv.symm_apply_apply]
  have hderivF : ∀ s u, HasDerivAt (fun r => UF r (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • UF s (H u))) s := by
    intro s u
    have h := hUderiv s _ _ ((hiff _ _).mpr ⟨u, rfl, rfl⟩)
    have h2 := (((physMap eta).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt s h
    simp only [ContinuousLinearMap.coe_restrictScalars'] at h2
    rw [map_neg, map_smul] at h2
    exact h2
  -- the initial state in `D(H²)`
  obtain ⟨u₀, hu₀1, hu₀2⟩ := (hiff ψ₀ h₀).mp hψ₀
  obtain ⟨v₀, hv₀1, hv₀2⟩ := (hiff h₀ h₁).mp hh₀
  have huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀ :=
    (physMap eta).injective (hu₀2.trans hv₀1.symm)
  have hx₀ : (physMap eta).symm ψ₀ = molecularH2StateMap eta (2 * Real.pi / L) u₀ := by
    rw [← hu₀1, LinearIsometryEquiv.symm_apply_apply]
  have hψt : U t ψ₀ = physMap eta (UF t (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    rw [hUF, LinearIsometryEquiv.apply_symm_apply, hu₀1]
  -- the grid expectation on the register
  have hdψ : dft ψg = Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    show dft (posConj (Ug t) (idft (regCoeff m ((physMap eta).symm ψ₀)))) = _
    rw [dft_posConj, dft_idft, hx₀]
  have hψg : posKinExpect sys g r ψg =
      regExpect sys g r (Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀))) := by
    rw [posKinExpect, hdψ]
  rw [hψt, posExpect_physMap, hψg]
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  have h := grid_kinetic_rate sys L H hKernel molecularCanonicalUnitHardyConstant hL hPeriodic
    (finiteCoulombPhysicalMassConstant_nonneg _ _ _) UF h0F hgraphF hderivF m hm hK hκ Ug hg0
    hgcomm hgderiv _ _ _ hBlow hCs hBker hLow hKernelScale hSobolev u₀ v₀ huv r ht
  dsimp only at h
  have e1 : ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ = ‖ψ₀‖ := by
    rw [← hu₀1, LinearIsometryEquiv.norm_map]
  have e2 : ‖H u₀‖ = ‖h₀‖ := by rw [← hu₀2, LinearIsometryEquiv.norm_map]
  have e3 : ‖molecularH2StateMap eta (2 * Real.pi / L) v₀‖ = ‖h₀‖ := by
    rw [← hv₀1, LinearIsometryEquiv.norm_map]
  have e4 : ‖H v₀‖ = ‖h₁‖ := by rw [← hv₀2, LinearIsometryEquiv.norm_map]
  rw [e1, e2, e3, e4] at h
  exact h

/-- **`prop:mult-grid`** (truncated-kernel grid method, kinetic energy after evolution). For a
periodic Coulomb system there is a propagator `U` (`e^{-iHt}`) on `L²((T³)^η)` (unitary group,
strongly continuous, preserving the graph of the Hamiltonian, solving the Schrödinger equation on
it, and the only evolution that does), and for every register radius `2m` and every real, even
kernel `κ` of the class `𝒦_K` (`K = 2πm/L`) a grid propagator `U_g` (`e^{-iH_pos t}` on the grid
values), such that: for every `ψ₀ ∈ D(H²)` (`H ψ₀ = h₀`, `H h₀ = h₁`) and particle `r`, with the
constants `(A₁, A₂) = gridKinConsts` at `(‖ψ₀‖, ‖h₀‖, ‖h₀‖, ‖h₁‖)`, which do not depend on `m`,
the kernel or `t`: for `m ≥ 8`, `K ≥ 8` and `t ≥ 0`, the grid state `ψ_g(t) = e^{-iH_pos t} P ψ₀`
and the kinetic energy `A_r` applied through the DFT satisfy
`|⟨ψ(t), A_r ψ(t)⟩ - ⟨ψ_g(t), A_r ψ_g(t)⟩| ≤ A₁ K^{-3} + A₂ t K^{-1}`. -/
theorem thm_mult_grid (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    ∃ U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, Continuous fun t => U t ψ) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasCoulombHamiltonian sys L (U t f) (U t h)) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) ∧
      (∀ φ ζ : ℝ → MolecularPositionL2 eta, (∀ t, HasCoulombHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
        (∀ x, Continuous fun t => Ug t x) ∧
        (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t x)) ∧
        (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
        ∀ ψ₀ h₀ h₁ : MolecularPositionL2 eta, HasCoulombHamiltonian sys L ψ₀ h₀ →
          HasCoulombHamiltonian sys L h₀ h₁ → ∀ r : Fin eta,
          let A := gridKinConsts sys L molecularCanonicalUnitHardyConstant
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let ψg := Ug t (idft (regCoeff m ((physMap eta).symm ψ₀)))
            |(regKin sys (2 * Real.pi / L) r).posExpect (U t ψ₀) -
                posKinExpect sys (2 * Real.pi / L) r ψg| ≤
              A.1 * (1 / K) ^ 3 + A.2 * t * (1 / K) := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, -, -⟩ := exists_coulombPropagator sys L hL
  refine ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, fun m κ hκ => ?_⟩
  obtain ⟨Ur, hr0, -, -, hrcomm, hrderiv, hp0, hpadd, hpcont, hpcomm, hpderiv⟩ :=
    exists_posPropagator (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) hκ.even
      (2 * Real.pi / L)
  refine ⟨fun t => posConj (Ur t), hp0, hpadd, hpcont, hpcomm, hpderiv, ?_⟩
  intro ψ₀ h₀ h₁ hψ₀ hh₀ r A hm hK t ht K ψg
  exact grid_kinetic_position sys L hL U h0 hgraph hderiv m hm hK hκ Ur hr0 hrcomm hrderiv ψ₀ h₀
    h₁ hψ₀ hh₀ r ht

end Position

/-! ## `cor:stopping`, grid route -/

/-- **`cor:stopping`, grid route.** In the setting of `grid_kinetic_position`, the secant-slope
estimator `Ŝ = (⟨A_r⟩(T) - ⟨A_r⟩(0))/(v_p T)` of the stopping power over a window `[0, T]`,
evaluated on the grid trajectory, deviates from the same functional of the exact trajectory by at
most `(A₂ K^{-1} + 2 A₁ K^{-3}/T)/v_p`. -/
theorem stopping_grid (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (ψ₀ h₀ h₁ : MolecularPositionL2 eta) (hψ₀ : HasCoulombHamiltonian sys L ψ₀ h₀)
    (hh₀ : HasCoulombHamiltonian sys L h₀ h₁) (r : Fin eta) {vp T : ℝ} (hvp : 0 < vp)
    (hT : 0 < T) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridKinConsts sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
    let ψg : ℝ → EuclideanSpace ℂ (RCfg eta m) := fun s =>
      posConj (Ug s) (idft (regCoeff m ((physMap eta).symm ψ₀)))
    let μ := regKin sys g r
    |(μ.posExpect (U T ψ₀) - μ.posExpect (U 0 ψ₀)) / (vp * T) -
        (posKinExpect sys g r (ψg T) - posKinExpect sys g r (ψg 0)) / (vp * T)| ≤
      (A.2 * (1 / K) + 2 * A.1 * (1 / K) ^ 3 / T) / vp := by
  intro g K A ψg μ
  have h0 := grid_kinetic_position sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
    hgderiv ψ₀ h₀ h₁ hψ₀ hh₀ r (le_refl 0)
  have hT' := grid_kinetic_position sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
    hgderiv ψ₀ h₀ h₁ hψ₀ hh₀ r hT.le
  exact (secant_slope_le hvp hT h0 hT').trans (le_of_eq (stopping_arith hvp hT))

end PlaneWaveKinetic

end DevK8
-- END SOURCE dev/DevK8.lean

-- BEGIN SOURCE dev/DevK9.lean
-- SHA256 8b856b89e37e0f2e2154215131106eee940c98b3d2cb8e51978c949884298ace
section DevK9

/-!
# Trajectory tails of the grid evolution: `lem:grid-tails`

For the grid state `ψ_g(s) = e^{-iH_grid s} P ψ₀` on the register of radius `2m` and every
threshold, the kinetic tail `‖1_{|q_r|∞ > T} A ψ_g(s)‖` is `O(Ξ (gT)^{-1/2})`, uniformly in `s`
(`grid_kin_tail_reg`, register form, sup-norm thresholds `2 ≤ T ≤ 2m`). The proof is the
manuscript's: on the register `A ψ_g = H_grid ψ_g - V_grid ψ_g`;

* the potential term at every threshold is `vGridK_tail` of the grid core (the grid analogue
  of `eq:lam-gen`), with the a priori shell of `ψ_g` and its weight `‖W ψ_g‖ ≤ X_b`
  (`lem:grid-traj`);
* the Hamiltonian term is `H_grid ψ_g(s) = e^{-iH_grid s} H_grid P ψ₀` with
  `H_grid P ψ₀ = P H ψ₀ + r_g`, `r_g = Δ P ψ₀ - P W (1 - P) ψ₀` (`regCoeff_H_eq_grid`): the flow
  of `P H ψ₀` has weight `O(Ξ)`, hence shell `O(Ξ T^{-2})`, and `‖r_g‖ = O(Ξ K^{-1/2})`. The
  grid difference `Δ = R - D` is bounded in norm by its form bound `Delta_form` paired with
  `Δ P ψ₀` itself (`norm_Delta_le`), with the continuum tails of `ψ₀` at `⌊m/4⌋` and the crude
  register weight `wTot ≤ 1 + 12 η m²` (`norm_wTot_le_reg`); the Galerkin source is
  `backscatter_initial_le` at the register cube.

`grid_kin_tail_euclid` turns this into Euclidean thresholds `λ` for the lifted state
(`‖1_{|k_r| > λ} A ψ_g(s)‖ ≤ D_g λ^{-1/2}` for `4g ≤ λ ≤ K`, `λ ≥ 1`), with the plain tails
`(8m̄/λ²) D_g λ^{-1/2}` by the restriction weights at the sup-norm threshold `⌊λ/(2g)⌋`
(`lem:grid-tails`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate lp ENNReal Topology
open Filter Set

namespace PlaneWaveKinetic

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Register weights, masks and the grid difference -/

section Register

variable {m : ℕ}

lemma wTot_le_reg (q : RCfg eta m) : wTot q ≤ 1 + 12 * eta * (m : ℝ) ^ 2 := by
  have h : ∑ a, nsq (gl (q a)) ≤ ∑ _a : Fin eta, 12 * (m : ℝ) ^ 2 :=
    Finset.sum_le_sum fun a _ => nsq_gl_le (q a)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [wTot_eq]
  linarith

/-- The crude register weight: `‖wTot x‖ ≤ (1 + 12 η m²) ‖x‖`. -/
lemma norm_wTot_le_reg (x : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul wTot x‖ ≤ (1 + 12 * eta * (m : ℝ) ^ 2) * ‖x‖ := by
  have hc : (0 : ℝ) ≤ 1 + 12 * eta * (m : ℝ) ^ 2 := by positivity
  refine (norm_le_of_pointwise (Y := ((1 + 12 * eta * (m : ℝ) ^ 2 : ℝ) : ℂ) • x)
    fun q => ?_).trans ?_
  · rw [wMul_apply, PiLp.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (le_trans zero_le_one (wTot_ge_one q)),
      Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_right (wTot_le_reg q) (norm_nonneg _)
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]

/-- **The grid difference in norm.** If the shells of `u` beyond `s` are at most `τ` and
`‖wTot u‖ ≤ X`, then `‖Δ u‖ ≤ Z_c (A(s, m)(τ (1 + 12 η m²) + X) + 52 m τ)`: the form bound
`Delta_form` paired with `Δ u` itself. -/
lemma norm_Delta_le {ν' : Type*} [Fintype ν'] (P : RegParticles eta) (D : NucData ν')
    {gamma : ℝ} (hg : 0 ≤ gamma) {s : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m) {κ : Lat3 → ℝ}
    (hκ : GridKernel gamma s κ) (u : EuclideanSpace ℂ (RCfg eta m)) {τ X : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : ∀ r, ‖maskOp (High s r) u‖ ≤ τ) (hX : ‖wMul wTot u‖ ≤ X) :
    ‖Delta eta m P D gamma κ u‖ ≤
      Zc P D gamma * (formA s m * (τ * (1 + 12 * eta * (m : ℝ) ^ 2) + X) + 52 * m * τ) := by
  set x := Delta eta m P D gamma κ u with hxdef
  have hZ : 0 ≤ Zc P D gamma := Zc_nonneg hg
  have hA := formA_nonneg s m
  have hX0 : 0 ≤ X := (norm_nonneg _).trans hX
  have hc : (0 : ℝ) ≤ 1 + 12 * eta * (m : ℝ) ^ 2 := by positivity
  set R := Zc P D gamma * (formA s m * (τ * (1 + 12 * eta * (m : ℝ) ^ 2) + X) + 52 * m * τ)
    with hRdef
  have hR0 : 0 ≤ R := mul_nonneg hZ (add_nonneg (mul_nonneg hA (add_nonneg (mul_nonneg hτ0 hc)
    hX0)) (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hτ0))
  rcases (norm_nonneg x).eq_or_lt with h | h
  · rw [← h]
    exact hR0
  have hf := Delta_form (P := P) (D := D) hg hs hsm hκ u x hτ0 (norm_nonneg x) hτ
    (fun r => norm_maskOp_le _ _)
  have hself : ‖⟪x, x⟫_ℂ‖ = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hf' : ‖x‖ ^ 2 ≤ ‖x‖ * R := by
    have h1 : ‖⟪x, x⟫_ℂ‖ ≤ Zc P D gamma * (formA s m * (τ * ‖wMul wTot x‖ + ‖x‖ * ‖wMul wTot u‖) +
        52 * m * (‖x‖ * τ)) := hf
    rw [hself] at h1
    refine h1.trans ?_
    have h2 : τ * ‖wMul wTot x‖ ≤ τ * ((1 + 12 * eta * (m : ℝ) ^ 2) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_wTot_le_reg x) hτ0
    have h3 : ‖x‖ * ‖wMul wTot u‖ ≤ ‖x‖ * X := mul_le_mul_of_nonneg_left hX (norm_nonneg _)
    have h4 : formA s m * (τ * ‖wMul wTot x‖ + ‖x‖ * ‖wMul wTot u‖) ≤
        formA s m * (τ * ((1 + 12 * eta * (m : ℝ) ^ 2) * ‖x‖) + ‖x‖ * X) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 h3) hA
    have h5 := mul_le_mul_of_nonneg_left (add_le_add h4 (le_refl (52 * (m : ℝ) * (‖x‖ * τ)))) hZ
    refine h5.trans (le_of_eq ?_)
    rw [hRdef]
    ring
  nlinarith

/-- **Euclidean tails of a register vector.** For the zero extension of a register vector, the
continuum tail beyond the Euclidean threshold `λ` is at most the register shell beyond the
sup-norm threshold `T` whenever `2 g T ≤ λ`. -/
lemma norm_tailMask_regEmb_le {g : ℝ} (hg : 0 < g) {lam : ℝ} {T : ℕ} (hT : 2 * g * T ≤ lam)
    (r : Fin eta) (x : EuclideanSpace ℂ (RCfg eta m)) :
    ‖tailMask g lam r (regEmb m x)‖ ≤ ‖maskOp (High T r) x‖ := by
  have htr : molecularH2Truncate (2 * m) (tailMask g lam r (regEmb m x)) =
      tailMask g lam r (regEmb m x) := by
    rw [truncate_tailMask, ← regEmb_regCoeff (m := m) (regEmb m x), regCoeff_regEmb]
  rw [← norm_regCoeff_of_truncate (m := m) _ htr]
  refine norm_le_of_pointwise fun q => ?_
  rw [regCoeff_apply, tailMask_apply]
  have hx : (regEmb m x) (liftCfg q) = x q := by
    rw [← regCoeff_apply, regCoeff_regEmb]
  rw [hx]
  split_ifs with h
  · have hH : High T r q := by
      intro hbox
      have hn : nsq (gl (q r)) ≤ 3 * (T : ℝ) ^ 2 := by
        rw [nsq_eq_sum, Fin.sum_univ_three]
        have hc : ∀ c : Fin 3, ((gl (q r) c : ℤ) : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by
          intro c
          have h0 : |gl (q r) c| ≤ (T : ℤ) := hbox c
          have h1 : |((gl (q r) c : ℤ) : ℝ)| ≤ (T : ℝ) := by
            have h1' : ((|gl (q r) c| : ℤ) : ℝ) ≤ ((T : ℤ) : ℝ) := Int.cast_le.mpr h0
            rwa [Int.cast_abs, Int.cast_natCast] at h1'
          calc ((gl (q r) c : ℤ) : ℝ) ^ 2 = |((gl (q r) c : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
            _ ≤ (T : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        linarith [hc 0, hc 1, hc 2]
      have hl : latticeNormSq (liftCfg q r) = nsq (gl (q r)) := rfl
      rw [hl] at h
      have hs : Real.sqrt (nsq (gl (q r))) ≤ 2 * T := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith
      have : g * Real.sqrt (nsq (gl (q r))) ≤ lam := by
        calc g * Real.sqrt (nsq (gl (q r))) ≤ g * (2 * T) := mul_le_mul_of_nonneg_left hs hg.le
          _ = 2 * g * T := by ring
          _ ≤ lam := hT
      linarith
    rw [one_mul, maskOp_apply_of _ _ hH]
  · rw [zero_mul, norm_zero]
    exact norm_nonneg _

/-- **Restriction weights on the register:**
`‖1_{High T r} x‖ ≤ (2 m̄/(g² (T+1)²)) ‖1_{High T r} A x‖` for the kinetic symbol `A = kinT`. -/
lemma norm_high_le_kinT (P : RegParticles eta) {g : ℝ} (hg : 0 < g) (T : ℕ) (r : Fin eta)
    (x : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) x‖ ≤ 2 * P.maxMass / (g ^ 2 * ((T : ℝ) + 1) ^ 2) *
      ‖maskOp (High T r) (wMul (kinT eta m P g) x)‖ := by
  have hc : 0 ≤ 2 * P.maxMass / (g ^ 2 * ((T : ℝ) + 1) ^ 2) := by
    have := P.maxMass_pos
    positivity
  refine (norm_le_of_pointwise (Y := ((2 * P.maxMass / (g ^ 2 * ((T : ℝ) + 1) ^ 2) : ℝ) : ℂ) •
    maskOp (High T r) (wMul (kinT eta m P g) x)) fun q => ?_).trans ?_
  · have hMp := P.maxMass_pos
    by_cases h : High T r q
    · rw [maskOp_apply_of _ _ h, PiLp.smul_apply, smul_eq_mul, maskOp_apply_of _ _ h, wMul_apply,
        norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc]
      have hk : g ^ 2 * ((T : ℝ) + 1) ^ 2 / (2 * P.maxMass) ≤ kinT eta m P g q := by
        have h1 : ((T : ℝ) + 1) ^ 2 ≤ nsq (gl (q r)) := nsq_ge_of_not_inBox h
        have h2 : nsq (gl (q r)) / P.mass r ≤ wM P q - 1 := by
          unfold wM
          have := Finset.single_le_sum (f := fun a => nsq (gl (q a)) / P.mass a)
            (fun a _ => div_nonneg (nsq_nonneg _) (P.mass_pos a).le) (Finset.mem_univ r)
          linarith
        have h3 : ((T : ℝ) + 1) ^ 2 / P.maxMass ≤ nsq (gl (q r)) / P.mass r :=
          div_le_div₀ (nsq_nonneg _) h1 (P.mass_pos r) (P.mass_le_maxMass r)
        unfold kinT
        have hM := P.maxMass_pos
        have e : g ^ 2 * ((T : ℝ) + 1) ^ 2 / (2 * P.maxMass) =
            g ^ 2 / 2 * (((T : ℝ) + 1) ^ 2 / P.maxMass) := by
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left (h3.trans h2) (by positivity)
      have hk0 : 0 ≤ kinT eta m P g q := le_trans (by positivity) hk
      rw [Real.norm_of_nonneg hk0]
      have hpos : 0 < g ^ 2 * ((T : ℝ) + 1) ^ 2 := by positivity
      have hM := P.maxMass_pos
      calc ‖x q‖ = (2 * P.maxMass / (g ^ 2 * ((T : ℝ) + 1) ^ 2)) *
            (g ^ 2 * ((T : ℝ) + 1) ^ 2 / (2 * P.maxMass)) * ‖x q‖ := by
            field_simp
        _ ≤ 2 * P.maxMass / (g ^ 2 * ((T : ℝ) + 1) ^ 2) * (kinT eta m P g q * ‖x q‖) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk (norm_nonneg _)) hc
    · rw [maskOp_apply_of_not _ _ h, norm_zero]
      exact norm_nonneg _
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]

end Register

/-! ## The tails of the grid trajectory -/

section Tails

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **The kinetic tails of the grid trajectory** (`lem:grid-tails`, register form). For
`ψ₀ = S u₀ ∈ D(H²)` (`H u₀ = S v₀`), the grid state `ψ_g(s) = e^{-iH_grid s} P ψ₀` (register of
radius `2m`, `m ≥ 8`, a kernel of the class `𝒦_K`), every time `s`, particle `r` and sup-norm
threshold `2 ≤ T ≤ 2m` (`J = ⌊T/2⌋`):
`‖1_{|q_r|∞ > T} A ψ_g(s)‖ ≤ Z_c (26 J m̄ X_b/(T - J + 1)² + √(1378/J) m̄ X_b)` (the potential,
`vGridK_tail` with the a priori shell) `+ m̄ Y₁/(T+1)²` (the flow of `P H ψ₀`) `+ R_g` (the
remainder `r_g = Δ P ψ₀ - P W (1 - P) ψ₀` of `H_grid P ψ₀ - P H ψ₀`). -/
theorem grid_kin_tail_reg (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ} (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (rho₂ rho₄ Blow Cs Bker : ℝ) (hK₄ : 1 ≤ (2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ))
    (hRho₂ : 0 ≤ rho₂) (hRhoScale₂ : rho₂ ^ 2 * ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) = 1)
    (hRho₄ : 0 ≤ rho₄) (hRhoScale₄ : rho₄ ^ 2 * ((2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ)) = 1)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (s : ℝ) (r : Fin eta) (T : ℕ) (hT : 2 ≤ T) (hTm : T ≤ 2 * m) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB sys L Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let S1 : ℝ := ‖molecularH2StateMap eta g v₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * S1
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let M₁ : ℝ := sys.maxMass * (S1 + 2 * Ξ₁)
    let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
    let tl : ℝ → ℝ → ℝ := fun K ρ =>
      (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    let s₀ : ℕ := m / 4
    let Zg : ℝ :=
      Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
    let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
    let cJ : ℝ := gridFlowConst sys L
    let Xb : ℝ := 5 / 3 * Xa + cJ * S0
    let Y₁ : ℝ := 5 / 3 * ((1 + 1 / g ^ 2) * M₁) + cJ * S1
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) rho₄
    let K₂ : ℝ := g * ((2 * m : ℕ) : ℝ)
    let B₂ : ℝ := (2 * sys.maxMass / K₂ ^ 2) * Ξ₁ + Ct M₀ * rho₂
    let t₂ : ℝ := (2 * sys.maxMass / K₂ ^ 2) * B₂
    let N₀ : ℝ := finiteCoulombPhysicalMassConstant sys L Hunit *
      Real.sqrt ((eta * t₂) * (eta * (t₂ + 2 * B₂)))
    let Rg : ℝ := Zg * (formA s₀ m * (t₄ * (1 + 12 * eta * (m : ℝ) ^ 2) + Xa) + 52 * m * t₄) + N₀
    let J : ℕ := T / 2
    let ψ := Ug s (regCoeff m (molecularH2StateMap eta g u₀))
    ‖maskOp (High T r) (wMul (kinT eta m (regParticlesOf sys) g) ψ)‖ ≤
      Zg * (26 * (J : ℝ) * (sys.maxMass * Xb) / (((T - J : ℕ) : ℝ) + 1) ^ 2 +
        Real.sqrt (1378 / (J : ℝ)) * (sys.maxMass * Xb)) +
      sys.maxMass * Y₁ / ((T : ℝ) + 1) ^ 2 + Rg := by
  intro g b S0 S1 Ξ₀ Ξ₁ M₀ M₁ Ct tl s₀ Zg Xa cJ Xb Y₁ t₄ K₂ B₂ t₂ N₀ Rg J ψ
  have hM := sys.one_le_maxMass
  have hM0 : 0 < sys.maxMass := by linarith
  have hb : 0 ≤ b := relB_nonneg sys L Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hZg : 0 ≤ Zg := Zc_nonneg hγ
  have hS0 : 0 ≤ S0 := norm_nonneg _
  have hS1 : 0 ≤ S1 := norm_nonneg _
  have hΞ₀ : 0 ≤ Ξ₀ := add_nonneg (mul_nonneg zero_le_two (norm_nonneg _))
    (mul_nonneg (mul_nonneg zero_le_two hb) hS0)
  have hΞ₁ : 0 ≤ Ξ₁ := add_nonneg (mul_nonneg zero_le_two (norm_nonneg _))
    (mul_nonneg (mul_nonneg zero_le_two hb) hS1)
  have hM₀ : 0 ≤ M₀ := mul_nonneg hM0.le (add_nonneg hS0 (mul_nonneg zero_le_two hΞ₀))
  have hcJ : 0 ≤ cJ := gridFlowConst_nonneg sys hL
  have hg1 : (0 : ℝ) ≤ 1 + 1 / g ^ 2 := by positivity
  have hXa : 0 ≤ Xa := mul_nonneg hg1 hM₀
  have hs₀m : s₀ ≤ m := Nat.div_le_self m 4
  have hs₀1 : 1 ≤ s₀ := by show 1 ≤ m / 4; omega
  have hs₀r : (2 : ℝ) ≤ s₀ := by
    have : 2 ≤ s₀ := by show 2 ≤ m / 4; omega
    exact_mod_cast this
  have hK₄' : 1 ≤ g * (s₀ : ℝ) := hK₄
  have hK₄2g : 2 * g ≤ g * (s₀ : ℝ) := by
    have := mul_le_mul_of_nonneg_left hs₀r hg.le
    linarith
  have hs₀2m : (s₀ : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
    exact_mod_cast (show s₀ ≤ 2 * m by omega)
  have hK₂ : 1 ≤ K₂ := hK₄'.trans (mul_le_mul_of_nonneg_left hs₀2m hg.le)
  have hK₂2g : 2 * g ≤ K₂ := hK₄2g.trans (mul_le_mul_of_nonneg_left hs₀2m hg.le)
  -- the weights of `P ψ₀`, `ψ_g(s)` and `P H ψ₀`
  have hnorm_le : ∀ (x : MolecularFourierH2 eta) (A B : ℝ), ‖molecularH2StateMap eta g x‖ = A →
      ‖coulombFourierKineticH2 sys g x‖ ≤ B → ‖x‖ ≤ sys.maxMass * (A + 2 * B) := by
    intro x A B hx hT'
    refine (h2norm_le sys L x).trans (mul_le_mul_of_nonneg_left ?_ hM0.le)
    show ‖molecularH2StateMap eta g x‖ + 2 * ‖coulombFourierKineticH2 sys g x‖ ≤ A + 2 * B
    rw [hx]
    linarith
  have hu₀_le : ‖u₀‖ ≤ M₀ :=
    hnorm_le u₀ S0 Ξ₀ rfl (kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u₀)
  have hv₀_le : ‖v₀‖ ≤ M₁ :=
    hnorm_le v₀ S1 Ξ₁ rfl (kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC v₀)
  set a₀ := regCoeff m (molecularH2StateMap eta g u₀) with ha₀def
  have ha₀T : ‖wMul wTot a₀‖ ≤ Xa := (norm_wTot_regCoeff_stateMap_le hg u₀).trans
    (mul_le_mul_of_nonneg_left hu₀_le hg1)
  have ha₀W : ‖wMul (wM (regParticlesOf sys)) a₀‖ ≤ Xa :=
    (norm_wM_le_wTot (regParticlesOf sys) _).trans ha₀T
  have ha₀S : ‖a₀‖ ≤ S0 := norm_regCoeff_le _
  have hψW : ‖wMul (wM (regParticlesOf sys)) ψ‖ ≤ Xb := by
    refine (norm_wM_gridFlow_le sys hL hκ.bound (Ug s) (hgcomm s) _).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left ha₀W (by norm_num))
      (mul_le_mul_of_nonneg_left ha₀S hcJ)
  set w₁ := regCoeff m (molecularH2StateMap eta g v₀) with hw₁def
  have hw₁W : ‖wMul (wM (regParticlesOf sys)) w₁‖ ≤ (1 + 1 / g ^ 2) * M₁ :=
    (norm_wM_le_wTot (regParticlesOf sys) _).trans ((norm_wTot_regCoeff_stateMap_le hg v₀).trans
      (mul_le_mul_of_nonneg_left hv₀_le hg1))
  have hw₁S : ‖w₁‖ ≤ S1 := norm_regCoeff_le _
  -- (i) the potential term
  have hJ1 : 1 ≤ J := by show 1 ≤ T / 2; omega
  have hJT : J ≤ T := Nat.div_le_self T 2
  have hV := vGridK_tail (eta := eta) (m := m) (P := regParticlesOf sys)
    (D := (posNucleiOf sys.nuclei).toNucData) hγ hκ.bound J T hJ1 hJT hTm r ψ
  have hshell : ((((T - J : ℕ) : ℝ) + 1) ^ 2) * ‖maskOp (High (T - J) r) ψ‖ ≤
      sys.maxMass * ‖wMul (wM (regParticlesOf sys)) ψ‖ :=
    sq_mul_norm_high_le_gen (regParticlesOf sys) (T - J) r ψ
  have hpos : (0 : ℝ) < (((T - J : ℕ) : ℝ) + 1) ^ 2 := by positivity
  have hhigh : ‖maskOp (High (T - J) r) ψ‖ ≤ sys.maxMass * Xb / (((T - J : ℕ) : ℝ) + 1) ^ 2 := by
    rw [le_div_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left hψW hM0.le
    linarith
  have hT₀ : ‖wMul wTot ψ‖ ≤ sys.maxMass * Xb :=
    (norm_wMul_wTot_le (regParticlesOf sys) ψ).trans (mul_le_mul_of_nonneg_left hψW hM0.le)
  have hVb : ‖maskOp (High T r) (kOp (vGridK eta m (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData κ) ψ)‖ ≤
      Zg * (26 * (J : ℝ) * (sys.maxMass * Xb) / (((T - J : ℕ) : ℝ) + 1) ^ 2 +
        Real.sqrt (1378 / (J : ℝ)) * (sys.maxMass * Xb)) := by
    refine hV.trans ?_
    have h1 : Zg * (26 * J) * ‖maskOp (High (T - J) r) ψ‖ ≤
        Zg * (26 * J) * (sys.maxMass * Xb / (((T - J : ℕ) : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hhigh (mul_nonneg hZg (by positivity))
    have h2 : Zg * Real.sqrt (1378 / J) * ‖wMul wTot ψ‖ ≤
        Zg * Real.sqrt (1378 / J) * (sys.maxMass * Xb) :=
      mul_le_mul_of_nonneg_left hT₀ (mul_nonneg hZg (Real.sqrt_nonneg _))
    have e : Zg * (26 * (J : ℝ) * (sys.maxMass * Xb) / (((T - J : ℕ) : ℝ) + 1) ^ 2 +
        Real.sqrt (1378 / (J : ℝ)) * (sys.maxMass * Xb)) =
        Zg * (26 * J) * (sys.maxMass * Xb / (((T - J : ℕ) : ℝ) + 1) ^ 2) +
          Zg * Real.sqrt (1378 / J) * (sys.maxMass * Xb) := by ring
    rw [e]
    exact add_le_add h1 h2
  -- (ii) the Hamiltonian term: `H_grid P ψ₀ = P H ψ₀ + r_g`
  have hdec := regCoeff_H_eq_grid sys L H hKernel hL m κ u₀
  rw [huv] at hdec
  set rg := Delta eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) κ a₀ -
    regCoeff m (coulombFourierPotentialH2 sys g H (u₀ - molecularH2Truncate (2 * m) u₀))
    with hrgdef
  have hHa₀ : Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ g a₀ =
      w₁ + rg := by
    rw [hw₁def, hdec, hrgdef]
    abel
  -- the shells of the flow of `P H ψ₀`
  have hw₁flow : ‖wMul (wM (regParticlesOf sys)) (Ug s w₁)‖ ≤ Y₁ := by
    refine (norm_wM_gridFlow_le sys hL hκ.bound (Ug s) (hgcomm s) _).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left hw₁W (by norm_num))
      (mul_le_mul_of_nonneg_left hw₁S hcJ)
  have hw₁high : ‖maskOp (High T r) (Ug s w₁)‖ ≤ sys.maxMass * Y₁ / ((T : ℝ) + 1) ^ 2 := by
    have h := sq_mul_norm_high_le_gen (regParticlesOf sys) T r (Ug s w₁)
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hw₁flow hM0.le
    have e : (regParticlesOf sys).maxMass = sys.maxMass := rfl
    rw [e] at h
    linarith
  -- the remainder `r_g`
  have ht₄ : ∀ r', ‖maskOp (High s₀ r') a₀‖ ≤ t₄ := by
    intro r'
    exact (norm_high_regCoeff_le hg s₀ r' _).trans (tails_at_time sys L H hKernel Hunit hL
      hPeriodic hC U hgraph r' (g * (s₀ : ℝ)) rho₄ Blow Cs Bker hK₄' hRho₄ hRhoScale₄ hBlow hCs
      hBker hK₄2g hAmplitude hBkerScale hCsScale u₀ v₀ huv 0 u₀ (h0 _).symm (h0 _).symm).2
  have ht₄0 : 0 ≤ t₄ := (norm_nonneg _).trans (ht₄ r)
  have hΔ := norm_Delta_le (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData hγ
    hs₀1 hs₀m hκ.gridKernel a₀ ht₄0 ht₄ ha₀T
  have hW : ‖regCoeff m (coulombFourierPotentialH2 sys g H (u₀ - molecularH2Truncate (2 * m) u₀))‖
      ≤ N₀ := by
    refine (norm_regCoeff_le _).trans ?_
    have h := backscatter_initial_le sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph (2 * m)
      rho₂ Blow Cs Bker hK₂ hRho₂ hRhoScale₂ hBlow hCs hBker hK₂2g hAmplitude hBkerScale hCsScale
      u₀ v₀ huv
    exact h
  have hrg : ‖rg‖ ≤ Rg := (norm_sub_le _ _).trans (add_le_add hΔ hW)
  -- assembly
  have hkin : wMul (kinT eta m (regParticlesOf sys) g) ψ =
      Ug s (w₁ + rg) - kOp (vGridK eta m (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData κ) ψ := by
    rw [← hHa₀, hgcomm]
    show wMul (kinT eta m (regParticlesOf sys) g) ψ =
      (wMul (kinT eta m (regParticlesOf sys) g) ψ + kOp (vGridK eta m (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData κ) ψ) - kOp (vGridK eta m (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData κ) ψ
    abel
  rw [hkin, map_sub, map_add, map_add]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖maskOp (High T r) (Ug s w₁) + maskOp (High T r) (Ug s rg)‖ ≤
      sys.maxMass * Y₁ / ((T : ℝ) + 1) ^ 2 + Rg := by
    refine (norm_add_le _ _).trans (add_le_add hw₁high ?_)
    refine (norm_maskOp_le _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    exact hrg
  linarith

end Tails

/-! ## The tails at Euclidean thresholds -/

section Arith

lemma inv_le_sqrt_inv {lam : ℝ} (hl : 1 ≤ lam) : 1 / lam ≤ Real.sqrt (1 / lam) := by
  have hlpos : 0 < lam := by linarith
  have h0 : 0 ≤ 1 / lam := (one_div_pos.mpr hlpos).le
  have h1 : 1 / lam ≤ 1 := by rw [div_le_one hlpos]; exact hl
  calc 1 / lam = Real.sqrt ((1 / lam) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (1 / lam) := Real.sqrt_le_sqrt (by nlinarith)

/-- **The arithmetic of `lem:grid-tails`.** At the sup-norm threshold `T` with
`λ ≤ 2g(T+1)`, `4g ≤ λ`, `1 ≤ λ ≤ K`, the bound of `grid_kin_tail_reg` is at most
`(Z_c m̄ X_b (104 g + √(11024 g)) + 4 g² m̄ Y₁ + c_R) λ^{-1/2}` when `R_g ≤ c_R K^{-1/2}`. -/
lemma grid_tail_arith {Zg mm Xb Y₁ Rg cR g lam K : ℝ} {T : ℕ} (hZg : 0 ≤ Zg) (hmm : 0 ≤ mm)
    (hXb : 0 ≤ Xb) (hY₁ : 0 ≤ Y₁) (hg : 0 < g) (hl1 : 1 ≤ lam) (hlK : lam ≤ K) (hT2 : 2 ≤ T)
    (hTl : lam ≤ 2 * g * ((T : ℝ) + 1)) (hl4 : 4 * g ≤ lam) (hcR : 0 ≤ cR)
    (hRg : Rg ≤ cR * Real.sqrt (1 / K)) :
    Zg * (26 * ((T / 2 : ℕ) : ℝ) * (mm * Xb) / (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2 +
        Real.sqrt (1378 / ((T / 2 : ℕ) : ℝ)) * (mm * Xb)) + mm * Y₁ / ((T : ℝ) + 1) ^ 2 + Rg ≤
      (Zg * (mm * Xb) * (104 * g + Real.sqrt (11024 * g)) + 4 * g ^ 2 * (mm * Y₁) + cR) *
        Real.sqrt (1 / lam) := by
  set J := T / 2 with hJdef
  have hlpos : 0 < lam := by linarith
  have hsq := inv_le_sqrt_inv hl1
  have hs0 : 0 ≤ Real.sqrt (1 / lam) := Real.sqrt_nonneg _
  have hmX : 0 ≤ mm * Xb := mul_nonneg hmm hXb
  have hJ1 : 1 ≤ J := by omega
  have hJT : J ≤ T := Nat.div_le_self T 2
  have h2J : 2 * J ≤ T := by omega
  have hT2J : T ≤ 2 * J + 1 := by omega
  have hJr1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have h2Jr : 2 * (J : ℝ) ≤ T := by exact_mod_cast h2J
  have hT2Jr : (T : ℝ) ≤ 2 * J + 1 := by exact_mod_cast hT2J
  set X : ℝ := ((T - J : ℕ) : ℝ) + 1 with hXdef
  have hXe : X = (T : ℝ) - J + 1 := by rw [hXdef, Nat.cast_sub hJT]
  have hJX : (J : ℝ) ≤ X := by rw [hXe]; linarith
  have hXpos : 0 < X := by linarith
  have hlX : lam ≤ 4 * g * X := by
    rw [hXe]
    nlinarith
  -- (a) the shell term of the potential
  have ha : 26 * (J : ℝ) * (mm * Xb) / X ^ 2 ≤ 104 * g * (mm * Xb) * Real.sqrt (1 / lam) := by
    have h1 : 26 * (J : ℝ) / X ^ 2 ≤ 104 * g / lam := by
      rw [div_le_div_iff₀ (by positivity) hlpos]
      have h2 : 26 * (J : ℝ) * lam ≤ 26 * X * (4 * g * X) := by
        have := mul_le_mul hJX hlX hlpos.le hXpos.le
        nlinarith
      nlinarith
    have h3 : 104 * g / lam ≤ 104 * g * Real.sqrt (1 / lam) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    have e : 26 * (J : ℝ) * (mm * Xb) / X ^ 2 = 26 * (J : ℝ) / X ^ 2 * (mm * Xb) := by ring
    rw [e]
    calc 26 * (J : ℝ) / X ^ 2 * (mm * Xb) ≤ 104 * g * Real.sqrt (1 / lam) * (mm * Xb) :=
          mul_le_mul_of_nonneg_right (h1.trans h3) hmX
      _ = 104 * g * (mm * Xb) * Real.sqrt (1 / lam) := by ring
  -- (b) the weight term of the potential
  have hb : Real.sqrt (1378 / (J : ℝ)) * (mm * Xb) ≤
      Real.sqrt (11024 * g) * (mm * Xb) * Real.sqrt (1 / lam) := by
    have hlJ : lam ≤ 8 * g * J := by nlinarith
    have h1 : 1378 / (J : ℝ) ≤ 11024 * g * (1 / lam) := by
      rw [div_le_iff₀ (by linarith), mul_one_div, mul_comm, ← mul_div_assoc, le_div_iff₀ hlpos]
      nlinarith
    have h2 : Real.sqrt (1378 / (J : ℝ)) ≤ Real.sqrt (11024 * g) * Real.sqrt (1 / lam) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt h1
    calc Real.sqrt (1378 / (J : ℝ)) * (mm * Xb) ≤
          Real.sqrt (11024 * g) * Real.sqrt (1 / lam) * (mm * Xb) :=
          mul_le_mul_of_nonneg_right h2 hmX
      _ = Real.sqrt (11024 * g) * (mm * Xb) * Real.sqrt (1 / lam) := by ring
  -- (c) the flow of `P H ψ₀`
  have hc : mm * Y₁ / ((T : ℝ) + 1) ^ 2 ≤ 4 * g ^ 2 * (mm * Y₁) * Real.sqrt (1 / lam) := by
    have hT1 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have h1 : 1 / ((T : ℝ) + 1) ^ 2 ≤ 4 * g ^ 2 * (1 / lam) := by
      rw [div_le_iff₀ (by positivity)]
      have h2 : lam ^ 2 ≤ (2 * g * ((T : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ hlpos.le hTl 2
      have h3 : lam ≤ lam ^ 2 := by nlinarith
      have e : 4 * g ^ 2 * (1 / lam) * ((T : ℝ) + 1) ^ 2 = (2 * g * ((T : ℝ) + 1)) ^ 2 / lam := by
        field_simp
        ring
      rw [e, le_div_iff₀ hlpos]
      linarith
    have h4 : 1 / ((T : ℝ) + 1) ^ 2 ≤ 4 * g ^ 2 * Real.sqrt (1 / lam) :=
      h1.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
    have hmY : 0 ≤ mm * Y₁ := mul_nonneg hmm hY₁
    calc mm * Y₁ / ((T : ℝ) + 1) ^ 2 = (mm * Y₁) * (1 / ((T : ℝ) + 1) ^ 2) := by ring
      _ ≤ (mm * Y₁) * (4 * g ^ 2 * Real.sqrt (1 / lam)) := mul_le_mul_of_nonneg_left h4 hmY
      _ = 4 * g ^ 2 * (mm * Y₁) * Real.sqrt (1 / lam) := by ring
  -- (d) the remainder
  have hd : Rg ≤ cR * Real.sqrt (1 / lam) := by
    refine hRg.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hcR)
    exact one_div_le_one_div_of_le hlpos hlK
  have e : (Zg * (mm * Xb) * (104 * g + Real.sqrt (11024 * g)) + 4 * g ^ 2 * (mm * Y₁) + cR) *
      Real.sqrt (1 / lam) = Zg * (104 * g * (mm * Xb) * Real.sqrt (1 / lam) +
        Real.sqrt (11024 * g) * (mm * Xb) * Real.sqrt (1 / lam)) +
      4 * g ^ 2 * (mm * Y₁) * Real.sqrt (1 / lam) + cR * Real.sqrt (1 / lam) := by ring
  rw [e]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (add_le_add ha hb) hZg) hc) hd

/-- **The remainder of `H_grid P ψ₀ - P H ψ₀`, rate.** With `ρ = K^{-1/2}`, `K = g m`,
`m ≥ 8`, `K ≥ 8`, and the tails of `ψ₀` at `2K` and `g⌊m/4⌋`:
`R_g ≤ c_R ρ` with
`c_R = Z_c (c_F (β₄ + 12 η β₄/g² + X_a) + 52 β₄/g) + C η (2m̄Ξ₁ + C₀) √(2m̄(2m̄+2))`. -/
lemma grid_Rg_rate {η mm Ξ₁ C₀ Cm g Zg Xa : ℝ} {m : ℕ} (hη : 0 ≤ η) (hmm : 1 ≤ mm)
    (hΞ₁ : 0 ≤ Ξ₁) (hC₀ : 0 ≤ C₀) (hCm : 0 ≤ Cm) (hg : 0 < g) (hm : 8 ≤ m) (hK : 8 ≤ g * m)
    (hZg : 0 ≤ Zg) (hXa : 0 ≤ Xa) :
    let K : ℝ := g * m
    let tl : ℝ → ℝ → ℝ := fun K ρ => (2 * mm / K ^ 2) * ((2 * mm / K ^ 2) * Ξ₁ + C₀ * ρ)
    let ρ₂ : ℝ := Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))
    let ρ₄ : ℝ := Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))
    let s₀ : ℕ := m / 4
    let K₂ : ℝ := g * ((2 * m : ℕ) : ℝ)
    let B₂ : ℝ := (2 * mm / K₂ ^ 2) * Ξ₁ + C₀ * ρ₂
    let t₂ : ℝ := (2 * mm / K₂ ^ 2) * B₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) ρ₄
    let N₀ : ℝ := Cm * Real.sqrt ((η * t₂) * (η * (t₂ + 2 * B₂)))
    let β₄ : ℝ := 128 * mm * (128 * mm * Ξ₁ + 8 * C₀)
    let cF : ℝ := 4 * Real.sqrt (5512 * g)
    Zg * (formA s₀ m * (t₄ * (1 + 12 * η * (m : ℝ) ^ 2) + Xa) + 52 * m * t₄) + N₀ ≤
      (Zg * (cF * (β₄ + 12 * η * β₄ / g ^ 2 + Xa) + 52 * β₄ / g) +
        Cm * η * (2 * mm * Ξ₁ + C₀) * Real.sqrt (2 * mm * (2 * mm + 2))) * Real.sqrt (1 / K) := by
  intro K tl ρ₂ ρ₄ s₀ K₂ B₂ t₂ t₄ N₀ β₄ cF
  set ρ := Real.sqrt (1 / K) with hρdef
  have hmm0 : 0 ≤ mm := by linarith
  have hKpos : 0 < K := by show 0 < g * (m : ℝ); linarith
  have hK1 : 1 ≤ K := by show 1 ≤ g * (m : ℝ); linarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = 1 / K := Real.sq_sqrt (one_div_nonneg.mpr hKpos.le)
  have hρK : ρ ^ 2 * K = 1 := by rw [hρ2]; exact one_div_mul_cancel hKpos.ne'
  have hρK' : ρ ^ 2 * (g * (m : ℝ)) = 1 := hρK
  have hρ1 : ρ ≤ 1 := by
    have h5 : ρ ^ 2 ≤ 1 := by
      rw [hρ2, div_le_one hKpos]
      exact hK1
    exact (pow_le_one_iff_of_nonneg hρ0 two_ne_zero).mp h5
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hmρ : (m : ℝ) * ρ ^ 2 = 1 / g := by
    field_simp
    linarith
  -- the cube `2m` and the threshold `⌊m/4⌋`
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hK₂pos : 0 < K₂ := by show 0 < g * ((2 * m : ℕ) : ℝ); rw [h2m]; positivity
  have hK₂1 : 1 ≤ K₂ := by
    show 1 ≤ g * ((2 * m : ℕ) : ℝ)
    rw [h2m]
    nlinarith
  have hρ₂0 : 0 ≤ ρ₂ := Real.sqrt_nonneg _
  have hρ₂K : ρ₂ ^ 2 * K₂ = 1 := by
    show Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (one_div_nonneg.mpr hK₂pos.le)]
    exact one_div_mul_cancel hK₂pos.ne'
  have hρ₂ρ : ρ₂ ≤ ρ := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hK₂pos hKpos]
    show 1 * (g * (m : ℝ)) ≤ 1 * (g * ((2 * m : ℕ) : ℝ))
    rw [h2m]
    nlinarith
  have hs0 : (0 : ℝ) < ((m / 4 : ℕ) : ℝ) := by
    have : 0 < m / 4 := by omega
    exact_mod_cast this
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hK₄pos : 0 < g * ((m / 4 : ℕ) : ℝ) := mul_pos hg hs0
  have hK₄ : K ≤ 8 * (g * (s₀ : ℝ)) := by
    show g * (m : ℝ) ≤ 8 * (g * ((m / 4 : ℕ) : ℝ))
    calc g * (m : ℝ) ≤ g * (8 * ((m / 4 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hs hg.le
      _ = 8 * (g * ((m / 4 : ℕ) : ℝ)) := by ring
  have hρ₄0 : 0 ≤ ρ₄ := Real.sqrt_nonneg _
  have hρ₄K : ρ₄ ^ 2 * (g * (s₀ : ℝ)) = 1 := by
    show Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ))) ^ 2 * (g * ((m / 4 : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (one_div_nonneg.mpr hK₄pos.le)]
    exact one_div_mul_cancel hK₄pos.ne'
  have hβ₄0 : 0 ≤ β₄ := mul_nonneg (mul_nonneg (by norm_num) hmm0)
    (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hmm0) hΞ₁) (mul_nonneg (by norm_num) hC₀))
  have ht₄ : t₄ ≤ β₄ * ρ ^ 5 := by
    have h := tl_rate (c := 8) hmm0 hΞ₁ hC₀ (by norm_num) hρ0 hρK hK1 hK₄ hρ₄0 hρ₄K
    have e : 2 * mm * 8 ^ 2 * (2 * mm * 8 ^ 2 * Ξ₁ + 8 * C₀) * ρ ^ 5 = β₄ * ρ ^ 5 := by
      show _ = 128 * mm * (128 * mm * Ξ₁ + 8 * C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have ht₄0 : 0 ≤ t₄ := by
    show 0 ≤ (2 * mm / (g * (s₀ : ℝ)) ^ 2) * ((2 * mm / (g * (s₀ : ℝ)) ^ 2) * Ξ₁ + C₀ * ρ₄)
    have h1 : 0 ≤ 2 * mm / (g * (s₀ : ℝ)) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
    exact mul_nonneg h1 (add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hC₀ hρ₄0))
  have hfA : formA s₀ m ≤ cF * ρ := formA_rate hg hρ0 hm hρK'
  have hfA0 := formA_nonneg s₀ m
  have hcF0 : 0 ≤ cF := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  -- the pieces
  have hρ5 : ρ ^ 5 ≤ ρ := pow_le_of_le_one hρ0 hρ1 (by norm_num)
  have hρ3 : ρ ^ 3 ≤ ρ := pow_le_of_le_one hρ0 hρ1 (by norm_num)
  have hm2 : (m : ℝ) ^ 2 * t₄ ≤ β₄ * ρ / g ^ 2 := by
    have h1 : (m : ℝ) ^ 2 * t₄ ≤ (m : ℝ) ^ 2 * (β₄ * ρ ^ 5) :=
      mul_le_mul_of_nonneg_left ht₄ (sq_nonneg _)
    have e : (m : ℝ) ^ 2 * (β₄ * ρ ^ 5) = β₄ * ((m : ℝ) * ρ ^ 2) ^ 2 * ρ := by ring
    rw [e, hmρ] at h1
    calc (m : ℝ) ^ 2 * t₄ ≤ β₄ * (1 / g) ^ 2 * ρ := h1
      _ = β₄ * ρ / g ^ 2 := by field_simp
  have hm1 : (m : ℝ) * t₄ ≤ β₄ * ρ / g := by
    have h1 : (m : ℝ) * t₄ ≤ (m : ℝ) * (β₄ * ρ ^ 5) := mul_le_mul_of_nonneg_left ht₄ hm0.le
    have e : (m : ℝ) * (β₄ * ρ ^ 5) = β₄ * ((m : ℝ) * ρ ^ 2) * ρ ^ 3 := by ring
    rw [e, hmρ] at h1
    have h2 : β₄ * (1 / g) * ρ ^ 3 ≤ β₄ * (1 / g) * ρ :=
      mul_le_mul_of_nonneg_left hρ3 (mul_nonneg hβ₄0 (one_div_pos.mpr hg).le)
    calc (m : ℝ) * t₄ ≤ β₄ * (1 / g) * ρ := h1.trans h2
      _ = β₄ * ρ / g := by ring
  have hin : t₄ * (1 + 12 * η * (m : ℝ) ^ 2) + Xa ≤ (β₄ + 12 * η * β₄ / g ^ 2) * ρ + Xa := by
    have h1 : t₄ ≤ β₄ * ρ := ht₄.trans (mul_le_mul_of_nonneg_left hρ5 hβ₄0)
    have h2 : 12 * η * ((m : ℝ) ^ 2 * t₄) ≤ 12 * η * (β₄ * ρ / g ^ 2) :=
      mul_le_mul_of_nonneg_left hm2 (mul_nonneg (by norm_num) hη)
    have e1 : t₄ * (1 + 12 * η * (m : ℝ) ^ 2) = t₄ + 12 * η * ((m : ℝ) ^ 2 * t₄) := by ring
    have e2 : (β₄ + 12 * η * β₄ / g ^ 2) * ρ = β₄ * ρ + 12 * η * (β₄ * ρ / g ^ 2) := by ring
    rw [e1, e2]
    linarith
  have hA : formA s₀ m * (t₄ * (1 + 12 * η * (m : ℝ) ^ 2) + Xa) ≤
      cF * (β₄ + 12 * η * β₄ / g ^ 2 + Xa) * ρ := by
    have hin0 : 0 ≤ t₄ * (1 + 12 * η * (m : ℝ) ^ 2) + Xa :=
      add_nonneg (mul_nonneg ht₄0 (add_nonneg zero_le_one
        (mul_nonneg (mul_nonneg (by norm_num) hη) (sq_nonneg _)))) hXa
    have h1 := mul_le_mul hfA hin hin0 (mul_nonneg hcF0 hρ0)
    have h2 : cF * ρ * ((β₄ + 12 * η * β₄ / g ^ 2) * ρ + Xa) ≤
        cF * (β₄ + 12 * η * β₄ / g ^ 2 + Xa) * ρ := by
      have hρρ : ρ * ρ ≤ ρ := mul_le_of_le_one_left hρ0 hρ1
      have hx : 0 ≤ β₄ + 12 * η * β₄ / g ^ 2 := add_nonneg hβ₄0
        (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hη) hβ₄0) (sq_nonneg g))
      have e : cF * ρ * ((β₄ + 12 * η * β₄ / g ^ 2) * ρ + Xa) =
          cF * (β₄ + 12 * η * β₄ / g ^ 2) * (ρ * ρ) + cF * Xa * ρ := by ring
      have e2 : cF * (β₄ + 12 * η * β₄ / g ^ 2 + Xa) * ρ =
          cF * (β₄ + 12 * η * β₄ / g ^ 2) * ρ + cF * Xa * ρ := by ring
      rw [e, e2]
      have := mul_le_mul_of_nonneg_left hρρ (mul_nonneg hcF0 hx)
      linarith
    exact h1.trans h2
  -- the Galerkin source at the register cube
  obtain ⟨-, -, -, -, -, hsqrt⟩ := tail_rate_pieces (e := η) (m := mm) (X := Ξ₁) (c := C₀)
    (ρ := ρ₂) (K := K₂) (B := B₂) (tK := t₂) hη hmm hΞ₁ hC₀ hρ₂0 hρ₂K hK₂1 rfl rfl
  have hN : N₀ ≤ Cm * η * (2 * mm * Ξ₁ + C₀) * Real.sqrt (2 * mm * (2 * mm + 2)) * ρ := by
    have h1 : N₀ ≤ Cm * (η * (2 * mm * Ξ₁ + C₀) * ρ₂ ^ 3 * Real.sqrt (2 * mm * (2 * mm + 2))) :=
      mul_le_mul_of_nonneg_left hsqrt hCm
    have h2 : ρ₂ ^ 3 ≤ ρ :=
      (pow_le_pow_left₀ hρ₂0 hρ₂ρ 3).trans hρ3
    have h3 : 0 ≤ Cm * (η * (2 * mm * Ξ₁ + C₀)) * Real.sqrt (2 * mm * (2 * mm + 2)) :=
      mul_nonneg (mul_nonneg hCm (mul_nonneg hη (add_nonneg (mul_nonneg (by linarith) hΞ₁) hC₀)))
        (Real.sqrt_nonneg _)
    calc N₀ ≤ Cm * (η * (2 * mm * Ξ₁ + C₀) * ρ₂ ^ 3 * Real.sqrt (2 * mm * (2 * mm + 2))) := h1
      _ = Cm * (η * (2 * mm * Ξ₁ + C₀)) * Real.sqrt (2 * mm * (2 * mm + 2)) * ρ₂ ^ 3 := by ring
      _ ≤ Cm * (η * (2 * mm * Ξ₁ + C₀)) * Real.sqrt (2 * mm * (2 * mm + 2)) * ρ :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = Cm * η * (2 * mm * Ξ₁ + C₀) * Real.sqrt (2 * mm * (2 * mm + 2)) * ρ := by ring
  have h52 : 52 * (m : ℝ) * t₄ ≤ 52 * β₄ / g * ρ := by
    have := mul_le_mul_of_nonneg_left hm1 (by norm_num : (0 : ℝ) ≤ 52)
    calc 52 * (m : ℝ) * t₄ = 52 * ((m : ℝ) * t₄) := by ring
      _ ≤ 52 * (β₄ * ρ / g) := this
      _ = 52 * β₄ / g * ρ := by ring
  have hZ := mul_le_mul_of_nonneg_left (add_le_add hA h52) hZg
  have e : (Zg * (cF * (β₄ + 12 * η * β₄ / g ^ 2 + Xa) + 52 * β₄ / g) +
      Cm * η * (2 * mm * Ξ₁ + C₀) * Real.sqrt (2 * mm * (2 * mm + 2))) * ρ =
      Zg * (cF * (β₄ + 12 * η * β₄ / g ^ 2 + Xa) * ρ + 52 * β₄ / g * ρ) +
        Cm * η * (2 * mm * Ξ₁ + C₀) * Real.sqrt (2 * mm * (2 * mm + 2)) * ρ := by ring
  rw [e]
  exact add_le_add hZ hN

end Arith

/-- The constant `D_g` of `lem:grid-tails` for the data norms `‖ψ₀‖ = s0`, `‖H ψ₀‖ = hu`,
`‖H ψ₀‖ = hs` (the decoded state of `H ψ₀`) and `‖H² ψ₀‖ = hv`; it does not depend on the
register, the kernel, the time or the threshold. -/
noncomputable def gridTailConst (sys : CoulombSystem eta ν) (L Hunit Blow Cs Bker : ℝ)
    (s0 hu hs hv : ℝ) : ℝ :=
  let g : ℝ := 2 * Real.pi / L
  let b : ℝ := relB sys L Hunit
  let Ξ₀ : ℝ := 2 * hu + 2 * b * s0
  let Ξ₁ : ℝ := 2 * hv + 2 * b * hs
  let M₀ : ℝ := sys.maxMass * (s0 + 2 * Ξ₀)
  let M₁ : ℝ := sys.maxMass * (hs + 2 * Ξ₁)
  let C₀ : ℝ := finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M₀
  let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
  let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
  let cJ : ℝ := gridFlowConst sys L
  let Xb : ℝ := 5 / 3 * Xa + cJ * s0
  let Y₁ : ℝ := 5 / 3 * ((1 + 1 / g ^ 2) * M₁) + cJ * hs
  let β₄ : ℝ := 128 * sys.maxMass * (128 * sys.maxMass * Ξ₁ + 8 * C₀)
  let cF : ℝ := 4 * Real.sqrt (5512 * g)
  let cR : ℝ := Zg * (cF * (β₄ + 12 * eta * β₄ / g ^ 2 + Xa) + 52 * β₄ / g) +
    finiteCoulombPhysicalMassConstant sys L Hunit * eta * (2 * sys.maxMass * Ξ₁ + C₀) *
      Real.sqrt (2 * sys.maxMass * (2 * sys.maxMass + 2))
  Zg * (sys.maxMass * Xb) * (104 * g + Real.sqrt (11024 * g)) +
    4 * g ^ 2 * (sys.maxMass * Y₁) + cR

section Euclid

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **`lem:grid-tails`** (Euclidean thresholds). For `ψ₀ = S u₀ ∈ D(H²)` (`H u₀ = S v₀`), the grid
state `ψ_g(s) = e^{-iH_grid s} P ψ₀` (register of radius `2m`, `m ≥ 8`, `K = g m ≥ 8`, a kernel
of the class `𝒦_K`), every time `s`, particle `r` and threshold `λ` with `1 ≤ λ`, `4g ≤ λ ≤ K`:
`‖1_{|k_r| > λ} A ψ̂_g(s)‖ ≤ D_g λ^{-1/2}` and `‖1_{|k_r| > λ} ψ̂_g(s)‖ ≤ (8 m̄/λ²) D_g λ^{-1/2}`
(as continuum tails of the zero extension), with `D_g = gridTailConst`, uniformly in `s`. -/
theorem grid_kin_tail_euclid (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (Blow Cs Bker : ℝ) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (s : ℝ) (r : Fin eta) {lam : ℝ} (hl1 : 1 ≤ lam) (hl4 : 4 * (2 * Real.pi / L) ≤ lam)
    (hlK : lam ≤ (2 * Real.pi / L) * m) :
    let g : ℝ := 2 * Real.pi / L
    let D := gridTailConst sys L Hunit Blow Cs Bker ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖
    let ψ := Ug s (regCoeff m (molecularH2StateMap eta g u₀))
    ‖tailMask g lam r (regEmb m (wMul (kinT eta m (regParticlesOf sys) g) ψ))‖ ≤
        D * Real.sqrt (1 / lam) ∧
      ‖tailMask g lam r (regEmb m ψ)‖ ≤ 8 * sys.maxMass / lam ^ 2 * (D * Real.sqrt (1 / lam)) := by
  intro g D ψ
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hlpos : 0 < lam := by linarith
  -- the sup-norm threshold `T = ⌊λ/(2g)⌋`
  set T := ⌊lam / (2 * g)⌋₊ with hTdef
  have h2g : 0 < 2 * g := by linarith
  have hT2 : 2 ≤ T := by
    apply Nat.le_floor
    rw [le_div_iff₀ h2g]
    push_cast
    linarith
  have hTle : (T : ℝ) ≤ lam / (2 * g) := Nat.floor_le (div_nonneg hlpos.le h2g.le)
  have hTlt : lam / (2 * g) < (T : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2gT : 2 * g * T ≤ lam := by
    rw [le_div_iff₀ h2g] at hTle
    linarith
  have hTl : lam ≤ 2 * g * ((T : ℝ) + 1) := by
    rw [div_lt_iff₀ h2g] at hTlt
    linarith
  have hTm : T ≤ 2 * m := by
    have h1 : (T : ℝ) ≤ 2 * m := by
      have : lam / (2 * g) ≤ (m : ℝ) / 2 := by
        rw [div_le_iff₀ h2g]
        have e : (m : ℝ) / 2 * (2 * g) = g * m := by ring
        rw [e]
        exact hlK
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact_mod_cast h1
  -- the register bound and its rate
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hK' : (8 : ℝ) ≤ g * (m : ℝ) := hK
  have hK₄ : 1 ≤ g * ((m / 4 : ℕ) : ℝ) := by
    have : g * (m : ℝ) ≤ 8 * (g * ((m / 4 : ℕ) : ℝ)) := by
      calc g * (m : ℝ) ≤ g * (8 * ((m / 4 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hs hg.le
        _ = 8 * (g * ((m / 4 : ℕ) : ℝ)) := by ring
    linarith
  have hK₂pos : 0 < g * ((2 * m : ℕ) : ℝ) := by
    have : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    rw [this]
    linarith
  have hK₄pos : 0 < g * ((m / 4 : ℕ) : ℝ) := by linarith
  have hscale : ∀ X : ℝ, 0 < X → Real.sqrt (1 / X) ^ 2 * X = 1 := by
    intro X hX
    rw [Real.sq_sqrt (one_div_nonneg.mpr hX.le)]
    exact one_div_mul_cancel hX.ne'
  have h := grid_kin_tail_reg sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph m hm hκ Ug hgcomm
    (Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))) (Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))) Blow Cs
    Bker hK₄ (Real.sqrt_nonneg _) (hscale _ hK₂pos) (Real.sqrt_nonneg _) (hscale _ hK₄pos) hBlow
    hCs hBker hAmplitude hBkerScale hCsScale u₀ v₀ huv s r T hT2 hTm
  dsimp only at h
  -- the nonnegative data
  have hS0 : 0 ≤ ‖molecularH2StateMap eta g u₀‖ := norm_nonneg _
  have hS1 : 0 ≤ ‖molecularH2StateMap eta g v₀‖ := norm_nonneg _
  have hΞ₀ : 0 ≤ 2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖ :=
    add_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) (mul_nonneg (mul_nonneg zero_le_two hb) hS0)
  have hΞ₁ : 0 ≤ 2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖ :=
    add_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) (mul_nonneg (mul_nonneg zero_le_two hb) hS1)
  have hM₀ : 0 ≤ sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖)) :=
    mul_nonneg (by linarith) (add_nonneg hS0 (mul_nonneg zero_le_two hΞ₀))
  have hM₁ : 0 ≤ sys.maxMass * (‖molecularH2StateMap eta g v₀‖ +
      2 * (2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖)) :=
    mul_nonneg (by linarith) (add_nonneg hS1 (mul_nonneg zero_le_two hΞ₁))
  have hC₀ := finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM₀
  have hZg : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg hγ
  have hcJ : 0 ≤ gridFlowConst sys L := gridFlowConst_nonneg sys hL
  have hg1 : (0 : ℝ) ≤ 1 + 1 / g ^ 2 := by positivity
  have hXa : 0 ≤ (1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))) :=
    mul_nonneg hg1 hM₀
  have hXb : 0 ≤ 5 / 3 * ((1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖)))) +
      gridFlowConst sys L * ‖molecularH2StateMap eta g u₀‖ :=
    add_nonneg (mul_nonneg (by norm_num) hXa) (mul_nonneg hcJ hS0)
  have hY₁ : 0 ≤ 5 / 3 * ((1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g v₀‖ +
      2 * (2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖)))) +
      gridFlowConst sys L * ‖molecularH2StateMap eta g v₀‖ :=
    add_nonneg (mul_nonneg (by norm_num) (mul_nonneg hg1 hM₁)) (mul_nonneg hcJ hS1)
  have hR := grid_Rg_rate (η := (eta : ℝ)) (mm := sys.maxMass)
    (Ξ₁ := 2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖)
    (C₀ := finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
      (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
        2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))))
    (Cm := finiteCoulombPhysicalMassConstant sys L Hunit) (g := g)
    (Zg := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L))
    (Xa := (1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))))
    (m := m) (Nat.cast_nonneg eta) hM hΞ₁ hC₀ hC hg hm hK hZg hXa
  dsimp only at hR
  have hcR0 : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) * (4 * Real.sqrt (5512 * g) *
        (128 * sys.maxMass * (128 * sys.maxMass *
          (2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖) +
          8 * finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
            (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
              2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖)))) +
        12 * eta * (128 * sys.maxMass * (128 * sys.maxMass *
          (2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖) +
          8 * finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
            (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
              2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))))) /
          g ^ 2 + (1 + 1 / g ^ 2) * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
            2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖)))) +
        52 * (128 * sys.maxMass * (128 * sys.maxMass *
          (2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖) +
          8 * finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
            (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
              2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖))))) / g) +
      finiteCoulombPhysicalMassConstant sys L Hunit * eta *
        (2 * sys.maxMass * (2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖) +
          finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
            (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
              2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖)))) *
        Real.sqrt (2 * sys.maxMass * (2 * sys.maxMass + 2)) := by
    have hβ₄ : 0 ≤ 128 * sys.maxMass * (128 * sys.maxMass *
        (2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖) +
        8 * finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
          (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
            2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g u₀‖)))) :=
      mul_nonneg (by linarith) (add_nonneg (mul_nonneg (by linarith) hΞ₁)
        (mul_nonneg (by norm_num) hC₀))
    refine add_nonneg (mul_nonneg hZg (add_nonneg (mul_nonneg (by positivity)
      (add_nonneg (add_nonneg hβ₄ (div_nonneg (mul_nonneg (by positivity) hβ₄) (sq_nonneg g)))
        hXa)) (div_nonneg (mul_nonneg (by norm_num) hβ₄) hg.le))) ?_
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _))
      (add_nonneg (mul_nonneg (by linarith) hΞ₁) hC₀)) (Real.sqrt_nonneg _)
  have harith := grid_tail_arith (lam := lam) (K := g * m) (mm := sys.maxMass) hZg (by linarith)
    hXb hY₁ hg hl1 hlK hT2 hTl hl4 hcR0 hR
  have hkin : ‖maskOp (High T r) (wMul (kinT eta m (regParticlesOf sys) g) ψ)‖ ≤
      D * Real.sqrt (1 / lam) := h.trans harith
  refine ⟨(norm_tailMask_regEmb_le hg h2gT r _).trans hkin, ?_⟩
  refine (norm_tailMask_regEmb_le hg h2gT r ψ).trans ?_
  refine (norm_high_le_kinT (regParticlesOf sys) hg T r ψ).trans ?_
  have hw : 2 * (regParticlesOf sys).maxMass / (g ^ 2 * ((T : ℝ) + 1) ^ 2) ≤
      8 * sys.maxMass / lam ^ 2 := by
    have e : (regParticlesOf sys).maxMass = sys.maxMass := rfl
    rw [e, div_le_div_iff₀ (mul_pos (pow_pos hg 2) (by positivity)) (pow_pos hlpos 2)]
    have h1 : lam ^ 2 ≤ (2 * g * ((T : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ hlpos.le hTl 2
    have h2 : 2 * sys.maxMass * lam ^ 2 ≤ 2 * sys.maxMass * (2 * g * ((T : ℝ) + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    calc 2 * sys.maxMass * lam ^ 2 ≤ 2 * sys.maxMass * (2 * g * ((T : ℝ) + 1)) ^ 2 := h2
      _ = 8 * sys.maxMass * (g ^ 2 * ((T : ℝ) + 1) ^ 2) := by ring
  exact mul_le_mul hw hkin (norm_nonneg _) (div_nonneg (by linarith) (sq_nonneg lam))

end Euclid

end PlaneWaveKinetic

end DevK9
-- END SOURCE dev/DevK9.lean

-- BEGIN SOURCE dev/DevK10.lean
-- SHA256 b54d885f5b44f9c7303745c13299e5b17c6e2076a744418b4f70145907c87a9a
section DevK10

/-!
# Capped kinetic observable under the grid evolution: `thm:mult-cap` (grid) for a fixed cap

The grid state `ψ_g(t)` lives on the register; its `H²` lift `l = regLift ψ_g(t)` (the zero
extension of the weighted register vector) has `S l = ψ_g(t)` and `T l = A ψ_g(t)` on the cube of
radius `2m` (`stateMap_regLift`, `kinetic_regLift`), so the continuum machinery of the capped
Galerkin bound applies to it (`expect_regEmb`, `regExpect_eq_expect`). For a cap `κ` with
`λ₀ ≤ κ ≤ K` (`λ₀ ≥ max(1, 4g)`), split `A_r = μ_κ + (A_r - μ_κ)`:

* (I) the projection term at `2K`, as in `prop:mult-grid`;
* the replacement terms: for `P ψ(t)` from the continuum tails at `κ`, `≤ 2m̄ β² κ^{-3}`, and for
  `ψ_g(t)` from `lem:grid-tails` at `κ`, `≤ 8 m̄ D_g² κ^{-3}` (`expect_le_tails_of_vanish`);
* the capped secular term: the two pairings of the in-band error with `μ_κ v`,
  `v ∈ {P ψ(t), ψ_g(t)}` (`expect_sub_le_pairings`, then `grid_duality`), with the flow budget
  `W = ((5/3)(1 + 2/g²) + c_J) Θ_κ` from capped smearing (`norm_theta_capLift_le`, `lem:capsmear`)
  with the every-threshold tails of both states: `Θ_κ = O(κ^{3/2})`.

`grid_capped_error` is the explicit bound; the rates `c₁ K^{-3} + c₂ κ^{-3} + c₃ t κ^{3/2} K^{-5/2}`
and the optimisation over `κ` are in DevK11.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate lp ENNReal Topology
open Filter Set

namespace PlaneWaveKinetic

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Register vectors as `H²` states -/

section Lift

variable (sys : CoulombSystem eta ν) (g : ℝ) {m : ℕ}

/-- The `H²` lift of a register vector: its weighted version, zero-extended to the lattice. -/
noncomputable def regLift (v : EuclideanSpace ℂ (RCfg eta m)) : MolecularFourierH2 eta :=
  cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm v)

omit [Fintype ν] in
lemma stateMap_regLift (v : EuclideanSpace ℂ (RCfg eta m)) :
    molecularH2StateMap eta g (regLift g v) = regEmb m v := by
  rw [regLift, stateMap_cubeLift, regEmb_eq]

omit [Fintype ν] in
lemma truncate_regLift (v : EuclideanSpace ℂ (RCfg eta m)) :
    molecularH2Truncate (2 * m) (regLift g v) = regLift g v :=
  truncate_cubeLift g (2 * m) _

omit [Fintype ν] in
/-- The register kinetic symbol is the continuum kinetic symbol at the lattice point. -/
lemma kinT_eq_symbol (q : RCfg eta m) :
    kinT eta m (regParticlesOf sys) g q = coulombKineticEnergySymbol sys g (liftCfg q) := by
  unfold kinT wM coulombKineticEnergySymbol
  have e : ∀ i : Fin eta, g ^ 2 * latticeNormSq (liftCfg q i) / sys.mass i =
      g ^ 2 * (nsq (gl (q i)) / (regParticlesOf sys).mass i) := fun i => by
    rw [mul_div_assoc]
    rfl
  rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum]
  ring

omit [Fintype ν] in
/-- On the register the kinetic operator is the multiplier `kinT`. -/
lemma regCoeff_kinetic (u : MolecularFourierH2 eta) :
    regCoeff m (coulombFourierKineticH2 sys g u) =
      wMul (kinT eta m (regParticlesOf sys) g) (regCoeff m (molecularH2StateMap eta g u)) := by
  ext q
  rw [regCoeff_apply, coulombFourierKineticH2_apply, wMul_apply, regCoeff_apply,
    molecularH2StateMap_apply, kinT_eq_symbol]

omit [Fintype ν] in
lemma kinetic_regLift (v : EuclideanSpace ℂ (RCfg eta m)) :
    coulombFourierKineticH2 sys g (regLift g v) =
      regEmb m (wMul (kinT eta m (regParticlesOf sys) g) v) := by
  have htr : molecularH2Truncate (2 * m) (coulombFourierKineticH2 sys g (regLift g v)) =
      coulombFourierKineticH2 sys g (regLift g v) := by
    rw [← kinetic_truncate, truncate_regLift]
  calc coulombFourierKineticH2 sys g (regLift g v)
      = regEmb m (regCoeff m (coulombFourierKineticH2 sys g (regLift g v))) := by
        rw [regEmb_regCoeff, htr]
    _ = regEmb m (wMul (kinT eta m (regParticlesOf sys) g) v) := by
        rw [regCoeff_kinetic, stateMap_regLift, regCoeff_regEmb]

omit [Fintype ν] in
lemma regCoeff_h2 (μ' : KinMult sys g) (u : MolecularFourierH2 eta) :
    regCoeff m (μ'.h2 u) =
      wMul (fun q => μ'.μ (liftCfg q)) (regCoeff m (molecularH2StateMap eta g u)) := by
  ext q
  rw [regCoeff_apply, KinMult.h2_apply, wMul_apply, regCoeff_apply, molecularH2StateMap_apply]

omit [Fintype ν] in
/-- The expectation of a kinetic multiplier in a state supported on the register cube is a
register sum. -/
lemma expect_regEmb (μ' : KinMult sys g) (v : EuclideanSpace ℂ (RCfg eta m)) :
    μ'.expect (regEmb m v) = ∑ q, μ'.μ (liftCfg q) * ‖v q‖ ^ 2 := by
  apply Complex.ofReal_injective
  have hx : molecularH2Truncate (2 * m) (molecularH2StateMap eta g (regLift g v)) =
      molecularH2StateMap eta g (regLift g v) := by
    rw [← stateMap_truncate, truncate_regLift]
  rw [← stateMap_regLift g v, ← μ'.inner_stateMap_h2_self, inner_regCoeff (m := m) _ _ hx,
    regCoeff_h2, stateMap_regLift, regCoeff_regEmb, inner_wMul_self]

omit [Fintype ν] in
/-- The register expectation of `A_r` is the continuum expectation in the zero extension. -/
lemma regExpect_eq_expect (r : Fin eta) (v : EuclideanSpace ℂ (RCfg eta m)) :
    regExpect sys g r v = (regKin sys g r).expect (regEmb m v) := by
  rw [expect_regEmb]
  rfl

omit [Fintype ν] in
lemma norm_kinT_le (hg : 0 < g) (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (kinT eta m (regParticlesOf sys) g) v‖ ≤
      g ^ 2 / 2 * ‖wMul (wM (regParticlesOf sys)) v‖ := by
  have hc : (0 : ℝ) ≤ g ^ 2 / 2 := by positivity
  refine (norm_le_of_pointwise (Y := ((g ^ 2 / 2 : ℝ) : ℂ) • wMul (wM (regParticlesOf sys)) v)
    fun q => ?_).trans ?_
  · have hW := wM_ge_one (regParticlesOf sys) q
    have hk : 0 ≤ kinT eta m (regParticlesOf sys) g q := by
      unfold kinT
      exact mul_nonneg hc (by linarith)
    rw [wMul_apply, PiLp.smul_apply, smul_eq_mul, wMul_apply, norm_mul, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hk,
      Real.norm_of_nonneg hc, Real.norm_of_nonneg (by linarith), ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    unfold kinT
    nlinarith
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]

omit [Fintype ν] in
lemma norm_stateMap_le_theta (y : MolecularFourierH2 eta) :
    ‖molecularH2StateMap eta g y‖ ≤
      ‖molecularH2StateMap eta g y + coulombFourierKineticH2 sys g y‖ := by
  have h := l2_norm_le_of_le (molecularH2StateMap eta g y)
    (molecularH2StateMap eta g y + coulombFourierKineticH2 sys g y) zero_le_one (fun p => by
      rw [one_mul, lp.coeFn_add, Pi.add_apply, molecularH2StateMap_apply,
        coulombFourierKineticH2_apply]
      have hk := coulombKineticEnergySymbol_nonneg sys g p
      have e : molecularH2Coeff g y p + (coulombKineticEnergySymbol sys g p : ℂ) *
          molecularH2Coeff g y p =
          ((1 + coulombKineticEnergySymbol sys g p : ℝ) : ℂ) * molecularH2Coeff g y p := by
        push_cast
        ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      exact le_mul_of_one_le_left (norm_nonneg _) (by linarith))
  rwa [one_mul] at h

omit [Fintype ν] in
/-- The register weight of a state is controlled by its `Θ`-vector:
`‖W P S y‖ ≤ (1 + 2/g²) ‖S y + T y‖`. -/
lemma norm_wM_regCoeff_le (hg : 0 < g) (y : MolecularFourierH2 eta) :
    ‖wMul (wM (regParticlesOf sys)) (regCoeff m (molecularH2StateMap eta g y))‖ ≤
      (1 + 2 / g ^ 2) * ‖molecularH2StateMap eta g y + coulombFourierKineticH2 sys g y‖ := by
  have hc : (0 : ℝ) ≤ 1 + 2 / g ^ 2 := by positivity
  refine (norm_le_of_pointwise (Y := ((1 + 2 / g ^ 2 : ℝ) : ℂ) •
    regCoeff m (molecularH2StateMap eta g y + coulombFourierKineticH2 sys g y))
    fun q => ?_).trans ?_
  · have hk := coulombKineticEnergySymbol_nonneg sys g (liftCfg q)
    have hW : wM (regParticlesOf sys) q =
        1 + 2 / g ^ 2 * coulombKineticEnergySymbol sys g (liftCfg q) := by
      rw [← kinT_eq_symbol]
      unfold kinT
      field_simp
      ring
    rw [wMul_apply, PiLp.smul_apply, smul_eq_mul, regCoeff_apply, regCoeff_apply, lp.coeFn_add,
      Pi.add_apply, molecularH2StateMap_apply, coulombFourierKineticH2_apply, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc, hW,
      Real.norm_of_nonneg (by positivity)]
    have e : molecularH2Coeff g y (liftCfg q) +
        (coulombKineticEnergySymbol sys g (liftCfg q) : ℂ) * molecularH2Coeff g y (liftCfg q) =
        ((1 + coulombKineticEnergySymbol sys g (liftCfg q) : ℝ) : ℂ) *
          molecularH2Coeff g y (liftCfg q) := by
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hg2 : 0 < 2 / g ^ 2 := by positivity
    nlinarith
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (norm_regCoeff_le _) hc

end Lift

/-! ## The capped bound on the grid -/

section Grid

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

set_option maxHeartbeats 400000 in
set_option linter.unusedVariables false in
include hKernel hL hPeriodic in
/-- **`thm:mult-cap` on the grid, for a fixed cap** (Fourier side, explicit form). For
`ψ₀ = S u₀ ∈ D(H²)` (`H u₀ = S v₀`), the grid state `ψ_g(t) = e^{-iH_grid t} P ψ₀` (register of
radius `2m`, `m ≥ 8`, `K = g m ≥ 8`, a kernel of the class `𝒦_K`), a particle `r` and a cap `κ`
with `λ₀ ≤ κ ≤ K` (`λ₀ ≥ 1`, `λ₀ ≥ 4g`):
`|⟨ψ(t), A_r ψ(t)⟩ - ⟨ψ_g(t), A_r ψ_g(t)⟩|`
`≤ (η t₂)(η B₂) + 2m̄ β² κ^{-3} + 8m̄ D_g² κ^{-3} + 2 t B_d`,
with the projection term at `2K`, the two replacement terms, and the pairings of `grid_duality`
at the capped flow budget `W = ((5/3)(1 + 2/g²) + c_J) Θ_κ`,
`Θ_κ = ½ (λ₀² (S0 + Ξ₀ + S0 + (g²/2) X_b) + √15 (D_a + D_b) κ^{3/2})`. -/
theorem grid_capped_error (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κg : Lat3 → ℝ}
    (hκg : IsGridKernel (coulombCellAmplitude L) m κg)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κg
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κg (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κg (2 * Real.pi / L) x))) t)
    (Blow Cs Bker : ℝ) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (r : Fin eta) {κ lam0 : ℝ} (hl : 1 ≤ lam0) (h4g : 4 * (2 * Real.pi / L) ≤ lam0)
    (hlk : lam0 ≤ κ) (hκK : κ ≤ (2 * Real.pi / L) * m) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB sys L Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
    let tl : ℝ → ℝ → ℝ := fun K ρ =>
      (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    let s₀ : ℕ := m / 4
    let Zg : ℝ :=
      Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
    let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
    let cJ : ℝ := gridFlowConst sys L
    let Xb : ℝ := 5 / 3 * Xa + cJ * S0
    let ρ₂ : ℝ := Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))
    let ρ₄ : ℝ := Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))
    let K₂ : ℝ := g * ((2 * m : ℕ) : ℝ)
    let B₂ : ℝ := (2 * sys.maxMass / K₂ ^ 2) * Ξ₁ + Ct M₀ * ρ₂
    let t₂ : ℝ := tl K₂ ρ₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) ρ₄
    let β : ℝ := 2 * sys.maxMass * Ξ₁ + Ct (sys.maxMass * (S0 + 2 * Ξ₀))
    let Dg : ℝ := gridTailConst sys L Hunit Blow Cs Bker S0 ‖H u₀‖
      ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖
    let Da : ℝ := (1 + 2 * sys.maxMass) * β
    let Db : ℝ := (1 + 8 * sys.maxMass) * Dg
    let Θκ : ℝ := (1 / 2 : ℝ) * (lam0 ^ 2 * ((S0 + Ξ₀) + (S0 + g ^ 2 / 2 * Xb)) +
      Real.sqrt 15 * (Da + Db) * (κ * Real.sqrt κ))
    let W : ℝ := (5 / 3 * (1 + 2 / g ^ 2) + cJ) * Θκ
    let τφ : ℝ := sys.maxMass * W / ((s₀ : ℝ) + 1) ^ 2
    let Bd : ℝ := (eta * t₂) * (eta * (Ct ((1 + g ^ 2) * (sys.maxMass * W)) * ρ₂)) +
      Zg * (formA s₀ m * (t₄ * (sys.maxMass * W) + τφ * Xa) + 52 * m * (τφ * t₄))
    let ψg := Ug t (regCoeff m (molecularH2StateMap eta g u₀))
    |(regKin sys g r).expect (U t (molecularH2StateMap eta g u₀)) - regExpect sys g r ψg| ≤
      (eta * t₂) * (eta * B₂) + 2 * sys.maxMass * β ^ 2 * (1 / κ) ^ 3 +
        8 * sys.maxMass * Dg ^ 2 * (1 / κ) ^ 3 + 2 * (Bd * t) := by
  intro g b S0 Ξ₀ Ξ₁ M₀ Ct tl s₀ Zg Xa cJ Xb ρ₂ ρ₄ K₂ B₂ t₂ t₄ β Dg Da Db Θκ W τφ Bd ψg
  have hM := sys.one_le_maxMass
  have hm0 : 0 ≤ sys.maxMass := by linarith
  have hb : 0 ≤ b := relB_nonneg sys L Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hκ1 : 1 ≤ κ := hl.trans hlk
  have hκpos : 0 < κ := by linarith
  have h2g : 2 * g ≤ lam0 := by linarith
  have h2gκ : 2 * g ≤ κ := h2g.trans hlk
  have h4gκ : 4 * g ≤ κ := h4g.trans hlk
  -- the scales of the register
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hK' : (8 : ℝ) ≤ g * (m : ℝ) := hK
  have hK₄ : 1 ≤ g * ((m / 4 : ℕ) : ℝ) := by
    have : g * (m : ℝ) ≤ 8 * (g * ((m / 4 : ℕ) : ℝ)) := by
      calc g * (m : ℝ) ≤ g * (8 * ((m / 4 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hs hg.le
        _ = 8 * (g * ((m / 4 : ℕ) : ℝ)) := by ring
    linarith
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hK₂pos : 0 < g * ((2 * m : ℕ) : ℝ) := by rw [h2m]; linarith
  have hK₄pos : 0 < g * ((m / 4 : ℕ) : ℝ) := by linarith
  have hscale : ∀ X : ℝ, 0 < X → Real.sqrt (1 / X) ^ 2 * X = 1 := by
    intro X hX
    rw [Real.sq_sqrt (one_div_nonneg.mpr hX.le)]
    exact one_div_mul_cancel hX.ne'
  have hRho₂ : 0 ≤ ρ₂ := Real.sqrt_nonneg _
  have hRhoScale₂ : ρ₂ ^ 2 * ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) = 1 := hscale _ hK₂pos
  have hRho₄ : 0 ≤ ρ₄ := Real.sqrt_nonneg _
  have hRhoScale₄ : ρ₄ ^ 2 * ((2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ)) = 1 := hscale _ hK₄pos
  have hK₂ : 1 ≤ K₂ := by show 1 ≤ g * ((2 * m : ℕ) : ℝ); rw [h2m]; linarith
  have hK₂2g : 2 * g ≤ K₂ := by show 2 * g ≤ g * ((2 * m : ℕ) : ℝ); rw [h2m]; linarith
  -- the data
  have hS0 : 0 ≤ S0 := norm_nonneg _
  have h2b : 0 ≤ 2 * b := mul_nonneg zero_le_two hb
  have hΞ₀ : 0 ≤ Ξ₀ := add_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) (mul_nonneg h2b hS0)
  have hΞ₁ : 0 ≤ Ξ₁ := add_nonneg (mul_nonneg zero_le_two (norm_nonneg _))
    (mul_nonneg h2b (norm_nonneg _))
  have hM₀ : 0 ≤ M₀ := mul_nonneg hm0 (add_nonneg hS0 (mul_nonneg zero_le_two hΞ₀))
  have hc0 : 0 ≤ Ct (sys.maxMass * (S0 + 2 * Ξ₀)) :=
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM₀
  have hβ : 0 ≤ β := add_nonneg (mul_nonneg (mul_nonneg zero_le_two hm0) hΞ₁) hc0
  have hcJ : 0 ≤ cJ := gridFlowConst_nonneg sys hL
  have hg1 : (0 : ℝ) ≤ 1 + 1 / g ^ 2 := by positivity
  have hXa : 0 ≤ Xa := mul_nonneg hg1 hM₀
  have hXb : 0 ≤ Xb := add_nonneg (mul_nonneg (by norm_num) hXa) (mul_nonneg hcJ hS0)
  have hg2 : (0 : ℝ) ≤ g ^ 2 / 2 := by positivity
  -- the exact state at time `t`
  obtain ⟨u, hu1, hu2⟩ := hgraph t u₀
  have hψ : U t (molecularH2StateMap eta g u₀) = molecularH2StateMap eta g u := hu1.symm
  have hSu : ‖molecularH2StateMap eta g u‖ = S0 := by
    rw [← hψ, LinearIsometryEquiv.norm_map]
  have hTu : ‖coulombFourierKineticH2 sys g u‖ ≤ Ξ₀ := by
    have h := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u
    rw [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
    exact h
  -- the exact tails at a threshold `λ`
  have hexact : ∀ lam, 1 ≤ lam → 2 * g ≤ lam →
      ‖tailMask g lam r (coulombFourierKineticH2 sys g u)‖ ≤ β * Real.sqrt (1 / lam) ∧
      ‖tailMask g lam r (molecularH2StateMap eta g u)‖ ≤
        (2 * sys.maxMass / lam ^ 2) * (β * Real.sqrt (1 / lam)) := by
    intro lam hlam1 hlam2
    have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam1
    have hρl : Real.sqrt (1 / lam) ^ 2 * lam = 1 := hscale lam hlam0
    have h := tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph r lam
      (Real.sqrt (1 / lam)) Blow Cs Bker hlam1 (Real.sqrt_nonneg _) hρl hBlow hCs hBker hlam2
      hAmplitude hBkerScale hCsScale u₀ v₀ huv t u hu1 hu2
    have hBl : (2 * sys.maxMass / lam ^ 2) * Ξ₁ + Ct (sys.maxMass * (S0 + 2 * Ξ₀)) *
        Real.sqrt (1 / lam) ≤ β * Real.sqrt (1 / lam) := tail_rate_le hm0 hΞ₁ hlam1
    exact ⟨h.1.trans hBl, h.2.trans (mul_le_mul_of_nonneg_left hBl
      (div_nonneg (mul_nonneg zero_le_two hm0) (sq_nonneg lam)))⟩
  -- the grid tails at a threshold `λ`
  set l := regLift g ψg with hldef
  have hSl : molecularH2StateMap eta g l = regEmb m ψg := stateMap_regLift g ψg
  have hTl : coulombFourierKineticH2 sys g l =
      regEmb m (wMul (kinT eta m (regParticlesOf sys) g) ψg) := kinetic_regLift sys g ψg
  have hgrid : ∀ lam, 1 ≤ lam → 4 * g ≤ lam → lam ≤ g * m →
      ‖tailMask g lam r (coulombFourierKineticH2 sys g l)‖ ≤ Dg * Real.sqrt (1 / lam) ∧
      ‖tailMask g lam r (molecularH2StateMap eta g l)‖ ≤
        8 * sys.maxMass / lam ^ 2 * (Dg * Real.sqrt (1 / lam)) := by
    intro lam hlam1 hlam4 hlamK
    rw [hSl, hTl]
    exact grid_kin_tail_euclid sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph m hm hK hκg Ug
      hgcomm Blow Cs Bker hBlow hCs hBker hAmplitude hBkerScale hCsScale u₀ v₀ huv t r hlam1 hlam4
      hlamK
  have hDg : 0 ≤ Dg := by
    have h := (hgrid κ hκ1 h4gκ hκK).1
    have h1 : 0 ≤ Dg * Real.sqrt (1 / κ) := (norm_nonneg _).trans h
    have h2 : 0 < Real.sqrt (1 / κ) := Real.sqrt_pos.mpr (one_div_pos.mpr hκpos)
    exact nonneg_of_mul_nonneg_left h1 h2
  have hDa : 0 ≤ Da := mul_nonneg (add_nonneg zero_le_one (mul_nonneg zero_le_two hm0)) hβ
  have hDb : 0 ≤ Db := mul_nonneg (add_nonneg zero_le_one (mul_nonneg (by norm_num) hm0)) hDg
  -- the weights of `a(t)` and `ψ_g(t)`
  have hnorm_le : ∀ (x : MolecularFourierH2 eta), ‖molecularH2StateMap eta g x‖ = S0 →
      ‖coulombFourierKineticH2 sys g x‖ ≤ Ξ₀ → ‖x‖ ≤ M₀ := by
    intro x hx hT
    refine (h2norm_le sys L x).trans (mul_le_mul_of_nonneg_left ?_ hm0)
    show ‖molecularH2StateMap eta g x‖ + 2 * ‖coulombFourierKineticH2 sys g x‖ ≤ S0 + 2 * Ξ₀
    rw [hx]
    linarith
  have hu₀_le : ‖u₀‖ ≤ M₀ :=
    hnorm_le u₀ rfl (kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u₀)
  have ha₀ : ‖wMul (wM (regParticlesOf sys)) (regCoeff m (molecularH2StateMap eta g u₀))‖ ≤ Xa :=
    (norm_wM_le_wTot (regParticlesOf sys) _).trans ((norm_wTot_regCoeff_stateMap_le hg u₀).trans
      (mul_le_mul_of_nonneg_left hu₀_le hg1))
  have haS₀ : ‖regCoeff m (molecularH2StateMap eta g u₀)‖ ≤ S0 := norm_regCoeff_le _
  have hbT : ‖wMul (wM (regParticlesOf sys)) ψg‖ ≤ Xb := by
    refine (norm_wM_gridFlow_le sys hL hκg.bound (Ug t) (hgcomm t) _).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left ha₀ (by norm_num))
      (mul_le_mul_of_nonneg_left haS₀ hcJ)
  have hbS : ‖ψg‖ ≤ S0 := by
    show ‖Ug t (regCoeff m (molecularH2StateMap eta g u₀))‖ ≤ S0
    rw [LinearIsometryEquiv.norm_map]
    exact haS₀
  -- (I): the projection term at `2K`
  have htl := fun c => tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph c K₂ ρ₂ Blow
    Cs Bker hK₂ hRho₂ hRhoScale₂ hBlow hCs hBker hK₂2g hAmplitude hBkerScale hCsScale u₀ v₀ huv t
    u hu1 hu2
  have hδS : ‖molecularH2StateMap eta g u -
      molecularH2Truncate (2 * m) (molecularH2StateMap eta g u)‖ ≤ eta * t₂ := by
    refine (norm_sub_truncate_le hg (2 * m) _).trans ?_
    calc ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖
        ≤ ∑ _c : Fin eta, t₂ := Finset.sum_le_sum fun c _ => (htl c).2
      _ = eta * t₂ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hδT : ‖coulombFourierKineticH2 sys g u -
      molecularH2Truncate (2 * m) (coulombFourierKineticH2 sys g u)‖ ≤ eta * B₂ := by
    refine (norm_sub_truncate_le hg (2 * m) _).trans ?_
    calc ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (coulombFourierKineticH2 sys g u)‖
        ≤ ∑ _c : Fin eta, B₂ := Finset.sum_le_sum fun c _ => (htl c).1
      _ = eta * B₂ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have ht₂0 : 0 ≤ eta * t₂ := (norm_nonneg _).trans hδS
  have hI : (regKin sys g r).expect (molecularH2StateMap eta g (u - molecularH2Truncate (2 * m) u))
      ≤ (eta * t₂) * (eta * B₂) :=
    ((regKin sys g r).expect_tail_le (2 * m) u).trans (mul_le_mul hδS hδT (norm_nonneg _) ht₂0)
  have hI0 := (regKin sys g r).expect_tail_nonneg (2 * m) u
  -- the replacement terms
  set Pu := molecularH2Truncate (2 * m) u with hPudef
  have hρκκ : Real.sqrt (1 / κ) ^ 2 * κ = 1 := hscale κ hκpos
  have hinvκ : 2 * sys.maxMass / κ ^ 2 * (Real.sqrt (1 / κ) ^ 2) =
      2 * sys.maxMass * (1 / κ) ^ 3 := by
    rw [Real.sq_sqrt (one_div_nonneg.mpr hκpos.le)]
    field_simp
  have hRa : (capRest sys g r κ).expect (molecularH2StateMap eta g Pu) ≤
      2 * sys.maxMass * β ^ 2 * (1 / κ) ^ 3 := by
    have hsplit := (capRest sys g r κ).expect_split (2 * m) u
    have hnn := (capRest sys g r κ).expect_tail_nonneg (2 * m) u
    have hle : (capRest sys g r κ).expect (molecularH2StateMap eta g u) ≤
        2 * sys.maxMass * β ^ 2 * (1 / κ) ^ 3 := by
      refine ((capRest sys g r κ).expect_le_tails_of_vanish r κ
        (capRest_vanish sys g r κ hg.le) u).trans ?_
      obtain ⟨h1, h2⟩ := hexact κ hκ1 h2gκ
      calc ‖tailMask g κ r (molecularH2StateMap eta g u)‖ *
            ‖tailMask g κ r (coulombFourierKineticH2 sys g u)‖
          ≤ ((2 * sys.maxMass / κ ^ 2) * (β * Real.sqrt (1 / κ))) * (β * Real.sqrt (1 / κ)) :=
            mul_le_mul h2 h1 (norm_nonneg _) (mul_nonneg (div_nonneg (mul_nonneg zero_le_two hm0)
              (sq_nonneg κ)) (mul_nonneg hβ (Real.sqrt_nonneg _)))
        _ = β ^ 2 * (2 * sys.maxMass / κ ^ 2 * (Real.sqrt (1 / κ) ^ 2)) := by ring
        _ = 2 * sys.maxMass * β ^ 2 * (1 / κ) ^ 3 := by rw [hinvκ]; ring
    linarith
  have hRa0 := (capRest sys g r κ).expect_nonneg (molecularH2StateMap eta g Pu)
  have hRb : (capRest sys g r κ).expect (molecularH2StateMap eta g l) ≤
      8 * sys.maxMass * Dg ^ 2 * (1 / κ) ^ 3 := by
    refine ((capRest sys g r κ).expect_le_tails_of_vanish r κ
      (capRest_vanish sys g r κ hg.le) l).trans ?_
    obtain ⟨h1, h2⟩ := hgrid κ hκ1 h4gκ hκK
    have hinv8 : 8 * sys.maxMass / κ ^ 2 * (Real.sqrt (1 / κ) ^ 2) =
        8 * sys.maxMass * (1 / κ) ^ 3 := by
      rw [Real.sq_sqrt (one_div_nonneg.mpr hκpos.le)]
      field_simp
    calc ‖tailMask g κ r (molecularH2StateMap eta g l)‖ *
          ‖tailMask g κ r (coulombFourierKineticH2 sys g l)‖
        ≤ (8 * sys.maxMass / κ ^ 2 * (Dg * Real.sqrt (1 / κ))) * (Dg * Real.sqrt (1 / κ)) :=
          mul_le_mul h2 h1 (norm_nonneg _) (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hm0)
            (sq_nonneg κ)) (mul_nonneg hDg (Real.sqrt_nonneg _)))
      _ = Dg ^ 2 * (8 * sys.maxMass / κ ^ 2 * (Real.sqrt (1 / κ) ^ 2)) := by ring
      _ = 8 * sys.maxMass * Dg ^ 2 * (1 / κ) ^ 3 := by rw [hinv8]; ring
  have hRb0 := (capRest sys g r κ).expect_nonneg (molecularH2StateMap eta g l)
  -- the capped smearing of both states
  have hθa : ‖molecularH2StateMap eta g (capLift sys g r κ Pu) +
      coulombFourierKineticH2 sys g (capLift sys g r κ Pu)‖ ≤ Θκ := by
    have htail : ∀ lam, lam0 ≤ lam → lam < κ →
        ‖tailMask g lam r (molecularH2StateMap eta g Pu + coulombFourierKineticH2 sys g Pu)‖ ≤
          Da * Real.sqrt (1 / lam) := by
      intro lam hl0 _
      have hlam1 : 1 ≤ lam := hl.trans hl0
      have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam1
      have e : molecularH2StateMap eta g Pu + coulombFourierKineticH2 sys g Pu =
          molecularH2Truncate (2 * m) (molecularH2StateMap eta g u +
            coulombFourierKineticH2 sys g u) := by
        rw [hPudef, stateMap_truncate, kinetic_truncate, molecularH2Truncate_add]
      rw [e, ← truncate_tailMask]
      refine (molecularH2Truncate_norm_le _ _).trans ?_
      obtain ⟨h1, _⟩ := hexact lam hlam1 (h2g.trans hl0)
      refine (theta_tail_le sys L hlam0 r u h1).trans ?_
      have hw : 1 + 2 * sys.maxMass / lam ^ 2 ≤ 1 + 2 * sys.maxMass := by
        have : 2 * sys.maxMass / lam ^ 2 ≤ 2 * sys.maxMass :=
          div_le_self (mul_nonneg zero_le_two hm0) (one_le_pow₀ hlam1)
        exact add_le_add_right this 1
      calc (1 + 2 * sys.maxMass / lam ^ 2) * (β * Real.sqrt (1 / lam)) ≤
            (1 + 2 * sys.maxMass) * (β * Real.sqrt (1 / lam)) :=
            mul_le_mul_of_nonneg_right hw (mul_nonneg hβ (Real.sqrt_nonneg _))
        _ = Da * Real.sqrt (1 / lam) := by ring
    refine (norm_theta_capLift_le sys L hL r hl hlk hDa Pu htail).trans ?_
    have hn : ‖molecularH2StateMap eta g Pu + coulombFourierKineticH2 sys g Pu‖ ≤ S0 + Ξ₀ := by
      have e : molecularH2StateMap eta g Pu + coulombFourierKineticH2 sys g Pu =
          molecularH2Truncate (2 * m) (molecularH2StateMap eta g u +
            coulombFourierKineticH2 sys g u) := by
        rw [hPudef, stateMap_truncate, kinetic_truncate, molecularH2Truncate_add]
      rw [e]
      refine (molecularH2Truncate_norm_le _ _).trans ((norm_add_le _ _).trans ?_)
      rw [hSu]
      linarith
    have hsq : 0 ≤ lam0 ^ 2 := sq_nonneg _
    have hn2 : 0 ≤ S0 + g ^ 2 / 2 * Xb := add_nonneg hS0 (mul_nonneg hg2 hXb)
    have h15 : 0 ≤ Real.sqrt 15 * (κ * Real.sqrt κ) :=
      mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hκpos.le (Real.sqrt_nonneg _))
    show _ ≤ (1 / 2 : ℝ) * (lam0 ^ 2 * ((S0 + Ξ₀) + (S0 + g ^ 2 / 2 * Xb)) +
      Real.sqrt 15 * (Da + Db) * (κ * Real.sqrt κ))
    have hA : lam0 ^ 2 * ‖molecularH2StateMap eta g Pu + coulombFourierKineticH2 sys g Pu‖ ≤
        lam0 ^ 2 * ((S0 + Ξ₀) + (S0 + g ^ 2 / 2 * Xb)) :=
      mul_le_mul_of_nonneg_left (hn.trans (le_add_of_nonneg_right hn2)) hsq
    have hB : Real.sqrt 15 * Da * (κ * Real.sqrt κ) ≤
        Real.sqrt 15 * (Da + Db) * (κ * Real.sqrt κ) := by
      have h3 := mul_nonneg h15 hDb
      have e : Real.sqrt 15 * (Da + Db) * (κ * Real.sqrt κ) =
          Real.sqrt 15 * Da * (κ * Real.sqrt κ) + Real.sqrt 15 * (κ * Real.sqrt κ) * Db := by ring
      rw [e]
      linarith
    exact mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num)
  have hθb : ‖molecularH2StateMap eta g (capLift sys g r κ l) +
      coulombFourierKineticH2 sys g (capLift sys g r κ l)‖ ≤ Θκ := by
    have htail : ∀ lam, lam0 ≤ lam → lam < κ →
        ‖tailMask g lam r (molecularH2StateMap eta g l + coulombFourierKineticH2 sys g l)‖ ≤
          Db * Real.sqrt (1 / lam) := by
      intro lam hl0 hlκ
      have hlam1 : 1 ≤ lam := hl.trans hl0
      obtain ⟨h1, h2⟩ := hgrid lam hlam1 (h4g.trans hl0) (hlκ.le.trans hκK)
      rw [map_add]
      refine (norm_add_le _ _).trans ?_
      have hw : 8 * sys.maxMass / lam ^ 2 ≤ 8 * sys.maxMass :=
        div_le_self (mul_nonneg (by norm_num) hm0) (one_le_pow₀ hlam1)
      have h3 := mul_le_mul_of_nonneg_right hw (mul_nonneg hDg (Real.sqrt_nonneg (1 / lam)))
      calc ‖tailMask g lam r (molecularH2StateMap eta g l)‖ +
            ‖tailMask g lam r (coulombFourierKineticH2 sys g l)‖
          ≤ 8 * sys.maxMass / lam ^ 2 * (Dg * Real.sqrt (1 / lam)) +
            Dg * Real.sqrt (1 / lam) := add_le_add h2 h1
        _ ≤ 8 * sys.maxMass * (Dg * Real.sqrt (1 / lam)) + Dg * Real.sqrt (1 / lam) := by linarith
        _ = Db * Real.sqrt (1 / lam) := by ring
    refine (norm_theta_capLift_le sys L hL r hl hlk hDb l htail).trans ?_
    have hn : ‖molecularH2StateMap eta g l + coulombFourierKineticH2 sys g l‖ ≤
        S0 + g ^ 2 / 2 * Xb := by
      rw [hSl, hTl, ← map_add, LinearIsometry.norm_map]
      refine (norm_add_le _ _).trans (add_le_add hbS ?_)
      exact (norm_kinT_le sys g hg ψg).trans (mul_le_mul_of_nonneg_left hbT hg2)
    have hsq : 0 ≤ lam0 ^ 2 := sq_nonneg _
    have hn1 : 0 ≤ S0 + Ξ₀ := add_nonneg hS0 hΞ₀
    have h15 : 0 ≤ Real.sqrt 15 * (κ * Real.sqrt κ) :=
      mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hκpos.le (Real.sqrt_nonneg _))
    show _ ≤ (1 / 2 : ℝ) * (lam0 ^ 2 * ((S0 + Ξ₀) + (S0 + g ^ 2 / 2 * Xb)) +
      Real.sqrt 15 * (Da + Db) * (κ * Real.sqrt κ))
    have hA : lam0 ^ 2 * ‖molecularH2StateMap eta g l + coulombFourierKineticH2 sys g l‖ ≤
        lam0 ^ 2 * ((S0 + Ξ₀) + (S0 + g ^ 2 / 2 * Xb)) :=
      mul_le_mul_of_nonneg_left (hn.trans (le_add_of_nonneg_left hn1)) hsq
    have hB : Real.sqrt 15 * Db * (κ * Real.sqrt κ) ≤
        Real.sqrt 15 * (Da + Db) * (κ * Real.sqrt κ) := by
      have h3 := mul_nonneg h15 hDa
      have e : Real.sqrt 15 * (Da + Db) * (κ * Real.sqrt κ) =
          Real.sqrt 15 * Db * (κ * Real.sqrt κ) + Real.sqrt 15 * (κ * Real.sqrt κ) * Da := by ring
      rw [e]
      linarith
    exact mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num)
  -- the flow budgets
  have hWx : ∀ x : MolecularFourierH2 eta,
      ‖molecularH2StateMap eta g (capLift sys g r κ x) +
        coulombFourierKineticH2 sys g (capLift sys g r κ x)‖ ≤ Θκ →
      ∀ τ, ‖wMul (wM (regParticlesOf sys))
        (Ug τ (regCoeff m ((capKin sys g r κ).h2 x)))‖ ≤ W := by
    intro x hθ τ
    rw [← stateMap_capLift]
    refine (norm_wM_gridFlow_le sys hL hκg.bound (Ug τ) (hgcomm τ) _).trans ?_
    have h1 := (norm_wM_regCoeff_le (m := m) sys g hg (capLift sys g r κ x)).trans
      (mul_le_mul_of_nonneg_left hθ (by positivity : (0 : ℝ) ≤ 1 + 2 / g ^ 2))
    have h2 : ‖regCoeff m (molecularH2StateMap eta g (capLift sys g r κ x))‖ ≤ Θκ :=
      ((norm_regCoeff_le _).trans (norm_stateMap_le_theta sys g _)).trans hθ
    show _ ≤ (5 / 3 * (1 + 2 / g ^ 2) + cJ) * Θκ
    have h3 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 5 / 3)
    have h4 := mul_le_mul_of_nonneg_left h2 hcJ
    have e : (5 / 3 * (1 + 2 / g ^ 2) + cJ) * Θκ = 5 / 3 * ((1 + 2 / g ^ 2) * Θκ) + cJ * Θκ := by
      ring
    rw [e]
    exact add_le_add h3 h4
  -- the capped secular term
  have hPu : molecularH2StateMap eta g Pu =
      regEmb m (regCoeff m (molecularH2StateMap eta g u)) := by
    rw [hPudef, stateMap_truncate, regEmb_regCoeff]
  have he : regCoeff m (molecularH2StateMap eta g u) - ψg =
      regCoeff m (U t (molecularH2StateMap eta g u₀)) -
        Ug t (regCoeff m (molecularH2StateMap eta g u₀)) := by
    rw [hψ]
  have hpair : ∀ x : MolecularFourierH2 eta,
      ‖molecularH2StateMap eta g (capLift sys g r κ x) +
        coulombFourierKineticH2 sys g (capLift sys g r κ x)‖ ≤ Θκ →
      ‖⟪molecularH2StateMap eta g Pu - molecularH2StateMap eta g l,
        (capKin sys g r κ).h2 x⟫_ℂ‖ ≤ Bd * t := by
    intro x hθ
    rw [hPu, hSl, ← map_sub, inner_regEmb_left, he]
    exact grid_duality sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph hderiv m hm hκg Ug hg0
      hgcomm hgderiv ρ₂ ρ₄ Blow Cs Bker hK₄ hRho₂ hRhoScale₂ hRho₄ hRhoScale₄ hBlow hCs hBker
      hAmplitude hBkerScale hCsScale u₀ v₀ huv _ W (hWx x hθ) ht
  have hsec : |(capKin sys g r κ).expect (molecularH2StateMap eta g Pu) -
      (capKin sys g r κ).expect (molecularH2StateMap eta g l)| ≤ 2 * (Bd * t) :=
    (expect_sub_le_pairings (capKin sys g r κ) Pu l).trans
      ((add_le_add (hpair Pu hθa) (hpair l hθb)).trans_eq (by ring))
  -- assembly
  have hsplit : (regKin sys g r).expect (molecularH2StateMap eta g u) =
      (regKin sys g r).expect (molecularH2StateMap eta g Pu) +
        (regKin sys g r).expect (molecularH2StateMap eta g (u - Pu)) :=
    (regKin sys g r).expect_split (2 * m) u
  have hreg : regExpect sys g r ψg = (regKin sys g r).expect (molecularH2StateMap eta g l) := by
    rw [hSl, regExpect_eq_expect]
  set A := (regKin sys g r).expect (molecularH2StateMap eta g (u - Pu)) with hAdef
  set Ka := (capKin sys g r κ).expect (molecularH2StateMap eta g Pu) with hKadef
  set Kb := (capKin sys g r κ).expect (molecularH2StateMap eta g l) with hKbdef
  set Ra := (capRest sys g r κ).expect (molecularH2StateMap eta g Pu) with hRadef
  set Rb := (capRest sys g r κ).expect (molecularH2StateMap eta g l) with hRbdef
  have hE : (regKin sys g r).expect (U t (molecularH2StateMap eta g u₀)) - regExpect sys g r ψg =
      A + (Ka - Kb) + (Ra - Rb) := by
    rw [hψ, hreg, hsplit, expect_regKin_eq sys g r κ Pu, expect_regKin_eq sys g r κ l]
    ring
  rw [hE]
  have hC : |Ra - Rb| ≤ 2 * sys.maxMass * β ^ 2 * (1 / κ) ^ 3 +
      8 * sys.maxMass * Dg ^ 2 * (1 / κ) ^ 3 := by
    have hq1 := hRa0.trans hRa
    have hq2 := hRb0.trans hRb
    rw [abs_le]
    constructor
    · linarith only [hRa0, hRb, hq1]
    · linarith only [hRa, hRb0, hq2]
  have h1 : |A| ≤ (eta * t₂) * (eta * B₂) := by
    rw [abs_of_nonneg hI0]
    exact hI
  have h3 := abs_add_le (A + (Ka - Kb)) (Ra - Rb)
  have h4 := abs_add_le A (Ka - Kb)
  linarith only [h1, hsec, hC, h3, h4]

end Grid

end PlaneWaveKinetic

end DevK10
-- END SOURCE dev/DevK10.lean

-- BEGIN SOURCE dev/DevK11.lean
-- SHA256 989bb6a2ca69f61e62ff5036a215fd791c18f7087240b6aeaad15de922c38841
section DevK11

/-!
# `thm:mult-cap` (grid) and `cor:stopping2` (grid): rates, optimisation, position space

* `grid_rate_core`: the projection term at `2K` plus the two source pairings of `grid_duality`
  are at most `A₁ K^{-3} + 2 m̄ Γ t W K^{-5/2}` for every flow budget `W` (the rate part of
  `prop:mult-grid`, linear in `W`).
* `cap_grid_rate_arith`, `grid_capped_fixed_rate`: with the capped budget
  `W = c_W Θ_κ ≤ c_W Θ₁ κ^{3/2}` the bound of `grid_capped_error` is
  `c₁ K^{-3} + c₂ κ^{-3} + c₃ t κ^{3/2} K^{-5/2}` for `λ₀ ≤ κ ≤ K`.
* The optimisation over `κ`, with `s = t^{1/3}`, `k = K^{1/6}`: `s² k⁸ ≤ 1` (`t ≤ K^{-2}`):
  `κ = K` (`gcap_regime_small`); `λ₀³ s² ≤ k^{10} ≤ s² k^{18}`: `κ = w²`, `w³ s = k⁵`
  (`gcap_regime_mid`, `gcap_mid_bounds`), balancing
  `κ^{-3} = t κ^{3/2} K^{-5/2} = t^{2/3} K^{-5/3}`;
  `k^{10} < λ₀³ s²` (`t ≳ K^{5/2}`): the energy bound (`grid_expect_pair_le`). This gives
  `|Δ⟨A_r⟩(t)| ≤ C₁ K^{-3} + C₂ t^{2/3} K^{-5/3}` (`grid_capped_rate`).
* In DevK12, with `prop:mult-grid`: the minimum form
  `D₁ K^{-3} + D₂ min(t K^{-1}, t^{2/3} K^{-5/3})` in position space (`grid_capped_min_position`),
  with propagators (`thm_mult_cap_grid`), and the window law of the stopping power
  (`stopping_window_grid`, `cor:stopping2`, grid route).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate lp ENNReal Topology
open Filter Set

namespace PlaneWaveKinetic

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Arithmetic -/

section Arith

/-- **The rates of the grid source pairings for any flow budget `W`.** The bound of
`grid_duality` (twice) plus the projection term at `2K`, at `ρ₂ = (2K)^{-1/2}`,
`ρ₄ = (g⌊m/4⌋)^{-1/2}`, with a linear tail constant `Ct M = M C₁`, is at most
`A₁ K^{-3} + 2 m̄ Γ t W K^{-5/2}` for `m ≥ 8` and `K = g m ≥ 8`. -/
lemma grid_rate_core {η mm Ξ₁ C₀ C1 g t Zg Xa W : ℝ} {m : ℕ} {Ct : ℝ → ℝ}
    (hη : 0 ≤ η) (hmm : 1 ≤ mm) (hΞ₁ : 0 ≤ Ξ₁) (hC₀ : 0 ≤ C₀) (hg : 0 < g) (hm : 8 ≤ m)
    (hK : 8 ≤ g * m) (ht : 0 ≤ t) (hZg : 0 ≤ Zg) (hXa : 0 ≤ Xa) (hW : 0 ≤ W)
    (hCt : ∀ M, Ct M = M * C1) (hC1 : 0 ≤ C1) :
    let K : ℝ := g * m
    let tl : ℝ → ℝ → ℝ := fun K ρ => (2 * mm / K ^ 2) * ((2 * mm / K ^ 2) * Ξ₁ + C₀ * ρ)
    let ρ₂ : ℝ := Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))
    let ρ₄ : ℝ := Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))
    let s₀ : ℕ := m / 4
    let τφ : ℝ := mm * W / ((s₀ : ℝ) + 1) ^ 2
    let K₂ : ℝ := g * ((2 * m : ℕ) : ℝ)
    let B₂ : ℝ := (2 * mm / K₂ ^ 2) * Ξ₁ + C₀ * ρ₂
    let t₂ : ℝ := tl K₂ ρ₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) ρ₄
    let Bd : ℝ := (η * t₂) * (η * (Ct ((1 + g ^ 2) * (mm * W)) * ρ₂)) +
      Zg * (formA s₀ m * (t₄ * (mm * W) + τφ * Xa) + 52 * m * (τφ * t₄))
    let τ₁ : ℝ := 2 * mm * (2 * mm * Ξ₁ + C₀)
    let β₄ : ℝ := 128 * mm * (128 * mm * Ξ₁ + 8 * C₀)
    let cF : ℝ := 4 * Real.sqrt (5512 * g)
    let Γ : ℝ := η * (η * τ₁) * ((1 + g ^ 2) * C1) +
      Zg * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)
    (η * t₂) * (η * B₂) + 2 * (Bd * t) ≤
      (η ^ 2 * τ₁ * (2 * mm * Ξ₁ + C₀)) * (1 / K) ^ 3 +
        2 * mm * Γ * t * (W * Real.sqrt (1 / K) ^ 5) := by
  intro K tl ρ₂ ρ₄ s₀ τφ K₂ B₂ t₂ t₄ Bd τ₁ β₄ cF Γ
  set ρ := Real.sqrt (1 / K) with hρdef
  have hmm0 : 0 ≤ mm := by linarith
  have hKpos : 0 < K := by show 0 < g * (m : ℝ); linarith
  have hK1 : 1 ≤ K := by show 1 ≤ g * (m : ℝ); linarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = 1 / K := Real.sq_sqrt (one_div_nonneg.mpr hKpos.le)
  have hρK : ρ ^ 2 * K = 1 := by rw [hρ2]; exact one_div_mul_cancel hKpos.ne'
  have hρ1 : ρ ≤ 1 := by
    have h5 : ρ ^ 2 ≤ 1 := by
      rw [hρ2, div_le_one hKpos]
      exact hK1
    exact (pow_le_one_iff_of_nonneg hρ0 two_ne_zero).mp h5
  have hρK' : ρ ^ 2 * (g * (m : ℝ)) = 1 := hρK
  -- the cube `2m` and the threshold `⌊m/4⌋`
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hK₂pos : 0 < K₂ := by show 0 < g * ((2 * m : ℕ) : ℝ); rw [h2m]; positivity
  have hK₂ : K ≤ 1 * K₂ := by
    show g * (m : ℝ) ≤ 1 * (g * ((2 * m : ℕ) : ℝ))
    rw [h2m, one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) hg.le
  have hρ₂0 : 0 ≤ ρ₂ := Real.sqrt_nonneg _
  have hρ₂K : ρ₂ ^ 2 * K₂ = 1 := by
    show Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (one_div_nonneg.mpr hK₂pos.le)]
    exact one_div_mul_cancel hK₂pos.ne'
  have hρ₂ρ : ρ₂ ≤ ρ := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hK₂pos hKpos]
    linarith
  have hs0 : (0 : ℝ) < ((m / 4 : ℕ) : ℝ) := by
    have : 0 < m / 4 := by omega
    exact_mod_cast this
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hK₄pos : 0 < g * ((m / 4 : ℕ) : ℝ) := mul_pos hg hs0
  have hK₄ : K ≤ 8 * (g * (s₀ : ℝ)) := by
    show g * (m : ℝ) ≤ 8 * (g * ((m / 4 : ℕ) : ℝ))
    calc g * (m : ℝ) ≤ g * (8 * ((m / 4 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hs hg.le
      _ = 8 * (g * ((m / 4 : ℕ) : ℝ)) := by ring
  have hρ₄0 : 0 ≤ ρ₄ := Real.sqrt_nonneg _
  have hρ₄K : ρ₄ ^ 2 * (g * (s₀ : ℝ)) = 1 := by
    show Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ))) ^ 2 * (g * ((m / 4 : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (one_div_nonneg.mpr hK₄pos.le)]
    exact one_div_mul_cancel hK₄pos.ne'
  -- the tails
  have h2mm : 0 ≤ 2 * mm := mul_nonneg zero_le_two hmm0
  have hX₁ : 0 ≤ 2 * mm * Ξ₁ + C₀ := add_nonneg (mul_nonneg h2mm hΞ₁) hC₀
  have hτ₁0 : 0 ≤ τ₁ := mul_nonneg h2mm hX₁
  have hβ₄0 : 0 ≤ β₄ := mul_nonneg (mul_nonneg (by norm_num) hmm0)
    (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hmm0) hΞ₁) (mul_nonneg (by norm_num) hC₀))
  have ht₂ : t₂ ≤ τ₁ * ρ ^ 5 := by
    have h := tl_rate (c := 1) hmm0 hΞ₁ hC₀ le_rfl hρ0 hρK hK1 hK₂ hρ₂0 hρ₂K
    have e : 2 * mm * 1 ^ 2 * (2 * mm * 1 ^ 2 * Ξ₁ + 1 * C₀) * ρ ^ 5 = τ₁ * ρ ^ 5 := by
      show _ = 2 * mm * (2 * mm * Ξ₁ + C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have ht₄ : t₄ ≤ β₄ * ρ ^ 5 := by
    have h := tl_rate (c := 8) hmm0 hΞ₁ hC₀ (by norm_num) hρ0 hρK hK1 hK₄ hρ₄0 hρ₄K
    have e : 2 * mm * 8 ^ 2 * (2 * mm * 8 ^ 2 * Ξ₁ + 8 * C₀) * ρ ^ 5 = β₄ * ρ ^ 5 := by
      show _ = 128 * mm * (128 * mm * Ξ₁ + 8 * C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have htl0 : ∀ K' ρ', 0 ≤ ρ' → 0 ≤ tl K' ρ' := by
    intro K' ρ' hρ'
    show 0 ≤ (2 * mm / K' ^ 2) * ((2 * mm / K' ^ 2) * Ξ₁ + C₀ * ρ')
    have h1 : 0 ≤ 2 * mm / K' ^ 2 := div_nonneg h2mm (sq_nonneg K')
    exact mul_nonneg h1 (add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hC₀ hρ'))
  have ht₂0 : 0 ≤ t₂ := htl0 _ _ hρ₂0
  have ht₄0 : 0 ≤ t₄ := htl0 _ _ hρ₄0
  -- (I): the projection term
  have hB₂ : B₂ ≤ (2 * mm * Ξ₁ + C₀) * ρ := by
    have hinv : 2 * mm / K₂ ^ 2 ≤ 2 * mm * ρ := by
      have h1 : 1 / K₂ ^ 2 ≤ ρ ^ 4 := by
        have h2 : 1 / K₂ ≤ 1 / K := one_div_le_one_div_of_le hKpos (by linarith)
        have h3 : (1 / K₂) ^ 2 ≤ (1 / K) ^ 2 :=
          pow_le_pow_left₀ (one_div_nonneg.mpr hK₂pos.le) h2 2
        have e1 : (1 / K₂) ^ 2 = 1 / K₂ ^ 2 := by ring
        have e2 : ρ ^ 4 = (1 / K) ^ 2 := by rw [show ρ ^ 4 = (ρ ^ 2) ^ 2 by ring, hρ2]
        rw [← e1, e2]
        exact h3
      have h4 : ρ ^ 4 ≤ ρ := by
        calc ρ ^ 4 = ρ * ρ ^ 3 := by ring
          _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hρ0 hρ1) hρ0
          _ = ρ := mul_one ρ
      calc 2 * mm / K₂ ^ 2 = 2 * mm * (1 / K₂ ^ 2) := by ring
        _ ≤ 2 * mm * ρ := mul_le_mul_of_nonneg_left (h1.trans h4) h2mm
    have h1 := mul_le_mul_of_nonneg_right hinv hΞ₁
    have h2 := mul_le_mul_of_nonneg_left hρ₂ρ hC₀
    show (2 * mm / K₂ ^ 2) * Ξ₁ + C₀ * ρ₂ ≤ (2 * mm * Ξ₁ + C₀) * ρ
    have e : (2 * mm * Ξ₁ + C₀) * ρ = 2 * mm * ρ * Ξ₁ + C₀ * ρ := by ring
    rw [e]
    exact add_le_add h1 h2
  have hB₂0 : 0 ≤ B₂ := by
    show 0 ≤ (2 * mm / K₂ ^ 2) * Ξ₁ + C₀ * ρ₂
    have h1 : 0 ≤ 2 * mm / K₂ ^ 2 := div_nonneg h2mm (sq_nonneg K₂)
    exact add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hC₀ hρ₂0)
  have hI : (η * t₂) * (η * B₂) ≤ (η ^ 2 * τ₁ * (2 * mm * Ξ₁ + C₀)) * (1 / K) ^ 3 := by
    have h1 : (η * t₂) * (η * B₂) ≤ (η * (τ₁ * ρ ^ 5)) * (η * ((2 * mm * Ξ₁ + C₀) * ρ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ht₂ hη) (mul_le_mul_of_nonneg_left hB₂ hη)
        (mul_nonneg hη hB₂0) (mul_nonneg hη (mul_nonneg hτ₁0 (pow_nonneg hρ0 5)))
    have hρ6 : ρ ^ 6 = (1 / K) ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hρ2]
    have e : (η * (τ₁ * ρ ^ 5)) * (η * ((2 * mm * Ξ₁ + C₀) * ρ)) =
        (η ^ 2 * τ₁ * (2 * mm * Ξ₁ + C₀)) * ρ ^ 6 := by ring
    rw [e, hρ6] at h1
    exact h1
  -- (III): the pairings
  have hfA : formA s₀ m ≤ cF * ρ := formA_rate hg hρ0 hm hρK'
  have hsh := shell_rate hg hm hρK'
  have hmW : 0 ≤ mm * W := mul_nonneg hmm0 hW
  have hτφ : τφ ≤ 64 * g ^ 2 * ρ ^ 4 * (mm * W) := by
    have e : τφ = (mm * W) * (1 / ((s₀ : ℝ) + 1) ^ 2) := by
      show mm * W / ((s₀ : ℝ) + 1) ^ 2 = _
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsh.1 hmW
    linarith
  have hτφ0 : 0 ≤ τφ := div_nonneg hmW (sq_nonneg _)
  have hmτ : (m : ℝ) * τφ ≤ 64 * g * ρ ^ 2 * (mm * W) := by
    have e : (m : ℝ) * τφ = (mm * W) * ((m : ℝ) / ((s₀ : ℝ) + 1) ^ 2) := by
      show (m : ℝ) * (mm * W / ((s₀ : ℝ) + 1) ^ 2) = _
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsh.2 hmW
    linarith
  have hcF0 : 0 ≤ cF := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hg1 : 0 ≤ 1 + g ^ 2 := add_nonneg zero_le_one (sq_nonneg g)
  have hCtL : 0 ≤ Ct ((1 + g ^ 2) * (mm * W)) := by
    rw [hCt]
    exact mul_nonneg (mul_nonneg hg1 hmW) hC1
  have hIII := rate_arith_III (m := (m : ℝ)) (Xa := Xa) hη hτ₁0 hρ0 hρ1 ht₂ hρ₂ρ hρ₂0 hCtL hZg hfA
    (formA_nonneg s₀ m) ht₄ ht₄0 hmW hτφ hτφ0 hmτ hXa hg.le ht hβ₄0 hcF0
  have e1 : 2 * (η * (η * τ₁) * Ct ((1 + g ^ 2) * (mm * W)) +
      Zg * (mm * W) * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)) * t * ρ ^ 5 =
      2 * mm * Γ * t * (W * ρ ^ 5) := by
    rw [hCt]
    ring
  rw [e1] at hIII
  linarith

/-- The regime `s² k⁸ ≤ 1` (`t ≤ K^{-2}`, `K = k⁶`, `t = s³`): with the cap `κ = K` the secular
term `t K^{3/2} K^{-5/2} = t K^{-1}` is at most `t^{2/3} K^{-5/3} = s² k^{-10}`. -/
lemma gcap_regime_small {c1 c2 c3 K k s t : ℝ} (hk : 0 < k) (hK : K = k ^ 6) (hs : 0 ≤ s)
    (hc3 : 0 ≤ c3) (hst : s ^ 3 = t) (h : s ^ 2 * k ^ 8 ≤ 1) :
    c1 * (1 / K) ^ 3 + c2 * (1 / K) ^ 3 + c3 * t * (K * Real.sqrt K) * Real.sqrt (1 / K) ^ 5 ≤
      (c1 + c2) * (1 / K) ^ 3 + c3 * s ^ 2 * (1 / k) ^ 10 := by
  subst hK hst
  have hsK : Real.sqrt (k ^ 6) = k ^ 3 := by
    rw [show k ^ 6 = (k ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsK' : Real.sqrt (1 / k ^ 6) = 1 / k ^ 3 := by
    rw [show 1 / k ^ 6 = (1 / k ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsK, hsK']
  have hsk : s * k ^ 4 ≤ 1 := by
    have h1 : (s * k ^ 4) ^ 2 ≤ 1 := by
      calc (s * k ^ 4) ^ 2 = s ^ 2 * k ^ 8 := by ring
        _ ≤ 1 := h
    exact (pow_le_one_iff_of_nonneg (by positivity) two_ne_zero).mp h1
  have e : c3 * s ^ 3 * (k ^ 6 * k ^ 3) * (1 / k ^ 3) ^ 5 =
      (c3 * s ^ 2 * (1 / k) ^ 10) * (s * k ^ 4) := by
    field_simp
  have h0 : 0 ≤ c3 * s ^ 2 * (1 / k) ^ 10 := by positivity
  rw [e]
  have := mul_le_mul_of_nonneg_left hsk h0
  linarith

/-- The balancing regime: `κ = w²` with `w³ s = k⁵` makes
`κ^{-3} = t κ^{3/2} K^{-5/2} = s² k^{-10}`. -/
lemma gcap_regime_mid {c1 c2 c3 K k s t w : ℝ} (hk : 0 < k) (hK : K = k ^ 6) (hs : 0 < s)
    (hw : 0 < w) (hst : s ^ 3 = t) (hws : w ^ 3 * s = k ^ 5) :
    c1 * (1 / K) ^ 3 + c2 * (1 / w ^ 2) ^ 3 +
        c3 * t * (w ^ 2 * Real.sqrt (w ^ 2)) * Real.sqrt (1 / K) ^ 5 =
      c1 * (1 / K) ^ 3 + (c2 + c3) * s ^ 2 * (1 / k) ^ 10 := by
  subst hK hst
  have hsK' : Real.sqrt (1 / k ^ 6) = 1 / k ^ 3 := by
    rw [show 1 / k ^ 6 = (1 / k ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsK', Real.sqrt_sq hw.le]
  have hw6 : w ^ 6 * s ^ 2 = k ^ 10 := by
    calc w ^ 6 * s ^ 2 = (w ^ 3 * s) ^ 2 := by ring
      _ = k ^ 10 := by rw [hws]; ring
  have e1 : (1 / w ^ 2) ^ 3 = s ^ 2 * (1 / k) ^ 10 := by
    field_simp
    linarith [hw6]
  have e2 : s ^ 3 * (w ^ 2 * w) * (1 / k ^ 3) ^ 5 = s ^ 2 * (1 / k) ^ 10 := by
    have e3 : s ^ 3 * (w ^ 2 * w) = s ^ 2 * (w ^ 3 * s) := by ring
    rw [e3, hws]
    field_simp
  calc c1 * (1 / k ^ 6) ^ 3 + c2 * (1 / w ^ 2) ^ 3 + c3 * s ^ 3 * (w ^ 2 * w) * (1 / k ^ 3) ^ 5
      = c1 * (1 / k ^ 6) ^ 3 + c2 * (1 / w ^ 2) ^ 3 +
          c3 * (s ^ 3 * (w ^ 2 * w) * (1 / k ^ 3) ^ 5) := by ring
    _ = c1 * (1 / k ^ 6) ^ 3 + (c2 + c3) * s ^ 2 * (1 / k) ^ 10 := by rw [e1, e2]; ring

/-- In the balancing regime the cap is admissible: `λ₀ ≤ w² ≤ K`. -/
lemma gcap_mid_bounds {K k s w lam0 : ℝ} (hk : 0 < k) (hK : K = k ^ 6) (hs : 0 < s)
    (hws : w ^ 3 * s = k ^ 5) (h1 : 1 ≤ s ^ 2 * k ^ 8) (h2 : lam0 ^ 3 * s ^ 2 ≤ k ^ 10) :
    lam0 ≤ w ^ 2 ∧ w ^ 2 ≤ K := by
  have hw6 : (w ^ 2) ^ 3 * s ^ 2 = k ^ 10 := by
    calc (w ^ 2) ^ 3 * s ^ 2 = (w ^ 3 * s) ^ 2 := by ring
      _ = k ^ 10 := by rw [hws]; ring
  have hs2 : 0 < s ^ 2 := pow_pos hs 2
  constructor
  · refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (sq_nonneg w) ?_
    refine le_of_mul_le_mul_right ?_ hs2
    rw [hw6]
    exact h2
  · subst hK
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
    refine le_of_mul_le_mul_right ?_ hs2
    rw [hw6]
    calc k ^ 10 = k ^ 10 * 1 := (mul_one _).symm
      _ ≤ k ^ 10 * (s ^ 2 * k ^ 8) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (k ^ 6) ^ 3 * s ^ 2 := by ring

/-- **The capped grid rate, arithmetic.** With the capped flow budget
`W = c_W Θ_κ`, `Θ_κ = ½ (λ₀² Y + √15 (D_a + D_b) κ^{3/2})` and `κ ≥ 1`, the bound of
`grid_capped_error` is at most `c₁ K^{-3} + c₂ κ^{-3} + c₃ t κ^{3/2} K^{-5/2}`. -/
lemma cap_grid_rate_arith {η mm Ξ₁ C₀ C1 g t Zg Xa β Dg κ lam0 Y Da Db cW : ℝ} {m : ℕ}
    {Ct : ℝ → ℝ} (hη : 0 ≤ η) (hmm : 1 ≤ mm) (hΞ₁ : 0 ≤ Ξ₁) (hC₀ : 0 ≤ C₀) (hg : 0 < g)
    (hm : 8 ≤ m) (hK : 8 ≤ g * m) (ht : 0 ≤ t) (hZg : 0 ≤ Zg) (hXa : 0 ≤ Xa)
    (hCt : ∀ M, Ct M = M * C1) (hC1 : 0 ≤ C1) (hκ1 : 1 ≤ κ) (hY : 0 ≤ Y) (hDa : 0 ≤ Da)
    (hDb : 0 ≤ Db) (hcW : 0 ≤ cW) :
    let K : ℝ := g * m
    let tl : ℝ → ℝ → ℝ := fun K ρ => (2 * mm / K ^ 2) * ((2 * mm / K ^ 2) * Ξ₁ + C₀ * ρ)
    let ρ₂ : ℝ := Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))
    let ρ₄ : ℝ := Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))
    let s₀ : ℕ := m / 4
    let Θκ : ℝ := (1 / 2 : ℝ) * (lam0 ^ 2 * Y + Real.sqrt 15 * (Da + Db) * (κ * Real.sqrt κ))
    let W : ℝ := cW * Θκ
    let τφ : ℝ := mm * W / ((s₀ : ℝ) + 1) ^ 2
    let K₂ : ℝ := g * ((2 * m : ℕ) : ℝ)
    let B₂ : ℝ := (2 * mm / K₂ ^ 2) * Ξ₁ + C₀ * ρ₂
    let t₂ : ℝ := tl K₂ ρ₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) ρ₄
    let Bd : ℝ := (η * t₂) * (η * (Ct ((1 + g ^ 2) * (mm * W)) * ρ₂)) +
      Zg * (formA s₀ m * (t₄ * (mm * W) + τφ * Xa) + 52 * m * (τφ * t₄))
    let τ₁ : ℝ := 2 * mm * (2 * mm * Ξ₁ + C₀)
    let β₄ : ℝ := 128 * mm * (128 * mm * Ξ₁ + 8 * C₀)
    let cF : ℝ := 4 * Real.sqrt (5512 * g)
    let Γ : ℝ := η * (η * τ₁) * ((1 + g ^ 2) * C1) +
      Zg * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)
    (η * t₂) * (η * B₂) + 2 * mm * β ^ 2 * (1 / κ) ^ 3 + 8 * mm * Dg ^ 2 * (1 / κ) ^ 3 +
        2 * (Bd * t) ≤
      (η ^ 2 * τ₁ * (2 * mm * Ξ₁ + C₀)) * (1 / K) ^ 3 +
        (2 * mm * β ^ 2 + 8 * mm * Dg ^ 2) * (1 / κ) ^ 3 +
        (2 * mm * Γ * (cW * ((1 / 2 : ℝ) * (lam0 ^ 2 * Y + Real.sqrt 15 * (Da + Db))))) * t *
          (κ * Real.sqrt κ) * Real.sqrt (1 / K) ^ 5 := by
  intro K tl ρ₂ ρ₄ s₀ Θκ W τφ K₂ B₂ t₂ t₄ Bd τ₁ β₄ cF Γ
  have hmm0 : 0 ≤ mm := by linarith
  have hX : 1 ≤ κ * Real.sqrt κ := by
    have : 1 ≤ Real.sqrt κ := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]
      linarith
    exact one_le_mul_of_one_le_of_one_le hκ1 this
  have hX0 : 0 ≤ κ * Real.sqrt κ := zero_le_one.trans hX
  have hc15 : 0 ≤ Real.sqrt 15 * (Da + Db) := mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hDa hDb)
  have hΘ0 : 0 ≤ Θκ := mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (sq_nonneg _) hY)
    (mul_nonneg hc15 hX0))
  have hW0 : 0 ≤ W := mul_nonneg hcW hΘ0
  have hcore : (η * t₂) * (η * B₂) + 2 * (Bd * t) ≤
      (η ^ 2 * τ₁ * (2 * mm * Ξ₁ + C₀)) * (1 / K) ^ 3 +
        2 * mm * Γ * t * (W * Real.sqrt (1 / K) ^ 5) :=
    grid_rate_core (W := W) (m := m) (Ct := Ct) hη hmm hΞ₁ hC₀ hg hm hK ht hZg hXa hW0 hCt hC1
  have hΘ : Θκ ≤ (1 / 2 : ℝ) * (lam0 ^ 2 * Y + Real.sqrt 15 * (Da + Db)) * (κ * Real.sqrt κ) := by
    have h1 : lam0 ^ 2 * Y ≤ lam0 ^ 2 * Y * (κ * Real.sqrt κ) :=
      le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) hY) hX
    have e : (1 / 2 : ℝ) * (lam0 ^ 2 * Y + Real.sqrt 15 * (Da + Db)) * (κ * Real.sqrt κ) =
        (1 / 2 : ℝ) * (lam0 ^ 2 * Y * (κ * Real.sqrt κ) +
          Real.sqrt 15 * (Da + Db) * (κ * Real.sqrt κ)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (add_le_add_left h1 _) (by norm_num)
  have hτ₁0 : 0 ≤ τ₁ := mul_nonneg (mul_nonneg zero_le_two hmm0)
    (add_nonneg (mul_nonneg (mul_nonneg zero_le_two hmm0) hΞ₁) hC₀)
  have hβ₄0 : 0 ≤ β₄ := mul_nonneg (mul_nonneg (by norm_num) hmm0)
    (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hmm0) hΞ₁) (mul_nonneg (by norm_num) hC₀))
  have hcF0 : 0 ≤ cF := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hΓ0 : 0 ≤ Γ := add_nonneg
    (mul_nonneg (mul_nonneg hη (mul_nonneg hη hτ₁0))
      (mul_nonneg (add_nonneg zero_le_one (sq_nonneg g)) hC1))
    (mul_nonneg hZg (add_nonneg (add_nonneg (mul_nonneg hcF0 hβ₄0)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcF0) (sq_nonneg g)) hXa))
      (mul_nonneg (mul_nonneg (by norm_num) hg.le) hβ₄0)))
  have hρ5 : 0 ≤ Real.sqrt (1 / K) ^ 5 := pow_nonneg (Real.sqrt_nonneg _) 5
  have hWle : W ≤ cW * ((1 / 2 : ℝ) * (lam0 ^ 2 * Y + Real.sqrt 15 * (Da + Db))) *
      (κ * Real.sqrt κ) := by
    calc W = cW * Θκ := rfl
      _ ≤ cW * ((1 / 2 : ℝ) * (lam0 ^ 2 * Y + Real.sqrt 15 * (Da + Db)) * (κ * Real.sqrt κ)) :=
          mul_le_mul_of_nonneg_left hΘ hcW
      _ = cW * ((1 / 2 : ℝ) * (lam0 ^ 2 * Y + Real.sqrt 15 * (Da + Db))) * (κ * Real.sqrt κ) := by
          ring
  have hsec : 2 * mm * Γ * t * (W * Real.sqrt (1 / K) ^ 5) ≤
      (2 * mm * Γ * (cW * ((1 / 2 : ℝ) * (lam0 ^ 2 * Y + Real.sqrt 15 * (Da + Db))))) * t *
        (κ * Real.sqrt κ) * Real.sqrt (1 / K) ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_right hWle hρ5
    have h2 := mul_le_mul_of_nonneg_left h1
      (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hmm0) hΓ0) ht)
    calc 2 * mm * Γ * t * (W * Real.sqrt (1 / K) ^ 5)
        ≤ 2 * mm * Γ * t * (cW * ((1 / 2 : ℝ) * (lam0 ^ 2 * Y + Real.sqrt 15 * (Da + Db))) *
            (κ * Real.sqrt κ) * Real.sqrt (1 / K) ^ 5) := h2
      _ = (2 * mm * Γ * (cW * ((1 / 2 : ℝ) * (lam0 ^ 2 * Y + Real.sqrt 15 * (Da + Db))))) * t *
            (κ * Real.sqrt κ) * Real.sqrt (1 / K) ^ 5 := by ring
  have e : (2 * mm * β ^ 2 + 8 * mm * Dg ^ 2) * (1 / κ) ^ 3 =
      2 * mm * β ^ 2 * (1 / κ) ^ 3 + 8 * mm * Dg ^ 2 * (1 / κ) ^ 3 := by ring
  rw [e]
  linarith

end Arith

/-! ## The constants -/

/-- The energy bound `‖ψ₀‖ (Ξ₀ + (g²/2) X_b)` on the exact and grid kinetic expectations. -/
noncomputable def gridTrivConst (sys : CoulombSystem eta ν) (L Hunit s0 hu : ℝ) : ℝ :=
  let g : ℝ := 2 * Real.pi / L
  let b : ℝ := relB sys L Hunit
  let Ξ₀ : ℝ := 2 * hu + 2 * b * s0
  let M₀ : ℝ := sys.maxMass * (s0 + 2 * Ξ₀)
  let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
  let Xb : ℝ := 5 / 3 * Xa + gridFlowConst sys L * s0
  s0 * (Ξ₀ + g ^ 2 / 2 * Xb)

/-- The constants `(c₁, c₂, c₃)` of the capped grid bound
`c₁ K^{-3} + c₂ κ^{-3} + c₃ t κ^{3/2} K^{-5/2}` for the data norms `(s0, hu, hs, hv)` and the
lowest cap `λ₀`. -/
noncomputable def capGridConsts (sys : CoulombSystem eta ν) (L Hunit Blow Cs Bker lam0 : ℝ)
    (s0 hu hs hv : ℝ) : ℝ × ℝ × ℝ :=
  let g : ℝ := 2 * Real.pi / L
  let b : ℝ := relB sys L Hunit
  let Ξ₀ : ℝ := 2 * hu + 2 * b * s0
  let Ξ₁ : ℝ := 2 * hv + 2 * b * hs
  let M₀ : ℝ := sys.maxMass * (s0 + 2 * Ξ₀)
  let Ct : ℝ → ℝ := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M
  let C₀ : ℝ := Ct M₀
  let τ₁ : ℝ := 2 * sys.maxMass * (2 * sys.maxMass * Ξ₁ + C₀)
  let β₄ : ℝ := 128 * sys.maxMass * (128 * sys.maxMass * Ξ₁ + 8 * C₀)
  let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
  let Xa : ℝ := (1 + 1 / g ^ 2) * M₀
  let cJ : ℝ := gridFlowConst sys L
  let Xb : ℝ := 5 / 3 * Xa + cJ * s0
  let cF : ℝ := 4 * Real.sqrt (5512 * g)
  let Γ : ℝ := eta * (eta * τ₁) * ((1 + g ^ 2) * Ct 1) +
    Zg * (cF * β₄ + 64 * cF * g ^ 2 * Xa + 3328 * g * β₄)
  let β : ℝ := 2 * sys.maxMass * Ξ₁ + C₀
  let Dg : ℝ := gridTailConst sys L Hunit Blow Cs Bker s0 hu hs hv
  let Da : ℝ := (1 + 2 * sys.maxMass) * β
  let Db : ℝ := (1 + 8 * sys.maxMass) * Dg
  let Y : ℝ := (s0 + Ξ₀) + (s0 + g ^ 2 / 2 * Xb)
  let cW : ℝ := 5 / 3 * (1 + 2 / g ^ 2) + cJ
  ((eta : ℝ) ^ 2 * τ₁ * (2 * sys.maxMass * Ξ₁ + C₀),
    2 * sys.maxMass * β ^ 2 + 8 * sys.maxMass * Dg ^ 2,
    2 * sys.maxMass * Γ * (cW * ((1 / 2 : ℝ) * (lam0 ^ 2 * Y + Real.sqrt 15 * (Da + Db)))))

/-- The constants `(C₁, C₂)` of `|Δ⟨A_r⟩(t)| ≤ C₁ K^{-3} + C₂ t^{2/3} K^{-5/3}` on the grid. -/
noncomputable def capGridRateConsts (sys : CoulombSystem eta ν) (L Hunit Blow Cs Bker lam0 : ℝ)
    (s0 hu hs hv : ℝ) : ℝ × ℝ :=
  let c := capGridConsts sys L Hunit Blow Cs Bker lam0 s0 hu hs hv
  (c.1 + c.2.1, c.2.1 + c.2.2 + gridTrivConst sys L Hunit s0 hu * lam0 ^ 3)

lemma gridTailConst_nonneg (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (Hunit : ℝ)
    (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit) {Blow Cs Bker s0 hu hs hv : ℝ}
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker) (hs0 : 0 ≤ s0) (hhu : 0 ≤ hu)
    (hhs : 0 ≤ hs) (hhv : 0 ≤ hv) :
    0 ≤ gridTailConst sys L Hunit Blow Cs Bker s0 hu hs hv := by
  have hb0 : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hm0 : 0 ≤ sys.maxMass := by linarith [sys.one_le_maxMass]
  have hCt0 : ∀ M, 0 ≤ M → 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M :=
    fun M hM => finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM
  have hZ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg (coulombCellAmplitude_pos hL).le
  have hcJ : 0 ≤ gridFlowConst sys L := gridFlowConst_nonneg sys hL
  have hg : 0 < 2 * Real.pi / L := by positivity
  unfold gridTailConst
  dsimp only
  generalize relB sys L Hunit = b at hb0 ⊢
  generalize sys.maxMass = m at hm0 ⊢
  generalize finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker = Ct at hCt0 ⊢
  generalize finiteCoulombPhysicalMassConstant sys L Hunit = Cm at hC ⊢
  generalize Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (coulombCellAmplitude L) = Z at hZ ⊢
  generalize gridFlowConst sys L = cJ at hcJ ⊢
  generalize 2 * Real.pi / L = g at hg ⊢
  have hΞ₀ : 0 ≤ 2 * hu + 2 * b * s0 := by positivity
  have hΞ₁ : 0 ≤ 2 * hv + 2 * b * hs := by positivity
  have hc0 := hCt0 (m * (s0 + 2 * (2 * hu + 2 * b * s0))) (by positivity)
  positivity

lemma capGridConsts_nonneg (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (Hunit : ℝ)
    (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit) {Blow Cs Bker lam0 s0 hu hs hv : ℝ}
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker) (hs0 : 0 ≤ s0) (hhu : 0 ≤ hu)
    (hhs : 0 ≤ hs) (hhv : 0 ≤ hv) :
    0 ≤ (capGridConsts sys L Hunit Blow Cs Bker lam0 s0 hu hs hv).1 ∧
      0 ≤ (capGridConsts sys L Hunit Blow Cs Bker lam0 s0 hu hs hv).2.1 ∧
      0 ≤ (capGridConsts sys L Hunit Blow Cs Bker lam0 s0 hu hs hv).2.2 := by
  have hDg := gridTailConst_nonneg sys hL Hunit hC (Blow := Blow) (Cs := Cs) (Bker := Bker)
    hBlow hCs hBker hs0 hhu hhs hhv
  have hb0 : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hm0 : 0 ≤ sys.maxMass := by linarith [sys.one_le_maxMass]
  have hCt0 : ∀ M, 0 ≤ M → 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M :=
    fun M hM => finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM
  have hZ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg (coulombCellAmplitude_pos hL).le
  have hcJ : 0 ≤ gridFlowConst sys L := gridFlowConst_nonneg sys hL
  have hg : 0 < 2 * Real.pi / L := by positivity
  unfold capGridConsts
  dsimp only
  generalize gridTailConst sys L Hunit Blow Cs Bker s0 hu hs hv = Dg at hDg ⊢
  generalize relB sys L Hunit = b at hb0 ⊢
  generalize sys.maxMass = m at hm0 ⊢
  generalize finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker = Ct at hCt0 ⊢
  generalize Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (coulombCellAmplitude L) = Z at hZ ⊢
  generalize gridFlowConst sys L = cJ at hcJ ⊢
  generalize 2 * Real.pi / L = g at hg ⊢
  have hΞ₀ : 0 ≤ 2 * hu + 2 * b * s0 := by positivity
  have hΞ₁ : 0 ≤ 2 * hv + 2 * b * hs := by positivity
  have hc0 := hCt0 (m * (s0 + 2 * (2 * hu + 2 * b * s0))) (by positivity)
  have hc1 := hCt0 1 zero_le_one
  refine ⟨by positivity, by positivity, by positivity⟩


/-! ## The capped grid bound: rates and optimisation -/

section Rates

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **`thm:mult-cap` on the grid, fixed cap, rates** (Fourier side). Under the hypotheses of
`grid_capped_error`: `|Δ⟨A_r⟩(t)| ≤ c₁ K^{-3} + c₂ κ^{-3} + c₃ t κ^{3/2} K^{-5/2}` with
`(c₁, c₂, c₃) = capGridConsts` (independent of `K`, `κ`, the kernel and `t`). -/
theorem grid_capped_fixed_rate (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κg : Lat3 → ℝ}
    (hκg : IsGridKernel (coulombCellAmplitude L) m κg)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κg
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κg (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κg (2 * Real.pi / L) x))) t)
    (Blow Cs Bker : ℝ) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (r : Fin eta) {κ lam0 : ℝ} (hl : 1 ≤ lam0) (h4g : 4 * (2 * Real.pi / L) ≤ lam0)
    (hlk : lam0 ≤ κ) (hκK : κ ≤ (2 * Real.pi / L) * m) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let c := capGridConsts sys L Hunit Blow Cs Bker lam0 ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖
    let ψg := Ug t (regCoeff m (molecularH2StateMap eta g u₀))
    |(regKin sys g r).expect (U t (molecularH2StateMap eta g u₀)) - regExpect sys g r ψg| ≤
      c.1 * (1 / K) ^ 3 + c.2.1 * (1 / κ) ^ 3 +
        c.2.2 * t * (κ * Real.sqrt κ) * Real.sqrt (1 / K) ^ 5 := by
  intro g K c ψg
  have hM := sys.one_le_maxMass
  have hm0 : 0 ≤ sys.maxMass := by linarith
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  set S0 := ‖molecularH2StateMap eta g u₀‖ with hS0def
  set Ξ₀ := 2 * ‖H u₀‖ + 2 * relB sys L Hunit * S0 with hΞ₀def
  set Ξ₁ := 2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta g v₀‖ with hΞ₁def
  set M₀ := sys.maxMass * (S0 + 2 * Ξ₀) with hM₀def
  set C₀ := finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M₀ with hC₀def
  set Zg := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
    with hZgdef
  set Xa := (1 + 1 / g ^ 2) * M₀ with hXadef
  set cJ := gridFlowConst sys L with hcJdef
  set Xb := 5 / 3 * Xa + cJ * S0 with hXbdef
  set β := 2 * sys.maxMass * Ξ₁ + C₀ with hβdef
  set Dg := gridTailConst sys L Hunit Blow Cs Bker S0 ‖H u₀‖ ‖molecularH2StateMap eta g v₀‖
    ‖H v₀‖ with hDgdef
  set Da := (1 + 2 * sys.maxMass) * β with hDadef
  set Db := (1 + 8 * sys.maxMass) * Dg with hDbdef
  set Y := (S0 + Ξ₀) + (S0 + g ^ 2 / 2 * Xb) with hYdef
  set cW := 5 / 3 * (1 + 2 / g ^ 2) + cJ with hcWdef
  have hS0 : 0 ≤ S0 := norm_nonneg _
  have h2b : 0 ≤ 2 * relB sys L Hunit := mul_nonneg zero_le_two hb
  have hΞ₀ : 0 ≤ Ξ₀ := add_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) (mul_nonneg h2b hS0)
  have hΞ₁ : 0 ≤ Ξ₁ := add_nonneg (mul_nonneg zero_le_two (norm_nonneg _))
    (mul_nonneg h2b (norm_nonneg _))
  have hM₀ : 0 ≤ M₀ := mul_nonneg hm0 (add_nonneg hS0 (mul_nonneg zero_le_two hΞ₀))
  have hC₀ : 0 ≤ C₀ := finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM₀
  have hC1 : 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker 1 :=
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker zero_le_one
  have hZg : 0 ≤ Zg := Zc_nonneg hγ
  have hcJ : 0 ≤ cJ := gridFlowConst_nonneg sys hL
  have hXa : 0 ≤ Xa := mul_nonneg (by positivity) hM₀
  have hXb : 0 ≤ Xb := add_nonneg (mul_nonneg (by norm_num) hXa) (mul_nonneg hcJ hS0)
  have hβ : 0 ≤ β := add_nonneg (mul_nonneg (mul_nonneg zero_le_two hm0) hΞ₁) hC₀
  have hDg : 0 ≤ Dg := gridTailConst_nonneg sys hL Hunit hC hBlow hCs hBker hS0 (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _)
  have hDa : 0 ≤ Da := mul_nonneg (add_nonneg zero_le_one (mul_nonneg zero_le_two hm0)) hβ
  have hDb : 0 ≤ Db := mul_nonneg (add_nonneg zero_le_one (mul_nonneg (by norm_num) hm0)) hDg
  have hY : 0 ≤ Y := add_nonneg (add_nonneg hS0 hΞ₀)
    (add_nonneg hS0 (mul_nonneg (by positivity) hXb))
  have hcW : 0 ≤ cW := add_nonneg (mul_nonneg (by norm_num) (by positivity)) hcJ
  have hκ1 : 1 ≤ κ := hl.trans hlk
  refine (grid_capped_error sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph hderiv m hm hK hκg Ug
    hg0 hgcomm hgderiv Blow Cs Bker hBlow hCs hBker hAmplitude hBkerScale hCsScale u₀ v₀ huv r hl
    h4g hlk hκK ht).trans ?_
  exact cap_grid_rate_arith (η := (eta : ℝ)) (mm := sys.maxMass) (Ξ₁ := Ξ₁) (C₀ := C₀)
    (C1 := finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker 1) (g := g) (t := t)
    (Zg := Zg) (Xa := Xa) (β := β) (Dg := Dg) (κ := κ) (lam0 := lam0) (Y := Y) (Da := Da)
    (Db := Db) (cW := cW) (m := m)
    (Ct := fun M => finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M)
    (Nat.cast_nonneg eta) hM hΞ₁ hC₀ hg hm hK ht hZg hXa
    (fun M => tailConstant_linear sys L Hunit Blow Cs Bker M) hC1 hκ1 hY hDa hDb hcW

include hKernel hL hPeriodic in
/-- **The energy bound on the grid.** The exact and grid expectations of `A_r` both lie in
`[0, ‖ψ₀‖ Ξ₀]` and `[0, ‖ψ₀‖ (g²/2) X_b]`, so they differ by at most `gridTrivConst`, uniformly in
the time and the register. -/
theorem grid_expect_pair_le (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (m : ℕ) {κg : Lat3 → ℝ} (hκb : ∀ x, |κg x| ≤ coulombCellAmplitude L * coul x)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κg
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κg (2 * Real.pi / L) (Ug t x))
    (u₀ : MolecularFourierH2 eta) (r : Fin eta) (t : ℝ) :
    |(regKin sys (2 * Real.pi / L) r).expect (U t (molecularH2StateMap eta (2 * Real.pi / L) u₀)) -
        regExpect sys (2 * Real.pi / L) r
          (Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)))| ≤
      gridTrivConst sys L Hunit ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ ‖H u₀‖ := by
  set g := 2 * Real.pi / L with hgdef
  set S := molecularH2StateMap eta g
  set b := relB sys L Hunit with hbdef
  set S0 := ‖S u₀‖ with hS0def
  set Ξ₀ := 2 * ‖H u₀‖ + 2 * b * S0 with hΞ₀def
  set M₀ := sys.maxMass * (S0 + 2 * Ξ₀) with hM₀def
  set Xa := (1 + 1 / g ^ 2) * M₀ with hXadef
  set Xb := 5 / 3 * Xa + gridFlowConst sys L * S0 with hXbdef
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ b := relB_nonneg sys L Hunit hC
  have hg : 0 < g := by positivity
  have hS0 : 0 ≤ S0 := norm_nonneg _
  have hcJ := gridFlowConst_nonneg sys hL
  have hg1 : (0 : ℝ) ≤ 1 + 1 / g ^ 2 := by positivity
  have hΞ₀ : 0 ≤ Ξ₀ := add_nonneg (mul_nonneg zero_le_two (norm_nonneg _))
    (mul_nonneg (mul_nonneg zero_le_two hb) hS0)
  obtain ⟨u, hu1, hu2⟩ := hgraph t u₀
  -- the exact expectation
  have hSu : ‖S u‖ = S0 := by rw [hu1, LinearIsometryEquiv.norm_map]
  have hTu : ‖coulombFourierKineticH2 sys g u‖ ≤ Ξ₀ := by
    have h := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u
    rwa [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
  have ha : (regKin sys g r).expect (S u) ≤ S0 * Ξ₀ := by
    refine ((regKin sys g r).expect_le_norm_mul u).trans ?_
    rw [hSu]
    exact mul_le_mul_of_nonneg_left (((regKin sys g r).norm_h2_le u).trans hTu) hS0
  have ha0 := (regKin sys g r).expect_nonneg (S u)
  -- the grid expectation
  have hu₀_le : ‖u₀‖ ≤ M₀ := by
    refine (h2norm_le sys L u₀).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    show ‖S u₀‖ + 2 * ‖coulombFourierKineticH2 sys g u₀‖ ≤ S0 + 2 * Ξ₀
    have := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u₀
    linarith
  have ha₀ : ‖wMul (wM (regParticlesOf sys)) (regCoeff m (S u₀))‖ ≤ Xa :=
    (norm_wM_le_wTot (regParticlesOf sys) _).trans ((norm_wTot_regCoeff_stateMap_le hg u₀).trans
      (mul_le_mul_of_nonneg_left hu₀_le hg1))
  have haS₀ : ‖regCoeff m (S u₀)‖ ≤ S0 := norm_regCoeff_le _
  set ψ := Ug t (regCoeff m (S u₀)) with hψdef
  have hψW : ‖wMul (wM (regParticlesOf sys)) ψ‖ ≤ Xb := by
    refine (norm_wM_gridFlow_le sys hL hκb (Ug t) (hgcomm t) _).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left ha₀ (by norm_num))
      (mul_le_mul_of_nonneg_left haS₀ hcJ)
  have hψS : ‖ψ‖ ≤ S0 := by rw [hψdef, LinearIsometryEquiv.norm_map]; exact haS₀
  have hb' : regExpect sys g r ψ ≤ S0 * (g ^ 2 / 2 * Xb) := by
    have h1 : (regExpect sys g r ψ : ℂ) = ⟪ψ, wMul (regKinSym sys g r) ψ⟫_ℂ := by
      rw [regExpect, inner_wMul_self]
    have h2 : |regExpect sys g r ψ| ≤ ‖ψ‖ * ‖wMul (regKinSym sys g r) ψ‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) ψ (wMul (regKinSym sys g r) ψ)
      rw [← h1, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    have h3 : ‖wMul (regKinSym sys g r) ψ‖ ≤ g ^ 2 / 2 * Xb :=
      (norm_regKin_le sys g r ψ).trans (mul_le_mul_of_nonneg_left hψW (by positivity))
    exact (le_abs_self _).trans (h2.trans (mul_le_mul hψS h3 (norm_nonneg _) hS0))
  have hb0 := regExpect_nonneg sys g r ψ
  rw [← hu1]
  have key : |(regKin sys g r).expect (S u) - regExpect sys g r ψ| ≤
      S0 * (Ξ₀ + g ^ 2 / 2 * Xb) := by
    rw [abs_le]
    constructor <;> nlinarith
  exact key

include hKernel hL hPeriodic in
/-- **`thm:mult-cap` on the grid, the sublinear branch** (Fourier side). For `m ≥ 8`,
`K = g m ≥ 8`, a lowest cap `λ₀` with `1 ≤ λ₀`, `4g ≤ λ₀ ≤ K`, and all `t ≥ 0`:
`|⟨ψ(t), A_r ψ(t)⟩ - ⟨ψ_g(t), A_r ψ_g(t)⟩| ≤ C₁ K^{-3} + C₂ t^{2/3} K^{-5/3}` with
`(C₁, C₂) = capGridRateConsts` (independent of `K`, the kernel and `t`). -/
theorem grid_capped_rate (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κg : Lat3 → ℝ}
    (hκg : IsGridKernel (coulombCellAmplitude L) m κg)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κg
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κg (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κg (2 * Real.pi / L) x))) t)
    (Blow Cs Bker : ℝ) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (r : Fin eta) {lam0 : ℝ} (hl : 1 ≤ lam0) (h4g : 4 * (2 * Real.pi / L) ≤ lam0)
    (hlK : lam0 ≤ (2 * Real.pi / L) * m) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let C := capGridRateConsts sys L Hunit Blow Cs Bker lam0 ‖molecularH2StateMap eta g u₀‖
      ‖H u₀‖ ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖
    let ψg := Ug t (regCoeff m (molecularH2StateMap eta g u₀))
    |(regKin sys g r).expect (U t (molecularH2StateMap eta g u₀)) - regExpect sys g r ψg| ≤
      C.1 * (1 / K) ^ 3 + C.2 * t ^ ((2 : ℝ) / 3) * (1 / K) ^ ((5 : ℝ) / 3) := by
  intro g K C ψg
  have hg : 0 < g := by positivity
  have hK1 : 1 ≤ K := hl.trans hlK
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hl0 : 0 ≤ lam0 := zero_le_one.trans hl
  have hX3 : 0 ≤ (1 / K) ^ 3 := pow_nonneg (one_div_nonneg.mpr hKpos.le) 3
  obtain ⟨hc1, hc2, hc3⟩ := capGridConsts_nonneg sys hL Hunit hC (lam0 := lam0)
    (s0 := ‖molecularH2StateMap eta g u₀‖) (hu := ‖H u₀‖)
    (hs := ‖molecularH2StateMap eta g v₀‖) (hv := ‖H v₀‖) (Blow := Blow) (Cs := Cs) (Bker := Bker)
    hBlow hCs hBker (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  set c := capGridConsts sys L Hunit Blow Cs Bker lam0 ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖
    ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖ with hcdef
  set D := gridTrivConst sys L Hunit ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖ with hDdef
  set E := (regKin sys g r).expect (U t (molecularH2StateMap eta g u₀)) -
    regExpect sys g r ψg with hEdef
  have hC1 : C.1 = c.1 + c.2.1 := rfl
  have hC2 : C.2 = c.2.1 + c.2.2 + D * lam0 ^ 3 := rfl
  have htriv : |E| ≤ D := grid_expect_pair_le sys L H hKernel Hunit hL hPeriodic hC U hgraph m
    hκg.bound Ug hgcomm u₀ r t
  have hD0 : 0 ≤ D := (abs_nonneg _).trans htriv
  rw [hC1, hC2]
  -- `s = t^{1/3}` and `k = K^{1/6}`
  obtain ⟨s, hs0, hst, hs2⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 3 = t ∧ t ^ ((2 : ℝ) / 3) = s ^ 2 := by
    refine ⟨t ^ ((1 : ℝ) / 3), Real.rpow_nonneg ht _, ?_, ?_⟩
    · rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
      norm_num
    · rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
      norm_num
  obtain ⟨k, hk, hKk, hk10⟩ : ∃ k : ℝ, 0 < k ∧ K = k ^ 6 ∧
      (1 / K) ^ ((5 : ℝ) / 3) = (1 / k) ^ 10 := by
    refine ⟨K ^ ((1 : ℝ) / 6), Real.rpow_pos_of_pos hKpos _, ?_, ?_⟩
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
      norm_num
    · have e : (1 / K) = (1 / K ^ ((1 : ℝ) / 6)) ^ 6 := by
        rw [div_pow, one_pow, ← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
        norm_num
      have h1 : (0 : ℝ) ≤ 1 / K ^ ((1 : ℝ) / 6) :=
        (one_div_pos.mpr (Real.rpow_pos_of_pos hKpos _)).le
      rw [e, ← Real.rpow_natCast, ← Real.rpow_mul h1, ← Real.rpow_natCast]
      norm_num
  rw [hs2, hk10]
  have hY : 0 ≤ s ^ 2 * (1 / k) ^ 10 := mul_nonneg (sq_nonneg s) (pow_nonneg (by positivity) 10)
  have hDl : 0 ≤ D * lam0 ^ 3 := mul_nonneg hD0 (pow_nonneg hl0 3)
  by_cases h3 : k ^ 10 < lam0 ^ 3 * s ^ 2
  · -- `t ≳ K^{5/2}`: the energy bound
    have hq : 1 ≤ lam0 ^ 3 * s ^ 2 * (1 / k) ^ 10 := by
      have e : lam0 ^ 3 * s ^ 2 * (1 / k) ^ 10 = lam0 ^ 3 * s ^ 2 / k ^ 10 := by ring
      rw [e, le_div_iff₀ (pow_pos hk 10), one_mul]
      exact h3.le
    have e1 := mul_le_mul_of_nonneg_left hq hD0
    have e2 : 0 ≤ (c.1 + c.2.1) * (1 / K) ^ 3 := mul_nonneg (add_nonneg hc1 hc2) hX3
    have e3 : 0 ≤ (c.2.1 + c.2.2) * (s ^ 2 * (1 / k) ^ 10) := mul_nonneg (add_nonneg hc2 hc3) hY
    refine htriv.trans ?_
    linarith
  replace h3 : lam0 ^ 3 * s ^ 2 ≤ k ^ 10 := not_lt.mp h3
  have hfix := fun {κ : ℝ} (hlk : lam0 ≤ κ) (hκK : κ ≤ (2 * Real.pi / L) * m) =>
    grid_capped_fixed_rate sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph hderiv m hm hK hκg Ug
      hg0 hgcomm hgderiv Blow Cs Bker hBlow hCs hBker hAmplitude hBkerScale hCsScale u₀ v₀ huv r
      hl h4g hlk hκK ht
  by_cases h1 : s ^ 2 * k ^ 8 ≤ 1
  · -- `t ≤ K^{-2}`: the cap `κ = K`
    have h : |E| ≤ c.1 * (1 / K) ^ 3 + c.2.1 * (1 / K) ^ 3 +
        c.2.2 * t * (K * Real.sqrt K) * Real.sqrt (1 / K) ^ 5 := hfix hlK le_rfl
    have h' := gcap_regime_small (c1 := c.1) (c2 := c.2.1) hk hKk hs0 hc3 hst h1
    have e1 : 0 ≤ c.2.1 * (s ^ 2 * (1 / k) ^ 10) := mul_nonneg hc2 hY
    have e2 : 0 ≤ D * lam0 ^ 3 * (s ^ 2 * (1 / k) ^ 10) := mul_nonneg hDl hY
    refine h.trans (h'.trans ?_)
    linarith
  · -- the balancing cap `κ = w²`, `w³ s = k⁵`
    have h1' : 1 ≤ s ^ 2 * k ^ 8 := (not_le.mp h1).le
    have hspos : 0 < s := by
      rcases hs0.lt_or_eq with h | h
      · exact h
      · exfalso
        apply h1
        rw [← h]
        simp
    have hks : 0 < k ^ 5 / s := div_pos (pow_pos hk 5) hspos
    obtain ⟨w, hw, hws⟩ : ∃ w : ℝ, 0 < w ∧ w ^ 3 * s = k ^ 5 := by
      refine ⟨(k ^ 5 / s) ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hks _, ?_⟩
      have e : ((k ^ 5 / s) ^ ((1 : ℝ) / 3)) ^ 3 = k ^ 5 / s := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hks.le]
        norm_num
      rw [e, div_mul_cancel₀ _ hspos.ne']
    obtain ⟨hlw, hwK⟩ := gcap_mid_bounds hk hKk hspos hws h1' h3
    have h : |E| ≤ c.1 * (1 / K) ^ 3 + c.2.1 * (1 / w ^ 2) ^ 3 +
        c.2.2 * t * (w ^ 2 * Real.sqrt (w ^ 2)) * Real.sqrt (1 / K) ^ 5 := hfix hlw hwK
    rw [gcap_regime_mid hk hKk hspos hw hst hws] at h
    have e1 : 0 ≤ c.2.1 * (1 / K) ^ 3 := mul_nonneg hc2 hX3
    have e2 : 0 ≤ D * lam0 ^ 3 * (s ^ 2 * (1 / k) ^ 10) := mul_nonneg hDl hY
    refine h.trans ?_
    linarith

end Rates

end PlaneWaveKinetic

end DevK11
-- END SOURCE dev/DevK11.lean

-- BEGIN SOURCE dev/DevK12.lean
-- SHA256 e701e4969b75a887d99a52f84040ef4ea5a778ca50f75e394edf4d36f5614fa0
section DevK12

/-!
# `thm:mult-cap` (grid) and `cor:stopping2` (grid) in position space

* `grid_capped_position`: the sublinear branch `C₁ K^{-3} + C₂ t^{2/3} K^{-5/3}` of the capped grid
  bound for the position-space grid state `ψ_g(t) = e^{-iH_pos t} P ψ₀` with the kinetic energy
  applied through the DFT, at the canonical constants of the cell.
* `grid_capped_min_position`: with `prop:mult-grid` (`grid_kinetic_position`), the minimum form
  `D₁ K^{-3} + D₂ min(t K^{-1}, t^{2/3} K^{-5/3})` of `eq:mult-cap-grid`; `thm_mult_cap_grid` with
  its propagators.
* `stopping_window_grid` (`cor:stopping2`, grid route): the secant-slope estimator deviates by at
  most `(D₂ min(K^{-1}, T^{-1/3} K^{-5/3}) + 2 D₁ K^{-3}/T)/v_p`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate lp ENNReal Topology
open Filter Set

namespace PlaneWaveKinetic

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **`thm:mult-cap` on the grid in position space, the sublinear branch.** In the setting of
`grid_kinetic_position`, for a lowest cap `λ₀` with `1 ≤ λ₀`, `4g ≤ λ₀ ≤ K` and all `t ≥ 0`:
`|⟨ψ(t), A_r ψ(t)⟩ - ⟨ψ_g(t), A_r ψ_g(t)⟩| ≤ C₁ K^{-3} + C₂ t^{2/3} K^{-5/3}` with
`(C₁, C₂) = capGridRateConsts` at the canonical constants and `(‖ψ₀‖, ‖h₀‖, ‖h₀‖, ‖h₁‖)`. -/
theorem grid_capped_position (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (ψ₀ h₀ h₁ : MolecularPositionL2 eta) (hψ₀ : HasCoulombHamiltonian sys L ψ₀ h₀)
    (hh₀ : HasCoulombHamiltonian sys L h₀ h₁) (r : Fin eta) {lam0 : ℝ} (hl : 1 ≤ lam0)
    (h4g : 4 * (2 * Real.pi / L) ≤ lam0) (hlK : lam0 ≤ (2 * Real.pi / L) * m) {t : ℝ}
    (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let C := capGridRateConsts sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) lam0 ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
    let ψg := posConj (Ug t) (idft (regCoeff m ((physMap eta).symm ψ₀)))
    |(regKin sys g r).posExpect (U t ψ₀) - posKinExpect sys g r ψg| ≤
      C.1 * (1 / K) ^ 3 + C.2 * t ^ ((2 : ℝ) / 3) * (1 / K) ^ ((5 : ℝ) / 3) := by
  intro g K C ψg
  have hPeriodic := canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨H, hKernel, -⟩ :=
    exists_coulombFourierH2Operator sys L molecularCanonicalUnitHardyConstant hL hPeriodic
  have hiff := hasCoulombHamiltonian_iff_phys sys L hL H hKernel
  -- the propagator on the Fourier side
  set UF : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
    fun s => ((physMap eta).trans (U s)).trans (physMap eta).symm with hUFdef
  have hUF : ∀ s x, UF s x = (physMap eta).symm (U s (physMap eta x)) := fun s x => rfl
  have h0F : ∀ x, UF 0 x = x := by
    intro x
    rw [hUF, hU0, LinearIsometryEquiv.symm_apply_apply]
  have hgraphF : ∀ s u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        UF s (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = UF s (H u) := by
    intro s u
    obtain ⟨u', h1, h2⟩ := (hiff _ _).mp (hUgraph s _ _ ((hiff _ _).mpr ⟨u, rfl, rfl⟩))
    refine ⟨u', ?_, ?_⟩
    · rw [hUF, ← h1, LinearIsometryEquiv.symm_apply_apply]
    · rw [hUF, ← h2, LinearIsometryEquiv.symm_apply_apply]
  have hderivF : ∀ s u, HasDerivAt (fun r => UF r (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • UF s (H u))) s := by
    intro s u
    have h := hUderiv s _ _ ((hiff _ _).mpr ⟨u, rfl, rfl⟩)
    have h2 := (((physMap eta).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt s h
    simp only [ContinuousLinearMap.coe_restrictScalars'] at h2
    rw [map_neg, map_smul] at h2
    exact h2
  -- the initial state in `D(H²)`
  obtain ⟨u₀, hu₀1, hu₀2⟩ := (hiff ψ₀ h₀).mp hψ₀
  obtain ⟨v₀, hv₀1, hv₀2⟩ := (hiff h₀ h₁).mp hh₀
  have huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀ :=
    (physMap eta).injective (hu₀2.trans hv₀1.symm)
  have hx₀ : (physMap eta).symm ψ₀ = molecularH2StateMap eta (2 * Real.pi / L) u₀ := by
    rw [← hu₀1, LinearIsometryEquiv.symm_apply_apply]
  have hψt : U t ψ₀ = physMap eta (UF t (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    rw [hUF, LinearIsometryEquiv.apply_symm_apply, hu₀1]
  -- the grid expectation on the register
  have hdψ : dft ψg = Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    show dft (posConj (Ug t) (idft (regCoeff m ((physMap eta).symm ψ₀)))) = _
    rw [dft_posConj, dft_idft, hx₀]
  have hψg : posKinExpect sys g r ψg =
      regExpect sys g r (Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀))) := by
    rw [posKinExpect, hdψ]
  rw [hψt, posExpect_physMap, hψg]
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  have h := grid_capped_rate sys L H hKernel molecularCanonicalUnitHardyConstant hL hPeriodic
    (finiteCoulombPhysicalMassConstant_nonneg _ _ _) UF h0F hgraphF hderivF m hm hK hκ Ug hg0
    hgcomm hgderiv _ _ _ hBlow hCs hBker hLow hKernelScale hSobolev u₀ v₀ huv r hl h4g hlK ht
  dsimp only at h
  have e1 : ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ = ‖ψ₀‖ := by
    rw [← hu₀1, LinearIsometryEquiv.norm_map]
  have e2 : ‖H u₀‖ = ‖h₀‖ := by rw [← hu₀2, LinearIsometryEquiv.norm_map]
  have e3 : ‖molecularH2StateMap eta (2 * Real.pi / L) v₀‖ = ‖h₀‖ := by
    rw [← hv₀1, LinearIsometryEquiv.norm_map]
  have e4 : ‖H v₀‖ = ‖h₁‖ := by rw [← hv₀2, LinearIsometryEquiv.norm_map]
  rw [e1, e2, e3, e4] at h
  exact h

/-- The constants `(D₁, D₂)` of `eq:mult-cap-grid` in position space for the data norms
`‖ψ₀‖ = s0`, `‖H ψ₀‖ = hu`, `‖H² ψ₀‖ = hv` and the lowest cap `λ₀`: the larger of the
`prop:mult-grid` constants and the sublinear-branch constants. -/
noncomputable def gridCapMinConsts (sys : CoulombSystem eta ν) (L lam0 s0 hu hv : ℝ) : ℝ × ℝ :=
  let A := gridKinConsts sys L molecularCanonicalUnitHardyConstant
    (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
    (molecularCanonicalKernelConstant L) s0 hu hu hv
  let C := capGridRateConsts sys L molecularCanonicalUnitHardyConstant
    (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
    (molecularCanonicalKernelConstant L) lam0 s0 hu hu hv
  (max A.1 C.1, max A.2 C.2)

/-- **`thm:mult-cap` on the grid** (`eq:mult-cap-grid`), position space. In the setting of
`grid_kinetic_position`, for a lowest cap `λ₀` with `1 ≤ λ₀`, `4g ≤ λ₀ ≤ K` and all `t ≥ 0`:
`|⟨ψ(t), A_r ψ(t)⟩ - ⟨ψ_g(t), A_r ψ_g(t)⟩| ≤ D₁ K^{-3} + D₂ min(t K^{-1}, t^{2/3} K^{-5/3})`,
with `(D₁, D₂) = gridCapMinConsts` at `(λ₀, ‖ψ₀‖, ‖h₀‖, ‖h₁‖)`. -/
theorem grid_capped_min_position (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (ψ₀ h₀ h₁ : MolecularPositionL2 eta) (hψ₀ : HasCoulombHamiltonian sys L ψ₀ h₀)
    (hh₀ : HasCoulombHamiltonian sys L h₀ h₁) (r : Fin eta) {lam0 : ℝ} (hl : 1 ≤ lam0)
    (h4g : 4 * (2 * Real.pi / L) ≤ lam0) (hlK : lam0 ≤ (2 * Real.pi / L) * m) {t : ℝ}
    (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let D := gridCapMinConsts sys L lam0 ‖ψ₀‖ ‖h₀‖ ‖h₁‖
    let ψg := posConj (Ug t) (idft (regCoeff m ((physMap eta).symm ψ₀)))
    |(regKin sys g r).posExpect (U t ψ₀) - posKinExpect sys g r ψg| ≤
      D.1 * (1 / K) ^ 3 +
        D.2 * min (t * (1 / K)) (t ^ ((2 : ℝ) / 3) * (1 / K) ^ ((5 : ℝ) / 3)) := by
  intro g K D ψg
  have hg : 0 < g := by positivity
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (hl.trans hlK)
  have hA := grid_kinetic_position sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm hgderiv
    ψ₀ h₀ h₁ hψ₀ hh₀ r ht
  have hB := grid_capped_position sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm hgderiv
    ψ₀ h₀ h₁ hψ₀ hh₀ r hl h4g hlK ht
  dsimp only at hA hB
  refine le_max_min_combine (pow_nonneg (one_div_nonneg.mpr hKpos.le) 3)
    (mul_nonneg ht (one_div_nonneg.mpr hKpos.le))
    (mul_nonneg (Real.rpow_nonneg ht _) (Real.rpow_nonneg (one_div_nonneg.mpr hKpos.le) _))
    (hA.trans_eq ?_) (hB.trans_eq ?_)
  · ring
  · ring

/-- **`thm:mult-cap` on the grid with its propagators.** For a periodic Coulomb system there is a
propagator `U` on `L²((T³)^η)` (unitary group, strongly continuous, preserving the graph of the
Hamiltonian, solving the Schrödinger equation on it, and the only evolution that does so), and for
every register radius `2m` and every real, even kernel `κ` of the class `𝒦_K` (`K = 2πm/L`) a
grid propagator `U_g` (`e^{-iH_pos t}` on the grid values), such that for all `ψ₀ ∈ D(H²)`
(`H ψ₀ = h₀`, `H h₀ = h₁`), every particle `r` and every lowest cap `λ₀ ≥ max(1, 4g)`, with
`(D₁, D₂) = gridCapMinConsts` at `(λ₀, ‖ψ₀‖, ‖h₀‖, ‖h₁‖)` (independent of `m`, the kernel and
`t`): for `m ≥ 8`, `K ≥ max(8, λ₀)` and `t ≥ 0`,
`|⟨ψ(t), A_r ψ(t)⟩ - ⟨ψ_g(t), A_r ψ_g(t)⟩| ≤ D₁ K^{-3} + D₂ min(t K^{-1}, t^{2/3} K^{-5/3})`. -/
theorem thm_mult_cap_grid (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) :
    ∃ U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, Continuous fun t => U t ψ) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasCoulombHamiltonian sys L (U t f) (U t h)) ∧
      (∀ t f h, HasCoulombHamiltonian sys L f h →
        HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) ∧
      (∀ φ ζ : ℝ → MolecularPositionL2 eta, (∀ t, HasCoulombHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
        (∀ x, Continuous fun t => Ug t x) ∧
        (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t x)) ∧
        (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
        ∀ ψ₀ h₀ h₁ : MolecularPositionL2 eta, HasCoulombHamiltonian sys L ψ₀ h₀ →
          HasCoulombHamiltonian sys L h₀ h₁ →
          ∀ (r : Fin eta) (lam0 : ℝ), 1 ≤ lam0 → 4 * (2 * Real.pi / L) ≤ lam0 →
          let D := gridCapMinConsts sys L lam0 ‖ψ₀‖ ‖h₀‖ ‖h₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → lam0 ≤ (2 * Real.pi / L) * m →
            ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let ψg := Ug t (idft (regCoeff m ((physMap eta).symm ψ₀)))
            |(regKin sys (2 * Real.pi / L) r).posExpect (U t ψ₀) -
                posKinExpect sys (2 * Real.pi / L) r ψg| ≤
              D.1 * (1 / K) ^ 3 +
                D.2 * min (t * (1 / K)) (t ^ ((2 : ℝ) / 3) * (1 / K) ^ ((5 : ℝ) / 3)) := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, -, -⟩ := exists_coulombPropagator sys L hL
  refine ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, fun m κ hκ => ?_⟩
  obtain ⟨Ur, hr0, -, -, hrcomm, hrderiv, hp0, hpadd, hpcont, hpcomm, hpderiv⟩ :=
    exists_posPropagator (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) hκ.even
      (2 * Real.pi / L)
  refine ⟨fun t => posConj (Ur t), hp0, hpadd, hpcont, hpcomm, hpderiv, ?_⟩
  intro ψ₀ h₀ h₁ hψ₀ hh₀ r lam0 hl h4g D hm hK hlK t ht K ψg
  exact grid_capped_min_position sys L hL U h0 hgraph hderiv m hm hK hκ Ur hr0 hrcomm hrderiv ψ₀
    h₀ h₁ hψ₀ hh₀ r hl h4g hlK ht

/-- **`cor:stopping2`, grid route (window law).** In the setting of `grid_capped_min_position`,
the secant-slope estimator `Ŝ = (⟨A_r⟩(T) - ⟨A_r⟩(0))/(v_p T)` over a window `[0, T]`, evaluated
on the grid trajectory, deviates from the same functional of the exact trajectory by at most
`(D₂ min(K^{-1}, T^{-1/3} K^{-5/3}) + 2 D₁ K^{-3}/T)/v_p`. -/
theorem stopping_window_grid (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (ψ₀ h₀ h₁ : MolecularPositionL2 eta) (hψ₀ : HasCoulombHamiltonian sys L ψ₀ h₀)
    (hh₀ : HasCoulombHamiltonian sys L h₀ h₁) (r : Fin eta) {lam0 : ℝ} (hl : 1 ≤ lam0)
    (h4g : 4 * (2 * Real.pi / L) ≤ lam0) (hlK : lam0 ≤ (2 * Real.pi / L) * m) {vp T : ℝ}
    (hvp : 0 < vp) (hT : 0 < T) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let D := gridCapMinConsts sys L lam0 ‖ψ₀‖ ‖h₀‖ ‖h₁‖
    let ψg : ℝ → EuclideanSpace ℂ (RCfg eta m) := fun s =>
      posConj (Ug s) (idft (regCoeff m ((physMap eta).symm ψ₀)))
    let μ := regKin sys g r
    |(μ.posExpect (U T ψ₀) - μ.posExpect (U 0 ψ₀)) / (vp * T) -
        (posKinExpect sys g r (ψg T) - posKinExpect sys g r (ψg 0)) / (vp * T)| ≤
      (D.2 * min (1 / K) ((1 / K) ^ ((5 : ℝ) / 3) / T ^ ((1 : ℝ) / 3)) +
        2 * D.1 * (1 / K) ^ 3 / T) / vp := by
  intro g K D ψg μ
  have h0 := grid_capped_min_position sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
    hgderiv ψ₀ h₀ h₁ hψ₀ hh₀ r hl h4g hlK (le_refl 0)
  have hT' := grid_capped_min_position sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
    hgderiv ψ₀ h₀ h₁ hψ₀ hh₀ r hl h4g hlK hT.le
  exact (secant_slope_le hvp hT h0 hT').trans (le_of_eq (window_arith hvp hT))

end PlaneWaveKinetic

end DevK12
-- END SOURCE dev/DevK12.lean

/-! ════════════════════════════════════════════════════════════════════
## Part `SpinGrid`
════════════════════════════════════════════════════════════════════ -/

/-!
The grid dynamics and the grid kinetic energy with internal spin (namespace `PlaneWaveSpin`; former
development files `dev/DevSP2.lean` and `dev/DevSP3.lean`).
-/

-- BEGIN SOURCE dev/DevSP2.lean
-- SHA256 f6f6485ac3512412977147992b8b6b1e33ac0afb0ab631169f9e49fe0061db60
section DevSP2

/-!
# Grid dynamics and grid kinetic energy with internal spin

The grid Hamiltonian of the grid files on the spin-inclusive grid states
`CoulombGridSpinState eta D m` (one grid function on the padded register for each spin
configuration) is `spinHpos`, `Hpos` on each spin component. Its propagator is the grid
propagator on each component (`spinGridProp`), the collocated observable acts on each component
(`spinPosObs`), and so does the kinetic energy applied through the DFT (`spinPosKinExpect`). The
spin-inclusive errors are therefore sums of the component errors, and the transfer of DevSP1
gives the spin-inclusive bounds at the spin-inclusive norms, with the same constants:

* `prop:grid-dyn`: `grid_observable_position_spin` (position space, raw form),
  `thm_grid_dyn_spin` (with the propagators, under `(Hχ)`), `thm_grid_dyn_min_spin`
  (`min {1, ·}`), and the normalised grid state `grid_observable_normalised_spin` with its
  threshold `grid_normalisation_threshold_spin` (`cor:norm` at cutoff `2K`; the spinless
  threshold `grid_normalisation_threshold` is in DevGD7);
* `thm:grid-dyn-sharp`: `grid_observable_position_sharp_spin`, `thm_grid_dyn_sharp_spin`,
  `thm_grid_dyn_sharp_min_spin`.

The raw bounds are transferred (`l2quad_gridRaw`, `l2quad_gridSharpRaw`, with `l2sub_gridPhi`
for the second-moment budget), and the `(Hχ)` form is derived once at the spin-inclusive norms
(`grid_final_le`). The grid kinetic energy with spin is in DevSP3.

The exchange sector plays no role: the bounds hold for every spin-inclusive `Ψ₀ ∈ D(H²)`, in
particular for the physical states (`IsCoulombSpinSector sys dim Ψ₀`, with every `dim s ≤ D`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate lp ENNReal Topology
open Filter Set UnitAddTorus

namespace PlaneWaveSpin

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics PlaneWaveKinetic

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The spin-inclusive grid -/

section SpinGrid

variable {S : Type} [Fintype S] {m : ℕ}

/-- A family of isometries `V(t)` of the grid functions applied to each spin component
(`V(t) ⊗ 1`). -/
noncomputable def spinGridProp
    (V : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)) (t : ℝ) :
    PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m)) ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m)) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun _ => V t

lemma spinGridProp_apply
    (V : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)) (t : ℝ)
    (Φ : PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m))) (σ : S) :
    spinGridProp V t Φ σ = V t (Φ σ) :=
  rfl

/-- **The spin-inclusive grid propagator.** If `V` is a propagator of `H_pos` on the grid
functions, `V ⊗ 1` is a propagator of the spin-independent grid Hamiltonian `spinHpos`, and it
acts on every spin component by `V(t)`. -/
theorem spinGridProp_spec (P : RegParticles eta) (Nn : PosNuclei ν) (κ : Lat3 → ℝ) (g : ℝ)
    (V : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (h0 : ∀ x, V 0 x = x) (hadd : ∀ s t x, V (s + t) x = V s (V t x))
    (hcont : ∀ x, Continuous fun t => V t x)
    (hcomm : ∀ t x, V t (Hpos P Nn κ g x) = Hpos P Nn κ g (V t x))
    (hderiv : ∀ t x, HasDerivAt (fun s => V s x) (-(Complex.I • V t (Hpos P Nn κ g x))) t) :
    (∀ Φ, spinGridProp (S := S) V 0 Φ = Φ) ∧
      (∀ s t Φ, spinGridProp (S := S) V (s + t) Φ = spinGridProp V s (spinGridProp V t Φ)) ∧
      (∀ Φ, Continuous fun t => spinGridProp (S := S) V t Φ) ∧
      (∀ t Φ, spinGridProp (S := S) V t (spinHpos P Nn κ g Φ) =
        spinHpos P Nn κ g (spinGridProp V t Φ)) ∧
      (∀ t Φ, HasDerivAt (fun s => spinGridProp (S := S) V s Φ)
        (-(Complex.I • spinGridProp V t (spinHpos P Nn κ g Φ))) t) ∧
      (∀ t, ∃ W : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        ∀ Φ σ, spinGridProp (S := S) V t Φ σ = W (Φ σ)) := by
  refine ⟨fun Φ => ?_, fun s t Φ => ?_, fun Φ => ?_, fun t Φ => ?_, fun t Φ => ?_,
    fun t => ⟨V t, fun Φ σ => spinGridProp_apply V t Φ σ⟩⟩
  · refine PiLp.ext fun σ => ?_
    rw [spinGridProp_apply]
    exact h0 _
  · refine PiLp.ext fun σ => ?_
    rw [spinGridProp_apply, spinGridProp_apply, spinGridProp_apply]
    exact hadd s t _
  · exact (PiLp.continuous_toLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m))).comp
      (continuous_pi fun σ => hcont (Φ σ))
  · refine PiLp.ext fun σ => ?_
    rw [spinGridProp_apply, spinHpos_apply, spinHpos_apply, spinGridProp_apply]
    exact hcomm t _
  · have hd : HasDerivAt (fun s => (fun σ => V s (Φ σ) : S → EuclideanSpace ℂ (RCfg eta m)))
        (fun σ => -(Complex.I • V t (Hpos P Nn κ g (Φ σ)))) t :=
      hasDerivAt_pi.2 fun σ => hderiv t (Φ σ)
    have hd2 := (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : S => EuclideanSpace ℂ (RCfg eta m))).symm.hasFDerivAt.comp_hasDerivAt t hd
    have e1 : (fun s => spinGridProp (S := S) V s Φ) = (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : S => EuclideanSpace ℂ (RCfg eta m))).symm ∘ fun s σ => V s (Φ σ) :=
      rfl
    have e2 : -(Complex.I • spinGridProp V t (spinHpos P Nn κ g Φ)) =
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : S => EuclideanSpace ℂ (RCfg eta m))).symm
          (fun σ => -(Complex.I • V t (Hpos P Nn κ g (Φ σ)))) :=
      rfl
    rw [e1, e2]
    exact hd2

/-- The collocated observable `χ(x_{j_a})` on each spin component. -/
noncomputable def spinPosObs (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) :
    PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m)) →ₗ[ℂ]
      PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m)) where
  toFun Φ := WithLp.toLp 2 (fun σ => posObs a χ (Φ σ))
  map_add' := by
    intro Φ Ψ
    apply PiLp.ext
    intro σ
    change posObs a χ ((Φ + Ψ) σ) = posObs a χ (Φ σ) + posObs a χ (Ψ σ)
    rw [PiLp.add_apply, map_add]
  map_smul' := by
    intro c Φ
    apply PiLp.ext
    intro σ
    change posObs a χ ((c • Φ) σ) = c • posObs a χ (Φ σ)
    rw [PiLp.smul_apply, map_smul]

lemma spinPosObs_apply (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (Φ : PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m))) (σ : S) :
    spinPosObs a χ Φ σ = posObs a χ (Φ σ) :=
  rfl

lemma inner_spinPosObs (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (Φ : PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m))) :
    ⟪Φ, spinPosObs a χ Φ⟫_ℂ = ∑ σ, ⟪Φ σ, posObs a χ (Φ σ)⟫_ℂ := by
  rw [PiLp.inner_apply]
  rfl

/-- The collocated observable of a function with `|χ| ≤ 1` is a contraction on the
spin-inclusive grid states. -/
lemma norm_spinPosObs_le (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (hχb : ∀ y, ‖χ y‖ ≤ 1)
    (Φ : PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m))) : ‖spinPosObs a χ Φ‖ ≤ ‖Φ‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun σ _ => ?_)
  rw [spinPosObs_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_posObs_le a χ hχb (Φ σ)) 2

/-- Normalising a state of norm `c ∈ (0, 1]` changes the expectation of a linear contraction by
at most `1 - c²` (`norm_inner_normalize_sub_le` for a linear map). -/
lemma norm_inner_normalize_sub_le_of_contraction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (O : E →ₗ[ℂ] E) (hO : ∀ y, ‖O y‖ ≤ ‖y‖) (f : E) {c : ℝ}
    (hc : ‖f‖ = c) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ‖⟪((c : ℂ)⁻¹) • f, O (((c : ℂ)⁻¹) • f)⟫_ℂ - ⟪f, O f⟫_ℂ‖ ≤ 1 - c ^ 2 := by
  have e : ⟪((c : ℂ)⁻¹) • f, O (((c : ℂ)⁻¹) • f)⟫_ℂ - ⟪f, O f⟫_ℂ =
      (((c ^ 2)⁻¹ - 1 : ℝ) : ℂ) * ⟪f, O f⟫_ℂ := by
    rw [map_smul, inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal]
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hinner : ‖⟪f, O f⟫_ℂ‖ ≤ c ^ 2 := by
    calc ‖⟪f, O f⟫_ℂ‖ ≤ ‖f‖ * ‖O f‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_left (hO f) (norm_nonneg _)
      _ = c ^ 2 := by rw [hc]; ring
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have hpos : 0 ≤ (c ^ 2)⁻¹ - 1 := by
    rw [sub_nonneg, one_le_inv₀ (pow_pos hc0 2)]
    exact hc2
  rw [abs_of_nonneg hpos]
  calc ((c ^ 2)⁻¹ - 1) * ‖⟪f, O f⟫_ℂ‖ ≤ ((c ^ 2)⁻¹ - 1) * c ^ 2 :=
        mul_le_mul_of_nonneg_left hinner hpos
    _ = 1 - c ^ 2 := by
        have : c ^ 2 ≠ 0 := (pow_pos hc0 2).ne'
        field_simp

/-- Normalising a spin-inclusive grid state of norm `c ∈ (0, 1]` changes the expectation of the
collocated observable of a function with `|χ| ≤ 1` by at most `1 - c²`. -/
lemma spin_normalize_sub_le (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (hχb : ∀ y, ‖χ y‖ ≤ 1)
    (Φ : PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m))) {c : ℝ} (hc : ‖Φ‖ = c)
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ‖⟪((c : ℂ)⁻¹) • Φ, spinPosObs a χ (((c : ℂ)⁻¹) • Φ)⟫_ℂ - ⟪Φ, spinPosObs a χ Φ⟫_ℂ‖ ≤
      1 - c ^ 2 :=
  -- the space is given explicitly: leaving it to unification times out against all of Mathlib
  norm_inner_normalize_sub_le_of_contraction
    (E := PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m))) (spinPosObs a χ)
    (norm_spinPosObs_le a χ hχb) Φ hc hc0 hc1

/-- The expectation of the kinetic energy `A_r` (applied through the DFT on each spin
component) in a spin-inclusive grid state. -/
noncomputable def spinPosKinExpect (sys : CoulombSystem eta ν) (g : ℝ) (r : Fin eta)
    (Φ : PiLp 2 (fun _ : S => EuclideanSpace ℂ (RCfg eta m))) : ℝ :=
  ∑ σ, posKinExpect sys g r (Φ σ)

end SpinGrid

/-- The spin-inclusive grid data: `P Ψ₀` sampled on the grid on each spin component. -/
noncomputable def spinGridData {D : ℕ} (m : ℕ) (Ψ₀ : CoulombSpinL2 eta D) :
    CoulombGridSpinState eta D m :=
  WithLp.toLp 2 fun σ => idft (regCoeff m ((physMap eta).symm (Ψ₀ σ)))

lemma spinGridData_apply {D : ℕ} (m : ℕ) (Ψ₀ : CoulombSpinL2 eta D) (σ : Fin eta → Fin D) :
    spinGridData m Ψ₀ σ = idft (regCoeff m ((physMap eta).symm (Ψ₀ σ))) :=
  rfl

/-! ## The grid bounds as `ℓ²`-superadditive functions of the data -/

section GridBounds

/-- The raw bound of `prop:grid-dyn` (`gridConsts`) is superadditive under `ℓ²` combination (for
all `c_i ≥ 0`). -/
lemma l2quad_gridRaw (sys : CoulombSystem eta ν) {L Hunit Blow Cs Bker : ℝ} (hL : 0 < L)
    (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs)
    (hBker : 0 ≤ Bker) (a : Fin eta) (c : Lat3 → ℂ) {c₁ c₂ c₃ c₄ : ℝ} (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) :
    L2Quad (fun x : Fin 4 → ℝ =>
      (gridConsts sys L Hunit Blow Cs Bker a c (x 0) (x 1) (x 2) (x 3)).1 * c₁ +
        (gridConsts sys L Hunit Blow Cs Bker a c (x 0) (x 1) (x 2) (x 3)).2.1 * c₂ +
        (gridConsts sys L Hunit Blow Cs Bker a c (x 0) (x 1) (x 2) (x 3)).2.2 * c₃ +
        x 0 ^ 2 * c₄) := by
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hm : 0 ≤ sys.maxMass := by linarith [sys.one_le_maxMass]
  have hCt : 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker 1 :=
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker zero_le_one
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hZ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg hγ
  have hcJ := gridFlowConst_nonneg sys hL
  have hCχ : 0 ≤ ∑' ν, ‖c ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hD2 : 0 ≤ momTwo c := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  simp only [gridConsts]
  l2quad

/-- `gridPhi` (the second-moment budget of `thm:grid-dyn-sharp`) is `ℓ²`-subadditive. -/
lemma l2sub_gridPhi (sys : CoulombSystem eta ν) {L Hunit Blow Cs Bker : ℝ} (hL : 0 < L)
    (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs)
    (hBker : 0 ≤ Bker) (c : Lat3 → ℂ) :
    L2Sub (fun x : Fin 4 → ℝ => gridPhi sys L Hunit Blow Cs Bker c (x 0) (x 1) (x 2) (x 3)) := by
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hm : 0 ≤ sys.maxMass := by linarith [sys.one_le_maxMass]
  have hCt : 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker 1 :=
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker zero_le_one
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hZ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg hγ
  have hcJ := gridFlowConst_nonneg sys hL
  have hCχ : 0 ≤ ∑' ν, ‖c ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hD2 : 0 ≤ momTwo c := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hD4 := momFour_nonneg c
  have hcG := coulombGridCoupling_nonneg sys L hL
  simp only [gridPhi, flow2]
  l2sub

/-- The raw bound of `thm:grid-dyn-sharp` (`gridConstsSharp`) is superadditive under `ℓ²`
combination (for all `c_i ≥ 0`). -/
lemma l2quad_gridSharpRaw (sys : CoulombSystem eta ν) {L Hunit Blow Cs Bker : ℝ} (hL : 0 < L)
    (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs)
    (hBker : 0 ≤ Bker) (a : Fin eta) (c : Lat3 → ℂ) {c₁ c₂ c₃ c₄ : ℝ} (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hc₄ : 0 ≤ c₄) :
    L2Quad (fun x : Fin 4 → ℝ =>
      (gridConstsSharp sys L Hunit Blow Cs Bker a c (x 0) (x 1) (x 2) (x 3)).1 * c₁ +
        (gridConstsSharp sys L Hunit Blow Cs Bker a c (x 0) (x 1) (x 2) (x 3)).2.1 * c₂ +
        (gridConstsSharp sys L Hunit Blow Cs Bker a c (x 0) (x 1) (x 2) (x 3)).2.2 * c₃ +
        x 0 ^ 2 * c₄) := by
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hm : 0 ≤ sys.maxMass := by linarith [sys.one_le_maxMass]
  have hCt : 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker 1 :=
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker zero_le_one
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hZ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg hγ
  have hcJ := gridFlowConst_nonneg sys hL
  have hCχ : 0 ≤ ∑' ν, ‖c ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hD2 : 0 ≤ momTwo c := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hΦ := l2sub_gridPhi sys hL hC hBlow hCs hBker c
  simp only [gridConstsSharp]
  l2quad

end GridBounds

/-! ## `prop:grid-dyn` and `thm:grid-dyn-sharp` with internal spin -/

section GridDynSpin

/-- The third constant of `gridConstsSharp` is nonnegative (stated separately, so that no
definitional unfolding of the two constant tuples against each other is needed). -/
lemma gridConstsSharp_nonneg_three (sys : CoulombSystem eta ν) {L Hunit Blow Cs Bker : ℝ}
    (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs)
    (hBker : 0 ≤ Bker) (a : Fin eta) (c : Lat3 → ℂ) {s0 hu hs hv : ℝ} (h0 : 0 ≤ s0)
    (h1 : 0 ≤ hu) (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    0 ≤ (gridConstsSharp sys L Hunit Blow Cs Bker a c s0 hu hs hv).2.2 := by
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hm : 0 ≤ sys.maxMass := by linarith [sys.one_le_maxMass]
  have hκ : 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
      (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB sys L Hunit * s0))) :=
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker (by positivity)
  simp only [gridConstsSharp]
  positivity

/-- The `(Hχ)` form of the raw grid bound (the arithmetic of `thm_grid_dyn`). -/
lemma grid_final_le {A1 A3 S T2 K τ sp CM5 E : ℝ} (hA3 : 0 ≤ A3) (hK : 8 ≤ K) (hCM : 0 ≤ CM5)
    (hτ : τ ≤ Real.sqrt 3 ^ 5 * CM5 * (1 / K) ^ 5) (hsp : sp ≤ CM5 * (1 / K) ^ 5)
    (h : E ≤ A1 * (1 / K) ^ 5 + T2 + A3 * Real.sqrt (1 / K) ^ 5 * τ + S ^ 2 * sp) :
    E ≤ (A1 + (A3 * Real.sqrt 3 ^ 5 + S ^ 2) * CM5) * (1 / K) ^ 5 + T2 := by
  have hKpos : 0 < K := by linarith
  have hρ1 : Real.sqrt (1 / K) ^ 5 ≤ 1 := by
    have h1 : 1 / K ≤ 1 := by rw [div_le_one hKpos]; linarith
    have h2 : Real.sqrt (1 / K) ≤ 1 := by
      have := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_one] at this
    exact pow_le_one₀ (Real.sqrt_nonneg _) h2
  have hρ0 : 0 ≤ Real.sqrt (1 / K) ^ 5 := by positivity
  have hτ' : A3 * Real.sqrt (1 / K) ^ 5 * τ ≤ A3 * Real.sqrt 3 ^ 5 * CM5 * (1 / K) ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left hτ (mul_nonneg hA3 hρ0)
    have h2 : A3 * Real.sqrt (1 / K) ^ 5 * (Real.sqrt 3 ^ 5 * CM5 * (1 / K) ^ 5) ≤
        A3 * 1 * (Real.sqrt 3 ^ 5 * CM5 * (1 / K) ^ 5) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ1 hA3)
      positivity
    have e : A3 * 1 * (Real.sqrt 3 ^ 5 * CM5 * (1 / K) ^ 5) =
        A3 * Real.sqrt 3 ^ 5 * CM5 * (1 / K) ^ 5 := by ring
    linarith
  have hs : S ^ 2 * sp ≤ S ^ 2 * (CM5 * (1 / K) ^ 5) :=
    mul_le_mul_of_nonneg_left hsp (sq_nonneg S)
  have e : (A1 + (A3 * Real.sqrt 3 ^ 5 + S ^ 2) * CM5) * (1 / K) ^ 5 + T2 =
      A1 * (1 / K) ^ 5 + T2 + A3 * Real.sqrt 3 ^ 5 * CM5 * (1 / K) ^ 5 +
        S ^ 2 * (CM5 * (1 / K) ^ 5) := by ring
  rw [e]
  linarith

/-- **`prop:grid-dyn` with internal spin**, position space, raw form. In the setting of
`grid_observable_position`, for a spin-inclusive `Ψ₀ ∈ D(H²)` (`H Ψ₀ = H₀`, `H H₀ = H₁`), the
observable error of the spin-inclusive grid state `Ψ_g(t) = (e^{-iH_pos t} ⊗ 1) P Ψ₀` is bounded
by the bound of `grid_observable_position` at the spin-inclusive norms. -/
theorem grid_observable_position_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    {D : ℕ} (Ψ₀ H₀ H₁ : CoulombSpinL2 eta D) (hΨ₀ : HasCoulombSpinHamiltonian sys L Ψ₀ H₀)
    (hH₀ : HasCoulombSpinHamiltonian sys L H₀ H₁)
    (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχ1 : Summable fun ν => ‖mFourierCoeff χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖mFourierCoeff χ ν‖)
    (hreal : ∀ y, conj (χ y) = χ y) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridConsts sys L molecularCanonicalUnitHardyConstant (molecularCanonicalLowConstant L)
      (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L) a
      (mFourierCoeff χ) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then ‖mFourierCoeff χ ν‖ else 0
    let Ψg := spinGridProp (fun s => posConj (Ug s)) t (spinGridData m Ψ₀)
    ‖⟪spinProp U t Ψ₀, spinLift (mulCLM (regFun a χ)) (spinProp U t Ψ₀)⟫_ℂ -
        ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * Real.sqrt (1 / K) ^ 5 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖Ψ₀‖ ^ 2 * supTail (mFourierCoeff χ) m := by
  intro g K A τχ Ψg
  obtain ⟨hBlow, hCs, hBker, -⟩ := molecularCanonicalTailConstants_spec L hL
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L molecularCanonicalUnitHardyConstant
  have hτ : 0 ≤ τχ := tsum_nonneg fun ν => by split_ifs <;> simp
  have hB := l2quad_gridRaw sys hL hC hBlow hCs hBker a (mFourierCoeff χ)
    (c₁ := (1 / K) ^ 5) (c₂ := t * Real.sqrt (1 / K) ^ 5) (c₃ := Real.sqrt (1 / K) ^ 5 * τχ)
    (c₄ := supTail (mFourierCoeff χ) m) (by positivity) (by positivity) (by positivity)
    (supTail_nonneg _ _)
  have h := hB.norm_sum_le_l2comb
    (fun σ => ⟪U t (Ψ₀ σ), mulCLM (regFun a χ) (U t (Ψ₀ σ))⟫_ℂ - ⟪Ψg σ, posObs a χ (Ψg σ)⟫_ℂ)
    (spinData Ψ₀ H₀ H₁) (spinData_nonneg Ψ₀ H₀ H₁) (fun σ => by
      have hσ := grid_observable_position sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
        hgderiv (Ψ₀ σ) (H₀ σ) (H₁ σ) (hΨ₀ σ) (hH₀ σ) a χ hχ1 hχ2 hreal ht
      refine hσ.trans_eq ?_
      simp only [spinData, Matrix.cons_val]
      ring)
  rw [l2comb_spinData] at h
  have hsplit : ⟪spinProp U t Ψ₀, spinLift (mulCLM (regFun a χ)) (spinProp U t Ψ₀)⟫_ℂ -
      ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ = ∑ σ, (⟪U t (Ψ₀ σ), mulCLM (regFun a χ) (U t (Ψ₀ σ))⟫_ℂ -
        ⟪Ψg σ, posObs a χ (Ψg σ)⟫_ℂ) := by
    rw [inner_spinLift, inner_spinPosObs, ← Finset.sum_sub_distrib]
    rfl
  rw [hsplit]
  refine h.trans_eq ?_
  simp only [Matrix.cons_val, A]
  ring

/-- **`thm:grid-dyn-sharp` with internal spin**, position space, raw form: the bound of
`grid_observable_position_sharp` at the spin-inclusive norms. -/
theorem grid_observable_position_sharp_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    {D : ℕ} (Ψ₀ H₀ H₁ : CoulombSpinL2 eta D) (hΨ₀ : HasCoulombSpinHamiltonian sys L Ψ₀ H₀)
    (hH₀ : HasCoulombSpinHamiltonian sys L H₀ H₁)
    (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχ1 : Summable fun ν => ‖mFourierCoeff χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖mFourierCoeff χ ν‖)
    (hχ4 : Summable fun ν => nsq ν ^ 2 * ‖mFourierCoeff χ ν‖)
    (hreal : ∀ y, conj (χ y) = χ y) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridConstsSharp sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) a (mFourierCoeff χ) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then ‖mFourierCoeff χ ν‖ else 0
    let Ψg := spinGridProp (fun s => posConj (Ug s)) t (spinGridData m Ψ₀)
    ‖⟪spinProp U t Ψ₀, spinLift (mulCLM (regFun a χ)) (spinProp U t Ψ₀)⟫_ℂ -
        ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖Ψ₀‖ ^ 2 * supTail (mFourierCoeff χ) m := by
  intro g K A τχ Ψg
  obtain ⟨hBlow, hCs, hBker, -⟩ := molecularCanonicalTailConstants_spec L hL
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L molecularCanonicalUnitHardyConstant
  have hτ : 0 ≤ τχ := tsum_nonneg fun ν => by split_ifs <;> simp
  have hB := l2quad_gridSharpRaw sys hL hC hBlow hCs hBker a (mFourierCoeff χ)
    (c₁ := (1 / K) ^ 5) (c₂ := t * (1 / K) ^ 3) (c₃ := Real.sqrt (1 / K) ^ 5 * τχ)
    (c₄ := supTail (mFourierCoeff χ) m) (by positivity) (by positivity) (by positivity)
    (supTail_nonneg _ _)
  have h := hB.norm_sum_le_l2comb
    (fun σ => ⟪U t (Ψ₀ σ), mulCLM (regFun a χ) (U t (Ψ₀ σ))⟫_ℂ - ⟪Ψg σ, posObs a χ (Ψg σ)⟫_ℂ)
    (spinData Ψ₀ H₀ H₁) (spinData_nonneg Ψ₀ H₀ H₁) (fun σ => by
      have hσ := grid_observable_position_sharp sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0
        hgcomm hgderiv (Ψ₀ σ) (H₀ σ) (H₁ σ) (hΨ₀ σ) (hH₀ σ) a χ hχ1 hχ2 hχ4 hreal ht
      refine hσ.trans_eq ?_
      simp only [spinData, Matrix.cons_val]
      ring)
  rw [l2comb_spinData] at h
  have hsplit : ⟪spinProp U t Ψ₀, spinLift (mulCLM (regFun a χ)) (spinProp U t Ψ₀)⟫_ℂ -
      ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ = ∑ σ, (⟪U t (Ψ₀ σ), mulCLM (regFun a χ) (U t (Ψ₀ σ))⟫_ℂ -
        ⟪Ψg σ, posObs a χ (Ψg σ)⟫_ℂ) := by
    rw [inner_spinLift, inner_spinPosObs, ← Finset.sum_sub_distrib]
    rfl
  rw [hsplit]
  refine h.trans_eq ?_
  simp only [Matrix.cons_val, A]
  ring

/-- **`prop:grid-dyn` with internal spin and its propagators.** There is a propagator `U` on
`CoulombSpinL2 eta D` (characterised as in `thm_dyn_spin`), and for every `m` and every real, even
kernel of the class `𝒦_K` a propagator `U_g` of the spin-independent grid Hamiltonian `spinHpos`
on `CoulombGridSpinState eta D m` acting on every spin component by one isometry, such that for
every spin-inclusive `Ψ₀ ∈ D(H²)`, register `a`, real `χ` under `(Hχ)`, `m ≥ 8`, `K = 2πm/L ≥ 8`
and `t ≥ 0` the error of `χ(x_a) ⊗ 1` between `U(t) Ψ₀` and `U_g(t) (spinGridData m Ψ₀)` is at
most `(A₁ + (A₃ 3^{5/2} + ‖Ψ₀‖²) C_{χ,5}) K^{-5} + A₂ t K^{-5/2}` (the bound of `thm_grid_dyn`),
with `(A₁, A₂, A₃) = gridConsts` at the spin-inclusive norms. `U_g` is determined by `U_g(0) = 1`
and its derivative clause (finite dimension). -/
theorem thm_grid_dyn_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) (D : ℕ) :
    ∃ U : ℝ → CoulombSpinL2 eta D ≃ₗᵢ[ℂ] CoulombSpinL2 eta D,
      (∀ Ψ, U 0 Ψ = Ψ) ∧
      (∀ s t Ψ, U (s + t) Ψ = U s (U t Ψ)) ∧
      (∀ Ψ, Continuous fun t => U t Ψ) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasCoulombSpinHamiltonian sys L (U t Ψ) (U t Φ)) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasDerivAt (fun s => U s Ψ) (-(Complex.I • U t Φ)) t) ∧
      (∀ φ ζ : ℝ → CoulombSpinL2 eta D, (∀ t, HasCoulombSpinHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      (∀ t, ∃ V : MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
        ∀ Ψ σ, U t Ψ σ = V (Ψ σ)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → CoulombGridSpinState eta D m ≃ₗᵢ[ℂ] CoulombGridSpinState eta D m,
        (∀ Φ, Ug 0 Φ = Φ) ∧ (∀ s t Φ, Ug (s + t) Φ = Ug s (Ug t Φ)) ∧
        (∀ Φ, Continuous fun t => Ug t Φ) ∧
        (∀ t Φ, Ug t (spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) Φ) = spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t Φ)) ∧
        (∀ t Φ, HasDerivAt (fun s => Ug s Φ) (-(Complex.I • Ug t (spinHpos
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Φ))) t) ∧
        (∀ t, ∃ W : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
          ∀ Φ σ, Ug t Φ σ = W (Φ σ)) ∧
        ∀ Ψ₀ H₀ H₁ : CoulombSpinL2 eta D, HasCoulombSpinHamiltonian sys L Ψ₀ H₀ →
          HasCoulombSpinHamiltonian sys L H₀ H₁ →
          ∀ (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (CM : ℕ → ℝ),
          HChi (2 * Real.pi / L) (mFourierCoeff χ) CM →
          (∀ y, conj (χ y) = χ y) →
          let A := gridConsts sys L molecularCanonicalUnitHardyConstant
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) a (mFourierCoeff χ) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let Ψg := Ug t (spinGridData m Ψ₀)
            ‖⟪U t Ψ₀, spinLift (mulCLM (regFun a χ)) (U t Ψ₀)⟫_ℂ -
                ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ‖ ≤
              (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖Ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
                A.2.1 * t * Real.sqrt (1 / K) ^ 5 := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, -, -⟩ := exists_coulombPropagator sys L hL
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := spinProp_spec sys L D U h0 hadd hcont hgraph hderiv huniq
  refine ⟨spinProp U, s0, s1, s2, s3, s4, s5, s6, fun m κ hκ => ?_⟩
  obtain ⟨Ur, hr0, -, -, hrcomm, hrderiv, hp0, hpadd, hpcont, hpcomm, hpderiv⟩ :=
    exists_posPropagator (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) hκ.even
      (2 * Real.pi / L)
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := spinGridProp_spec (S := Fin eta → Fin D)
    (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) (fun t => posConj (Ur t))
    hp0 hpadd hpcont hpcomm hpderiv
  refine ⟨spinGridProp (fun t => posConj (Ur t)), g0, g1, g2, g3, g4, g5, ?_⟩
  intro Ψ₀ H₀ H₁ hΨ₀ hH₀ a χ CM hc hreal A hm hK t ht K Ψg
  have hg : 0 < 2 * Real.pi / L := by positivity
  have h := grid_observable_position_spin sys L hL U h0 hgraph hderiv m hm hK hκ Ur hr0 hrcomm
    hrderiv Ψ₀ H₀ H₁ hΨ₀ hH₀ a χ hc.1 (summable_nsq_of_HChi hg hc) hreal ht
  obtain ⟨hBlow, hCs, hBker, -⟩ := molecularCanonicalTailConstants_spec L hL
  have hA₃ : 0 ≤ A.2.2 :=
    gridConsts_nonneg_three sys L _ _ _ _ a _ (finiteCoulombPhysicalMassConstant_nonneg _ _ _)
      hBlow hCs hBker (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have hK' : (8 : ℝ) ≤ K := hK
  have hsqrt3 : Real.sqrt 3 ≤ K := by
    have : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    linarith
  exact grid_final_le hA₃ hK' (CM_nonneg_of_HChi hc (M := 5) (by norm_num))
    (tail_le_of_HChi hg hc (M := 5) (by norm_num) hsqrt3)
    (supTail_le_of_HChi hg hc (M := 5) (by norm_num) (m := m) (by linarith)) h

/-- **`thm:grid-dyn-sharp` with internal spin and its propagators**: as `thm_grid_dyn_spin`, for
`χ` under `(Hχ)`, with the energy rate `t K^{-3}` and the constants `gridConstsSharp` at the
spin-inclusive norms (the bound of `thm_grid_dyn_sharp`). -/
theorem thm_grid_dyn_sharp_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) (D : ℕ) :
    ∃ U : ℝ → CoulombSpinL2 eta D ≃ₗᵢ[ℂ] CoulombSpinL2 eta D,
      (∀ Ψ, U 0 Ψ = Ψ) ∧
      (∀ s t Ψ, U (s + t) Ψ = U s (U t Ψ)) ∧
      (∀ Ψ, Continuous fun t => U t Ψ) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasCoulombSpinHamiltonian sys L (U t Ψ) (U t Φ)) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasDerivAt (fun s => U s Ψ) (-(Complex.I • U t Φ)) t) ∧
      (∀ φ ζ : ℝ → CoulombSpinL2 eta D, (∀ t, HasCoulombSpinHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      (∀ t, ∃ V : MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
        ∀ Ψ σ, U t Ψ σ = V (Ψ σ)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → CoulombGridSpinState eta D m ≃ₗᵢ[ℂ] CoulombGridSpinState eta D m,
        (∀ Φ, Ug 0 Φ = Φ) ∧ (∀ s t Φ, Ug (s + t) Φ = Ug s (Ug t Φ)) ∧
        (∀ Φ, Continuous fun t => Ug t Φ) ∧
        (∀ t Φ, Ug t (spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) Φ) = spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t Φ)) ∧
        (∀ t Φ, HasDerivAt (fun s => Ug s Φ) (-(Complex.I • Ug t (spinHpos
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Φ))) t) ∧
        (∀ t, ∃ W : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
          ∀ Φ σ, Ug t Φ σ = W (Φ σ)) ∧
        ∀ Ψ₀ H₀ H₁ : CoulombSpinL2 eta D, HasCoulombSpinHamiltonian sys L Ψ₀ H₀ →
          HasCoulombSpinHamiltonian sys L H₀ H₁ →
          ∀ (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (CM : ℕ → ℝ),
          HChi (2 * Real.pi / L) (mFourierCoeff χ) CM →
          (∀ y, conj (χ y) = χ y) →
          let A := gridConstsSharp sys L molecularCanonicalUnitHardyConstant
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) a (mFourierCoeff χ) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let Ψg := Ug t (spinGridData m Ψ₀)
            ‖⟪U t Ψ₀, spinLift (mulCLM (regFun a χ)) (U t Ψ₀)⟫_ℂ -
                ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ‖ ≤
              (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖Ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
                A.2.1 * t * (1 / K) ^ 3 := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, -, -⟩ := exists_coulombPropagator sys L hL
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := spinProp_spec sys L D U h0 hadd hcont hgraph hderiv huniq
  refine ⟨spinProp U, s0, s1, s2, s3, s4, s5, s6, fun m κ hκ => ?_⟩
  obtain ⟨Ur, hr0, -, -, hrcomm, hrderiv, hp0, hpadd, hpcont, hpcomm, hpderiv⟩ :=
    exists_posPropagator (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) hκ.even
      (2 * Real.pi / L)
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := spinGridProp_spec (S := Fin eta → Fin D)
    (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) (fun t => posConj (Ur t))
    hp0 hpadd hpcont hpcomm hpderiv
  refine ⟨spinGridProp (fun t => posConj (Ur t)), g0, g1, g2, g3, g4, g5, ?_⟩
  intro Ψ₀ H₀ H₁ hΨ₀ hH₀ a χ CM hc hreal A hm hK t ht K Ψg
  have hg : 0 < 2 * Real.pi / L := by positivity
  have h := grid_observable_position_sharp_spin sys L hL U h0 hgraph hderiv m hm hK hκ Ur hr0
    hrcomm hrderiv Ψ₀ H₀ H₁ hΨ₀ hH₀ a χ hc.1 (summable_nsq_of_HChi hg hc)
    (summable_nsq_sq_of_HChi hg hc) hreal ht
  obtain ⟨hBlow, hCs, hBker, -⟩ := molecularCanonicalTailConstants_spec L hL
  have hA₃ : 0 ≤ A.2.2 :=
    gridConstsSharp_nonneg_three sys (finiteCoulombPhysicalMassConstant_nonneg _ _ _)
      hBlow hCs hBker a (mFourierCoeff χ) (norm_nonneg Ψ₀) (norm_nonneg H₀) (norm_nonneg H₀)
      (norm_nonneg H₁)
  have hK' : (8 : ℝ) ≤ K := hK
  have hsqrt3 : Real.sqrt 3 ≤ K := by
    have : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    linarith
  exact grid_final_le hA₃ hK' (CM_nonneg_of_HChi hc (M := 5) (by norm_num))
    (tail_le_of_HChi hg hc (M := 5) (by norm_num) hsqrt3)
    (supTail_le_of_HChi hg hc (M := 5) (by norm_num) (m := m) (by linarith)) h

/-- Sums of numbers in unit segments. -/
lemma InUnitSeg.sum {S : Type} [Fintype S] {z : S → ℂ} {c : S → ℝ}
    (h : ∀ σ, InUnitSeg (z σ) (c σ)) : InUnitSeg (∑ σ, z σ) (∑ σ, c σ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.im_sum]
    exact Finset.sum_eq_zero fun σ _ => (h σ).1
  · rw [Complex.re_sum]
    exact Finset.sum_nonneg fun σ _ => (h σ).2.1
  · rw [Complex.re_sum]
    exact Finset.sum_le_sum fun σ _ => (h σ).2.2

/-- The grid data has at most the norm of the continuum data. -/
lemma norm_spinGridData_le {D : ℕ} (m : ℕ) (Ψ₀ : CoulombSpinL2 eta D) :
    ‖spinGridData m Ψ₀‖ ≤ ‖Ψ₀‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun σ _ => ?_)
  have e : ‖(spinGridData m Ψ₀) σ‖ = ‖regCoeff m ((physMap eta).symm (Ψ₀ σ))‖ := by
    show ‖idft (regCoeff m ((physMap eta).symm (Ψ₀ σ)))‖ = _
    rw [← dftLIE_symm_apply, LinearIsometryEquiv.norm_map]
  have h3 : ‖regCoeff m ((physMap eta).symm (Ψ₀ σ))‖ ≤ ‖Ψ₀ σ‖ := by
    refine (norm_regCoeff_le _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
  rw [e]
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

/-- The spin-inclusive expectations of an observable with values in `[0, 1]` lie in
`[0, ‖·‖²]`. -/
lemma spin_expectations_mem {D m : ℕ} (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχ : ∀ y, (χ y).im = 0 ∧ 0 ≤ (χ y).re ∧ (χ y).re ≤ 1) (Ψ : CoulombSpinL2 eta D)
    (Φ : CoulombGridSpinState eta D m) :
    InUnitSeg ⟪Ψ, spinLift (mulCLM (regFun a χ)) Ψ⟫_ℂ (‖Ψ‖ ^ 2) ∧
      InUnitSeg ⟪Φ, spinPosObs a χ Φ⟫_ℂ (‖Φ‖ ^ 2) := by
  constructor
  · rw [inner_spinLift, PiLp.norm_sq_eq_of_L2]
    exact InUnitSeg.sum fun σ => inner_mulCLM_mem (regFun a χ) (regFun_mem a χ hχ) (Ψ σ)
  · rw [inner_spinPosObs, PiLp.norm_sq_eq_of_L2]
    exact InUnitSeg.sum fun σ => inner_posObs_mem a χ hχ (Φ σ)

/-- **`prop:grid-dyn` with internal spin, `min {1, ·}` form**: as `thm_grid_dyn_spin`; for
`‖Ψ₀‖ = 1` and `χ` with values in `[0, 1]` the error is at most
`min {1, C [K^{-5} + t K^{-5/2}]}` (both expectations lie in `[0, 1]`). -/
theorem thm_grid_dyn_min_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) (D : ℕ) :
    ∃ U : ℝ → CoulombSpinL2 eta D ≃ₗᵢ[ℂ] CoulombSpinL2 eta D,
      (∀ Ψ, U 0 Ψ = Ψ) ∧
      (∀ s t Ψ, U (s + t) Ψ = U s (U t Ψ)) ∧
      (∀ Ψ, Continuous fun t => U t Ψ) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasCoulombSpinHamiltonian sys L (U t Ψ) (U t Φ)) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasDerivAt (fun s => U s Ψ) (-(Complex.I • U t Φ)) t) ∧
      (∀ φ ζ : ℝ → CoulombSpinL2 eta D, (∀ t, HasCoulombSpinHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      (∀ t, ∃ V : MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
        ∀ Ψ σ, U t Ψ σ = V (Ψ σ)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → CoulombGridSpinState eta D m ≃ₗᵢ[ℂ] CoulombGridSpinState eta D m,
        (∀ Φ, Ug 0 Φ = Φ) ∧ (∀ s t Φ, Ug (s + t) Φ = Ug s (Ug t Φ)) ∧
        (∀ Φ, Continuous fun t => Ug t Φ) ∧
        (∀ t Φ, Ug t (spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) Φ) = spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t Φ)) ∧
        (∀ t Φ, HasDerivAt (fun s => Ug s Φ) (-(Complex.I • Ug t (spinHpos
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Φ))) t) ∧
        (∀ t, ∃ W : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
          ∀ Φ σ, Ug t Φ σ = W (Φ σ)) ∧
        ∀ Ψ₀ H₀ H₁ : CoulombSpinL2 eta D, HasCoulombSpinHamiltonian sys L Ψ₀ H₀ →
          HasCoulombSpinHamiltonian sys L H₀ H₁ → ‖Ψ₀‖ = 1 →
          ∀ (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (CM : ℕ → ℝ),
          HChi (2 * Real.pi / L) (mFourierCoeff χ) CM →
          (∀ y, (χ y).im = 0 ∧ 0 ≤ (χ y).re ∧ (χ y).re ≤ 1) →
          let A := gridConsts sys L molecularCanonicalUnitHardyConstant
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) a (mFourierCoeff χ) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let Ψg := Ug t (spinGridData m Ψ₀)
            ‖⟪U t Ψ₀, spinLift (mulCLM (regFun a χ)) (U t Ψ₀)⟫_ℂ -
                ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ‖ ≤
              min 1 ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖Ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
                A.2.1 * t * Real.sqrt (1 / K) ^ 5) := by
  obtain ⟨U, s0, s1, s2, s3, s4, s5, s6, hrest⟩ := thm_grid_dyn_spin sys L hL D
  refine ⟨U, s0, s1, s2, s3, s4, s5, s6, fun m κ hκ => ?_⟩
  obtain ⟨Ug, g0, g1, g2, g3, g4, g5, hbound⟩ := hrest m κ hκ
  refine ⟨Ug, g0, g1, g2, g3, g4, g5, ?_⟩
  intro Ψ₀ H₀ H₁ hΨ₀ hH₀ hnorm a χ CM hc hχ A hm hK t ht K Ψg
  have hreal : ∀ y, conj (χ y) = χ y := fun y => by
    apply Complex.ext
    · simp
    · simp [(hχ y).1]
  refine le_min ?_ (hbound Ψ₀ H₀ H₁ hΨ₀ hH₀ a χ CM hc hreal hm hK t ht)
  obtain ⟨h1, h2⟩ := spin_expectations_mem a χ hχ (U t Ψ₀) Ψg
  have hUt : ‖U t Ψ₀‖ ^ 2 ≤ 1 := by rw [LinearIsometryEquiv.norm_map, hnorm]; norm_num
  have hΨg : ‖Ψg‖ ^ 2 ≤ 1 := by
    have e : ‖Ψg‖ = ‖spinGridData m Ψ₀‖ := LinearIsometryEquiv.norm_map _ _
    have h3 := norm_spinGridData_le m Ψ₀
    rw [hnorm] at h3
    rw [e]
    have h4 := norm_nonneg (spinGridData m Ψ₀)
    nlinarith
  exact norm_sub_le_of_inUnitSeg h1 h2 hUt hΨg

/-- **`thm:grid-dyn-sharp` with internal spin, `min {1, ·}` form**: as
`thm_grid_dyn_sharp_spin`; for `‖Ψ₀‖ = 1` and `χ` with values in `[0, 1]` the error is at most
`min {1, C [K^{-5} + t K^{-3}]}` (both expectations lie in `[0, 1]`). -/
theorem thm_grid_dyn_sharp_min_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) (D : ℕ) :
    ∃ U : ℝ → CoulombSpinL2 eta D ≃ₗᵢ[ℂ] CoulombSpinL2 eta D,
      (∀ Ψ, U 0 Ψ = Ψ) ∧
      (∀ s t Ψ, U (s + t) Ψ = U s (U t Ψ)) ∧
      (∀ Ψ, Continuous fun t => U t Ψ) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasCoulombSpinHamiltonian sys L (U t Ψ) (U t Φ)) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasDerivAt (fun s => U s Ψ) (-(Complex.I • U t Φ)) t) ∧
      (∀ φ ζ : ℝ → CoulombSpinL2 eta D, (∀ t, HasCoulombSpinHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      (∀ t, ∃ V : MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
        ∀ Ψ σ, U t Ψ σ = V (Ψ σ)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → CoulombGridSpinState eta D m ≃ₗᵢ[ℂ] CoulombGridSpinState eta D m,
        (∀ Φ, Ug 0 Φ = Φ) ∧ (∀ s t Φ, Ug (s + t) Φ = Ug s (Ug t Φ)) ∧
        (∀ Φ, Continuous fun t => Ug t Φ) ∧
        (∀ t Φ, Ug t (spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) Φ) = spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t Φ)) ∧
        (∀ t Φ, HasDerivAt (fun s => Ug s Φ) (-(Complex.I • Ug t (spinHpos
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Φ))) t) ∧
        (∀ t, ∃ W : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
          ∀ Φ σ, Ug t Φ σ = W (Φ σ)) ∧
        ∀ Ψ₀ H₀ H₁ : CoulombSpinL2 eta D, HasCoulombSpinHamiltonian sys L Ψ₀ H₀ →
          HasCoulombSpinHamiltonian sys L H₀ H₁ → ‖Ψ₀‖ = 1 →
          ∀ (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (CM : ℕ → ℝ),
          HChi (2 * Real.pi / L) (mFourierCoeff χ) CM →
          (∀ y, (χ y).im = 0 ∧ 0 ≤ (χ y).re ∧ (χ y).re ≤ 1) →
          let A := gridConstsSharp sys L molecularCanonicalUnitHardyConstant
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) a (mFourierCoeff χ) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let Ψg := Ug t (spinGridData m Ψ₀)
            ‖⟪U t Ψ₀, spinLift (mulCLM (regFun a χ)) (U t Ψ₀)⟫_ℂ -
                ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ‖ ≤
              min 1 ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖Ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
                A.2.1 * t * (1 / K) ^ 3) := by
  obtain ⟨U, s0, s1, s2, s3, s4, s5, s6, hrest⟩ := thm_grid_dyn_sharp_spin sys L hL D
  refine ⟨U, s0, s1, s2, s3, s4, s5, s6, fun m κ hκ => ?_⟩
  obtain ⟨Ug, g0, g1, g2, g3, g4, g5, hbound⟩ := hrest m κ hκ
  refine ⟨Ug, g0, g1, g2, g3, g4, g5, ?_⟩
  intro Ψ₀ H₀ H₁ hΨ₀ hH₀ hnorm a χ CM hc hχ A hm hK t ht K Ψg
  have hreal : ∀ y, conj (χ y) = χ y := fun y => by
    apply Complex.ext
    · simp
    · simp [(hχ y).1]
  refine le_min ?_ (hbound Ψ₀ H₀ H₁ hΨ₀ hH₀ a χ CM hc hreal hm hK t ht)
  obtain ⟨h1, h2⟩ := spin_expectations_mem a χ hχ (U t Ψ₀) Ψg
  have hUt : ‖U t Ψ₀‖ ^ 2 ≤ 1 := by rw [LinearIsometryEquiv.norm_map, hnorm]; norm_num
  have hΨg : ‖Ψg‖ ^ 2 ≤ 1 := by
    have e : ‖Ψg‖ = ‖spinGridData m Ψ₀‖ := LinearIsometryEquiv.norm_map _ _
    have h3 := norm_spinGridData_le m Ψ₀
    rw [hnorm] at h3
    rw [e]
    have h4 := norm_nonneg (spinGridData m Ψ₀)
    nlinarith
  exact norm_sub_le_of_inUnitSeg h1 h2 hUt hΨg

/-- The defect of the spin-inclusive grid datum: for `‖Ψ₀‖ = 1`,
`1 - ‖Ψ_g(0)‖² ≤ (δ₁ K^{-5/2})²` with `δ₁` at the spin-inclusive norms
(`1 - ‖Ψ_g(0)‖² = ‖(1 - P) Ψ₀‖²` with `P` the projection at cutoff `2K`, `spin_proj_defect` at
`n = 2m`, and `(2K)^{-5/2} ≤ K^{-5/2}`). -/
lemma spinGridData_defect (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) (m : ℕ) (hm : 8 ≤ m)
    (hK : 8 ≤ (2 * Real.pi / L) * m) {D : ℕ} (Ψ₀ H₀ H₁ : CoulombSpinL2 eta D)
    (hΨ₀ : HasCoulombSpinHamiltonian sys L Ψ₀ H₀) (hH₀ : HasCoulombSpinHamiltonian sys L H₀ H₁)
    (hnorm : ‖Ψ₀‖ = 1) :
    1 - ‖spinGridData m Ψ₀‖ ^ 2 ≤ (obsTailConst sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖ *
        Real.sqrt (1 / ((2 * Real.pi / L) * m)) ^ 5) ^ 2 := by
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  set δ₁ := obsTailConst sys L molecularCanonicalUnitHardyConstant
    (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
    (molecularCanonicalKernelConstant L) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖ with hδ₁
  have hδ0 : 0 ≤ δ₁ := obsTailConst_canonical_nonneg sys L hL (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _)
  set g : ℝ := 2 * Real.pi / L with hgdef
  have hg : 0 < g := by positivity
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hK2 : 2 ≤ g * ((2 * m : ℕ) : ℝ) := by rw [h2m]; linarith
  have h2gK : 2 * g ≤ g * ((2 * m : ℕ) : ℝ) := by
    rw [h2m]
    have : (8 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hK₂pos : 0 < g * ((2 * m : ℕ) : ℝ) := by linarith
  have hρ₂ : Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1 := by
    rw [Real.sq_sqrt (by positivity)]
    exact one_div_mul_cancel hK₂pos.ne'
  obtain ⟨-, hdef⟩ := spin_proj_defect sys L hL (2 * m) _ _ _ _ hK2 (Real.sqrt_nonneg _) hρ₂
    hBlow hCs hBker h2gK hLow hKernelScale hSobolev Ψ₀ H₀ H₁ hΨ₀ hH₀
  have hPσ : ∀ σ, ‖spinGridData m Ψ₀ σ‖ = ‖physMap eta (molecularH2Truncate (2 * m)
      ((physMap eta).symm (Ψ₀ σ)))‖ := fun σ => by
    rw [spinGridData_apply, ← dftLIE_symm_apply, LinearIsometryEquiv.norm_map,
      LinearIsometryEquiv.norm_map, ← (regEmb m).norm_map, regEmb_regCoeff]
  have hcP : ‖spinGridData m Ψ₀‖ = ‖(WithLp.toLp 2 fun σ => physMap eta (molecularH2Truncate
      (2 * m) ((physMap eta).symm (Ψ₀ σ))) : CoulombSpinL2 eta D)‖ := by
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    simp only [hPσ]
  rw [← hcP] at hdef
  have hρle : Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ≤ Real.sqrt (1 / (g * m)) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hK₂pos (by show 0 < g * (m : ℝ); linarith), h2m, one_mul, one_mul]
    have e : g * (2 * (m : ℝ)) = 2 * (g * m) := by ring
    rw [e]
    linarith
  have h1 : ‖Ψ₀‖ ^ 2 = 1 := by rw [hnorm]; norm_num
  have h2 : δ₁ * Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 5 ≤ δ₁ * Real.sqrt (1 / (g * m)) ^ 5 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hρle 5) hδ0
  have h3 := pow_le_pow_left₀ (mul_nonneg hδ0 (pow_nonneg (Real.sqrt_nonneg _) 5)) h2 2
  linarith

/-- **The normalised spin-inclusive grid state** (`cor:norm` at cutoff `2K`, with spin). Under
the hypotheses of `grid_observable_position_spin`, with `‖Ψ₀‖ = 1`, `|χ| ≤ 1` and `P Ψ₀ ≠ 0`, the
normalised grid state `Ψ̃_g(t) = Ψ_g(t)/‖P Ψ₀‖` satisfies the same bound up to
`‖(1 - P) Ψ₀‖² ≤ (δ₁ K^{-5/2})²` (`δ₁ = obsTailConst` at the spin-inclusive norms, Minkowski's
inequality over the components, `spinGridData_defect`). -/
theorem grid_observable_normalised_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    {D : ℕ} (Ψ₀ H₀ H₁ : CoulombSpinL2 eta D) (hΨ₀ : HasCoulombSpinHamiltonian sys L Ψ₀ H₀)
    (hH₀ : HasCoulombSpinHamiltonian sys L H₀ H₁) (hnorm : ‖Ψ₀‖ = 1)
    (hP : spinGridData m Ψ₀ ≠ 0)
    (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχ1 : Summable fun ν => ‖mFourierCoeff χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖mFourierCoeff χ ν‖)
    (hreal : ∀ y, conj (χ y) = χ y) (hχb : ∀ y, ‖χ y‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridConsts sys L molecularCanonicalUnitHardyConstant (molecularCanonicalLowConstant L)
      (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L) a
      (mFourierCoeff χ) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then ‖mFourierCoeff χ ν‖ else 0
    let δ₁ : ℝ := obsTailConst sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
    let c : ℝ := ‖spinGridData m Ψ₀‖
    let Ψg := spinGridProp (fun s => posConj (Ug s)) t (spinGridData m Ψ₀)
    let Ψgt := ((c : ℂ)⁻¹) • Ψg
    ‖⟪spinProp U t Ψ₀, spinLift (mulCLM (regFun a χ)) (spinProp U t Ψ₀)⟫_ℂ -
        ⟪Ψgt, spinPosObs a χ Ψgt⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * Real.sqrt (1 / K) ^ 5 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖Ψ₀‖ ^ 2 * supTail (mFourierCoeff χ) m + (δ₁ * Real.sqrt (1 / K) ^ 5) ^ 2 := by
  intro g K A τχ δ₁ c Ψg Ψgt
  have hdef : 1 - c ^ 2 ≤ (δ₁ * Real.sqrt (1 / K) ^ 5) ^ 2 :=
    spinGridData_defect sys L hL m hm hK Ψ₀ H₀ H₁ hΨ₀ hH₀ hnorm
  have hmain := grid_observable_position_spin sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0
    hgcomm hgderiv Ψ₀ H₀ H₁ hΨ₀ hH₀ a χ hχ1 hχ2 hreal ht
  -- the normalisation
  have hc : ‖Ψg‖ = c := LinearIsometryEquiv.norm_map _ _
  have hc0 : 0 < c := norm_pos_iff.mpr hP
  have hc1 : c ≤ 1 := hnorm ▸ norm_spinGridData_le m Ψ₀
  have hnormal : ‖⟪Ψgt, spinPosObs a χ Ψgt⟫_ℂ - ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ‖ ≤ 1 - c ^ 2 :=
    spin_normalize_sub_le a χ hχb Ψg hc hc0 hc1
  -- combine
  have htri := norm_sub_le_norm_sub_add_norm_sub
    ⟪spinProp U t Ψ₀, spinLift (mulCLM (regFun a χ)) (spinProp U t Ψ₀)⟫_ℂ
    ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ ⟪Ψgt, spinPosObs a χ Ψgt⟫_ℂ
  have hswap : ‖⟪Ψg, spinPosObs a χ Ψg⟫_ℂ - ⟪Ψgt, spinPosObs a χ Ψgt⟫_ℂ‖ =
      ‖⟪Ψgt, spinPosObs a χ Ψgt⟫_ℂ - ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ‖ := norm_sub_rev _ _
  have hmain' : ‖⟪spinProp U t Ψ₀, spinLift (mulCLM (regFun a χ)) (spinProp U t Ψ₀)⟫_ℂ -
      ⟪Ψg, spinPosObs a χ Ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * Real.sqrt (1 / K) ^ 5 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖Ψ₀‖ ^ 2 * supTail (mFourierCoeff χ) m := hmain
  linarith

/-- **The threshold of `cor:norm` on the spin-inclusive grid.** For `‖Ψ₀‖ = 1`, `Ψ₀ ∈ D(H²)`,
`m ≥ 8` and `K = 2πm/L ≥ 8`, as soon as `(δ₁ K^{-5/2})² ≤ 1/2` (`δ₁` at the spin-inclusive
norms), `‖Ψ_g(0)‖² ≥ 1/2`; in particular `spinGridData m Ψ₀ ≠ 0`, as
`grid_observable_normalised_spin` requires (`spinGridData_defect`). -/
theorem grid_normalisation_threshold_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {D : ℕ}
    (Ψ₀ H₀ H₁ : CoulombSpinL2 eta D) (hΨ₀ : HasCoulombSpinHamiltonian sys L Ψ₀ H₀)
    (hH₀ : HasCoulombSpinHamiltonian sys L H₀ H₁) (hnorm : ‖Ψ₀‖ = 1)
    (hthr : (obsTailConst sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖ *
        Real.sqrt (1 / ((2 * Real.pi / L) * m)) ^ 5) ^ 2 ≤ 1 / 2) :
    1 / 2 ≤ ‖spinGridData m Ψ₀‖ ^ 2 ∧ spinGridData m Ψ₀ ≠ 0 := by
  have hdef := spinGridData_defect sys L hL m hm hK Ψ₀ H₀ H₁ hΨ₀ hH₀ hnorm
  have hhalf : 1 / 2 ≤ ‖spinGridData m Ψ₀‖ ^ 2 := by linarith
  refine ⟨hhalf, fun h0 => ?_⟩
  rw [h0, norm_zero] at hhalf
  norm_num at hhalf

end GridDynSpin

end PlaneWaveSpin

end DevSP2
-- END SOURCE dev/DevSP2.lean

-- BEGIN SOURCE dev/DevSP3.lean
-- SHA256 d6ca1c954b8f1c10c5dcdfcbf44ff8b7d517dc5cd5ebd7a47ce399de28795392
section DevSP3

/-!
# Grid kinetic energy and the stopping power with internal spin

`prop:mult-grid`, the grid route of `thm:mult-cap` and the grid forms of `cor:stopping` and
`cor:stopping2` on the spin-inclusive space: the kinetic energy `A_r` applied through the DFT on
every spin component of the spin-inclusive grid state `Ψ_g(t) = (e^{-iH_pos t} ⊗ 1) P Ψ₀`
(`spinPosKinExpect`), against `A_r ⊗ 1` in `Ψ(t)` (`spinPosExpect`). The constants are those of
the spinless theorems (`gridKinConsts`, `capGridRateConsts`, `gridCapMinConsts`) at the
spin-inclusive norms; the minimum form combines the two transferred branches at those norms.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate lp ENNReal Topology
open Filter Set UnitAddTorus

namespace PlaneWaveSpin

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics PlaneWaveKinetic

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The grid kinetic bounds as `ℓ²`-superadditive functions of the data -/

section GridKinBounds

/-- The bound of `prop:mult-grid` (`gridKinConsts`) is superadditive under `ℓ²` combination (for
all `c_i ≥ 0`). -/
lemma l2quad_gridKinBound (sys : CoulombSystem eta ν) {L Hunit Blow Cs Bker : ℝ} (hL : 0 < L)
    (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs)
    (hBker : 0 ≤ Bker) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    L2Quad (fun x : Fin 4 → ℝ =>
      (gridKinConsts sys L Hunit Blow Cs Bker (x 0) (x 1) (x 2) (x 3)).1 * c₁ +
        (gridKinConsts sys L Hunit Blow Cs Bker (x 0) (x 1) (x 2) (x 3)).2 * c₂) := by
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hm : 0 ≤ sys.maxMass := by linarith [sys.one_le_maxMass]
  have hCt : 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker 1 :=
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker zero_le_one
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hZ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg hγ
  have hcJ := gridFlowConst_nonneg sys hL
  have hcG := coulombGridCoupling_nonneg sys L hL
  simp only [gridKinConsts, flow2]
  l2quad

/-- `gridTailConst` (the constant `D_g` of `lem:grid-tails`) is `ℓ²`-subadditive. -/
lemma l2sub_gridTailConst (sys : CoulombSystem eta ν) {L Hunit Blow Cs Bker : ℝ} (hL : 0 < L)
    (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs)
    (hBker : 0 ≤ Bker) :
    L2Sub (fun x : Fin 4 → ℝ =>
      gridTailConst sys L Hunit Blow Cs Bker (x 0) (x 1) (x 2) (x 3)) := by
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hm : 0 ≤ sys.maxMass := by linarith [sys.one_le_maxMass]
  have hCt : 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker 1 :=
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker zero_le_one
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hZ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg hγ
  have hcJ := gridFlowConst_nonneg sys hL
  simp only [gridTailConst]
  l2sub

/-- The bound of the capped grid rate (`capGridRateConsts`) is superadditive under `ℓ²`
combination (for all `c_i ≥ 0`). -/
lemma l2quad_capGridRateBound (sys : CoulombSystem eta ν) {L Hunit Blow Cs Bker lam0 : ℝ}
    (hL : 0 < L) (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit) (hBlow : 0 ≤ Blow)
    (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker) (hl : 0 ≤ lam0) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) :
    L2Quad (fun x : Fin 4 → ℝ =>
      (capGridRateConsts sys L Hunit Blow Cs Bker lam0 (x 0) (x 1) (x 2) (x 3)).1 * c₁ +
        (capGridRateConsts sys L Hunit Blow Cs Bker lam0 (x 0) (x 1) (x 2) (x 3)).2 * c₂) := by
  have hb : 0 ≤ relB sys L Hunit := relB_nonneg sys L Hunit hC
  have hm : 0 ≤ sys.maxMass := by linarith [sys.one_le_maxMass]
  have hCt : 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker 1 :=
    finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker zero_le_one
  have hγ : 0 ≤ coulombCellAmplitude L := (coulombCellAmplitude_pos hL).le
  have hZ : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) := Zc_nonneg hγ
  have hcJ := gridFlowConst_nonneg sys hL
  have hDg := l2sub_gridTailConst sys hL hC hBlow hCs hBker
  simp only [capGridRateConsts, capGridConsts, gridTrivConst]
  l2quad

end GridKinBounds

/-! ## `prop:mult-grid`, `thm:mult-cap` (grid), `cor:stopping` and `cor:stopping2` (grid) with
internal spin -/

section GridKinSpin

/-- **`prop:mult-grid` with internal spin**, position space: the bound of `grid_kinetic_position`
(`A₁ K^{-3} + A₂ t K^{-1}`, `(A₁, A₂) = gridKinConsts`) at the spin-inclusive norms. -/
theorem grid_kinetic_position_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    {D : ℕ} (Ψ₀ H₀ H₁ : CoulombSpinL2 eta D) (hΨ₀ : HasCoulombSpinHamiltonian sys L Ψ₀ H₀)
    (hH₀ : HasCoulombSpinHamiltonian sys L H₀ H₁) (r : Fin eta) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridKinConsts sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
    let Ψg := spinGridProp (fun s => posConj (Ug s)) t (spinGridData m Ψ₀)
    |spinPosExpect (regKin sys g r) (spinProp U t Ψ₀) - spinPosKinExpect sys g r Ψg| ≤
      A.1 * (1 / K) ^ 3 + A.2 * t * (1 / K) := by
  intro g K A Ψg
  obtain ⟨hBlow, hCs, hBker, -⟩ := molecularCanonicalTailConstants_spec L hL
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L molecularCanonicalUnitHardyConstant
  have hB := l2quad_gridKinBound sys hL hC hBlow hCs hBker (c₁ := (1 / K) ^ 3)
    (c₂ := t * (1 / K)) (by positivity) (by positivity)
  have h := hB.norm_sum_le_l2comb
    (fun σ => ((regKin sys g r).posExpect (U t (Ψ₀ σ)) - posKinExpect sys g r (Ψg σ)))
    (spinData Ψ₀ H₀ H₁) (spinData_nonneg Ψ₀ H₀ H₁) (fun σ => by
      have hσ := grid_kinetic_position sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
        hgderiv (Ψ₀ σ) (H₀ σ) (H₁ σ) (hΨ₀ σ) (hH₀ σ) r ht
      rw [Real.norm_eq_abs]
      refine hσ.trans_eq ?_
      simp only [spinData, Matrix.cons_val]
      ring)
  rw [l2comb_spinData] at h
  have hsplit : spinPosExpect (regKin sys g r) (spinProp U t Ψ₀) - spinPosKinExpect sys g r Ψg =
      ∑ σ, ((regKin sys g r).posExpect (U t (Ψ₀ σ)) - posKinExpect sys g r (Ψg σ)) := by
    simp only [spinPosExpect, spinPosKinExpect, ← Finset.sum_sub_distrib]
    rfl
  rw [hsplit, ← Real.norm_eq_abs]
  refine h.trans_eq ?_
  simp only [Matrix.cons_val, A]
  ring

/-- **`thm:mult-cap` (grid) with internal spin, the sublinear branch**, position space: the bound
of `grid_capped_position` at the spin-inclusive norms. -/
theorem grid_capped_position_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    {D : ℕ} (Ψ₀ H₀ H₁ : CoulombSpinL2 eta D) (hΨ₀ : HasCoulombSpinHamiltonian sys L Ψ₀ H₀)
    (hH₀ : HasCoulombSpinHamiltonian sys L H₀ H₁) (r : Fin eta) {lam0 : ℝ} (hl : 1 ≤ lam0)
    (h4g : 4 * (2 * Real.pi / L) ≤ lam0) (hlK : lam0 ≤ (2 * Real.pi / L) * m) {t : ℝ}
    (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let C := capGridRateConsts sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) lam0 ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
    let Ψg := spinGridProp (fun s => posConj (Ug s)) t (spinGridData m Ψ₀)
    |spinPosExpect (regKin sys g r) (spinProp U t Ψ₀) - spinPosKinExpect sys g r Ψg| ≤
      C.1 * (1 / K) ^ 3 + C.2 * t ^ ((2 : ℝ) / 3) * (1 / K) ^ ((5 : ℝ) / 3) := by
  intro g K C Ψg
  obtain ⟨hBlow, hCs, hBker, -⟩ := molecularCanonicalTailConstants_spec L hL
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L molecularCanonicalUnitHardyConstant
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (hl.trans hlK)
  have hB := l2quad_capGridRateBound sys hL hC hBlow hCs hBker (lam0 := lam0) (by linarith)
    (c₁ := (1 / K) ^ 3) (c₂ := t ^ ((2 : ℝ) / 3) * (1 / K) ^ ((5 : ℝ) / 3)) (by positivity)
    (mul_nonneg (Real.rpow_nonneg ht _) (Real.rpow_nonneg (one_div_nonneg.mpr hKpos.le) _))
  have h := hB.norm_sum_le_l2comb
    (fun σ => ((regKin sys g r).posExpect (U t (Ψ₀ σ)) - posKinExpect sys g r (Ψg σ)))
    (spinData Ψ₀ H₀ H₁) (spinData_nonneg Ψ₀ H₀ H₁) (fun σ => by
      have hσ := grid_capped_position sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
        hgderiv (Ψ₀ σ) (H₀ σ) (H₁ σ) (hΨ₀ σ) (hH₀ σ) r hl h4g hlK ht
      rw [Real.norm_eq_abs]
      refine hσ.trans_eq ?_
      simp only [spinData, Matrix.cons_val]
      ring)
  rw [l2comb_spinData] at h
  have hsplit : spinPosExpect (regKin sys g r) (spinProp U t Ψ₀) - spinPosKinExpect sys g r Ψg =
      ∑ σ, ((regKin sys g r).posExpect (U t (Ψ₀ σ)) - posKinExpect sys g r (Ψg σ)) := by
    simp only [spinPosExpect, spinPosKinExpect, ← Finset.sum_sub_distrib]
    rfl
  rw [hsplit, ← Real.norm_eq_abs]
  refine h.trans_eq ?_
  simp only [Matrix.cons_val, C]
  ring

/-- **`thm:mult-cap` (grid) with internal spin**, position space, minimum form
`D₁ K^{-3} + D₂ min(t K^{-1}, t^{2/3} K^{-5/3})` with `(D₁, D₂) = gridCapMinConsts` at the
spin-inclusive norms. -/
theorem grid_capped_min_position_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    {D : ℕ} (Ψ₀ H₀ H₁ : CoulombSpinL2 eta D) (hΨ₀ : HasCoulombSpinHamiltonian sys L Ψ₀ H₀)
    (hH₀ : HasCoulombSpinHamiltonian sys L H₀ H₁) (r : Fin eta) {lam0 : ℝ} (hl : 1 ≤ lam0)
    (h4g : 4 * (2 * Real.pi / L) ≤ lam0) (hlK : lam0 ≤ (2 * Real.pi / L) * m) {t : ℝ}
    (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let Dc := gridCapMinConsts sys L lam0 ‖Ψ₀‖ ‖H₀‖ ‖H₁‖
    let Ψg := spinGridProp (fun s => posConj (Ug s)) t (spinGridData m Ψ₀)
    |spinPosExpect (regKin sys g r) (spinProp U t Ψ₀) - spinPosKinExpect sys g r Ψg| ≤
      Dc.1 * (1 / K) ^ 3 +
        Dc.2 * min (t * (1 / K)) (t ^ ((2 : ℝ) / 3) * (1 / K) ^ ((5 : ℝ) / 3)) := by
  intro g K Dc Ψg
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (hl.trans hlK)
  have hA := grid_kinetic_position_spin sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
      hgderiv Ψ₀ H₀ H₁ hΨ₀ hH₀ r ht
  have hB := grid_capped_position_spin sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
      hgderiv Ψ₀ H₀ H₁ hΨ₀ hH₀ r hl h4g hlK ht
  dsimp only at hA hB
  refine le_max_min_combine (pow_nonneg (one_div_nonneg.mpr hKpos.le) 3)
    (mul_nonneg ht (one_div_nonneg.mpr hKpos.le))
    (mul_nonneg (Real.rpow_nonneg ht _) (Real.rpow_nonneg (one_div_nonneg.mpr hKpos.le) _))
    (hA.trans_eq ?_) (hB.trans_eq ?_)
  · ring
  · ring

/-- **`prop:mult-grid` with internal spin and its propagators**: the propagators of
`thm_grid_dyn_spin`, and for every spin-inclusive `Ψ₀ ∈ D(H²)`, particle `r`, `m ≥ 8`,
`K = 2πm/L ≥ 8` and `t ≥ 0`,
`|⟨Ψ(t), (A_r ⊗ 1) Ψ(t)⟩ - ⟨Ψ_g(t), (A_r ⊗ 1) Ψ_g(t)⟩| ≤ A₁ K^{-3} + A₂ t K^{-1}` (`A_r`
applied through the DFT) with
`(A₁, A₂) = gridKinConsts` at the spin-inclusive norms. -/
theorem thm_mult_grid_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) (D : ℕ) :
    ∃ U : ℝ → CoulombSpinL2 eta D ≃ₗᵢ[ℂ] CoulombSpinL2 eta D,
      (∀ Ψ, U 0 Ψ = Ψ) ∧
      (∀ s t Ψ, U (s + t) Ψ = U s (U t Ψ)) ∧
      (∀ Ψ, Continuous fun t => U t Ψ) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasCoulombSpinHamiltonian sys L (U t Ψ) (U t Φ)) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasDerivAt (fun s => U s Ψ) (-(Complex.I • U t Φ)) t) ∧
      (∀ φ ζ : ℝ → CoulombSpinL2 eta D, (∀ t, HasCoulombSpinHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      (∀ t, ∃ V : MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
        ∀ Ψ σ, U t Ψ σ = V (Ψ σ)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → CoulombGridSpinState eta D m ≃ₗᵢ[ℂ] CoulombGridSpinState eta D m,
        (∀ Φ, Ug 0 Φ = Φ) ∧ (∀ s t Φ, Ug (s + t) Φ = Ug s (Ug t Φ)) ∧
        (∀ Φ, Continuous fun t => Ug t Φ) ∧
        (∀ t Φ, Ug t (spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) Φ) = spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t Φ)) ∧
        (∀ t Φ, HasDerivAt (fun s => Ug s Φ) (-(Complex.I • Ug t (spinHpos
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Φ))) t) ∧
        (∀ t, ∃ W : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
          ∀ Φ σ, Ug t Φ σ = W (Φ σ)) ∧
        ∀ Ψ₀ H₀ H₁ : CoulombSpinL2 eta D, HasCoulombSpinHamiltonian sys L Ψ₀ H₀ →
          HasCoulombSpinHamiltonian sys L H₀ H₁ → ∀ r : Fin eta,
          let A := gridKinConsts sys L molecularCanonicalUnitHardyConstant
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let Ψg := Ug t (spinGridData m Ψ₀)
            |spinPosExpect (regKin sys (2 * Real.pi / L) r) (U t Ψ₀) -
                spinPosKinExpect sys (2 * Real.pi / L) r Ψg| ≤
              A.1 * (1 / K) ^ 3 + A.2 * t * (1 / K) := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, -, -⟩ := exists_coulombPropagator sys L hL
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := spinProp_spec sys L D U h0 hadd hcont hgraph hderiv huniq
  refine ⟨spinProp U, s0, s1, s2, s3, s4, s5, s6, fun m κ hκ => ?_⟩
  obtain ⟨Ur, hr0, -, -, hrcomm, hrderiv, hp0, hpadd, hpcont, hpcomm, hpderiv⟩ :=
    exists_posPropagator (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) hκ.even
      (2 * Real.pi / L)
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := spinGridProp_spec (S := Fin eta → Fin D)
    (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) (fun t => posConj (Ur t))
    hp0 hpadd hpcont hpcomm hpderiv
  refine ⟨spinGridProp (fun t => posConj (Ur t)), g0, g1, g2, g3, g4, g5, ?_⟩
  intro Ψ₀ H₀ H₁ hΨ₀ hH₀ r A hm hK t ht K Ψg
  exact grid_kinetic_position_spin sys L hL U h0 hgraph hderiv m hm hK hκ Ur hr0 hrcomm hrderiv Ψ₀
      H₀ H₁ hΨ₀ hH₀ r ht

/-- **`thm:mult-cap` (grid) with internal spin and its propagators**: as `thm_mult_grid_spin`,
for every lowest cap `λ₀ ≥ max(1, 4g)` and `K ≥ max(8, λ₀)`, the bound
`D₁ K^{-3} + D₂ min(t K^{-1}, t^{2/3} K^{-5/3})` with `(D₁, D₂) = gridCapMinConsts` at
`(λ₀, ‖Ψ₀‖, ‖H₀‖, ‖H₁‖)`. -/
theorem thm_mult_cap_grid_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) (D : ℕ) :
    ∃ U : ℝ → CoulombSpinL2 eta D ≃ₗᵢ[ℂ] CoulombSpinL2 eta D,
      (∀ Ψ, U 0 Ψ = Ψ) ∧
      (∀ s t Ψ, U (s + t) Ψ = U s (U t Ψ)) ∧
      (∀ Ψ, Continuous fun t => U t Ψ) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasCoulombSpinHamiltonian sys L (U t Ψ) (U t Φ)) ∧
      (∀ t Ψ Φ, HasCoulombSpinHamiltonian sys L Ψ Φ →
        HasDerivAt (fun s => U s Ψ) (-(Complex.I • U t Φ)) t) ∧
      (∀ φ ζ : ℝ → CoulombSpinL2 eta D, (∀ t, HasCoulombSpinHamiltonian sys L (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      (∀ t, ∃ V : MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
        ∀ Ψ σ, U t Ψ σ = V (Ψ σ)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), IsGridKernel (coulombCellAmplitude L) m κ →
      ∃ Ug : ℝ → CoulombGridSpinState eta D m ≃ₗᵢ[ℂ] CoulombGridSpinState eta D m,
        (∀ Φ, Ug 0 Φ = Φ) ∧ (∀ s t Φ, Ug (s + t) Φ = Ug s (Ug t Φ)) ∧
        (∀ Φ, Continuous fun t => Ug t Φ) ∧
        (∀ t Φ, Ug t (spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) Φ) = spinHpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t Φ)) ∧
        (∀ t Φ, HasDerivAt (fun s => Ug s Φ) (-(Complex.I • Ug t (spinHpos
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Φ))) t) ∧
        (∀ t, ∃ W : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
          ∀ Φ σ, Ug t Φ σ = W (Φ σ)) ∧
        ∀ Ψ₀ H₀ H₁ : CoulombSpinL2 eta D, HasCoulombSpinHamiltonian sys L Ψ₀ H₀ →
          HasCoulombSpinHamiltonian sys L H₀ H₁ →
          ∀ (r : Fin eta) (lam0 : ℝ), 1 ≤ lam0 → 4 * (2 * Real.pi / L) ≤ lam0 →
          let Dc := gridCapMinConsts sys L lam0 ‖Ψ₀‖ ‖H₀‖ ‖H₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → lam0 ≤ (2 * Real.pi / L) * m →
            ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let Ψg := Ug t (spinGridData m Ψ₀)
            |spinPosExpect (regKin sys (2 * Real.pi / L) r) (U t Ψ₀) -
                spinPosKinExpect sys (2 * Real.pi / L) r Ψg| ≤
              Dc.1 * (1 / K) ^ 3 +
                Dc.2 * min (t * (1 / K)) (t ^ ((2 : ℝ) / 3) * (1 / K) ^ ((5 : ℝ) / 3)) := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, -, -⟩ := exists_coulombPropagator sys L hL
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := spinProp_spec sys L D U h0 hadd hcont hgraph hderiv huniq
  refine ⟨spinProp U, s0, s1, s2, s3, s4, s5, s6, fun m κ hκ => ?_⟩
  obtain ⟨Ur, hr0, -, -, hrcomm, hrderiv, hp0, hpadd, hpcont, hpcomm, hpderiv⟩ :=
    exists_posPropagator (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) hκ.even
      (2 * Real.pi / L)
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := spinGridProp_spec (S := Fin eta → Fin D)
    (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) (fun t => posConj (Ur t))
    hp0 hpadd hpcont hpcomm hpderiv
  refine ⟨spinGridProp (fun t => posConj (Ur t)), g0, g1, g2, g3, g4, g5, ?_⟩
  intro Ψ₀ H₀ H₁ hΨ₀ hH₀ r lam0 hl h4g Dc hm hK hlK t ht K Ψg
  exact grid_capped_min_position_spin sys L hL U h0 hgraph hderiv m hm hK hκ Ur hr0 hrcomm hrderiv
      Ψ₀ H₀ H₁ hΨ₀ hH₀ r hl h4g hlK ht

/-- **`cor:stopping`, grid route, with internal spin.** In the setting of
`grid_kinetic_position_spin`, the secant-slope estimator over `[0, T]` deviates by at most
`(A₂ K^{-1} + 2 A₁ K^{-3}/T)/v_p`. -/
theorem stopping_grid_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    {D : ℕ} (Ψ₀ H₀ H₁ : CoulombSpinL2 eta D) (hΨ₀ : HasCoulombSpinHamiltonian sys L Ψ₀ H₀)
    (hH₀ : HasCoulombSpinHamiltonian sys L H₀ H₁) (r : Fin eta) {vp T : ℝ} (hvp : 0 < vp)
    (hT : 0 < T) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridKinConsts sys L molecularCanonicalUnitHardyConstant
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) ‖Ψ₀‖ ‖H₀‖ ‖H₀‖ ‖H₁‖
    let Ψg : ℝ → CoulombGridSpinState eta D m := fun s =>
      spinGridProp (fun u => posConj (Ug u)) s (spinGridData m Ψ₀)
    let μ := regKin sys g r
    |(spinPosExpect μ (spinProp U T Ψ₀) - spinPosExpect μ (spinProp U 0 Ψ₀)) / (vp * T) -
        (spinPosKinExpect sys g r (Ψg T) - spinPosKinExpect sys g r (Ψg 0)) / (vp * T)| ≤
      (A.2 * (1 / K) + 2 * A.1 * (1 / K) ^ 3 / T) / vp := by
  intro g K A Ψg μ
  have h0 := grid_kinetic_position_spin sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
      hgderiv Ψ₀ H₀ H₁ hΨ₀ hH₀ r (le_refl 0)
  have hT' := grid_kinetic_position_spin sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
      hgderiv Ψ₀ H₀ H₁ hΨ₀ hH₀ r hT.le
  exact (secant_slope_le hvp hT h0 hT').trans (le_of_eq (stopping_arith hvp hT))

/-- **`cor:stopping2`, grid route, with internal spin (window law).** In the setting of
`grid_capped_min_position_spin`, the secant-slope estimator deviates by at most
`(D₂ min(K^{-1}, T^{-1/3} K^{-5/3}) + 2 D₁ K^{-3}/T)/v_p`. -/
theorem stopping_window_grid_spin (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasCoulombHamiltonian sys L (U t f) (U t h))
    (hUderiv : ∀ t f h, HasCoulombHamiltonian sys L f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    {D : ℕ} (Ψ₀ H₀ H₁ : CoulombSpinL2 eta D) (hΨ₀ : HasCoulombSpinHamiltonian sys L Ψ₀ H₀)
    (hH₀ : HasCoulombSpinHamiltonian sys L H₀ H₁) (r : Fin eta) {lam0 : ℝ} (hl : 1 ≤ lam0)
    (h4g : 4 * (2 * Real.pi / L) ≤ lam0) (hlK : lam0 ≤ (2 * Real.pi / L) * m) {vp T : ℝ}
    (hvp : 0 < vp) (hT : 0 < T) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let Dc := gridCapMinConsts sys L lam0 ‖Ψ₀‖ ‖H₀‖ ‖H₁‖
    let Ψg : ℝ → CoulombGridSpinState eta D m := fun s =>
      spinGridProp (fun u => posConj (Ug u)) s (spinGridData m Ψ₀)
    let μ := regKin sys g r
    |(spinPosExpect μ (spinProp U T Ψ₀) - spinPosExpect μ (spinProp U 0 Ψ₀)) / (vp * T) -
        (spinPosKinExpect sys g r (Ψg T) - spinPosKinExpect sys g r (Ψg 0)) / (vp * T)| ≤
      (Dc.2 * min (1 / K) ((1 / K) ^ ((5 : ℝ) / 3) / T ^ ((1 : ℝ) / 3)) +
        2 * Dc.1 * (1 / K) ^ 3 / T) / vp := by
  intro g K Dc Ψg μ
  have h0 := grid_capped_min_position_spin sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
      hgderiv Ψ₀ H₀ H₁ hΨ₀ hH₀ r hl h4g hlK (le_refl 0)
  have hT' := grid_capped_min_position_spin sys L hL U hU0 hUgraph hUderiv m hm hK hκ Ug hg0 hgcomm
      hgderiv Ψ₀ H₀ H₁ hΨ₀ hH₀ r hl h4g hlK hT.le
  exact (secant_slope_le hvp hT h0 hT').trans (le_of_eq (window_arith hvp hT))

end GridKinSpin

end PlaneWaveSpin

end DevSP3
-- END SOURCE dev/DevSP3.lean
