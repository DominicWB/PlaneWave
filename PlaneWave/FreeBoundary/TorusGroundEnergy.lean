import PlaneWave.FreeBoundary.CubeHamiltonian

/-!
# `app:free`, part 5: the `g_L` Hamiltonian on all cubes and the torus ground energy

For a Coulomb system on the cell `T_L` and the range-truncated kernel `g_L` (`PlaneWave.FreeBoundary.RangeCut`, `PlaneWave.FreeBoundary.CubeHamiltonian`):

* `gLham_eq_latticeKernel`: every finite-cube `g_L` Hamiltonian is the compression of one lattice
  kernel (`gLlatHam`), as the release proves for the Coulomb Hamiltonian;
* `gLham_preserves_sector`, `gL_exists_sector_ground`: the exchange sectors of an admissible
  labelling are invariant, and every cube with at least `η` modes has a sector ground state;
* `transport`: the isometric inclusion of the cube `M` in the cube `n ≥ M` (by lattice index); it
  preserves the sectors and the quadratic form of the Hamiltonian (`transport_form`), and its
  image is the cubic Galerkin space at cutoff `(2π/L) M` (`exists_transport_of_cubic`);
* `IsGLTorusGroundEnergy`: the torus ground energy `E_L` of the `g_L` Hamiltonian in the sector,
  the infimum of its quadratic form over the finite Fourier states (trigonometric polynomials) of
  the sector; it exists (`exists_gLTorusGroundEnergy`) and is the limit of the cube ground
  energies (`tendsto_cube_ground`);
* **`gL_cubic_error`**: for a cube `M` with `K = (2π/L) M` above the explicit thresholds, the
  sector ground energy `E_M` of the cube (the cubic Galerkin energy at cutoff `K`) satisfies
  `0 ≤ E_M - E_L` and `K³ (E_M - E_L) ≤ 64 (1/2 + C_pot + |E_L|) S₁ S₂ C_W²`;
  **`gL_sector_cubic_error`** packages this with the explicit Hardy constant and an explicit
  threshold.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin FSNormal

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν] {R : ℝ} {θ : ℝ → ℝ}

/-! ## Lattice kernels -/

/-- `ĝ_L` on the lattice, without the zero mode. -/
noncomputable def gLlat (L : ℝ) (θ : ℝ → ℝ) (x : Lattice3) : ℂ := by
  classical
  exact if x = (fun _ => 0) then 0 else ghat L θ x

lemma gLk_eq_lat (L : ℝ) (θ : ℝ → ℝ) (n : ℕ) (v u : FinitePlaneWaveMode n) :
    gLk L θ n v u = gLlat L θ (finitePlaneWaveTransfer n v u) := rfl

lemma gLlat_neg (L : ℝ) (θ : ℝ → ℝ) (x : Lattice3) : gLlat L θ (-x) = gLlat L θ x := by
  classical
  unfold gLlat
  by_cases h : x = (fun _ => 0)
  · have h' : -x = (fun _ => 0) := by rw [h]; funext c; simp
    rw [if_pos h, if_pos h']
  · have h' : -x ≠ (fun _ => 0) := by
      intro h'
      apply h
      funext c
      have := congrFun h' c
      simpa using this
    rw [if_neg h, if_neg h', ghat_neg]

lemma gLlat_conj (hθ : Profile R θ) (L : ℝ) (x : Lattice3) :
    starRingEnd ℂ (gLlat L θ x) = gLlat L θ x := by
  classical
  unfold gLlat
  split_ifs
  · simp
  · exact ghat_conj hθ L x

/-- The nuclear lattice kernel `-Z_ℓ e^{i k·R_ℓ} ĝ_L(k)`, `k` the transfer. -/
noncomputable def gLlatNuc (data : FiniteBONuclearData ν) (L : ℝ) (θ : ℝ → ℝ) (ell : ν)
    (q p : Lattice3) : ℂ :=
  (-(data.charge ell : ℂ)) * (UnitAddTorus.mFourier (latticeSub q p) (data.position ell) *
    gLlat L θ (latticeSub q p))

omit [Fintype ν] in
lemma gLnuc_eq_lattice (data : FiniteBONuclearData ν) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ) (ell : ν)
    (v u : FinitePlaneWaveMode n) :
    gLnuc data L θ n ell v u = gLlatNuc data L θ ell (finitePlaneWaveLatticeIndex n v)
      (finitePlaneWaveLatticeIndex n u) := by
  unfold gLnuc gLlatNuc
  rw [finiteNuclearFourierPhase_transfer, gLk_eq_lat, mul_assoc]
  rfl

/-- The pair lattice kernel: spectators and the total pair momentum conserved, coefficient
`ĝ_L` of the transfer. -/
noncomputable def gLlatPair (i j : Fin eta) (L : ℝ) (θ : ℝ → ℝ)
    (q p : FourierConfig eta Lattice3) : ℂ := by
  classical
  exact if (∀ k : Fin eta, k ≠ i → k ≠ j → q k = p k) ∧ q i + q j = p i + p j then
    gLlat L θ (latticeSub (q i) (p i)) else 0

lemma lift_gLk_eq_lattice (i j : Fin eta) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ) (q p : Cfg eta n) :
    finiteElectronPairLiftKernel i j n (gLk L θ n) q p =
      gLlatPair i j L θ (finiteConfigLatticeIndex eta n q) (finiteConfigLatticeIndex eta n p) := by
  classical
  unfold finiteElectronPairLiftKernel gLlatPair
  by_cases h : finiteElectronPairSliceLabel i j n q = finiteElectronPairSliceLabel i j n p
  · rw [if_pos h, if_pos ((finiteElectronPairSliceLabel_eq_lattice_iff i j n q p).mp h)]
    rfl
  · rw [if_neg h, if_neg (fun hh => h ((finiteElectronPairSliceLabel_eq_lattice_iff i j n q p).mpr
      hh))]

/-- The potential lattice kernel. -/
noncomputable def gLlatPot (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (q p : FourierConfig eta Lattice3) : ℂ :=
  (∑ i : Fin eta, ((-sys.charge i : ℝ) : ℂ) *
    ∑ ell : ν, latticeReferenceConfigurationKernel i (gLlatNuc sys.nuclei L θ ell) q p) +
  ∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
    gLlatPair pair.1.1 pair.1.2 L θ q p

/-- The Hamiltonian lattice kernel. -/
noncomputable def gLlatHam (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (q p : FourierConfig eta Lattice3) : ℂ :=
  coulombLatticeKineticKernel sys L q p + gLlatPot sys L θ q p

lemma gLnucTerms_eq_latticeKernel (data : FiniteBONuclearData ν) (i : Fin eta) (L : ℝ)
    (θ : ℝ → ℝ) (n : ℕ) :
    (∑ ell : ν, referenceKernelConvolutionOperator i (gLnuc data L θ n ell)) =
      finiteCoefficientKernelOperator (fun q p => ∑ ell : ν, latticeReferenceConfigurationKernel i
        (gLlatNuc data L θ ell) (finiteConfigLatticeIndex eta n q)
          (finiteConfigLatticeIndex eta n p)) := by
  classical
  rw [finiteCoefficientKernelOperator_sum]
  apply Finset.sum_congr rfl
  intro ell _
  rw [referenceKernelConvolutionOperator_eq_finiteCoefficientKernelOperator]
  apply congrArg finiteCoefficientKernelOperator
  funext q p
  have hKernel : gLnuc data L θ n ell = (fun v w => gLlatNuc data L θ ell
      (finitePlaneWaveLatticeIndex n v) (finitePlaneWaveLatticeIndex n w)) := by
    funext v w
    exact gLnuc_eq_lattice data L θ n ell v w
  rw [hKernel]
  exact referenceConfigurationKernel_eq_lattice i n _ q p

lemma gLpot_eq_latticeKernel (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ) :
    gLpot sys L θ n = finiteCoefficientKernelOperator (fun q p =>
      gLlatPot sys L θ (finiteConfigLatticeIndex eta n q) (finiteConfigLatticeIndex eta n p)) := by
  classical
  have hN : (∑ a : Fin eta, ((-sys.charge a : ℝ) : ℂ) •
      ∑ l : ν, referenceKernelConvolutionOperator a (gLnuc sys.nuclei L θ n l)) =
      finiteCoefficientKernelOperator (fun q p => ∑ i : Fin eta, ((-sys.charge i : ℝ) : ℂ) *
        ∑ ell : ν, latticeReferenceConfigurationKernel i (gLlatNuc sys.nuclei L θ ell)
          (finiteConfigLatticeIndex eta n q) (finiteConfigLatticeIndex eta n p)) := by
    rw [finiteCoefficientKernelOperator_sum (fun (i : Fin eta) q p =>
      ((-sys.charge i : ℝ) : ℂ) * ∑ ell : ν, latticeReferenceConfigurationKernel i
        (gLlatNuc sys.nuclei L θ ell) (finiteConfigLatticeIndex eta n q)
          (finiteConfigLatticeIndex eta n p))]
    apply Finset.sum_congr rfl
    intro i _
    rw [finiteCoefficientKernelOperator_smul_kernel, gLnucTerms_eq_latticeKernel]
  have hP : (∑ pair : FiniteElectronPair eta,
      ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) •
        finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n)) =
      finiteCoefficientKernelOperator (fun q p => ∑ pair : FiniteElectronPair eta,
        ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
          gLlatPair pair.1.1 pair.1.2 L θ (finiteConfigLatticeIndex eta n q)
            (finiteConfigLatticeIndex eta n p)) := by
    rw [finiteCoefficientKernelOperator_sum (fun (pair : FiniteElectronPair eta) q p =>
      ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
        gLlatPair pair.1.1 pair.1.2 L θ (finiteConfigLatticeIndex eta n q)
          (finiteConfigLatticeIndex eta n p))]
    apply Finset.sum_congr rfl
    intro pair _
    rw [finiteCoefficientKernelOperator_smul_kernel]
    congr 1
    unfold finiteElectronPairKernelOperator
    congr 1
    funext q p
    exact lift_gLk_eq_lattice pair.1.1 pair.1.2 L θ n q p
  unfold gLpot gLlatPot
  rw [hN, hP]
  exact (map_add (finiteCoefficientKernelOperatorAddHom
    (ι := FourierConfig eta (FinitePlaneWaveMode n))) _ _).symm

/-- **Every finite-cube `g_L` Hamiltonian is the compression of one lattice kernel.** -/
theorem gLham_eq_latticeKernel (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ) :
    gLham sys L θ n = finiteCoefficientKernelOperator (fun q p =>
      gLlatHam sys L θ (finiteConfigLatticeIndex eta n q) (finiteConfigLatticeIndex eta n p)) := by
  rw [gLham, diagHamiltonian, finiteCoulombKinetic_eq_latticeKernel, gLpot_eq_latticeKernel]
  exact (map_add (finiteCoefficientKernelOperatorAddHom
    (ι := FourierConfig eta (FinitePlaneWaveMode n))) _ _).symm

/-! ## Exchange symmetry -/

lemma lift_permute (σ : Equiv.Perm (Fin eta)) (i j : Fin eta) (n : ℕ)
    (κ : FinitePlaneWaveMode n → FinitePlaneWaveMode n → ℂ) (q p : Cfg eta n) :
    finiteElectronPairLiftKernel i j n κ (q ∘ σ) (p ∘ σ) =
      finiteElectronPairLiftKernel (σ i) (σ j) n κ q p := by
  classical
  simp only [finiteElectronPairLiftKernel, finiteElectronPairSliceLabel_eq_permute_iff,
    Function.comp_apply]

lemma lift_gLk_swap_particles (L : ℝ) (θ : ℝ → ℝ) (i j : Fin eta) (n : ℕ) (q p : Cfg eta n) :
    finiteElectronPairLiftKernel i j n (gLk L θ n) q p =
      finiteElectronPairLiftKernel j i n (gLk L θ n) q p := by
  classical
  unfold finiteElectronPairLiftKernel
  by_cases h : finiteElectronPairSliceLabel i j n q = finiteElectronPairSliceLabel i j n p
  · have hBack := (finiteElectronPairSliceLabel_eq_swap_iff i j n q p).mp h
    rw [if_pos h, if_pos hBack]
    have hT := finiteElectronPairSliceLabel_opposite_transfers i j n q p h
    rw [gLk_eq_lat, gLk_eq_lat, hT]
    exact gLlat_neg L θ _
  · have hBack : finiteElectronPairSliceLabel j i n q ≠ finiteElectronPairSliceLabel j i n p :=
      fun hb => h ((finiteElectronPairSliceLabel_eq_swap_iff i j n q p).mpr hb)
    rw [if_neg h, if_neg hBack]

/-- The charge-weighted pair kernel. -/
noncomputable def gLpairKernel (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ)
    (q p : Cfg eta n) : ℂ :=
  ∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
    finiteElectronPairLiftKernel pair.1.1 pair.1.2 n (gLk L θ n) q p

omit [Fintype ν] in
lemma gLpairOp_eq_kernel (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ) :
    (∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) •
      finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n)) =
      finiteCoefficientKernelOperator (gLpairKernel sys L θ n) := by
  unfold gLpairKernel
  rw [finiteCoefficientKernelOperator_sum (fun (pair : FiniteElectronPair eta) q p =>
    ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
      finiteElectronPairLiftKernel pair.1.1 pair.1.2 n (gLk L θ n) q p)]
  apply Finset.sum_congr rfl
  intro pair _
  rw [finiteCoefficientKernelOperator_smul_kernel]
  rfl

omit [Fintype ν] in
lemma gLpairKernel_permute (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ)
    (σ : Equiv.Perm (Fin eta)) (hq : ∀ a, sys.charge (σ a) = sys.charge a) (q p : Cfg eta n) :
    gLpairKernel sys L θ n (q ∘ σ) (p ∘ σ) = gLpairKernel sys L θ n q p := by
  classical
  unfold gLpairKernel
  simp_rw [lift_permute]
  have h := sum_finiteElectronPair_permute σ
    (fun i j => ((sys.charge i * sys.charge j : ℝ) : ℂ) *
      finiteElectronPairLiftKernel i j n (gLk L θ n) q p)
    (fun i j => by rw [mul_comm (sys.charge i), lift_gLk_swap_particles])
  simp only [hq] at h
  exact h

lemma gLpot_commute (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ)
    (σ : Equiv.Perm (Fin eta)) (hq : ∀ a, sys.charge (σ a) = sys.charge a) (u : En eta n) :
    gLpot sys L θ n (particlePermutationOperator σ u) =
      particlePermutationOperator σ (gLpot sys L θ n u) := by
  classical
  have hN : (∑ a : Fin eta, ((-sys.charge a : ℝ) : ℂ) •
      ∑ l : ν, referenceKernelConvolutionOperator a (gLnuc sys.nuclei L θ n l))
        (particlePermutationOperator σ u) =
      particlePermutationOperator σ ((∑ a : Fin eta, ((-sys.charge a : ℝ) : ℂ) •
        ∑ l : ν, referenceKernelConvolutionOperator a (gLnuc sys.nuclei L θ n l)) u) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    symm
    apply Fintype.sum_equiv σ
    intro i
    rw [hq i]
    congr 1
    apply Finset.sum_congr rfl
    intro ell _
    exact (referenceKernelConvolutionOperator_particlePermutation_covariant σ i _ u).symm
  have hP : (∑ pair : FiniteElectronPair eta,
      ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) •
        finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n))
        (particlePermutationOperator σ u) =
      particlePermutationOperator σ ((∑ pair : FiniteElectronPair eta,
        ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) •
          finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n)) u) := by
    rw [gLpairOp_eq_kernel]
    exact finiteCoefficientKernelOperator_particlePermutation_commute σ _
      (gLpairKernel_permute sys L θ n σ hq) u
  unfold gLpot
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add, hN, hP]

lemma gLham_particlePermutation_commute (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (n : ℕ) (σ : Equiv.Perm (Fin eta)) (hm : ∀ a, sys.mass (σ a) = sys.mass a)
    (hq : ∀ a, sys.charge (σ a) = sys.charge a) (u : En eta n) :
    gLham sys L θ n (particlePermutationOperator σ u) =
      particlePermutationOperator σ (gLham sys L θ n u) := by
  unfold gLham diagHamiltonian
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    map_add, map_smul,
    diagOperator_particlePermutation_commute _ σ (massKineticSymbol_permute _ _ σ hm),
    gLpot_commute sys L θ n σ hq]

/-- **The `g_L` Hamiltonian preserves every exchange sector of an admissible labelling.** -/
theorem gLham_preserves_sector (sys : CoulombSystem eta ν) {sgn : Fin eta → ℂ}
    {lab : Fin eta → ℕ} (hlab : sys.IsAdmissible lab) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ)
    (u : En eta n) (hS : IsSectorVector sgn lab u) :
    IsSectorVector sgn lab (gLham sys L θ n u) := by
  apply isSectorVector_map_of_swap_commute _ _ u hS
  intro i j _ hl v
  have hs := hlab i j hl
  exact gLham_particlePermutation_commute sys L θ n (Equiv.swap i j) (sys.mass_swap hs)
    (sys.charge_swap hs) v

/-! ## Finite ground states -/

/-- Sector ground states exist on every cube with at least `η` modes. -/
theorem gL_exists_sector_ground (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) (hθ : Profile R θ) (L : ℝ) (n : ℕ)
    (hEnough : eta ≤ Fintype.card (FinitePlaneWaveMode n)) :
    ∃ E : ℝ, ∃ u : En eta n, IsSectorVector sys.sign lab u ∧ ‖u‖ = 1 ∧
      gLham sys L θ n u = (E : ℂ) • u ∧
      IsSectorGroundEnergy sys.sign lab (gLham sys L θ n) E := by
  have hInvariant : ∀ u ∈ sectorSubmodule eta sys.sign lab (FinitePlaneWaveMode n),
      gLham sys L θ n u ∈ sectorSubmodule eta sys.sign lab (FinitePlaneWaveMode n) :=
    fun u hu => gLham_preserves_sector sys hlab L θ n u hu
  have hNonzero : ∃ u : En eta n,
      u ∈ sectorSubmodule eta sys.sign lab (FinitePlaneWaveMode n) ∧ u ≠ 0 := by
    obtain ⟨u, hu, hu0, -⟩ := sys.exists_nonzero_sectorVector_supported_of_card hlab
      (Finset.univ : Finset (FinitePlaneWaveMode n)) (by simpa using hEnough)
    exact ⟨u, hu, hu0⟩
  obtain ⟨E, u, hu, hNorm, hEig, hLower⟩ := exists_ground_eigenpair_on_invariant_submodule
    (gLham sys L θ n) (gLham_isSymmetric hθ sys L n) _ hInvariant hNonzero
  exact ⟨E, u, hu, hNorm, hEig, fun v hv => hLower v hv⟩

/-! ## Transport between cubes -/

section Transport

variable {M n : ℕ}

/-- The inclusion of the modes of the cube `M` in the cube `n ≥ M`, by lattice index. -/
noncomputable def modeIncl (hMn : M ≤ n) (v : FinitePlaneWaveMode M) : FinitePlaneWaveMode n :=
  finitePlaneWaveModeOfBoundedLattice n (finitePlaneWaveLatticeIndex M v) (fun c => by
    obtain ⟨h1, h2⟩ := finitePlaneWaveLatticeIndex_coord_bounds M v c
    have hMn' : ((M : ℕ) : ℤ) ≤ ((n : ℕ) : ℤ) := by exact_mod_cast hMn
    exact ⟨by omega, by omega⟩)

lemma idx_modeIncl (hMn : M ≤ n) (v : FinitePlaneWaveMode M) :
    finitePlaneWaveLatticeIndex n (modeIncl hMn v) = finitePlaneWaveLatticeIndex M v :=
  finitePlaneWaveLatticeIndex_modeOfBoundedLattice n _ _

lemma modeIncl_injective (hMn : M ≤ n) : Function.Injective (modeIncl hMn) := by
  intro v w h
  apply finitePlaneWaveLatticeIndex_injective M
  rw [← idx_modeIncl hMn v, ← idx_modeIncl hMn w, h]

/-- The inclusion of configurations. -/
noncomputable def cfgIncl (hMn : M ≤ n) (p : Cfg eta M) : Cfg eta n :=
  fun i => modeIncl hMn (p i)

lemma idx_cfgIncl (hMn : M ≤ n) (p : Cfg eta M) :
    finiteConfigLatticeIndex eta n (cfgIncl hMn p) = finiteConfigLatticeIndex eta M p := by
  funext i
  exact idx_modeIncl hMn (p i)

lemma cfgIncl_injective (hMn : M ≤ n) : Function.Injective (cfgIncl (eta := eta) hMn) := by
  intro p q h
  funext i
  exact modeIncl_injective hMn (congrFun h i)

lemma cfgIncl_swap (hMn : M ≤ n) (i j : Fin eta) (p : Cfg eta M) :
    cfgIncl hMn (swapConfig i j p) = swapConfig i j (cfgIncl hMn p) := by
  funext k
  rfl

lemma swapConfig_swapConfig {μ : Type*} (i j : Fin eta) (p : FourierConfig eta μ) :
    swapConfig i j (swapConfig i j p) = p := by
  funext k
  simp [swapConfig, Equiv.swap_apply_self]

/-- **Transport** of a coefficient vector from the cube `M` to the cube `n ≥ M`. -/
noncomputable def transport (hMn : M ≤ n) (u : En eta M) : En eta n :=
  WithLp.toLp 2 (Function.extend (cfgIncl hMn) (fun p => u.ofLp p) 0)

lemma transport_apply_incl (hMn : M ≤ n) (u : En eta M) (p : Cfg eta M) :
    (transport hMn u).ofLp (cfgIncl hMn p) = u.ofLp p :=
  (cfgIncl_injective hMn).extend_apply _ _ p

lemma transport_apply_not_mem (hMn : M ≤ n) (u : En eta M) (q : Cfg eta n)
    (hq : ¬ ∃ p, cfgIncl hMn p = q) : (transport hMn u).ofLp q = 0 := by
  change Function.extend (cfgIncl hMn) (fun p => u.ofLp p) 0 q = 0
  rw [Function.extend_apply' _ _ _ hq]
  rfl

lemma transport_norm (hMn : M ≤ n) (u : En eta M) : ‖transport hMn u‖ = ‖u‖ := by
  have h : ‖transport hMn u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    symm
    apply Fintype.sum_of_injective (cfgIncl hMn) (cfgIncl_injective hMn)
    · intro q hq
      rw [transport_apply_not_mem hMn u q (by simpa [Set.mem_range] using hq)]
      simp
    · intro p
      rw [transport_apply_incl]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

lemma transport_isSector (hMn : M ≤ n) {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ} (u : En eta M)
    (hu : IsSectorVector sgn lab u) : IsSectorVector sgn lab (transport hMn u) := by
  intro i j hij hl q
  change (transport hMn u).ofLp (swapConfig i j q) = sgn i * (transport hMn u).ofLp q
  by_cases hq : ∃ p, cfgIncl hMn p = q
  · obtain ⟨p, rfl⟩ := hq
    rw [← cfgIncl_swap, transport_apply_incl, transport_apply_incl]
    exact hu i j hij hl p
  · have hq' : ¬ ∃ p, cfgIncl hMn p = swapConfig i j q := by
      rintro ⟨p, hp⟩
      apply hq
      refine ⟨swapConfig i j p, ?_⟩
      rw [cfgIncl_swap, hp, swapConfig_swapConfig]
    rw [transport_apply_not_mem hMn u _ hq', transport_apply_not_mem hMn u _ hq, mul_zero]

/-- The quadratic form of a kernel operator in coordinates. -/
lemma inner_fcko_eq {k : ℕ} (K : Cfg eta k → Cfg eta k → ℂ) (w : En eta k) :
    inner ℂ w (finiteCoefficientKernelOperator K w) =
      ∑ q, ∑ p, starRingEnd ℂ (w.ofLp q) * (w.ofLp p * K q p) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [RCLike.inner_apply', finiteCoefficientKernelOperator_apply, Finset.mul_sum]

/-- **Transport preserves the quadratic form of the `g_L` Hamiltonian.** -/
theorem transport_form (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ) (hMn : M ≤ n)
    (u : En eta M) :
    inner ℂ (transport hMn u) (gLham sys L θ n (transport hMn u)) =
      inner ℂ u (gLham sys L θ M u) := by
  rw [gLham_eq_latticeKernel, gLham_eq_latticeKernel, inner_fcko_eq, inner_fcko_eq]
  symm
  apply Fintype.sum_of_injective (cfgIncl hMn) (cfgIncl_injective hMn)
  · intro q hq
    rw [transport_apply_not_mem hMn u q (by simpa [Set.mem_range] using hq)]
    simp
  · intro q
    rw [transport_apply_incl]
    apply Fintype.sum_of_injective (cfgIncl hMn) (cfgIncl_injective hMn)
    · intro p hp
      rw [transport_apply_not_mem hMn u p (by simpa [Set.mem_range] using hp)]
      simp
    · intro p
      rw [transport_apply_incl, idx_cfgIncl, idx_cfgIncl]

lemma transport_isCubicRetained (L : ℝ) (hL : 0 < L) (hMn : M ≤ n) (u : En eta M) :
    IsCubicRetainedVector eta ((2 * Real.pi / L) * M) (2 * Real.pi / L) n (transport hMn u) := by
  intro q ⟨i, d, hq⟩
  apply transport_apply_not_mem
  rintro ⟨p, rfl⟩
  have hidx : finitePlaneWaveLatticeIndex n (cfgIncl hMn p i) =
      finitePlaneWaveLatticeIndex M (p i) := idx_modeIncl hMn (p i)
  rw [hidx] at hq
  obtain ⟨h1, h2⟩ := finitePlaneWaveLatticeIndex_coord_bounds M (p i) d
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hb : |((finitePlaneWaveLatticeIndex M (p i) d : ℤ) : ℝ)| ≤ (M : ℝ) := by
    rw [abs_le]
    constructor
    · have : (-((M : ℕ) : ℤ) : ℝ) ≤ ((finitePlaneWaveLatticeIndex M (p i) d : ℤ) : ℝ) := by
        exact_mod_cast h1
      push_cast at this
      linarith
    · exact_mod_cast h2
  rw [abs_mul, abs_of_pos hg] at hq
  have := mul_le_mul_of_nonneg_left hb hg.le
  linarith

/-- Every cubic-retained vector of the cube `n` at cutoff `(2π/L) M` is transported from the cube
`M`, with the same sector. -/
lemma exists_transport_of_cubic (L : ℝ) (hL : 0 < L) (hMn : M ≤ n) {sgn : Fin eta → ℂ}
    {lab : Fin eta → ℕ} (v : En eta n)
    (hv : IsCubicRetainedVector eta ((2 * Real.pi / L) * M) (2 * Real.pi / L) n v)
    (hS : IsSectorVector sgn lab v) :
    ∃ u : En eta M, IsSectorVector sgn lab u ∧ transport hMn u = v := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  refine ⟨WithLp.toLp 2 (fun p => v.ofLp (cfgIncl hMn p)), ?_, ?_⟩
  · intro i j hij hl p
    change v.ofLp (cfgIncl hMn (swapConfig i j p)) = sgn i * v.ofLp (cfgIncl hMn p)
    rw [cfgIncl_swap]
    exact hS i j hij hl _
  · ext q
    by_cases hq : ∃ p, cfgIncl hMn p = q
    · obtain ⟨p, rfl⟩ := hq
      rw [transport_apply_incl]
    · rw [transport_apply_not_mem hMn _ q hq]
      symm
      apply hv q
      by_contra hcon
      push Not at hcon
      apply hq
      have hbd : ∀ i c, -((M : ℕ) : ℤ) ≤ finitePlaneWaveLatticeIndex n (q i) c ∧
          finitePlaneWaveLatticeIndex n (q i) c ≤ ((M : ℕ) : ℤ) := by
        intro i c
        have h := hcon i c
        rw [abs_mul, abs_of_pos hg] at h
        have h' : |((finitePlaneWaveLatticeIndex n (q i) c : ℤ) : ℝ)| ≤ (M : ℝ) :=
          le_of_mul_le_mul_left h hg
        rw [abs_le] at h'
        constructor
        · have : (-(M : ℝ)) ≤ ((finitePlaneWaveLatticeIndex n (q i) c : ℤ) : ℝ) := h'.1
          exact_mod_cast this
        · exact_mod_cast h'.2
      refine ⟨fun i => finitePlaneWaveModeOfBoundedLattice M
        (finitePlaneWaveLatticeIndex n (q i)) (hbd i), ?_⟩
      funext i
      apply finitePlaneWaveLatticeIndex_injective n
      change finitePlaneWaveLatticeIndex n (modeIncl hMn _) = _
      rw [idx_modeIncl, finitePlaneWaveLatticeIndex_modeOfBoundedLattice]

/-- The form of a normalised eigenvector is its eigenvalue. -/
lemma form_of_eigen {k : ℕ} (H : En eta k →ₗ[ℂ] En eta k) (u : En eta k) (E : ℝ)
    (hn : ‖u‖ = 1) (hEig : H u = (E : ℂ) • u) : (inner ℂ u (H u)).re = E := by
  rw [hEig, inner_smul_right, inner_self_eq_norm_sq_to_K, hn]
  simp

/-- A sector ground state of the cube `M` gives the cubic Galerkin ground energy at cutoff
`(2π/L) M` on every cube `n ≥ M`. -/
theorem cube_ground_to_cubic (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ) (L : ℝ)
    (hL : 0 < L) (θ : ℝ → ℝ) (hMn : M ≤ n) (EM : ℝ) (uM : En eta M)
    (hS : IsSectorVector sys.sign lab uM) (hn : ‖uM‖ = 1)
    (hEig : gLham sys L θ M uM = (EM : ℂ) • uM)
    (hG : IsSectorGroundEnergy sys.sign lab (gLham sys L θ M) EM) :
    IsSectorCubicGalerkinGroundEnergy eta sys.sign lab ((2 * Real.pi / L) * M) (2 * Real.pi / L)
      n (gLham sys L θ n) EM := by
  constructor
  · intro v hv hcub
    obtain ⟨u, hu, rfl⟩ := exists_transport_of_cubic L hL hMn v hcub hv
    rw [transport_norm, transport_form]
    exact hG u hu
  · refine ⟨transport hMn uM, transport_isSector hMn uM hS,
      transport_isCubicRetained L hL hMn uM, by rw [transport_norm, hn], ?_⟩
    rw [transport_form]
    exact form_of_eigen _ uM EM hn hEig

end Transport

/-! ## The torus ground energy -/

/-- **The torus ground energy** `E_L` of the `g_L` Hamiltonian in the sector `(sign, lab)`: the
infimum of its quadratic form over the normalised finite Fourier states (trigonometric
polynomials) of the sector. -/
def IsGLTorusGroundEnergy (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ) (L : ℝ)
    (θ : ℝ → ℝ) (E : ℝ) : Prop :=
  (∀ (n : ℕ) (u : En eta n), IsSectorVector sys.sign lab u →
    E * ‖u‖ ^ 2 ≤ (inner ℂ u (gLham sys L θ n u)).re) ∧
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (u : En eta n), IsSectorVector sys.sign lab u ∧ ‖u‖ = 1 ∧
    (inner ℂ u (gLham sys L θ n u)).re < E + ε

/-- **The torus ground energy exists.** -/
theorem exists_gLTorusGroundEnergy (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ}
    (hlab : sys.IsAdmissible lab) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E := by
  classical
  have hex : ∀ n : ℕ, ∃ E : ℝ, ∃ u : En eta (eta + n), IsSectorVector sys.sign lab u ∧
      ‖u‖ = 1 ∧ gLham sys L θ (eta + n) u = (E : ℂ) • u ∧
      IsSectorGroundEnergy sys.sign lab (gLham sys L θ (eta + n)) E := fun n =>
    gL_exists_sector_ground sys lab hlab hθ L (eta + n)
      (enough_finitePlaneWaveModes_of_particle_le_count eta (eta + n) (by omega))
  choose En u hS hn hEig hG using hex
  -- the lower bound `-(B_m² + 1/4)`
  set B := sys.massCouplingWeight * ((1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit
    (2 * Real.pi / L)) with hBdef
  have hB0 : 0 ≤ B := mul_nonneg sys.massCouplingWeight_nonneg
    (mul_nonneg (by linarith [hθ.tv_nonneg]) (tB_nonneg _ _ _))
  have hlow : ∀ n, -(B ^ 2 + 1 / 4) ≤ En n := by
    intro n
    have hmpos : ∀ a, 0 < sys.mass a := fun a => sys.mass_pos a
    have h := diagHamiltonian_form_lower_bound_of_weightedBound
      (massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) (eta + n)))
      (fun p => massKineticSymbol_nonneg hmpos _ p) (gLpot sys L θ (eta + n)) hB0
      (gLpot_massBound sys hL hθ Hunit hPeriodic (eta + n)) (u n)
    have hf := form_of_eigen _ (u n) (En n) (hn n) (hEig n)
    rw [hn n] at h
    change -(B ^ 2 + 1 / 4) * 1 ^ 2 ≤ (inner ℂ (u n) (gLham sys L θ (eta + n) (u n))).re at h
    rw [hf] at h
    linarith
  have hbdd : BddBelow (Set.range En) := ⟨-(B ^ 2 + 1 / 4), by
    rintro _ ⟨n, rfl⟩; exact hlow n⟩
  refine ⟨⨅ n, En n, ?_, ?_⟩
  · intro k v hv
    have hk : k ≤ eta + k := by omega
    have h1 := hG k (transport hk v) (transport_isSector hk v hv)
    rw [transport_norm, transport_form] at h1
    have h2 : (⨅ n, En n) ≤ En k := ciInf_le hbdd k
    have h3 : (⨅ n, En n) * ‖v‖ ^ 2 ≤ En k * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    linarith
  · intro ε hε
    obtain ⟨n, hlt⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (⨅ n, En n) hε)
    exact ⟨eta + n, u n, hS n, hn n, by rw [form_of_eigen _ (u n) (En n) (hn n) (hEig n)]; exact hlt⟩

/-- The cube ground energies converge to the torus ground energy. -/
theorem tendsto_cube_ground (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} {L : ℝ}
    {θ : ℝ → ℝ} {E : ℝ} (hE : IsGLTorusGroundEnergy sys lab L θ E) (h : ℕ → ℕ)
    (hh : Tendsto h atTop atTop) (energy : ℕ → ℝ) (u : (n : ℕ) → En eta (h n))
    (hS : ∀ n, IsSectorVector sys.sign lab (u n)) (hn : ∀ n, ‖u n‖ = 1)
    (hEig : ∀ n, gLham sys L θ (h n) (u n) = (energy n : ℂ) • u n)
    (hG : ∀ n, IsSectorGroundEnergy sys.sign lab (gLham sys L θ (h n)) (energy n)) :
    Tendsto energy atTop (𝓝 E) := by
  have hge : ∀ n, E ≤ energy n := by
    intro n
    have h1 := hE.1 (h n) (u n) (hS n)
    rw [hn n, form_of_eigen _ (u n) (energy n) (hn n) (hEig n)] at h1
    simpa using h1
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, v, hv, hvn, hvlt⟩ := hE.2 ε hε
  obtain ⟨N, hN⟩ := (tendsto_atTop.mp hh) k |> Filter.eventually_atTop.mp
  refine ⟨N, fun n hnN => ?_⟩
  have hk : k ≤ h n := hN n hnN
  have h1 := hG n (transport hk v) (transport_isSector hk v hv)
  rw [transport_norm, transport_form, hvn] at h1
  have h2 := hge n
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

/-! ## The cubic error -/

/-- **The cubic Galerkin error for the torus ground energy.** For a cube `M` with
`K = (2π/L) M` large (`4 m̄ (|E_L| + 1) ≤ K²`, `32 S₂ C_W² ≤ K⁵`), the sector ground energy `E_M`
of the cube satisfies `0 ≤ E_M - E_L` and `K³ (E_M - E_L) ≤ 64 (1/2 + C_pot + |E_L|) S₁ S₂ C_W²`,
`C_W = gLtailConst` at the energy budget `|E_L| + 1`. -/
theorem gL_cubic_error (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ}
    (hlab : sys.IsAdmissible lab) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {E : ℝ}
    (hE : IsGLTorusGroundEnergy sys lab L θ E) (M : ℕ)
    (hK1 : 1 ≤ (2 * Real.pi / L) * M)
    (hAbsorb : 4 * sys.maxMass * (|E| + 1) ≤ ((2 * Real.pi / L) * M) ^ 2)
    (hLargeK : 32 * (∑ a, sys.mass a ^ 2) * (gLtailConst sys L (tv R θ) Hunit (|E| + 1)) ^ 2 ≤
      ((2 * Real.pi / L) * M) ^ 5)
    (EM : ℝ) (uM : En eta M) (hS : IsSectorVector sys.sign lab uM) (hn : ‖uM‖ = 1)
    (hEig : gLham sys L θ M uM = (EM : ℂ) • uM)
    (hG : IsSectorGroundEnergy sys.sign lab (gLham sys L θ M) EM) :
    0 ≤ EM - E ∧ ((2 * Real.pi / L) * M) ^ 3 * (EM - E) ≤
      64 * ((1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit + |E|) * (∑ a, sys.mass a) *
        (∑ a, sys.mass a ^ 2) * (gLtailConst sys L (tv R θ) Hunit (|E| + 1)) ^ 2 := by
  classical
  set K := (2 * Real.pi / L) * M with hKdef
  set h : ℕ → ℕ := fun n => M + eta + n with hhdef
  have hh : Tendsto h atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    simp only [hhdef]
    omega
  have hex : ∀ n : ℕ, ∃ E' : ℝ, ∃ coeff : FourierConfig eta (FinitePlaneWaveMode (h n)) → ℂ,
      IsSectorCoeff sys.sign lab coeff ∧ (∑ p, coeffMass coeff p) = 1 ∧
      gLham sys L θ (h n) (fullCoeffVector coeff) = (E' : ℂ) • fullCoeffVector coeff ∧
      IsSectorGroundEnergy sys.sign lab (gLham sys L θ (h n)) E' := by
    intro n
    obtain ⟨E', u, hSu, hnu, hEu, hGu⟩ := gL_exists_sector_ground sys lab hlab hθ L (h n)
      (enough_finitePlaneWaveModes_of_particle_le_count eta (h n) (by simp only [hhdef]; omega))
    refine ⟨E', (fun p => u.ofLp p), hSu, ?_, hEu, hGu⟩
    change (∑ p, ‖u.ofLp p‖ ^ 2) = 1
    rw [← EuclideanSpace.norm_sq_eq, hnu, one_pow]
  choose energy coeff hSc hMass hEigc hGc using hex
  have hnorm : ∀ n, ‖fullCoeffVector (coeff n)‖ = 1 := fun n =>
    fullCoeffVector_norm_eq_one_of_mass (coeff n) (hMass n)
  have hconv : Tendsto energy atTop (𝓝 E) :=
    tendsto_cube_ground sys hE h hh energy (fun n => fullCoeffVector (coeff n))
      (fun n => fullCoeffVector_isSector (coeff n) (hSc n)) hnorm hEigc hGc
  have hge : ∀ n, E ≤ energy n := by
    intro n
    have h1 := hE.1 (h n) (fullCoeffVector (coeff n))
      (fullCoeffVector_isSector (coeff n) (hSc n))
    rw [hnorm n, form_of_eigen _ _ (energy n) (hnorm n) (hEigc n)] at h1
    simpa using h1
  have hnear : ∀ᶠ n in atTop, energy n ≤ E + 1 :=
    (hconv.eventually (Iic_mem_nhds (by linarith : E < E + 1)))
  have hFinite : ∀ᶠ n in atTop, 0 ≤ EM - energy n ∧
      K ^ 3 * (EM - energy n) ≤ (((1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit) + |energy n|) *
        (64 * (∑ a, sys.mass a) * (∑ a, sys.mass a ^ 2) *
          (gLtailConst sys L (tv R θ) Hunit (|E| + 1)) ^ 2) := by
    filter_upwards [hnear] with n hnE
    have hEn : |energy n| ≤ |E| + 1 := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le E, hge n]
      · linarith [le_abs_self E]
    have hMh : M ≤ h n := by simp only [hhdef]; omega
    have hAbsN : 4 * sys.maxMass * |energy n| ≤ K ^ 2 := by
      have hM0 : 0 ≤ 4 * sys.maxMass := by have := sys.one_le_maxMass; positivity
      have := mul_le_mul_of_nonneg_left hEn hM0
      linarith
    have hGal := cube_ground_to_cubic sys lab L hL θ hMh EM uM hS hn hEig hG
    have hb := gL_cubic_energy_bound sys hL hθ Hunit hPeriodic (h n) K (energy n) EM (|E| + 1)
      (coeff n) hK1 (by positivity) hEn hAbsN hLargeK (hSc n) (hMass n) (hEigc n) (hGc n) hGal
    refine ⟨hb.1, hb.2.trans (le_of_eq ?_)⟩
    ring
  have hLim := cubic_energy_bound_passes_to_limit_factor K E EM
    ((1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit)
    (64 * (∑ a, sys.mass a) * (∑ a, sys.mass a ^ 2) *
      (gLtailConst sys L (tv R θ) Hunit (|E| + 1)) ^ 2) energy hconv hFinite
  refine ⟨hLim.1, hLim.2.trans (le_of_eq ?_)⟩
  ring

/-- The cubic error constant `64 (1/2 + C_pot + |E|) S₁ S₂ C_W²` at the explicit periodic Hardy
constant (`V` the total variation of `θ`, `E` the torus ground energy). -/
noncomputable def gLCubicConst (sys : CoulombSystem eta ν) (L V E : ℝ) : ℝ :=
  64 * ((1 / 2 : ℝ) + gLformConst sys L V molecularCanonicalUnitHardyConstant + |E|) *
    (∑ a, sys.mass a) * (∑ a, sys.mass a ^ 2) *
      (gLtailConst sys L V molecularCanonicalUnitHardyConstant (|E| + 1)) ^ 2

lemma gLCubicConst_nonneg (sys : CoulombSystem eta ν) (L : ℝ) {V : ℝ} (hV : 0 ≤ V) (E : ℝ) :
    0 ≤ gLCubicConst sys L V E := by
  unfold gLCubicConst
  have h1 := gLformConst_nonneg sys L hV molecularCanonicalUnitHardyConstant
  have h2 : 0 ≤ ∑ a, sys.mass a := Finset.sum_nonneg fun a _ => (sys.mass_pos a).le
  have h3 : 0 ≤ ∑ a, sys.mass a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  positivity

/-- An explicit cube threshold for the cubic error (the release's
`coulombExplicitCubicThreshold` at the `g_L` budgets). -/
noncomputable def gLCubicThreshold (sys : CoulombSystem eta ν) (L V E : ℝ) : ℕ :=
  coulombExplicitCubicThreshold eta (2 * Real.pi / L) sys.maxMass (∑ a, sys.mass a ^ 2) E
    (gLtailConst sys L V molecularCanonicalUnitHardyConstant (|E| + 1))

/-- **The cubic Galerkin error for the `g_L` torus ground energy, with explicit constants.**
The torus ground energy `E_L` exists, and for every cube `M` above an explicit threshold the
sector ground energy `E_M` of the cube (the cubic Galerkin energy at cutoff `K = (2π/L) M`)
satisfies `0 ≤ E_M - E_L ≤ C / K³`. -/
theorem gL_sector_cubic_error (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E ∧
      ∀ M : ℕ, gLCubicThreshold sys L (tv R θ) E ≤ M →
        ∃ EM : ℝ, ∃ uM : En eta M, IsSectorVector sys.sign lab uM ∧ ‖uM‖ = 1 ∧
          gLham sys L θ M uM = (EM : ℂ) • uM ∧
          IsSectorGroundEnergy sys.sign lab (gLham sys L θ M) EM ∧
          0 ≤ EM - E ∧ EM - E ≤ gLCubicConst sys L (tv R θ) E / ((2 * Real.pi / L) * M) ^ 3 := by
  obtain ⟨E, hE⟩ := exists_gLTorusGroundEnergy sys hlab hL hθ molecularCanonicalUnitHardyConstant
    canonicalPeriodicCoulombHardyBound_explicit
  refine ⟨E, hE, fun M hM => ?_⟩
  have hg : 0 < 2 * Real.pi / L := by positivity
  obtain ⟨_hm1, hCount, hK, _hGrid, hEnergyA, hTailA⟩ :=
    coulombExplicitCubicThreshold_admissible eta (2 * Real.pi / L) sys.maxMass
      (∑ a, sys.mass a ^ 2) E (gLtailConst sys L (tv R θ) molecularCanonicalUnitHardyConstant
        (|E| + 1)) hg sys.maxMass_pos.le (Finset.sum_nonneg fun a _ => sq_nonneg _) M hM
  obtain ⟨EM, uM, hS, hn, hEig, hG⟩ := gL_exists_sector_ground sys lab hlab hθ L M
    (by rw [finitePlaneWaveMode_card]; exact hCount)
  have hb := gL_cubic_error sys hlab hL hθ molecularCanonicalUnitHardyConstant
    canonicalPeriodicCoulombHardyBound_explicit hE M hK hEnergyA hTailA EM uM hS hn hEig hG
  refine ⟨EM, uM, hS, hn, hEig, hG, hb.1, ?_⟩
  have hKpos : 0 < (2 * Real.pi / L) * M := by linarith
  rw [le_div_iff₀ (pow_pos hKpos 3), mul_comm]
  exact hb.2

end FreeBoundary
