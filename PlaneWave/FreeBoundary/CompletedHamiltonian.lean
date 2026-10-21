import PlaneWave.FreeBoundary.PositionPotential

/-!
# `app:free`, part 9: the completed `g_L` Hamiltonian on `H²` and the variational bound for
`C²` torus states

Following the release's construction for the Coulomb kernel (milestones 147b, 148a, 148b):

* `exists_gLFourierH2Operator`: the `g_L` Hamiltonian as a bounded operator from the weighted
  `H²` coordinates to `ℓ²`, given on every Fourier truncation by the lattice kernel `gLlatHam`;
* `gLFourierDomainEmbedding_inner_eq`: on every finite cube it has the form of `gLham`;
* **`gL_variational_H2`**: the torus ground energy `E_L` (`PlaneWave.FreeBoundary.TorusGroundEnergy`, the infimum over
  trigonometric polynomials) is a lower bound of the form on the whole `H²` domain of the sector;
* `gLPositionPotentialH2_pointwise`: in position space its potential part is multiplication by the
  function `gLFourierPotential` of `PlaneWave.FreeBoundary.PositionPotential`;
* **`gL_variational_C2`**: for every `C²` periodic state `φ` of the sector and every `L²` function
  `p = V φ` (`V` the `g_L` multiplication function, zero mode removed),
  `E_L ‖φ‖² ≤ Re⟨φ, K φ⟩ + Re⟨φ, p⟩`, with `K` the classical kinetic operator
  `-(1/(2L²)) Σ_a m_a⁻¹ Δ_a` (the release's `coulombPositionContDiffKinetic`).
-/

set_option autoImplicit false

open MeasureTheory Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin FSNormal
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

local instance unitAddCircleMeasureSpaceFB9 : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

local instance unitAddCircleProbabilityMeasureFB9 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  instIsProbabilityMeasureUnitAddCircleVolume

local instance molecularTorusFiniteMeasureFB9 {eta : ℕ} :
    IsFiniteMeasure (volume : Measure (MolecularPositionTorus eta)) := by
  infer_instance

variable {eta : ℕ} {ν : Type} [Fintype ν] {R : ℝ} {θ : ℝ → ℝ}

/-! ## Finite `H²` bounds -/

lemma gLham_fullCoeff_apply_latticeKernel (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (count : ℕ) (coeff : FourierConfig eta (FinitePlaneWaveMode count) → ℂ)
    (q : FourierConfig eta (FinitePlaneWaveMode count)) :
    (gLham sys L θ count (fullCoeffVector coeff)).ofLp q =
      ∑ p, coeff p * gLlatHam sys L θ
        (finiteConfigLatticeIndex eta count q) (finiteConfigLatticeIndex eta count p) := by
  rw [gLham_eq_latticeKernel]
  rfl

theorem gLham_norm_le_sqrt_fullH2Sq (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (count : ℕ) (coeff : FourierConfig eta (FinitePlaneWaveMode count) → ℂ) :
    ‖gLham sys L θ count (fullCoeffVector coeff)‖ ≤
      ((1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit) *
        Real.sqrt (fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) count) coeff) :=
  diagHamiltonian_norm_le_sqrt_fullH2Sq _ _
    (massKineticSymbol_nonneg (fun a => sys.mass_pos a) _)
    (massKineticSymbol_le_boKineticSymbol sys.one_le_mass _) coeff _
    (gLformConst_nonneg sys L hθ.tv_nonneg Hunit) (gLpot_h1Bound sys hL hθ Hunit hPeriodic count)

theorem gLham_H2_extract_uniform (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (u : MolecularFourierH2 eta) (count : ℕ) :
    ‖gLham sys L θ count
      (fullCoeffVector (finiteFourierCoeffExtract count
        (molecularH2Coeff (2 * Real.pi / L) u)))‖ ≤
      ((1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit) * ‖u‖ := by
  have hC : 0 ≤ (1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit := by
    linarith only [gLformConst_nonneg sys L hθ.tv_nonneg Hunit]
  exact (gLham_norm_le_sqrt_fullH2Sq sys hL hθ Hunit hPeriodic count _).trans
    (mul_le_mul_of_nonneg_left (sqrt_fullH2Sq_extract_le_norm (2 * Real.pi / L) count u) hC)


/-! ## The core action and the completed operator -/

/-- The finite Hamiltonian applied to a fixed finite Fourier input. -/
def gLCoreOutput (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (inputCutoff : ℕ) (u : MolecularFourierH2 eta) (count : ℕ) :
    EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode count)) :=
  gLham sys L θ count
    (fullCoeffVector (finiteFourierCoeffExtract count
      (molecularH2Coeff (2 * Real.pi / L) (molecularH2Truncate inputCutoff u))))

def gLCoreOutputLp (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (inputCutoff : ℕ) (u : MolecularFourierH2 eta) (count : ℕ) :
    lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
  finiteFourierLpEmbed eta count (gLCoreOutput sys L θ inputCutoff u count).ofLp

lemma fourierKernelFiniteOutput_gL_eq (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (inputCutoff : ℕ) (u : MolecularFourierH2 eta) (count : ℕ) :
    fourierKernelFiniteOutput (2 * Real.pi / L)
      (gLlatHam sys L θ) inputCutoff u count =
      gLCoreOutput sys L θ inputCutoff u count := by
  ext q
  change (∑ p : FourierConfig eta (FinitePlaneWaveMode count),
    molecularH2Coeff (2 * Real.pi / L) (molecularH2Truncate inputCutoff u)
      (finiteConfigLatticeIndex eta count p) *
      gLlatHam sys L θ
        (finiteConfigLatticeIndex eta count q) (finiteConfigLatticeIndex eta count p)) =
    (gLham sys L θ count
      (fullCoeffVector (finiteFourierCoeffExtract count
        (molecularH2Coeff (2 * Real.pi / L) (molecularH2Truncate inputCutoff u))))).ofLp q
  exact (gLham_fullCoeff_apply_latticeKernel sys L θ count _ q).symm

lemma gLCoreOutputLp_eq_truncate (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (inputCutoff : ℕ) (u : MolecularFourierH2 eta)
    (v : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hv : ∀ q, v q = fourierCubeKernelAction (2 * Real.pi / L)
      (gLlatHam sys L θ) inputCutoff u q)
    (count : ℕ) (hCount : inputCutoff ≤ count) :
    gLCoreOutputLp sys L θ inputCutoff u count = molecularH2Truncate count v := by
  unfold gLCoreOutputLp
  rw [← fourierKernelFiniteOutput_gL_eq]
  exact fourierKernelFiniteOutput_embed_eq_truncate _ _ inputCutoff u v hv count hCount

/-- The full infinite output on each finite Fourier input, with the physical bound. -/
theorem exists_gLFourierCoreAction (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (inputCutoff : ℕ) (u : MolecularFourierH2 eta) :
    ∃ v : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2,
      (∀ q, v q = fourierCubeKernelAction (2 * Real.pi / L)
        (gLlatHam sys L θ) inputCutoff u q) ∧
      ‖v‖ ≤ ((1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit) *
        ‖molecularH2Truncate inputCutoff u‖ := by
  let C := (1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit
  have hC : 0 ≤ C := by
    change 0 ≤ (1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit
    linarith only [gLformConst_nonneg sys L hθ.tv_nonneg Hunit]
  have hBound : ∀ count, ‖fourierKernelFiniteOutput (2 * Real.pi / L)
      (gLlatHam sys L θ) inputCutoff u count‖ ≤
      C * ‖molecularH2Truncate inputCutoff u‖ := by
    intro count
    rw [fourierKernelFiniteOutput_gL_eq]
    exact gLham_H2_extract_uniform sys hL hθ Hunit hPeriodic
      (molecularH2Truncate inputCutoff u) count
  obtain ⟨v, hv, hNorm, _⟩ := exists_fourierCubeKernelAction_lp2 (2 * Real.pi / L)
    (gLlatHam sys L θ) inputCutoff u
    (C * ‖molecularH2Truncate inputCutoff u‖) (mul_nonneg hC (norm_nonneg _)) hBound
  exact ⟨v, hv, hNorm⟩

/-- The finite Hamiltonian applied to the coefficients of an arbitrary weighted `H²`
input, extended by zero. -/
def gLH2OutputLp (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (u : MolecularFourierH2 eta) (count : ℕ) :
    lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
  finiteFourierLpEmbed eta count
    (gLham sys L θ count
      (fullCoeffVector (finiteFourierCoeffExtract count
        (molecularH2Coeff (2 * Real.pi / L) u)))).ofLp

lemma gLH2OutputLp_eq_core (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (u : MolecularFourierH2 eta) (count : ℕ) :
    gLH2OutputLp sys L θ u count = gLCoreOutputLp sys L θ count u count := by
  unfold gLH2OutputLp gLCoreOutputLp gLCoreOutput
  rw [finiteFourierCoeffExtract_molecularH2Truncate]

lemma gLH2OutputLp_eq_compression (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (u : MolecularFourierH2 eta) (count : ℕ) :
    gLH2OutputLp sys L θ u count =
      molecularH2Truncate count (H (molecularH2Truncate count u)) := by
  rw [gLH2OutputLp_eq_core]
  exact gLCoreOutputLp_eq_truncate sys L θ count u
    (H (molecularH2Truncate count u)) (hKernel count u) count le_rfl

theorem gLH2OutputLp_tendsto (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (u : MolecularFourierH2 eta) :
    Tendsto (fun count => gLH2OutputLp sys L θ u count) atTop (𝓝 (H u)) := by
  have hAction : Tendsto (fun count => H (molecularH2Truncate count u))
      atTop (𝓝 (H u)) := (H.continuous.tendsto u).comp (molecularH2Truncate_tendsto u)
  have hBoth := molecularH2Truncate_tendsto_of_tendsto
    (fun count => H (molecularH2Truncate count u)) (H u) hAction
  simpa only [gLH2OutputLp_eq_compression sys L θ H hKernel] using hBoth

/-- The completed Fourier Hamiltonian of the Coulomb system on weighted `H²`
coefficients. -/
theorem exists_gLFourierH2Operator (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2,
      (∀ N u q, H (molecularH2Truncate N u) q =
        fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q) ∧
      (∀ u, ‖H u‖ ≤ ((1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit) * ‖u‖) := by
  have hC : 0 ≤ (1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit := by
    linarith only [gLformConst_nonneg sys L hθ.tv_nonneg Hunit]
  exact exists_fourierKernelH2Operator (2 * Real.pi / L)
    (gLlatHam sys L θ) _ hC
    (fun N u => exists_gLFourierCoreAction sys hL hθ Hunit hPeriodic N u)

/-! ## The Fourier-domain Galerkin bridge -/

lemma gLH2OutputLp_finiteFourierH2Lift (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (count : ℕ) (u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode count))) :
    gLH2OutputLp sys L θ (finiteFourierH2Lift eta (2 * Real.pi / L) count u.ofLp) count =
      finiteFourierLpEmbed eta count (gLham sys L θ count u).ofLp := by
  unfold gLH2OutputLp
  rw [finiteFourierCoeffExtract_molecularH2Coeff_finiteFourierH2Lift]
  rfl

/-- The constructed domain operator has the finite sesquilinear form on every finite
Fourier subspace. -/
theorem gLFourierDomainEmbedding_inner_eq (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (count : ℕ) (u v : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode count))) :
    inner ℂ
        ((finiteFourierDomainEmbedding eta (2 * Real.pi / L) count u :
          molecularFourierH2Domain eta (2 * Real.pi / L)) :
            lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
        (molecularFourierDomainOperator (2 * Real.pi / L) H
          (finiteFourierDomainEmbedding eta (2 * Real.pi / L) count v)) =
      inner ℂ u (gLham sys L θ count v) := by
  let w := finiteFourierH2Lift eta (2 * Real.pi / L) count v.ofLp
  have hAction : molecularFourierDomainOperator (2 * Real.pi / L) H
      (finiteFourierDomainEmbedding eta (2 * Real.pi / L) count v) = H w := by
    change molecularFourierDomainOperator (2 * Real.pi / L) H
      (molecularFourierH2DomainEquiv eta (2 * Real.pi / L) w) = H w
    exact molecularFourierDomainOperator_apply_equiv (2 * Real.pi / L) H w
  have hCompress := gLH2OutputLp_eq_compression sys L θ H hKernel w count
  have hFixed : molecularH2Truncate count w = w :=
    molecularH2Truncate_finiteFourierH2Lift eta (2 * Real.pi / L) count v.ofLp
  rw [hFixed] at hCompress
  have hOutput : gLH2OutputLp sys L θ w count =
      finiteFourierLpEmbed eta count (gLham sys L θ count v).ofLp :=
    gLH2OutputLp_finiteFourierH2Lift sys L θ count v
  rw [finiteFourierDomainEmbedding_coe, hAction]
  calc
    inner ℂ (finiteFourierLpEmbed eta count u.ofLp) (H w) =
        inner ℂ (finiteFourierLpEmbed eta count u.ofLp)
          (lpTruncate (fourierConfigCube eta count) (H w)) :=
      finiteFourierLpEmbed_inner_truncate eta count u.ofLp (H w)
    _ = inner ℂ (finiteFourierLpEmbed eta count u.ofLp)
          (gLH2OutputLp sys L θ w count) := by
      rw [hCompress]
      rfl
    _ = inner ℂ (finiteFourierLpEmbed eta count u.ofLp)
          (finiteFourierLpEmbed eta count (gLham sys L θ count v).ofLp) := by
      rw [hOutput]
    _ = inner ℂ u (gLham sys L θ count v) :=
      (finiteFourierLpIsometry eta count).inner_map_map u (gLham sys L θ count v)

theorem gLFourierDomainEmbedding_form_eq (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (count : ℕ) (u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode count))) :
    (inner ℂ
        ((finiteFourierDomainEmbedding eta (2 * Real.pi / L) count u :
          molecularFourierH2Domain eta (2 * Real.pi / L)) :
            lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
        (molecularFourierDomainOperator (2 * Real.pi / L) H
          (finiteFourierDomainEmbedding eta (2 * Real.pi / L) count u))).re =
      (inner ℂ u (gLham sys L θ count u)).re :=
  congrArg Complex.re (gLFourierDomainEmbedding_inner_eq sys L θ H hKernel count u u)


/-! ## The variational bound on `H²` -/

/-- On a cubic truncation the completed operator has the form of the cube Hamiltonian. -/
theorem gL_truncation_inner_eq (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (u : MolecularFourierH2 eta) (N : ℕ) :
    inner ℂ (molecularH2StateMap eta (2 * Real.pi / L) (molecularH2Truncate N u))
        (H (molecularH2Truncate N u)) =
      inner ℂ (fullCoeffVector (finiteFourierCoeffExtract N
          (molecularH2Coeff (2 * Real.pi / L) u)))
        (gLham sys L θ N (fullCoeffVector (finiteFourierCoeffExtract N
          (molecularH2Coeff (2 * Real.pi / L) u)))) := by
  set v := fullCoeffVector (finiteFourierCoeffExtract N (molecularH2Coeff (2 * Real.pi / L) u))
  have hembed : finiteFourierDomainEmbedding eta (2 * Real.pi / L) N v =
      molecularFourierH2DomainEquiv eta (2 * Real.pi / L) (molecularH2Truncate N u) := by
    change molecularFourierH2DomainEquiv eta (2 * Real.pi / L)
      (finiteFourierH2Lift eta (2 * Real.pi / L) N v.ofLp) = _
    rw [show v.ofLp = finiteFourierCoeffExtract N (molecularH2Coeff (2 * Real.pi / L) u) from rfl,
      finiteFourierH2Lift_extract]
  have h := gLFourierDomainEmbedding_inner_eq sys L θ H hKernel N v v
  rw [hembed, molecularFourierDomainOperator_apply_equiv,
    molecularFourierH2DomainEquiv_coe] at h
  exact h

lemma gL_truncation_norm_eq (u : MolecularFourierH2 eta) (g : ℝ) (N : ℕ) :
    ‖molecularH2StateMap eta g (molecularH2Truncate N u)‖ =
      ‖fullCoeffVector (finiteFourierCoeffExtract N (molecularH2Coeff g u))‖ := by
  set v := fullCoeffVector (finiteFourierCoeffExtract N (molecularH2Coeff g u))
  have hembed : finiteFourierDomainEmbedding eta g N v =
      molecularFourierH2DomainEquiv eta g (molecularH2Truncate N u) := by
    change molecularFourierH2DomainEquiv eta g (finiteFourierH2Lift eta g N v.ofLp) = _
    rw [show v.ofLp = finiteFourierCoeffExtract N (molecularH2Coeff g u) from rfl,
      finiteFourierH2Lift_extract]
  have h := (finiteFourierDomainEmbedding eta g N).norm_map v
  rw [hembed] at h
  exact h

/-- **The variational bound on `H²`**: for every `H²` state of the sector,
`E_L ‖ψ‖² ≤ Re⟨ψ, H ψ⟩`. -/
theorem gL_variational_H2 (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} (L : ℝ)
    (θ : ℝ → ℝ) {E : ℝ} (hE : IsGLTorusGroundEnergy sys lab L θ E)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (u : MolecularFourierH2 eta)
    (hS : IsSectorCoeff sys.sign lab (molecularH2Coeff (2 * Real.pi / L) u)) :
    E * ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ ^ 2 ≤
      (inner ℂ (molecularH2StateMap eta (2 * Real.pi / L) u) (H u)).re := by
  set g := 2 * Real.pi / L with hg
  have hfin : ∀ N : ℕ, E * ‖molecularH2StateMap eta g (molecularH2Truncate N u)‖ ^ 2 ≤
      (inner ℂ (molecularH2StateMap eta g (molecularH2Truncate N u))
        (H (molecularH2Truncate N u))).re := by
    intro N
    have hv : IsSectorVector sys.sign lab
        (fullCoeffVector (finiteFourierCoeffExtract N (molecularH2Coeff g u))) :=
      fullCoeffVector_isSector _ (finiteFourierCoeffExtract_isSector N _ hS)
    have h1 := hE.1 N _ hv
    rw [gL_truncation_norm_eq u g N, gL_truncation_inner_eq sys L θ H hKernel u N]
    exact h1
  have hT := molecularH2Truncate_tendsto u
  have hS1 : Tendsto (fun N => molecularH2StateMap eta g (molecularH2Truncate N u)) atTop
      (𝓝 (molecularH2StateMap eta g u)) :=
    ((molecularH2StateMap eta g).continuous.tendsto u).comp hT
  have hH1 : Tendsto (fun N => H (molecularH2Truncate N u)) atTop (𝓝 (H u)) :=
    (H.continuous.tendsto u).comp hT
  have hlim : Tendsto (fun N => (inner ℂ (molecularH2StateMap eta g (molecularH2Truncate N u))
      (H (molecularH2Truncate N u))).re -
        E * ‖molecularH2StateMap eta g (molecularH2Truncate N u)‖ ^ 2) atTop
      (𝓝 ((inner ℂ (molecularH2StateMap eta g u) (H u)).re -
        E * ‖molecularH2StateMap eta g u‖ ^ 2)) := by
    refine Tendsto.sub (Complex.continuous_re.continuousAt.tendsto.comp (hS1.inner hH1)) ?_
    exact tendsto_const_nhds.mul ((continuous_norm.tendsto _).comp hS1 |>.pow 2)
  have h0 := ge_of_tendsto hlim (Eventually.of_forall fun N => sub_nonneg.mpr (hfin N))
  linarith

/-! ## The potential part in position space -/

/-- The potential part of the completed `g_L` operator on the Fourier core. -/
theorem gLFourierPotentialH2_core (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (N : ℕ) (u : MolecularFourierH2 eta) (q : FourierConfig eta Lattice3) :
    coulombFourierPotentialH2 sys (2 * Real.pi / L) H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatPot sys L θ) N u q := by
  change H (molecularH2Truncate N u) q -
    coulombFourierKineticH2 sys (2 * Real.pi / L) (molecularH2Truncate N u) q = _
  rw [hKernel, coulombFourierKineticH2_core]
  simp only [fourierCubeKernelAction, gLlatHam, mul_add, Finset.sum_add_distrib]
  ring

theorem gLPositionPotentialH2_core_eq (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (V : MolecularPositionTorus eta → ℂ) (hV : MemLp V 2 volume)
    (hCoeff : ∀ q p : FourierConfig eta Lattice3,
      UnitAddTorus.mFourierCoeff V
          (molecularFourierIndexEquiv eta q - molecularFourierIndexEquiv eta p) =
        gLlatPot sys L θ q p)
    (N : ℕ) (u : MolecularFourierH2 eta) :
    coulombPositionPotentialH2 sys (2 * Real.pi / L) H (molecularH2Truncate N u) =
      molecularPositionPotentialFourierProduct eta V hV (fourierConfigCube eta N)
        (molecularH2Coeff (2 * Real.pi / L) u) := by
  apply (molecularPositionSynthesis eta).symm.injective
  apply lp.ext
  funext q
  change (molecularPositionSynthesis eta).symm
      (molecularPositionSynthesis eta
        (coulombFourierPotentialH2 sys (2 * Real.pi / L) H (molecularH2Truncate N u))) q = _
  rw [LinearIsometryEquiv.symm_apply_apply, gLFourierPotentialH2_core sys L θ H hKernel,
    molecularPositionPotentialFourierProduct_fourier]
  unfold fourierCubeKernelAction
  apply Finset.sum_congr rfl
  intro p _hp
  rw [hCoeff]

/-- **The potential part of the completed `g_L` operator is multiplication by `V`** on the whole
`H²` domain. -/
theorem gLPositionPotentialH2_pointwise (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (V : MolecularPositionTorus eta → ℂ) (hV : MemLp V 2 volume)
    (hCoeff : ∀ q p : FourierConfig eta Lattice3,
      UnitAddTorus.mFourierCoeff V
          (molecularFourierIndexEquiv eta q - molecularFourierIndexEquiv eta p) =
        gLlatPot sys L θ q p)
    (u : MolecularFourierH2 eta) :
    HasL2PointwisePotential volume V
      (molecularPositionH2StateMap eta (2 * Real.pi / L) u)
      (coulombPositionPotentialH2 sys (2 * Real.pi / L) H u) := by
  refine (molecularPositionH2Operator_pointwise_iff_core eta (2 * Real.pi / L) V
    (coulombPositionPotentialH2 sys (2 * Real.pi / L) H)).mpr (fun N v => ?_) u
  rw [gLPositionPotentialH2_core_eq sys L θ H hKernel V hV hCoeff N v,
    molecularPositionPotentialFourierProduct_eq_continuousProduct,
    ← molecularPositionFourierTest_cube_toLp]
  exact torusPotentialContinuousProduct_graph V hV
    (molecularPositionFourierTest eta (fourierConfigCube eta N)
      (molecularH2Coeff (2 * Real.pi / L) v))

/-! ## The variational bound for `C²` states -/

/-- **The variational bound for `C²` periodic states.** For every `C²` periodic state `φ` of the
sector and the `L²` function `p = V φ` (`V` the `g_L` multiplication function of `PlaneWave.FreeBoundary.PositionPotential`, zero
mode removed), `E_L ‖φ‖² ≤ Re⟨φ, K φ⟩ + Re⟨φ, p⟩`, `K` the classical kinetic operator. -/
theorem gL_variational_C2 (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (hR : R ≤ L / 2) {E : ℝ} (hE : IsGLTorusGroundEnergy sys lab L θ E)
    (φ : C(MolecularPositionTorus eta, ℂ)) (hφ : ContDiff ℝ 2 (torusRealLift φ))
    (hS : IsPositionSector sys.sign lab ((ContinuousMap.toLp 2 volume ℂ) φ))
    (p : MolecularPositionL2 eta)
    (hp : HasL2PointwisePotential volume (gLFourierPotential sys L θ)
      ((ContinuousMap.toLp 2 volume ℂ) φ) p) :
    E * ‖(ContinuousMap.toLp 2 volume ℂ) φ‖ ^ 2 ≤
      (inner ℂ ((ContinuousMap.toLp 2 volume ℂ) φ)
        ((ContinuousMap.toLp 2 volume ℂ) (coulombPositionContDiffKinetic sys L φ hφ))).re +
      (inner ℂ ((ContinuousMap.toLp 2 volume ℂ) φ) p).re := by
  obtain ⟨H, hKernel, -⟩ := exists_gLFourierH2Operator sys hL hθ
    molecularCanonicalUnitHardyConstant canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨u, hu, hk⟩ := coulombPositionContDiffTest_exists_H2 sys L φ hφ
  -- the sector of the coefficients
  have hS' : IsSectorCoeff sys.sign lab (molecularH2Coeff (2 * Real.pi / L) u) := by
    have h := (molecularPosition_sector_iff sys.sign lab _).mp hS
    rw [← hu] at h
    intro i j hij hl q
    have h1 := h i j hij hl q
    simp only [molecularPositionH2StateMap_apply, LinearIsometryEquiv.symm_apply_apply,
      molecularH2StateMap_apply] at h1
    exact h1
  have hvar := gL_variational_H2 sys L θ hE H hKernel u hS'
  -- transport to position space
  have hnorm : ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ =
      ‖(ContinuousMap.toLp 2 volume ℂ) φ‖ := by
    rw [← hu, molecularPositionH2StateMap_apply, molecularPositionSynthesis_norm]
  have hinner : inner ℂ (molecularH2StateMap eta (2 * Real.pi / L) u) (H u) =
      inner ℂ ((ContinuousMap.toLp 2 volume ℂ) φ) (molecularPositionHamiltonianH2 H u) := by
    rw [← hu, molecularPositionH2StateMap_apply, molecularPositionHamiltonianH2_apply,
      LinearIsometryEquiv.inner_map_map]
  have hpot : coulombPositionPotentialH2 sys (2 * Real.pi / L) H u = p := by
    have h := gLPositionPotentialH2_pointwise sys L θ H hKernel (gLFourierPotential sys L θ)
      (gLFourierPotential_memLp sys hL hθ) (gLFourierPotential_fourierCoeff sys hL hθ hR) u
    rw [hu] at h
    exact h.unique hp
  rw [hnorm, hinner, coulombPositionHamiltonianH2_decomposition sys (2 * Real.pi / L) H u, hk,
    hpot, inner_add_right, Complex.add_re] at hvar
  exact hvar

end

end FreeBoundary
