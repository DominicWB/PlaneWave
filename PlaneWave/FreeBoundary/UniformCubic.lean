import PlaneWave.FreeBoundary.UniformGridCore
import PlaneWave.FreeBoundary.TorusGroundEnergy

/-!
# `app:free`, `L`-uniform constants, part 2: the cubic Galerkin error with the sharper Sobolev
constant

The release bounds the one-particle Sobolev sum `Σ_ν (1 + g²|ν|²)⁻²` by `1 + 108/g⁴`
(`latticeSobolevShellTail_uniform_bound`), so its constant `C_s = √(1 + 108/g⁴)` grows like `L²`
in the cell side `L` (`g = 2π/L`). In the tail constant it multiplies `B_ker = √(432 C g)`,
`C = (πL)⁻²`, which decays like `L^{-3/2}`; so the `g_L` tail constant of `PlaneWave.FreeBoundary.CubeHamiltonian` grows like
`√L` and the cubic error constant of `PlaneWave.FreeBoundary.TorusGroundEnergy` like `L`. With the sum bounded by `1 + 78/g³`
(`PlaneWaveGridG.sum_sobolevP_le`, `PlaneWave.FreeBoundary.UniformGridCore`) the product `C_s B_ker` is bounded uniformly in `L`.

This file repeats, with the hypothesis `1 + 78/g³ ≤ C_s²`, the release lemmas that use the scale
condition (suffix `P`), the two release tail bounds of `PlaneWave.Auxiliary.PotentialTails` with `C_s = √(1 + 78/g³)`
(`tCsP`, `ctailP`), and the `g_L` tail bound, Galerkin energy bound and cubic error of `PlaneWave.FreeBoundary.CubeHamiltonian`
and `PlaneWave.FreeBoundary.TorusGroundEnergy` (`gLtailConstP`, `gL_cubic_energy_boundP`, `gL_cubic_errorP`, `gLCubicConstP`,
`gL_sector_cubic_errorP`). The proofs are those of the originals.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter

namespace PlaneWaveCertificate

/-- The release's Sobolev weight in the form of `PlaneWave.FreeBoundary.UniformGridCore`. -/
lemma latticeSobolevWeight_eq_inv (g : ℝ) (nu : Lattice3) :
    latticeSobolevWeight g nu = ((1 + g ^ 2 * PlaneWaveGridG.nsq nu)⁻¹) ^ 2 := by
  unfold latticeSobolevWeight
  rw [one_div]
  rfl

/-- The nonzero cubic shells carry Sobolev weight at most `78/g³`, uniformly in their number
(the release: `108/g⁴`). -/
lemma latticeSobolevShellTail_boundP (g : ℝ) (hg : 0 < g) (count : ℕ) :
    shellTailMass (finiteShellMass cubicSupShell (latticeSobolevWeight g)) 0 count ≤
      78 / g ^ 3 := by
  classical
  unfold shellTailMass finiteShellMass
  simp only [zero_add]
  have hdisj : (↑(Finset.range count) : Set ℕ).PairwiseDisjoint cubicSupShell := by
    intro a _ b _ hab
    exact Finset.disjoint_left.2 fun ν ha hb => hab (cubicSupShell_index_unique ha hb)
  rw [← Finset.sum_biUnion hdisj]
  set F := (Finset.range count).biUnion cubicSupShell with hF
  have h0 : (0 : Lattice3) ∉ F := by
    intro h
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.1 h
    have h1 := cubicSupShell_normSq_lower k hk
    have h2 : latticeNormSq (0 : Lattice3) = 0 := by simp [latticeNormSq]
    rw [h2] at h1
    have : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
    linarith
  have hsum := PlaneWaveGridG.sum_sobolevP_le hg (insert (0 : Lattice3) F)
  rw [Finset.sum_insert h0, PlaneWaveGridG.nsq_zero, mul_zero, add_zero, inv_one,
    one_pow] at hsum
  have e : ∑ ν ∈ F, latticeSobolevWeight g ν =
      ∑ ν ∈ F, ((1 + g ^ 2 * PlaneWaveGridG.nsq ν)⁻¹) ^ 2 :=
    Finset.sum_congr rfl fun ν _ => latticeSobolevWeight_eq_inv g ν
  rw [e]
  unfold PlaneWaveGridG.sobP at hsum
  linarith

/-- The finite plane-wave mode set satisfies the one-particle Sobolev weight bound when
`1 + 78/g³ ≤ C_s²` (the release: `1 + 108/g⁴ ≤ C_s²`). -/
lemma finitePlaneWave_hasOneParticleInverseH2WeightBoundP
    (g Cs : ℝ) (count : ℕ) (hgpos : 0 < g) (hCsScale : 1 + 78 / g ^ 3 ≤ Cs ^ 2) :
    HasOneParticleInverseH2WeightBound (finitePlaneWaveKabs g count) Cs := by
  unfold HasOneParticleInverseH2WeightBound
  rw [oneParticleInverseH2WeightSum_finitePlaneWave]
  have := latticeSobolevShellTail_boundP g hgpos count
  linarith

/-! ## The release lemmas that use the scale condition, with `1 + 78/g³ ≤ C_s²` -/

/-- The full high-pass estimate, using the existing explicit column, shell, and
slice-Sobolev theorems.  It uses H2 regularity but no eigenpair or Ritz premise. -/
lemma explicitHighPassCoulombOperator_norm_le_of_h2P
    {eta : ℕ} (r : Fin eta) (K g C rho Cs Bker M2 : ℝ) (basisExtra : ℕ)
    (coeff : FourierConfig eta
      (FinitePlaneWaveMode (cutoffShellIndex K g + basisExtra)) → ℂ)
    (hK1 : 1 ≤ K) (hg : 0 < g) (hC : 0 ≤ C)
    (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * K = 1)
    (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker) (hM2 : 0 ≤ M2)
    (hBkerScale : 432 * C * g ≤ Bker ^ 2)
    (hCsScale : 1 + 78 / g ^ 3 ≤ Cs ^ 2)
    (hH2 : fullH2Sq (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) coeff ≤ M2 ^ 2) :
    ‖explicitHighPassCoulombOperator eta r K g C
        (cutoffShellIndex K g + basisExtra) (fullCoeffVector coeff)‖ ≤
      (Cs * Bker * M2) * rho := by
  let m := cutoffShellIndex K g
  let count := m + basisExtra
  let transfers := coulombTransferShellCount m basisExtra
  let Q := finiteHighPassKernelTailSq K g C m transfers
  let kabs := finitePlaneWaveKabs g count
  let kernel := finiteHighPassCoulombKernel K g C count
  let A := explicitHighPassCoulombOperator eta r K g C count
  have hK : 0 ≤ K := le_trans (by norm_num : (0 : ℝ) ≤ 1) hK1
  have hQ : 0 ≤ Q := finiteHighPassKernelTailSq_nonneg K g C m transfers hC
  have hColumnSq : HasReferenceKernelColumnSqBound kernel Q :=
    finiteHighPassCoulombKernel_hasColumnSqBound K g C m basisExtra hC
  have hColumn := referenceSliceKernelColumnNormBound_of_sq r kernel Q hQ hColumnSq
  have hExpansion := explicitHighPassCoulombOperator_hasExpansion eta r K g C count coeff
  have hAtoms := hasSliceKernelAtomRepresentation_of_referenceKernel
    r kernel A coeff (Real.sqrt Q) hExpansion hColumn
  have hHolder := sliceHolderBound_of_sqrt_kernel_atom_representation
    (outerConfigOf r) A coeff Q hQ hAtoms
  have hOne := finitePlaneWave_hasOneParticleInverseH2WeightBoundP g Cs count hg hCsScale
  have hWeight := sliceInverseH2WeightBound_of_oneParticleBound r kabs Cs hOne
  have hSobolev := sliceSobolevBound_of_inverseH2Weight (outerConfigOf r) kabs coeff Cs hWeight
  have hSlice := highPassSliceBound_of_slice_holder_sobolev (outerConfigOf r)
    kabs A coeff (sliceFourierL1Sq (outerConfigOf r) coeff) Cs Q hQ hHolder hSobolev
  rcases cutoffShellIndex_placement K g hK hg with ⟨hUpper, hLower⟩
  have hCutBudget := cutoff_and_budget_from_shell_index_placement K g C Bker m
    hK (le_of_lt hg) hC hUpper hLower hBkerScale
  have hBelow := all_earlier_cubic_shells_below_half_cutoff K g m hCutBudget.1
  have hCover := finiteHighPassKernelTailSq_shell_cover K g C m transfers hC hBelow
  have hDecay := finiteShellMass_decay_on_range cubicSupShell
    (latticeCoulombSquareWeight C) 54 C m transfers (by norm_num) hC
    cubicSupShell_hasQuadraticShellCount (cubicSupShell_hasInverseFourthCoulombWeight C hC)
  have hKernelTail := kernel_tail_bound_from_inverse_square_shells K Q Bker (54 * C)
    (finiteShellMass cubicSupShell (latticeCoulombSquareWeight C)) m transfers
    hK (mul_nonneg (by norm_num) hC) hCover hDecay hCutBudget.2
  exact high_pass_bound_from_kernel_and_slice K rho Cs Bker M2 Q kabs coeff A
    hK1 hRho hRhoScale hCs hBker hM2 hQ hKernelTail hH2 hSlice

/-- Pair high-pass H2 bound.  All conserved total momenta share the same Q and Cs. -/
lemma finiteElectronPairHighPassOperator_hasHighPassSliceBoundP
    {eta : ℕ} (i j : Fin eta) (hij : i ≠ j)
    (K g C Cs : ℝ) (basisExtra : ℕ)
    (hC : 0 ≤ C) (hg : 0 < g) (hCsScale : 1 + 78 / g ^ 3 ≤ Cs ^ 2)
    (coeff : FourierConfig eta
      (FinitePlaneWaveMode (cutoffShellIndex K g + basisExtra)) → ℂ) :
    HasHighPassSliceBound
      (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra))
      (finiteElectronPairHighPassOperator i j K g C (cutoffShellIndex K g + basisExtra))
      coeff Cs
      (finiteHighPassKernelTailSq K g C (cutoffShellIndex K g)
        (coulombTransferShellCount (cutoffShellIndex K g) basisExtra)) := by
  let m := cutoffShellIndex K g
  let count := m + basisExtra
  let Q := finiteHighPassKernelTailSq K g C m (coulombTransferShellCount m basisExtra)
  have hQ : 0 ≤ Q := finiteHighPassKernelTailSq_nonneg K g C m _ hC
  have hColumn := finiteHighPassCoulombKernel_hasColumnSqBound K g C m basisExtra hC
  have hInverse := finitePlaneWave_hasOneParticleInverseH2WeightBoundP g Cs count hg hCsScale
  exact finiteElectronPairKernelOperator_h2_column_bound i j hij count
    (finitePlaneWaveKabs g count) (finiteHighPassCoulombKernel K g C count)
    Cs Q hQ hInverse hColumn (fullCoeffVector coeff)

/-- The genuine pair high-pass interaction satisfies the same K^(-1/2) estimate
as the one-body high-pass interaction.  There is no assumed pair estimate. -/
lemma finiteElectronPairHighPassOperator_norm_le_of_h2P
    {eta : ℕ} (i j : Fin eta) (hij : i ≠ j)
    (K g C rho Cs Bker M2 : ℝ) (basisExtra : ℕ)
    (coeff : FourierConfig eta
      (FinitePlaneWaveMode (cutoffShellIndex K g + basisExtra)) → ℂ)
    (hK1 : 1 ≤ K) (hg : 0 < g) (hC : 0 ≤ C)
    (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * K = 1)
    (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker) (hM2 : 0 ≤ M2)
    (hBkerScale : 432 * C * g ≤ Bker ^ 2)
    (hCsScale : 1 + 78 / g ^ 3 ≤ Cs ^ 2)
    (hH2 : fullH2Sq (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) coeff ≤ M2 ^ 2) :
    ‖finiteElectronPairHighPassOperator i j K g C
        (cutoffShellIndex K g + basisExtra) (fullCoeffVector coeff)‖ ≤
      (Cs * Bker * M2) * rho := by
  have hK : 0 ≤ K := le_trans (by norm_num : (0 : ℝ) ≤ 1) hK1
  have hQ := finiteHighPassKernelTailSq_nonneg K g C (cutoffShellIndex K g)
    (coulombTransferShellCount (cutoffShellIndex K g) basisExtra) hC
  have hKernel := finiteHighPassKernelTailSq_scaled_bound K g C Bker basisExtra
    hK hg hC hBkerScale
  have hSlice := finiteElectronPairHighPassOperator_hasHighPassSliceBoundP i j hij
    K g C Cs basisExtra hC hg hCsScale coeff
  exact high_pass_bound_from_kernel_and_slice K rho Cs Bker M2 _
    (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) coeff
    (finiteElectronPairHighPassOperator i j K g C (cutoffShellIndex K g + basisExtra))
    hK1 hRho hRhoScale hCs hBker hM2 hQ hKernel hH2 hSlice

/-- Strong two-scale tail estimate on either named first electron of the pair:
low transfer is O(K^-1), high transfer is O(K^-1/2).  All kernel estimates
are proved, and the only state-regularity input is the agreed H2 bound. -/
lemma finiteElectronPairCoulombOperator_tail_bound_first_two_scaleP
    {eta : ℕ} (i j : Fin eta) (hij : i ≠ j)
    (K g C rho Blow Cs Bker M2 : ℝ) (basisExtra : ℕ)
    (coeff : FourierConfig eta
      (FinitePlaneWaveMode (cutoffShellIndex K g + basisExtra)) → ℂ)
    (hK1 : 1 ≤ K) (hg : 0 < g) (hC : 0 ≤ C)
    (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * K = 1)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker) (hM2 : 0 ≤ M2)
    (h2gK : 2 * g ≤ K) (hAmplitude : 54 * Real.sqrt C ≤ Blow * g)
    (hBkerScale : 432 * C * g ≤ Bker ^ 2) (hCsScale : 1 + 78 / g ^ 3 ≤ Cs ^ 2)
    (hH2 : fullH2Sq (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) coeff ≤ M2 ^ 2) :
    ‖referenceTailOperator K (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) i
        (finiteElectronPairCoulombOperator i j C (cutoffShellIndex K g + basisExtra)
          (fullCoeffVector coeff))‖ ≤
      (4 * Blow * M2) * rho ^ 2 + (Cs * Bker * M2) * rho := by
  let count := cutoffShellIndex K g + basisExtra
  let kabs := finitePlaneWaveKabs g count
  let Wlow := finiteElectronPairLowPassOperator i j K g C count
  let Whigh := finiteElectronPairHighPassOperator i j K g C count
  have hK : 0 ≤ K := le_trans (by norm_num : (0 : ℝ) ≤ 1) hK1
  have hkabs : ∀ v, 0 ≤ kabs v := finitePlaneWaveKabs_nonneg g count (le_of_lt hg)
  have hLowOp : ∀ u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode count)),
      ‖referenceTailOperator K kabs i (Wlow u)‖ ≤ Blow * K * ‖u‖ := by
    intro u
    exact (referenceTailOperator_norm_le K kabs i (Wlow u)).trans
      (finiteElectronPairLowPassOperator_norm_le i j hij K g C Blow count
        hK hg hC hBlow h2gK hAmplitude u)
  have hLow := low_pass_bound_from_h2_tail K rho Blow M2 kabs i coeff Wlow
    hK1 hRhoScale hkabs hBlow hM2 hH2 hLowOp
  have hSupport := finiteElectronPairLowPassOperator_hasLowPassSupport i j K g C count
  have hLowTail : ‖referenceTailOperator K kabs i (Wlow (fullCoeffVector coeff))‖ ≤
      (4 * Blow * M2) * rho ^ 2 := by
    rw [hSupport (fullCoeffVector coeff)]
    exact hLow
  have hHigh := finiteElectronPairHighPassOperator_norm_le_of_h2P i j hij
    K g C rho Cs Bker M2 basisExtra coeff hK1 hg hC hRho hRhoScale hCs hBker hM2
    hBkerScale hCsScale hH2
  have hHighTail : ‖referenceTailOperator K kabs i (Whigh (fullCoeffVector coeff))‖ ≤
      (Cs * Bker * M2) * rho :=
    (referenceTailOperator_norm_le K kabs i (Whigh (fullCoeffVector coeff))).trans hHigh
  have hSplit := finiteElectronPairCoulombOperator_low_add_high i j K g C count hK (le_of_lt hg)
  rw [hSplit, LinearMap.add_apply, map_add]
  exact (norm_add_le _ _).trans (add_le_add hLowTail hHighTail)

/-- Common K^(-1/2) form for a pair involving the reference electron. -/
lemma finiteElectronPairCoulombOperator_tail_bound_firstP
    {eta : ℕ} (i j : Fin eta) (hij : i ≠ j)
    (K g C rho Blow Cs Bker M2 : ℝ) (basisExtra : ℕ)
    (coeff : FourierConfig eta
      (FinitePlaneWaveMode (cutoffShellIndex K g + basisExtra)) → ℂ)
    (hK1 : 1 ≤ K) (hg : 0 < g) (hC : 0 ≤ C)
    (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * K = 1)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker) (hM2 : 0 ≤ M2)
    (h2gK : 2 * g ≤ K) (hAmplitude : 54 * Real.sqrt C ≤ Blow * g)
    (hBkerScale : 432 * C * g ≤ Bker ^ 2) (hCsScale : 1 + 78 / g ^ 3 ≤ Cs ^ 2)
    (hH2 : fullH2Sq (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) coeff ≤ M2 ^ 2) :
    ‖referenceTailOperator K (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) i
        (finiteElectronPairCoulombOperator i j C (cutoffShellIndex K g + basisExtra)
          (fullCoeffVector coeff))‖ ≤
      (4 * Blow * M2 + Cs * Bker * M2) * rho := by
  have hTwo := finiteElectronPairCoulombOperator_tail_bound_first_two_scaleP i j hij
    K g C rho Blow Cs Bker M2 basisExtra coeff hK1 hg hC hRho hRhoScale
    hBlow hCs hBker hM2 h2gK hAmplitude hBkerScale hCsScale hH2
  have hSqLeOne : rho ^ 2 ≤ 1 := by
    nlinarith only [hRhoScale,
      mul_nonneg (sq_nonneg rho) (sub_nonneg.mpr hK1)]
  have hLeOne : rho ≤ 1 := by nlinarith only [hSqLeOne, sq_nonneg (rho - 1)]
  have hSqLe : rho ^ 2 ≤ rho := by
    nlinarith only [mul_nonneg hRho (sub_nonneg.mpr hLeOne)]
  have hLow0 : 0 ≤ 4 * Blow * M2 := mul_nonneg (mul_nonneg (by norm_num) hBlow) hM2
  calc
    _ ≤ (4 * Blow * M2) * rho ^ 2 + (Cs * Bker * M2) * rho := hTwo
    _ ≤ (4 * Blow * M2) * rho + (Cs * Bker * M2) * rho :=
      add_le_add (mul_le_mul_of_nonneg_left hSqLe hLow0) (le_refl _)
    _ = _ := by ring

/-- The same tail estimate when the reference electron is named second. -/
lemma finiteElectronPairCoulombOperator_tail_bound_secondP
    {eta : ℕ} (i j : Fin eta) (hij : i ≠ j)
    (K g C rho Blow Cs Bker M2 : ℝ) (basisExtra : ℕ)
    (coeff : FourierConfig eta
      (FinitePlaneWaveMode (cutoffShellIndex K g + basisExtra)) → ℂ)
    (hK1 : 1 ≤ K) (hg : 0 < g) (hC : 0 ≤ C)
    (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * K = 1)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker) (hM2 : 0 ≤ M2)
    (h2gK : 2 * g ≤ K) (hAmplitude : 54 * Real.sqrt C ≤ Blow * g)
    (hBkerScale : 432 * C * g ≤ Bker ^ 2) (hCsScale : 1 + 78 / g ^ 3 ≤ Cs ^ 2)
    (hH2 : fullH2Sq (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) coeff ≤ M2 ^ 2) :
    ‖referenceTailOperator K (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) j
        (finiteElectronPairCoulombOperator i j C (cutoffShellIndex K g + basisExtra)
          (fullCoeffVector coeff))‖ ≤
      (4 * Blow * M2 + Cs * Bker * M2) * rho := by
  rw [finiteElectronPairCoulombOperator_swap_particles i j C]
  exact finiteElectronPairCoulombOperator_tail_bound_firstP j i (Ne.symm hij)
    K g C rho Blow Cs Bker M2 basisExtra coeff hK1 hg hC hRho hRhoScale
    hBlow hCs hBker hM2 h2gK hAmplitude hBkerScale hCsScale hH2

/-- A uniform all-reference bound for one pair.  This deliberately uses a common
budget for the affected and unaffected cases, suitable for a simple finite sum.
The stronger two-scale affected and far estimates remain separately available. -/
lemma finiteElectronPairCoulombOperator_tail_bound_any_referenceP
    {eta : ℕ} (i j r : Fin eta) (hij : i ≠ j)
    (K g C rho B Hunit Blow Cs Bker M2 : ℝ) (basisExtra : ℕ)
    (coeff : FourierConfig eta
      (FinitePlaneWaveMode (cutoffShellIndex K g + basisExtra)) → ℂ)
    (hK1 : 1 ≤ K) (hg : 0 < g) (hC : 0 ≤ C)
    (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * K = 1)
    (hB : 0 ≤ B) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs)
    (hBker : 0 ≤ Bker) (hM2 : 0 ≤ M2)
    (h2gK : 2 * g ≤ K) (hAmplitude : 54 * Real.sqrt C ≤ Blow * g)
    (hBkerScale : 432 * C * g ≤ Bker ^ 2) (hCsScale : 1 + 78 / g ^ 3 ≤ Cs ^ 2)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hScale : C * Hunit ^ 2 ≤ B ^ 2 * physicalH1Scale g)
    (hH2 : fullH2Sq (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) coeff ≤ M2 ^ 2) :
    ‖referenceTailOperator K (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) r
        (finiteElectronPairCoulombOperator i j C (cutoffShellIndex K g + basisExtra)
          (fullCoeffVector coeff))‖ ≤
      (B * M2 + (4 * Blow * M2 + Cs * Bker * M2)) * rho := by
  have hFar0 : 0 ≤ B * M2 := mul_nonneg hB hM2
  have hNear0 : 0 ≤ 4 * Blow * M2 + Cs * Bker * M2 :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hBlow) hM2)
      (mul_nonneg (mul_nonneg hCs hBker) hM2)
  have hNearBudget : (4 * Blow * M2 + Cs * Bker * M2) * rho ≤
      (B * M2 + (4 * Blow * M2 + Cs * Bker * M2)) * rho := by
    apply mul_le_mul_of_nonneg_right _ hRho
    linarith only [hFar0]
  by_cases hri : r = i
  · subst r
    exact (finiteElectronPairCoulombOperator_tail_bound_firstP i j hij
      K g C rho Blow Cs Bker M2 basisExtra coeff hK1 hg hC hRho hRhoScale
      hBlow hCs hBker hM2 h2gK hAmplitude hBkerScale hCsScale hH2).trans hNearBudget
  · by_cases hrj : r = j
    · subst r
      exact (finiteElectronPairCoulombOperator_tail_bound_secondP i j hij
        K g C rho Blow Cs Bker M2 basisExtra coeff hK1 hg hC hRho hRhoScale
        hBlow hCs hBker hM2 h2gK hAmplitude hBkerScale hCsScale hH2).trans hNearBudget
    · have hFar := finiteElectronPairCoulombOperator_far_tail_bound i j r hij hri hrj
        K g C rho B Hunit M2 (cutoffShellIndex K g + basisExtra) coeff
        hK1 (le_of_lt hg) hC hRhoScale hB hM2 hPeriodic hScale hH2
      have hSqLeOne : rho ^ 2 ≤ 1 := by
        nlinarith only [hRhoScale,
          mul_nonneg (sq_nonneg rho) (sub_nonneg.mpr hK1)]
      have hLeOne : rho ≤ 1 := by nlinarith only [hSqLeOne, sq_nonneg (rho - 1)]
      have hSqLe : rho ^ 2 ≤ rho := by
        nlinarith only [mul_nonneg hRho (sub_nonneg.mpr hLeOne)]
      calc
        _ ≤ (B * M2) * rho ^ 2 := hFar
        _ ≤ (B * M2) * rho := mul_le_mul_of_nonneg_left hSqLe hFar0
        _ ≤ (B * M2 + (4 * Blow * M2 + Cs * Bker * M2)) * rho := by
          apply mul_le_mul_of_nonneg_right _ hRho
          linarith only [hNear0]

/-- Direct unshifted one-body tail with its two different powers of rho.
This uses only the already compiled low/high estimates, not a spectral theorem. -/
lemma referenceCoulombOperator_tail_bound_two_scaleP
    {eta : ℕ} (i : Fin eta)
    (K g C rho Blow Cs Bker M2 : ℝ) (basisExtra : ℕ)
    (coeff : FourierConfig eta
      (FinitePlaneWaveMode (cutoffShellIndex K g + basisExtra)) → ℂ)
    (hK1 : 1 ≤ K) (hg : 0 < g) (hC : 0 ≤ C)
    (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * K = 1)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker) (hM2 : 0 ≤ M2)
    (h2gK : 2 * g ≤ K) (hAmplitude : 54 * Real.sqrt C ≤ Blow * g)
    (hBkerScale : 432 * C * g ≤ Bker ^ 2) (hCsScale : 1 + 78 / g ^ 3 ≤ Cs ^ 2)
    (hH2 : fullH2Sq (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) coeff ≤ M2 ^ 2) :
    ‖referenceTailOperator K (finitePlaneWaveKabs g (cutoffShellIndex K g + basisExtra)) i
        (referenceKernelConvolutionOperator i
          (finiteCoulombKernel C (cutoffShellIndex K g + basisExtra))
          (fullCoeffVector coeff))‖ ≤
      (4 * Blow * M2) * rho ^ 2 + (Cs * Bker * M2) * rho := by
  let count := cutoffShellIndex K g + basisExtra
  let kabs := finitePlaneWaveKabs g count
  let Wlow := referenceKernelConvolutionOperator i (finiteLowPassCoulombKernel K g C count)
  let Whigh := explicitHighPassCoulombOperator eta i K g C count
  have hK : 0 ≤ K := le_trans (by norm_num : (0 : ℝ) ≤ 1) hK1
  have hkabs : ∀ v, 0 ≤ kabs v := finitePlaneWaveKabs_nonneg g count (le_of_lt hg)
  have hLowOp : ∀ u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode count)),
      ‖referenceTailOperator K kabs i (Wlow u)‖ ≤ Blow * K * ‖u‖ := by
    intro u
    exact (referenceTailOperator_norm_le K kabs i (Wlow u)).trans
      (finiteLowPassCoulombOperator_norm_le_of_amplitudeScale i K g C Blow count
        hK hg hC hBlow h2gK hAmplitude u)
  have hLow := low_pass_bound_from_h2_tail K rho Blow M2 kabs i coeff Wlow
    hK1 hRhoScale hkabs hBlow hM2 hH2 hLowOp
  have hSupport := referenceKernelConvolutionOperator_hasLowPassSupport K kabs i
    (finiteLowPassCoulombKernel K g C count)
    (finiteLowPassCoulombKernel_hasReferenceSupport K g C count)
  have hLowTail : ‖referenceTailOperator K kabs i (Wlow (fullCoeffVector coeff))‖ ≤
      (4 * Blow * M2) * rho ^ 2 := by
    rw [hSupport (fullCoeffVector coeff)]
    exact hLow
  have hHigh := explicitHighPassCoulombOperator_norm_le_of_h2P i
    K g C rho Cs Bker M2 basisExtra coeff hK1 hg hC hRho hRhoScale hCs hBker hM2
    hBkerScale hCsScale hH2
  have hHighTail : ‖referenceTailOperator K kabs i (Whigh (fullCoeffVector coeff))‖ ≤
      (Cs * Bker * M2) * rho :=
    (referenceTailOperator_norm_le K kabs i (Whigh (fullCoeffVector coeff))).trans hHigh
  rw [referenceLowHighCoulombOperator_eq_full i K g C count hK (le_of_lt hg),
    LinearMap.add_apply, map_add]
  exact (norm_add_le _ _).trans (add_le_add hLowTail hHighTail)

end PlaneWaveCertificate

open PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν] {n : ℕ}

/-! ## The tail constants with the sharper Sobolev constant -/

/-- `C_s = √(1 + 78/g³)`. -/
noncomputable def tCsP (g : ℝ) : ℝ := Real.sqrt (1 + 78 / g ^ 3)

/-- `Z = B + 4 B_low + C_s B_ker` with `C_s = tCsP`. -/
noncomputable def tZP (C Hunit g : ℝ) : ℝ := tB C Hunit g + (4 * tBlow C g + tCsP g * tBker C g)

/-- The tail constant `c_tail = (1 + √(2g)) B + Z` with `C_s = tCsP`. -/
noncomputable def ctailP (C Hunit g : ℝ) : ℝ :=
  (1 + Real.sqrt (2 * g)) * tB C Hunit g + tZP C Hunit g

lemma tCsP_nonneg (g : ℝ) : 0 ≤ tCsP g := Real.sqrt_nonneg _

lemma tZP_nonneg {C Hunit g : ℝ} (hg : 0 < g) : 0 ≤ tZP C Hunit g := by
  unfold tZP
  have := tB_nonneg C Hunit g; have := tBlow_nonneg (C := C) hg
  have := tCsP_nonneg g; have := tBker_nonneg C g
  positivity

lemma ctailP_nonneg {C Hunit g : ℝ} (hg : 0 < g) : 0 ≤ ctailP C Hunit g := by
  unfold ctailP
  have := tB_nonneg C Hunit g; have := tZP_nonneg (C := C) (Hunit := Hunit) hg
  positivity

lemma tCsP_scale {g : ℝ} (hg : 0 < g) : 1 + 78 / g ^ 3 ≤ tCsP g ^ 2 := by
  unfold tCsP; rw [Real.sq_sqrt (by positivity)]

omit [Fintype ν] in
/-- The release's all-reference pair tail bound, on any cube containing the cutoff shell. -/
lemma pair_tail_releaseP {i j : Fin eta} (hij : i ≠ j) (a : Fin eta) {g C : ℝ} (hg : 0 < g)
    (hC : 0 ≤ C) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {Kt M2 : ℝ} (hK1 : 1 ≤ Kt) (h2gK : 2 * g ≤ Kt) (hn : cutoffShellIndex Kt g ≤ n)
    (hM2 : 0 ≤ M2) (v : En eta n) (hH2 : fullH2Sq (finitePlaneWaveKabs g n) v.ofLp ≤ M2 ^ 2) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs g n) a
        (finiteElectronPairCoulombOperator i j C n v)‖ ≤
      tZP C Hunit g * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hK0 : 0 < Kt := by linarith
  have h := finiteElectronPairCoulombOperator_tail_bound_any_referenceP i j a hij Kt g C
    (Kt ^ (-(1 / 2 : ℝ))) (tB C Hunit g) Hunit (tBlow C g) (tCsP g) (tBker C g) M2 e v.ofLp
    hK1 hg hC (Real.rpow_pos_of_pos hK0 _).le (rho_scale hK0) (tB_nonneg C Hunit g)
    (tBlow_nonneg hg) (tCsP_nonneg g) (tBker_nonneg C g) hM2 h2gK (tBlow_amp hg)
    (tBker_scale hC hg) (tCsP_scale hg) hPeriodic (tB_scale hC hg) hH2
  have hfc : fullCoeffVector v.ofLp = v := rfl
  rw [hfc] at h
  refine h.trans (le_of_eq ?_)
  unfold tZP; ring

omit [Fintype ν] in
/-- The release's tail bounds for the Coulomb kernel of one register (the register itself:
two-scale bound; any other register: commutation and the far bound). -/
lemma single_tail_releaseP (r a : Fin eta) {g C : ℝ} (hg : 0 < g) (hC : 0 ≤ C) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {Kt M2 : ℝ} (hK1 : 1 ≤ Kt)
    (h2gK : 2 * g ≤ Kt) (hn : cutoffShellIndex Kt g ≤ n) (hM2 : 0 ≤ M2) (v : En eta n)
    (hH2 : fullH2Sq (finitePlaneWaveKabs g n) v.ofLp ≤ M2 ^ 2) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs g n) a
        (referenceKernelConvolutionOperator r (finiteCoulombKernel C n) v)‖ ≤
      tZP C Hunit g * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hK0 : 0 < Kt := by linarith
  have hρ0 : 0 ≤ Kt ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hK0 _).le
  have hρs := rho_scale hK0
  have hsq := rho_sq_le_rho_of_cutoff_scale hK1 hρ0 hρs
  have hB0 := tB_nonneg C Hunit g
  have hBlow0 := tBlow_nonneg (C := C) hg
  have hCs0 := tCsP_nonneg g
  have hBker0 := tBker_nonneg C g
  have hfc : fullCoeffVector v.ofLp = v := rfl
  unfold tZP
  by_cases har : a = r
  · rw [har]
    have h := referenceCoulombOperator_tail_bound_two_scaleP r Kt g C (Kt ^ (-(1 / 2 : ℝ)))
      (tBlow C g) (tCsP g) (tBker C g) M2 e v.ofLp hK1 hg hC hρ0 hρs hBlow0 hCs0 hBker0 hM2 h2gK
      (tBlow_amp hg) (tBker_scale hC hg) (tCsP_scale hg) hH2
    rw [hfc] at h
    refine h.trans ?_
    have h1 : 4 * tBlow C g * M2 * (Kt ^ (-(1 / 2 : ℝ))) ^ 2 ≤
        4 * tBlow C g * M2 * Kt ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h2 : 0 ≤ tB C Hunit g * M2 * Kt ^ (-(1 / 2 : ℝ)) := by positivity
    nlinarith
  · have hComm := referenceKernelConvolutionOperator_commutesWith_other_tail r a har Kt
      (finitePlaneWaveKabs g (cutoffShellIndex Kt g + e))
      (finiteCoulombKernel C (cutoffShellIndex Kt g + e))
    rw [hComm v]
    have hFar := far_bound_from_h1_h2_tail Kt (Kt ^ (-(1 / 2 : ℝ))) (tB C Hunit g) M2
      (finitePlaneWaveKabs g (cutoffShellIndex Kt g + e)) a v.ofLp _ hK1 hρs
      (finitePlaneWaveKabs_nonneg g _ hg.le) hB0 hM2 hH2
      (refCoulomb_h1 r hg hC Hunit hPeriodic (cutoffShellIndex Kt g + e))
    rw [hfc] at hFar
    refine hFar.trans ?_
    have h1 : tB C Hunit g * M2 * (Kt ^ (-(1 / 2 : ℝ))) ^ 2 ≤
        tB C Hunit g * M2 * Kt ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h2 : 0 ≤ (4 * tBlow C g + tCsP g * tBker C g) * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
      positivity
    nlinarith

end FSNormal

namespace FreeBoundary

open FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν] {R : ℝ} {θ : ℝ → ℝ}

/-! ## The potential tail with the sharper Sobolev constant -/

section TailP

variable {n : ℕ}

omit [Fintype ν] in
/-- `tail_pair_dominated` (`PlaneWave.Auxiliary.PotentialTails`) under any `H²` budget `M₂`. -/
lemma tail_pair_M2P {L : ℝ} (hL : 0 < L) {i j : Fin eta} (hij : i ≠ j) (a : Fin eta) {C : ℝ}
    (hC : 0 ≤ C) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (κ : Cfg eta n → Cfg eta n → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hdom : ∀ q p, ‖κ q p‖ ≤ Cg * ‖finiteElectronPairConfigurationKernel i j C n q p‖)
    {Kt M2 : ℝ} (hK1 : 1 ≤ Kt) (hM2 : 0 ≤ M2) (u : En eta n)
    (hH2 : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) u.ofLp ≤ M2 ^ 2) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs (2 * Real.pi / L) n) a
        (finiteCoefficientKernelOperator κ u)‖ ≤
      Cg * ctailP C Hunit (2 * Real.pi / L) * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hH2' : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) (umod u).ofLp ≤ M2 ^ 2 := by
    rw [fullH2Sq_umod]; exact hH2
  refine (tail_domination κ _ hCg (pairKernel_real i j C) hdom Kt _ a u).trans ?_
  unfold ctailP
  rw [mul_assoc Cg, mul_assoc Cg]
  refine mul_le_mul_of_nonneg_left ?_ hCg
  have hfull := norm_le_of_h1 (tB_nonneg C Hunit _) hM2
    (finiteElectronPairCoulombOperator_h1Bound_of_periodic i j hij _ C _ Hunit n hC hPeriodic
      (tB_scale hC hg)) (umod u) hH2'
  exact tail_regimes hg (kabs_cube_le hL) a _ (tB_nonneg C Hunit _) (tZP_nonneg hg) hM2 hK1 hfull
    (fun h2g hn => pair_tail_releaseP hij a hg hC Hunit hPeriodic hK1 h2g hn hM2 (umod u) hH2')

omit [Fintype ν] in
/-- `tail_single_dominated` (`PlaneWave.Auxiliary.PotentialTails`) under any `H²` budget `M₂`. -/
lemma tail_single_M2P {L : ℝ} (hL : 0 < L) (r a : Fin eta) {C : ℝ} (hC : 0 ≤ C) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (κ : Cfg eta n → Cfg eta n → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hdom : ∀ q p, ‖κ q p‖ ≤ Cg * ‖referenceConfigurationKernel r (finiteCoulombKernel C n) q p‖)
    {Kt M2 : ℝ} (hK1 : 1 ≤ Kt) (hM2 : 0 ≤ M2) (u : En eta n)
    (hH2 : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) u.ofLp ≤ M2 ^ 2) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs (2 * Real.pi / L) n) a
        (finiteCoefficientKernelOperator κ u)‖ ≤
      Cg * ctailP C Hunit (2 * Real.pi / L) * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hH2' : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) (umod u).ofLp ≤ M2 ^ 2 := by
    rw [fullH2Sq_umod]; exact hH2
  refine (tail_domination κ _ hCg (refKernel_real r C) hdom Kt _ a u).trans ?_
  rw [fcko_refKernel]
  unfold ctailP
  rw [mul_assoc Cg, mul_assoc Cg]
  refine mul_le_mul_of_nonneg_left ?_ hCg
  have hfull := norm_le_of_h1 (tB_nonneg C Hunit _) hM2
    (refCoulomb_h1 r hg hC Hunit hPeriodic n) (umod u) hH2'
  exact tail_regimes hg (kabs_cube_le hL) a _ (tB_nonneg C Hunit _) (tZP_nonneg hg) hM2 hK1 hfull
    (fun h2g hn => single_tail_releaseP r a hg hC Hunit hPeriodic hK1 h2g hn hM2 (umod u) hH2')

/-- **The potential tail** (eq:grid-tail for the `g_L` potential): for every register `a`, every
`K ≥ 1` and every state with `H²` budget `M₂`,
`‖1{|k_{p_a}| > K} W_L u‖ ≤ Q (1 + V_θ) c_tail M₂ K^{-1/2}`. -/
theorem gLpot_tail_boundP (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (a : Fin eta)
    {Kt M2 : ℝ} (hK1 : 1 ≤ Kt) (hM2 : 0 ≤ M2) (u : En eta n)
    (hH2 : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) u.ofLp ≤ M2 ^ 2) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs (2 * Real.pi / L) n) a (gLpot sys L θ n u)‖ ≤
      sys.couplingWeight * ((1 + tv R θ) * ctailP (coulombCellAmplitude L ^ 2) Hunit
        (2 * Real.pi / L)) * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
  classical
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hV : 0 ≤ 1 + tv R θ := by linarith [hθ.tv_nonneg]
  have hC : 0 ≤ coulombCellAmplitude L ^ 2 := sq_nonneg _
  set T := (1 + tv R θ) * ctailP (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L) * M2 *
    Kt ^ (-(1 / 2 : ℝ)) with hT
  have hK0 : 0 < Kt := by linarith
  have hT0 : 0 ≤ T := by
    have := ctailP_nonneg (C := coulombCellAmplitude L ^ 2) (Hunit := Hunit) hg
    have := Real.rpow_pos_of_pos hK0 (-(1 / 2 : ℝ))
    positivity
  set kabs := finitePlaneWaveKabs (2 * Real.pi / L) n with hkabs
  have hN : ∀ (a' : Fin eta) (l : ν), ‖referenceTailOperator Kt kabs a
      (referenceKernelConvolutionOperator a' (gLnuc sys.nuclei L θ n l) u)‖ ≤
      sys.nuclei.charge l * T := by
    intro a' l
    have hZ := sys.nuclei.charge_nonneg l
    have h := tail_single_M2P hL a' a hC Hunit hPeriodic
      (referenceConfigurationKernel a' (gLnuc sys.nuclei L θ n l)) (mul_nonneg hZ hV)
      (refKernel_dom a' (gLnuc sys.nuclei L θ n l)
        (fun v w => norm_gLnuc_le hL hθ sys.nuclei n l v w)) hK1 hM2 u hH2
    rw [fcko_refKernel] at h
    refine h.trans (le_of_eq ?_)
    rw [hT]; ring
  have hP : ∀ pair : FiniteElectronPair eta, ‖referenceTailOperator Kt kabs a
      (finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n) u)‖ ≤ T := by
    intro pair
    have h := tail_pair_M2P hL (ne_of_lt pair.2) a hC Hunit hPeriodic
      (finiteElectronPairLiftKernel pair.1.1 pair.1.2 n (gLk L θ n)) hV
      (fun q p => norm_lift_gLk_le hL hθ pair.1.1 pair.1.2 n q p) hK1 hM2 u hH2
    exact h.trans (le_of_eq (by rw [hT]))
  have hExp : referenceTailOperator Kt kabs a (gLpot sys L θ n u) =
      (∑ a' : Fin eta, ((-sys.charge a' : ℝ) : ℂ) • ∑ l : ν, referenceTailOperator Kt kabs a
        (referenceKernelConvolutionOperator a' (gLnuc sys.nuclei L θ n l) u)) +
      ∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) •
        referenceTailOperator Kt kabs a
          (finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n) u) := by
    unfold gLpot
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add, map_sum,
      map_smul]
  have h1 : ‖∑ a' : Fin eta, ((-sys.charge a' : ℝ) : ℂ) • ∑ l : ν, referenceTailOperator Kt kabs a
      (referenceKernelConvolutionOperator a' (gLnuc sys.nuclei L θ n l) u)‖ ≤
      ∑ a' : Fin eta, |sys.charge a'| * ∑ l : ν, sys.nuclei.charge l * T := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
    rw [norm_smul, norm_ofReal_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hN a' l)
  have h2 : ‖∑ pair : FiniteElectronPair eta,
      ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) • referenceTailOperator Kt kabs a
        (finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n) u)‖ ≤
      ∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2| * T := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun pair _ => ?_)
    rw [norm_smul, norm_ofReal']
    exact mul_le_mul_of_nonneg_left (hP pair) (abs_nonneg _)
  rw [hExp]
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  have e1 : ∑ a' : Fin eta, |sys.charge a'| * ∑ l : ν, sys.nuclei.charge l * T =
      (∑ a', |sys.charge a'|) * sys.nuclei.totalCharge * T := by
    unfold FiniteBONuclearData.totalCharge
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← Finset.sum_mul]
    ring
  have e2 : ∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2| * T =
      (∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2|) * T := by
    rw [Finset.sum_mul]
  rw [e1, e2, hT]
  unfold CoulombSystem.couplingWeight
  ring

end TailP

/-! ## The Galerkin energy bound and the cubic error with the sharper constant -/

/-- The tail constant `C_W = Q (1 + V) c_tail M₂`. -/
noncomputable def gLtailConstP (sys : CoulombSystem eta ν) (L V Hunit E0 : ℝ) : ℝ :=
  sys.couplingWeight * ((1 + V) * ctailP (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L)) *
    gLH2Const sys L V Hunit E0

/-- **The Galerkin energy bound for the `g_L` Hamiltonian on the cube.** For a normalised sector
eigenvector of `gLham` with energy `E` (`|E| ≤ E₀`) which is the sector ground energy, and the
cubic Galerkin ground energy `E_N` at cutoff `K` (large: `4 m̄ |E| ≤ K²`,
`32 S₂ C_W² ≤ K⁵`): `0 ≤ E_N - E` and `K³ (E_N - E) ≤ 64 (1/2 + C_pot + |E|) S₁ S₂ C_W²`, with
`C_pot = (1 + V) B Q` and `C_W = Q (1 + V) c_tail m̄ (2 + 8E₀ + 16 B_m²)`. -/
theorem gL_cubic_energy_boundP (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ} (n : ℕ) (K E EN E0 : ℝ)
    (coeff : FourierConfig eta (FinitePlaneWaveMode n) → ℂ)
    (hK1 : 1 ≤ K) (hE0 : 0 ≤ E0) (hEnergy : |E| ≤ E0)
    (hAbsorb : 4 * sys.maxMass * |E| ≤ K ^ 2)
    (hLargeK : 32 * (∑ a, sys.mass a ^ 2) * (gLtailConstP sys L (tv R θ) Hunit E0) ^ 2 ≤ K ^ 5)
    (hSector : IsSectorCoeff sgn lab coeff)
    (hNormalized : (∑ p, coeffMass coeff p) = 1)
    (hEigen : gLham sys L θ n (fullCoeffVector coeff) = (E : ℂ) • fullCoeffVector coeff)
    (hGround : IsSectorGroundEnergy sgn lab (gLham sys L θ n) E)
    (hGalerkin : IsSectorCubicGalerkinGroundEnergy eta sgn lab K (2 * Real.pi / L) n
      (gLham sys L θ n) EN) :
    0 ≤ EN - E ∧ K ^ 3 * (EN - E) ≤
      64 * ((1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit + |E|) * (∑ a, sys.mass a) *
        (∑ a, sys.mass a ^ 2) * (gLtailConstP sys L (tv R θ) Hunit E0) ^ 2 := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hK0 : 0 < K := by linarith
  have hV := hθ.tv_nonneg
  have hH2 := gL_eigen_fullH2Sq_le sys hL hθ Hunit hPeriodic n coeff E E0 hE0 hEnergy
    hNormalized hEigen
  have hM2 := gLH2Const_nonneg sys L (tv R θ) Hunit hE0
  have hPT : ∀ r : Fin eta, ‖referenceTailVector K (finitePlaneWaveKabs (2 * Real.pi / L) n) r
      (operatorPotentialCoeff (gLpot sys L θ n) coeff)‖ ≤
      gLtailConstP sys L (tv R θ) Hunit E0 * K ^ (-(1 / 2 : ℝ)) := by
    intro r
    rw [← referenceTailOperator_potential]
    refine (gLpot_tail_boundP sys hL hθ Hunit hPeriodic r hK1 hM2 (fullCoeffVector coeff)
      hH2).trans (le_of_eq ?_)
    unfold gLtailConstP
    ring
  have hPotential := discarded_potential_form_of_h1OperatorBound K
    (finitePlaneWaveKabs (2 * Real.pi / L) n) coeff (gLpot sys L θ n)
    (gLformConst_nonneg sys L hV Hunit) (gLpot_h1Bound sys hL hθ Hunit hPeriodic n) le_rfl
  exact mass_sector_cubic_energy_bound_of_tail_and_form eta sys.mass sys.maxMass K
    (2 * Real.pi / L) E EN (gLtailConstP sys L (tv R θ) Hunit E0) (K ^ (-(1 / 2 : ℝ)))
    (gLformConst sys L (tv R θ) Hunit) n coeff (gLpot sys L θ n) sys.one_le_mass
    sys.mass_le_maxMass hK1 hg.le (rho_scale hK0).le hPT hAbsorb hSector hNormalized hLargeK
    (gLpot_isSymmetric hθ sys L n) hEigen hGround hGalerkin
    (gLformConst_nonneg sys L hV Hunit) hPotential

/-- **The cubic Galerkin error for the torus ground energy.** For a cube `M` with
`K = (2π/L) M` large (`4 m̄ (|E_L| + 1) ≤ K²`, `32 S₂ C_W² ≤ K⁵`), the sector ground energy `E_M`
of the cube satisfies `0 ≤ E_M - E_L` and `K³ (E_M - E_L) ≤ 64 (1/2 + C_pot + |E_L|) S₁ S₂ C_W²`,
`C_W = gLtailConstP` at the energy budget `|E_L| + 1`. -/
theorem gL_cubic_errorP (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ}
    (hlab : sys.IsAdmissible lab) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {E : ℝ}
    (hE : IsGLTorusGroundEnergy sys lab L θ E) (M : ℕ)
    (hK1 : 1 ≤ (2 * Real.pi / L) * M)
    (hAbsorb : 4 * sys.maxMass * (|E| + 1) ≤ ((2 * Real.pi / L) * M) ^ 2)
    (hLargeK : 32 * (∑ a, sys.mass a ^ 2) * (gLtailConstP sys L (tv R θ) Hunit (|E| + 1)) ^ 2 ≤
      ((2 * Real.pi / L) * M) ^ 5)
    (EM : ℝ) (uM : En eta M) (hS : IsSectorVector sys.sign lab uM) (hn : ‖uM‖ = 1)
    (hEig : gLham sys L θ M uM = (EM : ℂ) • uM)
    (hG : IsSectorGroundEnergy sys.sign lab (gLham sys L θ M) EM) :
    0 ≤ EM - E ∧ ((2 * Real.pi / L) * M) ^ 3 * (EM - E) ≤
      64 * ((1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit + |E|) * (∑ a, sys.mass a) *
        (∑ a, sys.mass a ^ 2) * (gLtailConstP sys L (tv R θ) Hunit (|E| + 1)) ^ 2 := by
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
          (gLtailConstP sys L (tv R θ) Hunit (|E| + 1)) ^ 2) := by
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
    have hb := gL_cubic_energy_boundP sys hL hθ Hunit hPeriodic (h n) K (energy n) EM (|E| + 1)
      (coeff n) hK1 (by positivity) hEn hAbsN hLargeK (hSc n) (hMass n) (hEigc n) (hGc n) hGal
    refine ⟨hb.1, hb.2.trans (le_of_eq ?_)⟩
    ring
  have hLim := cubic_energy_bound_passes_to_limit_factor K E EM
    ((1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit)
    (64 * (∑ a, sys.mass a) * (∑ a, sys.mass a ^ 2) *
      (gLtailConstP sys L (tv R θ) Hunit (|E| + 1)) ^ 2) energy hconv hFinite
  refine ⟨hLim.1, hLim.2.trans (le_of_eq ?_)⟩
  ring

/-- The cubic error constant `64 (1/2 + C_pot + |E|) S₁ S₂ C_W²` at the explicit periodic Hardy
constant (`V` the total variation of `θ`, `E` the torus ground energy). -/
noncomputable def gLCubicConstP (sys : CoulombSystem eta ν) (L V E : ℝ) : ℝ :=
  64 * ((1 / 2 : ℝ) + gLformConst sys L V molecularCanonicalUnitHardyConstant + |E|) *
    (∑ a, sys.mass a) * (∑ a, sys.mass a ^ 2) *
      (gLtailConstP sys L V molecularCanonicalUnitHardyConstant (|E| + 1)) ^ 2

lemma gLCubicConstP_nonneg (sys : CoulombSystem eta ν) (L : ℝ) {V : ℝ} (hV : 0 ≤ V) (E : ℝ) :
    0 ≤ gLCubicConstP sys L V E := by
  unfold gLCubicConstP
  have h1 := gLformConst_nonneg sys L hV molecularCanonicalUnitHardyConstant
  have h2 : 0 ≤ ∑ a, sys.mass a := Finset.sum_nonneg fun a _ => (sys.mass_pos a).le
  have h3 : 0 ≤ ∑ a, sys.mass a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  positivity

/-- An explicit cube threshold for the cubic error (the release's
`coulombExplicitCubicThreshold` at the `g_L` budgets). -/
noncomputable def gLCubicThresholdP (sys : CoulombSystem eta ν) (L V E : ℝ) : ℕ :=
  coulombExplicitCubicThreshold eta (2 * Real.pi / L) sys.maxMass (∑ a, sys.mass a ^ 2) E
    (gLtailConstP sys L V molecularCanonicalUnitHardyConstant (|E| + 1))

/-- **The cubic Galerkin error for the `g_L` torus ground energy, with explicit constants.**
The torus ground energy `E_L` exists, and for every cube `M` above an explicit threshold the
sector ground energy `E_M` of the cube (the cubic Galerkin energy at cutoff `K = (2π/L) M`)
satisfies `0 ≤ E_M - E_L ≤ C / K³`. -/
theorem gL_sector_cubic_errorP (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E ∧
      ∀ M : ℕ, gLCubicThresholdP sys L (tv R θ) E ≤ M →
        ∃ EM : ℝ, ∃ uM : En eta M, IsSectorVector sys.sign lab uM ∧ ‖uM‖ = 1 ∧
          gLham sys L θ M uM = (EM : ℂ) • uM ∧
          IsSectorGroundEnergy sys.sign lab (gLham sys L θ M) EM ∧
          0 ≤ EM - E ∧ EM - E ≤ gLCubicConstP sys L (tv R θ) E / ((2 * Real.pi / L) * M) ^ 3 := by
  obtain ⟨E, hE⟩ := exists_gLTorusGroundEnergy sys hlab hL hθ molecularCanonicalUnitHardyConstant
    canonicalPeriodicCoulombHardyBound_explicit
  refine ⟨E, hE, fun M hM => ?_⟩
  have hg : 0 < 2 * Real.pi / L := by positivity
  obtain ⟨_hm1, hCount, hK, _hGrid, hEnergyA, hTailA⟩ :=
    coulombExplicitCubicThreshold_admissible eta (2 * Real.pi / L) sys.maxMass
      (∑ a, sys.mass a ^ 2) E (gLtailConstP sys L (tv R θ) molecularCanonicalUnitHardyConstant
        (|E| + 1)) hg sys.maxMass_pos.le (Finset.sum_nonneg fun a _ => sq_nonneg _) M hM
  obtain ⟨EM, uM, hS, hn, hEig, hG⟩ := gL_exists_sector_ground sys lab hlab hθ L M
    (by rw [finitePlaneWaveMode_card]; exact hCount)
  have hb := gL_cubic_errorP sys hlab hL hθ molecularCanonicalUnitHardyConstant
    canonicalPeriodicCoulombHardyBound_explicit hE M hK hEnergyA hTailA EM uM hS hn hEig hG
  refine ⟨EM, uM, hS, hn, hEig, hG, hb.1, ?_⟩
  have hKpos : 0 < (2 * Real.pi / L) * M := by linarith
  rw [le_div_iff₀ (pow_pos hKpos 3), mul_comm]
  exact hb.2

end FreeBoundary
