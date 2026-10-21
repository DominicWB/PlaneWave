import PlaneWave.FreeBoundary.TorusGroundEnergy
import PlaneWave.FreeBoundary.RetainedRegion

/-!
# `app:free`, part 8: the position-space `g_L` potential on the configuration torus

In the dimensionless coordinates of the release (`MolecularPositionTorus η`,
`x = r/L`):

* `memLp_gLtorus`: the torus kernel `g_L` is square integrable on `T³`;
* `gLtorus0 = g_L - ĝ_L(0)` (the zero mode removed) has the Fourier coefficients
  `gLlat = ĝ_L` off zero (`mFourierCoeff_gLtorus0`);
* **`gLFourierPotential_fourierCoeff`**: the charge-weighted multiplication function
  `V(x) = Σ_{a<b} q_a q_b g⁰_L(x_a - x_b) + Σ_{a,ℓ} q_a Z_ℓ g⁰_L(x_a + R_ℓ)` (the release's
  Fourier convention for the nuclear positions) has, between the Fourier modes `q` and `p`, exactly
  the coefficient `gLlatPot q p` of the lattice kernel of `PlaneWave.FreeBoundary.TorusGroundEnergy`. So the potential of the
  Fourier-space `g_L` Hamiltonian (`PlaneWave.FreeBoundary.CubeHamiltonian`–`PlaneWave.FreeBoundary.GridEnergy`) is multiplication by `V`, and with the zero
  mode added back by the function `g_L` itself (`V + ĝ_L(0) (Σ_{a<b} q_a q_b + Σ_{a,ℓ} q_a Z_ℓ)`).

The proofs use the release's coefficient lemmas for pullbacks to a pair difference and to a
translated particle coordinate (`molecularPositionDifference_fourierCoeff_transfer`,
`molecularPositionParticle_fourierCoeff_transfer`, `unitTorus3_fourierCoeff_add_right`).
-/

set_option autoImplicit false

open MeasureTheory Set Real PlaneWaveCertificate
open scoped InnerProductSpace

namespace FreeBoundary

noncomputable section

/-- The unit-circle measure of Mathlib's `UnitAddTorus.mFourierLp`, as in the release. -/
local instance unitAddCircleMeasureSpaceFB8 : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

local instance unitAddCircleProbabilityMeasureFB8 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  instIsProbabilityMeasureUnitAddCircleVolume

local instance unitTorus3FiniteMeasureFB8 : IsFiniteMeasure (volume : Measure UnitTorus3) := by
  infer_instance

local instance unitTorus3RightInvariantFB8 :
    Measure.IsAddRightInvariant (volume : Measure UnitTorus3) :=
  Measure.pi.isAddRightInvariant (fun _ : Fin 3 => AddCircle.haarAddCircle)

variable {R : ℝ} {θ : ℝ → ℝ}

/-! ## The torus kernel is square integrable -/

lemma cellRep_inCell {L : ℝ} (hL : 0 ≤ L) (t : UnitAddTorus (Fin 3)) (c : Fin 3) :
    |cellRep L t c| ≤ L / 2 := by
  have h := (AddCircle.equivIoc 1 (-1 / 2 : ℝ) (t c)).2
  change |L * ((AddCircle.equivIoc 1 (-1 / 2 : ℝ) (t c) : ℝ))| ≤ L / 2
  rw [abs_mul, abs_of_nonneg hL]
  have h' : |((AddCircle.equivIoc 1 (-1 / 2 : ℝ) (t c) : ℝ))| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  nlinarith

lemma gLtorus_eq_gker {L : ℝ} (hL : 0 ≤ L) (θ : ℝ → ℝ) (t : UnitAddTorus (Fin 3)) :
    gLtorus L θ t = (gker θ (cellRep L t) : ℂ) := by
  unfold gLtorus
  rw [gLni_eq_gker hL θ (cellRep_inCell hL t)]

lemma measurable_gker (hθ : Profile R θ) : Measurable (gker θ) := by
  unfold gker
  exact (hθ.cont.measurable.comp measurable_norm).div measurable_norm

lemma memLp_gker_scaled (hθ : Profile R θ) {L : ℝ} (hL : 0 < L) :
    MemLp (fun y : E3 => (gker θ (L • y) : ℂ)) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun y : E3 => (gker θ (L • y) : ℂ)) volume :=
    (Complex.measurable_ofReal.comp ((measurable_gker hθ).comp
      (measurable_const_smul L))).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hrad : (fun y : E3 => ‖(gker θ (L • y) : ℂ)‖ ^ 2) =
      fun y => (fun r : ℝ => (θ (L * r) / (L * r)) ^ 2) ‖y‖ := by
    funext y
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    unfold gker
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  rw [hrad]
  refine (integrable_fun_norm_addHaar (volume : Measure E3)
    (f := fun r : ℝ => (θ (L * r) / (L * r)) ^ 2)).mpr ?_
  rw [finrank_euclideanSpace_fin]
  have hcont : Continuous (fun r : ℝ => θ (L * r) ^ 2 / L ^ 2) := by
    have := hθ.cont
    fun_prop
  have h1 : IntegrableOn (fun r : ℝ => θ (L * r) ^ 2 / L ^ 2) (Icc 0 (R / L)) :=
    hcont.integrableOn_Icc
  refine (h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun r hr => ?_).congr_fun
    (fun r hr => ?_) measurableSet_Ioi
  · have hr' : R / L < r := by
      rcases hr with ⟨h0, h1⟩
      simp only [mem_Icc, not_and, not_le] at h1
      exact h1 (le_of_lt h0)
    have hLr : R ≤ L * r := by
      rw [div_lt_iff₀ hL] at hr'
      linarith
    rw [hθ.vanish _ hLr]
    simp
  · have hr0 : r ≠ 0 := (mem_Ioi.mp hr).ne'
    have hL0 : L ≠ 0 := hL.ne'
    simp only [smul_eq_mul, show (3 : ℕ) - 1 = 2 from rfl]
    field_simp

/-- **The torus kernel `g_L` is square integrable on `T³`.** -/
theorem memLp_gLtorus {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) :
    MemLp (gLtorus L θ) 2 volume := by
  set a : Fin 3 → ℝ := fun _ => -1 / 2 with ha
  have hS : MeasurableSet {x : Fin 3 → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)} := by
    have hSeq : {x : Fin 3 → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)} =
        ⋂ i : Fin 3, (fun x : Fin 3 → ℝ => x i) ⁻¹' Ioc (a i) (a i + 1) := by
      ext x
      simp
    rw [hSeq]
    exact MeasurableSet.iInter fun i => measurableSet_Ioc.preimage (measurable_pi_apply i)
  have hG : MemLp (fun x : Fin 3 → ℝ => (gker θ (L • (WithLp.toLp 2 x : E3)) : ℂ)) 2 volume :=
    (memLp_gker_scaled hθ hL).comp_measurePreserving (PiLp.volume_preserving_toLp (Fin 3))
  have hGS := (hG.restrict _).comp_measurePreserving (measurePreserving_subtype_coe hS)
  have hT := hGS.comp_measurePreserving (UnitAddTorus.measurePreserving_equivPiIoc a)
  convert hT using 1
  funext t
  rw [gLtorus_eq_gker hL.le]
  simp only [Function.comp_apply, UnitAddTorus.coe_measurableEquivPiIoc_apply]
  congr 2

/-! ## The zero mode removed -/

/-- The torus kernel without its zero mode. -/
noncomputable def gLtorus0 (L : ℝ) (θ : ℝ → ℝ) (t : UnitAddTorus (Fin 3)) : ℂ :=
  gLtorus L θ t - ghat L θ (fun _ => 0)

lemma integral_mFourier (n : Fin 3 → ℤ) :
    ∫ x : UnitAddTorus (Fin 3), UnitAddTorus.mFourier n x = if n = 0 then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin 3)) 0 n
  rw [ContinuousMap.inner_toLp] at h
  simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, map_one, mul_one] at h
  rw [h]
  by_cases hn : n = 0
  · rw [if_pos hn.symm, if_pos hn]
  · rw [if_neg (Ne.symm hn), if_neg hn]

lemma mFourierCoeff_const (c : ℂ) (n : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun _ : UnitAddTorus (Fin 3) => c) n =
      if n = 0 then c else 0 := by
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  rw [integral_mul_const, integral_mFourier]
  by_cases hn : n = 0
  · rw [if_pos (by rw [hn, neg_zero]), if_pos hn, one_mul]
  · rw [if_neg (by intro h; exact hn (neg_eq_zero.mp h)), if_neg hn, zero_mul]

lemma memLp_gLtorus0 {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) :
    MemLp (gLtorus0 L θ) 2 volume :=
  (memLp_gLtorus hL hθ).sub (memLp_const _)

/-- `g_L - ĝ_L(0)` has the coefficients `ĝ_L` off zero and `0` at zero. -/
theorem mFourierCoeff_gLtorus0 {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2)
    (n : Lattice3) : UnitAddTorus.mFourierCoeff (gLtorus0 L θ) n = gLlat L θ n := by
  classical
  unfold gLtorus0
  rw [torus_mFourierCoeff_sub_of_memLp _ _ (memLp_gLtorus hL hθ) (memLp_const _),
    mFourierCoeff_gLtorus hL hθ hR, mFourierCoeff_const]
  unfold gLlat
  by_cases hn : n = (fun _ => 0)
  · have hn' : n = 0 := hn
    rw [if_pos hn', if_pos hn, hn, sub_self]
  · have hn' : n ≠ 0 := hn
    rw [if_neg hn', if_neg hn, sub_zero]

/-! ## The multiplication function on the configuration torus -/

section Potential

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- The charge-weighted `g_L` multiplication function (zero mode removed) on the configuration
torus, in the release's Fourier convention for the nuclear positions (`x_a + R_ℓ`). -/
noncomputable def gLFourierPotential (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (x : MolecularPositionTorus eta) : ℂ :=
  (∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
      gLtorus0 L θ (molecularPositionDifference pair.1.1 pair.1.2 x)) +
    ∑ i : Fin eta, ((sys.charge i : ℝ) : ℂ) *
      ∑ ell : ν, (sys.nuclei.charge ell : ℂ) *
        gLtorus0 L θ (molecularPositionNuclearArgument i (sys.nuclei.position ell) x)

lemma pair_memLp {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) {i j : Fin eta} (hij : i ≠ j) :
    MemLp (fun x : MolecularPositionTorus eta =>
      gLtorus0 L θ (molecularPositionDifference i j x)) 2 volume :=
  (memLp_gLtorus0 hL hθ).comp_measurePreserving
    (molecularPositionDifference_measurePreserving i j hij)

lemma translate_memLp {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (Rn : UnitTorus3) :
    MemLp (fun y : UnitTorus3 => gLtorus0 L θ (y + Rn)) 2 volume :=
  (memLp_gLtorus0 hL hθ).comp_measurePreserving
    (measurePreserving_add_right (volume : Measure UnitTorus3) Rn)

lemma nuclear_memLp {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (i : Fin eta) (Rn : UnitTorus3) :
    MemLp (fun x : MolecularPositionTorus eta =>
      gLtorus0 L θ (molecularPositionNuclearArgument i Rn x)) 2 volume :=
  (memLp_gLtorus0 hL hθ).comp_measurePreserving
    (molecularPositionNuclearArgument_measurePreserving i Rn)

theorem gLFourierPotential_memLp (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) : MemLp (gLFourierPotential sys L θ) 2 volume := by
  have hPair : MemLp (fun x : MolecularPositionTorus eta =>
      ∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
        gLtorus0 L θ (molecularPositionDifference pair.1.1 pair.1.2 x)) 2 volume := by
    apply memLp_finsetSum
    intro pair _
    exact (pair_memLp hL hθ (ne_of_lt pair.2)).const_mul _
  have hNuclear : MemLp (fun x : MolecularPositionTorus eta =>
      ∑ i : Fin eta, ((sys.charge i : ℝ) : ℂ) *
        ∑ ell : ν, (sys.nuclei.charge ell : ℂ) *
          gLtorus0 L θ (molecularPositionNuclearArgument i (sys.nuclei.position ell) x))
      2 volume := by
    apply memLp_finsetSum
    intro i _
    apply MemLp.const_mul
    apply memLp_finsetSum
    intro ell _
    exact (nuclear_memLp hL hθ i (sys.nuclei.position ell)).const_mul _
  exact hPair.add hNuclear

/-- The pair term has exactly the pair lattice kernel. -/
lemma pair_fourierCoeff {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2)
    {i j : Fin eta} (hij : i ≠ j) (q p : FourierConfig eta Lattice3) :
    UnitAddTorus.mFourierCoeff (fun x : MolecularPositionTorus eta =>
        gLtorus0 L θ (molecularPositionDifference i j x))
        (molecularFourierIndexEquiv eta q - molecularFourierIndexEquiv eta p) =
      gLlatPair i j L θ q p := by
  classical
  rw [molecularPositionDifference_fourierCoeff_transfer i j hij _ (memLp_gLtorus0 hL hθ),
    mFourierCoeff_gLtorus0 hL hθ hR]
  unfold gLlatPair
  rfl

omit [Fintype ν] in
/-- The nuclear term has exactly the nuclear lattice kernel. -/
lemma nuclear_fourierCoeff {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2)
    (data : FiniteBONuclearData ν) (i : Fin eta) (ell : ν) (q p : FourierConfig eta Lattice3) :
    -(data.charge ell : ℂ) * UnitAddTorus.mFourierCoeff (fun x : MolecularPositionTorus eta =>
        gLtorus0 L θ (molecularPositionNuclearArgument i (data.position ell) x))
        (molecularFourierIndexEquiv eta q - molecularFourierIndexEquiv eta p) =
      latticeReferenceConfigurationKernel i (gLlatNuc data L θ ell) q p := by
  classical
  change -(data.charge ell : ℂ) * UnitAddTorus.mFourierCoeff
    (fun x : MolecularPositionTorus eta =>
      (fun y : UnitTorus3 => gLtorus0 L θ (y + data.position ell))
        (molecularPositionParticle i x)) _ = _
  rw [molecularPositionParticle_fourierCoeff_transfer i _ (translate_memLp hL hθ _),
    latticeReferenceConfigurationKernel]
  split_ifs
  · rw [unitTorus3_fourierCoeff_add_right, mFourierCoeff_gLtorus0 hL hθ hR, gLlatNuc]
  · exact mul_zero _

/-- **The `g_L` multiplication function has exactly the potential lattice kernel.** -/
theorem gLFourierPotential_fourierCoeff (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (hR : R ≤ L / 2) (q p : FourierConfig eta Lattice3) :
    UnitAddTorus.mFourierCoeff (gLFourierPotential sys L θ)
        (molecularFourierIndexEquiv eta q - molecularFourierIndexEquiv eta p) =
      gLlatPot sys L θ q p := by
  classical
  have hPairW : ∀ pair : FiniteElectronPair eta,
      MemLp (fun x : MolecularPositionTorus eta =>
        ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
          gLtorus0 L θ (molecularPositionDifference pair.1.1 pair.1.2 x)) 2 volume :=
    fun pair => (pair_memLp hL hθ (ne_of_lt pair.2)).const_mul _
  have hNucW : ∀ (i : Fin eta) (ell : ν),
      MemLp (fun x : MolecularPositionTorus eta => (sys.nuclei.charge ell : ℂ) *
        gLtorus0 L θ (molecularPositionNuclearArgument i (sys.nuclei.position ell) x))
        2 volume :=
    fun i ell => (nuclear_memLp hL hθ i _).const_mul _
  have hNucSum : ∀ i : Fin eta, MemLp (fun x : MolecularPositionTorus eta =>
      ∑ ell : ν, (sys.nuclei.charge ell : ℂ) *
        gLtorus0 L θ (molecularPositionNuclearArgument i (sys.nuclei.position ell) x))
        2 volume :=
    fun i => memLp_finsetSum _ (fun ell _ => hNucW i ell)
  have hNucSumW : ∀ i : Fin eta, MemLp (fun x : MolecularPositionTorus eta =>
      ((sys.charge i : ℝ) : ℂ) * ∑ ell : ν, (sys.nuclei.charge ell : ℂ) *
        gLtorus0 L θ (molecularPositionNuclearArgument i (sys.nuclei.position ell) x))
        2 volume :=
    fun i => (hNucSum i).const_mul _
  have hPairSum : MemLp (fun x : MolecularPositionTorus eta =>
      ∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
        gLtorus0 L θ (molecularPositionDifference pair.1.1 pair.1.2 x)) 2 volume :=
    memLp_finsetSum _ (fun pair _ => hPairW pair)
  have hAllNuc : MemLp (fun x : MolecularPositionTorus eta =>
      ∑ i : Fin eta, ((sys.charge i : ℝ) : ℂ) * ∑ ell : ν, (sys.nuclei.charge ell : ℂ) *
        gLtorus0 L θ (molecularPositionNuclearArgument i (sys.nuclei.position ell) x))
        2 volume :=
    memLp_finsetSum _ (fun i _ => hNucSumW i)
  unfold gLFourierPotential gLlatPot
  rw [torus_mFourierCoeff_add_of_memLp _ _ hPairSum hAllNuc,
    torus_mFourierCoeff_fintypeSum_of_memLp _ hPairW,
    torus_mFourierCoeff_fintypeSum_of_memLp _ hNucSumW, add_comm]
  simp_rw [torus_mFourierCoeff_const_mul]
  simp_rw [torus_mFourierCoeff_fintypeSum_of_memLp _ (hNucW _), torus_mFourierCoeff_const_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ell _ => ?_
    rw [← nuclear_fourierCoeff hL hθ hR sys.nuclei i ell q p]
    push_cast
    ring
  · refine Finset.sum_congr rfl fun pair _ => ?_
    rw [pair_fourierCoeff hL hθ hR (ne_of_lt pair.2) q p]

end Potential

end

end FreeBoundary
