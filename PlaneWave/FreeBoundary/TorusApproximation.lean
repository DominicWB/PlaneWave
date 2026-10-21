import PlaneWave.FreeBoundary.AgmonApproximation

/-!
# Free-space regularity, part 9: approximate torus ground states

The lower bound of `prop:free` takes normalised `C²` torus states of the sector with energy
`≤ E_L + ε` and small mass outside the retained region. The manuscript assumes instead the
weighted bound (A) for the torus ground state `u_L`. Here `u_L` is an `H²` state `u` (weighted
Fourier coordinates) of the sector with `‖u‖ = 1` and `Re⟨u, H u⟩ ≤ E` for the completed `g_L`
operator `H`. Its cubic Fourier truncations are trigonometric polynomials (`C²`), lie in the sector
and converge to `u` in `H²`, so their normalised energies converge to `Re⟨u, H u⟩` and their masses
on any set converge to that of `u_L`.

* `torusEnergy_eq_form`: the torus energy of a `C²` state is the form of `H` at its `H²`
  coordinates;
* `h2Test`, `h2Test_toLp`, `h2Test_sector`: the truncations as continuous test functions, with
  pointwise exchange symmetry;
* **`approx_torus_ground`**: approximate ground states with mass `≤ τ` on a set where `u_L` has
  mass `< τ`;
* **`approx_torus_agmon`**: under `Σ_i ∫ e^{2β(|x_i| - R')} |u_L|² ≤ A'` (cell coordinates), mass
  `≤ 2 max(A', 1) e^{-2β(d - R')}` outside `{every |x_i| < d}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15
  molecularTorusFiniteMeasureFB15

local instance unitAddCircleOpenPosFB48 : (volume : Measure UnitAddCircle).IsOpenPosMeasure := by
  change (AddCircle.haarAddCircle : Measure UnitAddCircle).IsOpenPosMeasure
  infer_instance

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The torus energy as a form -/

/-- **The torus energy of a `C²` state is the form of the completed operator** at its `H²`
coordinates `v`. -/
theorem torusEnergy_eq_form (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (hR : R ≤ L / 2)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (v : MolecularFourierH2 eta) (w : C(MolecularPositionTorus eta, ℂ))
    (hw : ContDiff ℝ 2 (torusRealLift w))
    (hvw : molecularPositionH2StateMap eta (2 * Real.pi / L) v =
      (ContinuousMap.toLp 2 volume ℂ) w) :
    torusEnergy sys L θ w hw =
      (inner ℂ (molecularH2StateMap eta (2 * Real.pi / L) v) (H v)).re := by
  obtain ⟨u, hu, hk⟩ := coulombPositionContDiffTest_exists_H2 sys L w hw
  have huv : u = v := by
    apply molecularH2StateMap_injective eta (2 * Real.pi / L)
    apply (molecularPositionSynthesis eta).injective
    rw [← molecularPositionH2StateMap_apply, ← molecularPositionH2StateMap_apply, hu, hvw]
  rw [← huv]
  have hcT := w.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure (MolecularPositionTorus eta))
  have hTmem : MemLp (fun x => w x) ⊤ volume :=
    memLp_top_of_bound w.continuous.aestronglyMeasurable ‖w‖
      (ae_of_all _ fun x => w.norm_coe_le_norm x)
  have hpmem : MemLp (fun x => gLFourierPotential sys L θ x * w x) 2 volume :=
    hTmem.mul' (gLFourierPotential_memLp sys hL hθ)
  have hp : HasL2PointwisePotential volume (gLFourierPotential sys L θ)
      ((ContinuousMap.toLp 2 volume ℂ) w) (hpmem.toLp _) := by
    filter_upwards [hpmem.coeFn_toLp, hcT] with x h1 h2
    rw [h1, h2]
  have hpot : coulombPositionPotentialH2 sys (2 * Real.pi / L) H u = hpmem.toLp _ := by
    have h := gLPositionPotentialH2_pointwise sys L θ H hKernel (gLFourierPotential sys L θ)
      (gLFourierPotential_memLp sys hL hθ) (gLFourierPotential_fourierCoeff sys hL hθ hR) u
    rw [hu] at h
    exact h.unique hp
  have hinner : inner ℂ (molecularH2StateMap eta (2 * Real.pi / L) u) (H u) =
      inner ℂ ((ContinuousMap.toLp 2 volume ℂ) w) (molecularPositionHamiltonianH2 H u) := by
    rw [← hu, molecularPositionH2StateMap_apply, molecularPositionHamiltonianH2_apply,
      LinearIsometryEquiv.inner_map_map]
  rw [hinner, coulombPositionHamiltonianH2_decomposition sys (2 * Real.pi / L) H u, hk, hpot,
    inner_add_right, Complex.add_re]
  have hkin : (inner ℂ ((ContinuousMap.toLp 2 volume ℂ) w)
      ((ContinuousMap.toLp 2 volume ℂ) (coulombPositionContDiffKinetic sys L w hw))).re =
      (∫ x, coulombPositionContDiffKinetic sys L w hw x * conj (w x)).re := by
    rw [ContinuousMap.inner_toLp]
  have hae : (fun x => inner ℂ (((ContinuousMap.toLp 2 volume ℂ) w) x) ((hpmem.toLp _) x))
      =ᵐ[volume] fun x => gLFourierPotential sys L θ x * w x * conj (w x) := by
    filter_upwards [hp, hcT] with x h1 h2
    rw [RCLike.inner_apply, h1, h2]
  have hint : Integrable (fun x => gLFourierPotential sys L θ x * w x * conj (w x)) :=
    (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) _ _).congr hae
  have hpot' : (inner ℂ ((ContinuousMap.toLp 2 volume ℂ) w) (hpmem.toLp _)).re =
      ∫ x, (gLFourierPotential sys L θ x).re * ‖w x‖ ^ 2 := by
    rw [MeasureTheory.L2.inner_def, integral_congr_ae hae]
    rw [← RCLike.re_to_complex, ← integral_re hint]
    congr 1
    funext x
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, RCLike.re_to_complex]
    exact Complex.re_mul_ofReal _ _
  rw [hkin, hpot']
  rfl

/-! ## Fourier truncations as test functions -/

/-- The cubic Fourier truncation of an `H²` state, as a continuous trigonometric polynomial. -/
def h2Test (g : ℝ) (N : ℕ) (v : MolecularFourierH2 eta) : C(MolecularPositionTorus eta, ℂ) :=
  molecularPositionFourierTest eta (fourierConfigCube eta N) (molecularH2Coeff g v)

lemma contDiff_h2Test (g : ℝ) (N : ℕ) (v : MolecularFourierH2 eta) :
    ContDiff ℝ 2 (torusRealLift (h2Test g N v)) :=
  contDiff_two_molecularPositionFourierTest_realLift eta _ _

lemma h2Test_toLp (g : ℝ) (N : ℕ) (v : MolecularFourierH2 eta) :
    (ContinuousMap.toLp 2 volume ℂ) (h2Test g N v) =
      molecularPositionH2StateMap eta g (molecularH2Truncate N v) :=
  molecularPositionFourierTest_cube_toLp eta g v N

lemma isSectorCoeff_cube {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ}
    {c : FourierConfig eta Lattice3 → ℂ} (hS : IsSectorCoeff sgn lab c) (N : ℕ) :
    IsSectorCoeff sgn lab (fun p => if p ∈ fourierConfigCube eta N then c p else 0) := by
  intro i j hij hl p
  dsimp only
  by_cases hp : p ∈ fourierConfigCube eta N
  · rw [if_pos ((mem_fourierConfigCube_swap_iff N i j p).mpr hp), if_pos hp]
    exact hS i j hij hl p
  · rw [if_neg (fun h => hp ((mem_fourierConfigCube_swap_iff N i j p).mp h)), if_neg hp,
      mul_zero]

/-- The truncations of a state of the sector are pointwise in the sector. -/
lemma h2Test_sector {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ} (g : ℝ) (N : ℕ)
    {v : MolecularFourierH2 eta} (hS : IsSectorCoeff sgn lab (molecularH2Coeff g v))
    (i j : Fin eta) (hij : i ≠ j) (hl : lab i = lab j) (x : MolecularPositionTorus eta) :
    h2Test g N v (molecularPositionSwap i j x) = sgn i * h2Test g N v x := by
  have hsec : IsPositionSector sgn lab ((ContinuousMap.toLp 2 volume ℂ) (h2Test g N v)) := by
    rw [molecularPosition_sector_iff]
    intro i j hij hl p
    simp only [h2Test, molecularPositionFourierTest_fourierCoeff]
    exact isSectorCoeff_cube hS N i j hij hl p
  have hcT := (h2Test g N v).coeFn_toLp (p := 2) (𝕜 := ℂ)
    (volume : Measure (MolecularPositionTorus eta))
  have h1 : (fun x => h2Test g N v (molecularPositionSwap i j x)) =ᵐ[volume]
      fun x => sgn i * h2Test g N v x := by
    filter_upwards [hsec i j hij hl, hcT,
      (molecularPositionSwap_measurePreserving i j).quasiMeasurePreserving.ae hcT] with x h1 h2 h3
    rw [← h3, h1, h2]
  have hc1 : Continuous fun x => h2Test g N v (molecularPositionSwap i j x) :=
    (h2Test g N v).continuous.comp (continuous_pi fun a => continuous_apply _)
  have hc2 : Continuous fun x => sgn i * h2Test g N v x :=
    continuous_const.mul (h2Test g N v).continuous
  exact congrFun ((Continuous.ae_eq_iff_eq volume hc1 hc2).mp h1) x

lemma h2Truncate_smul (N : ℕ) (c : ℂ) (v : MolecularFourierH2 eta) :
    molecularH2Truncate N (c • v) = c • molecularH2Truncate N v := by
  apply lp.ext
  funext p
  rw [lp.coeFn_smul, Pi.smul_apply, molecularH2Truncate, molecularH2Truncate, lpTruncate_apply,
    lpTruncate_apply, lp.coeFn_smul, Pi.smul_apply]
  split_ifs <;> simp

lemma molecularH2Coeff_smul (g : ℝ) (c : ℂ) (v : MolecularFourierH2 eta)
    (p : FourierConfig eta Lattice3) :
    molecularH2Coeff g (c • v) p = c * molecularH2Coeff g v p := by
  unfold molecularH2Coeff
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

lemma integral_sq_eq_toLp (w : C(MolecularPositionTorus eta, ℂ))
    (T : Set (MolecularPositionTorus eta)) :
    ∫ x in T, ‖w x‖ ^ 2 = ∫ x in T, ‖(ContinuousMap.toLp 2 volume ℂ) w x‖ ^ 2 := by
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae ((w.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (volume : Measure (MolecularPositionTorus eta))))] with x hx
  rw [hx]

/-! ## Approximate ground states on the torus -/

/-- **Approximate torus ground states from an `H²` state**: if `u` (weighted Fourier coordinates)
lies in the sector, `‖u_L‖ = 1` and `Re⟨u, H u⟩ ≤ E`, and `u_L` has mass `< τ` on `T`, then for
every `ε > 0` there is a normalised `C²` torus state of the sector (pointwise exchange symmetry)
with torus energy `≤ E + ε` and mass `≤ τ` on `T`. -/
theorem approx_torus_ground (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ) {L R : ℝ}
    {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (u : MolecularFourierH2 eta)
    (hS : IsSectorCoeff sys.sign lab (molecularH2Coeff (2 * Real.pi / L) u))
    (hn : ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ = 1) {E : ℝ}
    (hE : (inner ℂ (molecularH2StateMap eta (2 * Real.pi / L) u) (H u)).re ≤ E)
    (T : Set (MolecularPositionTorus eta)) {τ : ℝ}
    (hτ : ∫ x in T, ‖molecularPositionH2StateMap eta (2 * Real.pi / L) u x‖ ^ 2 < τ) :
    ∀ ε > 0, ∃ w : C(MolecularPositionTorus eta, ℂ), ∃ hw : ContDiff ℝ 2 (torusRealLift w),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, w (molecularPositionSwap i j x) = sys.sign i * w x) ∧
      ∫ x, ‖w x‖ ^ 2 = 1 ∧ torusEnergy sys L θ w hw ≤ E + ε ∧ ∫ x in T, ‖w x‖ ^ 2 ≤ τ := by
  intro ε hε
  set g := 2 * Real.pi / L with hg
  have hT := molecularH2Truncate_tendsto u
  -- the three convergent quantities
  have ha : Tendsto (fun N => molecularH2StateMap eta g (molecularH2Truncate N u)) atTop
      (𝓝 (molecularH2StateMap eta g u)) :=
    ((molecularH2StateMap eta g).continuous.tendsto u).comp hT
  have hHt : Tendsto (fun N => H (molecularH2Truncate N u)) atTop (𝓝 (H u)) :=
    (H.continuous.tendsto u).comp hT
  have hU : Tendsto (fun N => molecularPositionH2StateMap eta g (molecularH2Truncate N u)) atTop
      (𝓝 (molecularPositionH2StateMap eta g u)) :=
    ((molecularPositionH2StateMap eta g).continuous.tendsto u).comp hT
  have hEt : Tendsto (fun N => (inner ℂ (molecularH2StateMap eta g (molecularH2Truncate N u))
      (H (molecularH2Truncate N u))).re) atTop
      (𝓝 (inner ℂ (molecularH2StateMap eta g u) (H u)).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp (ha.inner hHt)
  have hNt : Tendsto (fun N => ‖molecularH2StateMap eta g (molecularH2Truncate N u)‖ ^ 2) atTop
      (𝓝 1) := by
    have := (ha.norm).pow 2
    rwa [hn, one_pow] at this
  have hTt := setIntegral_sq_tendsto T hU
  have hq1 := hEt.div hNt one_ne_zero
  have hq2 := hTt.div hNt one_ne_zero
  rw [div_one] at hq1 hq2
  have ev1 : ∀ᶠ N in atTop, (inner ℂ (molecularH2StateMap eta g (molecularH2Truncate N u))
      (H (molecularH2Truncate N u))).re /
        ‖molecularH2StateMap eta g (molecularH2Truncate N u)‖ ^ 2 < E + ε :=
    hq1.eventually (gt_mem_nhds (by linarith))
  have ev2 : ∀ᶠ N in atTop, (∫ x in T, ‖molecularPositionH2StateMap eta g
      (molecularH2Truncate N u) x‖ ^ 2) /
        ‖molecularH2StateMap eta g (molecularH2Truncate N u)‖ ^ 2 < τ :=
    hq2.eventually (gt_mem_nhds hτ)
  have ev3 : ∀ᶠ N in atTop, (1 : ℝ) / 2 <
      ‖molecularH2StateMap eta g (molecularH2Truncate N u)‖ ^ 2 :=
    hNt.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨N, h1, h2, h3⟩ := (ev1.and (ev2.and ev3)).exists
  -- the normalised truncation
  set a := molecularH2StateMap eta g (molecularH2Truncate N u) with ha_def
  have ha0 : 0 < ‖a‖ := by
    by_contra hc
    have : ‖a‖ = 0 := le_antisymm (not_lt.mp hc) (norm_nonneg _)
    rw [this] at h3
    norm_num at h3
  set c : ℝ := ‖a‖⁻¹ with hc
  have hc2 : c ^ 2 * ‖a‖ ^ 2 = 1 := by
    rw [hc, inv_pow]
    field_simp
  set w := h2Test g N ((c : ℂ) • u) with hw_def
  have hw : ContDiff ℝ 2 (torusRealLift w) := contDiff_h2Test g N _
  have hwL : (ContinuousMap.toLp 2 volume ℂ) w =
      (c : ℂ) • molecularPositionH2StateMap eta g (molecularH2Truncate N u) := by
    rw [hw_def, h2Test_toLp, h2Truncate_smul, map_smul]
  have hnorm : ∀ z : ℂ, ‖(c : ℂ) * z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := fun z => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hmass : ∀ S : Set (MolecularPositionTorus eta), ∫ x in S, ‖w x‖ ^ 2 =
      c ^ 2 * ∫ x in S, ‖molecularPositionH2StateMap eta g (molecularH2Truncate N u) x‖ ^ 2 := by
    intro S
    rw [integral_sq_eq_toLp, hwL, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (c : ℂ)
      (molecularPositionH2StateMap eta g (molecularH2Truncate N u)))] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul, hnorm]
  refine ⟨w, hw, fun i j hij hl x => ?_, ?_, ?_, ?_⟩
  · refine h2Test_sector g N ?_ i j hij hl x
    intro i j hij hl p
    rw [molecularH2Coeff_smul, molecularH2Coeff_smul, hS i j hij hl p]
    ring
  · have h := hmass univ
    rw [setIntegral_univ, setIntegral_univ] at h
    rw [h, ← norm_sq_L2_eq, molecularPositionH2StateMap_apply, molecularPositionSynthesis_norm,
      ← ha_def, hc2]
  · rw [torusEnergy_eq_form sys hL hθ hR H hKernel _ w hw (h2Test_toLp g N _).symm,
      h2Truncate_smul, map_smul, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    have e : ((c : ℂ) * ((c : ℂ) * inner ℂ a (H (molecularH2Truncate N u)))).re =
        (inner ℂ a (H (molecularH2Truncate N u))).re / ‖a‖ ^ 2 := by
      rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul, hc]
      field_simp
    rw [← ha_def, e]
    exact h1.le
  · rw [hmass]
    have e : c ^ 2 * ∫ x in T, ‖molecularPositionH2StateMap eta g (molecularH2Truncate N u) x‖ ^ 2 =
        (∫ x in T, ‖molecularPositionH2StateMap eta g (molecularH2Truncate N u) x‖ ^ 2) /
          ‖a‖ ^ 2 := by
      rw [hc, inv_pow]
      ring
    rw [e]
    exact h2.le

/-! ## Assumption (A) for the ground state -/

lemma abs_cellCoord_le {L : ℝ} (hL : 0 ≤ L) (x : MolecularPositionTorus eta)
    (a : Fin eta × Fin 3) : |cellCoord L x a| ≤ L / 2 := by
  unfold cellCoord
  have hm := (AddCircle.equivIoc 1 (-1 / 2 : ℝ) (x a)).2
  rw [abs_mul, abs_of_nonneg hL]
  have h : |((AddCircle.equivIoc 1 (-1 / 2 : ℝ) (x a)) : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hm.1, hm.2]
  nlinarith

lemma norm_particle_cellCoord_le {L : ℝ} (hL : 0 ≤ L) (x : MolecularPositionTorus eta)
    (i : Fin eta) : ‖particle (cellCoord L x) i‖ ≤ L := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨hL, ?_⟩
  have hc : ∀ c : Fin 3, ‖(particle (cellCoord L x) i).ofLp c‖ ^ 2 ≤ (L / 2) ^ 2 := by
    intro c
    change ‖cellCoord L x (i, c)‖ ^ 2 ≤ (L / 2) ^ 2
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_cellCoord_le hL x (i, c)) 2
  calc ∑ c, ‖(particle (cellCoord L x) i).ofLp c‖ ^ 2 ≤ ∑ _c : Fin 3, (L / 2) ^ 2 :=
        Finset.sum_le_sum fun c _ => hc c
    _ = 3 * (L / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
    _ ≤ L ^ 2 := by nlinarith

/-- **Approximate torus ground states under (A)**: if moreover
`Σ_i ∫ e^{2β(|x_i| - R')} |u_L|² ≤ A'` (`x_i` in cell coordinates), the approximate ground states
can be chosen with mass `≤ 2 max(A', 1) e^{-2β(d - R')}` outside `{every |x_i| < d}`. -/
theorem approx_torus_agmon (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ) {L R : ℝ}
    {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (u : MolecularFourierH2 eta)
    (hS : IsSectorCoeff sys.sign lab (molecularH2Coeff (2 * Real.pi / L) u))
    (hn : ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ = 1) {E : ℝ}
    (hE : (inner ℂ (molecularH2StateMap eta (2 * Real.pi / L) u) (H u)).re ≤ E)
    {β A' R' : ℝ} (hβ : 0 ≤ β)
    (hA : ∑ i, ∫ x, Real.exp (2 * β * (‖particle (cellCoord L x) i‖ - R')) *
      ‖molecularPositionH2StateMap eta (2 * Real.pi / L) u x‖ ^ 2 ≤ A') (d : ℝ) :
    ∀ ε > 0, ∃ w : C(MolecularPositionTorus eta, ℂ), ∃ hw : ContDiff ℝ 2 (torusRealLift w),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, w (molecularPositionSwap i j x) = sys.sign i * w x) ∧
      ∫ x, ‖w x‖ ^ 2 = 1 ∧ torusEnergy sys L θ w hw ≤ E + ε ∧
      ∫ x in {x | ∀ i, ‖particle (cellCoord L x) i‖ < d}ᶜ, ‖w x‖ ^ 2 ≤
        2 * max A' 1 * Real.exp (-(2 * β * (d - R'))) := by
  set U := molecularPositionH2StateMap eta (2 * Real.pi / L) u with hUdef
  set T := {x : MolecularPositionTorus eta | ∀ i, ‖particle (cellCoord L x) i‖ < d}ᶜ with hTdef
  have hmeas : ∀ i, Measurable fun x : MolecularPositionTorus eta =>
      ‖particle (cellCoord L x) i‖ :=
    fun i => (continuous_norm_particle i).measurable.comp (measurable_cellCoord L)
  have hAi : ∀ i, Integrable fun x =>
      Real.exp (2 * β * (‖particle (cellCoord L x) i‖ - R')) * ‖U x‖ ^ 2 := by
    intro i
    refine (integrable_sq_Lp U).bdd_mul (c := Real.exp (2 * β * (L - R')))
      (((hmeas i).sub_const R').const_mul (2 * β)).exp.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := norm_particle_cellCoord_le hL.le x i
    nlinarith
  have hS0 : Integrable fun x => ∑ i, Real.exp (-(2 * β * (d - R'))) *
      (Real.exp (2 * β * (‖particle (cellCoord L x) i‖ - R')) * ‖U x‖ ^ 2) :=
    integrable_finsetSum _ fun i _ => (hAi i).const_mul _
  have htail : ∫ x in T, ‖U x‖ ^ 2 ≤ Real.exp (-(2 * β * (d - R'))) * A' := by
    calc ∫ x in T, ‖U x‖ ^ 2
        ≤ ∫ x in T, ∑ i, Real.exp (-(2 * β * (d - R'))) *
            (Real.exp (2 * β * (‖particle (cellCoord L x) i‖ - R')) * ‖U x‖ ^ 2) := by
          refine setIntegral_mono_on (integrable_sq_Lp U).integrableOn hS0.integrableOn
            (measurableSet_prodInnerT L d).compl fun x hx => ?_
          simp only [hTdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hx
          obtain ⟨i, hi⟩ := hx
          have h1 : 1 ≤ Real.exp (-(2 * β * (d - R'))) *
              Real.exp (2 * β * (‖particle (cellCoord L x) i‖ - R')) := by
            rw [← Real.exp_add]
            apply Real.one_le_exp
            nlinarith [mul_nonneg hβ (sub_nonneg.mpr hi)]
          have h2 : ‖U x‖ ^ 2 ≤ Real.exp (-(2 * β * (d - R'))) *
              (Real.exp (2 * β * (‖particle (cellCoord L x) i‖ - R')) * ‖U x‖ ^ 2) := by
            nlinarith [sq_nonneg ‖U x‖]
          refine h2.trans (Finset.single_le_sum (f := fun j => Real.exp (-(2 * β * (d - R'))) *
            (Real.exp (2 * β * (‖particle (cellCoord L x) j‖ - R')) * ‖U x‖ ^ 2))
            (fun j _ => by positivity) (Finset.mem_univ i))
      _ ≤ ∫ x, ∑ i, Real.exp (-(2 * β * (d - R'))) *
            (Real.exp (2 * β * (‖particle (cellCoord L x) i‖ - R')) * ‖U x‖ ^ 2) :=
          setIntegral_le_integral hS0 (ae_of_all _ fun x =>
            Finset.sum_nonneg fun i _ => by positivity)
      _ = Real.exp (-(2 * β * (d - R'))) *
            ∑ i, ∫ x, Real.exp (2 * β * (‖particle (cellCoord L x) i‖ - R')) * ‖U x‖ ^ 2 := by
          rw [integral_finsetSum _ fun i _ => (hAi i).const_mul _, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul]
      _ ≤ Real.exp (-(2 * β * (d - R'))) * A' :=
          mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
  have hlt : ∫ x in T, ‖U x‖ ^ 2 < 2 * max A' 1 * Real.exp (-(2 * β * (d - R'))) := by
    have he := Real.exp_pos (-(2 * β * (d - R')))
    have hm : A' ≤ max A' 1 := le_max_left _ _
    have hm1 : 1 ≤ max A' 1 := le_max_right _ _
    nlinarith
  exact approx_torus_ground sys lab hL hθ hR H hKernel u hS hn hE T hlt

/-- An eigenvector of the completed operator: `H u = E u` and `‖u‖ = 1` give `Re⟨u, H u⟩ = E`. -/
lemma h2Form_of_eigen
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (g : ℝ) {u : MolecularFourierH2 eta} {E : ℝ}
    (hu : H u = (E : ℂ) • molecularH2StateMap eta g u)
    (hn : ‖molecularH2StateMap eta g u‖ = 1) :
    (inner ℂ (molecularH2StateMap eta g u) (H u)).re = E := by
  rw [hu, inner_smul_right, inner_self_eq_norm_sq_to_K, hn]
  simp

end

end FreeBoundary
