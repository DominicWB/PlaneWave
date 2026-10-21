import PlaneWave.FreeBoundary.LocalisationPair
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# `app:free`, part 14: IMS localisation on the configuration torus

The torus counterpart of `PlaneWave.FreeBoundary.IMS`, from the release's periodic integration of coordinate
derivatives (`integral_torusCoordinateDerivative_eq_zero`):

* `torus_ibp`, `torus_kinetic_by_parts`: for a torus function `w` with a `C²` periodic lift,
  `∫ (K w) w̄ = (1/(2L²)) Σ_a m_a⁻¹ ∫ |∂_a w|²` (`tGrad`), `∂_a` the coordinate derivative of the
  release (`torusCoordinateDerivative`);
* `tGrad_ims`: for real `c, e` with `C²` lifts and `c² + e² = 1`, the IMS formula
  `T(cw) + T(ew) = T(w) + (1/(2L²)) Σ_a m_a⁻¹ ∫ ((∂_a c)² + (∂_a e)²) |w|²`;
* `torusEnergy`, `torusEnergy_ims`: the same for the `g_L` energy (zero mode removed);
* **`torus_variational`**: the torus ground energy `E_L` bounds `torusEnergy` below on the `C²`
  states of the sector (pointwise exchange symmetry).
-/

set_option autoImplicit false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

local instance unitAddCircleMeasureSpaceFB14 : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

local instance unitAddCircleProbabilityMeasureFB14 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  instIsProbabilityMeasureUnitAddCircleVolume

local instance molecularTorusFiniteMeasureFB14 {eta : ℕ} :
    IsFiniteMeasure (volume : Measure (MolecularPositionTorus eta)) := by
  infer_instance

variable {eta : ℕ}

/-- Continuous functions on the configuration torus are integrable. -/
lemma integrable_of_continuous_torus {E : Type*} [NormedAddCommGroup E]
    {f : MolecularPositionTorus eta → E} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (isClosed_tsupport f).isCompact

/-! ## Real functions on the torus -/

/-- The real periodic lift. -/
def liftR (c : MolecularPositionTorus eta → ℝ) : Rcfg eta → ℝ :=
  fun y => c (torusRealQuotient _ y)

/-- The derivative of a real function along a coordinate line of the torus. -/
def tDR (a : Fin eta × Fin 3) (c : MolecularPositionTorus eta → ℝ)
    (x : MolecularPositionTorus eta) : ℝ :=
  deriv (fun t : ℝ => c (torusCoordinateLine x a t)) 0

lemma line_quot (y : Rcfg eta) (a : Fin eta × Fin 3) (t : ℝ) :
    torusCoordinateLine (torusRealQuotient _ y) a t =
      torusRealQuotient _ (y + t • Pi.single a 1) := by
  rw [← torusRealQuotient_coordinateLine]
  congr
  exact Subsingleton.elim _ _

lemma tDR_quot {c : MolecularPositionTorus eta → ℝ} (hc : Differentiable ℝ (liftR c))
    (y : Rcfg eta) (a : Fin eta × Fin 3) :
    tDR a c (torusRealQuotient _ y) = dirD a (liftR c) y := by
  unfold tDR
  have h : (fun t : ℝ => c (torusCoordinateLine (torusRealQuotient _ y) a t)) =
      fun t => liftR c (y + t • Pi.single a 1) := by
    funext t
    rw [line_quot]
    rfl
  rw [h]
  exact (hasDerivAt_line (by rw [zero_smul, add_zero]; exact (hc y).hasFDerivAt)).deriv

lemma tDR_hasDerivAt {c : MolecularPositionTorus eta → ℝ} (hc : Differentiable ℝ (liftR c))
    (x : MolecularPositionTorus eta) (a : Fin eta × Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => c (torusCoordinateLine x a s))
      (tDR a c (torusCoordinateLine x a t)) t := by
  obtain ⟨y, rfl⟩ := torusRealQuotient_surjective _ x
  have h : (fun s : ℝ => c (torusCoordinateLine (torusRealQuotient _ y) a s)) =
      fun s => liftR c (y + s • Pi.single a 1) := by
    funext s
    rw [line_quot]
    rfl
  rw [h, line_quot, tDR_quot hc]
  exact hasDerivAt_line (hc _).hasFDerivAt

lemma continuous_of_liftR {c : MolecularPositionTorus eta → ℝ} (hc : Continuous (liftR c)) :
    Continuous c :=
  (isOpenQuotientMap_torusRealQuotient (Fin eta × Fin 3)).isQuotientMap.continuous_iff.mpr hc

lemma continuous_tDR {c : MolecularPositionTorus eta → ℝ} (hc : ContDiff ℝ 1 (liftR c))
    (a : Fin eta × Fin 3) : Continuous (tDR a c) := by
  rw [(isOpenQuotientMap_torusRealQuotient (Fin eta × Fin 3)).isQuotientMap.continuous_iff]
  have h : tDR a c ∘ torusRealQuotient _ = dirD a (liftR c) := by
    funext y
    exact tDR_quot (hc.differentiable (by norm_num)) y a
  rw [h]
  exact continuous_dirD hc (by norm_num) a

/-! ## The kinetic form by parts on the torus -/

/-- Periodic integration by parts: `∫ (∂_a² w) w̄ = -∫ |∂_a w|²`. -/
lemma torus_ibp {w : C(MolecularPositionTorus eta, ℂ)} (hw : ContDiff ℝ 2 (torusRealLift w))
    (a : Fin eta × Fin 3) :
    ∫ x, torusCoordinateDerivative (torusCoordinateDerivative w a) a x * conj (w x) =
      -∫ x, ((‖torusCoordinateDerivative w a x‖ ^ 2 : ℝ) : ℂ) := by
  have hw1 : ContDiff ℝ 1 (torusRealLift w) := hw.of_le (by norm_num)
  have hD1 : ContDiff ℝ 1 (torusRealLift (torusCoordinateDerivative w a)) :=
    contDiff_torusCoordinateDerivative_realLift w hw a
  have hc1 : Continuous (torusCoordinateDerivative w a) :=
    continuous_torusCoordinateDerivative w hw1 a
  have hc2 : Continuous (torusCoordinateDerivative (torusCoordinateDerivative w a) a) :=
    continuous_torusCoordinateDerivative _ hD1 a
  have hwc : Continuous (fun x => conj (w x)) := Complex.continuous_conj.comp w.continuous
  let F : C(MolecularPositionTorus eta, ℂ) :=
    ⟨fun x => torusCoordinateDerivative w a x * conj (w x), hc1.mul hwc⟩
  let dF : C(MolecularPositionTorus eta, ℂ) :=
    ⟨fun x => torusCoordinateDerivative (torusCoordinateDerivative w a) a x * conj (w x) +
      torusCoordinateDerivative w a x * conj (torusCoordinateDerivative w a x),
      (hc2.mul hwc).add (hc1.mul (Complex.continuous_conj.comp hc1))⟩
  have hd : ∀ x t, HasDerivAt (fun s : ℝ => F (torusCoordinateLine x a s))
      (dF (torusCoordinateLine x a t)) t := by
    intro x t
    have h1 := torusCoordinateDerivative_hasDerivAt (torusCoordinateDerivative w a)
      hD1.differentiable_one x a t
    have h2 := torusCoordinateDerivative_hasDerivAt w hw1.differentiable_one x a t
    have h3 := HasDerivAt.star h2
    exact h1.mul h3
  have hz := integral_torusCoordinateDerivative_eq_zero F dF a hd
  have hi1 : Integrable (fun x => torusCoordinateDerivative (torusCoordinateDerivative w a) a x *
      conj (w x)) := integrable_of_continuous_torus (hc2.mul hwc)
  have hi2 : Integrable (fun x => torusCoordinateDerivative w a x *
      conj (torusCoordinateDerivative w a x)) :=
    integrable_of_continuous_torus (hc1.mul (Complex.continuous_conj.comp hc1))
  change ∫ x, (torusCoordinateDerivative (torusCoordinateDerivative w a) a x * conj (w x) +
      torusCoordinateDerivative w a x * conj (torusCoordinateDerivative w a x)) = 0 at hz
  rw [integral_add hi1 hi2] at hz
  have hpt : ∀ x, torusCoordinateDerivative w a x * conj (torusCoordinateDerivative w a x) =
      ((‖torusCoordinateDerivative w a x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hpt] at hz
  linear_combination hz

lemma deriv2_torusLine {w : MolecularPositionTorus eta → ℂ}
    (hw : ContDiff ℝ 2 (torusRealLift w)) (x : MolecularPositionTorus eta)
    (a : Fin eta × Fin 3) :
    deriv (deriv (fun t : ℝ => w (torusCoordinateLine x a t))) 0 =
      torusCoordinateDerivative (torusCoordinateDerivative w a) a x := by
  have h : deriv (fun t : ℝ => w (torusCoordinateLine x a t)) =
      fun t => torusCoordinateDerivative w a (torusCoordinateLine x a t) := by
    funext t
    exact (torusCoordinateDerivative_hasDerivAt w
      (hw.of_le (by norm_num) : ContDiff ℝ 1 _).differentiable_one x a t).deriv
  rw [h]
  rfl

/-- The torus gradient form `(1/(2L²)) Σ_a m_a⁻¹ ∫ |∂_a w|²`. -/
def tGrad (m : Fin eta → ℝ) (L : ℝ) (w : MolecularPositionTorus eta → ℂ) : ℝ :=
  (1 / (2 * L ^ 2)) * ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ *
    ∫ x, ‖torusCoordinateDerivative w a x‖ ^ 2

section System

variable {ν : Type} [Fintype ν]

omit [Fintype ν] in
/-- **The torus kinetic form by parts.** -/
theorem torus_kinetic_by_parts (sys : CoulombSystem eta ν) (L : ℝ)
    {w : C(MolecularPositionTorus eta, ℂ)} (hw : ContDiff ℝ 2 (torusRealLift w)) :
    ∫ x, coulombPositionContDiffKinetic sys L w hw x * conj (w x) = (tGrad sys.mass L w : ℂ) := by
  have hw1 : ContDiff ℝ 1 (torusRealLift w) := hw.of_le (by norm_num)
  have hint : ∀ a : Fin eta × Fin 3, Integrable (fun x =>
      torusCoordinateDerivative (torusCoordinateDerivative w a) a x * conj (w x)) := fun a =>
    integrable_of_continuous_torus ((continuous_torusCoordinateDerivative _
      (contDiff_torusCoordinateDerivative_realLift w hw a) a).mul
      (Complex.continuous_conj.comp w.continuous))
  have hpt : ∀ x, coulombPositionContDiffKinetic sys L w hw x * conj (w x) =
      ∑ a : Fin eta × Fin 3, (-(1 / 2 : ℂ) / (L : ℂ) ^ 2) * ((sys.mass a.1 : ℂ))⁻¹ *
        (torusCoordinateDerivative (torusCoordinateDerivative w a) a x * conj (w x)) := by
    intro x
    rw [coulombPositionContDiffKinetic_eq_classicalKinetic]
    unfold coulombPositionClassicalKinetic
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [deriv2_torusLine hw x a]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun a _ => (hint a).const_mul _)]
  simp_rw [integral_const_mul, torus_ibp hw, integral_complex_ofReal]
  unfold tGrad
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end System

/-! ## The IMS formula on the torus -/

lemma tD_ofReal_mul {c : MolecularPositionTorus eta → ℝ} (hc : Differentiable ℝ (liftR c))
    {u : MolecularPositionTorus eta → ℂ} (hu : Differentiable ℝ (torusRealLift u))
    (a : Fin eta × Fin 3) (x : MolecularPositionTorus eta) :
    torusCoordinateDerivative (fun y => (c y : ℂ) * u y) a x =
      (tDR a c x : ℂ) * u x + (c x : ℂ) * torusCoordinateDerivative u a x := by
  have h1 := (tDR_hasDerivAt hc x a 0).ofReal_comp
  have h2 := torusCoordinateDerivative_hasDerivAt u hu x a 0
  have h := h1.mul h2
  simp only [torusCoordinateLine_zero] at h
  exact h.deriv

lemma cutoff_tDR_rel {c e : MolecularPositionTorus eta → ℝ} (hc : Differentiable ℝ (liftR c))
    (he : Differentiable ℝ (liftR e)) (h1 : ∀ x, c x ^ 2 + e x ^ 2 = 1)
    (a : Fin eta × Fin 3) (x : MolecularPositionTorus eta) :
    c x * tDR a c x + e x * tDR a e x = 0 := by
  have hc' := tDR_hasDerivAt hc x a 0
  have he' := tDR_hasDerivAt he x a 0
  have h : HasDerivAt (fun s : ℝ => c (torusCoordinateLine x a s) * c (torusCoordinateLine x a s) +
      e (torusCoordinateLine x a s) * e (torusCoordinateLine x a s))
      (tDR a c (torusCoordinateLine x a 0) * c (torusCoordinateLine x a 0) +
        c (torusCoordinateLine x a 0) * tDR a c (torusCoordinateLine x a 0) +
        (tDR a e (torusCoordinateLine x a 0) * e (torusCoordinateLine x a 0) +
          e (torusCoordinateLine x a 0) * tDR a e (torusCoordinateLine x a 0))) 0 :=
    (hc'.mul hc').add (he'.mul he')
  have hconst : (fun s : ℝ => c (torusCoordinateLine x a s) * c (torusCoordinateLine x a s) +
      e (torusCoordinateLine x a s) * e (torusCoordinateLine x a s)) = fun _ => (1 : ℝ) := by
    funext s
    rw [← h1 (torusCoordinateLine x a s)]
    ring
  rw [hconst] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  simp only [torusCoordinateLine_zero] at h0
  linarith

lemma liftR_ofReal_mul (c : MolecularPositionTorus eta → ℝ) (u : MolecularPositionTorus eta → ℂ) :
    torusRealLift (fun y => (c y : ℂ) * u y) = fun y => (liftR c y : ℂ) * torusRealLift u y :=
  rfl

lemma contDiff_lift_ofReal_mul {c : MolecularPositionTorus eta → ℝ} (hc : ContDiff ℝ 2 (liftR c))
    {u : MolecularPositionTorus eta → ℂ} (hu : ContDiff ℝ 2 (torusRealLift u)) :
    ContDiff ℝ 2 (torusRealLift (fun y => (c y : ℂ) * u y)) := by
  rw [liftR_ofReal_mul]
  exact (Complex.ofRealCLM.contDiff.comp hc).mul hu

/-- The torus function `c u` as a continuous map. -/
def cutT (c : MolecularPositionTorus eta → ℝ) (hc : Continuous c)
    (u : C(MolecularPositionTorus eta, ℂ)) : C(MolecularPositionTorus eta, ℂ) :=
  ⟨fun y => (c y : ℂ) * u y, (Complex.continuous_ofReal.comp hc).mul u.continuous⟩

lemma integrable_tD_sq {w : C(MolecularPositionTorus eta, ℂ)}
    (hw : ContDiff ℝ 2 (torusRealLift w)) (a : Fin eta × Fin 3) :
    Integrable (fun x => ‖torusCoordinateDerivative w a x‖ ^ 2) :=
  integrable_of_continuous_torus
    ((continuous_torusCoordinateDerivative w (hw.of_le (by norm_num)) a).norm.pow 2)

/-- **The IMS formula on the torus.** -/
theorem tGrad_ims (m : Fin eta → ℝ) (L : ℝ) {c e : MolecularPositionTorus eta → ℝ}
    (hc : ContDiff ℝ 2 (liftR c)) (he : ContDiff ℝ 2 (liftR e)) (h1 : ∀ x, c x ^ 2 + e x ^ 2 = 1)
    {u : C(MolecularPositionTorus eta, ℂ)} (hu : ContDiff ℝ 2 (torusRealLift u)) :
    tGrad m L (fun y => (c y : ℂ) * u y) + tGrad m L (fun y => (e y : ℂ) * u y) =
      tGrad m L u + (1 / (2 * L ^ 2)) * ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ *
        ∫ x, (tDR a c x ^ 2 + tDR a e x ^ 2) * ‖u x‖ ^ 2 := by
  have hcd : Differentiable ℝ (liftR c) := hc.differentiable (by norm_num)
  have hed : Differentiable ℝ (liftR e) := he.differentiable (by norm_num)
  have hud : Differentiable ℝ (torusRealLift u) := hu.differentiable (by norm_num)
  have hcc : Continuous c := continuous_of_liftR hc.continuous
  have hec : Continuous e := continuous_of_liftR he.continuous
  have hcw : ContDiff ℝ 2 (torusRealLift (cutT c hcc u)) := contDiff_lift_ofReal_mul hc hu
  have hew : ContDiff ℝ 2 (torusRealLift (cutT e hec u)) := contDiff_lift_ofReal_mul he hu
  have hloc : ∀ a : Fin eta × Fin 3, Integrable
      (fun x => (tDR a c x ^ 2 + tDR a e x ^ 2) * ‖u x‖ ^ 2) := fun a =>
    integrable_of_continuous_torus ((((continuous_tDR (hc.of_le (by norm_num)) a).pow 2).add
      ((continuous_tDR (he.of_le (by norm_num)) a).pow 2)).mul (u.continuous.norm.pow 2))
  unfold tGrad
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_add, ← mul_add]
  congr 1
  have hi1 : Integrable (fun x => ‖torusCoordinateDerivative (fun y => (c y : ℂ) * u y) a x‖ ^ 2) :=
    integrable_tD_sq hcw a
  have hi2 : Integrable (fun x => ‖torusCoordinateDerivative (fun y => (e y : ℂ) * u y) a x‖ ^ 2) :=
    integrable_tD_sq hew a
  rw [← integral_add hi1 hi2, ← integral_add (integrable_tD_sq hu a) (hloc a)]
  congr 1
  funext x
  rw [tD_ofReal_mul hcd hud, tD_ofReal_mul hed hud,
    ims_pointwise (h1 x) (cutoff_tDR_rel hcd hed h1 a x)]
  ring

/-! ## The torus energy -/

section System

variable {ν : Type} [Fintype ν]

/-- The `g_L` energy (zero mode removed) of a torus state with a `C²` lift. -/
def torusEnergy (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (w : C(MolecularPositionTorus eta, ℂ)) (hw : ContDiff ℝ 2 (torusRealLift w)) : ℝ :=
  (∫ x, coulombPositionContDiffKinetic sys L w hw x * conj (w x)).re +
    ∫ x, (gLFourierPotential sys L θ x).re * ‖w x‖ ^ 2

lemma integrable_pot_torus (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {R : ℝ}
    {θ : ℝ → ℝ} (hθ : Profile R θ) {f : MolecularPositionTorus eta → ℝ} (hf : Continuous f) :
    Integrable (fun x => (gLFourierPotential sys L θ x).re * f x) := by
  have hV : Integrable (fun x => (gLFourierPotential sys L θ x).re) :=
    ((gLFourierPotential_memLp sys hL hθ).integrable (by norm_num)).re
  obtain ⟨C, hC⟩ := (isCompact_univ (X := MolecularPositionTorus eta)).exists_bound_of_continuousOn
    hf.continuousOn
  exact hV.mul_bdd hf.aestronglyMeasurable (ae_of_all _ fun x => hC x (Set.mem_univ x))

/-- **The IMS formula for the torus energy.** -/
theorem torusEnergy_ims (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {R : ℝ}
    {θ : ℝ → ℝ} (hθ : Profile R θ) {c e : MolecularPositionTorus eta → ℝ}
    (hc : ContDiff ℝ 2 (liftR c)) (he : ContDiff ℝ 2 (liftR e)) (h1 : ∀ x, c x ^ 2 + e x ^ 2 = 1)
    {u : C(MolecularPositionTorus eta, ℂ)} (hu : ContDiff ℝ 2 (torusRealLift u)) :
    torusEnergy sys L θ (cutT c (continuous_of_liftR hc.continuous) u)
        (contDiff_lift_ofReal_mul hc hu) +
      torusEnergy sys L θ (cutT e (continuous_of_liftR he.continuous) u)
        (contDiff_lift_ofReal_mul he hu) =
      torusEnergy sys L θ u hu + (1 / (2 * L ^ 2)) * ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ *
        ∫ x, (tDR a c x ^ 2 + tDR a e x ^ 2) * ‖u x‖ ^ 2 := by
  unfold torusEnergy
  rw [torus_kinetic_by_parts, torus_kinetic_by_parts, torus_kinetic_by_parts,
    Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
  have hcc : Continuous c := continuous_of_liftR hc.continuous
  have hec : Continuous e := continuous_of_liftR he.continuous
  have hpot : (∫ x, (gLFourierPotential sys L θ x).re * ‖(cutT c hcc u) x‖ ^ 2) +
      (∫ x, (gLFourierPotential sys L θ x).re * ‖(cutT e hec u) x‖ ^ 2) =
      ∫ x, (gLFourierPotential sys L θ x).re * ‖u x‖ ^ 2 := by
    have hi1 : Integrable (fun x => (gLFourierPotential sys L θ x).re * ‖(cutT c hcc u) x‖ ^ 2) :=
      integrable_pot_torus sys hL hθ
        ((cutT c hcc u).continuous.norm.pow 2 : Continuous (fun x => ‖(cutT c hcc u) x‖ ^ 2))
    have hi2 : Integrable (fun x => (gLFourierPotential sys L θ x).re * ‖(cutT e hec u) x‖ ^ 2) :=
      integrable_pot_torus sys hL hθ
        ((cutT e hec u).continuous.norm.pow 2 : Continuous (fun x => ‖(cutT e hec u) x‖ ^ 2))
    rw [← integral_add hi1 hi2]
    congr 1
    funext x
    change (gLFourierPotential sys L θ x).re * ‖(c x : ℂ) * u x‖ ^ 2 +
        (gLFourierPotential sys L θ x).re * ‖(e x : ℂ) * u x‖ ^ 2 =
      (gLFourierPotential sys L θ x).re * ‖u x‖ ^ 2
    rw [norm_ofReal_mul_sq, norm_ofReal_mul_sq]
    linear_combination ((gLFourierPotential sys L θ x).re * ‖u x‖ ^ 2) * h1 x
  have hgrad := tGrad_ims sys.mass L hc he h1 hu
  change tGrad sys.mass L (fun y => (c y : ℂ) * u y) +
      (∫ x, (gLFourierPotential sys L θ x).re * ‖(cutT c hcc u) x‖ ^ 2) +
      (tGrad sys.mass L (fun y => (e y : ℂ) * u y) +
        ∫ x, (gLFourierPotential sys L θ x).re * ‖(cutT e hec u) x‖ ^ 2) =
    tGrad sys.mass L u + (∫ x, (gLFourierPotential sys L θ x).re * ‖u x‖ ^ 2) +
      (1 / (2 * L ^ 2)) * ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ *
        ∫ x, (tDR a c x ^ 2 + tDR a e x ^ 2) * ‖u x‖ ^ 2
  linarith [hgrad, hpot]

/-- **The torus variational bound in integral form**: for a `C²` torus state with pointwise
exchange symmetry of the sector, `E_L ∫ |w|² ≤ torusEnergy w`. -/
theorem torus_variational (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} {L : ℝ} (hL : 0 < L)
    {R : ℝ} {θ : ℝ → ℝ} (hθ : Profile R θ) (hR : R ≤ L / 2) {E : ℝ}
    (hE : IsGLTorusGroundEnergy sys lab L θ E)
    (w : C(MolecularPositionTorus eta, ℂ)) (hw : ContDiff ℝ 2 (torusRealLift w))
    (hS : ∀ i j : Fin eta, i ≠ j → lab i = lab j →
      ∀ x, w (molecularPositionSwap i j x) = sys.sign i * w x) :
    E * ∫ x, ‖w x‖ ^ 2 ≤ torusEnergy sys L θ w hw := by
  have hcT := w.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure (MolecularPositionTorus eta))
  have hsec : IsPositionSector sys.sign lab ((ContinuousMap.toLp 2 volume ℂ) w) := by
    intro i j hij hlab
    filter_upwards [hcT, (molecularPositionSwap_measurePreserving i j).quasiMeasurePreserving.ae
      hcT] with x h1 h2
    rw [h2, h1]
    exact hS i j hij hlab x
  have hTmem : MemLp (fun x => w x) ⊤ volume :=
    memLp_top_of_bound w.continuous.aestronglyMeasurable ‖w‖
      (ae_of_all _ fun x => w.norm_coe_le_norm x)
  have hpmem : MemLp (fun x => gLFourierPotential sys L θ x * w x) 2 volume :=
    hTmem.mul' (gLFourierPotential_memLp sys hL hθ)
  have hp : HasL2PointwisePotential volume (gLFourierPotential sys L θ)
      ((ContinuousMap.toLp 2 volume ℂ) w) (hpmem.toLp _) := by
    filter_upwards [hpmem.coeFn_toLp, hcT] with x h1 h2
    rw [h1, h2]
  have hvar := gL_variational_C2 sys hL hθ hR hE w hw hsec (hpmem.toLp _) hp
  -- the three terms
  have hnorm : ‖(ContinuousMap.toLp 2 volume ℂ) w‖ ^ 2 = ∫ x, ‖w x‖ ^ 2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), ContinuousMap.inner_toLp]
    have hc : ∀ x, w x * conj (w x) = ((‖w x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [hc]
    rw [integral_complex_ofReal, RCLike.re_to_complex, Complex.ofReal_re]
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
  have hpot : (inner ℂ ((ContinuousMap.toLp 2 volume ℂ) w) (hpmem.toLp _)).re =
      ∫ x, (gLFourierPotential sys L θ x).re * ‖w x‖ ^ 2 := by
    rw [MeasureTheory.L2.inner_def, integral_congr_ae hae]
    rw [← RCLike.re_to_complex, ← integral_re hint]
    congr 1
    funext x
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, RCLike.re_to_complex]
    exact Complex.re_mul_ofReal _ _
  rw [hnorm, hkin, hpot] at hvar
  exact hvar

end System

end

end FreeBoundary
