import PlaneWave.FreeBoundary.CompletedHamiltonian

/-!
# `app:free`, part 10: transplanting free-space trial states to the torus

A free-space trial state `φ` on the physical configuration space `ℝ^{3η}` (coordinates
`r_{a,c}`), of class `C²` and vanishing unless every coordinate lies in `[-L/4, L/4]`, is
transplanted to the configuration torus of the release (dimensionless coordinates `x = r/L`):
`Tφ(x) = φ(L · rep(x))`, `rep(x) ∈ (-1/2, 1/2]^{3η}` the representative of `x`.

* `perLift`, `transplantFun`, `transplant`: the periodic lift `Φ(y) = φ(L · rep(y))` and the
  torus function; `torusRealLift_transplant`;
* `perLift_eventuallyEq`, `contDiff_perLift`: near every point `Φ` agrees with a translate of
  `φ(L ·)`, so `Φ` is `C²` (the support condition keeps the cell boundary away);
* `integral_transplant`: `∫_T (h ∘ T) = L^{-3η} ∫ h` for every `h` with the support condition;
  `integrable_of_transplant`: integrability descends from the torus;
* `contDiffKinetic_transplant`: the release's kinetic operator of `Tφ` is the transplant of the
  free-space kinetic expression `freeKinetic` (`-(1/2) Σ_a m_a⁻¹ ∂²_a`);
* `transplant_isPositionSector`: free-space sectors go to torus sectors;
* `gLFourierPotential_eq_freePot`: in the retained region the `g_L` multiplication function
  (zero mode removed) is the free-space Coulomb interaction `freePot` minus the zero-mode shift
  `C₀ = ĝ_L(0)(Σ q_a q_b + Σ q_a Z_ℓ)` (`zeroModeShift`);
* **`free_transplant_bound`**: for every `C²` free-space sector state in the retained region,
  `(E_L + C₀) ‖φ‖² ≤ Re⟨φ, Kφ⟩ + ∫ V_∞ |φ|²` (the Coulomb term integrable);
* **`free_upper_of_trial`**: `E_L + C₀ ≤ E_∞ + δ` when retained trial states reach `E_∞ + δ`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

local instance unitAddCircleMeasureSpaceFB10 : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

local instance unitAddCircleProbabilityMeasureFB10 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  instIsProbabilityMeasureUnitAddCircleVolume

local instance molecularTorusFiniteMeasureFB10 {eta : ℕ} :
    IsFiniteMeasure (volume : Measure (MolecularPositionTorus eta)) := by
  infer_instance

variable {eta : ℕ}

/-- Physical configurations `r_{a,c}` of `η` particles. -/
abbrev Rcfg (eta : ℕ) := Fin eta × Fin 3 → ℝ

/-! ## The representative in `(-1/2, 1/2]` -/

/-- The representative of `t` in `(-1/2, 1/2]`. -/
def rep1 (t : ℝ) : ℝ := t - ⌈t - 1 / 2⌉

lemma rep1_mem (t : ℝ) : rep1 t ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
  unfold rep1
  have h1 := Int.ceil_lt_add_one (t - 1 / 2)
  have h2 := Int.le_ceil (t - 1 / 2)
  constructor <;> linarith

lemma rep1_of_mem {t : ℝ} (ht : t ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) : rep1 t = t := by
  unfold rep1
  have hc : ⌈t - 1 / 2⌉ = 0 := by
    rw [Int.ceil_eq_iff]
    obtain ⟨h1, h2⟩ := ht
    constructor
    · push_cast
      linarith
    · push_cast
      linarith
  rw [hc]
  simp

lemma coe_rep1 (t : ℝ) : ((rep1 t : ℝ) : UnitAddCircle) = (t : UnitAddCircle) := by
  have h : (((⌈t - 1 / 2⌉ : ℤ) : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨⌈t - 1 / 2⌉, by simp⟩
  unfold rep1
  rw [AddCircle.coe_sub, h, sub_zero]

lemma equivIoc_coe_rep1 (t : ℝ) :
    (AddCircle.equivIoc 1 (-1 / 2) (t : UnitAddCircle) : ℝ) = rep1 t := by
  rw [← coe_rep1 t, AddCircle.equivIoc_coe_of_mem (rep1_mem t)]

/-! ## The transplant -/

/-- The support condition: `φ` vanishes unless every coordinate lies in `[-L/4, L/4]`. -/
def Supp4 (L : ℝ) (φ : Rcfg eta → ℂ) : Prop := ∀ r, φ r ≠ 0 → ∀ a, |r a| ≤ L / 4

/-- The periodic lift `Φ(y) = φ(L · rep(y))`. -/
def perLift (L : ℝ) (φ : Rcfg eta → ℂ) (y : Rcfg eta) : ℂ := φ (fun a => L * rep1 (y a))

/-- The transplant to the configuration torus. -/
def transplantFun (L : ℝ) (φ : Rcfg eta → ℂ) (x : MolecularPositionTorus eta) : ℂ :=
  φ (fun a => L * (AddCircle.equivIoc 1 (-1 / 2) (x a) : ℝ))

lemma torusRealLift_transplant (L : ℝ) (φ : Rcfg eta → ℂ) :
    torusRealLift (transplantFun L φ) = perLift L φ := by
  funext y
  unfold torusRealLift transplantFun perLift torusRealQuotient
  simp only [equivIoc_coe_rep1]

lemma transplantFun_coe (L : ℝ) (φ : Rcfg eta → ℂ) (y : Rcfg eta) :
    transplantFun L φ (torusRealQuotient _ y) = perLift L φ y := by
  rw [← torusRealLift_transplant]
  rfl

lemma abs_le_quarter {L t : ℝ} (hL : 0 < L) (h : |L * t| ≤ L / 4) : |t| ≤ 1 / 4 := by
  rw [abs_mul, abs_of_pos hL] at h
  by_contra hc
  push Not at hc
  nlinarith

/-- If a translate `φ(L(y - m))` does not vanish, it is the value of the periodic lift. -/
lemma perLift_eq_of_ne {L : ℝ} (hL : 0 < L) {φ : Rcfg eta → ℂ} (hs : Supp4 L φ) (y : Rcfg eta)
    (m : Fin eta × Fin 3 → ℤ) (h : φ (fun a => L * (y a - m a)) ≠ 0) :
    perLift L φ y = φ (fun a => L * (y a - m a)) := by
  have hm : ∀ a, rep1 (y a) = y a - m a := by
    intro a
    have hb := abs_le_quarter hL (hs _ h a)
    obtain ⟨h1, h2⟩ := abs_le.mp hb
    unfold rep1
    have hc : ⌈y a - 1 / 2⌉ = m a := by
      rw [Int.ceil_eq_iff]
      constructor <;> linarith
    rw [hc]
  unfold perLift
  congr 1
  funext a
  rw [hm a]

/-- **Near every point the periodic lift is a translate of `φ(L ·)`.** -/
lemma perLift_eventuallyEq {L : ℝ} (hL : 0 < L) {φ : Rcfg eta → ℂ} (hs : Supp4 L φ)
    (y : Rcfg eta) :
    perLift L φ =ᶠ[𝓝 y] fun y' => φ (fun a => L * (y' a - ⌈y a - 1 / 2⌉)) := by
  set n : Fin eta × Fin 3 → ℤ := fun a => ⌈y a - 1 / 2⌉ with hn
  have hU : ∀ᶠ y' in 𝓝 y, ∀ a, |y' a - y a| < 1 / 4 := by
    rw [Filter.eventually_all]
    intro a
    have ht : Tendsto (fun y' : Rcfg eta => y' a) (𝓝 y) (𝓝 (y a)) :=
      (continuous_apply a).tendsto y
    filter_upwards [ht (Metric.ball_mem_nhds (y a) (by norm_num : (0 : ℝ) < 1 / 4))]
      with y' hy'
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hy'
    exact hy'
  filter_upwards [hU] with y' hy'
  by_cases h : φ (fun a => L * (y' a - n a)) ≠ 0
  · exact perLift_eq_of_ne hL hs y' n h
  · push Not at h
    rw [h]
    by_contra hne
    have hne' : φ (fun a => L * (y' a - ⌈y' a - 1 / 2⌉)) ≠ 0 := by
      unfold perLift rep1 at hne
      exact hne
    have heq : ∀ a, ⌈y' a - 1 / 2⌉ = n a := by
      intro a
      have hb := abs_le_quarter hL (hs _ hne' a)
      have hy := rep1_mem (y a)
      unfold rep1 at hy
      have hya := hy' a
      obtain ⟨hy1, hy2⟩ := hy
      obtain ⟨hb1, hb2⟩ := abs_le.mp hb
      obtain ⟨hya1, hya2⟩ := abs_lt.mp hya
      have hlt : |((⌈y' a - 1 / 2⌉ - n a : ℤ) : ℝ)| < 1 := by
        rw [abs_lt]
        push_cast
        simp only [hn]
        constructor <;> linarith
      have h0 : ⌈y' a - 1 / 2⌉ - n a = 0 := by
        have : |(⌈y' a - 1 / 2⌉ - n a : ℤ)| < 1 := by exact_mod_cast hlt
        rw [abs_lt] at this
        omega
      omega
    apply hne'
    have : (fun a => L * (y' a - ⌈y' a - 1 / 2⌉)) = fun a => L * (y' a - n a) := by
      funext a
      rw [heq a]
    rw [this]
    exact h

/-- **The periodic lift is `C²`.** -/
theorem contDiff_perLift {L : ℝ} (hL : 0 < L) {φ : Rcfg eta → ℂ} (hs : Supp4 L φ)
    (h2 : ContDiff ℝ 2 φ) : ContDiff ℝ 2 (perLift L φ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have haff : ContDiff ℝ 2 (fun y' : Rcfg eta => fun a => L * (y' a - ⌈y a - 1 / 2⌉)) := by
    apply contDiff_pi.mpr
    intro a
    exact contDiff_const.mul ((contDiff_apply ℝ ℝ a).sub contDiff_const)
  exact (h2.comp haff).contDiffAt.congr_of_eventuallyEq (perLift_eventuallyEq hL hs y)

lemma continuous_transplantFun {L : ℝ} (hL : 0 < L) {φ : Rcfg eta → ℂ} (hs : Supp4 L φ)
    (h2 : ContDiff ℝ 2 φ) : Continuous (transplantFun L φ) := by
  rw [(isOpenQuotientMap_torusRealQuotient (Fin eta × Fin 3)).isQuotientMap.continuous_iff]
  have h := (contDiff_perLift hL hs h2).continuous
  rw [← torusRealLift_transplant] at h
  exact h

/-- The transplant as a continuous function on the configuration torus. -/
def transplant {L : ℝ} (hL : 0 < L) (φ : Rcfg eta → ℂ) (hs : Supp4 L φ)
    (h2 : ContDiff ℝ 2 φ) : C(MolecularPositionTorus eta, ℂ) :=
  ⟨transplantFun L φ, continuous_transplantFun hL hs h2⟩

lemma contDiff_transplant_lift {L : ℝ} (hL : 0 < L) {φ : Rcfg eta → ℂ} (hs : Supp4 L φ)
    (h2 : ContDiff ℝ 2 φ) : ContDiff ℝ 2 (torusRealLift (transplant hL φ hs h2)) := by
  change ContDiff ℝ 2 (torusRealLift (transplantFun L φ))
  rw [torusRealLift_transplant]
  exact contDiff_perLift hL hs h2

/-! ## Integrals of transplants -/

lemma box_measurable :
    MeasurableSet {x : Rcfg eta | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
      ((fun _ => (-1 / 2 : ℝ)) i + 1)} := by
  have hSeq : {x : Rcfg eta | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
      ((fun _ => (-1 / 2 : ℝ)) i + 1)} =
      ⋂ i : Fin eta × Fin 3, (fun x : Rcfg eta => x i) ⁻¹' Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
    ext x
    simp
  rw [hSeq]
  exact MeasurableSet.iInter fun i => measurableSet_Ioc.preimage (measurable_pi_apply i)

/-- **The integral of a transplant**: `∫_T h(L · rep(x)) dx = L^{-3η} ∫ h` for every `h` with the
support condition. -/
theorem integral_transplant {L : ℝ} (hL : 0 < L) (h : Rcfg eta → ℂ) (hs : Supp4 L h) :
    ∫ x : MolecularPositionTorus eta, transplantFun L h x =
      ((L ^ Fintype.card (Fin eta × Fin 3))⁻¹ : ℝ) • ∫ r, h r := by
  rw [UnitAddTorus.integral_preimage _ (fun _ => -1 / 2)]
  have hbox : ∀ y ∈ {x : Rcfg eta | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
      ((fun _ => (-1 / 2 : ℝ)) i + 1)},
      transplantFun L h (fun i => (y i : UnitAddCircle)) = h (L • y) := by
    intro y hy
    unfold transplantFun
    congr 1
    funext a
    rw [equivIoc_coe_rep1, rep1_of_mem (hy a)]
    rfl
  rw [setIntegral_congr_fun box_measurable hbox]
  have hzero : ∀ y, y ∉ {x : Rcfg eta | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
      ((fun _ => (-1 / 2 : ℝ)) i + 1)} → h (L • y) = 0 := by
    intro y hy
    by_contra hne
    apply hy
    intro a
    have hb := abs_le_quarter hL (hs _ hne a)
    obtain ⟨h1, h2⟩ := abs_le.mp hb
    constructor <;> linarith
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    Measure.integral_comp_smul volume h L, Module.finrank_fintype_fun_eq_card,
    abs_of_pos (by positivity)]

lemma transplantFun_box (L : ℝ) (h : Rcfg eta → ℂ) (y : Rcfg eta)
    (hy : ∀ i, y i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i) ((fun _ => (-1 / 2 : ℝ)) i + 1)) :
    transplantFun L h (fun i => (y i : UnitAddCircle)) = h (L • y) := by
  unfold transplantFun
  congr 1
  funext a
  rw [equivIoc_coe_rep1, rep1_of_mem (hy a)]
  rfl

lemma eq_zero_of_not_box {L : ℝ} (hL : 0 < L) {h : Rcfg eta → ℂ} (hs : Supp4 L h) (y : Rcfg eta)
    (hy : y ∉ {x : Rcfg eta | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
      ((fun _ => (-1 / 2 : ℝ)) i + 1)}) :
    h (L • y) = 0 := by
  by_contra hne
  apply hy
  intro a
  have hb := abs_le_quarter hL (hs _ hne a)
  obtain ⟨h1, h2⟩ := abs_le.mp hb
  constructor <;> linarith

/-- Integrability descends from the transplant. -/
theorem integrable_of_transplant {L : ℝ} (hL : 0 < L) {h : Rcfg eta → ℂ} (hs : Supp4 L h)
    (hint : Integrable (transplantFun L h)) : Integrable h := by
  have hmp := (UnitAddTorus.measurePreserving_equivPiIoc
    (fun _ : Fin eta × Fin 3 => (-1 / 2 : ℝ))).symm
  have h1 := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hint
  have h2 : IntegrableOn (fun y : Rcfg eta => h (L • y))
      {x : Rcfg eta | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
        ((fun _ => (-1 / 2 : ℝ)) i + 1)} := by
    rw [integrableOn_iff_comap_subtypeVal box_measurable]
    refine h1.congr (ae_of_all _ fun y => ?_)
    simp only [Function.comp_apply, UnitAddTorus.coe_symm_measurableEquivPiIoc_apply]
    exact transplantFun_box L h y.1 y.2
  have h3 : Integrable (fun y : Rcfg eta => h (L • y)) := by
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp h2
    intro y hy
    by_contra hy'
    exact (Function.mem_support.mp hy) (eq_zero_of_not_box hL hs y hy')
  exact (integrable_comp_smul_iff volume h hL.ne').mp h3

lemma Supp4.mul_conj {L : ℝ} {φ : Rcfg eta → ℂ} (hs : Supp4 L φ) (g : Rcfg eta → ℂ) :
    Supp4 L (fun r => g r * conj (φ r)) := by
  intro r hr
  apply hs r
  intro h0
  apply hr
  change g r * conj (φ r) = 0
  rw [h0, map_zero, mul_zero]

/-! ## The kinetic energy -/

/-- The free-space kinetic expression `-(1/2) Σ_a m_a⁻¹ ∂²φ/∂r_a²` (`a` runs over the particle
coordinates). -/
def freeKinetic (m : Fin eta → ℝ) (φ : Rcfg eta → ℂ) (r : Rcfg eta) : ℂ :=
  (-(1 / 2 : ℂ)) * ∑ a : Fin eta × Fin 3, ((m a.1 : ℂ))⁻¹ *
    deriv (deriv (fun s : ℝ => φ (r + s • Pi.single a 1))) 0

lemma deriv2_comp_mul_left (g : ℝ → ℂ) (L : ℝ) :
    deriv (deriv (fun t : ℝ => g (L * t))) 0 = ((L ^ 2 : ℝ) : ℂ) * deriv (deriv g) 0 := by
  have h1 : deriv (fun t : ℝ => g (L * t)) = fun t => L • deriv g (L * t) := by
    funext t
    exact deriv_comp_mul_left L g t
  rw [h1, deriv_fun_const_smul_field]
  have h2 : deriv (fun t : ℝ => deriv g (L * t)) 0 = L • deriv (deriv g) (L * 0) :=
    deriv_comp_mul_left L (deriv g) 0
  rw [h2, mul_zero, smul_smul, Complex.real_smul]
  push_cast
  ring

/-- Along a coordinate line the periodic lift is, near `t = 0`, the scaled line of `φ` through
`L · rep(y)`. -/
lemma perLift_line_eventuallyEq {L : ℝ} (hL : 0 < L) {φ : Rcfg eta → ℂ} (hs : Supp4 L φ)
    (y : Rcfg eta) (a : Fin eta × Fin 3) :
    (fun t : ℝ => perLift L φ (y + t • Pi.single a 1)) =ᶠ[𝓝 0]
      fun t => φ ((fun b => L * rep1 (y b)) + (L * t) • Pi.single a 1) := by
  have hc : Tendsto (fun t : ℝ => y + t • Pi.single a (1 : ℝ)) (𝓝 0) (𝓝 y) := by
    have hcont : Continuous (fun t : ℝ => y + t • Pi.single a (1 : ℝ)) := by fun_prop
    simpa using hcont.tendsto 0
  filter_upwards [hc.eventually (perLift_eventuallyEq hL hs y)] with t ht
  refine ht.trans ?_
  congr 1
  funext b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rep1]
  ring

section System

variable {ν : Type} [Fintype ν]

omit [Fintype ν] in
/-- **The kinetic energy of a transplant**: `K_T (Tφ) = T(K φ)`; the factor `L²` of the chain
rule cancels the `1/L²` of the dimensionless torus coordinates. -/
theorem classicalKinetic_transplant (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    {φ : Rcfg eta → ℂ} (hs : Supp4 L φ) (y : Rcfg eta) :
    coulombPositionClassicalKinetic sys L (transplantFun L φ) (torusRealQuotient _ y) =
      transplantFun L (freeKinetic sys.mass φ) (torusRealQuotient _ y) := by
  have hline : ∀ a : Fin eta × Fin 3,
      deriv (deriv (fun t : ℝ => transplantFun L φ
        (torusCoordinateLine (torusRealQuotient _ y) a t))) 0 =
      ((L ^ 2 : ℝ) : ℂ) * deriv (deriv (fun s : ℝ =>
        φ ((fun b => L * rep1 (y b)) + s • Pi.single a 1))) 0 := by
    intro a
    have heq : (fun t : ℝ => transplantFun L φ
        (torusCoordinateLine (torusRealQuotient _ y) a t)) =
        fun t => perLift L φ (y + t • Pi.single a 1) := by
      funext t
      rw [← torusRealQuotient_coordinateLine, transplantFun_coe]
      congr
      exact Subsingleton.elim _ _
    rw [heq, (perLift_line_eventuallyEq hL hs y a).deriv.deriv_eq]
    exact deriv2_comp_mul_left (fun s => φ ((fun b => L * rep1 (y b)) + s • Pi.single a 1)) L
  rw [transplantFun_coe]
  unfold coulombPositionClassicalKinetic perLift freeKinetic
  simp_rw [hline]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  push_cast
  field_simp

omit [Fintype ν] in
theorem contDiffKinetic_transplant (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    {φ : Rcfg eta → ℂ} (hs : Supp4 L φ) (h2 : ContDiff ℝ 2 φ) (x : MolecularPositionTorus eta) :
    coulombPositionContDiffKinetic sys L (transplant hL φ hs h2)
        (contDiff_transplant_lift hL hs h2) x = transplantFun L (freeKinetic sys.mass φ) x := by
  obtain ⟨y, rfl⟩ := torusRealQuotient_surjective _ x
  rw [coulombPositionContDiffKinetic_eq_classicalKinetic]
  exact classicalKinetic_transplant sys hL hs y

end System

/-! ## Exchange sectors -/

/-- The cell coordinates `L · rep(x) ∈ (-L/2, L/2]^{3η}` of a torus point; `Tφ(x) = φ(L · rep(x))`. -/
def cellCoord (L : ℝ) (x : MolecularPositionTorus eta) : Rcfg eta :=
  fun a => L * (AddCircle.equivIoc 1 (-1 / 2) (x a) : ℝ)

lemma transplantFun_eq (L : ℝ) (φ : Rcfg eta → ℂ) (x : MolecularPositionTorus eta) :
    transplantFun L φ x = φ (cellCoord L x) := rfl

/-- Exchange of the positions of particles `i` and `j` in free space. -/
def freeSwap (i j : Fin eta) (r : Rcfg eta) : Rcfg eta := fun a => r ((Equiv.swap i j) a.1, a.2)

/-- The exchange sector in free space: exchanging two distinct particles with equal labels
multiplies `φ` by the sign of the particle. -/
def IsFreeSector (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ) (φ : Rcfg eta → ℂ) : Prop :=
  ∀ i j : Fin eta, i ≠ j → lab i = lab j → ∀ r, φ (freeSwap i j r) = sgn i * φ r

/-- The transplant of a state of a free-space sector lies in the same sector of the torus. -/
theorem transplant_isPositionSector {L : ℝ} (hL : 0 < L) {φ : Rcfg eta → ℂ} (hs : Supp4 L φ)
    (h2 : ContDiff ℝ 2 φ) {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ}
    (hS : IsFreeSector sgn lab φ) :
    IsPositionSector sgn lab ((ContinuousMap.toLp 2 volume ℂ) (transplant hL φ hs h2)) := by
  intro i j hij hlab
  have hc := (transplant hL φ hs h2).coeFn_toLp (p := 2) (𝕜 := ℂ)
    (volume : Measure (MolecularPositionTorus eta))
  filter_upwards [hc, (molecularPositionSwap_measurePreserving i j).quasiMeasurePreserving.ae hc]
    with x h1 h2'
  rw [h2', h1]
  exact hS i j hij hlab (cellCoord L x)

/-! ## The potential energy -/

/-- The position `r_i ∈ ℝ³` of particle `i`. -/
def particle (r : Rcfg eta) (i : Fin eta) : E3 := WithLp.toLp 2 (fun c => r (i, c))

lemma latVec_add (L : ℝ) (m n : Fin 3 → ℤ) : latVec L m + latVec L n = latVec L (m + n) := by
  unfold latVec
  ext c
  simp
  ring

/-- The nearest-image distance is periodic. -/
lemma niDist_sub_latVec (L : ℝ) (x : E3) (m : Fin 3 → ℤ) :
    niDist L (x - latVec L m) = niDist L x := by
  unfold niDist
  have h : ∀ n, ‖x - latVec L m - latVec L n‖ = ‖x - latVec L (m + n)‖ := by
    intro n
    rw [← latVec_add, sub_sub]
  simp_rw [h]
  exact Equiv.iInf_comp (g := fun n => ‖x - latVec L n‖) (Equiv.addLeft m)

/-- The torus kernel at the class of `z` is `g_L(L z)`, for any representative `z`. -/
lemma gLtorus_coe (L : ℝ) (θ : ℝ → ℝ) (z : Fin 3 → ℝ) :
    gLtorus L θ (fun c => (z c : UnitAddCircle)) =
      (gLni L θ (WithLp.toLp 2 (fun c => L * z c)) : ℂ) := by
  have h : cellRep L (fun c => (z c : UnitAddCircle)) =
      WithLp.toLp 2 (fun c => L * z c) - latVec L (fun c => ⌈z c - 1 / 2⌉) := by
    unfold cellRep latVec
    ext c
    simp [equivIoc_coe_rep1, rep1]
    ring
  unfold gLtorus gLni
  rw [h, niDist_sub_latVec]

lemma gLtorus_pair {L : ℝ} (θ : ℝ → ℝ) (i j : Fin eta) (x : MolecularPositionTorus eta) :
    gLtorus L θ (molecularPositionDifference i j x) =
      (gLni L θ (particle (cellCoord L x) i - particle (cellCoord L x) j) : ℂ) := by
  have h : molecularPositionDifference i j x = fun c =>
      (((AddCircle.equivIoc 1 (-1 / 2) (x (i, c)) : ℝ) -
        (AddCircle.equivIoc 1 (-1 / 2) (x (j, c)) : ℝ) : ℝ) : UnitAddCircle) := by
    funext c
    rw [AddCircle.coe_sub, AddCircle.coe_equivIoc, AddCircle.coe_equivIoc]
    rfl
  rw [h, gLtorus_coe]
  congr 2
  ext c
  simp [particle, cellCoord]
  ring

lemma gLtorus_nuclear {L : ℝ} (hL : L ≠ 0) (θ : ℝ → ℝ) (i : Fin eta) (Pl : E3)
    (x : MolecularPositionTorus eta) :
    gLtorus L θ (molecularPositionNuclearArgument i
        (fun c => ((-(Pl c) / L : ℝ) : UnitAddCircle)) x) =
      (gLni L θ (particle (cellCoord L x) i - Pl) : ℂ) := by
  have h : molecularPositionNuclearArgument i
      (fun c => ((-(Pl c) / L : ℝ) : UnitAddCircle)) x = fun c =>
      (((AddCircle.equivIoc 1 (-1 / 2) (x (i, c)) : ℝ) + -(Pl c) / L : ℝ) : UnitAddCircle) := by
    funext c
    rw [AddCircle.coe_add, AddCircle.coe_equivIoc]
    rfl
  rw [h, gLtorus_coe]
  congr 2
  ext c
  simp [particle, cellCoord]
  field_simp
  ring

section System

variable {ν : Type} [Fintype ν]

/-- The free-space Coulomb interaction of the system, with the nuclei at `P_ℓ ∈ ℝ³`. -/
def freePot (sys : CoulombSystem eta ν) (P : ν → E3) (r : Rcfg eta) : ℝ :=
  potInf sys.charge sys.nuclei.charge P (particle r)

/-- The zero-mode shift `ĝ_L(0) (Σ_{a<b} q_a q_b + Σ_{a,ℓ} q_a Z_ℓ)`: the `g_L` Hamiltonian with
its zero mode is the one of `PlaneWave.FreeBoundary.CubeHamiltonian`–`PlaneWave.FreeBoundary.CompletedHamiltonian` plus this constant. -/
def zeroModeShift (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ) : ℂ :=
  (∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
      ghat L θ (fun _ => 0)) +
    ∑ i : Fin eta, ((sys.charge i : ℝ) : ℂ) *
      ∑ ell : ν, (sys.nuclei.charge ell : ℂ) * ghat L θ (fun _ => 0)

lemma freePot_ofReal (sys : CoulombSystem eta ν) (P : ν → E3) (r : Rcfg eta) :
    ((freePot sys P r : ℝ) : ℂ) =
      (∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
          ((1 / ‖particle r pair.1.1 - particle r pair.1.2‖ : ℝ) : ℂ)) +
        ∑ i : Fin eta, ((sys.charge i : ℝ) : ℂ) *
          ∑ ell : ν, (sys.nuclei.charge ell : ℂ) * ((1 / ‖particle r i - P ell‖ : ℝ) : ℂ) := by
  unfold freePot potInf
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The potential of a transplant**: in the retained region (molecule centred at the origin,
nuclei at `P_ℓ` with `|P_ℓ| ≤ R₀`, which on the torus sit at `-P_ℓ/L` in the release's convention
`x_a + R_ℓ`), the `g_L` multiplication function (zero mode removed) is the free-space Coulomb
interaction minus the zero-mode shift. -/
theorem gLFourierPotential_eq_freePot (sys : CoulombSystem eta ν) {L R0 ρ : ℝ} (hL : 0 < L)
    (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) {θ : ℝ → ℝ} (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (x : MolecularPositionTorus eta)
    (hx : ∀ i, ‖particle (cellCoord L x) i‖ ≤ retainedRadius L R0 ρ) :
    gLFourierPotential sys L θ x =
      (freePot sys P (cellCoord L x) : ℂ) - zeroModeShift sys L θ := by
  have hL0 : L ≠ 0 := hL.ne'
  have hx' : ∀ i, ‖particle (cellCoord L x) i - 0‖ ≤ retainedRadius L R0 ρ := by
    intro i
    rw [sub_zero]
    exact hx i
  have hP' : ∀ l, ‖P l - 0‖ ≤ R0 := by
    intro l
    rw [sub_zero]
    exact hP l
  have hpair : ∀ i j : Fin eta, gLtorus0 L θ (molecularPositionDifference i j x) =
      ((1 / ‖particle (cellCoord L x) i - particle (cellCoord L x) j‖ : ℝ) : ℂ) -
        ghat L θ (fun _ => 0) := by
    intro i j
    unfold gLtorus0
    rw [gLtorus_pair θ i j x, retained_pair hL hR0 hρ hone 0 _ _ (hx' i) (hx' j)]
  have hnuc : ∀ i l, gLtorus0 L θ
      (molecularPositionNuclearArgument i (sys.nuclei.position l) x) =
      ((1 / ‖particle (cellCoord L x) i - P l‖ : ℝ) : ℂ) - ghat L θ (fun _ => 0) := by
    intro i l
    unfold gLtorus0
    rw [hpos l, gLtorus_nuclear hL0 θ i (P l) x,
      retained_nuclear hL hρ hone 0 _ _ (hx' i) (hP' l)]
  unfold gLFourierPotential
  rw [freePot_ofReal]
  unfold zeroModeShift
  simp only [hpair, hnuc, mul_sub, Finset.sum_sub_distrib]
  ring

end System

/-! ## The transplant inequality -/

/-- The retained support condition (molecule centred at the origin): `φ` vanishes unless every
particle lies in `B_{R_L}(0)`, `R_L = L/4 - R₀ - ρ`. -/
def SuppRet (L R0 ρ : ℝ) (φ : Rcfg eta → ℂ) : Prop :=
  ∀ r, φ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ

lemma SuppRet.supp4 {L R0 ρ : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) {φ : Rcfg eta → ℂ}
    (h : SuppRet L R0 ρ φ) : Supp4 L φ := by
  intro r hr a
  have h1 := h r hr a.1
  have h2 : |r a| ≤ ‖particle r a.1‖ := by
    have := abs_coord_le_norm (particle r a.1) a.2
    simpa [particle] using this
  unfold retainedRadius at h1
  linarith

/-- The norm of a transplant: `‖Tφ‖² = L^{-3η} ‖φ‖²`. -/
lemma norm_sq_toLp_transplant {L : ℝ} (hL : 0 < L) {φ : Rcfg eta → ℂ} (hs : Supp4 L φ)
    (h2 : ContDiff ℝ 2 φ) :
    ‖(ContinuousMap.toLp 2 volume ℂ) (transplant hL φ hs h2)‖ ^ 2 =
      (L ^ Fintype.card (Fin eta × Fin 3))⁻¹ * ∫ r, ‖φ r‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), ContinuousMap.inner_toLp]
  have hfun : (fun x => (transplant hL φ hs h2) x * conj ((transplant hL φ hs h2) x)) =
      transplantFun L (fun r => φ r * conj (φ r)) := rfl
  rw [hfun, integral_transplant hL _ (hs.mul_conj φ)]
  have hc : ∀ r, φ r * conj (φ r) = ((‖φ r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hc]
  rw [integral_complex_ofReal, RCLike.re_to_complex, Complex.smul_re, Complex.ofReal_re,
    smul_eq_mul]

lemma integrable_mul_conj {L : ℝ} (hL : 0 < L) {φ : Rcfg eta → ℂ} (hs : Supp4 L φ)
    (h2 : ContDiff ℝ 2 φ) : Integrable (fun r => φ r * conj (φ r)) := by
  have hcT := (transplant hL φ hs h2).coeFn_toLp (p := 2) (𝕜 := ℂ)
    (volume : Measure (MolecularPositionTorus eta))
  refine integrable_of_transplant hL (hs.mul_conj φ)
    ((MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      ((ContinuousMap.toLp 2 volume ℂ) (transplant hL φ hs h2))
      ((ContinuousMap.toLp 2 volume ℂ) (transplant hL φ hs h2))).congr ?_)
  filter_upwards [hcT] with x hx
  rw [RCLike.inner_apply, hx]
  rfl

section System

variable {ν : Type} [Fintype ν]

omit [Fintype ν] in
/-- The kinetic form of a transplant: `⟨Tφ, K_T Tφ⟩ = L^{-3η} ⟨φ, K φ⟩`. -/
lemma inner_kinetic_transplant (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    {φ : Rcfg eta → ℂ} (hs : Supp4 L φ) (h2 : ContDiff ℝ 2 φ) :
    inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (transplant hL φ hs h2))
        ((ContinuousMap.toLp 2 volume ℂ) (coulombPositionContDiffKinetic sys L
          (transplant hL φ hs h2) (contDiff_transplant_lift hL hs h2))) =
      ((L ^ Fintype.card (Fin eta × Fin 3))⁻¹ : ℝ) •
        ∫ r, freeKinetic sys.mass φ r * conj (φ r) := by
  rw [ContinuousMap.inner_toLp]
  have hfun : (fun x => coulombPositionContDiffKinetic sys L (transplant hL φ hs h2)
      (contDiff_transplant_lift hL hs h2) x * conj ((transplant hL φ hs h2) x)) =
      transplantFun L (fun r => freeKinetic sys.mass φ r * conj (φ r)) := by
    funext x
    rw [contDiffKinetic_transplant sys hL hs h2 x]
    rfl
  rw [hfun]
  exact integral_transplant hL _ (hs.mul_conj _)

/-- **The potential output of a transplant**: `V (Tφ)` is in `L²`, and
`⟨Tφ, V Tφ⟩ = L^{-3η} ∫ (V_∞ - C₀) |φ|²`, with an integrable integrand. -/
theorem transplant_potential (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hθ : Profile R θ) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {φ : Rcfg eta → ℂ} (h2 : ContDiff ℝ 2 φ) (hsupp : SuppRet L R0 ρ φ) :
    ∃ p : MolecularPositionL2 eta,
      HasL2PointwisePotential volume (gLFourierPotential sys L θ)
        ((ContinuousMap.toLp 2 volume ℂ) (transplant hL φ (hsupp.supp4 hR0 hρ) h2)) p ∧
      inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (transplant hL φ (hsupp.supp4 hR0 hρ) h2)) p =
        ((L ^ Fintype.card (Fin eta × Fin 3))⁻¹ : ℝ) •
          ∫ r, ((freePot sys P r : ℂ) - zeroModeShift sys L θ) * φ r * conj (φ r) ∧
      Integrable (fun r => ((freePot sys P r : ℂ) - zeroModeShift sys L θ) * φ r *
        conj (φ r)) := by
  have hs4 : Supp4 L φ := hsupp.supp4 hR0 hρ
  set T := transplant hL φ hs4 h2 with hT
  have hTmem : MemLp (fun x => T x) ⊤ volume :=
    memLp_top_of_bound T.continuous.aestronglyMeasurable ‖T‖
      (ae_of_all _ fun x => T.norm_coe_le_norm x)
  have hpmem : MemLp (fun x => gLFourierPotential sys L θ x * T x) 2 volume :=
    hTmem.mul' (gLFourierPotential_memLp sys hL hθ)
  have hcT := T.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure (MolecularPositionTorus eta))
  have hp : HasL2PointwisePotential volume (gLFourierPotential sys L θ)
      ((ContinuousMap.toLp 2 volume ℂ) T) (hpmem.toLp _) := by
    filter_upwards [hpmem.coeFn_toLp, hcT] with x h1 h2
    rw [h1, h2]
  have hpot_fun : ∀ x, gLFourierPotential sys L θ x * T x * conj (T x) =
      transplantFun L (fun r => ((freePot sys P r : ℂ) - zeroModeShift sys L θ) * φ r *
        conj (φ r)) x := by
    intro x
    rw [transplantFun_eq]
    have hTx : T x = φ (cellCoord L x) := rfl
    by_cases h0 : φ (cellCoord L x) = 0
    · rw [hTx, h0]
      simp
    · rw [gLFourierPotential_eq_freePot sys hL hR0 hρ hone P hP hpos x (hsupp _ h0), hTx]
  have hae : (fun x => inner ℂ (((ContinuousMap.toLp 2 volume ℂ) T) x) ((hpmem.toLp _) x))
      =ᵐ[volume] transplantFun L (fun r => ((freePot sys P r : ℂ) - zeroModeShift sys L θ) *
        φ r * conj (φ r)) := by
    filter_upwards [hp, hcT] with x h1 h2
    rw [RCLike.inner_apply, h1, h2, hpot_fun x]
  refine ⟨hpmem.toLp _, hp, ?_, ?_⟩
  · rw [MeasureTheory.L2.inner_def, integral_congr_ae hae]
    exact integral_transplant hL _ (hs4.mul_conj _)
  · exact integrable_of_transplant hL (hs4.mul_conj _)
      ((MeasureTheory.L2.integrable_inner (𝕜 := ℂ) _ _).congr hae)

/-- **`prop:free`, the transplant inequality.** Let `θ ≡ 1` on `[0, L/2 - ρ]`, the nuclei at
`P_ℓ ∈ B_{R₀}(0)` (on the torus at `-P_ℓ/L`, the release's convention), and `E_L` the torus
ground energy of the sector (`PlaneWave.FreeBoundary.TorusGroundEnergy`, zero mode removed). Every `C²` state `φ` of the
free-space sector supported in the retained region `B_{R_L}(0)^η`, `R_L = L/4 - R₀ - ρ`, has an
integrable Coulomb term and `(E_L + C₀) ‖φ‖² ≤ Re⟨φ, K φ⟩ + ∫ V_∞ |φ|²`, `C₀` the zero-mode
shift: the free-space energy of `φ` bounds the torus energy (zero mode included). -/
theorem free_transplant_bound (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} {L R R0 ρ : ℝ}
    {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {E : ℝ} (hE : IsGLTorusGroundEnergy sys lab L θ E)
    {φ : Rcfg eta → ℂ} (h2 : ContDiff ℝ 2 φ) (hsupp : SuppRet L R0 ρ φ)
    (hS : IsFreeSector sys.sign lab φ) :
    Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      (E + (zeroModeShift sys L θ).re) * ∫ r, ‖φ r‖ ^ 2 ≤
        (∫ r, freeKinetic sys.mass φ r * conj (φ r)).re + ∫ r, freePot sys P r * ‖φ r‖ ^ 2 := by
  have hs4 : Supp4 L φ := hsupp.supp4 hR0 hρ
  obtain ⟨p, hp, hinner, hint⟩ := transplant_potential sys hL hθ hR0 hρ hone P hP hpos h2 hsupp
  have hvar := gL_variational_C2 sys hL hθ hR hE (transplant hL φ hs4 h2)
    (contDiff_transplant_lift hL hs4 h2) (transplant_isPositionSector hL hs4 h2 hS) p hp
  rw [norm_sq_toLp_transplant hL hs4 h2, inner_kinetic_transplant sys hL hs4 h2, hinner,
    Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul] at hvar
  have hint2 := integrable_mul_conj hL hs4 h2
  have hc2 : ∀ r, φ r * conj (φ r) = ((‖φ r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hpt : ∀ r, ((freePot sys P r : ℂ) - zeroModeShift sys L θ) * φ r * conj (φ r) =
      ((freePot sys P r * ‖φ r‖ ^ 2 : ℝ) : ℂ) - zeroModeShift sys L θ * ((‖φ r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    rw [mul_assoc, hc2]
    push_cast
    ring
  have hint2' : Integrable (fun r => ((‖φ r‖ ^ 2 : ℝ) : ℂ)) := by
    refine hint2.congr (ae_of_all _ fun r => ?_)
    exact hc2 r
  have hint3 : Integrable (fun r => ((freePot sys P r * ‖φ r‖ ^ 2 : ℝ) : ℂ)) := by
    have hfun : (fun r => ((freePot sys P r * ‖φ r‖ ^ 2 : ℝ) : ℂ)) = fun r =>
        ((freePot sys P r : ℂ) - zeroModeShift sys L θ) * φ r * conj (φ r) +
          zeroModeShift sys L θ * ((‖φ r‖ ^ 2 : ℝ) : ℂ) := by
      funext r
      rw [hpt]
      ring
    rw [hfun]
    exact hint.add (hint2'.const_mul _)
  have hreal : Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) := by
    refine hint3.re.congr (ae_of_all _ fun r => ?_)
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine ⟨hreal, ?_⟩
  have hsplit : ∫ r, ((freePot sys P r : ℂ) - zeroModeShift sys L θ) * φ r * conj (φ r) =
      ((∫ r, freePot sys P r * ‖φ r‖ ^ 2 : ℝ) : ℂ) -
        zeroModeShift sys L θ * ((∫ r, ‖φ r‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]
    rw [integral_sub hint3 (hint2'.const_mul _), integral_const_mul, integral_complex_ofReal,
      integral_complex_ofReal]
  rw [hsplit, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hvar
  set c : ℝ := (L ^ Fintype.card (Fin eta × Fin 3))⁻¹ with hc_def
  have hc : 0 < c := by positivity
  set N : ℝ := ∫ r, ‖φ r‖ ^ 2
  set I : ℝ := ∫ r, freePot sys P r * ‖φ r‖ ^ 2
  set A : ℝ := (∫ r, freeKinetic sys.mass φ r * conj (φ r)).re
  set z : ℝ := (zeroModeShift sys L θ).re
  have key : c * ((E + z) * N) ≤ c * (A + I) := by
    have e1 : c * ((E + z) * N) = E * (c * N) + c * (z * N) := by ring
    have e2 : c * (A + I) = c * A + c * (I - z * N) + c * (z * N) := by ring
    rw [e1, e2]
    linarith [hvar]
  exact le_of_mul_le_mul_left key hc

/-- **`prop:free`, upper bound, from retained trial states.** If for every `ε > 0` the
free-space sector has a `C²` state supported in the retained region with energy at most
`E_∞ + δ + ε` per unit norm (for the free ground state: a cut-off `χψ_∞`, `δ` the IMS
localisation error, `δ ≤ C e^{-α R_L}` by Agmon decay), then `E_L + C₀ ≤ E_∞ + δ`. -/
theorem free_upper_of_trial (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} {L R R0 ρ : ℝ}
    {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {E : ℝ} (hE : IsGLTorusGroundEnergy sys lab L θ E) {Einf δ : ℝ}
    (htrial : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ SuppRet L R0 ρ φ ∧
      IsFreeSector sys.sign lab φ ∧ 0 < ∫ r, ‖φ r‖ ^ 2 ∧
      (∫ r, freeKinetic sys.mass φ r * conj (φ r)).re + ∫ r, freePot sys P r * ‖φ r‖ ^ 2 ≤
        (Einf + δ + ε) * ∫ r, ‖φ r‖ ^ 2) :
    E + (zeroModeShift sys L θ).re ≤ Einf + δ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨φ, h2, hsupp, hS, hN, hen⟩ := htrial ε hε
  have hb := (free_transplant_bound sys hL hθ hR hR0 hρ hone P hP hpos hE h2 hsupp hS).2
  exact le_of_mul_le_mul_right (hb.trans hen) hN

end System

end

end FreeBoundary
