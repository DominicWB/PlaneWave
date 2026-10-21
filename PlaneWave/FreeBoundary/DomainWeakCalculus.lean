import PlaneWave.FreeBoundary.ObservableMomentsUniform
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The cut initial state in `D(H_L²)`, part 1: weak calculus

Tools for `PlaneWave.FreeBoundary.MassWeightedCutoff`–`PlaneWave.FreeBoundary.CutStateDomain`, which
prove that the transplanted cut initial state `φ = T(χ ψ_∞(0))` lies in `D(H_L²)` with bounds
uniform in `L`:

* `contDiff_dirD_nat`, `dirD_comm`, `dirD_freeKinetic`: coordinate derivatives of smooth
  functions commute, also with the free kinetic expression;
* `integrable_conj_mul_weight`, `ibp_weight`: integration by parts against a weak gradient, with a
  compactly supported real weight;
* `HasGLHamiltonian.add`, `.smul`, `.sub`, `.sum`: the torus Hamiltonian relation is linear;
* `BoxWeight.ofReal`: a bounded measurable real weight in the quarter box;
* `contDiff_lift_fourierTest`, `hasGLHamiltonian_of_fourierTests`: the torus kinetic relation is
  tested on trigonometric polynomials, whose periodic lifts are smooth.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15

variable {eta : ℕ}

/-! ## Coordinate derivatives -/

section Derivatives

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma contDiff_dirD_nat {n : ℕ} {f : Rcfg eta → F} (hf : ContDiff ℝ (n + 1) f)
    (a : Fin eta × Fin 3) : ContDiff ℝ n (dirD a f) := by
  have h : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (m := n) le_rfl
  exact h.clm_apply contDiff_const

lemma dirD_eq_snd {f : Rcfg eta → F} (hf : ContDiff ℝ 2 f) (v w : Fin eta × Fin 3)
    (x : Rcfg eta) :
    dirD v (dirD w f) x = fderiv ℝ (fderiv ℝ f) x (Pi.single v 1) (Pi.single w 1) := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  unfold dirD
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simp

/-- **Coordinate derivatives of a `C²` function commute.** -/
lemma dirD_comm {f : Rcfg eta → F} (hf : ContDiff ℝ 2 f) (a b : Fin eta × Fin 3) :
    dirD a (dirD b f) = dirD b (dirD a f) := by
  funext x
  rw [dirD_eq_snd hf, dirD_eq_snd hf]
  exact (ContDiffAt.isSymmSndFDerivAt (f := f) (x := x) hf.contDiffAt (by simp)) _ _

lemma dirD_add_fun {f g : Rcfg eta → F} {x : Rcfg eta} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (a : Fin eta × Fin 3) :
    dirD a (fun y => f y + g y) x = dirD a f x + dirD a g x := by
  unfold dirD
  rw [fderiv_fun_add hf hg]
  rfl

lemma dirD_const_mul {f : Rcfg eta → ℂ} {x : Rcfg eta} (hf : DifferentiableAt ℝ f x) (c : ℂ)
    (a : Fin eta × Fin 3) : dirD a (fun y => c * f y) x = c * dirD a f x := by
  unfold dirD
  rw [fderiv_const_mul hf c]
  rfl

lemma dirD_sum_fun {ι : Type*} (s : Finset ι) {f : ι → Rcfg eta → F} {x : Rcfg eta}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (a : Fin eta × Fin 3) :
    dirD a (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, dirD a (f i) x := by
  unfold dirD
  rw [fderiv_fun_sum hf]
  simp

/-- **The derivative of the kinetic expression**: `∂_a K Ψ = K ∂_a Ψ` for `Ψ ∈ C³`. -/
lemma dirD_freeKinetic (m : Fin eta → ℝ) {Ψ : Rcfg eta → ℂ} (hΨ : ContDiff ℝ 3 Ψ)
    (a : Fin eta × Fin 3) :
    dirD a (freeKinetic m Ψ) = freeKinetic m (dirD a Ψ) := by
  have hΨ2 : ContDiff ℝ 2 Ψ := hΨ.of_le (by norm_num)
  have h1 : ContDiff ℝ 2 (dirD a Ψ) := contDiff_dirD_nat (n := 2) hΨ a
  have hK : freeKinetic m Ψ = fun r => (-(1 / 2 : ℂ)) * ∑ b : Fin eta × Fin 3,
      ((m b.1 : ℂ))⁻¹ * dirD b (dirD b Ψ) r := funext fun r => freeKinetic_eq m hΨ2 r
  have hdd : ∀ b, ContDiff ℝ 1 (dirD b (dirD b Ψ)) := fun b =>
    contDiff_dirD_nat (n := 1) (contDiff_dirD_nat (n := 2) hΨ b) b
  funext x
  rw [hK, freeKinetic_eq m h1 x]
  have hdiff : ∀ b ∈ (Finset.univ : Finset (Fin eta × Fin 3)),
      DifferentiableAt ℝ (fun r => ((m b.1 : ℂ))⁻¹ * dirD b (dirD b Ψ) r) x := fun b _ =>
    (((hdd b).differentiable (by norm_num)) x).const_mul _
  rw [dirD_const_mul (DifferentiableAt.fun_sum hdiff) _ a, dirD_sum_fun _ hdiff a]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dirD_const_mul (((hdd b).differentiable (by norm_num)) x) _ a]
  congr 1
  -- `∂_a ∂_b ∂_b Ψ = ∂_b ∂_b ∂_a Ψ`
  have e1 : dirD a (dirD b (dirD b Ψ)) = dirD b (dirD a (dirD b Ψ)) :=
    dirD_comm (contDiff_dirD_nat (n := 2) hΨ b) a b
  have e2 : dirD a (dirD b Ψ) = dirD b (dirD a Ψ) := dirD_comm hΨ2 a b
  rw [e1, e2]

end Derivatives

/-! ## Integration by parts against a weak gradient -/

section Parts

lemma integrable_conj_mul_weight {Ψ : Rcfg eta → ℂ} (hΨ : Continuous Ψ) {ζ : Rcfg eta → ℝ}
    (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) (f : FreeL2 eta) :
    Integrable (fun r => conj (Ψ r) * ((ζ r : ℂ) * f r)) := by
  have h := integrable_cont_mul_L2 ((Complex.continuous_conj.comp hΨ).mul
    (Complex.continuous_ofReal.comp hζ)) (hasCompactSupport_ofReal hζc).mul_left f
  refine h.congr (ae_of_all _ fun r => ?_)
  simp only [Function.comp_apply, Pi.mul_apply]
  ring

/-- **Integration by parts with a weight**: for `f` with weak gradient `G`, a `C¹` real weight `ζ`
of compact support and a `C¹` function `Ψ`,
`∫ conj(∂_aΨ) ζ f = -∫ conj(Ψ) (∂_aζ) f - ∫ conj(Ψ) ζ G_a`. -/
lemma ibp_weight {f : FreeL2 eta} {G : Fin eta × Fin 3 → FreeL2 eta} (hG : HasWeakGrad f G)
    {ζ : Rcfg eta → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ)
    {Ψ : Rcfg eta → ℂ} (hΨ : ContDiff ℝ 1 Ψ) (a : Fin eta × Fin 3) :
    ∫ r, conj (dirD a Ψ r) * ((ζ r : ℂ) * f r) =
      -(∫ r, conj (Ψ r) * (((dirD a ζ r : ℝ) : ℂ) * f r)) -
        ∫ r, conj (Ψ r) * ((ζ r : ℂ) * G a r) := by
  have hφ : ContDiff ℝ 1 (fun y => (ζ y : ℂ) * Ψ y) :=
    (Complex.ofRealCLM.contDiff.comp hζ).mul hΨ
  have hφc : HasCompactSupport (fun y => (ζ y : ℂ) * Ψ y) :=
    (hasCompactSupport_ofReal hζc).mul_right
  have hW := hG _ hφ hφc a
  have hζd : Differentiable ℝ ζ := hζ.differentiable (by norm_num)
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hdφ : ∀ r, dirD a (fun y => (ζ y : ℂ) * Ψ y) r =
      ((dirD a ζ r : ℝ) : ℂ) * Ψ r + (ζ r : ℂ) * dirD a Ψ r := fun r =>
    dirD_ofReal_mul (hζd r) (hΨd r) a
  have hΨc : Continuous Ψ := hΨ.continuous
  have hdΨc : Continuous (dirD a Ψ) := continuous_dirD hΨ (by norm_num) a
  have hdζc : Continuous (dirD a ζ) := continuous_dirD hζ (by norm_num) a
  have hdζcs : HasCompactSupport (dirD a ζ) := hasCompactSupport_dirD hζc a
  have hI1 := integrable_conj_mul_weight hΨc hdζc hdζcs f
  have hI2 := integrable_conj_mul_weight hdΨc hζ.continuous hζc f
  -- rewrite the weak gradient test
  have hL : ∫ r, conj ((ζ r : ℂ) * Ψ r) * G a r = ∫ r, conj (Ψ r) * ((ζ r : ℂ) * G a r) := by
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have hR : ∫ r, conj (dirD a (fun y => (ζ y : ℂ) * Ψ y) r) * f r =
      (∫ r, conj (Ψ r) * (((dirD a ζ r : ℝ) : ℂ) * f r)) +
        ∫ r, conj (dirD a Ψ r) * ((ζ r : ℂ) * f r) := by
    rw [← integral_add hI1 hI2]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [hdφ, map_add, map_mul, Complex.conj_ofReal]
    ring
  rw [hL, hR] at hW
  linear_combination hW

end Parts

/-! ## Linearity of the torus Hamiltonian relation -/

section Linear

variable {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} {θ : ℝ → ℝ}

lemma HasGLHamiltonian.add {f₁ f₂ h₁ h₂ : MolecularPositionL2 eta}
    (h1 : HasGLHamiltonian sys L θ f₁ h₁) (h2 : HasGLHamiltonian sys L θ f₂ h₂) :
    HasGLHamiltonian sys L θ (f₁ + f₂) (h₁ + h₂) := by
  obtain ⟨v₁, hv₁, hk₁⟩ := h1
  obtain ⟨v₂, hv₂, hk₂⟩ := h2
  refine ⟨v₁ + v₂, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add v₁ v₂, Lp.coeFn_add f₁ f₂, hv₁, hv₂] with x e1 e2 e3 e4
    rw [e1, e2, Pi.add_apply, Pi.add_apply, e3, e4]
    ring
  · intro φ hφ
    have e : h₁ + h₂ - (v₁ + v₂) = (h₁ - v₁) + (h₂ - v₂) := by abel
    rw [e, inner_add_right, inner_add_right, hk₁ φ hφ, hk₂ φ hφ]

lemma HasGLHamiltonian.smul {f h : MolecularPositionL2 eta} (hf : HasGLHamiltonian sys L θ f h)
    (c : ℂ) : HasGLHamiltonian sys L θ (c • f) (c • h) := by
  obtain ⟨v, hv, hk⟩ := hf
  refine ⟨c • v, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul c v, Lp.coeFn_smul c f, hv] with x e1 e2 e3
    rw [e1, e2, Pi.smul_apply, Pi.smul_apply, e3, smul_eq_mul, smul_eq_mul]
    ring
  · intro φ hφ
    rw [← smul_sub, inner_smul_right, inner_smul_right, hk φ hφ]

lemma HasGLHamiltonian.zero : HasGLHamiltonian sys L θ (0 : MolecularPositionL2 eta) 0 := by
  refine ⟨0, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (MolecularPositionTorus eta))] with x e
    rw [e]
    simp
  · intro φ hφ
    simp

lemma HasGLHamiltonian.neg {f h : MolecularPositionL2 eta} (hf : HasGLHamiltonian sys L θ f h) :
    HasGLHamiltonian sys L θ (-f) (-h) := by
  have := hf.smul sys (-1)
  simpa using this

lemma HasGLHamiltonian.sub {f₁ f₂ h₁ h₂ : MolecularPositionL2 eta}
    (h1 : HasGLHamiltonian sys L θ f₁ h₁) (h2 : HasGLHamiltonian sys L θ f₂ h₂) :
    HasGLHamiltonian sys L θ (f₁ - f₂) (h₁ - h₂) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h1.add sys (h2.neg sys)

lemma HasGLHamiltonian.sum {ι : Type*} (s : Finset ι) {f h : ι → MolecularPositionL2 eta}
    (hf : ∀ i ∈ s, HasGLHamiltonian sys L θ (f i) (h i)) :
    HasGLHamiltonian sys L θ (∑ i ∈ s, f i) (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasGLHamiltonian.zero sys
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j s)).add sys
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Linear

/-! ## Real weights in the quarter box -/

/-- A bounded measurable real weight supported in the quarter box. -/
def BoxWeight.ofReal {L : ℝ} (w : Rcfg eta → ℝ) (hm : Measurable w) (B : ℝ)
    (hB : ∀ r, |w r| ≤ B) (hs : ∀ r, w r ≠ 0 → ∀ a, |r a| ≤ L / 4) : BoxWeight eta L where
  w := fun r => (w r : ℂ)
  meas := (Complex.continuous_ofReal.measurable.comp hm)
  B := B
  bound := fun r => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hB r
  supp := fun r hr => hs r fun h => hr (by rw [h, Complex.ofReal_zero])

lemma BoxWeight.ofReal_w {L : ℝ} (w : Rcfg eta → ℝ) (hm : Measurable w) (B : ℝ)
    (hB : ∀ r, |w r| ≤ B) (hs : ∀ r, w r ≠ 0 → ∀ a, |r a| ≤ L / 4) (r : Rcfg eta) :
    (BoxWeight.ofReal (L := L) w hm B hB hs).w r = (w r : ℂ) := rfl

lemma BoxWeight.ofReal_B {L : ℝ} (w : Rcfg eta → ℝ) (hm : Measurable w) (B : ℝ)
    (hB : ∀ r, |w r| ≤ B) (hs : ∀ r, w r ≠ 0 → ∀ a, |r a| ≤ L / 4) :
    (BoxWeight.ofReal (L := L) w hm B hB hs).B = B := rfl

/-! ## Trigonometric test functions -/

section Tests

/-- The periodic lifts of the Fourier characters are smooth. -/
lemma contDiff_mFourier_realLift {d : Type*} [Fintype d] (n : d → ℤ) (k : ℕ) :
    ContDiff ℝ k (torusRealLift (UnitAddTorus.mFourier n)) := by
  change ContDiff ℝ k (fun y : d → ℝ => ∏ a : d, fourier (n a) (y a : UnitAddCircle))
  simp_rw [fourier_coe_apply]
  apply contDiff_prod
  intro a _ha
  have hEval : ContDiff ℝ k (fun y : d → ℝ => (y a : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ a)
  exact ((contDiff_const.mul hEval).div_const (1 : ℂ)).cexp

/-- The periodic lift of a trigonometric polynomial is smooth. -/
lemma contDiff_lift_fourierTest (s : Finset (FourierConfig eta Lattice3))
    (c : FourierConfig eta Lattice3 → ℂ) (k : ℕ) :
    ContDiff ℝ k (torusRealLift (molecularPositionFourierTest eta s c)) := by
  change ContDiff ℝ k (fun y : (Fin eta × Fin 3) → ℝ =>
    molecularPositionFourierTest eta s c (torusRealQuotient _ y))
  simp_rw [molecularPositionFourierTest_apply]
  apply ContDiff.sum
  intro p _hp
  exact contDiff_const.mul (contDiff_mFourier_realLift (molecularFourierIndexEquiv eta p) k)

/-- The free-space test function `Ψ(r) = Φ(r/L)` of a trigonometric polynomial `Φ`. -/
noncomputable def liftTest (L : ℝ) (s : Finset (FourierConfig eta Lattice3))
    (c : FourierConfig eta Lattice3 → ℂ) (r : Rcfg eta) : ℂ :=
  torusRealLift (molecularPositionFourierTest eta s c) (L⁻¹ • r)

lemma contDiff_liftTest (L : ℝ) (s : Finset (FourierConfig eta Lattice3))
    (c : FourierConfig eta Lattice3 → ℂ) (k : ℕ) : ContDiff ℝ k (liftTest L s c) :=
  (contDiff_lift_fourierTest s c k).comp (contDiff_const_smul L⁻¹)

variable {ν : Type} [Fintype ν]

/-- **The torus kinetic energy of a test, in free space**: the lift of `K_L Φ` is `K Ψ`. -/
lemma lift_kineticTest (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    (s : Finset (FourierConfig eta Lattice3)) (c : FourierConfig eta Lattice3 → ℂ)
    (r : Rcfg eta) :
    torusRealLift (coulombPositionKineticTest sys (2 * Real.pi / L) s c) (L⁻¹ • r) =
      freeKinetic sys.mass (liftTest L s c) r := by
  rw [← coulombPositionContDiffKinetic_fourierTest sys L s c]
  exact (freeKinetic_lift sys hL.ne' _ (contDiff_two_molecularPositionFourierTest_realLift eta s c)
    r).symm

/-- **The torus Hamiltonian relation from trigonometric tests**: `H_L f = h` follows from the
potential relation `V_L f = v` and the kinetic identities `⟨Φ, h - v⟩ = ⟨K_L Φ, f⟩` for the
trigonometric polynomials `Φ`. -/
lemma hasGLHamiltonian_of_fourierTests (sys : CoulombSystem eta ν) {L : ℝ} {θ : ℝ → ℝ}
    {f h v : MolecularPositionL2 eta}
    (hv : HasL2PointwisePotential volume (gLFourierPotential sys L θ) f v)
    (hk : ∀ (s : Finset (FourierConfig eta Lattice3)) (c : FourierConfig eta Lattice3 → ℂ),
      inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (molecularPositionFourierTest eta s c)) (h - v) =
        inner ℂ ((ContinuousMap.toLp 2 volume ℂ)
          (coulombPositionKineticTest sys (2 * Real.pi / L) s c)) f) :
    HasGLHamiltonian sys L θ f h :=
  ⟨v, hv, (hasCoulombContDiffWeakKinetic_iff sys L f (h - v)).mpr hk⟩

/-- `⟨Φ, T_w f⟩` for a trigonometric test, in free space. -/
lemma inner_test_cutL2 {L : ℝ} (hL : 0 < L) (W : BoxWeight eta L)
    (s : Finset (FourierConfig eta Lattice3)) (c : FourierConfig eta Lattice3 → ℂ)
    (f : FreeL2 eta) :
    inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (molecularPositionFourierTest eta s c))
        (W.cutL2 hL f) =
      ((tScale eta L : ℂ))⁻¹ * ∫ r, conj (liftTest L s c r) * (W.w r * f r) :=
  BoxWeight.inner_cutL2 hL W _ f

/-- `⟨K_L Φ, T_w f⟩` for a trigonometric test, in free space. -/
lemma inner_kineticTest_cutL2 (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    (W : BoxWeight eta L) (s : Finset (FourierConfig eta Lattice3))
    (c : FourierConfig eta Lattice3 → ℂ) (f : FreeL2 eta) :
    inner ℂ ((ContinuousMap.toLp 2 volume ℂ)
        (coulombPositionKineticTest sys (2 * Real.pi / L) s c)) (W.cutL2 hL f) =
      ((tScale eta L : ℂ))⁻¹ *
        ∫ r, conj (freeKinetic sys.mass (liftTest L s c) r) * (W.w r * f r) := by
  rw [BoxWeight.inner_cutL2 hL W _ f]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  simp only
  rw [lift_kineticTest sys hL s c r]

end Tests

end FreeBoundary
