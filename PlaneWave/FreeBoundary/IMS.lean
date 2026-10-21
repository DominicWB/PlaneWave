import PlaneWave.FreeBoundary.Transplant
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# `app:free`, part 12: IMS localisation

The IMS localisation formula for the free-space kinetic form, from Mathlib's integration by parts
on `ℝ^{3η}` (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`):

* `integral_freeKinetic_mul_conj`: for a `C²` function `u` of compact support,
  `∫ (K u) ū = (1/2) Σ_a m_a⁻¹ ∫ |∂_a u|²` (`gradForm`);
* `gradForm_ims`: for real `C²` functions `χ, η` with `χ² + η² = 1`,
  `T(χφ) + T(ηφ) = T(φ) + (1/2) Σ_a m_a⁻¹ ∫ ((∂_aχ)² + (∂_aη)²) |φ|²`;
* `LocPair`, **`retained_trial`**: if the free-space energy `E_∞` is a lower bound of the form on
  the `C²` sector states of compact support, a normalised state `φ` with energy `≤ E_∞ + ε` and
  mass `≤ τ` outside the inner region `S` gives the retained trial state `χφ` with energy
  `≤ (E_∞ + (Mτ/2 + ε)/(1 - τ)) ‖χφ‖²`;
* **`free_upper_ims`**: `E_L + C₀ ≤ E_∞ + Mτ/(2(1 - τ))` when such states exist for every `ε > 0`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

variable {eta : ℕ}

/-! ## Coordinate derivatives -/

/-- The derivative of `f` along the coordinate `a`. -/
def dirD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : Fin eta × Fin 3)
    (f : Rcfg eta → F) (x : Rcfg eta) : F :=
  fderiv ℝ f x (Pi.single a 1)

lemma hasDerivAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Rcfg eta → F} {r e : Rcfg eta} {t : ℝ} {f' : Rcfg eta →L[ℝ] F}
    (hf : HasFDerivAt f f' (r + t • e)) :
    HasDerivAt (fun s : ℝ => f (r + s • e)) (f' e) t := by
  have hl : HasDerivAt (fun s : ℝ => r + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add r
  exact hf.comp_hasDerivAt t hl

lemma contDiff_dirD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Rcfg eta → F}
    (hf : ContDiff ℝ 2 f) (a : Fin eta × Fin 3) : ContDiff ℝ 1 (dirD a f) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma continuous_dirD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Rcfg eta → F}
    {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hn : n ≠ 0) (a : Fin eta × Fin 3) :
    Continuous (dirD a f) :=
  (hf.continuous_fderiv hn).clm_apply continuous_const

lemma hasCompactSupport_dirD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Rcfg eta → F} (hf : HasCompactSupport f) (a : Fin eta × Fin 3) :
    HasCompactSupport (dirD a f) :=
  hf.fderiv_apply (𝕜 := ℝ) (Pi.single a 1)

/-- The second line derivative of the kinetic expression is the iterated coordinate derivative. -/
lemma deriv2_line_eq {f : Rcfg eta → ℂ} (hf : ContDiff ℝ 2 f) (r : Rcfg eta)
    (a : Fin eta × Fin 3) :
    deriv (deriv (fun s : ℝ => f (r + s • Pi.single a 1))) 0 = dirD a (dirD a f) r := by
  have h1 : deriv (fun s : ℝ => f (r + s • Pi.single a 1)) =
      fun t => dirD a f (r + t • Pi.single a 1) := by
    funext t
    exact (hasDerivAt_line (r := r) (e := Pi.single a 1) (t := t)
      ((hf.differentiable (by norm_num)) (r + t • Pi.single a 1)).hasFDerivAt).deriv
  rw [h1]
  have h2 := hasDerivAt_line (r := r) (e := Pi.single a (1 : ℝ)) (t := 0)
    (((contDiff_dirD hf a).differentiable (by norm_num))
      (r + (0 : ℝ) • Pi.single a 1)).hasFDerivAt
  rw [zero_smul, add_zero] at h2
  exact h2.deriv

lemma freeKinetic_eq (m : Fin eta → ℝ) {f : Rcfg eta → ℂ} (hf : ContDiff ℝ 2 f)
    (r : Rcfg eta) :
    freeKinetic m f r = (-(1 / 2 : ℂ)) * ∑ a : Fin eta × Fin 3, ((m a.1 : ℂ))⁻¹ *
      dirD a (dirD a f) r := by
  unfold freeKinetic
  simp_rw [deriv2_line_eq hf r]

lemma fderiv_conj_apply {u : Rcfg eta → ℂ} {x : Rcfg eta} (hu : DifferentiableAt ℝ u x)
    (v : Rcfg eta) : fderiv ℝ (fun y => conj (u y)) x v = conj (fderiv ℝ u x v) := by
  have h := HasFDerivAt.star hu.hasFDerivAt
  simp only [starRingEnd_apply]
  rw [h.fderiv]
  rfl

lemma conj_mul_self_eq (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-! ## The kinetic form by parts -/

/-- `∫ (∂_a² u) ū = -∫ |∂_a u|²` for `u ∈ C²` of compact support. -/
lemma integral_dirD2_mul_conj {u : Rcfg eta → ℂ} (hu : ContDiff ℝ 2 u)
    (hcs : HasCompactSupport u) (a : Fin eta × Fin 3) :
    ∫ x, dirD a (dirD a u) x * conj (u x) = -∫ x, ((‖dirD a u x‖ ^ 2 : ℝ) : ℂ) := by
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hg1 : ContDiff ℝ 1 (dirD a u) := contDiff_dirD hu a
  have hgd : Differentiable ℝ (dirD a u) := hg1.differentiable (by norm_num)
  have hgc : Continuous (dirD a u) := hg1.continuous
  have hg2c : Continuous (dirD a (dirD a u)) := continuous_dirD hg1 (by norm_num) a
  have hfc : Continuous (fun x => conj (u x)) := Complex.continuous_conj.comp hu.continuous
  have hfd : Differentiable ℝ (fun x => conj (u x)) := fun x => DifferentiableAt.star (hd x)
  have hfcs : HasCompactSupport (fun x => conj (u x)) :=
    hcs.comp_left (g := fun z : ℂ => conj z) (by simp)
  have hgcs : HasCompactSupport (dirD a u) := hasCompactSupport_dirD hcs a
  have hfder : (fun x => fderiv ℝ (fun y => conj (u y)) x (Pi.single a 1)) =
      fun x => conj (dirD a u x) := by
    funext x
    exact fderiv_conj_apply (hd x) _
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun x => conj (u x)) (g := dirD a u) (v := Pi.single a 1)
    (by
      have hfun : (fun x => fderiv ℝ (fun y => conj (u y)) x (Pi.single a 1) * dirD a u x) =
          fun x => conj (dirD a u x) * dirD a u x := by
        funext x
        rw [fderiv_conj_apply (hd x)]
        rfl
      rw [hfun]
      exact (Complex.continuous_conj.comp hgc |>.mul hgc).integrable_of_hasCompactSupport
        (hgcs.mono (Function.support_mul_subset_right _ _)))
    ((hfc.mul hg2c).integrable_of_hasCompactSupport
      (hfcs.mono (Function.support_mul_subset_left _ _)))
    ((hfc.mul hgc).integrable_of_hasCompactSupport
      (hfcs.mono (Function.support_mul_subset_left _ _)))
    (fun x _ => hfd x) (fun x _ => hgd x)
  calc ∫ x, dirD a (dirD a u) x * conj (u x)
      = ∫ x, conj (u x) * fderiv ℝ (dirD a u) x (Pi.single a 1) := by
        congr 1
        funext x
        rw [mul_comm]
        rfl
    _ = -∫ x, fderiv ℝ (fun y => conj (u y)) x (Pi.single a 1) * dirD a u x := h
    _ = -∫ x, ((‖dirD a u x‖ ^ 2 : ℝ) : ℂ) := by
        congr 2
        funext x
        rw [fderiv_conj_apply (hd x)]
        exact conj_mul_self_eq (dirD a u x)

/-- The gradient form `(1/2) Σ_a m_a⁻¹ ∫ |∂_a u|²`. -/
def gradForm (m : Fin eta → ℝ) (u : Rcfg eta → ℂ) : ℝ :=
  (1 / 2) * ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ∫ x, ‖dirD a u x‖ ^ 2

lemma integrable_dirD2_mul_conj {u : Rcfg eta → ℂ} (hu : ContDiff ℝ 2 u)
    (hcs : HasCompactSupport u) (a : Fin eta × Fin 3) :
    Integrable (fun x => dirD a (dirD a u) x * conj (u x)) := by
  have hg2c : Continuous (dirD a (dirD a u)) := continuous_dirD (contDiff_dirD hu a) (by norm_num) a
  have hfc : Continuous (fun x => conj (u x)) := Complex.continuous_conj.comp hu.continuous
  have hfcs : HasCompactSupport (fun x => conj (u x)) :=
    hcs.comp_left (g := fun z : ℂ => conj z) (by simp)
  exact (hg2c.mul hfc).integrable_of_hasCompactSupport
    (hfcs.mono (Function.support_mul_subset_right _ _))

/-- **The kinetic form by parts**: `∫ (K u) ū = (1/2) Σ_a m_a⁻¹ ∫ |∂_a u|²`. -/
theorem integral_freeKinetic_mul_conj (m : Fin eta → ℝ) {u : Rcfg eta → ℂ}
    (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) :
    ∫ x, freeKinetic m u x * conj (u x) = (gradForm m u : ℂ) := by
  have hpt : ∀ x, freeKinetic m u x * conj (u x) = ∑ a : Fin eta × Fin 3,
      (-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹ * (dirD a (dirD a u) x * conj (u x)) := by
    intro x
    rw [freeKinetic_eq m hu, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun a _ => (integrable_dirD2_mul_conj hu hcs a).const_mul _)]
  simp_rw [integral_const_mul, integral_dirD2_mul_conj hu hcs, integral_complex_ofReal]
  unfold gradForm
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ## The IMS formula -/

lemma dirD_ofReal_mul {χ : Rcfg eta → ℝ} {φ : Rcfg eta → ℂ} {x : Rcfg eta}
    (hχ : DifferentiableAt ℝ χ x) (hφ : DifferentiableAt ℝ φ x) (a : Fin eta × Fin 3) :
    dirD a (fun y => (χ y : ℂ) * φ y) x =
      ((dirD a χ x : ℝ) : ℂ) * φ x + (χ x : ℂ) * dirD a φ x := by
  have hc : HasFDerivAt (fun y => (χ y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ χ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hχ.hasFDerivAt
  have h : HasFDerivAt (fun y => (χ y : ℂ) * φ y)
      ((χ x : ℂ) • fderiv ℝ φ x + φ x • Complex.ofRealCLM.comp (fderiv ℝ χ x)) x :=
    hc.mul hφ.hasFDerivAt
  unfold dirD
  rw [h.fderiv]
  simp
  ring

lemma cutoff_deriv_rel {χ η : Rcfg eta → ℝ} (hχ : Differentiable ℝ χ) (hη : Differentiable ℝ η)
    (h1 : ∀ r, χ r ^ 2 + η r ^ 2 = 1) (a : Fin eta × Fin 3) (x : Rcfg eta) :
    χ x * dirD a χ x + η x * dirD a η x = 0 := by
  have hconst : (fun y => χ y * χ y + η y * η y) = fun _ => (1 : ℝ) := by
    funext y
    rw [← h1 y]
    ring
  have h : HasFDerivAt (fun y => χ y * χ y + η y * η y)
      ((χ x • fderiv ℝ χ x + χ x • fderiv ℝ χ x) +
        (η x • fderiv ℝ η x + η x • fderiv ℝ η x)) x :=
    ((hχ x).hasFDerivAt.mul (hχ x).hasFDerivAt).add ((hη x).hasFDerivAt.mul (hη x).hasFDerivAt)
  rw [hconst] at h
  have h0 := h.unique (hasFDerivAt_const (1 : ℝ) x)
  have h0' := congrArg (fun T : Rcfg eta →L[ℝ] ℝ => T (Pi.single a (1 : ℝ))) h0
  rw [show (0 : Rcfg eta →L[ℝ] ℝ) (Pi.single a (1 : ℝ)) = 0 from rfl] at h0'
  have e1 : ((χ x • fderiv ℝ χ x + χ x • fderiv ℝ χ x) +
      (η x • fderiv ℝ η x + η x • fderiv ℝ η x)) (Pi.single a (1 : ℝ)) =
      2 * (χ x * dirD a χ x + η x * dirD a η x) := by
    simp [dirD]
    ring
  rw [e1] at h0'
  linarith

lemma ims_pointwise {p q s t : ℝ} {z w : ℂ} (h1 : q ^ 2 + t ^ 2 = 1) (h2 : q * p + t * s = 0) :
    ‖(p : ℂ) * z + (q : ℂ) * w‖ ^ 2 + ‖(s : ℂ) * z + (t : ℂ) * w‖ ^ 2 =
      (p ^ 2 + s ^ 2) * ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero]
  linear_combination (w.re * w.re + w.im * w.im) * h1 + 2 * (z.re * w.re + z.im * w.im) * h2

lemma contDiff_ofReal_mul {χ : Rcfg eta → ℝ} {φ : Rcfg eta → ℂ} (hχ : ContDiff ℝ 2 χ)
    (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 2 (fun r => (χ r : ℂ) * φ r) :=
  (Complex.ofRealCLM.contDiff.comp hχ).mul hφ

lemma hasCompactSupport_ofReal_mul {χ : Rcfg eta → ℝ} {φ : Rcfg eta → ℂ}
    (hcs : HasCompactSupport φ) : HasCompactSupport (fun r => (χ r : ℂ) * φ r) :=
  hcs.mono (Function.support_mul_subset_right _ _)

lemma integrable_norm_dirD_sq {u : Rcfg eta → ℂ} (hu : ContDiff ℝ 2 u)
    (hcs : HasCompactSupport u) (a : Fin eta × Fin 3) :
    Integrable (fun x => ‖dirD a u x‖ ^ 2) := by
  have hc : Continuous (fun x => ‖dirD a u x‖ ^ 2) :=
    ((continuous_dirD hu (by norm_num) a).norm).pow 2
  exact hc.integrable_of_hasCompactSupport
    ((hasCompactSupport_dirD hcs a).comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))

/-- **The IMS localisation formula** for the gradient form. -/
theorem gradForm_ims (m : Fin eta → ℝ) {χ η : Rcfg eta → ℝ} {φ : Rcfg eta → ℂ}
    (hχ : ContDiff ℝ 2 χ) (hη : ContDiff ℝ 2 η) (h1 : ∀ r, χ r ^ 2 + η r ^ 2 = 1)
    (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ) :
    gradForm m (fun r => (χ r : ℂ) * φ r) + gradForm m (fun r => (η r : ℂ) * φ r) =
      gradForm m φ + (1 / 2) * ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ *
        ∫ x, (dirD a χ x ^ 2 + dirD a η x ^ 2) * ‖φ x‖ ^ 2 := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hηd : Differentiable ℝ η := hη.differentiable (by norm_num)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hloc : ∀ a : Fin eta × Fin 3, Integrable
      (fun x => (dirD a χ x ^ 2 + dirD a η x ^ 2) * ‖φ x‖ ^ 2) := by
    intro a
    have hc : Continuous (fun x => (dirD a χ x ^ 2 + dirD a η x ^ 2) * ‖φ x‖ ^ 2) :=
      (((continuous_dirD hχ (by norm_num) a).pow 2).add
        ((continuous_dirD hη (by norm_num) a).pow 2)).mul (hφ.continuous.norm.pow 2)
    exact hc.integrable_of_hasCompactSupport
      ((hcs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)).mono
        (Function.support_mul_subset_right _ _))
  unfold gradForm
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_add, ← mul_add]
  congr 1
  rw [← integral_add (integrable_norm_dirD_sq (contDiff_ofReal_mul hχ hφ)
      (hasCompactSupport_ofReal_mul hcs) a)
      (integrable_norm_dirD_sq (contDiff_ofReal_mul hη hφ) (hasCompactSupport_ofReal_mul hcs) a),
    ← integral_add (integrable_norm_dirD_sq hφ hcs a) (hloc a)]
  congr 1
  funext x
  rw [dirD_ofReal_mul (hχd x) (hφd x), dirD_ofReal_mul (hηd x) (hφd x),
    ims_pointwise (h1 x) (cutoff_deriv_rel hχd hηd h1 a x)]
  ring

/-! ## The localised energy -/

lemma norm_ofReal_mul_sq (c : ℝ) (z : ℂ) : ‖(c : ℂ) * z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

lemma integrable_cont_mul_normSq {g : Rcfg eta → ℝ} (hg : Continuous g) {φ : Rcfg eta → ℂ}
    (hφc : Continuous φ) (hcs : HasCompactSupport φ) :
    Integrable (fun x => g x * ‖φ x‖ ^ 2) :=
  (hg.mul (hφc.norm.pow 2)).integrable_of_hasCompactSupport
    ((hcs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)).mono
      (Function.support_mul_subset_right _ _))

lemma integrable_normSq_cut {c : Rcfg eta → ℝ} (hc : Continuous c) {φ : Rcfg eta → ℂ}
    (hφc : Continuous φ) (hcs : HasCompactSupport φ) :
    Integrable (fun r => ‖(c r : ℂ) * φ r‖ ^ 2) := by
  refine (integrable_cont_mul_normSq (hc.pow 2) hφc hcs).congr (ae_of_all _ fun r => ?_)
  beta_reduce
  rw [norm_ofReal_mul_sq]
  rfl

/-- A smooth localisation pair `χ² + η² = 1` for the retained region: `χ` vanishes outside the
retained region `B_{R_L}(0)^η` and equals `1` on the inner region `S`; both are
exchange-invariant; `Σ_a ((∂_aχ)² + (∂_aη)²) ≤ M`, and it vanishes on `S`. -/
structure LocPair (eta : ℕ) (L R0 ρ : ℝ) (S : Set (Rcfg eta)) (M : ℝ) where
  χ : Rcfg eta → ℝ
  η : Rcfg eta → ℝ
  χ_smooth : ContDiff ℝ 2 χ
  η_smooth : ContDiff ℝ 2 η
  sq_add : ∀ r, χ r ^ 2 + η r ^ 2 = 1
  χ_swap : ∀ i j r, χ (freeSwap i j r) = χ r
  η_swap : ∀ i j r, η (freeSwap i j r) = η r
  χ_supp : ∀ r, χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ
  χ_one : ∀ r ∈ S, χ r = 1
  grad_bound : ∀ r, ∑ a, (dirD a χ r ^ 2 + dirD a η r ^ 2) ≤ M
  grad_zero : ∀ r ∈ S, ∀ a, dirD a χ r = 0 ∧ dirD a η r = 0

lemma isFreeSector_cut {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ} {c : Rcfg eta → ℝ}
    (hc : ∀ i j r, c (freeSwap i j r) = c r) {φ : Rcfg eta → ℂ} (hS : IsFreeSector sgn lab φ) :
    IsFreeSector sgn lab (fun r => (c r : ℂ) * φ r) := by
  intro i j hij hlab r
  beta_reduce
  rw [hc i j r, hS i j hij hlab r]
  ring

section System

variable {ν : Type} [Fintype ν]

/-- The free-space energy `Re⟨u, K u⟩ + ∫ V_∞ |u|²`. -/
def freeEnergy (sys : CoulombSystem eta ν) (P : ν → E3) (u : Rcfg eta → ℂ) : ℝ :=
  (∫ r, freeKinetic sys.mass u r * conj (u r)).re + ∫ r, freePot sys P r * ‖u r‖ ^ 2

lemma freeEnergy_eq (sys : CoulombSystem eta ν) (P : ν → E3) {u : Rcfg eta → ℂ}
    (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) :
    freeEnergy sys P u = gradForm sys.mass u + ∫ r, freePot sys P r * ‖u r‖ ^ 2 := by
  unfold freeEnergy
  rw [integral_freeKinetic_mul_conj sys.mass hu hcs, Complex.ofReal_re]

lemma integrable_pot_cut (sys : CoulombSystem eta ν) (P : ν → E3) {φ : Rcfg eta → ℂ}
    (hV : Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2)) {c : Rcfg eta → ℝ}
    (hc : Continuous c) (hc1 : ∀ r, c r ^ 2 ≤ 1) :
    Integrable (fun r => freePot sys P r * ‖(c r : ℂ) * φ r‖ ^ 2) := by
  have h := hV.bdd_mul (f := fun r => c r ^ 2) (c := 1) (hc.pow 2).aestronglyMeasurable
    (ae_of_all _ fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hc1 r)
  refine h.congr (ae_of_all _ fun r => ?_)
  beta_reduce
  rw [norm_ofReal_mul_sq]
  ring

/-- **The IMS localisation formula** for the free-space energy. -/
theorem freeEnergy_ims (sys : CoulombSystem eta ν) (P : ν → E3) {χ η : Rcfg eta → ℝ}
    {φ : Rcfg eta → ℂ} (hχ : ContDiff ℝ 2 χ) (hη : ContDiff ℝ 2 η)
    (h1 : ∀ r, χ r ^ 2 + η r ^ 2 = 1) (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ)
    (hV : Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2)) :
    freeEnergy sys P (fun r => (χ r : ℂ) * φ r) + freeEnergy sys P (fun r => (η r : ℂ) * φ r) =
      freeEnergy sys P φ + (1 / 2) * ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ *
        ∫ x, (dirD a χ x ^ 2 + dirD a η x ^ 2) * ‖φ x‖ ^ 2 := by
  rw [freeEnergy_eq sys P (contDiff_ofReal_mul hχ hφ) (hasCompactSupport_ofReal_mul hcs),
    freeEnergy_eq sys P (contDiff_ofReal_mul hη hφ) (hasCompactSupport_ofReal_mul hcs),
    freeEnergy_eq sys P hφ hcs]
  have hχ1 : ∀ r, χ r ^ 2 ≤ 1 := fun r => by linarith [h1 r, sq_nonneg (η r)]
  have hη1 : ∀ r, η r ^ 2 ≤ 1 := fun r => by linarith [h1 r, sq_nonneg (χ r)]
  have hpot : (∫ r, freePot sys P r * ‖(χ r : ℂ) * φ r‖ ^ 2) +
      (∫ r, freePot sys P r * ‖(η r : ℂ) * φ r‖ ^ 2) = ∫ r, freePot sys P r * ‖φ r‖ ^ 2 := by
    rw [← integral_add (integrable_pot_cut sys P hV hχ.continuous hχ1)
      (integrable_pot_cut sys P hV hη.continuous hη1)]
    congr 1
    funext r
    rw [norm_ofReal_mul_sq, norm_ofReal_mul_sq]
    linear_combination (freePot sys P r * ‖φ r‖ ^ 2) * h1 r
  have hgrad := gradForm_ims sys.mass hχ hη h1 hφ hcs
  linarith [hgrad, hpot]

/-- **The retained trial state.** If `E_∞` bounds the free-space form below on the `C²` sector
states of compact support, a normalised `C²` sector state `φ` with energy `≤ E_∞ + ε` and mass
`≤ τ < 1` outside the inner region `S` gives the retained state `χφ` with
`E(χφ) ≤ (E_∞ + (Mτ/2 + ε)/(1 - τ)) ‖χφ‖²`. -/
theorem retained_trial (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} (P : ν → E3)
    {L R0 ρ M : ℝ} {S : Set (Rcfg eta)} (hSm : MeasurableSet S) (C : LocPair eta L R0 ρ S M)
    {Einf : ℝ}
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    {φ : Rcfg eta → ℂ} (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ)
    (hsec : IsFreeSector sys.sign lab φ) (hV : Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2))
    (hN : ∫ r, ‖φ r‖ ^ 2 = 1) {ε τ : ℝ} (hen : freeEnergy sys P φ ≤ Einf + ε)
    (htail : ∫ r in Sᶜ, ‖φ r‖ ^ 2 ≤ τ) (hτ : τ < 1) :
    ContDiff ℝ 2 (fun r => (C.χ r : ℂ) * φ r) ∧ SuppRet L R0 ρ (fun r => (C.χ r : ℂ) * φ r) ∧
      IsFreeSector sys.sign lab (fun r => (C.χ r : ℂ) * φ r) ∧
      0 < ∫ r, ‖(C.χ r : ℂ) * φ r‖ ^ 2 ∧
      freeEnergy sys P (fun r => (C.χ r : ℂ) * φ r) ≤
        (Einf + (M * τ / 2 + ε) / (1 - τ)) * ∫ r, ‖(C.χ r : ℂ) * φ r‖ ^ 2 := by
  have hχ := C.χ_smooth
  have hη := C.η_smooth
  have h1 := C.sq_add
  have hφc := hφ.continuous
  have hχ1 : ∀ r, C.χ r ^ 2 ≤ 1 := fun r => by linarith [h1 r, sq_nonneg (C.η r)]
  have hη1 : ∀ r, C.η r ^ 2 ≤ 1 := fun r => by linarith [h1 r, sq_nonneg (C.χ r)]
  have hφ2 : Integrable (fun r => ‖φ r‖ ^ 2) := by
    have h := integrable_cont_mul_normSq (g := fun _ => (1 : ℝ)) continuous_const hφc hcs
    simpa using h
  -- the two masses
  have hsum : (∫ r, ‖(C.χ r : ℂ) * φ r‖ ^ 2) + (∫ r, ‖(C.η r : ℂ) * φ r‖ ^ 2) = 1 := by
    rw [← integral_add (integrable_normSq_cut hχ.continuous hφc hcs)
      (integrable_normSq_cut hη.continuous hφc hcs), ← hN]
    congr 1
    funext r
    rw [norm_ofReal_mul_sq, norm_ofReal_mul_sq]
    linear_combination ‖φ r‖ ^ 2 * h1 r
  have hτ0 : 0 ≤ τ :=
    le_trans (setIntegral_nonneg_of_ae (ae_of_all _ fun r => by positivity)) htail
  have hNχ_ge : 1 - τ ≤ ∫ r, ‖(C.χ r : ℂ) * φ r‖ ^ 2 := by
    have hS1 : (∫ r in S, ‖φ r‖ ^ 2) + (∫ r in Sᶜ, ‖φ r‖ ^ 2) = 1 := by
      rw [integral_add_compl hSm hφ2, hN]
    have hS2 : ∫ r in S, ‖φ r‖ ^ 2 ≤ ∫ r, ‖(C.χ r : ℂ) * φ r‖ ^ 2 := by
      have heq : ∫ r in S, ‖φ r‖ ^ 2 = ∫ r in S, ‖(C.χ r : ℂ) * φ r‖ ^ 2 := by
        refine setIntegral_congr_fun hSm fun r hr => ?_
        rw [norm_ofReal_mul_sq, C.χ_one r hr]
        ring
      rw [heq]
      exact setIntegral_le_integral (integrable_normSq_cut hχ.continuous hφc hcs)
        (ae_of_all _ fun r => by positivity)
    linarith
  have hd : 0 < 1 - τ := by linarith
  have hNpos : 0 < ∫ r, ‖(C.χ r : ℂ) * φ r‖ ^ 2 := lt_of_lt_of_le hd hNχ_ge
  -- the localisation error
  have hM0 : 0 ≤ M := le_trans (Finset.sum_nonneg fun a _ => by positivity) (C.grad_bound 0)
  have hG : (1 / 2) * ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ *
      ∫ x, (dirD a C.χ x ^ 2 + dirD a C.η x ^ 2) * ‖φ x‖ ^ 2 ≤ M * τ / 2 := by
    have hint : ∀ a : Fin eta × Fin 3, Integrable
        (fun x => (dirD a C.χ x ^ 2 + dirD a C.η x ^ 2) * ‖φ x‖ ^ 2) := fun a =>
      integrable_cont_mul_normSq (((continuous_dirD hχ (by norm_num) a).pow 2).add
        ((continuous_dirD hη (by norm_num) a).pow 2)) hφc hcs
    have hstep1 : ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ *
        ∫ x, (dirD a C.χ x ^ 2 + dirD a C.η x ^ 2) * ‖φ x‖ ^ 2 ≤
        ∫ x, (∑ a : Fin eta × Fin 3, (dirD a C.χ x ^ 2 + dirD a C.η x ^ 2)) * ‖φ x‖ ^ 2 := by
      rw [show (fun x => (∑ a : Fin eta × Fin 3, (dirD a C.χ x ^ 2 + dirD a C.η x ^ 2)) *
          ‖φ x‖ ^ 2) = fun x => ∑ a : Fin eta × Fin 3,
            (dirD a C.χ x ^ 2 + dirD a C.η x ^ 2) * ‖φ x‖ ^ 2 from
          funext fun x => Finset.sum_mul _ _ _, integral_finsetSum _ (fun a _ => hint a)]
      refine Finset.sum_le_sum fun a _ => ?_
      have hI : 0 ≤ ∫ x, (dirD a C.χ x ^ 2 + dirD a C.η x ^ 2) * ‖φ x‖ ^ 2 :=
        integral_nonneg fun x => by positivity
      have hm : (sys.mass a.1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (sys.one_le_mass a.1)
      nlinarith
    have hstep2 : ∫ x, (∑ a : Fin eta × Fin 3, (dirD a C.χ x ^ 2 + dirD a C.η x ^ 2)) *
        ‖φ x‖ ^ 2 ≤ ∫ x, Sᶜ.indicator (fun r => M * ‖φ r‖ ^ 2) x := by
      refine integral_mono (by
          have h := integrable_finsetSum (s := Finset.univ) (fun a _ => hint a)
          refine h.congr (ae_of_all _ fun x => ?_)
          simp only
          rw [Finset.sum_mul])
        ((hφ2.const_mul M).indicator hSm.compl) fun x => ?_
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_notMem (by simpa using hx)]
        have h0 : ∑ a : Fin eta × Fin 3, (dirD a C.χ x ^ 2 + dirD a C.η x ^ 2) = 0 :=
          Finset.sum_eq_zero fun a _ => by
            rw [(C.grad_zero x hx a).1, (C.grad_zero x hx a).2]
            ring
        rw [h0, zero_mul]
      · rw [Set.indicator_of_mem (by simpa using hx)]
        exact mul_le_mul_of_nonneg_right (C.grad_bound x) (by positivity)
    have hstep3 : ∫ x, Sᶜ.indicator (fun r => M * ‖φ r‖ ^ 2) x ≤ M * τ := by
      rw [integral_indicator hSm.compl, integral_const_mul]
      exact mul_le_mul_of_nonneg_left htail hM0
    linarith
  -- the outer part is bounded below by `E_∞`
  have hη_low := hlow (fun r => (C.η r : ℂ) * φ r) (contDiff_ofReal_mul hη hφ)
    (hasCompactSupport_ofReal_mul hcs) (isFreeSector_cut C.η_swap hsec)
    (integrable_pot_cut sys P hV hη.continuous hη1)
  have hφ_low := hlow φ hφ hcs hsec hV
  rw [hN, mul_one] at hφ_low
  have hε : 0 ≤ ε := by linarith
  have hims := freeEnergy_ims sys P hχ hη h1 hφ hcs hV
  refine ⟨contDiff_ofReal_mul hχ hφ, fun r hr => C.χ_supp r (fun h0 => hr (by
    beta_reduce
    rw [h0, Complex.ofReal_zero, zero_mul])), isFreeSector_cut C.χ_swap hsec, hNpos, ?_⟩
  set Nχ := ∫ r, ‖(C.χ r : ℂ) * φ r‖ ^ 2 with hNχ
  set Nη := ∫ r, ‖(C.η r : ℂ) * φ r‖ ^ 2 with hNη
  have key : freeEnergy sys P (fun r => (C.χ r : ℂ) * φ r) ≤ Einf * Nχ + (M * τ / 2 + ε) := by
    have hNη' : Nη = 1 - Nχ := by linarith
    rw [hNη'] at hη_low
    nlinarith [hims, hG, hen, hη_low]
  have hX : 0 ≤ M * τ / 2 + ε := by positivity
  have hfrac : M * τ / 2 + ε ≤ (M * τ / 2 + ε) / (1 - τ) * Nχ := by
    calc M * τ / 2 + ε = (M * τ / 2 + ε) / (1 - τ) * (1 - τ) := by field_simp
      _ ≤ (M * τ / 2 + ε) / (1 - τ) * Nχ :=
        mul_le_mul_of_nonneg_left hNχ_ge (div_nonneg hX hd.le)
  nlinarith [key, hfrac]

/-- **`prop:free`, upper bound, by IMS localisation.** If `E_∞` bounds the free-space form below
on the `C²` sector states of compact support, and for every `ε > 0` a normalised `C²` sector
state of compact support has energy `≤ E_∞ + ε` and mass `≤ τ < 1` outside the inner region `S`
of a localisation pair (Agmon decay: `τ ≤ C e^{-2α R}` for `S ⊇ B_R`), then
`E_L + C₀ ≤ E_∞ + Mτ/(2(1 - τ))`. -/
theorem free_upper_ims (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} {L R R0 ρ : ℝ}
    {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {E : ℝ} (hE : IsGLTorusGroundEnergy sys lab L θ E)
    {M : ℝ} {S : Set (Rcfg eta)} (hSm : MeasurableSet S) (C : LocPair eta L R0 ρ S M)
    {Einf τ : ℝ} (hτ : τ < 1)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (happrox : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧ ∫ r in Sᶜ, ‖φ r‖ ^ 2 ≤ τ) :
    E + (zeroModeShift sys L θ).re ≤ Einf + M * τ / (2 * (1 - τ)) := by
  apply free_upper_of_trial sys hL hθ hR hR0 hρ hone P hP hpos hE
  intro ε' hε'
  have hd : 0 < 1 - τ := by linarith
  obtain ⟨φ, hφ, hcs, hsec, hV, hN, hen, htail⟩ := happrox (ε' * (1 - τ)) (by positivity)
  obtain ⟨h2, hsupp, hsec', hpos', hbound⟩ :=
    retained_trial sys P hSm C hlow hφ hcs hsec hV hN hen htail hτ
  refine ⟨_, h2, hsupp, hsec', hpos', ?_⟩
  have e : Einf + (M * τ / 2 + ε' * (1 - τ)) / (1 - τ) = Einf + M * τ / (2 * (1 - τ)) + ε' := by
    field_simp
    ring
  rw [e] at hbound
  exact hbound

end System

end

end FreeBoundary
