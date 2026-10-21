import PlaneWave.FreeBoundary.CellObservable
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Free-space regularity, part 1: mollification

The tools for deriving the regularity of the initial state from two Hamiltonian relations
(`PlaneWave.FreeBoundary.KineticRegularity`–`PlaneWave.FreeBoundary.RegularityBridge`): the
mollification `(ρ ⋆ f)(x) = ∫ ρ(x - t) f(t) dt` of an `L²` function by a smooth compactly supported
kernel.

* `moll`, `moll_apply`, `contDiff_moll`, `dirD_moll`: the mollification is smooth and its
  derivatives are the mollifications by the derivatives of the kernel;
* `sq_le_of_forall_two_mul_le`, `sq_integral_weighted_le`, `sq_integral_mul_le`: Cauchy–Schwarz
  inequalities for integrals, from `2ab ≤ λa² + b²/λ`;
* `norm_moll_sq_le`, `memLp_moll`, `mollL2`, `norm_mollL2_le`: `‖ρ ⋆ f‖₂ ≤ ‖ρ‖₁ ‖f‖₂`;
* `rhoN`: the mollifiers of radius `1/(n+1)`, and **`tendsto_mollL2`**: `ρ_n ⋆ f → f` in `L²`;
* `moll_dirD_eq`, `moll_kin_eq`: weak derivatives and the weak kinetic relation commute with
  mollification.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology Convolution Pointwise
open Finset Set MeasureTheory Filter

namespace FreeBoundary

variable {eta : ℕ}

/-! ## Cauchy–Schwarz from `2ab ≤ λa² + b²/λ` -/

section CS

/-- `m² ≤ A B` if `2m ≤ λA + B/λ` for every `λ > 0`. -/
lemma sq_le_of_forall_two_mul_le {m A B : ℝ} (hm : 0 ≤ m) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ l : ℝ, 0 < l → 2 * m ≤ l * A + B / l) : m ^ 2 ≤ A * B := by
  rcases hm.eq_or_lt with hm0 | hmpos
  · rw [← hm0]
    nlinarith [mul_nonneg hA hB]
  rcases hA.eq_or_lt with hA0 | hApos
  · exfalso
    have h1 := h (B / m + 1) (by positivity)
    rw [← hA0, mul_zero, zero_add] at h1
    have h2 : B / (B / m + 1) < m := by
      rw [div_lt_iff₀ (by positivity)]
      have e : m * (B / m + 1) = B + m := by field_simp
      linarith
    linarith
  · have h1 := h (m / A) (div_pos hmpos hApos)
    have e1 : m / A * A = m := by field_simp
    have e2 : B / (m / A) = B * A / m := by field_simp
    rw [e1, e2] at h1
    have h3 : m ≤ B * A / m := by linarith
    rw [le_div_iff₀ hmpos] at h3
    nlinarith

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Weighted Cauchy–Schwarz**: `(∫ w a)² ≤ (∫ w)(∫ w a²)` for `w, a ≥ 0`. -/
lemma sq_integral_weighted_le {w a : X → ℝ} (hw : ∀ x, 0 ≤ w x) (ha : ∀ x, 0 ≤ a x)
    (hwi : Integrable w μ) (hwa : Integrable (fun x => w x * a x) μ)
    (hwa2 : Integrable (fun x => w x * a x ^ 2) μ) :
    (∫ x, w x * a x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * ∫ x, w x * a x ^ 2 ∂μ := by
  refine sq_le_of_forall_two_mul_le (integral_nonneg fun x => mul_nonneg (hw x) (ha x))
    (integral_nonneg hw) (integral_nonneg fun x => mul_nonneg (hw x) (sq_nonneg _))
    fun l hl => ?_
  have hpt : ∀ x, 2 * (w x * a x) ≤ l * w x + w x * a x ^ 2 / l := by
    intro x
    have h0 : 0 ≤ w x * (a x - l) ^ 2 / l := by
      have := hw x
      positivity
    have e : l * w x + w x * a x ^ 2 / l - 2 * (w x * a x) = w x * (a x - l) ^ 2 / l := by
      field_simp
      ring
    linarith
  calc 2 * ∫ x, w x * a x ∂μ = ∫ x, 2 * (w x * a x) ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ x, (l * w x + w x * a x ^ 2 / l) ∂μ :=
        integral_mono (hwa.const_mul 2) ((hwi.const_mul l).add (hwa2.div_const l)) hpt
    _ = l * ∫ x, w x ∂μ + (∫ x, w x * a x ^ 2 ∂μ) / l := by
        rw [integral_add (hwi.const_mul l) (hwa2.div_const l), integral_const_mul, integral_div]

/-- **Cauchy–Schwarz**: `(∫ p q)² ≤ (∫ p²)(∫ q²)` for `p, q ≥ 0`. -/
lemma sq_integral_mul_le {p q : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpq : Integrable (fun x => p x * q x) μ) (hp2 : Integrable (fun x => p x ^ 2) μ)
    (hq2 : Integrable (fun x => q x ^ 2) μ) :
    (∫ x, p x * q x ∂μ) ^ 2 ≤ (∫ x, p x ^ 2 ∂μ) * ∫ x, q x ^ 2 ∂μ := by
  refine sq_le_of_forall_two_mul_le (integral_nonneg fun x => mul_nonneg (hp x) (hq x))
    (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
    fun l hl => ?_
  have hpt : ∀ x, 2 * (p x * q x) ≤ l * p x ^ 2 + q x ^ 2 / l := by
    intro x
    have h0 : 0 ≤ (l * p x - q x) ^ 2 / l := by positivity
    have e : l * p x ^ 2 + q x ^ 2 / l - 2 * (p x * q x) = (l * p x - q x) ^ 2 / l := by
      field_simp
      ring
    linarith
  calc 2 * ∫ x, p x * q x ∂μ = ∫ x, 2 * (p x * q x) ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ x, (l * p x ^ 2 + q x ^ 2 / l) ∂μ :=
        integral_mono (hpq.const_mul 2) ((hp2.const_mul l).add (hq2.div_const l)) hpt
    _ = l * ∫ x, p x ^ 2 ∂μ + (∫ x, q x ^ 2 ∂μ) / l := by
        rw [integral_add (hp2.const_mul l) (hq2.div_const l), integral_const_mul, integral_div]

end CS

/-! ## The mollification -/

section Moll

/-- The bilinear map `(c, r) ↦ r c`. -/
noncomputable def mollL : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip

/-- The mollification `(ρ ⋆ f)(x) = ∫ ρ(x - t) f(t) dt`. -/
noncomputable def moll (ρ : Rcfg eta → ℝ) (f : Rcfg eta → ℂ) : Rcfg eta → ℂ :=
  f ⋆[mollL, volume] ρ

lemma moll_apply (ρ : Rcfg eta → ℝ) (f : Rcfg eta → ℂ) (x : Rcfg eta) :
    moll ρ f x = ∫ t, (ρ (x - t) : ℂ) * f t := by
  unfold moll
  rw [convolution_def]
  simp [mollL, Complex.real_smul]

lemma moll_eq_conv (ρ : Rcfg eta → ℝ) (f : Rcfg eta → ℂ) :
    moll ρ f = ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  unfold moll
  rw [← convolution_flip]
  simp [mollL]

lemma moll_congr_ae (ρ : Rcfg eta → ℝ) {f g : Rcfg eta → ℂ} (h : f =ᵐ[volume] g) :
    moll ρ f = moll ρ g := by
  funext x
  rw [moll_apply, moll_apply]
  refine integral_congr_ae ?_
  filter_upwards [h] with t ht
  rw [ht]

lemma locInt_L2 (f : FreeL2 eta) : LocallyIntegrable (f : Rcfg eta → ℂ) volume :=
  (Lp.memLp f).locallyIntegrable (by norm_num)

lemma hasCompactSupport_comp_sub {β : Type*} [Zero β] {ρ : Rcfg eta → β}
    (hρc : HasCompactSupport ρ) (x : Rcfg eta) : HasCompactSupport (fun t => ρ (x - t)) := by
  refine HasCompactSupport.intro (hρc.isCompact.image (continuous_const.sub continuous_id) :
    IsCompact ((fun s => x - s) '' tsupport ρ)) fun t ht => ?_
  by_contra h
  exact ht ⟨x - t, subset_tsupport ρ h, by simp⟩

lemma contDiff_moll {ρ : Rcfg eta → ℝ} (hρc : HasCompactSupport ρ) {n : ℕ∞}
    (hρ : ContDiff ℝ n ρ) {f : Rcfg eta → ℂ} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ n (moll ρ f) :=
  hρc.contDiff_convolution_right mollL hf hρ

lemma continuous_moll {ρ : Rcfg eta → ℝ} (hρc : HasCompactSupport ρ) (hρ : Continuous ρ)
    {f : Rcfg eta → ℂ} (hf : LocallyIntegrable f volume) : Continuous (moll ρ f) :=
  hρc.continuous_convolution_right mollL hf hρ

/-- **The derivative of a mollification**: `∂_a (ρ ⋆ f) = (∂_aρ) ⋆ f`. -/
lemma dirD_moll {ρ : Rcfg eta → ℝ} (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    {f : Rcfg eta → ℂ} (hf : LocallyIntegrable f volume) (a : Fin eta × Fin 3) :
    dirD a (moll ρ f) = moll (dirD a ρ) f := by
  funext x
  unfold dirD moll
  rw [(hρc.hasFDerivAt_convolution_right mollL hf hρ x).fderiv]
  exact convolution_precompR_apply mollL hf (hρc.fderiv ℝ) (hρ.continuous_fderiv one_ne_zero) x
    (Pi.single a 1)

end Moll

/-! ## `‖ρ ⋆ f‖₂ ≤ ‖ρ‖₁ ‖f‖₂` -/

section Young

lemma integrable_sq_L2 (f : FreeL2 eta) : Integrable (fun t => ‖f t‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

lemma norm_moll_sq_le {ρ : Rcfg eta → ℝ} (hρc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (f : FreeL2 eta) (x : Rcfg eta) :
    ‖moll ρ f x‖ ^ 2 ≤ (∫ t, |ρ t|) * ∫ t, |ρ (x - t)| * ‖f t‖ ^ 2 := by
  have hwc : Continuous fun t => |ρ (x - t)| :=
    (hρ.comp (continuous_const.sub continuous_id)).abs
  have hwcs : HasCompactSupport fun t => |ρ (x - t)| :=
    (hasCompactSupport_comp_sub hρc x).comp_left (g := fun s : ℝ => |s|) (by simp)
  have hwi : Integrable (fun t => |ρ (x - t)|) := hwc.integrable_of_hasCompactSupport hwcs
  obtain ⟨Cw, hCw⟩ := hwc.bounded_above_of_compact_support hwcs
  have hwa : Integrable (fun t => |ρ (x - t)| * ‖f t‖) :=
    (hwc.memLp_of_hasCompactSupport (p := 2) (μ := volume) hwcs).integrable_mul
      (Lp.memLp f).norm
  have hwa2 : Integrable (fun t => |ρ (x - t)| * ‖f t‖ ^ 2) :=
    (integrable_sq_L2 f).bdd_mul hwc.aestronglyMeasurable (ae_of_all _ fun t => hCw t)
  have hA : ∫ t, |ρ (x - t)| = ∫ t, |ρ t| := integral_sub_left_eq_self (fun s => |ρ s|) volume x
  have h1 : ‖moll ρ f x‖ ≤ ∫ t, |ρ (x - t)| * ‖f t‖ := by
    rw [moll_apply]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 := sq_integral_weighted_le (μ := volume) (fun t => abs_nonneg (ρ (x - t)))
    (fun t => norm_nonneg (f t)) hwi hwa hwa2
  rw [hA] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- **Young's inequality for `L¹ ⋆ L²`**: `ρ ⋆ f ∈ L²` with `‖ρ ⋆ f‖₂ ≤ ‖ρ‖₁ ‖f‖₂`. -/
lemma memLp_moll {ρ : Rcfg eta → ℝ} (hρc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (f : FreeL2 eta) :
    MemLp (moll ρ f) 2 volume ∧ ∫ x, ‖moll ρ f x‖ ^ 2 ≤ (∫ t, |ρ t|) ^ 2 * ‖f‖ ^ 2 := by
  have hf2 := integrable_sq_L2 f
  have hr : Integrable (fun t => |ρ t|) :=
    hρ.abs.integrable_of_hasCompactSupport (hρc.comp_left (g := fun s : ℝ => |s|) (by simp))
  set B : Rcfg eta → ℝ :=
    (fun t => ‖f t‖ ^ 2) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun t => |ρ t|) with hB
  have hBi : Integrable B := hf2.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hr
  have hBx : ∀ x, B x = ∫ t, |ρ (x - t)| * ‖f t‖ ^ 2 := by
    intro x
    rw [hB, convolution_def]
    congr 1
    funext t
    simp [mul_comm]
  have hBint : ∫ x, B x = ‖f‖ ^ 2 * ∫ t, |ρ t| := by
    rw [hB, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf2 hr, ← norm_sq_L2_eq f]
    simp
  have hcont : Continuous (moll ρ f) := continuous_moll hρc hρ (locInt_L2 f)
  have hpt : ∀ x, ‖moll ρ f x‖ ^ 2 ≤ (∫ t, |ρ t|) * B x := fun x => by
    rw [hBx]
    exact norm_moll_sq_le hρc hρ f x
  have hA0 : 0 ≤ ∫ t, |ρ t| := integral_nonneg fun t => abs_nonneg _
  have hint : Integrable (fun x => ‖moll ρ f x‖ ^ 2) :=
    (hBi.const_mul (∫ t, |ρ t|)).mono' (hcont.norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpt x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr hint, ?_⟩
  calc ∫ x, ‖moll ρ f x‖ ^ 2 ≤ ∫ x, (∫ t, |ρ t|) * B x :=
        integral_mono hint (hBi.const_mul _) hpt
    _ = (∫ t, |ρ t|) ^ 2 * ‖f‖ ^ 2 := by
        rw [integral_const_mul, hBint]
        ring

/-- The mollification as an element of `L²`. -/
noncomputable def mollL2 (ρ : Rcfg eta → ℝ) (hρc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (f : FreeL2 eta) : FreeL2 eta :=
  (memLp_moll hρc hρ f).1.toLp _

variable {ρ : Rcfg eta → ℝ} (hρc : HasCompactSupport ρ) (hρ : Continuous ρ)

lemma mollL2_ae (f : FreeL2 eta) :
    (mollL2 ρ hρc hρ f : Rcfg eta → ℂ) =ᵐ[volume] moll ρ f :=
  MemLp.coeFn_toLp _

lemma norm_sq_eq_of_ae {F : FreeL2 eta} {G : Rcfg eta → ℂ} (h : (F : Rcfg eta → ℂ) =ᵐ[volume] G) :
    ‖F‖ ^ 2 = ∫ x, ‖G x‖ ^ 2 := by
  rw [norm_sq_L2_eq F]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

lemma norm_mollL2_le (f : FreeL2 eta) : ‖mollL2 ρ hρc hρ f‖ ≤ (∫ t, |ρ t|) * ‖f‖ := by
  have hA0 : 0 ≤ ∫ t, |ρ t| := integral_nonneg fun t => abs_nonneg _
  have h1 : ‖mollL2 ρ hρc hρ f‖ ^ 2 ≤ ((∫ t, |ρ t|) * ‖f‖) ^ 2 := by
    rw [norm_sq_eq_of_ae (mollL2_ae hρc hρ f), mul_pow]
    exact (memLp_moll hρc hρ f).2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

include hρc hρ in
lemma moll_sub_ae (f g : FreeL2 eta) (x : Rcfg eta) :
    moll ρ (⇑(f - g)) x = moll ρ f x - moll ρ g x := by
  have hw : Integrable fun t => ((ρ (x - t) : ℝ) : ℂ) * f t :=
    integrable_cont_mul_L2 (Complex.continuous_ofReal.comp
      (hρ.comp (continuous_const.sub continuous_id)))
      ((hasCompactSupport_comp_sub hρc x).comp_left (g := fun s : ℝ => (s : ℂ)) (by simp)) f
  have hw' : Integrable fun t => ((ρ (x - t) : ℝ) : ℂ) * g t :=
    integrable_cont_mul_L2 (Complex.continuous_ofReal.comp
      (hρ.comp (continuous_const.sub continuous_id)))
      ((hasCompactSupport_comp_sub hρc x).comp_left (g := fun s : ℝ => (s : ℂ)) (by simp)) g
  rw [moll_congr_ae ρ (Lp.coeFn_sub f g), moll_apply, moll_apply, moll_apply,
    ← integral_sub hw hw']
  congr 1
  funext t
  simp only [Pi.sub_apply]
  ring

lemma mollL2_sub (f g : FreeL2 eta) :
    mollL2 ρ hρc hρ (f - g) = mollL2 ρ hρc hρ f - mollL2 ρ hρc hρ g := by
  apply Lp.ext
  filter_upwards [mollL2_ae hρc hρ (f - g), mollL2_ae hρc hρ f, mollL2_ae hρc hρ g,
    Lp.coeFn_sub (mollL2 ρ hρc hρ f) (mollL2 ρ hρc hρ g)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, h2, h3, moll_sub_ae hρc hρ f g x]

end Young

/-! ## The mollifiers `ρ_n` and the approximation of the identity -/

section Bump

/-- The bump of radii `1/(2(n+1))` and `1/(n+1)` at the origin. -/
noncomputable def bumpN (n : ℕ) : ContDiffBump (0 : Rcfg eta) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) h]
    linarith

/-- The mollifier `ρ_n`: smooth, nonnegative, of integral `1`, supported in the ball of radius
`1/(n+1)`. -/
noncomputable def rhoN (n : ℕ) : Rcfg eta → ℝ := (bumpN n).normed volume

lemma contDiff_rhoN (n : ℕ) {k : ℕ∞} : ContDiff ℝ k (rhoN (eta := eta) n) :=
  (bumpN n).contDiff_normed

lemma hasCompactSupport_rhoN (n : ℕ) : HasCompactSupport (rhoN (eta := eta) n) :=
  (bumpN n).hasCompactSupport_normed

lemma continuous_rhoN (n : ℕ) : Continuous (rhoN (eta := eta) n) := (bumpN n).continuous_normed

lemma rhoN_nonneg (n : ℕ) (x : Rcfg eta) : 0 ≤ rhoN n x := (bumpN n).nonneg_normed x

lemma integral_abs_rhoN (n : ℕ) : ∫ x, |rhoN (eta := eta) n x| = 1 := by
  simp_rw [abs_of_nonneg (rhoN_nonneg n _)]
  exact (bumpN n).integral_normed

/-- `f_n = ρ_n ⋆ f` as an element of `L²`. -/
noncomputable def mollN (n : ℕ) (f : FreeL2 eta) : FreeL2 eta :=
  mollL2 (rhoN n) (hasCompactSupport_rhoN n) (continuous_rhoN n) f

lemma mollN_ae (n : ℕ) (f : FreeL2 eta) :
    (mollN n f : Rcfg eta → ℂ) =ᵐ[volume] moll (rhoN n) f :=
  mollL2_ae _ _ f

lemma norm_mollN_le (n : ℕ) (f : FreeL2 eta) : ‖mollN n f‖ ≤ ‖f‖ := by
  have := norm_mollL2_le (hasCompactSupport_rhoN (eta := eta) n) (continuous_rhoN n) f
  rwa [integral_abs_rhoN, one_mul] at this

lemma mollN_sub (n : ℕ) (f g : FreeL2 eta) : mollN n (f - g) = mollN n f - mollN n g :=
  mollL2_sub _ _ f g

/-- A uniformly small function supported in a compact set is small in `L²`. -/
lemma norm_le_of_bound_supp {F : FreeL2 eta} {G : Rcfg eta → ℂ}
    (hFG : (F : Rcfg eta → ℂ) =ᵐ[volume] G) {K : Set (Rcfg eta)} (hK : IsCompact K) {η : ℝ}
    (hb : ∀ x, ‖G x‖ ≤ η) (hs : ∀ x, x ∉ K → G x = 0) :
    ‖F‖ ^ 2 ≤ η ^ 2 * volume.real K := by
  rw [norm_sq_eq_of_ae hFG]
  have hint : Integrable (K.indicator fun _ => η ^ 2) :=
    (integrableOn_const (C := η ^ 2) hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  calc ∫ x, ‖G x‖ ^ 2 ≤ ∫ x, K.indicator (fun _ => η ^ 2) x := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) hint
          (ae_of_all _ fun x => ?_)
        by_cases hx : x ∈ K
        · rw [Set.indicator_of_mem hx]
          exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
        · simp only [Set.indicator_of_notMem hx, hs x hx, norm_zero]
          norm_num
    _ = η ^ 2 * volume.real K := by
        rw [integral_indicator_const _ hK.measurableSet, smul_eq_mul, mul_comm]

/-- **The approximation of the identity**: `ρ_n ⋆ f → f` in `L²`. -/
theorem tendsto_mollN (f : FreeL2 eta) : Tendsto (fun n => mollN n f) atTop (𝓝 f) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ψ, hψc, hψs, hψ⟩ := (Lp.memLp f).exist_eLpNorm_sub_le (p := 2) (by norm_num)
    (by norm_num) (ε := ε / 4) (by positivity)
  have hψcont : Continuous ψ := hψs.continuous
  have hψL : MemLp ψ 2 volume := hψcont.memLp_of_hasCompactSupport hψc
  set Ψ : FreeL2 eta := hψL.toLp ψ with hΨdef
  have hΨ : (Ψ : Rcfg eta → ℂ) =ᵐ[volume] ψ := MemLp.coeFn_toLp hψL
  have hfΨ : ‖f - Ψ‖ ≤ ε / 4 := by
    rw [Lp.norm_def]
    have he : eLpNorm (⇑(f - Ψ)) 2 volume = eLpNorm (⇑f - ψ) 2 volume := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub f Ψ, hΨ] with x h1 h2
      rw [h1, Pi.sub_apply, Pi.sub_apply, h2]
    rw [he]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hψ
  -- the compact set containing all the supports
  set K : Set (Rcfg eta) := tsupport ψ + Metric.closedBall (0 : Rcfg eta) 1 with hKdef
  have hK : IsCompact K := hψc.isCompact.add (isCompact_closedBall (0 : Rcfg eta) 1)
  have hsub : tsupport ψ ⊆ K := fun y hy => by
    have := Set.add_mem_add hy (Metric.mem_closedBall_self (x := (0 : Rcfg eta)) zero_le_one)
    simpa using this
  set V : ℝ := volume.real K with hVdef
  have hV : 0 ≤ V := measureReal_nonneg
  set η : ℝ := ε / (4 * (Real.sqrt V + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hψδ⟩ := Metric.uniformContinuous_iff.mp
    (hψc.uniformContinuous_of_continuous hψcont) η hη
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hδ one_pos)
  refine ⟨N, fun n hn => ?_⟩
  have hr : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hn 1
  have hrδ : 1 / ((n : ℝ) + 1) < δ := lt_of_le_of_lt hr (lt_of_lt_of_le hN (min_le_left _ _))
  have hr1 : 1 / ((n : ℝ) + 1) < 1 := lt_of_le_of_lt hr (lt_of_lt_of_le hN (min_le_right _ _))
  -- `ρ_n ⋆ ψ - ψ` is uniformly small and supported in `K`
  have hpt : ∀ x, ‖moll (rhoN n) ψ x - ψ x‖ ≤ η := by
    intro x
    rw [← dist_eq_norm, moll_eq_conv]
    exact (bumpN n).dist_normed_convolution_le hψcont.aestronglyMeasurable fun y hy =>
      (hψδ (lt_trans (Metric.mem_ball.mp hy) hrδ)).le
  have hzero : ∀ x, x ∉ K → moll (rhoN n) ψ x - ψ x = 0 := by
    intro x hx
    have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hsub h)
    rw [hψx, sub_zero, moll_apply]
    refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
    by_cases hρ : rhoN n (x - t) = 0
    · simp [hρ]
    · have hb : x - t ∈ Metric.ball (0 : Rcfg eta) (1 / ((n : ℝ) + 1)) := by
        have := (bumpN (eta := eta) n).support_normed_eq (μ := volume) ▸
          (Function.mem_support.mpr hρ)
        exact this
      by_cases hψt : ψ t = 0
      · simp [hψt]
      · exfalso
        apply hx
        have h1 : t ∈ tsupport ψ := subset_tsupport ψ hψt
        have h2 : x - t ∈ Metric.closedBall (0 : Rcfg eta) 1 :=
          Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hb).le.trans hr1.le)
        have := Set.add_mem_add h1 h2
        simpa using this
  have hdiff : (⇑(mollN n Ψ - Ψ) : Rcfg eta → ℂ) =ᵐ[volume] fun x => moll (rhoN n) ψ x - ψ x := by
    filter_upwards [Lp.coeFn_sub (mollN n Ψ) Ψ, mollN_ae n Ψ, hΨ] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, moll_congr_ae (rhoN n) hΨ]
  have hsmall : ‖mollN n Ψ - Ψ‖ ≤ ε / 4 := by
    have h1 := norm_le_of_bound_supp hdiff hK hpt hzero
    have h2 : η ^ 2 * V ≤ (ε / 4) ^ 2 := by
      have hs : V ≤ (Real.sqrt V + 1) ^ 2 := by
        have := Real.sq_sqrt hV
        nlinarith [Real.sqrt_nonneg V]
      rw [hηdef, div_pow, mul_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : (ε / 4) ^ 2 * (4 ^ 2 * (Real.sqrt V + 1) ^ 2) = ε ^ 2 * (Real.sqrt V + 1) ^ 2 := by
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hs (sq_nonneg ε)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h1.trans h2)
  have hfn : ‖mollN n (f - Ψ)‖ ≤ ε / 4 := (norm_mollN_le n _).trans hfΨ
  rw [dist_eq_norm]
  have e : mollN n f - f = mollN n (f - Ψ) + (mollN n Ψ - Ψ) + (Ψ - f) := by
    rw [mollN_sub]
    abel
  rw [e]
  have h3 : ‖Ψ - f‖ ≤ ε / 4 := by rw [norm_sub_rev]; exact hfΨ
  calc ‖mollN n (f - Ψ) + (mollN n Ψ - Ψ) + (Ψ - f)‖
      ≤ ‖mollN n (f - Ψ)‖ + ‖mollN n Ψ - Ψ‖ + ‖Ψ - f‖ := norm_add₃_le
    _ ≤ ε / 4 + ε / 4 + ε / 4 := by gcongr
    _ < ε := by linarith

end Bump

/-! ## Weak derivatives commute with mollification -/

section Commute

lemma dirD_comp_sub {G : Rcfg eta → ℝ} (hG : Differentiable ℝ G) (x : Rcfg eta)
    (a : Fin eta × Fin 3) : dirD a (fun t => G (x - t)) = fun t => -dirD a G (x - t) := by
  funext t
  have h1 : HasFDerivAt (fun t : Rcfg eta => x - t) (-ContinuousLinearMap.id ℝ (Rcfg eta)) t :=
    (hasFDerivAt_id t).const_sub x
  have h2 : HasFDerivAt (fun t => G (x - t))
      ((fderiv ℝ G (x - t)).comp (-ContinuousLinearMap.id ℝ (Rcfg eta))) t :=
    (hG (x - t)).hasFDerivAt.comp t h1
  unfold dirD
  rw [h2.fderiv]
  simp

lemma dirD_ofReal_fun {F : Rcfg eta → ℝ} (hF : Differentiable ℝ F) (a : Fin eta × Fin 3) :
    dirD a (fun t => ((F t : ℝ) : ℂ)) = fun t => ((dirD a F t : ℝ) : ℂ) := by
  funext t
  have h : HasFDerivAt (fun t => ((F t : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ F t)) t :=
    Complex.ofRealCLM.hasFDerivAt.comp t (hF t).hasFDerivAt
  unfold dirD
  rw [h.fderiv]
  simp

lemma dirD_neg_fun' {F : Rcfg eta → ℝ} (a : Fin eta × Fin 3) :
    dirD a (fun t => -F t) = fun t => -dirD a F t := by
  funext t
  unfold dirD
  rw [fderiv_fun_neg]
  simp

/-- The test function `t ↦ ρ(x - t)` is a `C^k` function of compact support. -/
lemma contDiff_testSub {ρ : Rcfg eta → ℝ} {k : ℕ} (hρ : ContDiff ℝ k ρ) (x : Rcfg eta) :
    ContDiff ℝ k (fun t => ((ρ (x - t) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hρ.comp (contDiff_const.sub contDiff_id))

lemma hasCompactSupport_testSub {ρ : Rcfg eta → ℝ} (hρc : HasCompactSupport ρ) (x : Rcfg eta) :
    HasCompactSupport (fun t => ((ρ (x - t) : ℝ) : ℂ)) :=
  (hasCompactSupport_comp_sub hρc x).comp_left (g := fun s : ℝ => (s : ℂ)) (by simp)

lemma dirD_testSub {ρ : Rcfg eta → ℝ} (hρ : ContDiff ℝ 1 ρ) (x : Rcfg eta)
    (a : Fin eta × Fin 3) :
    dirD a (fun t => ((ρ (x - t) : ℝ) : ℂ)) = fun t => -((dirD a ρ (x - t) : ℝ) : ℂ) := by
  have hd : Differentiable ℝ (fun t => ρ (x - t)) :=
    (hρ.comp (contDiff_const.sub contDiff_id)).differentiable (by norm_num)
  rw [dirD_ofReal_fun hd, dirD_comp_sub (hρ.differentiable (by norm_num)) x a]
  funext t
  push_cast
  ring

lemma dirD2_testSub {ρ : Rcfg eta → ℝ} (hρ : ContDiff ℝ 2 ρ) (x : Rcfg eta)
    (a : Fin eta × Fin 3) :
    dirD a (dirD a (fun t => ((ρ (x - t) : ℝ) : ℂ))) =
      fun t => ((dirD a (dirD a ρ) (x - t) : ℝ) : ℂ) := by
  rw [dirD_testSub (hρ.of_le (by norm_num)) x a]
  have hd1 : ContDiff ℝ 1 (dirD a ρ) := contDiff_dirD hρ a
  have hd : Differentiable ℝ (fun t => -dirD a ρ (x - t)) :=
    ((hd1.comp (contDiff_const.sub contDiff_id)).neg).differentiable (by norm_num)
  have e : (fun t => -((dirD a ρ (x - t) : ℝ) : ℂ)) =
      fun t => (((fun s => -dirD a ρ (x - s)) t : ℝ) : ℂ) := by
    funext t
    push_cast
    ring
  rw [e, dirD_ofReal_fun hd, dirD_neg_fun', dirD_comp_sub (hd1.differentiable (by norm_num)) x a]
  funext t
  push_cast
  ring

/-- **Weak derivatives commute with mollification**: `(∂_aρ) ⋆ f = ρ ⋆ ∂_a f`. -/
lemma moll_dirD_eq {f : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad f g)
    {ρ : Rcfg eta → ℝ} (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (a : Fin eta × Fin 3)
    (x : Rcfg eta) : moll (dirD a ρ) f x = moll ρ (g a) x := by
  have h := hg _ (contDiff_testSub hρ x) (hasCompactSupport_testSub hρc x) a
  rw [dirD_testSub hρ x a] at h
  simp only [Complex.conj_ofReal, map_neg, neg_mul, integral_neg, neg_neg] at h
  rw [moll_apply, moll_apply]
  exact h.symm

/-- The real kinetic expression `-(1/2) Σ_a m_a⁻¹ ∂_a²ρ`. -/
noncomputable def kinR (m : Fin eta → ℝ) (ρ : Rcfg eta → ℝ) (y : Rcfg eta) : ℝ :=
  -(1 / 2) * ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * dirD a (dirD a ρ) y

/-- **The weak kinetic relation commutes with mollification**: `(Kρ) ⋆ f = ρ ⋆ z` if `Kf = z`. -/
lemma moll_kin_eq {m : Fin eta → ℝ} {f z : FreeL2 eta} (hK : HasFreeWeakKinetic m f z)
    {ρ : Rcfg eta → ℝ} (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (x : Rcfg eta) :
    moll (kinR m ρ) f x = moll ρ z x := by
  have h := hK _ (contDiff_testSub hρ x) (hasCompactSupport_testSub hρc x)
  have hk : ∀ r, freeKinetic m (fun t => ((ρ (x - t) : ℝ) : ℂ)) r =
      ((kinR m ρ (x - r) : ℝ) : ℂ) := by
    intro r
    rw [freeKinetic_eq m (contDiff_testSub hρ x) r]
    simp_rw [dirD2_testSub hρ x]
    unfold kinR
    push_cast
    ring
  simp_rw [hk, Complex.conj_ofReal] at h
  rw [moll_apply, moll_apply]
  exact h.symm

lemma integrable_kernel_mul {ρ : Rcfg eta → ℝ} (hρc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (f : FreeL2 eta) (x : Rcfg eta) : Integrable fun t => ((ρ (x - t) : ℝ) : ℂ) * f t :=
  integrable_cont_mul_L2 (Complex.continuous_ofReal.comp
    (hρ.comp (continuous_const.sub continuous_id))) (hasCompactSupport_testSub hρc x) f

/-- The kinetic expression of a mollification: `K(ρ ⋆ f) = (Kρ) ⋆ f`. -/
lemma freeKinetic_moll (m : Fin eta → ℝ) {ρ : Rcfg eta → ℝ} (hρc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 3 ρ) (f : FreeL2 eta) (x : Rcfg eta) :
    freeKinetic m (moll ρ f) x = moll (kinR m ρ) f x := by
  have hf := locInt_L2 f
  have hρ2 : ContDiff ℝ 2 ρ := hρ.of_le (by norm_num)
  rw [freeKinetic_eq m (contDiff_moll hρc hρ2 hf) x]
  have hd : ∀ a : Fin eta × Fin 3, dirD a (dirD a (moll ρ f)) = moll (dirD a (dirD a ρ)) f := by
    intro a
    rw [dirD_moll hρc (hρ.of_le (by norm_num)) hf a,
      dirD_moll ((hasCompactSupport_dirD hρc a)) (contDiff_dirD hρ2 a) hf a]
  simp_rw [hd]
  have hint : ∀ a : Fin eta × Fin 3, Integrable fun t =>
      (((dirD a (dirD a ρ) (x - t)) : ℝ) : ℂ) * f t := fun a =>
    integrable_kernel_mul (hasCompactSupport_dirD (hasCompactSupport_dirD hρc a) a)
      (continuous_dirD (contDiff_dirD hρ2 a) (by norm_num) a) f x
  rw [moll_apply]
  simp_rw [moll_apply]
  unfold kinR
  have e : (fun t => ((((-(1 / 2) * ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ *
      dirD a (dirD a ρ) (x - t)) : ℝ) : ℂ) * f t)) = fun t => (-(1 / 2 : ℂ)) *
      ∑ a : Fin eta × Fin 3, ((m a.1 : ℂ))⁻¹ * ((((dirD a (dirD a ρ) (x - t)) : ℝ) : ℂ) * f t) := by
    funext t
    push_cast
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e, integral_const_mul, integral_finsetSum _ fun a _ => (hint a).const_mul _]
  simp_rw [integral_const_mul]

end Commute

end FreeBoundary
