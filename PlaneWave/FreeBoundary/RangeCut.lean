import PlaneWave.FreeBoundary.Scaling
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# `app:free`, part 2: the Fourier coefficients of the range-truncated kernel (eq:rangecut)

The range-truncated kernel is `g(x) = θ(|x|)/|x|` on `ℝ³`, for a radial profile `θ` that is
continuously differentiable, equals `1` at `0`, satisfies `|θ| ≤ 1` and vanishes on `[R, ∞)`
(`Profile R θ`; in the manuscript `R = L/2`, and `θ ≡ 1` on `[0, L/2 - ρ]`). Since its support
lies in the ball of radius `L/2`, its Fourier coefficients on the cell `T_L` are
`ĝ_L(ν) = Ω⁻¹ ĝ(k_ν)`, `ĝ(k) = ∫_{ℝ³} g(x) e^{-i k·x} dx`, `Ω = L³`, `k_ν = 2πν/L`.

* `gFT_eq_sin` (the radial Fourier integral): for `k ≠ 0`,
  `ĝ(k) = (4π/|k|) ∫_0^R θ(r) sin(|k| r) dr`; by rotation invariance (`gFT_rot`), the slice
  decomposition `x = (a, y)` (`gFT_slice`), the planar radial integral and the substitution
  `s = (a² + |y|²)^{1/2}` (`slice_eq`), and Fubini on `{|a| < s}` (`outer_eq`);
* `norm_gFT_le` (one integration by parts): `|ĝ(k)| ≤ 4π (1 + V_θ)/|k|²`, `V_θ = ∫_0^R |θ'|`;
* `gFT_zero`, `norm_gFT_zero_le`: `ĝ(0) = 4π ∫_0^R r θ(r) dr`, `|ĝ(0)| ≤ 2π R²`;
* **`rangecut`** (eq:rangecut): `|ĝ_L(ν)| ≤ (1 + V_θ) ŵ(ν)` for `ν ≠ 0`, `ŵ(ν) = 4π/(Ω |k_ν|²)`;
  `ghat_zero_le`: `|ĝ_L(0)| ≤ π/(2L)` for `R = L/2`;
* `scaling_low_gL` … `scaling_moment4_gL`: `lem:scaling` for the actual `g_L`, `C_ρ = 1 + V_θ`.

The constant `1 + V_θ` does not depend on `L`: for a fixed transition shape
`θ(r) = θ₀((r - R + ρ)/ρ)`, `V_θ = V_{θ₀}`, and `V_θ = 1` for a monotone profile.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Real PlaneWaveCertificate
open scoped InnerProductSpace

namespace FreeBoundary

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A radial cutoff profile on `[0, R]`. -/
structure Profile (R : ℝ) (θ : ℝ → ℝ) : Prop where
  pos : 0 < R
  diff : ContDiff ℝ 1 θ
  zero : θ 0 = 1
  bound : ∀ r, |θ r| ≤ 1
  vanish : ∀ r, R ≤ r → θ r = 0

/-- The range-truncated kernel `g(x) = θ(|x|)/|x|` on `ℝ³`. -/
noncomputable def gker (θ : ℝ → ℝ) (x : E3) : ℝ := θ ‖x‖ / ‖x‖

/-- Its Fourier transform `ĝ(k) = ∫ g(x) e^{-i k·x} dx`. -/
noncomputable def gFT (θ : ℝ → ℝ) (k : E3) : ℂ :=
  ∫ x : E3, (gker θ x : ℂ) * Complex.exp (-(Complex.I * (⟪k, x⟫_ℝ : ℂ)))

/-- The total variation `V_θ = ∫_0^R |θ'|`. -/
noncomputable def tv (R : ℝ) (θ : ℝ → ℝ) : ℝ := ∫ r in (0 : ℝ)..R, |deriv θ r|

variable {R : ℝ} {θ : ℝ → ℝ}

namespace Profile

variable (hθ : Profile R θ)
include hθ

lemma cont : Continuous θ := hθ.diff.continuous

lemma tv_nonneg : 0 ≤ tv R θ :=
  intervalIntegral.integral_nonneg hθ.pos.le fun _ _ => abs_nonneg _

/-- `r θ(r)` is integrable on `(0, ∞)`. -/
lemma integrableOn_mul : IntegrableOn (fun r : ℝ => r * θ r) (Ioi 0) := by
  have h1 : IntegrableOn (fun r : ℝ => r * θ r) (Icc 0 R) :=
    (continuous_id.mul hθ.cont).integrableOn_Icc
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun r hr => ?_
  have hr' : R < r := by
    rcases hr with ⟨h0, h1⟩
    simp only [mem_Icc, not_and, not_le] at h1
    exact h1 (le_of_lt h0)
  rw [hθ.vanish r hr'.le, mul_zero]

/-- `θ` is integrable on `[c, ∞)`. -/
lemma integrableOn_Ici (c : ℝ) : IntegrableOn θ (Ici c) := by
  have h1 : IntegrableOn θ (Icc c R) := hθ.cont.integrableOn_Icc
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ici fun r hr => ?_
  have hr' : R < r := by
    rcases hr with ⟨h0, h1⟩
    simp only [mem_Icc, not_and, not_le] at h1
    exact h1 h0
  exact hθ.vanish r hr'.le

/-- The kernel is integrable on `ℝ³`. -/
lemma integrable_gker : Integrable (gker θ) := by
  have h := (integrable_fun_norm_addHaar (volume : Measure E3) (f := fun r : ℝ => θ r / r)).mpr
  refine h ?_
  rw [finrank_euclideanSpace_fin]
  refine hθ.integrableOn_mul.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr0 : r ≠ 0 := (mem_Ioi.mp hr).ne'
  simp only [smul_eq_mul]
  field_simp
  ring

lemma integrable_gFT (k : E3) :
    Integrable fun x : E3 => (gker θ x : ℂ) * Complex.exp (-(Complex.I * (⟪k, x⟫_ℝ : ℂ))) := by
  refine (hθ.integrable_gker.ofReal (𝕜 := ℂ)).mul_bdd (c := 1) ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · refine (Continuous.aestronglyMeasurable ?_)
    fun_prop
  · rw [Complex.norm_exp]
    simp

end Profile

/-! ## The zero mode -/

/-- `ĝ(0) = 4π ∫_0^R r θ(r) dr`. -/
lemma gFT_zero (hθ : Profile R θ) :
    gFT θ 0 = ((4 * π * ∫ r in (0 : ℝ)..R, r * θ r : ℝ) : ℂ) := by
  have h0 : gFT θ 0 = ((∫ x : E3, gker θ x : ℝ) : ℂ) := by
    unfold gFT
    simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
      mul_one]
    exact integral_ofReal
  rw [h0]
  congr 1
  have h := integral_fun_norm_addHaar (volume : Measure E3) (fun r : ℝ => θ r / r)
  simp only [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul] at h
  change ∫ x : E3, θ ‖x‖ / ‖x‖ = _
  rw [h]
  have hball : (volume : Measure E3).real (Metric.ball 0 1) = 4 / 3 * π := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hball]
  have hI : ∫ y in Ioi (0 : ℝ), y ^ (3 - 1) * (θ y / y) = ∫ r in (0 : ℝ)..R, r * θ r := by
    rw [intervalIntegral.integral_of_le hθ.pos.le]
    have e : ∫ y in Ioi (0 : ℝ), y ^ (3 - 1) * (θ y / y) = ∫ y in Ioi (0 : ℝ), y * θ y := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      have hy0 : y ≠ 0 := (mem_Ioi.mp hy).ne'
      field_simp
      ring
    rw [e]
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun y hy => ?_)
    have hy' : R < y := by
      rcases hy with ⟨h0, h1⟩
      simp only [mem_Ioc, not_and, not_le] at h1
      exact h1 h0
    rw [hθ.vanish y hy'.le, mul_zero]
  rw [hI]
  push_cast
  ring

/-- `|ĝ(0)| ≤ 2π R²`. -/
lemma norm_gFT_zero_le (hθ : Profile R θ) : ‖gFT θ 0‖ ≤ 2 * π * R ^ 2 := by
  rw [gFT_zero hθ, Complex.norm_real, Real.norm_eq_abs]
  have hR := hθ.pos
  have hb : |∫ r in (0 : ℝ)..R, r * θ r| ≤ R ^ 2 / 2 := by
    calc |∫ r in (0 : ℝ)..R, r * θ r| ≤ ∫ r in (0 : ℝ)..R, |r * θ r| :=
          intervalIntegral.abs_integral_le_integral_abs hR.le
      _ ≤ ∫ r in (0 : ℝ)..R, r := by
          refine intervalIntegral.integral_mono_on hR.le ?_ (continuous_id.intervalIntegrable _ _)
            fun r hr => ?_
          · exact ((continuous_id.mul hθ.cont).abs).intervalIntegrable _ _
          · rw [abs_mul, abs_of_nonneg hr.1]
            exact mul_le_of_le_one_right hr.1 (hθ.bound r)
      _ = R ^ 2 / 2 := by rw [integral_id]; ring
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]
  nlinarith [Real.pi_pos]

/-! ## Rotation invariance -/

/-- The unit vector `e₀`. -/
noncomputable def e0 : E3 := EuclideanSpace.single 0 1

lemma norm_e0 : ‖e0‖ = 1 := by
  unfold e0; rw [PiLp.norm_single, norm_one]

/-- `ĝ` is radial: `ĝ(k) = ĝ(|k| e₀)`. -/
lemma gFT_rot (k : E3) : gFT θ k = gFT θ (‖k‖ • e0) := by
  obtain ⟨v, hv⟩ : ∃ v : E3, v = ‖k‖ • e0 := ⟨_, rfl⟩
  rw [← hv]
  have hnorm : ‖v‖ = ‖k‖ := by rw [hv, norm_smul, norm_e0, mul_one, norm_norm]
  obtain ⟨Q, hQ⟩ : ∃ Q : E3 ≃ₗᵢ[ℝ] E3, Q = Submodule.reflection (ℝ ∙ (v - k))ᗮ := ⟨_, rfl⟩
  have hQv : Q v = k := by rw [hQ]; exact Submodule.reflection_sub hnorm
  have hQk : Q k = v := by rw [← hQv, hQ, Submodule.reflection_reflection]
  have h := (LinearIsometryEquiv.measurePreserving Q).integral_comp
    Q.toHomeomorph.measurableEmbedding
    (fun x : E3 => (gker θ x : ℂ) * Complex.exp (-(Complex.I * (⟪v, x⟫_ℝ : ℂ))))
  unfold gFT
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h1 : gker θ (Q x) = gker θ x := by unfold gker; rw [Q.norm_map]
  have h2 : ⟪v, Q x⟫_ℝ = ⟪k, x⟫_ℝ := by
    rw [← hQk, LinearIsometryEquiv.inner_map_map]
  simp only [h1, h2]

/-! ## Slices -/

/-- The slice integral `S(a) = ∫_{ℝ²} g(a, y) dy`. -/
noncomputable def sl (θ : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ z : Fin 2 → ℝ, gker θ (WithLp.toLp 2 (Fin.cons a z : Fin 3 → ℝ))

lemma norm_toLp_cons (a : ℝ) (z : Fin 2 → ℝ) :
    ‖(WithLp.toLp 2 (Fin.cons a z : Fin 3 → ℝ) : E3)‖ =
      Real.sqrt (a ^ 2 + ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 2))‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 (Fin.cons a z : Fin 3 → ℝ) : E3))]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp

lemma inner_e0 (κ : ℝ) (y : Fin 3 → ℝ) : ⟪κ • e0, (WithLp.toLp 2 y : E3)⟫_ℝ = κ * y 0 := by
  rw [real_inner_smul_left, e0, EuclideanSpace.inner_single_left]
  simp

/-- The slice decomposition: `ĝ(κ e₀) = ∫ e^{-iκa} S(a) da`. -/
lemma gFT_slice (hθ : Profile R θ) (κ : ℝ) :
    gFT θ (κ • e0) = ∫ a : ℝ, Complex.exp (-(Complex.I * ((κ * a : ℝ) : ℂ))) * ((sl θ a : ℝ) : ℂ) := by
  obtain ⟨F, hF⟩ : ∃ F : E3 → ℂ,
      F = fun x => (gker θ x : ℂ) * Complex.exp (-(Complex.I * (⟪κ • e0, x⟫_ℝ : ℂ))) := ⟨_, rfl⟩
  have hFi : Integrable F := by rw [hF]; exact hθ.integrable_gFT _
  have hg : gFT θ (κ • e0) = ∫ x, F x := by rw [hF]; rfl
  have h1 : ∫ x : E3, F x = ∫ y : Fin 3 → ℝ, F (WithLp.toLp 2 y) :=
    ((PiLp.volume_preserving_toLp (Fin 3)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding F).symm
  have hFi1 : Integrable (fun y : Fin 3 → ℝ => F (WithLp.toLp 2 y)) :=
    ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding).mpr hFi
  obtain ⟨e, he⟩ : ∃ e, e = MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0 := ⟨_, rfl⟩
  have hmp : MeasurePreserving e.symm := by
    rw [he]; exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm _
  have h2 : ∫ y : Fin 3 → ℝ, F (WithLp.toLp 2 y) =
      ∫ p : ℝ × (Fin 2 → ℝ), F (WithLp.toLp 2 (e.symm p)) :=
    (hmp.integral_comp' (fun y => F (WithLp.toLp 2 y))).symm
  have hFi2 : Integrable (fun p : ℝ × (Fin 2 → ℝ) => F (WithLp.toLp 2 (e.symm p))) :=
    (hmp.integrable_comp_emb e.symm.measurableEmbedding).mpr hFi1
  have h3 : ∫ p : ℝ × (Fin 2 → ℝ), F (WithLp.toLp 2 (e.symm p)) =
      ∫ a : ℝ, ∫ z : Fin 2 → ℝ, F (WithLp.toLp 2 (e.symm (a, z))) :=
    integral_prod _ hFi2
  have hes : ∀ (a : ℝ) (z : Fin 2 → ℝ), e.symm (a, z) = (Fin.cons a z : Fin 3 → ℝ) := by
    intro a z
    rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
    exact Fin.insertNth_zero' a z
  have h4 : ∀ a : ℝ, ∫ z : Fin 2 → ℝ, F (WithLp.toLp 2 (e.symm (a, z))) =
      Complex.exp (-(Complex.I * ((κ * a : ℝ) : ℂ))) * ((sl θ a : ℝ) : ℂ) := by
    intro a
    have e1 : ∀ z : Fin 2 → ℝ, F (WithLp.toLp 2 (e.symm (a, z))) =
        (gker θ (WithLp.toLp 2 (Fin.cons a z : Fin 3 → ℝ)) : ℂ) *
          Complex.exp (-(Complex.I * ((κ * a : ℝ) : ℂ))) := by
      intro z
      rw [hes, hF]
      simp only [inner_e0, Fin.cons_zero]
    simp_rw [e1]
    rw [integral_mul_const, integral_complex_ofReal, mul_comm]
    rfl
  rw [hg, h1, h2, h3]
  exact integral_congr_ae (Filter.Eventually.of_forall h4)

/-! ## The slice integral -/

/-- The planar radial integral `∫_{ℝ²} h(|y|) dy = 2π ∫_0^∞ r h(r) dr`. -/
lemma planar_radial (h : ℝ → ℝ) :
    ∫ z : Fin 2 → ℝ, h ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 2))‖ =
      2 * π * ∫ r in Ioi (0 : ℝ), r * h r := by
  have h1 := (PiLp.volume_preserving_toLp (Fin 2)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding
    (fun w : EuclideanSpace ℝ (Fin 2) => h ‖w‖)
  rw [h1, integral_fun_norm_addHaar volume h]
  simp only [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  have hball : (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) = π := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_two]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    exact ENNReal.toReal_ofReal Real.pi_pos.le
  rw [hball]
  norm_num
  ring

/-- The substitution `s = (a² + r²)^{1/2}`: `∫_0^∞ r θ(s(r))/s(r) dr = ∫_{|a|}^∞ θ`. -/
lemma radial_subst (hθ : Profile R θ) (a : ℝ) :
    ∫ r in Ioi (0 : ℝ), r * (θ (Real.sqrt (a ^ 2 + r ^ 2)) / Real.sqrt (a ^ 2 + r ^ 2)) =
      ∫ s in Ioi |a|, θ s := by
  have hcont : Continuous fun r : ℝ => Real.sqrt (a ^ 2 + r ^ 2) := by fun_prop
  have hge : ∀ r : ℝ, |r| ≤ Real.sqrt (a ^ 2 + r ^ 2) := fun r =>
    Real.abs_le_sqrt (by nlinarith [sq_nonneg a])
  have hmeas : Measurable fun x : ℝ => (θ ∘ fun r => Real.sqrt (a ^ 2 + r ^ 2)) x *
      (x / Real.sqrt (a ^ 2 + x ^ 2)) :=
    ((hθ.cont.comp hcont).measurable).mul (measurable_id.div hcont.measurable)
  have key := integral_comp_mul_deriv_Ioi (f := fun r => Real.sqrt (a ^ 2 + r ^ 2))
    (f' := fun r => r / Real.sqrt (a ^ 2 + r ^ 2)) (g := θ) (a := 0)
    hcont.continuousOn
    (tendsto_atTop_mono (fun r => (le_abs_self r).trans (hge r)) tendsto_id)
    (fun x hx => by
      have hx0 : (0 : ℝ) < x := hx
      have hpos : a ^ 2 + x ^ 2 ≠ 0 := by positivity
      have hd := (((hasDerivAt_id' x).pow 2).const_add (a ^ 2)).sqrt hpos
      have hs : Real.sqrt (a ^ 2 + x ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      refine (hd.congr_deriv ?_).hasDerivWithinAt
      simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_one, Pi.pow_apply]
      field_simp)
    hθ.cont.continuousOn
    ((hθ.integrableOn_Ici 0).mono_set fun s ⟨r, _, hr⟩ => by
      rw [← hr]; exact Real.sqrt_nonneg _)
    (by
      have hI : IntegrableOn (fun x : ℝ => (θ ∘ fun r => Real.sqrt (a ^ 2 + r ^ 2)) x *
          (x / Real.sqrt (a ^ 2 + x ^ 2))) (Icc 0 R) := by
        refine Integrable.of_bound hmeas.aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun x => ?_)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_nonneg
          (Real.sqrt_nonneg _)]
        have h1 := hθ.bound (Real.sqrt (a ^ 2 + x ^ 2))
        have h2 : |x| / Real.sqrt (a ^ 2 + x ^ 2) ≤ 1 := div_le_one_of_le₀ (hge x)
          (Real.sqrt_nonneg _)
        have h3 : 0 ≤ |x| / Real.sqrt (a ^ 2 + x ^ 2) := by positivity
        calc |(θ ∘ fun r => Real.sqrt (a ^ 2 + r ^ 2)) x| * (|x| / Real.sqrt (a ^ 2 + x ^ 2))
            ≤ 1 * 1 := mul_le_mul h1 h2 h3 zero_le_one
          _ = 1 := one_mul 1
      refine hI.of_forall_sdiff_eq_zero measurableSet_Ici fun x hx => ?_
      rcases hx with ⟨h0, h1⟩
      have hx' : R < x := by
        simp only [mem_Icc, not_and, not_le] at h1
        exact h1 h0
      have hR : R ≤ Real.sqrt (a ^ 2 + x ^ 2) := by
        have := hge x
        rw [abs_of_nonneg (mem_Ici.mp h0)] at this
        linarith
      simp only [Function.comp, hθ.vanish _ hR, zero_mul])
  have hf0 : Real.sqrt (a ^ 2 + 0 ^ 2) = |a| := by
    rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs]
  rw [hf0] at key
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp only [Function.comp]
  ring

/-- `S(a) = 2π ∫_{|a|}^∞ θ`. -/
lemma sl_eq (hθ : Profile R θ) (a : ℝ) : sl θ a = 2 * π * ∫ s in Ioi |a|, θ s := by
  calc sl θ a = ∫ z : Fin 2 → ℝ, (fun r => θ (Real.sqrt (a ^ 2 + r ^ 2)) /
        Real.sqrt (a ^ 2 + r ^ 2)) ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 2))‖ := by
        unfold sl
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        unfold gker
        rw [norm_toLp_cons]
    _ = 2 * π * ∫ r in Ioi (0 : ℝ), r * (fun r => θ (Real.sqrt (a ^ 2 + r ^ 2)) /
        Real.sqrt (a ^ 2 + r ^ 2)) r :=
          planar_radial (fun r => θ (Real.sqrt (a ^ 2 + r ^ 2)) / Real.sqrt (a ^ 2 + r ^ 2))
    _ = 2 * π * ∫ s in Ioi |a|, θ s := by
        congr 1
        exact radial_subst hθ a

/-! ## The outer integral -/

/-- `∫_{-s}^{s} e^{-iκa} da = 2 sin(κs)/κ`. -/
lemma integral_exp_sym {κ : ℝ} (hκ : κ ≠ 0) (s : ℝ) :
    ∫ a in (-s)..s, Complex.exp (-(Complex.I * ((κ * a : ℝ) : ℂ))) =
      ((2 * Real.sin (κ * s) / κ : ℝ) : ℂ) := by
  have hc : (-(Complex.I * κ) : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, hκ]
  have e : ∀ a : ℝ, Complex.exp (-(Complex.I * ((κ * a : ℝ) : ℂ))) =
      Complex.exp ((-(Complex.I * κ)) * a) := by
    intro a; congr 1; push_cast; ring
  simp_rw [e]
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((-(Complex.I * κ)) * (s : ℂ)) =
      Complex.cos (κ * s) - Complex.sin (κ * s) * Complex.I := by
    rw [show (-(Complex.I * κ)) * (s : ℂ) = (-((κ : ℂ) * s)) * Complex.I by ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have h2 : Complex.exp ((-(Complex.I * κ)) * ((-s : ℝ) : ℂ)) =
      Complex.cos (κ * s) + Complex.sin (κ * s) * Complex.I := by
    rw [show (-(Complex.I * κ)) * ((-s : ℝ) : ℂ) = ((κ : ℂ) * s) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
  rw [h1, h2]
  have hκc : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  push_cast
  field_simp
  ring_nf
  try simp only [Complex.I_sq]
  try ring

/-- The kernel `ψ(a, s) = θ(s) 1{|a| < s}`. -/
noncomputable def psiK (θ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := if |p.1| < p.2 then θ p.2 else 0

lemma integral_psiK (a : ℝ) : ∫ s, psiK θ (a, s) = ∫ s in Ioi |a|, θ s := by
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [psiK, Set.indicator_apply, mem_Ioi]

/-- `∫ e^{-iκa} (∫_{|a|}^∞ θ) da = (2/κ) ∫_0^R θ(s) sin(κs) ds`. -/
lemma outer_eq (hθ : Profile R θ) {κ : ℝ} (hκ : κ ≠ 0) :
    ∫ a : ℝ, Complex.exp (-(Complex.I * ((κ * a : ℝ) : ℂ))) * ((∫ s in Ioi |a|, θ s : ℝ) : ℂ) =
      ((2 / κ * ∫ s in (0 : ℝ)..R, θ s * Real.sin (κ * s) : ℝ) : ℂ) := by
  have hR := hθ.pos
  set f : ℝ → ℝ → ℂ := fun a s => Complex.exp (-(Complex.I * ((κ * a : ℝ) : ℂ))) *
    ((psiK θ (a, s) : ℝ) : ℂ) with hf
  have hmeas : Measurable (Function.uncurry f) := by
    have hm : Measurable fun p : ℝ × ℝ => psiK θ p := by
      unfold psiK
      refine Measurable.ite ?_ (hθ.cont.measurable.comp measurable_snd) measurable_const
      exact measurableSet_lt (continuous_abs.measurable.comp measurable_fst) measurable_snd
    refine Measurable.mul ?_ (Complex.measurable_ofReal.comp hm)
    exact (Complex.measurable_exp.comp (by fun_prop))
  have hint : Integrable (Function.uncurry f) (volume.prod volume) := by
    have hbox : IntegrableOn (Function.uncurry f) (Icc (-R) R ×ˢ Icc 0 R) (volume.prod volume) := by
      rw [IntegrableOn, ← Measure.prod_restrict]
      refine Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall
        fun p => ?_)
      simp only [Function.uncurry, hf, norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_eq_abs]
      have h1 : |psiK θ p| ≤ 1 := by
        unfold psiK; split_ifs
        · exact hθ.bound _
        · simp
      have h2 : (-(Complex.I * ((κ * p.1 : ℝ) : ℂ))).re = 0 := by simp
      rw [h2, Real.exp_zero, one_mul]
      exact h1
    refine hbox.integrable_of_forall_notMem_eq_zero fun p hp => ?_
    simp only [Function.uncurry, hf]
    have h0 : psiK θ p = 0 := by
      unfold psiK
      split_ifs with h
      · by_contra hθ0
        apply hp
        have hlt : p.2 < R := by
          by_contra hge; push Not at hge; exact hθ0 (hθ.vanish _ hge)
        have ha := abs_lt.mp (lt_of_lt_of_le h hlt.le)
        exact ⟨⟨ha.1.le, ha.2.le⟩, ⟨(abs_nonneg _).trans h.le, hlt.le⟩⟩
      · rfl
    rw [h0, Complex.ofReal_zero, mul_zero]
  have hL : ∀ a : ℝ, Complex.exp (-(Complex.I * ((κ * a : ℝ) : ℂ))) *
      ((∫ s in Ioi |a|, θ s : ℝ) : ℂ) = ∫ s, f a s := by
    intro a
    rw [← integral_psiK, ← integral_complex_ofReal, ← integral_const_mul]
  simp_rw [hL]
  rw [integral_integral_swap hint]
  have hin : ∀ s : ℝ, ∫ a, f a s =
      ((θ s * (if 0 < s then 2 * Real.sin (κ * s) / κ else 0) : ℝ) : ℂ) := by
    intro s
    have e1 : ∀ a : ℝ, f a s = (Ioo (-s) s).indicator
        (fun a => Complex.exp (-(Complex.I * ((κ * a : ℝ) : ℂ))) * ((θ s : ℝ) : ℂ)) a := by
      intro a
      simp only [hf, psiK, Set.indicator_apply, mem_Ioo]
      by_cases h : |a| < s
      · rw [if_pos h, if_pos (abs_lt.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (abs_lt.mpr h')), Complex.ofReal_zero, mul_zero]
    simp_rw [e1]
    rw [integral_indicator measurableSet_Ioo, integral_mul_const]
    split_ifs with hs
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
        integral_exp_sym hκ s]
      push_cast; ring
    · have hem : Ioo (-s) s = ∅ := Ioo_eq_empty (by linarith)
      rw [hem, Measure.restrict_empty, integral_zero_measure]
      simp
  simp_rw [hin]
  rw [integral_complex_ofReal]
  congr 1
  have hsplit : ∫ s, θ s * (if 0 < s then 2 * Real.sin (κ * s) / κ else 0) =
      ∫ s in Ioi (0 : ℝ), θ s * (2 * Real.sin (κ * s) / κ) := by
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [Set.indicator_apply, mem_Ioi]
    split_ifs <;> simp
  rw [hsplit, intervalIntegral.integral_of_le hR.le]
  have hsub : ∫ s in Ioi (0 : ℝ), θ s * (2 * Real.sin (κ * s) / κ) =
      ∫ s in Ioc (0 : ℝ) R, θ s * (2 * Real.sin (κ * s) / κ) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun s hs => by
        have hs' : R < s := by
          rcases hs with ⟨h0, h1⟩
          simp only [mem_Ioc, not_and, not_le] at h1
          exact h1 h0
        rw [hθ.vanish s hs'.le, zero_mul]
  rw [hsub, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  ring

/-! ## The radial Fourier integral and the bound -/

/-- **The radial Fourier integral**: `ĝ(k) = (4π/|k|) ∫_0^R θ(r) sin(|k| r) dr` for `k ≠ 0`. -/
theorem gFT_eq_sin (hθ : Profile R θ) {k : E3} (hk : k ≠ 0) :
    gFT θ k = ((4 * π / ‖k‖ * ∫ r in (0 : ℝ)..R, θ r * Real.sin (‖k‖ * r) : ℝ) : ℂ) := by
  have hκ : ‖k‖ ≠ 0 := norm_ne_zero_iff.mpr hk
  rw [gFT_rot, gFT_slice hθ]
  have e : ∀ a : ℝ, Complex.exp (-(Complex.I * ((‖k‖ * a : ℝ) : ℂ))) * ((sl θ a : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ) * (Complex.exp (-(Complex.I * ((‖k‖ * a : ℝ) : ℂ))) *
        ((∫ s in Ioi |a|, θ s : ℝ) : ℂ)) := by
    intro a; rw [sl_eq hθ]; push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, outer_eq hθ hκ]
  push_cast
  ring

/-- One integration by parts: `|∫_0^R θ(r) sin(κr) dr| ≤ (1 + V_θ)/κ`. -/
lemma abs_integral_sin_le (hθ : Profile R θ) {κ : ℝ} (hκ : 0 < κ) :
    |∫ r in (0 : ℝ)..R, θ r * Real.sin (κ * r)| ≤ (1 + tv R θ) / κ := by
  have hR := hθ.pos
  have hd : ∀ x, HasDerivAt θ (deriv θ x) x := fun x =>
    ((hθ.diff.differentiable (by norm_num)) x).hasDerivAt
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hv : ∀ x, HasDerivAt (fun r => -Real.cos (κ * r) / κ) (Real.sin (κ * x)) x := by
    intro x
    have h := ((((hasDerivAt_id' x).const_mul κ).cos).neg).div_const κ
    exact h.congr_deriv (by field_simp)
  have hcd : Continuous (deriv θ) := hθ.diff.continuous_deriv (by norm_num)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := R)
    (fun x _ => hd x) (fun x _ => hv x) (hcd.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun r => Real.sin (κ * r)).intervalIntegrable _ _)
  rw [hibp, hθ.vanish R le_rfl, hθ.zero]
  have hI : |∫ x in (0 : ℝ)..R, deriv θ x * (-Real.cos (κ * x) / κ)| ≤ tv R θ / κ := by
    calc |∫ x in (0 : ℝ)..R, deriv θ x * (-Real.cos (κ * x) / κ)|
        ≤ ∫ x in (0 : ℝ)..R, |deriv θ x * (-Real.cos (κ * x) / κ)| :=
          intervalIntegral.abs_integral_le_integral_abs hR.le
      _ ≤ ∫ x in (0 : ℝ)..R, |deriv θ x| / κ := by
          refine intervalIntegral.integral_mono_on hR.le ?_ ?_ fun x _ => ?_
          · exact (hcd.mul (by fun_prop : Continuous fun r => -Real.cos (κ * r) / κ)).abs
              |>.intervalIntegrable _ _
          · exact (hcd.abs.div_const κ).intervalIntegrable _ _
          · rw [abs_mul, abs_div, abs_neg, abs_of_pos hκ, mul_div_assoc']
            exact div_le_div_of_nonneg_right
              (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)) hκ.le
      _ = tv R θ / κ := by
          unfold tv; rw [intervalIntegral.integral_div]
  have e : (0 : ℝ) * (-Real.cos (κ * R) / κ) - 1 * (-Real.cos (κ * 0) / κ) = 1 / κ := by
    simp only [zero_mul, one_mul, mul_zero, Real.cos_zero, zero_sub]
    ring
  rw [e]
  calc |1 / κ - ∫ x in (0 : ℝ)..R, deriv θ x * (-Real.cos (κ * x) / κ)|
      ≤ |1 / κ| + |∫ x in (0 : ℝ)..R, deriv θ x * (-Real.cos (κ * x) / κ)| := abs_sub _ _
    _ ≤ 1 / κ + tv R θ / κ := by rw [abs_of_pos (by positivity)]; linarith
    _ = (1 + tv R θ) / κ := by ring

/-- **The domination**: `|ĝ(k)| ≤ 4π (1 + V_θ)/|k|²` for `k ≠ 0`. -/
theorem norm_gFT_le (hθ : Profile R θ) {k : E3} (hk : k ≠ 0) :
    ‖gFT θ k‖ ≤ 4 * π * (1 + tv R θ) / ‖k‖ ^ 2 := by
  have hκ : 0 < ‖k‖ := norm_pos_iff.mpr hk
  rw [gFT_eq_sin hθ hk, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : 0 < 4 * π / ‖k‖)]
  calc 4 * π / ‖k‖ * |∫ r in (0 : ℝ)..R, θ r * Real.sin (‖k‖ * r)|
      ≤ 4 * π / ‖k‖ * ((1 + tv R θ) / ‖k‖) :=
        mul_le_mul_of_nonneg_left (abs_integral_sin_le hθ hκ) (by positivity)
    _ = 4 * π * (1 + tv R θ) / ‖k‖ ^ 2 := by field_simp

/-! ## The lattice coefficients: eq:rangecut -/

/-- The momentum `k_ν = 2πν/L` as a vector of `ℝ³`. -/
noncomputable def kvec (L : ℝ) (ν : Lattice3) : E3 :=
  WithLp.toLp 2 (fun i => 2 * π / L * (ν i : ℝ))

lemma norm_kvec_sq (L : ℝ) (ν : Lattice3) : ‖kvec L ν‖ ^ 2 = kSq L ν := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold kvec kSq
  rw [latticeNormSq_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma kvec_ne_zero {L : ℝ} (hL : 0 < L) {ν : Lattice3} (hν : ν ≠ (fun _ => 0)) :
    kvec L ν ≠ 0 := by
  intro h
  have h1 := norm_kvec_sq L ν
  rw [h, norm_zero] at h1
  have h2 : 0 < kSq L ν := by
    unfold kSq
    have := latticeNormSq_pos hν
    positivity
  rw [← h1] at h2
  norm_num at h2

lemma kvec_zero (L : ℝ) : kvec L (fun _ => 0) = 0 := by
  unfold kvec
  simp only [Int.cast_zero, mul_zero]
  rfl

/-- **The Fourier coefficients of `g_L`** on the cell `T_L`: `ĝ_L(ν) = Ω⁻¹ ĝ(k_ν)`. -/
noncomputable def ghat (L : ℝ) (θ : ℝ → ℝ) (ν : Lattice3) : ℂ := gFT θ (kvec L ν) / ((L ^ 3 : ℝ) : ℂ)

/-- **eq:rangecut**: `|ĝ_L(ν)| ≤ (1 + V_θ) ŵ(ν)` for `ν ≠ 0`, `ŵ(ν) = 4π/(Ω |k_ν|²)`. -/
theorem rangecut {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) : RangeCut L (1 + tv R θ) (ghat L θ) := by
  intro ν hν
  have hk := kvec_ne_zero hL hν
  have hb := norm_gFT_le hθ hk
  rw [norm_kvec_sq] at hb
  have hks : 0 < kSq L ν := by
    unfold kSq
    have := latticeNormSq_pos hν
    positivity
  unfold ghat
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖gFT θ (kvec L ν)‖ / L ^ 3 ≤ 4 * π * (1 + tv R θ) / kSq L ν / L ^ 3 :=
        div_le_div_of_nonneg_right hb (by positivity)
    _ = (1 + tv R θ) * (4 * π / (L ^ 3 * kSq L ν)) := by
        field_simp

/-- **The zero mode**: `|ĝ_L(0)| ≤ 2π R²/Ω`; for `R = L/2`, `|ĝ_L(0)| ≤ π/(2L)`. -/
theorem ghat_zero_le {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) :
    ‖ghat L θ (fun _ => 0)‖ ≤ 2 * π * R ^ 2 / L ^ 3 := by
  unfold ghat
  rw [kvec_zero, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact div_le_div_of_nonneg_right (norm_gFT_zero_le hθ) (by positivity)

theorem ghat_zero_le_half {L : ℝ} (hL : 0 < L) (hθ : Profile (L / 2) θ) :
    ‖ghat L θ (fun _ => 0)‖ ≤ π / (2 * L) := by
  refine (ghat_zero_le hL hθ).trans (le_of_eq ?_)
  field_simp
  try ring

/-! ## `lem:scaling` for `g_L` -/

section Scaling

variable {L : ℝ} (hL : 0 < L) (hθ : Profile R θ)
include hL hθ

theorem scaling_low_gL {J : ℝ} (hJ : 0 ≤ J) (F : Finset Lattice3)
    (hF : ∀ ν ∈ F, ν ≠ (fun _ => 0) ∧ kSq L ν ≤ J ^ 2) :
    ∑ ν ∈ F, ‖ghat L θ ν‖ ≤ 27 / Real.pi ^ 2 * (1 + tv R θ) * J :=
  scaling_low hL (by linarith [hθ.tv_nonneg]) (rangecut hL hθ) hJ F hF

theorem scaling_tail_gL {J : ℝ} (hJ : 0 < J) (F : Finset Lattice3)
    (hF : ∀ ν ∈ F, J ^ 2 < kSq L ν) :
    L ^ 3 * ∑ ν ∈ F, ‖ghat L θ ν‖ ^ 2 ≤ 216 * Real.sqrt 3 / Real.pi * (1 + tv R θ) ^ 2 / J :=
  scaling_tail hL (rangecut hL hθ) hJ F hF

theorem scaling_moment2_gL {K : ℝ} (hK : 0 ≤ K) (F : Finset Lattice3)
    (hF : ∀ ν ∈ F, ν ≠ (fun _ => 0) ∧ kSq L ν ≤ (2 * K) ^ 2) :
    L ^ 3 * ∑ ν ∈ F, kSq L ν * ‖ghat L θ ν‖ ^ 2 ≤ 216 / Real.pi * (1 + tv R θ) ^ 2 * K :=
  scaling_moment2 hL (rangecut hL hθ) hK F hF

theorem scaling_moment4_gL {K : ℝ} (hK : 0 ≤ K) (F : Finset Lattice3)
    (hF : ∀ ν ∈ F, ν ≠ (fun _ => 0) ∧ kSq L ν ≤ (2 * K) ^ 2) :
    L ^ 3 * ∑ ν ∈ F, kSq L ν ^ 2 * ‖ghat L θ ν‖ ^ 2 ≤
      864 / Real.pi * (1 + tv R θ) ^ 2 * K ^ 3 :=
  scaling_moment4 hL (rangecut hL hθ) hK F hF

end Scaling

end FreeBoundary
