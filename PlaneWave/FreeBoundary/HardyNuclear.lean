import PlaneWave.FreeBoundary.FreeDynamicsEndpoint

/-!
# Free-space regularity, part 5: Hardy's inequality for one particle and a point

Hardy's inequality of `PlaneWave.FreeBoundary.HardyInequality` for every Coulomb term: for an affine
map `Y(x) = T x - y₀` of the configuration into `ℝ³` whose linear part is the identity in the
coordinates of particle `i` (`T e_{(i,c)} = e_c`), `‖f / |Y|‖² ≤ 4 Σ_c ‖∂_{(i,c)} f‖²` for `f ∈ L²`
with weak gradient `g`. This covers the pairs `Y = x_i - x_j` and the nuclear terms `Y = x_i - R`
(`R` a nucleus). The proof is that of `PlaneWave.FreeBoundary.HardyInequality`, with the vector
field `V_δ = Y/(|Y|² + δ²)`.

* `aQ`, `aV`, `dirD_aV`, `sum_dirD_aV_ge`, `sum_aV_sq_le`: the vector field;
* `hardy_smooth_aff`, `hardy_delta_aff`, **`hardy_weak_aff`**: the inequality;
* `volume_particle_eq`, `ae_particle_ne`: a particle avoids a given point almost everywhere;
* **`hardy_nuc`**: the quotient `f / |x_i - R|` in `L²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology ENNReal
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

variable {eta : ℕ}

/-! ## The vector field -/

section Field

variable (T : Rcfg eta →L[ℝ] E3) (y₀ : E3)

/-- `Q_δ = |Y|² + δ²`, `Y = T x - y₀`. -/
noncomputable def aQ (δ : ℝ) (x : Rcfg eta) : ℝ := ‖T x - y₀‖ ^ 2 + δ ^ 2

/-- The vector field `V_{δ,c} = Y_c / Q_δ`. -/
noncomputable def aV (δ : ℝ) (c : Fin 3) (x : Rcfg eta) : ℝ := (T x - y₀) c * (aQ T y₀ δ x)⁻¹

variable {δ : ℝ} (hδ : 0 < δ)
include hδ

lemma aQ_pos (x : Rcfg eta) : 0 < aQ T y₀ δ x := by
  unfold aQ
  positivity

lemma aQ_ge (x : Rcfg eta) : δ ^ 2 ≤ aQ T y₀ δ x := by
  unfold aQ
  nlinarith [sq_nonneg ‖T x - y₀‖]

omit hδ in
lemma norm_sq_E3 (y : E3) : ‖y‖ ^ 2 = ∑ c : Fin 3, (y c) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

omit hδ in
lemma hasFDerivAt_aY (x : Rcfg eta) : HasFDerivAt (fun y => T y - y₀) T x :=
  T.hasFDerivAt.sub_const y₀

omit hδ in
lemma dirD_aY_comp {i : Fin eta} (hT : ∀ c, T (Pi.single (i, c) 1) = EuclideanSpace.single c 1)
    (c d : Fin 3) (x : Rcfg eta) :
    dirD (i, c) (fun y => (T y - y₀) d) x = if c = d then 1 else 0 := by
  have e : (fun y => (T y - y₀) d) =
      fun y => ((EuclideanSpace.proj d : E3 →L[ℝ] ℝ).comp T) y - y₀ d := by
    funext y
    simp
  have h : HasFDerivAt (fun y => (T y - y₀) d)
      ((EuclideanSpace.proj d : E3 →L[ℝ] ℝ).comp T) x := by
    rw [e]
    exact ((EuclideanSpace.proj d : E3 →L[ℝ] ℝ).comp T).hasFDerivAt.sub_const _
  unfold dirD
  rw [h.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hT]
  by_cases hcd : c = d
  · subst hcd
    simp
  · simp [hcd, Ne.symm hcd]

omit hδ in
lemma dirD_aQ {i : Fin eta} (hT : ∀ c, T (Pi.single (i, c) 1) = EuclideanSpace.single c 1)
    (c : Fin 3) (x : Rcfg eta) : dirD (i, c) (aQ T y₀ δ) x = 2 * (T x - y₀) c := by
  have h : HasFDerivAt (aQ T y₀ δ) (2 • (innerSL ℝ (T x - y₀)).comp T) x :=
    ((hasFDerivAt_aY T y₀ x).norm_sq).add_const _
  unfold dirD
  rw [h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    innerSL_apply_apply, hT]
  rw [EuclideanSpace.inner_single_right]
  simp

omit hδ in
lemma differentiable_aQ : Differentiable ℝ (aQ T y₀ δ) := fun x =>
  (((hasFDerivAt_aY T y₀ x).norm_sq).add_const (δ ^ 2)).differentiableAt

omit hδ in
lemma continuous_aQ : Continuous (aQ T y₀ δ) := (differentiable_aQ T y₀).continuous

omit hδ in
lemma differentiable_aY_comp (c : Fin 3) : Differentiable ℝ (fun y => (T y - y₀) c) := by
  have e : (fun y => (T y - y₀) c) =
      fun y => ((EuclideanSpace.proj c : E3 →L[ℝ] ℝ).comp T) y - y₀ c := by
    funext y
    simp
  rw [e]
  exact ((EuclideanSpace.proj c : E3 →L[ℝ] ℝ).comp T).differentiable.sub_const _

/-- `∂_{(i,c)} V_c = Q⁻¹ - 2 Y_c² Q⁻²`. -/
lemma dirD_aV {i : Fin eta} (hT : ∀ c, T (Pi.single (i, c) 1) = EuclideanSpace.single c 1)
    (c : Fin 3) (x : Rcfg eta) :
    dirD (i, c) (aV T y₀ δ c) x =
      (aQ T y₀ δ x)⁻¹ - 2 * ((T x - y₀) c) ^ 2 * ((aQ T y₀ δ x)⁻¹) ^ 2 := by
  have hyd : DifferentiableAt ℝ (fun y => (T y - y₀) c) x := differentiable_aY_comp T y₀ c x
  have hQd : DifferentiableAt ℝ (fun y => (aQ T y₀ δ y)⁻¹) x :=
    (differentiable_aQ T y₀ x).inv (aQ_pos T y₀ hδ x).ne'
  have hinv : dirD (i, c) (fun y => (aQ T y₀ δ y)⁻¹) x =
      -((aQ T y₀ δ x ^ 2)⁻¹ * dirD (i, c) (aQ T y₀ δ) x) := by
    have h : HasFDerivAt (fun y => (aQ T y₀ δ y)⁻¹)
        ((-((aQ T y₀ δ x) ^ 2)⁻¹) • fderiv ℝ (aQ T y₀ δ) x) x :=
      (hasDerivAt_inv (aQ_pos T y₀ hδ x).ne').comp_hasFDerivAt x
        (differentiable_aQ T y₀ x).hasFDerivAt
    unfold dirD
    rw [h.fderiv]
    simp
  unfold aV
  rw [dirD_mul_real hyd hQd, dirD_aY_comp T y₀ hT, if_pos rfl, hinv, dirD_aQ T y₀ hT]
  ring

lemma continuous_aV (c : Fin 3) : Continuous (aV T y₀ δ c) := by
  have hQi : Continuous fun x => (aQ T y₀ δ x)⁻¹ :=
    (continuous_aQ T y₀).inv₀ fun x => (aQ_pos T y₀ hδ x).ne'
  exact (differentiable_aY_comp T y₀ c).continuous.mul hQi

lemma continuous_dirD_aV {i : Fin eta}
    (hT : ∀ c, T (Pi.single (i, c) 1) = EuclideanSpace.single c 1) (c : Fin 3) :
    Continuous (dirD (i, c) (aV T y₀ δ c)) := by
  have e : dirD (i, c) (aV T y₀ δ c) = fun x =>
      (aQ T y₀ δ x)⁻¹ - 2 * ((T x - y₀) c) ^ 2 * ((aQ T y₀ δ x)⁻¹) ^ 2 :=
    funext fun x => dirD_aV T y₀ hδ hT c x
  rw [e]
  have hQi : Continuous fun x => (aQ T y₀ δ x)⁻¹ :=
    (continuous_aQ T y₀).inv₀ fun x => (aQ_pos T y₀ hδ x).ne'
  have hy : Continuous fun x => (T x - y₀) c := (differentiable_aY_comp T y₀ c).continuous
  exact hQi.sub ((continuous_const.mul (hy.pow 2)).mul (hQi.pow 2))

lemma differentiable_aV (c : Fin 3) : Differentiable ℝ (aV T y₀ δ c) := fun x =>
  (differentiable_aY_comp T y₀ c x).mul ((differentiable_aQ T y₀ x).inv (aQ_pos T y₀ hδ x).ne')

/-- `div V ≥ Q⁻¹`. -/
lemma sum_dirD_aV_ge {i : Fin eta}
    (hT : ∀ c, T (Pi.single (i, c) 1) = EuclideanSpace.single c 1) (x : Rcfg eta) :
    (aQ T y₀ δ x)⁻¹ ≤ ∑ c : Fin 3, dirD (i, c) (aV T y₀ δ c) x := by
  simp_rw [dirD_aV T y₀ hδ hT]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← norm_sq_E3]
  have hQp := aQ_pos T y₀ hδ x
  have hy : ‖T x - y₀‖ ^ 2 ≤ aQ T y₀ δ x := by
    unfold aQ
    nlinarith [sq_nonneg δ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e : 2 * ‖T x - y₀‖ ^ 2 * (aQ T y₀ δ x)⁻¹ ^ 2 ≤ 2 * (aQ T y₀ δ x)⁻¹ := by
    have : ‖T x - y₀‖ ^ 2 * (aQ T y₀ δ x)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hQp]
      exact hy
    have h2 : 0 ≤ (aQ T y₀ δ x)⁻¹ := (inv_pos.mpr hQp).le
    nlinarith
  push_cast
  linarith

/-- `|V|² ≤ Q⁻¹`. -/
lemma sum_aV_sq_le (x : Rcfg eta) : ∑ c : Fin 3, aV T y₀ δ c x ^ 2 ≤ (aQ T y₀ δ x)⁻¹ := by
  unfold aV
  simp_rw [mul_pow]
  rw [← Finset.sum_mul, ← norm_sq_E3]
  have hQp := aQ_pos T y₀ hδ x
  have hy : ‖T x - y₀‖ ^ 2 ≤ aQ T y₀ δ x := by
    unfold aQ
    nlinarith [sq_nonneg δ]
  rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  have : (aQ T y₀ δ x)⁻¹ * aQ T y₀ δ x ^ 2 = aQ T y₀ δ x := by field_simp
  rw [this]
  exact hy

omit hδ in
lemma abs_comp_le_norm (y : E3) (c : Fin 3) : |y c| ≤ ‖y‖ := by
  have h2 : (y c) ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [norm_sq_E3]
    exact Finset.single_le_sum (f := fun d => (y d) ^ 2) (fun d _ => sq_nonneg _)
      (Finset.mem_univ c)
  exact abs_le_of_sq_le_sq' h2 (norm_nonneg _) |> fun h => abs_le.mpr ⟨h.1, h.2⟩

lemma abs_aV_le (c : Fin 3) (x : Rcfg eta) : |aV T y₀ δ c x| ≤ 1 / δ := by
  unfold aV
  have hQp := aQ_pos T y₀ hδ x
  have h1 := abs_comp_le_norm (T x - y₀) c
  have h3 : ‖T x - y₀‖ * δ ≤ aQ T y₀ δ x := by
    unfold aQ
    nlinarith [sq_nonneg (‖T x - y₀‖ - δ)]
  rw [abs_mul, abs_inv, abs_of_pos hQp, ← div_eq_mul_inv, div_le_div_iff₀ hQp hδ]
  nlinarith [abs_nonneg ((T x - y₀) c)]

lemma abs_dirD_aV_le {i : Fin eta}
    (hT : ∀ c, T (Pi.single (i, c) 1) = EuclideanSpace.single c 1) (c : Fin 3) (x : Rcfg eta) :
    |dirD (i, c) (aV T y₀ δ c) x| ≤ 3 / δ ^ 2 := by
  rw [dirD_aV T y₀ hδ hT]
  have hQp := aQ_pos T y₀ hδ x
  have hQg := aQ_ge T y₀ hδ x
  have hyc : ((T x - y₀) c) ^ 2 ≤ aQ T y₀ δ x := by
    have h1 := abs_comp_le_norm (T x - y₀) c
    have h2 : ((T x - y₀) c) ^ 2 ≤ ‖T x - y₀‖ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    unfold aQ
    nlinarith [sq_nonneg δ]
  have hi : (aQ T y₀ δ x)⁻¹ ≤ 1 / δ ^ 2 := by
    rw [one_div]
    exact inv_anti₀ (by positivity) hQg
  have hi0 : 0 ≤ (aQ T y₀ δ x)⁻¹ := (inv_pos.mpr hQp).le
  have h2 : 2 * ((T x - y₀) c) ^ 2 * ((aQ T y₀ δ x)⁻¹) ^ 2 ≤ 2 * (aQ T y₀ δ x)⁻¹ := by
    have : ((T x - y₀) c) ^ 2 * (aQ T y₀ δ x)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hQp]
      exact hyc
    nlinarith
  have h3 : 0 ≤ 2 * ((T x - y₀) c) ^ 2 * ((aQ T y₀ δ x)⁻¹) ^ 2 := by positivity
  have h4 : 3 / δ ^ 2 = 3 * (1 / δ ^ 2) := by ring
  have h5 : 0 ≤ 1 / δ ^ 2 := by positivity
  rw [abs_le, h4]
  constructor <;> linarith

lemma norm_aQ_inv_le (x : Rcfg eta) : ‖(aQ T y₀ δ x)⁻¹‖ ≤ 1 / δ ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (aQ_pos T y₀ hδ x)), one_div]
  exact inv_anti₀ (by positivity) (aQ_ge T y₀ hδ x)

lemma integrable_aQ_weight {F : Rcfg eta → ℂ} (hF : MemLp F 2 volume) :
    Integrable (fun x => ‖F x‖ ^ 2 * (aQ T y₀ δ x)⁻¹) := by
  have hN : Integrable (fun x => ‖F x‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hF.1).mp hF
  have hQi : Continuous fun x => (aQ T y₀ δ x)⁻¹ :=
    (continuous_aQ T y₀).inv₀ fun x => (aQ_pos T y₀ hδ x).ne'
  exact hN.mul_bdd hQi.aestronglyMeasurable (ae_of_all _ (norm_aQ_inv_le T y₀ hδ))

end Field

/-! ## The inequality -/

section Hardy

variable (T : Rcfg eta →L[ℝ] E3) (y₀ : E3) {i : Fin eta}
  (hT : ∀ c, T (Pi.single (i, c) 1) = EuclideanSpace.single c 1)
variable {δ : ℝ} (hδ : 0 < δ)
include hT hδ

/-- Hardy's inequality at `δ > 0` for a `C¹` function. -/
lemma hardy_smooth_aff {F : Rcfg eta → ℂ} (hF : ContDiff ℝ 1 F) (h0 : MemLp F 2 volume)
    (h1 : ∀ c : Fin 3, MemLp (dirD (i, c) F) 2 volume) :
    ∫ x, ‖F x‖ ^ 2 * (aQ T y₀ δ x)⁻¹ ≤ 4 * ∑ c : Fin 3, ∫ x, ‖dirD (i, c) F x‖ ^ 2 := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hFc : Continuous F := hF.continuous
  have hdFc : ∀ c : Fin 3, Continuous (dirD (i, c) F) := fun c =>
    continuous_dirD hF (by norm_num) _
  have hN : Integrable (fun x => ‖F x‖ ^ 2) := (memLp_two_iff_integrable_sq_norm h0.1).mp h0
  have hD : ∀ c : Fin 3, Integrable (fun x => ‖dirD (i, c) F x‖ ^ 2) := fun c =>
    (memLp_two_iff_integrable_sq_norm (h1 c).1).mp (h1 c)
  have hNd : ∀ x, HasFDerivAt (fun y => ‖F y‖ ^ 2)
      (2 • (innerSL ℝ (F x)).comp (fderiv ℝ F x)) x := fun x =>
    (hFd x).hasFDerivAt.norm_sq
  have hdN : ∀ (c : Fin 3) x, dirD (i, c) (fun y => ‖F y‖ ^ 2) x =
      2 * ⟪F x, dirD (i, c) F x⟫_ℝ := by
    intro c x
    unfold dirD
    rw [(hNd x).fderiv]
    simp
    ring
  have hI : Integrable (fun x => ‖F x‖ ^ 2 * (aQ T y₀ δ x)⁻¹) :=
    integrable_aQ_weight T y₀ hδ h0
  have hint2 : ∀ c : Fin 3, Integrable fun x => 2 * ⟪F x, dirD (i, c) F x⟫_ℝ * aV T y₀ δ c x := by
    intro c
    refine (((h0.norm.integrable_mul (h1 c).norm).const_mul (2 / δ))).mono'
      (((continuous_const.mul (hFc.inner (hdFc c))).mul
        (continuous_aV T y₀ hδ c)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
    have e1 := abs_real_inner_le_norm (F x) (dirD (i, c) F x)
    have e2 := abs_aV_le T y₀ hδ c x
    calc 2 * |⟪F x, dirD (i, c) F x⟫_ℝ| * |aV T y₀ δ c x|
        ≤ 2 * (‖F x‖ * ‖dirD (i, c) F x‖) * (1 / δ) := by gcongr
      _ = 2 / δ * (‖F x‖ * ‖dirD (i, c) F x‖) := by ring
  have hint1 : ∀ c : Fin 3, Integrable fun x => ‖F x‖ ^ 2 * dirD (i, c) (aV T y₀ δ c) x :=
    fun c => hN.mul_bdd (continuous_dirD_aV T y₀ hδ hT c).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_dirD_aV_le T y₀ hδ hT c x)
  -- integration by parts
  have hibp : ∀ c : Fin 3, ∫ x, ‖F x‖ ^ 2 * dirD (i, c) (aV T y₀ δ c) x =
      -∫ x, 2 * ⟪F x, dirD (i, c) F x⟫_ℝ * aV T y₀ δ c x := by
    intro c
    have i3 : Integrable fun x => ‖F x‖ ^ 2 * aV T y₀ δ c x :=
      hN.mul_bdd (continuous_aV T y₀ hδ c).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_aV_le T y₀ hδ c x)
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (𝕜 := ℝ)
      (f := fun y => ‖F y‖ ^ 2) (g := aV T y₀ δ c) (v := Pi.single (i, c) 1)
      ((hint2 c).congr (ae_of_all _ fun x => by
        show 2 * ⟪F x, dirD (i, c) F x⟫_ℝ * aV T y₀ δ c x =
          dirD (i, c) (fun y => ‖F y‖ ^ 2) x * aV T y₀ δ c x
        rw [hdN c x])) (hint1 c) i3 (fun x _ => (hNd x).differentiableAt)
      (fun x _ => differentiable_aV T y₀ hδ c x)
    have e : ∀ x, fderiv ℝ (fun y => ‖F y‖ ^ 2) x (Pi.single (i, c) 1) =
        2 * ⟪F x, dirD (i, c) F x⟫_ℝ := fun x => hdN c x
    simp_rw [e] at h
    exact h
  -- the pointwise inequalities
  have hpt1 : ∀ x, ‖F x‖ ^ 2 * (aQ T y₀ δ x)⁻¹ ≤
      ∑ c : Fin 3, ‖F x‖ ^ 2 * dirD (i, c) (aV T y₀ δ c) x := fun x => by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_dirD_aV_ge T y₀ hδ hT x) (sq_nonneg _)
  have hpt2 : ∀ x, ∑ c : Fin 3, -(2 * ⟪F x, dirD (i, c) F x⟫_ℝ * aV T y₀ δ c x) ≤
      (1 / 2) * (‖F x‖ ^ 2 * (aQ T y₀ δ x)⁻¹) +
        2 * ∑ c : Fin 3, ‖dirD (i, c) F x‖ ^ 2 := fun x => by
    have hc : ∀ c : Fin 3, -(2 * ⟪F x, dirD (i, c) F x⟫_ℝ * aV T y₀ δ c x) ≤
        (1 / 2) * (‖F x‖ ^ 2 * aV T y₀ δ c x ^ 2) + 2 * ‖dirD (i, c) F x‖ ^ 2 := by
      intro c
      have e1 := abs_real_inner_le_norm (F x) (dirD (i, c) F x)
      have e2 : -(2 * ⟪F x, dirD (i, c) F x⟫_ℝ * aV T y₀ δ c x) ≤
          2 * (‖F x‖ * ‖dirD (i, c) F x‖) * |aV T y₀ δ c x| := by
        have := neg_abs_le (2 * ⟪F x, dirD (i, c) F x⟫_ℝ * aV T y₀ δ c x)
        rw [abs_mul, abs_mul, abs_two] at this
        have h3 : 2 * |⟪F x, dirD (i, c) F x⟫_ℝ| * |aV T y₀ δ c x| ≤
            2 * (‖F x‖ * ‖dirD (i, c) F x‖) * |aV T y₀ δ c x| := by gcongr
        linarith
      have e3 : 2 * (‖F x‖ * ‖dirD (i, c) F x‖) * |aV T y₀ δ c x| ≤
          (1 / 2) * (‖F x‖ ^ 2 * aV T y₀ δ c x ^ 2) + 2 * ‖dirD (i, c) F x‖ ^ 2 := by
        nlinarith [sq_nonneg (‖F x‖ * |aV T y₀ δ c x| - 2 * ‖dirD (i, c) F x‖),
          sq_abs (aV T y₀ δ c x)]
      linarith
    have hs := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hc c
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    have hV2 := sum_aV_sq_le T y₀ hδ x
    have : (1 / 2) * (‖F x‖ ^ 2 * ∑ c : Fin 3, aV T y₀ δ c x ^ 2) ≤
        (1 / 2) * (‖F x‖ ^ 2 * (aQ T y₀ δ x)⁻¹) := by
      have := mul_le_mul_of_nonneg_left hV2 (sq_nonneg ‖F x‖)
      linarith
    linarith
  -- integrate
  have hint2' : ∀ c : Fin 3, Integrable fun x => -(2 * ⟪F x, dirD (i, c) F x⟫_ℝ *
      aV T y₀ δ c x) := fun c => (hint2 c).neg
  set I := ∫ x, ‖F x‖ ^ 2 * (aQ T y₀ δ x)⁻¹ with hIdef
  set G := ∑ c : Fin 3, ∫ x, ‖dirD (i, c) F x‖ ^ 2 with hGdef
  have step1 : I ≤ ∑ c : Fin 3, ∫ x, ‖F x‖ ^ 2 * dirD (i, c) (aV T y₀ δ c) x := by
    rw [← integral_finsetSum _ fun c _ => hint1 c]
    exact integral_mono hI (integrable_finsetSum _ fun c _ => hint1 c) hpt1
  have step2 : ∑ c : Fin 3, ∫ x, ‖F x‖ ^ 2 * dirD (i, c) (aV T y₀ δ c) x =
      ∫ x, ∑ c : Fin 3, -(2 * ⟪F x, dirD (i, c) F x⟫_ℝ * aV T y₀ δ c x) := by
    rw [integral_finsetSum _ fun c _ => hint2' c]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hibp c, integral_neg]
  have step3 : ∫ x, ∑ c : Fin 3, -(2 * ⟪F x, dirD (i, c) F x⟫_ℝ * aV T y₀ δ c x) ≤
      (1 / 2) * I + 2 * G := by
    have hR : Integrable fun x => (1 / 2) * (‖F x‖ ^ 2 * (aQ T y₀ δ x)⁻¹) +
        2 * ∑ c : Fin 3, ‖dirD (i, c) F x‖ ^ 2 :=
      (hI.const_mul _).add ((integrable_finsetSum _ fun c _ => hD c).const_mul _)
    calc ∫ x, ∑ c : Fin 3, -(2 * ⟪F x, dirD (i, c) F x⟫_ℝ * aV T y₀ δ c x)
        ≤ ∫ x, ((1 / 2) * (‖F x‖ ^ 2 * (aQ T y₀ δ x)⁻¹) +
            2 * ∑ c : Fin 3, ‖dirD (i, c) F x‖ ^ 2) :=
          integral_mono (integrable_finsetSum _ fun c _ => hint2' c) hR hpt2
      _ = (1 / 2) * I + 2 * G := by
          rw [integral_add (hI.const_mul _)
              ((integrable_finsetSum _ fun c _ => hD c).const_mul _),
            integral_const_mul, integral_const_mul, integral_finsetSum _ fun c _ => hD c]
  linarith

/-- Hardy's inequality at `δ > 0` for `f ∈ L²` with a weak gradient. -/
lemma hardy_delta_aff {f : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad f g) :
    ∫ x, ‖f x‖ ^ 2 * (aQ T y₀ δ x)⁻¹ ≤ 4 * ∑ c : Fin 3, ‖g (i, c)‖ ^ 2 := by
  set G := ∑ c : Fin 3, ‖g (i, c)‖ ^ 2 with hGdef
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hsm : ∀ n : ℕ, ∫ x, ‖moll (rhoN n) f x‖ ^ 2 * (aQ T y₀ δ x)⁻¹ ≤ 4 * G := by
    intro n
    rw [hGdef]
    have hc := hasCompactSupport_rhoN (eta := eta) n
    have hF : ContDiff ℝ 1 (moll (rhoN n) f) :=
      contDiff_moll hc (contDiff_rhoN n) (locInt_L2 f)
    have hd : ∀ c : Fin 3, dirD (i, c) (moll (rhoN n) f) = moll (rhoN n) (g (i, c)) :=
      fun c => by
        rw [dirD_moll hc (contDiff_rhoN n) (locInt_L2 f)]
        funext x
        exact moll_dirD_eq hg hc (contDiff_rhoN n) _ x
    have h := hardy_smooth_aff T y₀ hT hδ hF (memLp_moll hc (continuous_rhoN n) f).1
      (fun c => by rw [hd c]; exact (memLp_moll hc (continuous_rhoN n) _).1)
    refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) (by norm_num))
    rw [hd c, ← norm_sq_eq_of_ae (mollN_ae n _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_mollN_le n _) 2
  have hlam : ∀ l : ℝ, 0 < l → ∫ x, ‖f x‖ ^ 2 * (aQ T y₀ δ x)⁻¹ ≤ (1 + l) * (4 * G) := by
    intro l hl
    have hb : ∀ n : ℕ, ∫ x, ‖f x‖ ^ 2 * (aQ T y₀ δ x)⁻¹ ≤
        (1 + l) * (4 * G) + (1 + 1 / l) * (1 / δ ^ 2) * ‖f - mollN n f‖ ^ 2 := by
      intro n
      have hc := hasCompactSupport_rhoN (eta := eta) n
      have hm := (memLp_moll hc (continuous_rhoN n) f).1
      have hdiff : (⇑(f - mollN n f) : Rcfg eta → ℂ) =ᵐ[volume]
          fun x => f x - moll (rhoN n) f x := by
        filter_upwards [Lp.coeFn_sub f (mollN n f), mollN_ae n f] with x h1 h2
        rw [h1, Pi.sub_apply, h2]
      have i1 := integrable_aQ_weight T y₀ hδ (Lp.memLp f)
      have i2 := integrable_aQ_weight T y₀ hδ hm
      have i3 : Integrable fun x => ‖f x - moll (rhoN n) f x‖ ^ 2 :=
        (integrable_sq_L2 (f - mollN n f)).congr (hdiff.mono fun x hx => by simp only [hx])
      have hpt : ∀ x, ‖f x‖ ^ 2 * (aQ T y₀ δ x)⁻¹ ≤
          (1 + l) * (‖moll (rhoN n) f x‖ ^ 2 * (aQ T y₀ δ x)⁻¹) +
          (1 + 1 / l) * (1 / δ ^ 2) * ‖f x - moll (rhoN n) f x‖ ^ 2 := fun x => by
        have e1 := sq_norm_le_split (f x) (moll (rhoN n) f x) hl
        have w0 : 0 ≤ (aQ T y₀ δ x)⁻¹ := (inv_pos.mpr (aQ_pos T y₀ hδ x)).le
        have w1 : (aQ T y₀ δ x)⁻¹ ≤ 1 / δ ^ 2 := by
          have := norm_aQ_inv_le T y₀ hδ x
          rwa [Real.norm_eq_abs, abs_of_nonneg w0] at this
        have e2 := mul_le_mul_of_nonneg_right e1 w0
        have e3 : ‖f x - moll (rhoN n) f x‖ ^ 2 * (aQ T y₀ δ x)⁻¹ ≤
            ‖f x - moll (rhoN n) f x‖ ^ 2 * (1 / δ ^ 2) :=
          mul_le_mul_of_nonneg_left w1 (sq_nonneg _)
        have hl1 : 0 ≤ 1 + 1 / l := by positivity
        nlinarith [mul_le_mul_of_nonneg_left e3 hl1]
      calc ∫ x, ‖f x‖ ^ 2 * (aQ T y₀ δ x)⁻¹
          ≤ ∫ x, ((1 + l) * (‖moll (rhoN n) f x‖ ^ 2 * (aQ T y₀ δ x)⁻¹) +
            (1 + 1 / l) * (1 / δ ^ 2) * ‖f x - moll (rhoN n) f x‖ ^ 2) :=
            integral_mono i1 ((i2.const_mul _).add (i3.const_mul _)) hpt
        _ = (1 + l) * (∫ x, ‖moll (rhoN n) f x‖ ^ 2 * (aQ T y₀ δ x)⁻¹) +
            (1 + 1 / l) * (1 / δ ^ 2) * ‖f - mollN n f‖ ^ 2 := by
            rw [integral_add (i2.const_mul _) (i3.const_mul _), integral_const_mul,
              integral_const_mul, norm_sq_eq_of_ae hdiff]
        _ ≤ (1 + l) * (4 * G) + (1 + 1 / l) * (1 / δ ^ 2) * ‖f - mollN n f‖ ^ 2 := by
            gcongr
            exact hsm n
    have h0 : Tendsto (fun n : ℕ => ‖f - mollN n f‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_mollN f)).congr fun n => norm_sub_rev _ _
    have ht := (tendsto_const_nhds (x := (1 + l) * (4 * G))).add
      ((tendsto_const_nhds (x := (1 + 1 / l) * (1 / δ ^ 2))).mul (h0.pow 2))
    have e : (1 + l) * (4 * G) + (1 + 1 / l) * (1 / δ ^ 2) * (0 : ℝ) ^ 2 =
        (1 + l) * (4 * G) := by ring
    rw [e] at ht
    exact ge_of_tendsto' ht hb
  refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
  have hl : 0 < ε / (4 * G + 1) := by positivity
  have h1 := hlam _ hl
  have h2 : ε / (4 * G + 1) * (4 * G) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

end Hardy

section Quotient

variable (T : Rcfg eta →L[ℝ] E3) (y₀ : E3) {i : Fin eta}
  (hT : ∀ c, T (Pi.single (i, c) 1) = EuclideanSpace.single c 1)
include hT

/-- **Hardy's inequality** for an affine map `Y = T x - y₀` with `T e_{(i,c)} = e_c` and `Y ≠ 0`
almost everywhere: `f / |Y| ∈ L²` and `‖f / |Y|‖² ≤ 4 Σ_c ‖∂_{(i,c)} f‖²`. -/
theorem hardy_weak_aff (hnull : ∀ᵐ x : Rcfg eta, T x - y₀ ≠ 0) {f : FreeL2 eta}
    {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad f g) :
    ∃ Y : FreeL2 eta, (∀ᵐ x, Y x = ((‖T x - y₀‖⁻¹ : ℝ) : ℂ) * f x) ∧
      ‖Y‖ ^ 2 ≤ 4 * ∑ c : Fin 3, ‖g (i, c)‖ ^ 2 := by
  set φ : Rcfg eta → ℂ := fun x => ((‖T x - y₀‖⁻¹ : ℝ) : ℂ) * f x with hφ
  have hmeas : Measurable fun x => ‖T x - y₀‖⁻¹ :=
    ((T.continuous.sub continuous_const).measurable.norm).inv
  have hφm : AEStronglyMeasurable φ volume :=
    ((Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable).mul (Lp.aestronglyMeasurable f)
  have hφn : ∀ x, ‖φ x‖ ^ 2 = ‖f x‖ ^ 2 * (‖T x - y₀‖ ^ 2)⁻¹ := fun x => by
    show ‖((‖T x - y₀‖⁻¹ : ℝ) : ℂ) * f x‖ ^ 2 = _
    rw [norm_mul, Complex.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    ring
  have hδp : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hmeask : ∀ k : ℕ, AEMeasurable
      (fun x => ENNReal.ofReal (‖f x‖ ^ 2 * (aQ T y₀ (1 / ((k : ℝ) + 1)) x)⁻¹)) volume :=
    fun k => (integrable_aQ_weight T y₀ (hδp k) (Lp.memLp f)).aemeasurable.ennreal_ofReal
  have hmono : ∀ᵐ x ∂volume, Monotone fun k : ℕ =>
      ENNReal.ofReal (‖f x‖ ^ 2 * (aQ T y₀ (1 / ((k : ℝ) + 1)) x)⁻¹) :=
    ae_of_all _ fun x k k' hkk => by
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
      refine inv_anti₀ (aQ_pos T y₀ (hδp k') x) ?_
      have hle : 1 / ((k' : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity)
          (by have := (Nat.cast_le (α := ℝ)).mpr hkk; linarith)
      have h2 := pow_le_pow_left₀ (hδp k').le hle 2
      unfold aQ
      linarith
  have htend : ∀ᵐ x ∂volume, Tendsto (fun k : ℕ =>
      ENNReal.ofReal (‖f x‖ ^ 2 * (aQ T y₀ (1 / ((k : ℝ) + 1)) x)⁻¹)) atTop
      (𝓝 (ENNReal.ofReal (‖φ x‖ ^ 2))) := by
    filter_upwards [hnull] with x hy
    have h1 : Tendsto (fun k : ℕ => aQ T y₀ (1 / ((k : ℝ) + 1)) x) atTop
        (𝓝 (‖T x - y₀‖ ^ 2)) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2 |>.const_add
        (‖T x - y₀‖ ^ 2)
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero] at this
      exact this
    have h2 := (h1.inv₀ (pow_pos (norm_pos_iff.mpr hy) 2).ne').const_mul (‖f x‖ ^ 2)
    rw [hφn x]
    exact (ENNReal.continuous_ofReal.tendsto _).comp h2
  have hlim := lintegral_tendsto_of_tendsto_of_monotone hmeask hmono htend
  have hbd : ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * (aQ T y₀ (1 / ((k : ℝ) + 1)) x)⁻¹) ≤
      ENNReal.ofReal (4 * ∑ c : Fin 3, ‖g (i, c)‖ ^ 2) := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_aQ_weight T y₀ (hδp k) (Lp.memLp f))
      (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (inv_pos.mpr (aQ_pos T y₀ (hδp k) x)).le)]
    exact ENNReal.ofReal_le_ofReal (hardy_delta_aff T y₀ hT (hδp k) hg)
  have hF : ∫⁻ x, ENNReal.ofReal (‖φ x‖ ^ 2) ≤
      ENNReal.ofReal (4 * ∑ c : Fin 3, ‖g (i, c)‖ ^ 2) := le_of_tendsto' hlim hbd
  have hint : Integrable (fun x => ‖φ x‖ ^ 2) := by
    refine ⟨hφm.norm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)]
    exact hF.trans_lt ENNReal.ofReal_lt_top
  have hmem : MemLp φ 2 volume := (memLp_two_iff_integrable_sq_norm hφm).mpr hint
  refine ⟨hmem.toLp φ, hmem.coeFn_toLp, ?_⟩
  rw [norm_sq_eq_of_ae hmem.coeFn_toLp,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _) hint.1]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun c _ => sq_nonneg _)) hF

end Quotient

/-! ## The nuclear terms -/

section Nuclear

lemma particleCLM_single (i : Fin eta) (c : Fin 3) :
    particleCLM i (Pi.single (i, c) 1) = EuclideanSpace.single c 1 := by
  rw [particleCLM_apply, particle_single, if_pos rfl]

/-- A particle is almost nowhere at a given point. -/
lemma volume_particle_eq (i : Fin eta) (y : E3) :
    volume {r : Rcfg eta | particle r i = y} = 0 := by
  let ℓ : Rcfg eta →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin eta × Fin 3 => ℝ) (i, (0 : Fin 3))
  let x₀ : Rcfg eta := Pi.single (i, (0 : Fin 3)) (y 0)
  have hsub : {r : Rcfg eta | particle r i = y} ⊆
      (fun r => r + (-x₀)) ⁻¹' (LinearMap.ker ℓ : Set (Rcfg eta)) := by
    intro r hr
    have h0 : (particle r i) 0 = y 0 := by rw [show particle r i = y from hr]
    simp only [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker]
    simp only [particle] at h0
    simp [ℓ, x₀, h0]
  have hne : LinearMap.ker ℓ ≠ ⊤ := by
    intro h
    have hmem : (Pi.single (i, (0 : Fin 3)) (1 : ℝ) : Rcfg eta) ∈ LinearMap.ker ℓ := by
      rw [h]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker] at hmem
    simp [ℓ] at hmem
  have h0 : volume ((fun r => r + (-x₀)) ⁻¹' (LinearMap.ker ℓ : Set (Rcfg eta))) = 0 := by
    rw [measure_preimage_add_right]
    exact Measure.addHaar_submodule volume _ hne
  exact measure_mono_null hsub h0

lemma ae_particle_ne (i : Fin eta) (y : E3) : ∀ᵐ r : Rcfg eta, particleCLM i r - y ≠ 0 := by
  have h := measure_eq_zero_iff_ae_notMem.mp (volume_particle_eq i y)
  filter_upwards [h] with r hr
  intro he
  exact hr (sub_eq_zero.mp he)

/-- **Hardy's inequality for a nuclear term**: `f / |x_i - R| ∈ L²` with
`‖f / |x_i - R|‖² ≤ 4 Σ_c ‖∂_{(i,c)} f‖²`. -/
theorem hardy_nuc (i : Fin eta) (R : E3) {f : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad f g) :
    ∃ Y : FreeL2 eta, (∀ᵐ x, Y x = ((‖particle x i - R‖⁻¹ : ℝ) : ℂ) * f x) ∧
      ‖Y‖ ^ 2 ≤ 4 * ∑ c : Fin 3, ‖g (i, c)‖ ^ 2 :=
  hardy_weak_aff (particleCLM i) R (particleCLM_single i) (ae_particle_ne i R) hg

end Nuclear

end FreeBoundary
