import PlaneWave.FreeBoundary.KineticRegularity

/-!
# Free-space regularity, part 3: Hardy's inequality

**Hardy's inequality for a pair**: if `f ∈ L²(ℝ^{3η})` has weak gradient `g`, then
`f/|x_i - x_j| ∈ L²` with `‖f/|x_i - x_j|‖² ≤ 4 Σ_c ‖∂_{(i,c)} f‖²`. No symmetry or collision
condition is needed.

For smooth `F` with `F`, `∂F` in `L²` the proof uses the vector field
`V_δ = (x_i - x_j)/(|x_i - x_j|² + δ²)` in the coordinates of particle `i`: `div_i V_δ ≥ w_δ`,
`|V_δ|² ≤ w_δ`, `w_δ = 1/(|x_i - x_j|² + δ²)`, and integration by parts gives
`∫ |F|² w_δ ≤ ∫ |F|² div_i V_δ = -2 Re ∫ conj(F) V_δ · ∇_i F ≤ (1/2) ∫ |F|² w_δ + 2 ‖∇_i F‖²`.
Mollification passes to `f` with weak gradient, and `δ → 0` (monotone convergence) gives the
quotient.

* `hQ`, `hV`, `dirD_hV`, `sum_dirD_hV_ge`, `sum_hV_sq_le`: the vector field;
* `hardy_smooth`: the smooth inequality at `δ > 0`;
* `hardy_delta`: the inequality at `δ > 0` for a weak gradient;
* **`hardy_weak`**: the Hardy quotient `Y = f/|x_i - x_j|` as an element of `L²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology Convolution Pointwise ENNReal
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

variable {eta : ℕ}

/-! ## The vector field -/

section Field

variable (p : FiniteElectronPair eta)

/-- `Q_δ = |x_i - x_j|² + δ²`. -/
noncomputable def hQ (δ : ℝ) (x : Rcfg eta) : ℝ := ‖pairY p x‖ ^ 2 + δ ^ 2

/-- The vector field `V_{δ,c} = (x_i - x_j)_c / Q_δ`. -/
noncomputable def hV (δ : ℝ) (c : Fin 3) (x : Rcfg eta) : ℝ := pairY p x c * (hQ p δ x)⁻¹

variable {δ : ℝ} (hδ : 0 < δ)
include hδ

lemma hQ_pos (x : Rcfg eta) : 0 < hQ p δ x := by
  unfold hQ
  positivity

lemma hQ_ge (x : Rcfg eta) : δ ^ 2 ≤ hQ p δ x := by
  unfold hQ
  nlinarith [sq_nonneg ‖pairY p x‖]

omit hδ in
lemma norm_sq_pairY (x : Rcfg eta) : ‖pairY p x‖ ^ 2 = ∑ c : Fin 3, (pairY p x c) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

omit hδ in
lemma pairY_single_self (c : Fin 3) :
    pairY p (Pi.single (p.1.1, c) 1) = EuclideanSpace.single c 1 := by
  have hij : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  rw [pairY_apply, particle_single, particle_single, if_pos rfl, if_neg hij, sub_zero]

omit hδ in
lemma dirD_pairY_comp (c d : Fin 3) (x : Rcfg eta) :
    dirD (p.1.1, c) (fun y => pairY p y d) x = if c = d then 1 else 0 := by
  have h : HasFDerivAt (fun y => pairY p y d)
      ((EuclideanSpace.proj d : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).comp (pairY p)) x :=
    ((EuclideanSpace.proj d : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).comp (pairY p)).hasFDerivAt
  unfold dirD
  rw [h.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, pairY_single_self]
  by_cases hcd : c = d
  · subst hcd
    simp
  · simp [hcd, Ne.symm hcd]

omit hδ in
lemma dirD_hQ (c : Fin 3) (x : Rcfg eta) : dirD (p.1.1, c) (hQ p δ) x = 2 * pairY p x c := by
  have h : HasFDerivAt (hQ p δ) (2 • (innerSL ℝ (pairY p x)).comp (pairY p)) x :=
    ((pairY p).hasFDerivAt.norm_sq).add_const _
  unfold dirD
  rw [h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, innerSL_apply_apply, pairY_single_self]
  rw [EuclideanSpace.inner_single_right]
  simp

omit hδ in
lemma differentiable_hQ : Differentiable ℝ (hQ p δ) := fun _ =>
  (((pairY p).hasFDerivAt.norm_sq).add_const (δ ^ 2)).differentiableAt

omit hδ in
lemma continuous_hQ : Continuous (hQ p δ) := (differentiable_hQ p).continuous

/-- `∂_{(i,c)} V_c = Q⁻¹ - 2 y_c² Q⁻²`. -/
lemma dirD_hV (c : Fin 3) (x : Rcfg eta) :
    dirD (p.1.1, c) (hV p δ c) x = (hQ p δ x)⁻¹ - 2 * (pairY p x c) ^ 2 * ((hQ p δ x)⁻¹) ^ 2 := by
  have hyd : DifferentiableAt ℝ (fun y => pairY p y c) x :=
    ((EuclideanSpace.proj c : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).comp (pairY p)).differentiableAt
  have hQd : DifferentiableAt ℝ (fun y => (hQ p δ y)⁻¹) x :=
    (differentiable_hQ p x).inv (hQ_pos p hδ x).ne'
  have hinv : dirD (p.1.1, c) (fun y => (hQ p δ y)⁻¹) x =
      -((hQ p δ x ^ 2)⁻¹ * dirD (p.1.1, c) (hQ p δ) x) := by
    have h : HasFDerivAt (fun y => (hQ p δ y)⁻¹)
        ((-((hQ p δ x) ^ 2)⁻¹) • fderiv ℝ (hQ p δ) x) x :=
      (hasDerivAt_inv (hQ_pos p hδ x).ne').comp_hasFDerivAt x
        (differentiable_hQ p x).hasFDerivAt
    unfold dirD
    rw [h.fderiv]
    simp
  unfold hV
  rw [dirD_mul_real hyd hQd, dirD_pairY_comp, if_pos rfl, hinv, dirD_hQ]
  ring

lemma continuous_dirD_hV (c : Fin 3) : Continuous (dirD (p.1.1, c) (hV p δ c)) := by
  have e : dirD (p.1.1, c) (hV p δ c) = fun x =>
      (hQ p δ x)⁻¹ - 2 * (pairY p x c) ^ 2 * ((hQ p δ x)⁻¹) ^ 2 :=
    funext fun x => dirD_hV p hδ c x
  rw [e]
  have hQi : Continuous fun x => (hQ p δ x)⁻¹ :=
    (continuous_hQ p).inv₀ fun x => (hQ_pos p hδ x).ne'
  have hy : Continuous fun x => pairY p x c :=
    ((EuclideanSpace.proj c : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).comp (pairY p)).continuous
  exact hQi.sub ((continuous_const.mul (hy.pow 2)).mul (hQi.pow 2))

lemma continuous_hV (c : Fin 3) : Continuous (hV p δ c) := by
  have hQi : Continuous fun x => (hQ p δ x)⁻¹ :=
    (continuous_hQ p).inv₀ fun x => (hQ_pos p hδ x).ne'
  have hy : Continuous fun x => pairY p x c :=
    ((EuclideanSpace.proj c : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).comp (pairY p)).continuous
  exact hy.mul hQi

lemma differentiable_hV (c : Fin 3) : Differentiable ℝ (hV p δ c) := fun x =>
  (((EuclideanSpace.proj c : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).comp
    (pairY p)).differentiableAt).mul ((differentiable_hQ p x).inv (hQ_pos p hδ x).ne')

/-- `div_i V ≥ Q⁻¹`. -/
lemma sum_dirD_hV_ge (x : Rcfg eta) :
    (hQ p δ x)⁻¹ ≤ ∑ c : Fin 3, dirD (p.1.1, c) (hV p δ c) x := by
  simp_rw [dirD_hV p hδ]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← norm_sq_pairY]
  have hQp := hQ_pos p hδ x
  have hy : ‖pairY p x‖ ^ 2 ≤ hQ p δ x := by
    unfold hQ
    nlinarith [sq_nonneg δ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e : 2 * ‖pairY p x‖ ^ 2 * (hQ p δ x)⁻¹ ^ 2 ≤ 2 * (hQ p δ x)⁻¹ := by
    have : ‖pairY p x‖ ^ 2 * (hQ p δ x)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hQp]
      exact hy
    have h2 : 0 ≤ (hQ p δ x)⁻¹ := (inv_pos.mpr hQp).le
    nlinarith
  push_cast
  linarith

/-- `|V|² ≤ Q⁻¹`. -/
lemma sum_hV_sq_le (x : Rcfg eta) : ∑ c : Fin 3, hV p δ c x ^ 2 ≤ (hQ p δ x)⁻¹ := by
  unfold hV
  simp_rw [mul_pow]
  rw [← Finset.sum_mul, ← norm_sq_pairY]
  have hQp := hQ_pos p hδ x
  have hy : ‖pairY p x‖ ^ 2 ≤ hQ p δ x := by
    unfold hQ
    nlinarith [sq_nonneg δ]
  rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  have : (hQ p δ x)⁻¹ * hQ p δ x ^ 2 = hQ p δ x := by field_simp
  rw [this]
  exact hy

lemma abs_hV_le (c : Fin 3) (x : Rcfg eta) : |hV p δ c x| ≤ 1 / δ := by
  unfold hV
  have hQp := hQ_pos p hδ x
  have h1 : |pairY p x c| ≤ ‖pairY p x‖ := by
    have := norm_sq_pairY p x
    have h2 : (pairY p x c) ^ 2 ≤ ‖pairY p x‖ ^ 2 := by
      rw [this]
      exact Finset.single_le_sum (f := fun d => (pairY p x d) ^ 2) (fun d _ => sq_nonneg _)
        (Finset.mem_univ c)
    exact abs_le_of_sq_le_sq' h2 (norm_nonneg _) |> fun h => abs_le.mpr ⟨h.1, h.2⟩
  have h3 : ‖pairY p x‖ * δ ≤ hQ p δ x := by
    unfold hQ
    nlinarith [sq_nonneg (‖pairY p x‖ - δ)]
  rw [abs_mul, abs_inv, abs_of_pos hQp, ← div_eq_mul_inv, div_le_div_iff₀ hQp hδ]
  nlinarith [abs_nonneg (pairY p x c)]

lemma abs_dirD_hV_le (c : Fin 3) (x : Rcfg eta) :
    |dirD (p.1.1, c) (hV p δ c) x| ≤ 3 / δ ^ 2 := by
  rw [dirD_hV p hδ]
  have hQp := hQ_pos p hδ x
  have hQg := hQ_ge p hδ x
  have hyc : (pairY p x c) ^ 2 ≤ hQ p δ x := by
    have := norm_sq_pairY p x
    have h2 : (pairY p x c) ^ 2 ≤ ‖pairY p x‖ ^ 2 := by
      rw [this]
      exact Finset.single_le_sum (f := fun d => (pairY p x d) ^ 2) (fun d _ => sq_nonneg _)
        (Finset.mem_univ c)
    unfold hQ at *
    nlinarith [sq_nonneg δ]
  have hi : (hQ p δ x)⁻¹ ≤ 1 / δ ^ 2 := by
    rw [one_div]
    exact inv_anti₀ (by positivity) hQg
  have hi0 : 0 ≤ (hQ p δ x)⁻¹ := (inv_pos.mpr hQp).le
  have h2 : 2 * (pairY p x c) ^ 2 * ((hQ p δ x)⁻¹) ^ 2 ≤ 2 * (hQ p δ x)⁻¹ := by
    have : (pairY p x c) ^ 2 * (hQ p δ x)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hQp]
      exact hyc
    nlinarith
  have h3 : 0 ≤ 2 * (pairY p x c) ^ 2 * ((hQ p δ x)⁻¹) ^ 2 := by positivity
  have h4 : 3 / δ ^ 2 = 3 * (1 / δ ^ 2) := by ring
  have h5 : 0 ≤ 1 / δ ^ 2 := by positivity
  rw [abs_le, h4]
  constructor <;> linarith

end Field

/-! ## The smooth inequality -/

section Smooth

variable (p : FiniteElectronPair eta) {δ : ℝ} (hδ : 0 < δ)
include hδ

/-- **Hardy's inequality at `δ > 0`** for a `C¹` function `F` with `F`, `∇_i F ∈ L²`:
`∫ |F|² / (|x_i - x_j|² + δ²) ≤ 4 Σ_c ‖∂_{(i,c)} F‖²`. -/
lemma hardy_smooth {F : Rcfg eta → ℂ} (hF : ContDiff ℝ 1 F) (h0 : MemLp F 2 volume)
    (h1 : ∀ c : Fin 3, MemLp (dirD (p.1.1, c) F) 2 volume) :
    ∫ x, ‖F x‖ ^ 2 * (hQ p δ x)⁻¹ ≤ 4 * ∑ c : Fin 3, ∫ x, ‖dirD (p.1.1, c) F x‖ ^ 2 := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hFc : Continuous F := hF.continuous
  have hdFc : ∀ c : Fin 3, Continuous (dirD (p.1.1, c) F) := fun c =>
    continuous_dirD hF (by norm_num) _
  have hN : Integrable (fun x => ‖F x‖ ^ 2) := (memLp_two_iff_integrable_sq_norm h0.1).mp h0
  have hD : ∀ c : Fin 3, Integrable (fun x => ‖dirD (p.1.1, c) F x‖ ^ 2) := fun c =>
    (memLp_two_iff_integrable_sq_norm (h1 c).1).mp (h1 c)
  -- the derivative of `N = |F|²`
  have hNd : ∀ x, HasFDerivAt (fun y => ‖F y‖ ^ 2)
      (2 • (innerSL ℝ (F x)).comp (fderiv ℝ F x)) x := fun x =>
    (hFd x).hasFDerivAt.norm_sq
  have hdN : ∀ (c : Fin 3) x, dirD (p.1.1, c) (fun y => ‖F y‖ ^ 2) x =
      2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ := by
    intro c x
    unfold dirD
    rw [(hNd x).fderiv]
    simp
    ring
  have hQi : Continuous fun x => (hQ p δ x)⁻¹ :=
    (continuous_hQ p).inv₀ fun x => (hQ_pos p hδ x).ne'
  have hwb : ∀ x, ‖(hQ p δ x)⁻¹‖ ≤ 1 / δ ^ 2 := fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hQ_pos p hδ x)), one_div]
    exact inv_anti₀ (by positivity) (hQ_ge p hδ x)
  have hI : Integrable (fun x => ‖F x‖ ^ 2 * (hQ p δ x)⁻¹) :=
    hN.mul_bdd hQi.aestronglyMeasurable (ae_of_all _ hwb)
  -- integration by parts for each `c`
  have hibp : ∀ c : Fin 3, ∫ x, ‖F x‖ ^ 2 * dirD (p.1.1, c) (hV p δ c) x =
      -∫ x, 2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ * hV p δ c x := by
    intro c
    have hVb : ∀ x, ‖hV p δ c x‖ ≤ 1 / δ := fun x => by
      rw [Real.norm_eq_abs]
      exact abs_hV_le p hδ c x
    have hdVb : ∀ x, ‖dirD (p.1.1, c) (hV p δ c) x‖ ≤ 3 / δ ^ 2 := fun x => by
      rw [Real.norm_eq_abs]
      exact abs_dirD_hV_le p hδ c x
    have i1 : Integrable fun x => 2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ * hV p δ c x := by
      refine (((h0.norm.integrable_mul (h1 c).norm).const_mul (2 / δ))).mono'
        (((continuous_const.mul (hFc.inner (hdFc c))).mul
          (continuous_hV p hδ c)).aestronglyMeasurable)
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
      have e1 := abs_real_inner_le_norm (F x) (dirD (p.1.1, c) F x)
      have e2 := abs_hV_le p hδ c x
      have e3 : 0 ≤ |⟪F x, dirD (p.1.1, c) F x⟫_ℝ| := abs_nonneg _
      calc 2 * |⟪F x, dirD (p.1.1, c) F x⟫_ℝ| * |hV p δ c x|
          ≤ 2 * (‖F x‖ * ‖dirD (p.1.1, c) F x‖) * (1 / δ) := by gcongr
        _ = 2 / δ * (‖F x‖ * ‖dirD (p.1.1, c) F x‖) := by ring
    have i2 : Integrable fun x => ‖F x‖ ^ 2 * dirD (p.1.1, c) (hV p δ c) x :=
      hN.mul_bdd (continuous_dirD_hV p hδ c).aestronglyMeasurable (ae_of_all _ hdVb)
    have i3 : Integrable fun x => ‖F x‖ ^ 2 * hV p δ c x :=
      hN.mul_bdd (continuous_hV p hδ c).aestronglyMeasurable (ae_of_all _ hVb)
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (𝕜 := ℝ)
      (f := fun y => ‖F y‖ ^ 2) (g := hV p δ c) (v := Pi.single (p.1.1, c) 1)
      (i1.congr (ae_of_all _ fun x => by
        show 2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ * hV p δ c x =
          dirD (p.1.1, c) (fun y => ‖F y‖ ^ 2) x * hV p δ c x
        rw [hdN c x])) i2 i3 (fun x _ => (hNd x).differentiableAt)
      (fun x _ => differentiable_hV p hδ c x)
    have e : ∀ x, fderiv ℝ (fun y => ‖F y‖ ^ 2) x (Pi.single (p.1.1, c) 1) =
        2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ := fun x => hdN c x
    simp_rw [e] at h
    exact h
  -- the pointwise inequalities
  have hpt1 : ∀ x, ‖F x‖ ^ 2 * (hQ p δ x)⁻¹ ≤
      ∑ c : Fin 3, ‖F x‖ ^ 2 * dirD (p.1.1, c) (hV p δ c) x := fun x => by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_dirD_hV_ge p hδ x) (sq_nonneg _)
  have hpt2 : ∀ x, ∑ c : Fin 3, -(2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ * hV p δ c x) ≤
      (1 / 2) * (‖F x‖ ^ 2 * (hQ p δ x)⁻¹) +
        2 * ∑ c : Fin 3, ‖dirD (p.1.1, c) F x‖ ^ 2 := fun x => by
    have hc : ∀ c : Fin 3, -(2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ * hV p δ c x) ≤
        (1 / 2) * (‖F x‖ ^ 2 * hV p δ c x ^ 2) + 2 * ‖dirD (p.1.1, c) F x‖ ^ 2 := by
      intro c
      have e1 := abs_real_inner_le_norm (F x) (dirD (p.1.1, c) F x)
      have e2 : -(2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ * hV p δ c x) ≤
          2 * (‖F x‖ * ‖dirD (p.1.1, c) F x‖) * |hV p δ c x| := by
        have := neg_abs_le (2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ * hV p δ c x)
        rw [abs_mul, abs_mul, abs_two] at this
        have h3 : 2 * |⟪F x, dirD (p.1.1, c) F x⟫_ℝ| * |hV p δ c x| ≤
            2 * (‖F x‖ * ‖dirD (p.1.1, c) F x‖) * |hV p δ c x| := by gcongr
        linarith
      have e3 : 2 * (‖F x‖ * ‖dirD (p.1.1, c) F x‖) * |hV p δ c x| ≤
          (1 / 2) * (‖F x‖ ^ 2 * hV p δ c x ^ 2) + 2 * ‖dirD (p.1.1, c) F x‖ ^ 2 := by
        nlinarith [sq_nonneg (‖F x‖ * |hV p δ c x| - 2 * ‖dirD (p.1.1, c) F x‖),
          sq_abs (hV p δ c x)]
      linarith
    have hs := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hc c
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    have hV2 := sum_hV_sq_le p hδ x
    have : (1 / 2) * (‖F x‖ ^ 2 * ∑ c : Fin 3, hV p δ c x ^ 2) ≤
        (1 / 2) * (‖F x‖ ^ 2 * (hQ p δ x)⁻¹) := by
      have := mul_le_mul_of_nonneg_left hV2 (sq_nonneg ‖F x‖)
      linarith
    linarith
  -- integrate
  have hint1 : ∀ c : Fin 3, Integrable fun x => ‖F x‖ ^ 2 * dirD (p.1.1, c) (hV p δ c) x :=
    fun c => hN.mul_bdd (continuous_dirD_hV p hδ c).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_dirD_hV_le p hδ c x)
  have hint2 : ∀ c : Fin 3, Integrable fun x => -(2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ *
      hV p δ c x) := by
    intro c
    refine Integrable.neg ?_
    refine (((h0.norm.integrable_mul (h1 c).norm).const_mul (2 / δ))).mono'
      (((continuous_const.mul (hFc.inner (hdFc c))).mul
        (continuous_hV p hδ c)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
    have e1 := abs_real_inner_le_norm (F x) (dirD (p.1.1, c) F x)
    have e2 := abs_hV_le p hδ c x
    calc 2 * |⟪F x, dirD (p.1.1, c) F x⟫_ℝ| * |hV p δ c x|
        ≤ 2 * (‖F x‖ * ‖dirD (p.1.1, c) F x‖) * (1 / δ) := by gcongr
      _ = 2 / δ * (‖F x‖ * ‖dirD (p.1.1, c) F x‖) := by ring
  set I := ∫ x, ‖F x‖ ^ 2 * (hQ p δ x)⁻¹ with hIdef
  set G := ∑ c : Fin 3, ∫ x, ‖dirD (p.1.1, c) F x‖ ^ 2 with hGdef
  have step1 : I ≤ ∑ c : Fin 3, ∫ x, ‖F x‖ ^ 2 * dirD (p.1.1, c) (hV p δ c) x := by
    rw [← integral_finsetSum _ fun c _ => hint1 c]
    exact integral_mono hI (integrable_finsetSum _ fun c _ => hint1 c) hpt1
  have step2 : ∑ c : Fin 3, ∫ x, ‖F x‖ ^ 2 * dirD (p.1.1, c) (hV p δ c) x =
      ∫ x, ∑ c : Fin 3, -(2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ * hV p δ c x) := by
    rw [integral_finsetSum _ fun c _ => hint2 c]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hibp c, integral_neg]
  have step3 : ∫ x, ∑ c : Fin 3, -(2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ * hV p δ c x) ≤
      (1 / 2) * I + 2 * G := by
    have hR : Integrable fun x => (1 / 2) * (‖F x‖ ^ 2 * (hQ p δ x)⁻¹) +
        2 * ∑ c : Fin 3, ‖dirD (p.1.1, c) F x‖ ^ 2 :=
      (hI.const_mul _).add ((integrable_finsetSum _ fun c _ => hD c).const_mul _)
    calc ∫ x, ∑ c : Fin 3, -(2 * ⟪F x, dirD (p.1.1, c) F x⟫_ℝ * hV p δ c x)
        ≤ ∫ x, ((1 / 2) * (‖F x‖ ^ 2 * (hQ p δ x)⁻¹) +
            2 * ∑ c : Fin 3, ‖dirD (p.1.1, c) F x‖ ^ 2) :=
          integral_mono (integrable_finsetSum _ fun c _ => hint2 c) hR hpt2
      _ = (1 / 2) * I + 2 * G := by
          rw [integral_add (hI.const_mul _)
              ((integrable_finsetSum _ fun c _ => hD c).const_mul _),
            integral_const_mul, integral_const_mul, integral_finsetSum _ fun c _ => hD c]
  linarith

end Smooth

/-! ## Weak gradients -/

section Weak

variable (p : FiniteElectronPair eta)

/-- `|a|² ≤ (1 + λ)|b|² + (1 + 1/λ)|a - b|²`. -/
lemma sq_norm_le_split (a b : ℂ) {l : ℝ} (hl : 0 < l) :
    ‖a‖ ^ 2 ≤ (1 + l) * ‖b‖ ^ 2 + (1 + 1 / l) * ‖a - b‖ ^ 2 := by
  have h1 : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
    calc ‖a‖ = ‖b + (a - b)‖ := by congr 1; ring
      _ ≤ ‖b‖ + ‖a - b‖ := norm_add_le _ _
  have hl0 : l ≠ 0 := hl.ne'
  have h2 : 2 * ‖b‖ * ‖a - b‖ ≤ l * ‖b‖ ^ 2 + 1 / l * ‖a - b‖ ^ 2 := by
    have e : l * ‖b‖ ^ 2 + 1 / l * ‖a - b‖ ^ 2 - 2 * ‖b‖ * ‖a - b‖ =
        (l * ‖b‖ - ‖a - b‖) ^ 2 / l := by
      field_simp
      ring
    have : 0 ≤ (l * ‖b‖ - ‖a - b‖) ^ 2 / l := by positivity
    linarith
  have h3 : ‖a‖ ^ 2 ≤ (‖b‖ + ‖a - b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [h2, h3]

lemma measurable_pinv : Measurable (pinv p) :=
  ((pairY p).continuous.measurable.norm).inv

variable {δ : ℝ} (hδ : 0 < δ)
include hδ

lemma norm_hQ_inv_le (x : Rcfg eta) : ‖(hQ p δ x)⁻¹‖ ≤ 1 / δ ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hQ_pos p hδ x)), one_div]
  exact inv_anti₀ (by positivity) (hQ_ge p hδ x)

lemma integrable_hardy_weight {F : Rcfg eta → ℂ} (hF : MemLp F 2 volume) :
    Integrable (fun x => ‖F x‖ ^ 2 * (hQ p δ x)⁻¹) := by
  have hN : Integrable (fun x => ‖F x‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hF.1).mp hF
  have hQi : Continuous fun x => (hQ p δ x)⁻¹ :=
    (continuous_hQ p).inv₀ fun x => (hQ_pos p hδ x).ne'
  exact hN.mul_bdd hQi.aestronglyMeasurable (ae_of_all _ (norm_hQ_inv_le p hδ))

/-- **Hardy's inequality at `δ > 0`** for `f ∈ L²` with a weak gradient. -/
lemma hardy_delta {f : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad f g) :
    ∫ x, ‖f x‖ ^ 2 * (hQ p δ x)⁻¹ ≤ 4 * ∑ c : Fin 3, ‖g (p.1.1, c)‖ ^ 2 := by
  set G := ∑ c : Fin 3, ‖g (p.1.1, c)‖ ^ 2 with hGdef
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun c _ => sq_nonneg _
  -- the mollified functions
  have hsm : ∀ n : ℕ, ∫ x, ‖moll (rhoN n) f x‖ ^ 2 * (hQ p δ x)⁻¹ ≤ 4 * G := by
    intro n
    rw [hGdef]
    have hc := hasCompactSupport_rhoN (eta := eta) n
    have hF : ContDiff ℝ 1 (moll (rhoN n) f) :=
      contDiff_moll hc (contDiff_rhoN n) (locInt_L2 f)
    have hd : ∀ c : Fin 3, dirD (p.1.1, c) (moll (rhoN n) f) = moll (rhoN n) (g (p.1.1, c)) :=
      fun c => by
        rw [dirD_moll hc (contDiff_rhoN n) (locInt_L2 f)]
        funext x
        exact moll_dirD_eq hg hc (contDiff_rhoN n) _ x
    have h := hardy_smooth p hδ hF (memLp_moll hc (continuous_rhoN n) f).1
      (fun c => by rw [hd c]; exact (memLp_moll hc (continuous_rhoN n) _).1)
    refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) (by norm_num))
    rw [hd c, ← norm_sq_eq_of_ae (mollN_ae n _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_mollN_le n _) 2
  -- the approximation, with a loss `1 + λ`
  have hlam : ∀ l : ℝ, 0 < l → ∫ x, ‖f x‖ ^ 2 * (hQ p δ x)⁻¹ ≤ (1 + l) * (4 * G) := by
    intro l hl
    have hb : ∀ n : ℕ, ∫ x, ‖f x‖ ^ 2 * (hQ p δ x)⁻¹ ≤
        (1 + l) * (4 * G) + (1 + 1 / l) * (1 / δ ^ 2) * ‖f - mollN n f‖ ^ 2 := by
      intro n
      have hc := hasCompactSupport_rhoN (eta := eta) n
      have hm := (memLp_moll hc (continuous_rhoN n) f).1
      have hdiff : (⇑(f - mollN n f) : Rcfg eta → ℂ) =ᵐ[volume]
          fun x => f x - moll (rhoN n) f x := by
        filter_upwards [Lp.coeFn_sub f (mollN n f), mollN_ae n f] with x h1 h2
        rw [h1, Pi.sub_apply, h2]
      have i1 := integrable_hardy_weight p hδ (Lp.memLp f)
      have i2 := integrable_hardy_weight p hδ hm
      have i3 : Integrable fun x => ‖f x - moll (rhoN n) f x‖ ^ 2 :=
        (integrable_sq_L2 (f - mollN n f)).congr (hdiff.mono fun x hx => by simp only [hx])
      have hpt : ∀ x, ‖f x‖ ^ 2 * (hQ p δ x)⁻¹ ≤
          (1 + l) * (‖moll (rhoN n) f x‖ ^ 2 * (hQ p δ x)⁻¹) +
          (1 + 1 / l) * (1 / δ ^ 2) * ‖f x - moll (rhoN n) f x‖ ^ 2 := fun x => by
        have e1 := sq_norm_le_split (f x) (moll (rhoN n) f x) hl
        have w0 : 0 ≤ (hQ p δ x)⁻¹ := (inv_pos.mpr (hQ_pos p hδ x)).le
        have w1 : (hQ p δ x)⁻¹ ≤ 1 / δ ^ 2 := by
          have := norm_hQ_inv_le p hδ x
          rwa [Real.norm_eq_abs, abs_of_nonneg w0] at this
        have e2 := mul_le_mul_of_nonneg_right e1 w0
        have e3 : ‖f x - moll (rhoN n) f x‖ ^ 2 * (hQ p δ x)⁻¹ ≤
            ‖f x - moll (rhoN n) f x‖ ^ 2 * (1 / δ ^ 2) :=
          mul_le_mul_of_nonneg_left w1 (sq_nonneg _)
        have hl1 : 0 ≤ 1 + 1 / l := by positivity
        nlinarith [mul_le_mul_of_nonneg_left e3 hl1]
      calc ∫ x, ‖f x‖ ^ 2 * (hQ p δ x)⁻¹
          ≤ ∫ x, ((1 + l) * (‖moll (rhoN n) f x‖ ^ 2 * (hQ p δ x)⁻¹) +
            (1 + 1 / l) * (1 / δ ^ 2) * ‖f x - moll (rhoN n) f x‖ ^ 2) :=
            integral_mono i1 ((i2.const_mul _).add (i3.const_mul _)) hpt
        _ = (1 + l) * (∫ x, ‖moll (rhoN n) f x‖ ^ 2 * (hQ p δ x)⁻¹) +
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
  -- `λ → 0`
  refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
  have hl : 0 < ε / (4 * G + 1) := by positivity
  have h1 := hlam _ hl
  have h2 : ε / (4 * G + 1) * (4 * G) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

omit hδ in
/-- **Hardy's inequality**: for `f ∈ L²` with weak gradient `g`, the quotient
`f / |x_i - x_j|` is in `L²`, with `‖f / |x_i - x_j|‖² ≤ 4 Σ_c ‖∂_{(i,c)} f‖²`. -/
theorem hardy_weak {f : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad f g) :
    ∃ Y : FreeL2 eta, (∀ᵐ x, Y x = (pinv p x : ℂ) * f x) ∧
      ‖Y‖ ^ 2 ≤ 4 * ∑ c : Fin 3, ‖g (p.1.1, c)‖ ^ 2 := by
  set φ : Rcfg eta → ℂ := fun x => (pinv p x : ℂ) * f x with hφ
  have hφm : AEStronglyMeasurable φ volume :=
    ((Complex.measurable_ofReal.comp (measurable_pinv p)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  have hφn : ∀ x, ‖φ x‖ ^ 2 = ‖f x‖ ^ 2 * (‖pairY p x‖ ^ 2)⁻¹ := fun x => by
    show ‖(pinv p x : ℂ) * f x‖ ^ 2 = _
    rw [norm_mul, Complex.norm_of_nonneg (pinv_nonneg p x)]
    unfold pinv
    ring
  have hδp : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  -- monotone convergence as `δ_k = 1/(k+1) ↓ 0`
  have hmeas : ∀ k : ℕ, AEMeasurable
      (fun x => ENNReal.ofReal (‖f x‖ ^ 2 * (hQ p (1 / ((k : ℝ) + 1)) x)⁻¹)) volume :=
    fun k => (integrable_hardy_weight p (hδp k) (Lp.memLp f)).aemeasurable.ennreal_ofReal
  have hmono : ∀ᵐ x ∂volume, Monotone fun k : ℕ =>
      ENNReal.ofReal (‖f x‖ ^ 2 * (hQ p (1 / ((k : ℝ) + 1)) x)⁻¹) :=
    ae_of_all _ fun x k k' hkk => by
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
      refine inv_anti₀ (hQ_pos p (hδp k') x) ?_
      have hle : 1 / ((k' : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity)
          (by have := (Nat.cast_le (α := ℝ)).mpr hkk; linarith)
      have h2 := pow_le_pow_left₀ (hδp k').le hle 2
      unfold hQ
      linarith
  have htend : ∀ᵐ x ∂volume, Tendsto (fun k : ℕ =>
      ENNReal.ofReal (‖f x‖ ^ 2 * (hQ p (1 / ((k : ℝ) + 1)) x)⁻¹)) atTop
      (𝓝 (ENNReal.ofReal (‖φ x‖ ^ 2))) := by
    filter_upwards [ae_pairY_ne] with x hx
    have hy : pairY p x ≠ 0 := hx p
    have h1 : Tendsto (fun k : ℕ => hQ p (1 / ((k : ℝ) + 1)) x) atTop
        (𝓝 (‖pairY p x‖ ^ 2)) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2 |>.const_add
        (‖pairY p x‖ ^ 2)
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero] at this
      exact this
    have h2 := (h1.inv₀ (pow_pos (norm_pos_iff.mpr hy) 2).ne').const_mul (‖f x‖ ^ 2)
    rw [hφn x]
    exact (ENNReal.continuous_ofReal.tendsto _).comp h2
  have hlim := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htend
  have hbd : ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * (hQ p (1 / ((k : ℝ) + 1)) x)⁻¹) ≤
      ENNReal.ofReal (4 * ∑ c : Fin 3, ‖g (p.1.1, c)‖ ^ 2) := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_hardy_weight p (hδp k) (Lp.memLp f))
      (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (inv_pos.mpr (hQ_pos p (hδp k) x)).le)]
    exact ENNReal.ofReal_le_ofReal (hardy_delta p (hδp k) hg)
  have hF : ∫⁻ x, ENNReal.ofReal (‖φ x‖ ^ 2) ≤
      ENNReal.ofReal (4 * ∑ c : Fin 3, ‖g (p.1.1, c)‖ ^ 2) := le_of_tendsto' hlim hbd
  -- the quotient in `L²`
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

end Weak

end FreeBoundary
