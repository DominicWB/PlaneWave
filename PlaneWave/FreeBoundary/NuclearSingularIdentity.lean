import PlaneWave.FreeBoundary.NuclearRegularity

/-!
# Clamped nuclei, part 3: the nuclear singular identity

The nuclear counterpart of `singular_identity` (`PlaneWave.FreeBoundary.SingularCommutator`). With
the regularised nuclear interaction `V_ε = Σ_{i,ℓ} q_i Z_ℓ (|x_i - P_ℓ|² + ε²)^{-1/2}` and a cutoff
flat near the nuclei (`IsFlatNear`), every `∂_aχ ∂_aV_ε` is bounded by
`Σ_{i,ℓ} |q_i Z_ℓ| |∂_aχ| / δ²` uniformly in `ε`, so the regularised identity passes to the limit by
dominated convergence: `Σ_a w_a (∫ conj(Ψ) ∂_a²χ V u + ∫ conj(∂_aΨ) ∂_aχ V u)`
`= -Σ_a w_a ∫ conj(Ψ) ∂_aχ V g_a - Σ_a w_a ∫ conj(Ψ) ∂_aχ ∂_aV u` (`w_a = -m_a⁻¹`,
`V u = nucL2 q Z Yn`, `V g_a = nucL2 q Z Zn_a`), with the bounded functions
`∂_aχ ∂_aV = ∂_aχ · nucDV 0 a`.

* `reg_identity_one_gen`: the regularised identity for any `C¹` potential;
* `ninvε`, `ndir`, `dirD_ninvε`, `nucPotε`, `nucDV`, `dirD_nucPotε`: the regularisation;
* `abs_mul_ndir_le`, `abs_mul_nucDV_le`: the bound from flatness;
* `tendsto_integral_nucPotε`, `tendsto_integral_nucDV`: the limits;
* **`nuc_singular_identity`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The regularised identity for any `C¹` potential -/

section General

variable {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m)
include hL

/-- The regularised identity for one coordinate `a` and a `C¹` potential `V`. -/
lemma reg_identity_one_gen {V : Rcfg eta → ℝ} (hV1 : ContDiff ℝ 1 V) {u : FreeL2 eta}
    {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad u g) {Ψ : Rcfg eta → ℂ}
    (hΨ : ContDiff ℝ 1 Ψ) (a : Fin eta × Fin 3) :
    (∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r * V r : ℝ) : ℂ) * u r)) +
        ∫ r, conj (dirD a Ψ r) * (((dirD a X.χ r * V r : ℝ) : ℂ) * u r) =
      -(∫ r, conj (Ψ r) * (((dirD a X.χ r * V r : ℝ) : ℂ) * g a r)) -
        ∫ r, conj (Ψ r) * (((dirD a X.χ r * dirD a V r : ℝ) : ℂ) * u r) := by
  have hχ1 : ContDiff ℝ 1 (dirD a X.χ) := (X.c1 a).of_le (by norm_num)
  have hζ : ContDiff ℝ 1 (fun r => dirD a X.χ r * V r) := hχ1.mul hV1
  have hcsχ : HasCompactSupport (dirD a X.χ) := X.hcs_of_sub hL (X.ts1 a)
  have hcs2 : HasCompactSupport (dirD a (dirD a X.χ)) := X.hcs_of_sub hL (X.ts2 a a)
  have hζc : HasCompactSupport (fun r => dirD a X.χ r * V r) := hcsχ.mul_right
  have hibp := ibp_weight hg hζ hζc hΨ a
  have hdζ : ∀ r, dirD a (fun r => dirD a X.χ r * V r) r =
      dirD a (dirD a X.χ) r * V r + dirD a X.χ r * dirD a V r :=
    fun r => dirD_mul_real ((hχ1.differentiable (by norm_num)) r)
      ((hV1.differentiable (by norm_num)) r) a
  have hΨc : Continuous Ψ := hΨ.continuous
  have hVc : Continuous V := hV1.continuous
  have hdVc : Continuous (dirD a V) := continuous_dirD hV1 (by norm_num) a
  have hc2 : Continuous (dirD a (dirD a X.χ)) := continuous_dirD (X.c1 a) (by norm_num) a
  have hI1 : Integrable fun r => conj (Ψ r) * (((dirD a (dirD a X.χ) r * V r : ℝ) : ℂ) * u r) :=
    integrable_conj_mul_weight hΨc (hc2.mul hVc) hcs2.mul_right u
  have hI2 : Integrable fun r =>
      conj (Ψ r) * (((dirD a X.χ r * dirD a V r : ℝ) : ℂ) * u r) :=
    integrable_conj_mul_weight hΨc (hχ1.continuous.mul hdVc) hcsχ.mul_right u
  have hsplit : ∫ r, conj (Ψ r) * (((dirD a (fun r => dirD a X.χ r * V r) r : ℝ) :
      ℂ) * u r) = (∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r * V r : ℝ) : ℂ) * u r)) +
        ∫ r, conj (Ψ r) * (((dirD a X.χ r * dirD a V r : ℝ) : ℂ) * u r) := by
    rw [← integral_add hI1 hI2]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [hdζ]
    push_cast
    ring
  rw [hsplit] at hibp
  linear_combination hibp

end General

/-! ## The regularised nuclear distance -/

section Regularised

/-- `(|x_i - R|² + ε²)^{-1/2}`. -/
noncomputable def ninvε (ε : ℝ) (i : Fin eta) (R : E3) (r : Rcfg eta) : ℝ :=
  (Real.sqrt (‖particleCLM i r - R‖ ^ 2 + ε ^ 2))⁻¹

/-- `-⟨y, ∂_a y⟩ / ((|y|² + ε²)^{3/2})`, `y = x_i - R`: the derivative `∂_a ninvε` for `ε > 0`,
and the derivative of `|x_i - R|⁻¹` for `ε = 0`. -/
noncomputable def ndir (ε : ℝ) (i : Fin eta) (R : E3) (a : Fin eta × Fin 3) (r : Rcfg eta) : ℝ :=
  -⟪particleCLM i r - R, particleCLM i (Pi.single a 1)⟫_ℝ /
    ((‖particleCLM i r - R‖ ^ 2 + ε ^ 2) * Real.sqrt (‖particleCLM i r - R‖ ^ 2 + ε ^ 2))

lemma hasFDerivAt_ninvε {ε : ℝ} (hε : 0 < ε) (i : Fin eta) (R : E3) (r : Rcfg eta) :
    HasFDerivAt (ninvε ε i R)
      (-((‖particleCLM i r - R‖ ^ 2 + ε ^ 2) * Real.sqrt (‖particleCLM i r - R‖ ^ 2 + ε ^ 2))⁻¹ •
        (innerSL ℝ (particleCLM i r - R)).comp (particleCLM i)) r := by
  set s := ‖particleCLM i r - R‖ ^ 2 + ε ^ 2 with hs
  have hs0 : 0 < s := sq_add_pos hε _
  have h1 : HasFDerivAt (fun x => ‖particleCLM i x - R‖ ^ 2 + ε ^ 2)
      (2 • (innerSL ℝ (particleCLM i r - R)).comp (particleCLM i)) r :=
    (((particleCLM i).hasFDerivAt.sub_const R).norm_sq).add_const _
  have h2 := h1.sqrt hs0.ne'
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have h3 := (hasDerivAt_inv hsq.ne').comp_hasFDerivAt r h2
  unfold ninvε
  refine h3.congr_fderiv ?_
  ext v
  simp only [FunLike.coe_smul, ContinuousLinearMap.coe_comp, Pi.smul_apply,
    Function.comp_apply, innerSL_apply_apply, smul_eq_mul]
  rw [Real.sq_sqrt hs0.le]
  field_simp
  ring

lemma dirD_ninvε {ε : ℝ} (hε : 0 < ε) (i : Fin eta) (R : E3) (a : Fin eta × Fin 3)
    (r : Rcfg eta) : dirD a (ninvε ε i R) r = ndir ε i R a r := by
  unfold dirD ndir
  rw [(hasFDerivAt_ninvε hε i R r).fderiv]
  simp only [FunLike.coe_smul, ContinuousLinearMap.coe_comp, Pi.smul_apply,
    Function.comp_apply, innerSL_apply_apply, smul_eq_mul]
  ring

lemma contDiff_ninvε {ε : ℝ} (hε : 0 < ε) (i : Fin eta) (R : E3) (n : ℕ) :
    ContDiff ℝ n (ninvε ε i R) := by
  unfold ninvε
  have h1 : ContDiff ℝ n (fun x : Rcfg eta => ‖particleCLM i x - R‖ ^ 2 + ε ^ 2) :=
    ((contDiff_norm_sq ℝ).comp ((particleCLM i).contDiff.sub contDiff_const)).add contDiff_const
  have h2 := h1.sqrt fun x => (sq_add_pos hε _).ne'
  exact h2.inv fun x => (Real.sqrt_pos.mpr (sq_add_pos hε _)).ne'

lemma ninvε_pos {ε : ℝ} (hε : 0 < ε) (i : Fin eta) (R : E3) (r : Rcfg eta) :
    0 < ninvε ε i R r :=
  inv_pos.mpr (Real.sqrt_pos.mpr (sq_add_pos hε _))

lemma ninvε_le (ε : ℝ) (i : Fin eta) (R : E3) {r : Rcfg eta} (hr : particleCLM i r - R ≠ 0) :
    ninvε ε i R r ≤ ‖particleCLM i r - R‖⁻¹ := by
  unfold ninvε
  have hy : 0 < ‖particleCLM i r - R‖ := norm_pos_iff.mpr hr
  refine inv_anti₀ hy ?_
  calc ‖particleCLM i r - R‖ = Real.sqrt (‖particleCLM i r - R‖ ^ 2) := (Real.sqrt_sq hy.le).symm
    _ ≤ Real.sqrt (‖particleCLM i r - R‖ ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

lemma tendsto_ninvε (i : Fin eta) (R : E3) {r : Rcfg eta} (hr : particleCLM i r - R ≠ 0) :
    Tendsto (fun n : ℕ => ninvε (1 / ((n : ℝ) + 1)) i R r) atTop
      (𝓝 ‖particleCLM i r - R‖⁻¹) := by
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hy : 0 < ‖particleCLM i r - R‖ := norm_pos_iff.mpr hr
  have h1 : Tendsto (fun n : ℕ => ‖particleCLM i r - R‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) atTop
      (𝓝 (‖particleCLM i r - R‖ ^ 2 + 0 ^ 2)) := tendsto_const_nhds.add (hε.pow 2)
  have h2 := (Real.continuous_sqrt.tendsto _).comp h1
  have h3 : Real.sqrt (‖particleCLM i r - R‖ ^ 2 + 0 ^ 2) = ‖particleCLM i r - R‖ := by
    rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hy.le]
  rw [h3] at h2
  exact h2.inv₀ hy.ne'

lemma tendsto_ndir (i : Fin eta) (R : E3) (a : Fin eta × Fin 3) {r : Rcfg eta}
    (hr : particleCLM i r - R ≠ 0) :
    Tendsto (fun n : ℕ => ndir (1 / ((n : ℝ) + 1)) i R a r) atTop (𝓝 (ndir 0 i R a r)) := by
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hy : 0 < ‖particleCLM i r - R‖ := norm_pos_iff.mpr hr
  have h1 : Tendsto (fun n : ℕ => ‖particleCLM i r - R‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) atTop
      (𝓝 (‖particleCLM i r - R‖ ^ 2 + 0 ^ 2)) := tendsto_const_nhds.add (hε.pow 2)
  have h2 := (Real.continuous_sqrt.tendsto _).comp h1
  have hpos : (‖particleCLM i r - R‖ ^ 2 + 0 ^ 2) *
      Real.sqrt (‖particleCLM i r - R‖ ^ 2 + 0 ^ 2) ≠ 0 := by
    have h0 : 0 < ‖particleCLM i r - R‖ ^ 2 + 0 ^ 2 := by positivity
    exact (mul_pos h0 (Real.sqrt_pos.mpr h0)).ne'
  exact (tendsto_const_nhds (x := -⟪particleCLM i r - R, particleCLM i (Pi.single a 1)⟫_ℝ)).div
    (h1.mul h2) hpos

lemma continuous_ndir {ε : ℝ} (hε : 0 < ε) (i : Fin eta) (R : E3) (a : Fin eta × Fin 3) :
    Continuous (ndir ε i R a) := by
  unfold ndir
  have hY : Continuous fun r : Rcfg eta => particleCLM i r - R :=
    (particleCLM i).continuous.sub continuous_const
  have h2 : Continuous fun r : Rcfg eta => ‖particleCLM i r - R‖ ^ 2 + ε ^ 2 :=
    (hY.norm.pow 2).add continuous_const
  refine (hY.inner continuous_const).neg.div (h2.mul h2.sqrt) fun r => ?_
  have hs : 0 < ‖particleCLM i r - R‖ ^ 2 + ε ^ 2 := sq_add_pos hε _
  exact (mul_pos hs (Real.sqrt_pos.mpr hs)).ne'

end Regularised

/-! ## The regularised nuclear interaction -/

section Potential

/-- The regularised nuclear interaction `Σ_{i,ℓ} q_i Z_ℓ (|x_i - P_ℓ|² + ε²)^{-1/2}`. -/
noncomputable def nucPotε (q : Fin eta → ℝ) (Z : ν → ℝ) (P : ν → E3) (ε : ℝ) (r : Rcfg eta) :
    ℝ :=
  ∑ i : Fin eta, ∑ l : ν, q i * Z l * ninvε ε i (P l) r

/-- `∂_a` of the nuclear interaction (`ε = 0`) and of its regularisation (`ε > 0`). -/
noncomputable def nucDV (q : Fin eta → ℝ) (Z : ν → ℝ) (P : ν → E3) (ε : ℝ)
    (a : Fin eta × Fin 3) (r : Rcfg eta) : ℝ :=
  ∑ i : Fin eta, ∑ l : ν, q i * Z l * ndir ε i (P l) a r

lemma contDiff_nucPotε (q : Fin eta → ℝ) (Z : ν → ℝ) (P : ν → E3) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) : ContDiff ℝ n (nucPotε q Z P ε) := by
  unfold nucPotε
  exact ContDiff.sum fun i _ => ContDiff.sum fun l _ =>
    contDiff_const.mul (contDiff_ninvε hε i (P l) n)

lemma dirD_nucPotε (q : Fin eta → ℝ) (Z : ν → ℝ) (P : ν → E3) {ε : ℝ} (hε : 0 < ε)
    (a : Fin eta × Fin 3) (r : Rcfg eta) :
    dirD a (nucPotε q Z P ε) r = nucDV q Z P ε a r := by
  have hd1 : ∀ i ∈ (Finset.univ : Finset (Fin eta)), DifferentiableAt ℝ
      (fun x => ∑ l : ν, q i * Z l * ninvε ε i (P l) x) r := fun i _ =>
    ((ContDiff.sum fun l _ => contDiff_const.mul (contDiff_ninvε hε i (P l) 1)).differentiable
      (by norm_num)) r
  have e : nucPotε q Z P ε = fun x => ∑ i : Fin eta, ∑ l : ν, q i * Z l * ninvε ε i (P l) x :=
    rfl
  rw [e, dirD_sum_fun _ hd1 a]
  unfold nucDV
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd2 : ∀ l ∈ (Finset.univ : Finset ν), DifferentiableAt ℝ
      (fun x => q i * Z l * ninvε ε i (P l) x) r := fun l _ =>
    (((contDiff_ninvε hε i (P l) 1).differentiable (by norm_num)) r).const_mul _
  rw [dirD_sum_fun _ hd2 a]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← dirD_ninvε hε i (P l) a r]
  unfold dirD
  rw [fderiv_const_mul (((contDiff_ninvε hε i (P l) 1).differentiable (by norm_num)) r)]
  rfl

lemma nucPotε_tendsto (q : Fin eta → ℝ) (Z : ν → ℝ) (P : ν → E3) {r : Rcfg eta}
    (hr : ∀ i l, particleCLM i r - P l ≠ 0) :
    Tendsto (fun n : ℕ => nucPotε q Z P (1 / ((n : ℝ) + 1)) r) atTop (𝓝 (nucPot q Z P r)) := by
  unfold nucPotε nucPot
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun l _ =>
    (tendsto_ninvε i (P l) (hr i l)).const_mul _

lemma abs_nucPotε_le (q : Fin eta → ℝ) (Z : ν → ℝ) (P : ν → E3) {ε : ℝ} (hε : 0 < ε)
    {r : Rcfg eta} (hr : ∀ i l, particleCLM i r - P l ≠ 0) :
    |nucPotε q Z P ε r| ≤ ∑ i : Fin eta, ∑ l : ν, |q i * Z l| * ‖particleCLM i r - P l‖⁻¹ := by
  unfold nucPotε
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul, abs_of_pos (ninvε_pos hε i (P l) r)]
  exact mul_le_mul_of_nonneg_left (ninvε_le ε i (P l) (hr i l)) (abs_nonneg _)

lemma ae_nuc_ne (P : ν → E3) : ∀ᵐ r : Rcfg eta, ∀ i l, particleCLM i r - P l ≠ 0 :=
  ae_all_iff.mpr fun i => ae_all_iff.mpr fun l => ae_particle_ne i (P l)

/-- **Convergence of the regularised nuclear terms** against a continuous `ω` of compact
support: `∫ ω V_ε f → ∫ ω nucL2 q Z F`, `F_{iℓ} = f/|x_i - P_ℓ|`. -/
lemma tendsto_integral_nucPotε (q : Fin eta → ℝ) (Z : ν → ℝ) (P : ν → E3) {ω : Rcfg eta → ℂ}
    (hω : Continuous ω) (hωc : HasCompactSupport ω) {f : FreeL2 eta}
    {F : Fin eta → ν → FreeL2 eta}
    (hF : ∀ i l, ∀ᵐ r, F i l r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * f r) :
    Tendsto (fun n : ℕ => ∫ r, ω r * ((nucPotε q Z P (1 / ((n : ℝ) + 1)) r : ℂ) * f r)) atTop
      (𝓝 (∫ r, ω r * nucL2 q Z F r)) := by
  have hall : ∀ᵐ r, ∀ i l, F i l r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * f r :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun l => hF i l
  have hnl := nucL2_ae q Z P hF
  refine tendsto_integral_of_dominated_convergence
    (fun r => ∑ i : Fin eta, ∑ l : ν, |q i * Z l| * ‖ω r * F i l r‖) ?_ ?_ ?_ ?_
  · intro n
    have hc : Continuous fun r => (nucPotε q Z P (1 / ((n : ℝ) + 1)) r : ℂ) :=
      Complex.continuous_ofReal.comp (contDiff_nucPotε q Z P (by positivity) 0).continuous
    exact hω.aestronglyMeasurable.mul (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ =>
      ((integrable_cont_mul_L2 hω hωc (F i l)).norm).const_mul _
  · intro n
    filter_upwards [ae_nuc_ne P, hall] with r hr hFr
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖ω r‖ * (|nucPotε q Z P (1 / ((n : ℝ) + 1)) r| * ‖f r‖)
        ≤ ‖ω r‖ * ((∑ i : Fin eta, ∑ l : ν, |q i * Z l| * ‖particleCLM i r - P l‖⁻¹) *
            ‖f r‖) := by
          gcongr
          exact abs_nucPotε_le q Z P (by positivity) hr
      _ = ∑ i : Fin eta, ∑ l : ν, |q i * Z l| * ‖ω r * F i l r‖ := by
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hFr i l, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          change ‖ω r‖ * (|q i * Z l| * ‖particle r i - P l‖⁻¹ * ‖f r‖) =
            |q i * Z l| * (‖ω r‖ * (‖particle r i - P l‖⁻¹ * ‖f r‖))
          ring
  · filter_upwards [ae_nuc_ne P, hnl] with r hr hpr
    rw [hpr]
    have h2 : Tendsto (fun n : ℕ => ((nucPotε q Z P (1 / ((n : ℝ) + 1)) r : ℝ) : ℂ)) atTop
        (𝓝 (nucPot q Z P r : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (nucPotε_tendsto q Z P hr)
    exact (h2.mul_const (f r)).const_mul (ω r)

end Potential

/-! ## The bound from flatness and the limit of the derivative terms -/

section Flat

/-- **The bound from flatness**: `|∂_aχ ∂_a |x_i - P_ℓ|_ε⁻¹| ≤ |∂_aχ| / δ²` for every `ε`. -/
lemma abs_mul_ndir_le {χ : Rcfg eta → ℝ} {P : ν → E3} {δ : ℝ} (hδ : 0 < δ)
    (hflat : IsFlatNear χ P δ) (ε : ℝ) (i : Fin eta) (l : ν)
    (a : Fin eta × Fin 3) (r : Rcfg eta) :
    |dirD a χ r * ndir ε i (P l) a r| ≤ |dirD a χ r| / δ ^ 2 := by
  obtain ⟨k, c⟩ := a
  have hT : particleCLM i (Pi.single (k, c) 1) =
      if k = i then EuclideanSpace.single c (1 : ℝ) else 0 := by
    rw [particleCLM_apply, particle_single]
  by_cases hk : k = i
  · subst hk
    by_cases hnear : ‖particle r k - P l‖ < δ
    · rw [hflat r k l hnear c]
      simp
    · have hnear := not_lt.mp hnear
      have hy0 : 0 < ‖particle r k - P l‖ := lt_of_lt_of_le hδ hnear
      set y := particle r k - P l with hydef
      have hY : particleCLM k r - P l = y := rfl
      have key : |ndir ε k (P l) (k, c) r| ≤ 1 / δ ^ 2 := by
        unfold ndir
        rw [hT, if_pos rfl, hY, abs_div, abs_neg]
        have hin : |⟪y, EuclideanSpace.single c (1 : ℝ)⟫_ℝ| ≤ ‖y‖ := by
          have := abs_real_inner_le_norm y (EuclideanSpace.single c (1 : ℝ))
          have hn : ‖EuclideanSpace.single c (1 : ℝ)‖ = 1 := by simp
          rwa [hn, mul_one] at this
        have hs : ‖y‖ ≤ Real.sqrt (‖y‖ ^ 2 + ε ^ 2) := by
          calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
            _ ≤ Real.sqrt (‖y‖ ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        have hD : ‖y‖ ^ 2 * ‖y‖ ≤ (‖y‖ ^ 2 + ε ^ 2) * Real.sqrt (‖y‖ ^ 2 + ε ^ 2) :=
          mul_le_mul (by nlinarith) hs (norm_nonneg _) (by positivity)
        have hD0 : 0 < ‖y‖ ^ 2 * ‖y‖ := by positivity
        have hDp := lt_of_lt_of_le hD0 hD
        rw [abs_of_pos hDp, div_le_div_iff₀ hDp (by positivity)]
        calc |⟪y, EuclideanSpace.single c (1 : ℝ)⟫_ℝ| * δ ^ 2 ≤ ‖y‖ * ‖y‖ ^ 2 :=
              mul_le_mul hin (pow_le_pow_left₀ hδ.le hnear 2) (by positivity) (norm_nonneg _)
          _ = ‖y‖ ^ 2 * ‖y‖ := by ring
          _ ≤ _ := hD
          _ = 1 * _ := (one_mul _).symm
      rw [abs_mul]
      calc |dirD (k, c) χ r| * |ndir ε k (P l) (k, c) r| ≤ |dirD (k, c) χ r| * (1 / δ ^ 2) :=
            mul_le_mul_of_nonneg_left key (abs_nonneg _)
        _ = |dirD (k, c) χ r| / δ ^ 2 := by ring
  · have h0 : ndir ε i (P l) (k, c) r = 0 := by
      unfold ndir
      rw [hT, if_neg hk, inner_zero_right, neg_zero, zero_div]
    rw [h0, mul_zero, abs_zero]
    positivity

lemma abs_mul_nucDV_le (q : Fin eta → ℝ) (Z : ν → ℝ) {χ : Rcfg eta → ℝ} {P : ν → E3} {δ : ℝ}
    (hδ : 0 < δ) (hflat : IsFlatNear χ P δ) (ε : ℝ) (a : Fin eta × Fin 3)
    (r : Rcfg eta) :
    |dirD a χ r * nucDV q Z P ε a r| ≤
      (∑ i : Fin eta, ∑ l : ν, |q i * Z l|) * (|dirD a χ r| / δ ^ 2) := by
  unfold nucDV
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  have e : dirD a χ r * (q i * Z l * ndir ε i (P l) a r) =
      q i * Z l * (dirD a χ r * ndir ε i (P l) a r) := by ring
  rw [e, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_mul_ndir_le hδ hflat ε i l a r) (abs_nonneg _)

variable {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m)
include hL

/-- **Convergence of the derivative terms**: `∫ ω ∂_aχ ∂_aV_ε u → ∫ ω ∂_aχ ∂_aV u`. -/
lemma tendsto_integral_nucDV (q : Fin eta → ℝ) (Z : ν → ℝ) {P : ν → E3} {δ : ℝ} (hδ : 0 < δ)
    (hflat : IsFlatNear X.χ P δ) {ω : Rcfg eta → ℂ} (hω : Continuous ω) (u : FreeL2 eta)
    (a : Fin eta × Fin 3) :
    Tendsto (fun n : ℕ => ∫ r, ω r *
        (((dirD a X.χ r * nucDV q Z P (1 / ((n : ℝ) + 1)) a r : ℝ) : ℂ) * u r)) atTop
      (𝓝 (∫ r, ω r * (((dirD a X.χ r * nucDV q Z P 0 a r : ℝ) : ℂ) * u r))) := by
  have hc1 : Continuous (dirD a X.χ) := continuous_dirD X.smooth (by norm_num) a
  have hcs1 : HasCompactSupport (dirD a X.χ) := X.hcs_of_sub hL (X.ts1 a)
  set B := (∑ i : Fin eta, ∑ l : ν, |q i * Z l|) / δ ^ 2 with hB
  have hω' : Continuous fun r => ((|dirD a X.χ r| : ℝ) : ℂ) * ω r :=
    (Complex.continuous_ofReal.comp hc1.abs).mul hω
  have hωc' : HasCompactSupport fun r => ((|dirD a X.χ r| : ℝ) : ℂ) * ω r :=
    (hasCompactSupport_ofReal hcs1.abs).mul_right
  refine tendsto_integral_of_dominated_convergence
    (fun r => B * ‖((|dirD a X.χ r| : ℝ) : ℂ) * ω r * u r‖) ?_ ?_ ?_ ?_
  · intro n
    have hc : Continuous fun r =>
        ((dirD a X.χ r * nucDV q Z P (1 / ((n : ℝ) + 1)) a r : ℝ) : ℂ) := by
      refine Complex.continuous_ofReal.comp (hc1.mul ?_)
      unfold nucDV
      exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun l _ =>
        continuous_const.mul (continuous_ndir (by positivity) i (P l) a)
    exact hω.aestronglyMeasurable.mul (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  · exact ((integrable_cont_mul_L2 hω' hωc' u).norm).const_mul _
  · intro n
    refine ae_of_all _ fun r => ?_
    have hb := abs_mul_nucDV_le q Z hδ hflat (1 / ((n : ℝ) + 1)) a r
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_abs]
    calc ‖ω r‖ * (|dirD a X.χ r * nucDV q Z P (1 / ((n : ℝ) + 1)) a r| * ‖u r‖)
        ≤ ‖ω r‖ * ((∑ i : Fin eta, ∑ l : ν, |q i * Z l|) * (|dirD a X.χ r| / δ ^ 2) * ‖u r‖) := by
          gcongr
      _ = B * (|dirD a X.χ r| * ‖ω r‖ * ‖u r‖) := by
          rw [hB]
          ring
  · filter_upwards [ae_nuc_ne P] with r hr
    have h1 : Tendsto (fun n : ℕ => nucDV q Z P (1 / ((n : ℝ) + 1)) a r) atTop
        (𝓝 (nucDV q Z P 0 a r)) := by
      unfold nucDV
      exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun l _ =>
        (tendsto_ndir i (P l) a (hr i l)).const_mul _
    have h2 := (Complex.continuous_ofReal.tendsto _).comp (h1.const_mul (dirD a X.χ r))
    exact (h2.mul_const (u r)).const_mul (ω r)

end Flat

/-! ## The nuclear singular identity -/

section Identity

variable {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m)
include hL

/-- **The nuclear singular identity**: for `u` with weak gradient `g`, nuclear Hardy functions
`Yn_{iℓ} = u/|x_i - P_ℓ|`, `Zn_{iℓ,a} = g_a/|x_i - P_ℓ|`, a cutoff flat near the nuclei and
`Ψ ∈ C¹`, with `w_a = -m_a⁻¹`,
`Σ_a w_a (∫ conj(Ψ) ∂_a²χ V u + ∫ conj(∂_aΨ) ∂_aχ V u)
  = -Σ_a w_a ∫ conj(Ψ) ∂_aχ V g_a - Σ_a w_a ∫ conj(Ψ) ∂_aχ ∂_aV u`
for the nuclear interaction `V`, where `∂_aχ ∂_aV = ∂_aχ · nucDV 0 a` is bounded
(`abs_mul_nucDV_le`). -/
theorem nuc_singular_identity (q : Fin eta → ℝ) (Z : ν → ℝ) {P : ν → E3} {δ : ℝ}
    (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ) {u : FreeL2 eta}
    {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad u g) {Yn : Fin eta → ν → FreeL2 eta}
    (hYn : ∀ i l, ∀ᵐ r, Yn i l r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * u r)
    {Zn : Fin eta → ν → Fin eta × Fin 3 → FreeL2 eta}
    (hZn : ∀ i l a, ∀ᵐ r, Zn i l a r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * g a r)
    {Ψ : Rcfg eta → ℂ} (hΨ : ContDiff ℝ 1 Ψ) :
    ∑ a : Fin eta × Fin 3, ((-(m a.1)⁻¹ : ℝ) : ℂ) *
        ((∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r : ℝ) : ℂ) * nucL2 q Z Yn r)) +
          ∫ r, conj (dirD a Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) * nucL2 q Z Yn r)) =
      -(∑ a : Fin eta × Fin 3, ((-(m a.1)⁻¹ : ℝ) : ℂ) *
          ∫ r, conj (Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) * nucL2 q Z (fun i l => Zn i l a) r)) -
        ∑ a : Fin eta × Fin 3, ((-(m a.1)⁻¹ : ℝ) : ℂ) *
          ∫ r, conj (Ψ r) * (((dirD a X.χ r * nucDV q Z P 0 a r : ℝ) : ℂ) * u r) := by
  have hΨc : Continuous Ψ := hΨ.continuous
  have hcΨ : Continuous fun r => conj (Ψ r) := Complex.continuous_conj.comp hΨc
  have hdΨ : ∀ a, Continuous fun r => conj (dirD a Ψ r) := fun a =>
    Complex.continuous_conj.comp (continuous_dirD hΨ (by norm_num) a)
  have hc1 : ∀ a, Continuous fun r => ((dirD a X.χ r : ℝ) : ℂ) := fun a =>
    Complex.continuous_ofReal.comp (continuous_dirD X.smooth (by norm_num) a)
  have hc2 : ∀ a, Continuous fun r => ((dirD a (dirD a X.χ) r : ℝ) : ℂ) := fun a =>
    Complex.continuous_ofReal.comp (continuous_dirD (X.c1 a) (by norm_num) a)
  have hcs1 : ∀ a, HasCompactSupport fun r => ((dirD a X.χ r : ℝ) : ℂ) := fun a =>
    hasCompactSupport_ofReal (X.hcs_of_sub hL (X.ts1 a))
  have hcs2 : ∀ a, HasCompactSupport fun r => ((dirD a (dirD a X.χ) r : ℝ) : ℂ) := fun a =>
    hasCompactSupport_ofReal (X.hcs_of_sub hL (X.ts2 a a))
  -- the regularised identity
  have hreg : ∀ n : ℕ, ∑ a : Fin eta × Fin 3, ((-(m a.1)⁻¹ : ℝ) : ℂ) *
      ((∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r * nucPotε q Z P (1 / ((n : ℝ) + 1)) r :
        ℝ) : ℂ) * u r)) +
        ∫ r, conj (dirD a Ψ r) * (((dirD a X.χ r * nucPotε q Z P (1 / ((n : ℝ) + 1)) r : ℝ) :
          ℂ) * u r)) =
      -(∑ a : Fin eta × Fin 3, ((-(m a.1)⁻¹ : ℝ) : ℂ) *
          ∫ r, conj (Ψ r) * (((dirD a X.χ r * nucPotε q Z P (1 / ((n : ℝ) + 1)) r : ℝ) : ℂ) *
            g a r)) -
        ∑ a : Fin eta × Fin 3, ((-(m a.1)⁻¹ : ℝ) : ℂ) *
          ∫ r, conj (Ψ r) * (((dirD a X.χ r * nucDV q Z P (1 / ((n : ℝ) + 1)) a r : ℝ) : ℂ) *
            u r) := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h1 := fun a => reg_identity_one_gen hL X (contDiff_nucPotε q Z P hε 1) hg hΨ a
    simp_rw [h1, dirD_nucPotε q Z P hε]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  -- the limits
  have T1 : ∀ a, Tendsto (fun n : ℕ => ∫ r, conj (Ψ r) *
      (((dirD a (dirD a X.χ) r * nucPotε q Z P (1 / ((n : ℝ) + 1)) r : ℝ) : ℂ) * u r)) atTop
      (𝓝 (∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r : ℝ) : ℂ) * nucL2 q Z Yn r))) := by
    intro a
    have h := tendsto_integral_nucPotε q Z P (hcΨ.mul (hc2 a)) (hcs2 a).mul_left (f := u) hYn
    have e : (∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r : ℝ) : ℂ) * nucL2 q Z Yn r)) =
        ∫ r, ((fun r => conj (Ψ r)) * fun r => ((dirD a (dirD a X.χ) r : ℝ) : ℂ)) r *
          nucL2 q Z Yn r :=
      integral_congr_ae (ae_of_all _ fun r => by simp only [Pi.mul_apply]; ring)
    rw [e]
    refine h.congr fun n => integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [Pi.mul_apply]
    push_cast
    ring
  have T2 : ∀ a, Tendsto (fun n : ℕ => ∫ r, conj (dirD a Ψ r) *
      (((dirD a X.χ r * nucPotε q Z P (1 / ((n : ℝ) + 1)) r : ℝ) : ℂ) * u r)) atTop
      (𝓝 (∫ r, conj (dirD a Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) * nucL2 q Z Yn r))) := by
    intro a
    have h := tendsto_integral_nucPotε q Z P ((hdΨ a).mul (hc1 a)) (hcs1 a).mul_left (f := u)
      hYn
    have e : (∫ r, conj (dirD a Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) * nucL2 q Z Yn r)) =
        ∫ r, ((fun r => conj (dirD a Ψ r)) * fun r => ((dirD a X.χ r : ℝ) : ℂ)) r *
          nucL2 q Z Yn r :=
      integral_congr_ae (ae_of_all _ fun r => by simp only [Pi.mul_apply]; ring)
    rw [e]
    refine h.congr fun n => integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [Pi.mul_apply]
    push_cast
    ring
  have T3 : ∀ a, Tendsto (fun n : ℕ => ∫ r, conj (Ψ r) *
      (((dirD a X.χ r * nucPotε q Z P (1 / ((n : ℝ) + 1)) r : ℝ) : ℂ) * g a r)) atTop
      (𝓝 (∫ r, conj (Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) * nucL2 q Z (fun i l => Zn i l a) r))) := by
    intro a
    have h := tendsto_integral_nucPotε q Z P (hcΨ.mul (hc1 a)) (hcs1 a).mul_left (f := g a)
      (F := fun i l => Zn i l a) (fun i l => hZn i l a)
    have e : (∫ r, conj (Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) *
        nucL2 q Z (fun i l => Zn i l a) r)) =
        ∫ r, ((fun r => conj (Ψ r)) * fun r => ((dirD a X.χ r : ℝ) : ℂ)) r *
          nucL2 q Z (fun i l => Zn i l a) r :=
      integral_congr_ae (ae_of_all _ fun r => by simp only [Pi.mul_apply]; ring)
    rw [e]
    refine h.congr fun n => integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [Pi.mul_apply]
    push_cast
    ring
  have T4 := fun a => tendsto_integral_nucDV hL X q Z hδ hflat hcΨ u a
  have hLHS := tendsto_finsetSum (Finset.univ : Finset (Fin eta × Fin 3))
    fun a _ => ((T1 a).add (T2 a)).const_mul (((-(m a.1)⁻¹ : ℝ) : ℂ))
  have hRHS := (tendsto_finsetSum (Finset.univ : Finset (Fin eta × Fin 3))
    fun a _ => (T3 a).const_mul (((-(m a.1)⁻¹ : ℝ) : ℂ))).neg.sub
      (tendsto_finsetSum (Finset.univ : Finset (Fin eta × Fin 3))
        fun a _ => (T4 a).const_mul (((-(m a.1)⁻¹ : ℝ) : ℂ)))
  refine tendsto_nhds_unique hLHS (hRHS.congr fun n => ?_)
  exact (hreg n).symm

end Identity

end FreeBoundary
