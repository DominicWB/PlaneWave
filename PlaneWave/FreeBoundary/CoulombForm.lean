import PlaneWave.FreeBoundary.HardyNuclear

/-!
# Free-space regularity, part 6: the Coulomb form

For `f ∈ L²` with a weak gradient every Coulomb term `|Y|⁻¹ |f|²` (`Y = x_i - x_j` or `x_i - R`) is
integrable, by Hardy's inequality, and depends continuously on `f` in the form norm:
`|∫ |Y|⁻¹ (|f₁|² - |f₂|²)| ≤ ‖(f₁ - f₂)/|Y|‖ ‖f₁ + f₂‖`. Hence `∫ V_∞ |f_n|² → ∫ V_∞ |f|²` when
`f_n → f` and `∇f_n → ∇f` in `L²`; a smooth function of compact support has its classical gradient
as weak gradient.

* `hasWeakGrad_of_contDiff`, `HasWeakGrad.sub`: weak gradients;
* `coulomb_integrable`, `coulomb_sub_le`: one Coulomb term;
* `freePot_integral`: the expansion of `∫ V_∞ |f|²` into Coulomb terms;
* **`tendsto_integral_freePot`**: continuity in the form norm.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology ENNReal
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Weak gradients -/

section Weak

lemma memLp_cs {φ : Rcfg eta → ℂ} (hφ : Continuous φ) (hcs : HasCompactSupport φ) :
    MemLp φ 2 volume := hφ.memLp_of_hasCompactSupport hcs

/-- A `C¹` function of compact support has its classical gradient as weak gradient. -/
theorem hasWeakGrad_of_contDiff {φ : Rcfg eta → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hcs : HasCompactSupport φ) :
    HasWeakGrad ((memLp_cs hφ.continuous hcs).toLp φ)
      (fun a => (memLp_cs (continuous_dirD hφ one_ne_zero a)
        (hasCompactSupport_dirD hcs a)).toLp (dirD a φ)) := by
  intro t ht htc a
  have m0 := memLp_cs hφ.continuous hcs
  have m1 := memLp_cs (continuous_dirD hφ one_ne_zero a) (hasCompactSupport_dirD hcs a)
  have t0 := memLp_cs ht.continuous htc
  have t1 := memLp_cs (continuous_dirD ht one_ne_zero a) (hasCompactSupport_dirD htc a)
  have e1 : ∫ r, conj (t r) * (m1.toLp (dirD a φ)) r = ∫ r, conj (t r) * dirD a φ r := by
    refine integral_congr_ae ?_
    filter_upwards [m1.coeFn_toLp] with r hr
    rw [hr]
  have e2 : ∫ r, conj (dirD a t r) * (m0.toLp φ) r = ∫ r, conj (dirD a t r) * φ r := by
    refine integral_congr_ae ?_
    filter_upwards [m0.coeFn_toLp] with r hr
    rw [hr]
  rw [e1, e2]
  exact ibp_conj (ht.differentiable one_ne_zero) (hφ.differentiable one_ne_zero) a
    (integrable_conj_mul_of_memLp t1 m0) (integrable_conj_mul_of_memLp t0 m1)
    (integrable_conj_mul_of_memLp t0 m0)

lemma integrable_conj_test_mul {t : Rcfg eta → ℂ} (ht : ContDiff ℝ 1 t) (htc : HasCompactSupport t)
    (F : FreeL2 eta) : Integrable fun r => conj (t r) * F r :=
  integrable_conj_mul_of_memLp (memLp_cs ht.continuous htc) (Lp.memLp F)

/-- Weak gradients are linear. -/
lemma HasWeakGrad.sub {f₁ f₂ : FreeL2 eta} {g₁ g₂ : Fin eta × Fin 3 → FreeL2 eta}
    (h₁ : HasWeakGrad f₁ g₁) (h₂ : HasWeakGrad f₂ g₂) :
    HasWeakGrad (f₁ - f₂) (fun a => g₁ a - g₂ a) := by
  intro t ht htc a
  have i1 := integrable_conj_test_mul ht htc (g₁ a)
  have i2 := integrable_conj_test_mul ht htc (g₂ a)
  have t1 := memLp_cs (continuous_dirD ht one_ne_zero a) (hasCompactSupport_dirD htc a)
  have j1 := integrable_conj_mul_of_memLp t1 (Lp.memLp f₁)
  have j2 := integrable_conj_mul_of_memLp t1 (Lp.memLp f₂)
  have e1 : ∫ r, conj (t r) * (g₁ a - g₂ a) r =
      (∫ r, conj (t r) * g₁ a r) - ∫ r, conj (t r) * g₂ a r := by
    rw [← integral_sub i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (g₁ a) (g₂ a)] with r hr
    rw [hr, Pi.sub_apply, mul_sub]
  have e2 : ∫ r, conj (dirD a t r) * (f₁ - f₂) r =
      (∫ r, conj (dirD a t r) * f₁ r) - ∫ r, conj (dirD a t r) * f₂ r := by
    rw [← integral_sub j1 j2]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub f₁ f₂] with r hr
    rw [hr, Pi.sub_apply, mul_sub]
  rw [e1, e2, h₁ t ht htc a, h₂ t ht htc a]
  ring

end Weak

/-! ## One Coulomb term -/

section Coulomb

variable (T : Rcfg eta →L[ℝ] E3) (y₀ : E3) {i : Fin eta}
  (hT : ∀ c, T (Pi.single (i, c) 1) = EuclideanSpace.single c 1)
  (hnull : ∀ᵐ x : Rcfg eta, T x - y₀ ≠ 0)
include hT hnull

/-- `|Y|⁻¹ |f|²` is integrable for `f ∈ L²` with a weak gradient. -/
lemma coulomb_integrable {f : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad f g) : Integrable (fun x => ‖T x - y₀‖⁻¹ * ‖f x‖ ^ 2) := by
  obtain ⟨Y, hY, -⟩ := hardy_weak_aff T y₀ hT hnull hg
  have h : Integrable (fun x => ‖f x‖ * ‖Y x‖) :=
    (Lp.memLp f).norm.integrable_mul (Lp.memLp Y).norm
  refine h.congr ?_
  filter_upwards [hY] with x hx
  rw [hx, norm_mul, Complex.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  ring

/-- **The form continuity of one Coulomb term**:
`|∫ |Y|⁻¹ |f₁|² - ∫ |Y|⁻¹ |f₂|²| ≤ √(4 Σ_c ‖∂_{(i,c)} (f₁ - f₂)‖²) (‖f₁‖ + ‖f₂‖)`. -/
lemma coulomb_sub_le {f₁ f₂ : FreeL2 eta} {g₁ g₂ : Fin eta × Fin 3 → FreeL2 eta}
    (h₁ : HasWeakGrad f₁ g₁) (h₂ : HasWeakGrad f₂ g₂) :
    |(∫ x, ‖T x - y₀‖⁻¹ * ‖f₁ x‖ ^ 2) - ∫ x, ‖T x - y₀‖⁻¹ * ‖f₂ x‖ ^ 2| ≤
      Real.sqrt (4 * ∑ c : Fin 3, ‖g₁ (i, c) - g₂ (i, c)‖ ^ 2) * (‖f₁‖ + ‖f₂‖) := by
  obtain ⟨Q, hQ, hQb⟩ := hardy_weak_aff T y₀ hT hnull (h₁.sub h₂)
  have i1 := coulomb_integrable T y₀ hT hnull h₁
  have i2 := coulomb_integrable T y₀ hT hnull h₂
  -- the pointwise identity
  have hpt : (fun x => ‖T x - y₀‖⁻¹ * ‖f₁ x‖ ^ 2 - ‖T x - y₀‖⁻¹ * ‖f₂ x‖ ^ 2) =ᵐ[volume]
      fun x => (conj (Q x) * (f₁ + f₂) x).re := by
    filter_upwards [hQ, Lp.coeFn_sub f₁ f₂, Lp.coeFn_add f₁ f₂] with x hx hs ha
    rw [hx, hs, ha, Pi.sub_apply, Pi.add_apply]
    set w := ‖T x - y₀‖⁻¹
    set a := f₁ x
    set b := f₂ x
    have hna : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have hnb : ‖b‖ ^ 2 = b.re ^ 2 + b.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [hna, hnb]
    simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_im]
    ring
  have hint : Integrable fun x => (conj (Q x) * (f₁ + f₂) x).re :=
    (integrable_conj_mul_of_memLp (Lp.memLp Q) (Lp.memLp (f₁ + f₂))).re
  have heq : (∫ x, ‖T x - y₀‖⁻¹ * ‖f₁ x‖ ^ 2) - ∫ x, ‖T x - y₀‖⁻¹ * ‖f₂ x‖ ^ 2 =
      (⟪Q, f₁ + f₂⟫_ℂ).re := by
    rw [← integral_sub i1 i2, integral_congr_ae hpt, inner_L2_eq, ← RCLike.re_to_complex,
      ← integral_re (integrable_conj_mul_of_memLp (Lp.memLp Q) (Lp.memLp (f₁ + f₂)))]
    rfl
  rw [heq]
  have hQn : ‖Q‖ ≤ Real.sqrt (4 * ∑ c : Fin 3, ‖g₁ (i, c) - g₂ (i, c)‖ ^ 2) :=
    Real.le_sqrt_of_sq_le hQb
  calc |(⟪Q, f₁ + f₂⟫_ℂ).re| ≤ ‖⟪Q, f₁ + f₂⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖Q‖ * ‖f₁ + f₂‖ := norm_inner_le_norm _ _
    _ ≤ Real.sqrt (4 * ∑ c : Fin 3, ‖g₁ (i, c) - g₂ (i, c)‖ ^ 2) * (‖f₁‖ + ‖f₂‖) :=
        mul_le_mul hQn (norm_add_le _ _) (norm_nonneg _) (Real.sqrt_nonneg _)

/-- Convergence of one Coulomb term along `f_n → f`, `∂f_n → ∂f` in `L²`. -/
lemma tendsto_coulomb {f : ℕ → FreeL2 eta} {g : ℕ → Fin eta × Fin 3 → FreeL2 eta}
    {f₀ : FreeL2 eta} {g₀ : Fin eta × Fin 3 → FreeL2 eta} (hg : ∀ n, HasWeakGrad (f n) (g n))
    (hg₀ : HasWeakGrad f₀ g₀) (hf : Tendsto f atTop (𝓝 f₀))
    (hgt : ∀ a, Tendsto (fun n => g n a) atTop (𝓝 (g₀ a))) :
    Tendsto (fun n => ∫ x, ‖T x - y₀‖⁻¹ * ‖f n x‖ ^ 2) atTop
      (𝓝 (∫ x, ‖T x - y₀‖⁻¹ * ‖f₀ x‖ ^ 2)) := by
  have hb : Tendsto (fun n => Real.sqrt (4 * ∑ c : Fin 3, ‖g n (i, c) - g₀ (i, c)‖ ^ 2) *
      (‖f n‖ + ‖f₀‖)) atTop (𝓝 (Real.sqrt (4 * ∑ c : Fin 3, (0 : ℝ) ^ 2) * (‖f₀‖ + ‖f₀‖))) := by
    refine Tendsto.mul (Real.continuous_sqrt.tendsto _ |>.comp ?_)
      ((hf.norm).add tendsto_const_nhds)
    refine Tendsto.const_mul _ (tendsto_finsetSum (f := fun c n => ‖g n (i, c) - g₀ (i, c)‖ ^ 2)
      Finset.univ fun c _ => ?_)
    have := (tendsto_iff_norm_sub_tendsto_zero.mp (hgt (i, c))).pow 2
    exact this
  have h0 : Real.sqrt (4 * ∑ c : Fin 3, (0 : ℝ) ^ 2) * (‖f₀‖ + ‖f₀‖) = 0 := by simp
  rw [h0] at hb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
  rw [Real.norm_eq_abs]
  exact coulomb_sub_le T y₀ hT hnull (hg n) hg₀

end Coulomb

/-! ## The free-space potential -/

section Potential

lemma pairY_single_self' (p : FiniteElectronPair eta) (c : Fin 3) :
    pairY p (Pi.single (p.1.1, c) 1) = EuclideanSpace.single c 1 := pairY_single_self p c

lemma ae_pairY_sub_ne (p : FiniteElectronPair eta) : ∀ᵐ x : Rcfg eta, pairY p x - 0 ≠ 0 := by
  filter_upwards [ae_pairY_ne] with x hx
  rw [sub_zero]
  exact hx p

/-- `V_∞ = Σ_{i<j} q_i q_j |x_i - x_j|⁻¹ + Σ_{a,ℓ} q_a Z_ℓ |x_a - R_ℓ|⁻¹`. -/
lemma freePot_eq (sys : CoulombSystem eta ν) (P : ν → E3) (r : Rcfg eta) :
    freePot sys P r = (∑ p : FiniteElectronPair eta, sys.charge p.1.1 * sys.charge p.1.2 *
        ‖pairY p r - 0‖⁻¹) +
      ∑ a : Fin eta, ∑ l : ν, sys.charge a * sys.nuclei.charge l * ‖particleCLM a r - P l‖⁻¹ := by
  unfold freePot potInf
  simp only [sub_zero, one_div, pairY_apply, particleCLM_apply]

/-- **`∫ V_∞ |f|²`** for `f ∈ L²` with a weak gradient: integrable, and the sum of the Coulomb
terms. -/
theorem freePot_integral (sys : CoulombSystem eta ν) (P : ν → E3) {f : FreeL2 eta}
    {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad f g) :
    Integrable (fun r => freePot sys P r * ‖f r‖ ^ 2) ∧
      ∫ r, freePot sys P r * ‖f r‖ ^ 2 =
        (∑ p : FiniteElectronPair eta, sys.charge p.1.1 * sys.charge p.1.2 *
          ∫ r, ‖pairY p r - 0‖⁻¹ * ‖f r‖ ^ 2) +
        ∑ a : Fin eta, ∑ l : ν, sys.charge a * sys.nuclei.charge l *
          ∫ r, ‖particleCLM a r - P l‖⁻¹ * ‖f r‖ ^ 2 := by
  have ip : ∀ p : FiniteElectronPair eta, Integrable
      (fun r => sys.charge p.1.1 * sys.charge p.1.2 * (‖pairY p r - 0‖⁻¹ * ‖f r‖ ^ 2)) :=
    fun p => (coulomb_integrable (pairY p) 0 (pairY_single_self' p) (ae_pairY_sub_ne p)
      hg).const_mul _
  have inn : ∀ (a : Fin eta) (l : ν), Integrable
      (fun r => sys.charge a * sys.nuclei.charge l * (‖particleCLM a r - P l‖⁻¹ * ‖f r‖ ^ 2)) :=
    fun a l => (coulomb_integrable (particleCLM a) (P l) (particleCLM_single a)
      (ae_particle_ne a (P l)) hg).const_mul _
  have ipS : Integrable fun r => ∑ p : FiniteElectronPair eta,
      sys.charge p.1.1 * sys.charge p.1.2 * (‖pairY p r - 0‖⁻¹ * ‖f r‖ ^ 2) :=
    integrable_finsetSum _ fun p _ => ip p
  have inS : Integrable fun r => ∑ a : Fin eta, ∑ l : ν,
      sys.charge a * sys.nuclei.charge l * (‖particleCLM a r - P l‖⁻¹ * ‖f r‖ ^ 2) :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun l _ => inn a l
  have hfun : (fun r => freePot sys P r * ‖f r‖ ^ 2) = fun r =>
      (∑ p : FiniteElectronPair eta,
        sys.charge p.1.1 * sys.charge p.1.2 * (‖pairY p r - 0‖⁻¹ * ‖f r‖ ^ 2)) +
      ∑ a : Fin eta, ∑ l : ν,
        sys.charge a * sys.nuclei.charge l * (‖particleCLM a r - P l‖⁻¹ * ‖f r‖ ^ 2) := by
    funext r
    rw [freePot_eq, add_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      ring
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
  rw [hfun]
  refine ⟨ipS.add inS, ?_⟩
  rw [integral_add ipS inS, integral_finsetSum _ fun p _ => ip p,
    integral_finsetSum _ fun a _ => integrable_finsetSum _ fun l _ => inn a l]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun l _ => inn a l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul]

/-- **Continuity of `∫ V_∞ |f|²` in the form norm**: `f_n → f`, `∇f_n → ∇f` in `L²` give
`∫ V_∞ |f_n|² → ∫ V_∞ |f|²`. -/
theorem tendsto_integral_freePot (sys : CoulombSystem eta ν) (P : ν → E3)
    {f : ℕ → FreeL2 eta} {g : ℕ → Fin eta × Fin 3 → FreeL2 eta} {f₀ : FreeL2 eta}
    {g₀ : Fin eta × Fin 3 → FreeL2 eta} (hg : ∀ n, HasWeakGrad (f n) (g n))
    (hg₀ : HasWeakGrad f₀ g₀) (hf : Tendsto f atTop (𝓝 f₀))
    (hgt : ∀ a, Tendsto (fun n => g n a) atTop (𝓝 (g₀ a))) :
    Tendsto (fun n => ∫ r, freePot sys P r * ‖f n r‖ ^ 2) atTop
      (𝓝 (∫ r, freePot sys P r * ‖f₀ r‖ ^ 2)) := by
  simp_rw [(freePot_integral sys P (hg _)).2, (freePot_integral sys P hg₀).2]
  refine Tendsto.add (tendsto_finsetSum _ fun p _ => Tendsto.const_mul _ ?_)
    (tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun l _ => Tendsto.const_mul _ ?_)
  · exact tendsto_coulomb (pairY p) 0 (pairY_single_self' p) (ae_pairY_sub_ne p) hg hg₀ hf hgt
  · exact tendsto_coulomb (particleCLM a) (P l) (particleCLM_single a) (ae_particle_ne a (P l))
      hg hg₀ hf hgt

end Potential

end FreeBoundary
