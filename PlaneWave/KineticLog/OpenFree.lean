import PlaneWave.KineticLog.OpenCell
import PlaneWave.FreeBoundary.SpinFreeDynamicsEndpoint

/-!
# Logarithmic kinetic bound, part 24: free-space calculus for the kinetic localisation

The free-space ingredients of `prop:free-kinetic-log`, for a supplied strong solution
`i ψ' = H_∞ ψ` (`HasFreeHamiltonian`, as in `prop:free-dyn`):

* `RWeight`, `RWeight.mul`: multiplication by a bounded measurable real function on `L²(ℝ^{3η})`,
  with its norm bounds, its symmetry and its localised bound (`norm_mul_le_of_supp`);
* `hasWeakGrad_mul`: the product rule `∂(w f) = (∂w) f + w ∂f` for weak gradients;
* **`inner_ibp`**: integration by parts for `H¹` functions, `⟪h, ∂_a f⟫ = -⟪∂_a h, f⟫`
  (mollification);
* `massP`, **`freeKinQ`**: the kinetic energy of particle `p` as the quadratic form
  `(1/(2 m_p)) Σ_c ‖∂_{p,c} f‖²`; `inner_kinP_eq`: it is `⟪f, T_p f⟫` whenever `T_p f = z` weakly
  (`HasFreeWeakKinetic (massP sys p) f z`), and `hasFreeWeakKinetic_massP` constructs `T_p f` from
  the weak second derivatives;
* `HasFreeHamiltonian.sub` and **`norm_H_conserved`**: the Hamiltonian relation is linear, so the
  difference quotients `(ψ(t+h) - ψ(t))/h` of a strong solution are strong solutions and have
  conserved norms; letting `h → 0` gives conservation of `‖H_∞ ψ(t)‖`. No spectral filter and no
  assumed all-time graph budget is used.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter MeasureTheory Set PlaneWaveCertificate FreeBoundary

namespace KineticLog

variable {eta : ℕ}

/-! ## Bounded real weights on `L²(ℝ^{3η})` -/

/-- A bounded measurable real weight on `ℝ^{3η}`. -/
structure RWeight (eta : ℕ) where
  /-- The weight. -/
  w : Rcfg eta → ℝ
  meas : Measurable w
  /-- A bound for the weight. -/
  B : ℝ
  bound : ∀ r, |w r| ≤ B

namespace RWeight

lemma B_nonneg (W : RWeight eta) : 0 ≤ W.B := (abs_nonneg _).trans (W.bound 0)

lemma memLp_mul (W : RWeight eta) (f : FreeL2 eta) :
    MemLp (fun r => (W.w r : ℂ) * f r) 2 volume :=
  (Lp.memLp f).of_le_mul
    ((Complex.continuous_ofReal.measurable.comp W.meas).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f))
    (ae_of_all _ fun r => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (W.bound r) (norm_nonneg _))

/-- **Multiplication by the weight** on `L²(ℝ^{3η})`. -/
noncomputable def mul (W : RWeight eta) (f : FreeL2 eta) : FreeL2 eta := (W.memLp_mul f).toLp _

lemma mul_ae (W : RWeight eta) (f : FreeL2 eta) :
    (W.mul f : Rcfg eta → ℂ) =ᵐ[volume] fun r => (W.w r : ℂ) * f r :=
  MemLp.coeFn_toLp _

lemma norm_mul_le (W : RWeight eta) (f : FreeL2 eta) : ‖W.mul f‖ ≤ W.B * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [W.mul_ae f] with r hr
  rw [hr, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (W.bound r) (norm_nonneg _)

/-- The weight is symmetric: `⟪w f₁, f₂⟫ = ⟪f₁, w f₂⟫`. -/
lemma inner_mul_left (W : RWeight eta) (f₁ f₂ : FreeL2 eta) :
    ⟪W.mul f₁, f₂⟫_ℂ = ⟪f₁, W.mul f₂⟫_ℂ := by
  rw [inner_L2_eq, inner_L2_eq]
  refine integral_congr_ae ?_
  filter_upwards [W.mul_ae f₁, W.mul_ae f₂] with r h1 h2
  rw [h1, h2, map_mul, Complex.conj_ofReal]
  ring

end RWeight

/-- **A localised `L²` bound**: if `F = c f` a.e. with `|c| ≤ B`, `c = 0` off `S` and
`∫_S |f|² ≤ e²`, then `‖F‖ ≤ B e`. -/
lemma norm_le_of_ae_mul_supp {F f : FreeL2 eta} {c : Rcfg eta → ℂ}
    (hF : (F : Rcfg eta → ℂ) =ᵐ[volume] fun r => c r * f r) {S : Set (Rcfg eta)}
    (hS : MeasurableSet S) (hc : ∀ r, r ∉ S → c r = 0) {B : ℝ} (hB : ∀ r, ‖c r‖ ≤ B) {e : ℝ}
    (he : 0 ≤ e) (hfe : ∫ r in S, ‖f r‖ ^ 2 ≤ e ^ 2) : ‖F‖ ≤ B * e := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hf2 : Integrable (fun r => ‖f r‖ ^ 2) := integrable_sq_L2 f
  have h1 : ∫ r, ‖c r * f r‖ ^ 2 ≤ B ^ 2 * e ^ 2 := by
    calc ∫ r, ‖c r * f r‖ ^ 2
        ≤ ∫ r, S.indicator (fun r => B ^ 2 * ‖f r‖ ^ 2) r := by
          refine integral_mono_of_nonneg (ae_of_all _ fun r => by positivity)
            ((hf2.const_mul _).indicator hS) (ae_of_all _ fun r => ?_)
          by_cases hr : r ∈ S
          · rw [indicator_of_mem hr]
            beta_reduce
            rw [norm_mul, mul_pow]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB r) 2)
              (by positivity)
          · rw [indicator_of_notMem hr]
            simp [hc r hr]
      _ = B ^ 2 * ∫ r in S, ‖f r‖ ^ 2 := by
          rw [integral_indicator hS, integral_const_mul]
      _ ≤ B ^ 2 * e ^ 2 := mul_le_mul_of_nonneg_left hfe (by positivity)
  have h3 : ‖F‖ ^ 2 ≤ (B * e) ^ 2 := by
    rw [mul_pow, norm_sq_eq_of_ae hF]
    exact h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hB0 he) two_ne_zero).mp h3

lemma RWeight.norm_mul_le_of_supp (W : RWeight eta) {S : Set (Rcfg eta)} (hS : MeasurableSet S)
    (hW : ∀ r, r ∉ S → W.w r = 0) (f : FreeL2 eta) {e : ℝ} (he : 0 ≤ e)
    (hfe : ∫ r in S, ‖f r‖ ^ 2 ≤ e ^ 2) : ‖W.mul f‖ ≤ W.B * e :=
  norm_le_of_ae_mul_supp (W.mul_ae f) hS (fun r hr => by rw [hW r hr, Complex.ofReal_zero])
    (fun r => by rw [Complex.norm_real, Real.norm_eq_abs]; exact W.bound r) he hfe

lemma mem_tsupport_of_dirD_neC {φ : Rcfg eta → ℂ} {r : Rcfg eta} {a : Fin eta × Fin 3}
    (h : dirD a φ r ≠ 0) : r ∈ tsupport φ := by
  apply support_fderiv_subset (𝕜 := ℝ)
  rw [Function.mem_support]
  intro h0
  apply h
  unfold dirD
  rw [h0]
  rfl

lemma tsupport_dirD_subsetC {φ : Rcfg eta → ℂ} (a : Fin eta × Fin 3) :
    tsupport (dirD a φ) ⊆ tsupport φ :=
  closure_minimal (fun _ hy => mem_tsupport_of_dirD_neC hy) (isClosed_tsupport φ)

/-! ## The product rule -/

/-- **The product rule for weak gradients**: if `∂f = g` weakly and `w` is a `C¹` bounded real
weight whose derivatives are the weights `W' a`, then `∂_a(w f) = (∂_a w) f + w g_a`. -/
theorem hasWeakGrad_mul {f : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad f g) (W : RWeight eta) (hW : ContDiff ℝ 1 W.w)
    (W' : Fin eta × Fin 3 → RWeight eta) (hW' : ∀ a, (W' a).w = dirD a W.w) :
    HasWeakGrad (W.mul f) (fun a => (W' a).mul f + W.mul (g a)) := by
  intro φ hφ hφc a
  have hwc : ContDiff ℝ 1 (fun y => (W.w y : ℂ)) := Complex.ofRealCLM.contDiff.comp hW
  have hψ : ContDiff ℝ 1 (fun y => (W.w y : ℂ) * φ y) := hwc.mul hφ
  have hψc : HasCompactSupport (fun y => (W.w y : ℂ) * φ y) := hφc.mul_left
  have hT := hg _ hψ hψc a
  have hd : ∀ r, dirD a (fun y => (W.w y : ℂ) * φ y) r =
      ((dirD a W.w r : ℝ) : ℂ) * φ r + (W.w r : ℂ) * dirD a φ r := fun r =>
    dirD_ofReal_mul ((hW.differentiable (by norm_num)) r) ((hφ.differentiable (by norm_num)) r) a
  have hdW : ∀ r, (W' a).w r = dirD a W.w r := fun r => by rw [hW' a]
  -- integrability of the pieces
  have hφcont : Continuous φ := hφ.continuous
  have hdφ : Continuous (dirD a φ) := continuous_dirD hφ (by norm_num) a
  have hdφc : HasCompactSupport (dirD a φ) := hasCompactSupport_dirD hφc a
  have hwcont : Continuous W.w := hW.continuous
  have hdwcont : Continuous (dirD a W.w) := continuous_dirD hW (by norm_num) a
  have i1 : Integrable (fun r => conj (φ r) * (((dirD a W.w r : ℝ) : ℂ) * f r)) := by
    have h := integrable_cont_mul_L2 ((Complex.continuous_conj.comp hφcont).mul
      (Complex.continuous_ofReal.comp hdwcont)) ((hφc.comp_left (g := conj) (by simp)).mul_right) f
    refine h.congr (ae_of_all _ fun r => ?_)
    simp only [Function.comp_apply, Pi.mul_apply]
    ring
  have i2 : Integrable (fun r => conj (φ r) * ((W.w r : ℂ) * g a r)) := by
    have h := integrable_cont_mul_L2 ((Complex.continuous_conj.comp hφcont).mul
      (Complex.continuous_ofReal.comp hwcont)) ((hφc.comp_left (g := conj) (by simp)).mul_right)
      (g a)
    refine h.congr (ae_of_all _ fun r => ?_)
    simp only [Function.comp_apply, Pi.mul_apply]
    ring
  have i3 : Integrable (fun r => conj (dirD a φ r) * ((W.w r : ℂ) * f r)) := by
    have h := integrable_cont_mul_L2 ((Complex.continuous_conj.comp hdφ).mul
      (Complex.continuous_ofReal.comp hwcont)) ((hdφc.comp_left (g := conj) (by simp)).mul_right) f
    refine h.congr (ae_of_all _ fun r => ?_)
    simp only [Function.comp_apply, Pi.mul_apply]
    ring
  -- the weak-gradient test with `w φ`
  have hL : ∫ r, conj ((W.w r : ℂ) * φ r) * g a r = ∫ r, conj (φ r) * ((W.w r : ℂ) * g a r) := by
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have hR : ∫ r, conj (dirD a (fun y => (W.w y : ℂ) * φ y) r) * f r =
      (∫ r, conj (φ r) * (((dirD a W.w r : ℝ) : ℂ) * f r)) +
        ∫ r, conj (dirD a φ r) * ((W.w r : ℂ) * f r) := by
    rw [← integral_add i1 i3]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [hd, map_add, map_mul, Complex.conj_ofReal]
    ring
  rw [hL, hR] at hT
  -- the left side of the goal
  have e1 : ∫ r, conj (φ r) * ((W' a).mul f + W.mul (g a)) r =
      (∫ r, conj (φ r) * (((dirD a W.w r : ℝ) : ℂ) * f r)) +
        ∫ r, conj (φ r) * ((W.w r : ℂ) * g a r) := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add ((W' a).mul f) (W.mul (g a)), (W' a).mul_ae f,
      W.mul_ae (g a)] with r h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, hdW r]
    ring
  have e2 : ∫ r, conj (dirD a φ r) * (W.mul f) r =
      ∫ r, conj (dirD a φ r) * ((W.w r : ℂ) * f r) := by
    refine integral_congr_ae ?_
    filter_upwards [W.mul_ae f] with r h1
    rw [h1]
  rw [e1, e2]
  linear_combination hT

/-! ## Integration by parts for `H¹` functions -/

/-- **Integration by parts on `ℝ^{3η}` for `H¹` functions**: if `∂f = g` and `∂h = k` weakly,
then `⟪h, ∂_a f⟫ = -⟪∂_a h, f⟫`. -/
theorem inner_ibp {f h : FreeL2 eta} {g k : Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad f g) (hk : HasWeakGrad h k) (a : Fin eta × Fin 3) :
    ⟪h, g a⟫_ℂ = -⟪k a, f⟫_ℂ := by
  have hfl := locInt_L2 f
  have hhl := locInt_L2 h
  have hn : ∀ n : ℕ, ⟪mollN n h, mollN n (g a)⟫_ℂ = -⟪mollN n (k a), mollN n f⟫_ℂ := by
    intro n
    have hσ : ContDiff ℝ 3 (rhoN (eta := eta) n) := contDiff_rhoN n
    have hσc := hasCompactSupport_rhoN (eta := eta) n
    have hσ1 : ContDiff ℝ 1 (rhoN (eta := eta) n) := hσ.of_le (by norm_num)
    have hF : ContDiff ℝ 1 (moll (rhoN n) h) := contDiff_moll hσc hσ1 hhl
    have hG : ContDiff ℝ 1 (moll (rhoN n) f) := contDiff_moll hσc hσ1 hfl
    have dF : dirD a (moll (rhoN n) h) = moll (rhoN n) (k a) := by
      funext x
      rw [dirD_moll hσc hσ1 hhl a]
      exact moll_dirD_eq hk hσc hσ1 a x
    have dG : dirD a (moll (rhoN n) f) = moll (rhoN n) (g a) := by
      funext x
      rw [dirD_moll hσc hσ1 hfl a]
      exact moll_dirD_eq hg hσc hσ1 a x
    have m0 := memLp_moll_k hσc hσ.continuous h
    have m1 := memLp_moll_k hσc hσ.continuous f
    have m2 := memLp_moll_k hσc hσ.continuous (k a)
    have m3 := memLp_moll_k hσc hσ.continuous (g a)
    have hibp := ibp_conj (hF.differentiable (by norm_num)) (hG.differentiable (by norm_num)) a
      (by rw [dF]; exact integrable_conj_mul_of_memLp m2 m1)
      (by rw [dG]; exact integrable_conj_mul_of_memLp m0 m3)
      (integrable_conj_mul_of_memLp m0 m1)
    rw [dF, dG] at hibp
    rw [inner_L2_eq, inner_L2_eq]
    have e1 : ∫ x, conj (mollN n h x) * mollN n (g a) x =
        ∫ x, conj (moll (rhoN n) h x) * moll (rhoN n) (g a) x := by
      refine integral_congr_ae ?_
      filter_upwards [mollN_ae n h, mollN_ae n (g a)] with x h1 h2
      rw [h1, h2]
    have e2 : ∫ x, conj (mollN n (k a) x) * mollN n f x =
        ∫ x, conj (moll (rhoN n) (k a) x) * moll (rhoN n) f x := by
      refine integral_congr_ae ?_
      filter_upwards [mollN_ae n (k a), mollN_ae n f] with x h1 h2
      rw [h1, h2]
    rw [e1, e2, hibp]
  have hL : Tendsto (fun n => ⟪mollN n h, mollN n (g a)⟫_ℂ) atTop (𝓝 ⟪h, g a⟫_ℂ) :=
    (tendsto_mollN h).inner (tendsto_mollN (g a))
  have hR : Tendsto (fun n => -⟪mollN n (k a), mollN n f⟫_ℂ) atTop (𝓝 (-⟪k a, f⟫_ℂ)) :=
    ((tendsto_mollN (k a)).inner (tendsto_mollN f)).neg
  exact tendsto_nhds_unique (hL.congr hn) hR

/-! ## The kinetic energy of one particle in free space -/

section KinP

variable {ν : Type} [Fintype ν]

/-- The mass vector of particle `p` alone: `m_p` at `p` and `0` elsewhere (so that
`freeKinetic (massP sys p) = -(1/(2 m_p)) Δ_p`, the kinetic energy `T_p`). -/
noncomputable def massP (sys : CoulombSystem eta ν) (p : Fin eta) : Fin eta → ℝ :=
  fun i => if i = p then sys.mass p else 0

/-- **The free-space kinetic energy of particle `p`** as the quadratic form of `T_p`:
`(1/(2 m_p)) Σ_c ‖∂_{p,c} f‖²`, `g` the weak gradient of `f`. -/
noncomputable def freeKinQ (sys : CoulombSystem eta ν) (p : Fin eta)
    (g : Fin eta × Fin 3 → FreeL2 eta) : ℝ :=
  1 / (2 * sys.mass p) * ∑ c : Fin 3, ‖g (p, c)‖ ^ 2

omit [Fintype ν] in
lemma freeKinQ_nonneg (sys : CoulombSystem eta ν) (p : Fin eta)
    (g : Fin eta × Fin 3 → FreeL2 eta) : 0 ≤ freeKinQ sys p g := by
  unfold freeKinQ
  have := sys.mass_pos p
  positivity

omit [Fintype ν] in
lemma sum_massP_inv (sys : CoulombSystem eta ν) (p : Fin eta) (F : Fin eta × Fin 3 → ℝ) :
    ∑ a : Fin eta × Fin 3, (massP sys p a.1)⁻¹ * F a = (sys.mass p)⁻¹ * ∑ c : Fin 3, F (p, c) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
  · simp [massP, Finset.mul_sum]
  · intro i _ hi
    simp [massP, hi]
  · simp

omit [Fintype ν] in
/-- **`⟪f, T_p f⟫` is the quadratic form**: if `T_p f = z` weakly
(`HasFreeWeakKinetic (massP sys p) f z`) and `g` is the weak gradient of `f`, then
`⟪f, z⟫ = (1/(2 m_p)) Σ_c ‖∂_{p,c} f‖²`. -/
theorem inner_kinP_eq (sys : CoulombSystem eta ν) (p : Fin eta) {f z : FreeL2 eta}
    (hK : HasFreeWeakKinetic (massP sys p) f z) {g : Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad f g) : ⟪f, z⟫_ℂ = (freeKinQ sys p g : ℂ) := by
  have e := sum_massP_inv sys p (fun a => ‖g a‖ ^ 2)
  rw [inner_weak_kinetic hK hg, e]
  unfold freeKinQ
  congr 1
  have := sys.mass_pos p
  field_simp

omit [Fintype ν] in
/-- **`T_p f` from the weak second derivatives**:
`T_p f = -(1/(2 m_p)) Σ_c ∂_{p,c}² f` weakly. -/
theorem hasFreeWeakKinetic_massP (sys : CoulombSystem eta ν) (p : Fin eta) {f : FreeL2 eta}
    {g : Fin eta × Fin 3 → FreeL2 eta} {g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad f g) (hg2 : ∀ b, HasWeakGrad (g b) (g2 b)) :
    HasFreeWeakKinetic (massP sys p) f
      (∑ c : Fin 3, ((-(1 / (2 * sys.mass p)) : ℝ) : ℂ) • g2 (p, c) (p, c)) := by
  intro φ hφ hφc
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  -- `∫ conj(φ) ∂_a² f = ∫ conj(∂_a² φ) f`
  have hpair : ∀ a : Fin eta × Fin 3,
      ∫ r, conj (φ r) * g2 a a r = ∫ r, conj (dirD a (dirD a φ) r) * f r := by
    intro a
    rw [hg2 a φ hφ1 hφc a, hg (dirD a φ) (contDiff_dirD hφ a) (hasCompactSupport_dirD hφc a) a,
      neg_neg]
  have hint2 : ∀ a : Fin eta × Fin 3, Integrable (fun r => conj (dirD a (dirD a φ) r) * f r) :=
    fun a => integrable_conj_mul_of_memLp
      (memLp_cs (continuous_dirD (contDiff_dirD hφ a) (by norm_num) a)
        (hasCompactSupport_dirD (hasCompactSupport_dirD hφc a) a)) (Lp.memLp f)
  -- the left side, by linearity of the inner product with `φ`
  have hφL : MemLp φ 2 volume := memLp_cs hφ.continuous hφc
  have hin : ∀ G : FreeL2 eta, ∫ r, conj (φ r) * G r = ⟪hφL.toLp φ, G⟫_ℂ := by
    intro G
    rw [inner_L2_eq]
    refine integral_congr_ae ?_
    filter_upwards [hφL.coeFn_toLp] with r hr
    rw [hr]
  have eL : ∫ r, conj (φ r) *
      (∑ c : Fin 3, ((-(1 / (2 * sys.mass p)) : ℝ) : ℂ) • g2 (p, c) (p, c)) r =
      ∑ c : Fin 3, ((-(1 / (2 * sys.mass p)) : ℝ) : ℂ) * ∫ r, conj (φ r) * g2 (p, c) (p, c) r := by
    rw [hin, inner_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_smul_right, hin]
  -- the right side
  have eR : ∫ r, conj (freeKinetic (massP sys p) φ r) * f r =
      ∑ c : Fin 3, ((-(1 / (2 * sys.mass p)) : ℝ) : ℂ) *
        ∫ r, conj (dirD (p, c) (dirD (p, c) φ) r) * f r := by
    have hk : ∀ r, conj (freeKinetic (massP sys p) φ r) * f r =
        ∑ c : Fin 3, ((-(1 / (2 * sys.mass p)) : ℝ) : ℂ) *
          (conj (dirD (p, c) (dirD (p, c) φ) r) * f r) := by
      intro r
      rw [freeKinetic_eq (massP sys p) hφ r]
      have e : ∑ a : Fin eta × Fin 3, ((massP sys p a.1 : ℂ))⁻¹ * dirD a (dirD a φ) r =
          ∑ c : Fin 3, ((sys.mass p : ℂ))⁻¹ * dirD (p, c) (dirD (p, c) φ) r := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
        · simp only [massP, if_true]
        · intro i _ hi
          simp [massP, hi]
        · simp
      rw [e, Finset.mul_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [map_mul, map_neg, map_inv₀, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
      push_cast
      field_simp
    simp_rw [hk]
    rw [integral_finsetSum _ fun c _ => (hint2 (p, c)).const_mul _]
    exact Finset.sum_congr rfl fun c _ => integral_const_mul _ _
  rw [eL, eR]
  exact Finset.sum_congr rfl fun c _ => by rw [hpair (p, c)]

end KinP

/-! ## Conservation of the Hamiltonian norm -/

section Conservation

variable {ν : Type} [Fintype ν]

/-- **The free Hamiltonian relation is linear.** -/
lemma HasFreeHamiltonian.sub (sys : CoulombSystem eta ν) (P : ν → E3)
    {f₁ f₂ h₁ h₂ : FreeL2 eta} (h1 : HasFreeHamiltonian sys P f₁ h₁)
    (h2 : HasFreeHamiltonian sys P f₂ h₂) : HasFreeHamiltonian sys P (f₁ - f₂) (h₁ - h₂) := by
  obtain ⟨v₁, hv₁, hk₁⟩ := h1
  obtain ⟨v₂, hv₂, hk₂⟩ := h2
  refine ⟨v₁ - v₂, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub v₁ v₂, Lp.coeFn_sub f₁ f₂, hv₁, hv₂] with x e1 e2 e3 e4
    rw [e1, e2, Pi.sub_apply, Pi.sub_apply, e3, e4]
    ring
  · intro φ hφ hφc
    have hKc : Continuous (freeKinetic sys.mass φ) := by
      have h : freeKinetic sys.mass φ = fun r => (-(1 / 2 : ℂ)) * ∑ a : Fin eta × Fin 3,
          ((sys.mass a.1 : ℂ))⁻¹ * dirD a (dirD a φ) r := funext fun r => freeKinetic_eq _ hφ r
      rw [h]
      exact continuous_const.mul (continuous_finsetSum _ fun a _ => continuous_const.mul
        (continuous_dirD (contDiff_dirD hφ a) (by norm_num) a))
    have hKcs : HasCompactSupport (freeKinetic sys.mass φ) := by
      refine HasCompactSupport.intro hφc.isCompact fun r hr => ?_
      rw [freeKinetic_eq _ hφ r]
      have h0 : ∀ a : Fin eta × Fin 3, dirD a (dirD a φ) r = 0 := by
        intro a
        by_contra hne
        exact hr (tsupport_dirD_subsetC a (tsupport_dirD_subsetC a (subset_tsupport _ hne)))
      simp [h0]
    have hφL : MemLp φ 2 volume := memLp_cs hφ.continuous hφc
    have hKL : MemLp (freeKinetic sys.mass φ) 2 volume := memLp_cs hKc hKcs
    have hin : ∀ (t : Rcfg eta → ℂ) (ht : MemLp t 2 volume) (G : FreeL2 eta),
        ∫ r, conj (t r) * G r = ⟪ht.toLp t, G⟫_ℂ := by
      intro t ht G
      rw [inner_L2_eq]
      refine integral_congr_ae ?_
      filter_upwards [ht.coeFn_toLp] with r hr
      rw [hr]
    have e1 : h₁ - h₂ - (v₁ - v₂) = (h₁ - v₁) - (h₂ - v₂) := by abel
    have L1 : ∫ r, conj (φ r) * (h₁ - h₂ - (v₁ - v₂)) r =
        (∫ r, conj (φ r) * (h₁ - v₁) r) - ∫ r, conj (φ r) * (h₂ - v₂) r := by
      rw [hin φ hφL, hin φ hφL, hin φ hφL, e1, inner_sub_right]
    have L2 : ∫ r, conj (freeKinetic sys.mass φ r) * (f₁ - f₂) r =
        (∫ r, conj (freeKinetic sys.mass φ r) * f₁ r) -
          ∫ r, conj (freeKinetic sys.mass φ r) * f₂ r := by
      rw [hin _ hKL, hin _ hKL, hin _ hKL, inner_sub_right]
    rw [L1, L2]
    rw [hk₁ φ hφ hφc, hk₂ φ hφ hφc]

/-- **Conservation of the Hamiltonian norm** along a supplied strong solution `i ψ' = H_∞ ψ`:
`‖H_∞ ψ(t)‖ = ‖H_∞ ψ(0)‖`. The difference quotients `ψ(· + h) - ψ` are strong solutions, so their
norms are conserved (`norm_conserved`); their limits as `h → 0` are `‖H_∞ ψ‖`. -/
theorem norm_H_conserved (sys : CoulombSystem eta ν) (P : ν → E3) {ψ H : ℝ → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s)) (t : ℝ) : ‖H t‖ = ‖H 0‖ := by
  have hw : ∀ h : ℝ, ‖ψ (t + h) - ψ t‖ = ‖ψ (0 + h) - ψ 0‖ := by
    intro h
    have hd : ∀ s, HasDerivAt (fun s => ψ (s + h) - ψ s) (-(Complex.I • (H (s + h) - H s))) s := by
      intro s
      have h1 := (hψd (s + h)).comp_add_const s h
      have e : -(Complex.I • (H (s + h) - H s)) =
          -(Complex.I • H (s + h)) - -(Complex.I • H s) := by
        rw [smul_sub]
        abel
      rw [e]
      exact h1.sub (hψd s)
    have hH : ∀ s, HasFreeHamiltonian sys P (ψ (s + h) - ψ s) (H (s + h) - H s) := fun s =>
      HasFreeHamiltonian.sub sys P (hHam (s + h)) (hHam s)
    exact norm_conserved sys P (ψ := fun s => ψ (s + h) - ψ s) hd hH t
  have n_t := ((hψd t).tendsto_slope_zero).norm
  have n_0 := ((hψd 0).tendsto_slope_zero).norm
  have n_t' : Tendsto (fun h : ℝ => ‖h⁻¹ • (ψ (0 + h) - ψ 0)‖) (𝓝[≠] 0)
      (𝓝 ‖-(Complex.I • H t)‖) :=
    Tendsto.congr (fun h => by rw [norm_smul, norm_smul, hw h]) n_t
  have h := tendsto_nhds_unique n_t' n_0
  simpa [norm_neg, norm_smul] using h

end Conservation

end KineticLog
