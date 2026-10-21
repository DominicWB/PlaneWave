import PlaneWave.FreeBoundary.Mollification

/-!
# Free-space regularity, part 2: the weak kinetic relation gives `H²`

If `f, z ∈ L²(ℝ^{3η})` and `K f = z` weakly, `K = -(1/2) Σ_a m_a⁻¹ ∂_a²`, then `f` has weak first
and second derivatives in `L²`, with

`(Σ_a m_a⁻¹ ‖∂_a f‖²)² ≤ 4 ‖f‖² ‖z‖²` and `Σ_{a,b} m_a⁻¹ m_b⁻¹ ‖∂_a ∂_b f‖² = 4 ‖z‖²`.

The proof mollifies: `f_n = ρ_n ⋆ f` is smooth with `K f_n = ρ_n ⋆ z`; for smooth functions with
derivatives in `L²` the two energy identities `∫ conj(F) KF = (1/2) Σ_a m_a⁻¹ ‖∂_a F‖²` and
`‖KF‖² = (1/4) Σ_{a,b} m_a⁻¹ m_b⁻¹ ‖∂_b ∂_a F‖²` hold (integration by parts on `ℝ^{3η}`), and
applied to `f_n - f_k` they make `∂ f_n` and `∂² f_n` Cauchy in `L²`.

* `ibp_conj`: integration by parts with integrable products;
* `energy_one`, `energy_two`: the energy identities;
* `energy_moll`: the energy estimates for a mollification;
* **`weak_kinetic_regularity`**: the theorem.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology Convolution Pointwise
open Finset Set MeasureTheory Filter

namespace FreeBoundary

variable {eta : ℕ}

/-! ## Integration by parts -/

section Parts

lemma memLp_conj_fun {G : Rcfg eta → ℂ} (hG : MemLp G 2 volume) :
    MemLp (fun x => conj (G x)) 2 volume :=
  hG.mono (Complex.continuous_conj.comp_aestronglyMeasurable hG.1)
    (ae_of_all _ fun x => by simp)

lemma integrable_conj_mul_of_memLp {F G : Rcfg eta → ℂ} (hF : MemLp F 2 volume)
    (hG : MemLp G 2 volume) : Integrable (fun x => conj (F x) * G x) :=
  (memLp_conj_fun hF).integrable_mul hG

/-- **Integration by parts on `ℝ^{3η}`**, with integrable products:
`∫ conj(F) ∂_a G = -∫ conj(∂_a F) G`. -/
lemma ibp_conj {F G : Rcfg eta → ℂ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (a : Fin eta × Fin 3) (h1 : Integrable fun x => conj (dirD a F x) * G x)
    (h2 : Integrable fun x => conj (F x) * dirD a G x)
    (h3 : Integrable fun x => conj (F x) * G x) :
    ∫ x, conj (F x) * dirD a G x = -∫ x, conj (dirD a F x) * G x := by
  have hc : ∀ x, fderiv ℝ (fun y => conj (F y)) x (Pi.single a 1) = conj (dirD a F x) :=
    fun x => fderiv_conj_apply (hF x) _
  have h1' : Integrable fun x => fderiv ℝ (fun y => conj (F y)) x (Pi.single a 1) * G x := by
    simp_rw [hc]
    exact h1
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun x => conj (F x)) (g := G) (v := Pi.single a 1) h1' h2 h3
    (fun x _ => (hF x).star) (fun x _ => hG x)
  simp_rw [hc] at h
  exact h

end Parts

/-! ## The energy identities -/

section Energy

variable {F : Rcfg eta → ℂ}

/-- **The first energy identity**: `∫ conj(F) KF = (1/2) Σ_a m_a⁻¹ ∫ |∂_a F|²`. -/
lemma energy_one (m : Fin eta → ℝ) (hF : ContDiff ℝ 2 F) (h0 : MemLp F 2 volume)
    (h1 : ∀ a, MemLp (dirD a F) 2 volume) (h2 : ∀ a, MemLp (dirD a (dirD a F)) 2 volume) :
    ∫ x, conj (F x) * freeKinetic m F x =
      (((1 / 2) * ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ∫ x, ‖dirD a F x‖ ^ 2 : ℝ) : ℂ) := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hd1 : ∀ a, Differentiable ℝ (dirD a F) := fun a =>
    (contDiff_dirD hF a).differentiable (by norm_num)
  have hibp : ∀ a, ∫ x, conj (F x) * dirD a (dirD a F) x =
      -(((∫ x, ‖dirD a F x‖ ^ 2 : ℝ)) : ℂ) := by
    intro a
    rw [ibp_conj hd (hd1 a) a (integrable_conj_mul_of_memLp (h1 a) (h1 a))
      (integrable_conj_mul_of_memLp h0 (h2 a)) (integrable_conj_mul_of_memLp h0 (h1 a)),
      ← integral_complex_ofReal]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact conj_mul_self_eq _
  have hint : ∀ a : Fin eta × Fin 3, Integrable fun x => conj (F x) * dirD a (dirD a F) x :=
    fun a => integrable_conj_mul_of_memLp h0 (h2 a)
  have e : (fun x => conj (F x) * freeKinetic m F x) = fun x => (-(1 / 2 : ℂ)) *
      ∑ a : Fin eta × Fin 3, ((m a.1 : ℂ))⁻¹ * (conj (F x) * dirD a (dirD a F) x) := by
    funext x
    rw [freeKinetic_eq m hF x, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e, integral_const_mul, integral_finsetSum _ fun a _ => (hint a).const_mul _]
  simp_rw [integral_const_mul, hibp]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

lemma conj_dd_dd (hF : ContDiff ℝ 3 F) (h1 : ∀ a, MemLp (dirD a F) 2 volume)
    (h2 : ∀ a b, MemLp (dirD b (dirD a F)) 2 volume)
    (h3 : ∀ a b c, MemLp (dirD c (dirD b (dirD a F))) 2 volume) (a b : Fin eta × Fin 3) :
    ∫ x, conj (dirD a (dirD a F) x) * dirD b (dirD b F) x =
      ((∫ x, ‖dirD b (dirD a F) x‖ ^ 2 : ℝ) : ℂ) := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hF1 : ∀ c, ContDiff ℝ 2 (dirD c F) := fun c => contDiff_dirD_nat (n := 2) hF c
  have hd1 : Differentiable ℝ (dirD a F) := (hF1 a).differentiable (by norm_num)
  have hdbb : Differentiable ℝ (dirD b (dirD b F)) :=
    (contDiff_dirD (hF1 b) b).differentiable (by norm_num)
  have hdba : Differentiable ℝ (dirD b (dirD a F)) :=
    (contDiff_dirD (hF1 a) b).differentiable (by norm_num)
  -- `∂_a ∂_b ∂_b F = ∂_b ∂_b ∂_a F`
  have c1 : dirD a (dirD b (dirD b F)) = dirD b (dirD a (dirD b F)) := dirD_comm (hF1 b) a b
  have c2 : dirD a (dirD b F) = dirD b (dirD a F) := dirD_comm hF2 a b
  have s1 := ibp_conj hd1 hdbb a (integrable_conj_mul_of_memLp (h2 a a) (h2 b b))
    (integrable_conj_mul_of_memLp (h1 a) (by rw [c1, c2]; exact h3 a b b))
    (integrable_conj_mul_of_memLp (h1 a) (h2 b b))
  have s3 := ibp_conj hd1 hdba b (integrable_conj_mul_of_memLp (h2 a b) (h2 a b))
    (integrable_conj_mul_of_memLp (h1 a) (h3 a b b))
    (integrable_conj_mul_of_memLp (h1 a) (h2 a b))
  rw [c1, c2] at s1
  have hs : ∫ x, conj (dirD a (dirD a F) x) * dirD b (dirD b F) x =
      ∫ x, conj (dirD b (dirD a F) x) * dirD b (dirD a F) x := by
    linear_combination s1 - s3
  rw [hs, ← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  exact conj_mul_self_eq _

/-- **The second energy identity**: `‖KF‖² = (1/4) Σ_{a,b} m_a⁻¹ m_b⁻¹ ‖∂_b ∂_a F‖²`. -/
lemma energy_two (m : Fin eta → ℝ) (hF : ContDiff ℝ 3 F) (h1 : ∀ a, MemLp (dirD a F) 2 volume)
    (h2 : ∀ a b, MemLp (dirD b (dirD a F)) 2 volume)
    (h3 : ∀ a b c, MemLp (dirD c (dirD b (dirD a F))) 2 volume) :
    ∫ x, ‖freeKinetic m F x‖ ^ 2 = (1 / 4) * ∑ a : Fin eta × Fin 3, ∑ b : Fin eta × Fin 3,
      (m a.1)⁻¹ * (m b.1)⁻¹ * ∫ x, ‖dirD b (dirD a F) x‖ ^ 2 := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hint : ∀ a b : Fin eta × Fin 3,
      Integrable fun x => conj (dirD a (dirD a F) x) * dirD b (dirD b F) x :=
    fun a b => integrable_conj_mul_of_memLp (h2 a a) (h2 b b)
  have e : (fun x => (((‖freeKinetic m F x‖ ^ 2 : ℝ)) : ℂ)) = fun x =>
      (1 / 4 : ℂ) * ∑ a : Fin eta × Fin 3, ∑ b : Fin eta × Fin 3,
        ((m a.1 : ℂ))⁻¹ * ((m b.1 : ℂ))⁻¹ *
          (conj (dirD a (dirD a F) x) * dirD b (dirD b F) x) := by
    funext x
    rw [← conj_mul_self_eq, freeKinetic_eq m hF2 x]
    simp only [map_mul, map_neg, map_div₀, map_one, map_ofNat, map_sum, map_inv₀,
      Complex.conj_ofReal]
    have hst : ∀ S T : ℂ, (-(1 / 2) * S) * (-(1 / 2) * T) = 1 / 4 * (S * T) := fun S T => by
      ring
    rw [hst, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have h := congrArg (fun x : Rcfg eta → ℂ => ∫ y, x y) e
  rw [integral_complex_ofReal, integral_const_mul,
    integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _] at h
  simp_rw [integral_finsetSum _ fun b _ => (hint _ b).const_mul _, integral_const_mul,
    conj_dd_dd hF h1 h2 h3] at h
  have h' : (((∫ x, ‖freeKinetic m F x‖ ^ 2 : ℝ)) : ℂ) =
      (((1 / 4) * ∑ a : Fin eta × Fin 3, ∑ b : Fin eta × Fin 3,
        (m a.1)⁻¹ * (m b.1)⁻¹ * ∫ x, ‖dirD b (dirD a F) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [h]
    push_cast
    rfl
  exact_mod_cast h'

end Energy

/-! ## The energy estimates for a mollification -/

section MollEnergy

lemma dirD_sub_fun' {F G : Rcfg eta → ℝ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (a : Fin eta × Fin 3) : dirD a (fun x => F x - G x) = fun x => dirD a F x - dirD a G x := by
  funext x
  unfold dirD
  rw [fderiv_fun_sub (hF x) (hG x)]
  rfl

lemma moll_sub_kernel {τ₁ τ₂ : Rcfg eta → ℝ} (h1c : HasCompactSupport τ₁) (h1 : Continuous τ₁)
    (h2c : HasCompactSupport τ₂) (h2 : Continuous τ₂) (f : FreeL2 eta) (x : Rcfg eta) :
    moll (fun y => τ₁ y - τ₂ y) f x = moll τ₁ f x - moll τ₂ f x := by
  rw [moll_apply, moll_apply, moll_apply, ← integral_sub (integrable_kernel_mul h1c h1 f x)
    (integrable_kernel_mul h2c h2 f x)]
  congr 1
  funext t
  push_cast
  ring

variable {σ : Rcfg eta → ℝ}

lemma memLp_moll_k (hσc : HasCompactSupport σ) (hσ : Continuous σ) (f : FreeL2 eta) :
    MemLp (moll σ f) 2 volume := (memLp_moll hσc hσ f).1

/-- The derivatives of a mollification by a `C³` kernel, up to order three. -/
lemma moll_derivs (hσ : ContDiff ℝ 3 σ) (hσc : HasCompactSupport σ) (f : FreeL2 eta) :
    (∀ a, dirD a (moll σ f) = moll (dirD a σ) f) ∧
    (∀ a b, dirD b (dirD a (moll σ f)) = moll (dirD b (dirD a σ)) f) ∧
    (∀ a b c, dirD c (dirD b (dirD a (moll σ f))) = moll (dirD c (dirD b (dirD a σ))) f) := by
  have hf := locInt_L2 f
  have c1 : ∀ a, ContDiff ℝ 2 (dirD a σ) := fun a => contDiff_dirD_nat (n := 2) hσ a
  have c2 : ∀ a b, ContDiff ℝ 1 (dirD b (dirD a σ)) := fun a b =>
    contDiff_dirD_nat (n := 1) (c1 a) b
  have s1 : ∀ a, HasCompactSupport (dirD a σ) := fun a => hasCompactSupport_dirD hσc a
  have s2 : ∀ a b, HasCompactSupport (dirD b (dirD a σ)) := fun a b =>
    hasCompactSupport_dirD (s1 a) b
  have d1 : ∀ a, dirD a (moll σ f) = moll (dirD a σ) f := fun a =>
    dirD_moll hσc (hσ.of_le (by norm_num)) hf a
  have d2 : ∀ a b, dirD b (dirD a (moll σ f)) = moll (dirD b (dirD a σ)) f := fun a b => by
    rw [d1 a, dirD_moll (s1 a) ((c1 a).of_le (by norm_num)) hf b]
  refine ⟨d1, d2, fun a b c => ?_⟩
  rw [d2 a b, dirD_moll (s2 a b) (c2 a b) hf c]

/-- **The energy estimates for `F = σ ⋆ f`** when `K f = z` weakly:
`(Σ_a m_a⁻¹ ‖∂_a F‖²)² ≤ 4 ‖F‖² ‖σ ⋆ z‖²` and `Σ_{a,b} m_a⁻¹ m_b⁻¹ ‖∂_b ∂_a F‖² = 4 ‖σ ⋆ z‖²`. -/
lemma energy_moll {m : Fin eta → ℝ} (hm : ∀ i, 0 < m i) {f z : FreeL2 eta}
    (hK : HasFreeWeakKinetic m f z) (hσ : ContDiff ℝ 3 σ) (hσc : HasCompactSupport σ) :
    (∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ∫ x, ‖moll (dirD a σ) f x‖ ^ 2) ^ 2 ≤
        4 * (∫ x, ‖moll σ f x‖ ^ 2) * ∫ x, ‖moll σ z x‖ ^ 2 ∧
      ∑ a : Fin eta × Fin 3, ∑ b : Fin eta × Fin 3,
        (m a.1)⁻¹ * (m b.1)⁻¹ * ∫ x, ‖moll (dirD b (dirD a σ)) f x‖ ^ 2 =
        4 * ∫ x, ‖moll σ z x‖ ^ 2 := by
  obtain ⟨d1, d2, d3⟩ := moll_derivs hσ hσc f
  have hf := locInt_L2 f
  have c1 : ∀ a, ContDiff ℝ 2 (dirD a σ) := fun a => contDiff_dirD_nat (n := 2) hσ a
  have c2 : ∀ a b, ContDiff ℝ 1 (dirD b (dirD a σ)) := fun a b =>
    contDiff_dirD_nat (n := 1) (c1 a) b
  have s1 : ∀ a, HasCompactSupport (dirD a σ) := fun a => hasCompactSupport_dirD hσc a
  have s2 : ∀ a b, HasCompactSupport (dirD b (dirD a σ)) := fun a b =>
    hasCompactSupport_dirD (s1 a) b
  have hF3 : ContDiff ℝ 3 (moll σ f) := contDiff_moll hσc hσ hf
  have h0 : MemLp (moll σ f) 2 volume := memLp_moll_k hσc hσ.continuous f
  have h1 : ∀ a, MemLp (dirD a (moll σ f)) 2 volume := fun a => by
    rw [d1 a]
    exact memLp_moll_k (s1 a) (c1 a).continuous f
  have h2 : ∀ a b, MemLp (dirD b (dirD a (moll σ f))) 2 volume := fun a b => by
    rw [d2 a b]
    exact memLp_moll_k (s2 a b) (c2 a b).continuous f
  have h3 : ∀ a b c, MemLp (dirD c (dirD b (dirD a (moll σ f)))) 2 volume := fun a b c => by
    rw [d3 a b c]
    exact memLp_moll_k (hasCompactSupport_dirD (s2 a b) c)
      (continuous_dirD (c2 a b) (by norm_num) c) f
  have hKF : ∀ x, freeKinetic m (moll σ f) x = moll σ z x := fun x => by
    rw [freeKinetic_moll m hσc hσ f x, moll_kin_eq hK hσc (hσ.of_le (by norm_num)) x]
  have hz : MemLp (moll σ z) 2 volume := memLp_moll_k hσc hσ.continuous z
  constructor
  · -- the first estimate
    have e1 := energy_one m (hF3.of_le (by norm_num)) h0 h1 fun a => h2 a a
    simp_rw [hKF, d1] at e1
    set S := ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ∫ x, ‖moll (dirD a σ) f x‖ ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => mul_nonneg (inv_nonneg.mpr (hm a.1).le)
      (integral_nonneg fun x => sq_nonneg _)
    have hJ : (1 / 2) * S ≤ ∫ x, ‖moll σ f x‖ * ‖moll σ z x‖ := by
      have h := norm_integral_le_integral_norm (μ := volume)
        (fun x => conj (moll σ f x) * moll σ z x)
      rw [e1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
      refine h.trans (le_of_eq ?_)
      congr 1
      funext x
      rw [norm_mul, Complex.norm_conj]
    have hCS := sq_integral_mul_le (μ := volume) (fun x => norm_nonneg (moll σ f x))
      (fun x => norm_nonneg (moll σ z x)) (h0.norm.integrable_mul hz.norm)
      ((memLp_two_iff_integrable_sq_norm h0.1).mp h0)
      ((memLp_two_iff_integrable_sq_norm hz.1).mp hz)
    have hJ0 : 0 ≤ (1 / 2) * S := by positivity
    have := pow_le_pow_left₀ hJ0 hJ 2
    nlinarith
  · -- the second estimate
    have e2 := energy_two m hF3 h1 h2 h3
    simp_rw [hKF, d2] at e2
    linarith

end MollEnergy

/-! ## The regularity theorem -/

section Regularity

lemma cauchySeq_of_sq_le {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    {u : ℕ → E} {v : ℕ → F} {C : ℝ} (hC : 0 ≤ C) (hv : CauchySeq v)
    (h : ∀ n k, ‖u n - u k‖ ^ 2 ≤ C * ‖v n - v k‖) : CauchySeq u := by
  rw [Metric.cauchySeq_iff] at hv ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hv (ε ^ 2 / (C + 1)) (by positivity)
  refine ⟨N, fun n hn k hk => ?_⟩
  have h1 := hN n hn k hk
  rw [dist_eq_norm] at h1 ⊢
  have h2 : ‖u n - u k‖ ^ 2 < ε ^ 2 := by
    calc ‖u n - u k‖ ^ 2 ≤ C * ‖v n - v k‖ := h n k
      _ ≤ C * (ε ^ 2 / (C + 1)) := mul_le_mul_of_nonneg_left h1.le hC
      _ < ε ^ 2 := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [sq_pos_of_pos hε]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).mp h2

lemma tendsto_integral_conj_mul {φ : Rcfg eta → ℂ} (hφ : MemLp φ 2 volume) {u : ℕ → FreeL2 eta}
    {F : FreeL2 eta} (hu : Tendsto u atTop (𝓝 F)) :
    Tendsto (fun n => ∫ x, conj (φ x) * u n x) atTop (𝓝 (∫ x, conj (φ x) * F x)) := by
  have e : ∀ G : FreeL2 eta, ∫ x, conj (φ x) * G x = inner ℂ (hφ.toLp φ) G := by
    intro G
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hφ] with x hx
    rw [hx, RCLike.inner_apply, mul_comm]
  simp_rw [e]
  exact tendsto_const_nhds.inner hu

/-- The derivative kernels of the mollifiers. -/
lemma rhoN_props (n : ℕ) :
    (∀ a : Fin eta × Fin 3, HasCompactSupport (dirD a (rhoN (eta := eta) n)) ∧
      Continuous (dirD a (rhoN (eta := eta) n))) ∧
    (∀ a b : Fin eta × Fin 3, HasCompactSupport (dirD a (dirD b (rhoN (eta := eta) n))) ∧
      Continuous (dirD a (dirD b (rhoN (eta := eta) n)))) := by
  have h4 : ContDiff ℝ 4 (rhoN (eta := eta) n) := contDiff_rhoN n
  refine ⟨fun a => ⟨hasCompactSupport_dirD (hasCompactSupport_rhoN n) a,
    continuous_dirD h4 (by norm_num) a⟩, fun a b => ⟨hasCompactSupport_dirD
      (hasCompactSupport_dirD (hasCompactSupport_rhoN n) b) a,
    continuous_dirD (contDiff_dirD_nat (n := 3) h4 b) (by norm_num) a⟩⟩

/-- `∂_a f_n` in `L²`. -/
noncomputable def mollD1 (f : FreeL2 eta) (a : Fin eta × Fin 3) (n : ℕ) : FreeL2 eta :=
  mollL2 (dirD a (rhoN n)) ((rhoN_props n).1 a).1 ((rhoN_props n).1 a).2 f

/-- `∂_a ∂_b f_n` in `L²`. -/
noncomputable def mollD2 (f : FreeL2 eta) (b a : Fin eta × Fin 3) (n : ℕ) : FreeL2 eta :=
  mollL2 (dirD a (dirD b (rhoN n))) ((rhoN_props n).2 a b).1 ((rhoN_props n).2 a b).2 f

/-- The kernel `ρ_n - ρ_k`. -/
noncomputable def rhoD (n k : ℕ) : Rcfg eta → ℝ := fun x => rhoN n x - rhoN k x

lemma rhoD_smooth (n k : ℕ) : ContDiff ℝ 3 (rhoD (eta := eta) n k) :=
  (contDiff_rhoN n).sub (contDiff_rhoN k)

lemma rhoD_hcs (n k : ℕ) : HasCompactSupport (rhoD (eta := eta) n k) :=
  (hasCompactSupport_rhoN n).sub (hasCompactSupport_rhoN k)

lemma dirD_rhoD (n k : ℕ) (a : Fin eta × Fin 3) :
    dirD a (rhoD (eta := eta) n k) = fun x => dirD a (rhoN n) x - dirD a (rhoN k) x :=
  dirD_sub_fun' ((contDiff_rhoN (k := 1) n).differentiable (by norm_num))
    ((contDiff_rhoN (k := 1) k).differentiable (by norm_num)) a

lemma dirD2_rhoD (n k : ℕ) (a b : Fin eta × Fin 3) :
    dirD a (dirD b (rhoD (eta := eta) n k)) =
      fun x => dirD a (dirD b (rhoN n)) x - dirD a (dirD b (rhoN k)) x := by
  rw [dirD_rhoD]
  have h4 : ∀ j : ℕ, ContDiff ℝ 4 (rhoN (eta := eta) j) := fun j => contDiff_rhoN j
  exact dirD_sub_fun' ((contDiff_dirD_nat (n := 3) (h4 n) b).differentiable (by norm_num))
    ((contDiff_dirD_nat (n := 3) (h4 k) b).differentiable (by norm_num)) a

lemma norm_sq_mollL2_sub {τ₁ τ₂ : Rcfg eta → ℝ} (h1c : HasCompactSupport τ₁) (h1 : Continuous τ₁)
    (h2c : HasCompactSupport τ₂) (h2 : Continuous τ₂) (f : FreeL2 eta) :
    ‖mollL2 τ₁ h1c h1 f - mollL2 τ₂ h2c h2 f‖ ^ 2 =
      ∫ x, ‖moll (fun y => τ₁ y - τ₂ y) f x‖ ^ 2 := by
  refine norm_sq_eq_of_ae ?_
  filter_upwards [Lp.coeFn_sub (mollL2 τ₁ h1c h1 f) (mollL2 τ₂ h2c h2 f), mollL2_ae h1c h1 f,
    mollL2_ae h2c h2 f] with x e1 e2 e3
  rw [e1, Pi.sub_apply, e2, e3, moll_sub_kernel h1c h1 h2c h2 f x]

/-- **The weak kinetic relation gives `H²`**: if `K f = z` weakly (`K = -(1/2) Σ_a m_a⁻¹ ∂_a²`,
`m_i > 0`), then `f` has weak gradient `g` and `g` has weak gradients `g2 b`, with
`(Σ_a m_a⁻¹ ‖g_a‖²)² ≤ 4 ‖f‖² ‖z‖²` and `Σ_{a,b} m_a⁻¹ m_b⁻¹ ‖g2 a b‖² = 4 ‖z‖²`. -/
theorem weak_kinetic_regularity {m : Fin eta → ℝ} (hm : ∀ i, 0 < m i) {f z : FreeL2 eta}
    (hK : HasFreeWeakKinetic m f z) :
    ∃ (g : Fin eta × Fin 3 → FreeL2 eta) (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta),
      HasWeakGrad f g ∧ (∀ b, HasWeakGrad (g b) (g2 b)) ∧
      (∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ‖g a‖ ^ 2) ^ 2 ≤ 4 * ‖f‖ ^ 2 * ‖z‖ ^ 2 ∧
      ∑ a : Fin eta × Fin 3, ∑ b : Fin eta × Fin 3, (m a.1)⁻¹ * (m b.1)⁻¹ * ‖g2 a b‖ ^ 2 =
        4 * ‖z‖ ^ 2 := by
  have hf := locInt_L2 f
  have hfn := tendsto_mollN f
  have hzn := tendsto_mollN z
  -- the energy estimates for the differences
  have hdiff : ∀ n k, (∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ‖mollD1 f a n - mollD1 f a k‖ ^ 2) ^ 2 ≤
        4 * ‖mollN n f - mollN k f‖ ^ 2 * ‖mollN n z - mollN k z‖ ^ 2 ∧
      ∑ a : Fin eta × Fin 3, ∑ b : Fin eta × Fin 3,
        (m a.1)⁻¹ * (m b.1)⁻¹ * ‖mollD2 f a b n - mollD2 f a b k‖ ^ 2 =
        4 * ‖mollN n z - mollN k z‖ ^ 2 := by
    intro n k
    obtain ⟨e1, e2⟩ := energy_moll hm hK (rhoD_smooth n k) (rhoD_hcs n k)
    have q1 : ∀ a, ‖mollD1 f a n - mollD1 f a k‖ ^ 2 =
        ∫ x, ‖moll (dirD a (rhoD n k)) f x‖ ^ 2 := fun a => by
      rw [mollD1, mollD1, norm_sq_mollL2_sub, dirD_rhoD]
    have q2 : ∀ a b, ‖mollD2 f a b n - mollD2 f a b k‖ ^ 2 =
        ∫ x, ‖moll (dirD b (dirD a (rhoD n k))) f x‖ ^ 2 := fun a b => by
      rw [mollD2, mollD2, norm_sq_mollL2_sub, dirD2_rhoD]
    have q0 : ∀ F : FreeL2 eta, ‖mollN n F - mollN k F‖ ^ 2 =
        ∫ x, ‖moll (rhoD n k) F x‖ ^ 2 := fun F => by
      rw [mollN, mollN, norm_sq_mollL2_sub]
      rfl
    simp_rw [q1, q2, q0]
    exact ⟨e1, e2⟩
  -- the energy estimates at each `n`
  have hone : ∀ n, (∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ‖mollD1 f a n‖ ^ 2) ^ 2 ≤
        4 * ‖mollN n f‖ ^ 2 * ‖mollN n z‖ ^ 2 ∧
      ∑ a : Fin eta × Fin 3, ∑ b : Fin eta × Fin 3,
        (m a.1)⁻¹ * (m b.1)⁻¹ * ‖mollD2 f a b n‖ ^ 2 = 4 * ‖mollN n z‖ ^ 2 := by
    intro n
    obtain ⟨e1, e2⟩ := energy_moll hm hK (contDiff_rhoN (k := 3) n) (hasCompactSupport_rhoN n)
    have q1 : ∀ a, ‖mollD1 f a n‖ ^ 2 = ∫ x, ‖moll (dirD a (rhoN n)) f x‖ ^ 2 := fun a =>
      norm_sq_eq_of_ae (mollL2_ae _ _ f)
    have q2 : ∀ a b, ‖mollD2 f a b n‖ ^ 2 = ∫ x, ‖moll (dirD b (dirD a (rhoN n))) f x‖ ^ 2 :=
      fun a b => norm_sq_eq_of_ae (mollL2_ae _ _ f)
    have q0 : ∀ F : FreeL2 eta, ‖mollN n F‖ ^ 2 = ∫ x, ‖moll (rhoN n) F x‖ ^ 2 := fun F =>
      norm_sq_eq_of_ae (mollN_ae n F)
    simp_rw [q1, q2, q0]
    exact ⟨e1, e2⟩
  -- Cauchy sequences
  have hzb : ∀ n k, ‖mollN n z - mollN k z‖ ≤ 2 * ‖z‖ := fun n k =>
    (norm_sub_le _ _).trans (by linarith [norm_mollN_le n z, norm_mollN_le k z])
  have hc1 : ∀ a, CauchySeq (mollD1 f a) := by
    intro a
    refine cauchySeq_of_sq_le (C := 4 * m a.1 * ‖z‖) (by have := hm a.1; positivity)
      hfn.cauchySeq fun n k => ?_
    obtain ⟨e1, -⟩ := hdiff n k
    set X := ‖mollD1 f a n - mollD1 f a k‖ ^ 2
    have hX : (m a.1)⁻¹ * X ≤ ∑ a' : Fin eta × Fin 3, (m a'.1)⁻¹ *
        ‖mollD1 f a' n - mollD1 f a' k‖ ^ 2 :=
      Finset.single_le_sum (f := fun a' => (m a'.1)⁻¹ * ‖mollD1 f a' n - mollD1 f a' k‖ ^ 2)
        (fun a' _ => mul_nonneg (inv_nonneg.mpr (hm a'.1).le) (sq_nonneg _)) (Finset.mem_univ a)
    have hma := hm a.1
    have hX0 : 0 ≤ (m a.1)⁻¹ * X := by positivity
    have h1 : ((m a.1)⁻¹ * X) ^ 2 ≤ 4 * ‖mollN n f - mollN k f‖ ^ 2 * (2 * ‖z‖) ^ 2 :=
      (pow_le_pow_left₀ hX0 hX 2).trans (e1.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hzb n k) 2) (by positivity)))
    have h2 : (m a.1)⁻¹ * X ≤ 2 * ‖mollN n f - mollN k f‖ * (2 * ‖z‖) := by
      have h3 : (2 * ‖mollN n f - mollN k f‖ * (2 * ‖z‖)) ^ 2 =
          4 * ‖mollN n f - mollN k f‖ ^ 2 * (2 * ‖z‖) ^ 2 := by ring
      rw [← h3] at h1
      exact (pow_le_pow_iff_left₀ hX0 (by positivity) two_ne_zero).mp h1
    have h4 : X = m a.1 * ((m a.1)⁻¹ * X) := by field_simp
    rw [h4]
    calc m a.1 * ((m a.1)⁻¹ * X) ≤ m a.1 * (2 * ‖mollN n f - mollN k f‖ * (2 * ‖z‖)) :=
          mul_le_mul_of_nonneg_left h2 hma.le
      _ = 4 * m a.1 * ‖z‖ * ‖mollN n f - mollN k f‖ := by ring
  have hc2 : ∀ a b, CauchySeq (mollD2 f a b) := by
    intro a b
    refine cauchySeq_of_sq_le (C := 8 * m a.1 * m b.1 * ‖z‖)
      (by have := hm a.1; have := hm b.1; positivity) hzn.cauchySeq fun n k => ?_
    obtain ⟨-, e2⟩ := hdiff n k
    set X := ‖mollD2 f a b n - mollD2 f a b k‖ ^ 2
    have hX : (m a.1)⁻¹ * (m b.1)⁻¹ * X ≤ 4 * ‖mollN n z - mollN k z‖ ^ 2 := by
      rw [← e2]
      have hin := Finset.single_le_sum (f := fun b' => (m a.1)⁻¹ * (m b'.1)⁻¹ *
        ‖mollD2 f a b' n - mollD2 f a b' k‖ ^ 2) (fun b' _ => mul_nonneg (mul_nonneg
          (inv_nonneg.mpr (hm a.1).le) (inv_nonneg.mpr (hm b'.1).le)) (sq_nonneg _))
          (Finset.mem_univ b)
      refine hin.trans (Finset.single_le_sum (f := fun a' => ∑ b' : Fin eta × Fin 3,
        (m a'.1)⁻¹ * (m b'.1)⁻¹ * ‖mollD2 f a' b' n - mollD2 f a' b' k‖ ^ 2)
        (fun a' _ => Finset.sum_nonneg fun b' _ => mul_nonneg (mul_nonneg
          (inv_nonneg.mpr (hm a'.1).le) (inv_nonneg.mpr (hm b'.1).le)) (sq_nonneg _))
          (Finset.mem_univ a))
    have hma := hm a.1
    have hmb := hm b.1
    have h4 : X = m a.1 * m b.1 * ((m a.1)⁻¹ * (m b.1)⁻¹ * X) := by field_simp
    rw [h4]
    have h5 : ‖mollN n z - mollN k z‖ ^ 2 ≤ 2 * ‖z‖ * ‖mollN n z - mollN k z‖ := by
      have := hzb n k
      nlinarith [norm_nonneg (mollN n z - mollN k z)]
    calc m a.1 * m b.1 * ((m a.1)⁻¹ * (m b.1)⁻¹ * X)
        ≤ m a.1 * m b.1 * (4 * ‖mollN n z - mollN k z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ ≤ m a.1 * m b.1 * (4 * (2 * ‖z‖ * ‖mollN n z - mollN k z‖)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 8 * m a.1 * m b.1 * ‖z‖ * ‖mollN n z - mollN k z‖ := by ring
  -- the limits
  choose g hg using fun a => cauchySeq_tendsto_of_complete (hc1 a)
  choose g2' hg2' using fun a b => cauchySeq_tendsto_of_complete (hc2 a b)
  -- `g2 b a = lim ∂_a ∂_b f_n = lim mollD2 f b a n`
  refine ⟨g, fun b a => g2' b a, ?_, ?_, ?_, ?_⟩
  · -- `HasWeakGrad f g`
    intro φ hφ hφc a
    have hφL : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφc
    have hdφ : Continuous (dirD a φ) := continuous_dirD hφ (by norm_num) a
    have hdφL : MemLp (dirD a φ) 2 volume :=
      hdφ.memLp_of_hasCompactSupport (hasCompactSupport_dirD hφc a)
    have hn : ∀ n, ∫ x, conj (φ x) * mollD1 f a n x = -∫ x, conj (dirD a φ x) * mollN n f x := by
      intro n
      have hG : ContDiff ℝ 1 (moll (rhoN n) f) := contDiff_moll (hasCompactSupport_rhoN n)
        (contDiff_rhoN n) hf
      have e1 : ∫ x, conj (φ x) * mollD1 f a n x =
          ∫ x, conj (φ x) * dirD a (moll (rhoN n) f) x := by
        rw [dirD_moll (hasCompactSupport_rhoN n) (contDiff_rhoN n) hf a]
        refine integral_congr_ae ?_
        filter_upwards [mollL2_ae ((rhoN_props (eta := eta) n).1 a).1
          ((rhoN_props (eta := eta) n).1 a).2 f] with x hx
        rw [mollD1, hx]
      have e2 : ∫ x, conj (dirD a φ x) * mollN n f x =
          ∫ x, conj (dirD a φ x) * moll (rhoN n) f x := by
        refine integral_congr_ae ?_
        filter_upwards [mollN_ae n f] with x hx
        rw [hx]
      have hGL : MemLp (moll (rhoN n) f) 2 volume :=
        memLp_moll_k (hasCompactSupport_rhoN n) (continuous_rhoN n) f
      have hdGL : MemLp (dirD a (moll (rhoN n) f)) 2 volume := by
        rw [dirD_moll (hasCompactSupport_rhoN n) (contDiff_rhoN n) hf a]
        exact memLp_moll_k ((rhoN_props n).1 a).1 ((rhoN_props n).1 a).2 f
      rw [e1, e2]
      exact ibp_conj (hφ.differentiable (by norm_num)) (hG.differentiable (by norm_num)) a
        (integrable_conj_mul_of_memLp hdφL hGL) (integrable_conj_mul_of_memLp hφL hdGL)
        (integrable_conj_mul_of_memLp hφL hGL)
    have t1 := tendsto_integral_conj_mul hφL (hg a)
    have t2 := (tendsto_integral_conj_mul hdφL hfn).neg
    exact tendsto_nhds_unique t1 (t2.congr fun n => (hn n).symm)
  · -- `HasWeakGrad (g b) (g2 b)`
    intro b φ hφ hφc a
    have hφL : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφc
    have hdφ : Continuous (dirD a φ) := continuous_dirD hφ (by norm_num) a
    have hdφL : MemLp (dirD a φ) 2 volume :=
      hdφ.memLp_of_hasCompactSupport (hasCompactSupport_dirD hφc a)
    have hn : ∀ n, ∫ x, conj (φ x) * mollD2 f b a n x =
        -∫ x, conj (dirD a φ x) * mollD1 f b n x := by
      intro n
      obtain ⟨d1, d2, -⟩ := moll_derivs (contDiff_rhoN (k := 3) n) (hasCompactSupport_rhoN n) f
      have hG : ContDiff ℝ 1 (dirD b (moll (rhoN n) f)) := by
        rw [d1 b]
        exact contDiff_moll (hasCompactSupport_dirD (hasCompactSupport_rhoN n) b)
          (contDiff_dirD_nat (n := 1) (contDiff_rhoN (k := 2) n) b) hf
      have e1 : ∫ x, conj (φ x) * mollD2 f b a n x =
          ∫ x, conj (φ x) * dirD a (dirD b (moll (rhoN n) f)) x := by
        rw [d2 b a]
        refine integral_congr_ae ?_
        filter_upwards [mollL2_ae ((rhoN_props (eta := eta) n).2 a b).1
          ((rhoN_props (eta := eta) n).2 a b).2 f] with x hx
        rw [mollD2, hx]
      have e2 : ∫ x, conj (dirD a φ x) * mollD1 f b n x =
          ∫ x, conj (dirD a φ x) * dirD b (moll (rhoN n) f) x := by
        rw [d1 b]
        refine integral_congr_ae ?_
        filter_upwards [mollL2_ae ((rhoN_props (eta := eta) n).1 b).1
          ((rhoN_props (eta := eta) n).1 b).2 f] with x hx
        rw [mollD1, hx]
      have hGL : MemLp (dirD b (moll (rhoN n) f)) 2 volume := by
        rw [d1 b]
        exact memLp_moll_k ((rhoN_props n).1 b).1 ((rhoN_props n).1 b).2 f
      have hdGL : MemLp (dirD a (dirD b (moll (rhoN n) f))) 2 volume := by
        rw [d2 b a]
        exact memLp_moll_k ((rhoN_props n).2 a b).1 ((rhoN_props n).2 a b).2 f
      rw [e1, e2]
      exact ibp_conj (hφ.differentiable (by norm_num)) (hG.differentiable (by norm_num)) a
        (integrable_conj_mul_of_memLp hdφL hGL) (integrable_conj_mul_of_memLp hφL hdGL)
        (integrable_conj_mul_of_memLp hφL hGL)
    have t1 := tendsto_integral_conj_mul hφL (hg2' b a)
    have t2 := (tendsto_integral_conj_mul hdφL (hg b)).neg
    exact tendsto_nhds_unique t1 (t2.congr fun n => (hn n).symm)
  · -- the first bound
    have tl : Tendsto (fun n => (∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ‖mollD1 f a n‖ ^ 2) ^ 2)
        atTop (𝓝 ((∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ‖g a‖ ^ 2) ^ 2)) :=
      (tendsto_finsetSum _ fun a _ => ((hg a).norm.pow 2).const_mul _).pow 2
    have tr : Tendsto (fun n => 4 * ‖mollN n f‖ ^ 2 * ‖mollN n z‖ ^ 2) atTop
        (𝓝 (4 * ‖f‖ ^ 2 * ‖z‖ ^ 2)) :=
      ((hfn.norm.pow 2).const_mul 4).mul (hzn.norm.pow 2)
    exact le_of_tendsto_of_tendsto' tl tr fun n => (hone n).1
  · -- the second bound
    have tl : Tendsto (fun n => ∑ a : Fin eta × Fin 3, ∑ b : Fin eta × Fin 3,
        (m a.1)⁻¹ * (m b.1)⁻¹ * ‖mollD2 f a b n‖ ^ 2) atTop
        (𝓝 (∑ a : Fin eta × Fin 3, ∑ b : Fin eta × Fin 3,
          (m a.1)⁻¹ * (m b.1)⁻¹ * ‖g2' a b‖ ^ 2)) :=
      tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
        ((hg2' a b).norm.pow 2).const_mul _
    have tr : Tendsto (fun n => 4 * ‖mollN n z‖ ^ 2) atTop (𝓝 (4 * ‖z‖ ^ 2)) :=
      (hzn.norm.pow 2).const_mul 4
    exact tendsto_nhds_unique (tl.congr fun n => (hone n).2) tr

end Regularity

end FreeBoundary
