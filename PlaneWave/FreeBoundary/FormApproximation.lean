import PlaneWave.FreeBoundary.CoulombForm

/-!
# Free-space regularity, part 7: smooth approximation in the form norm

An `L²` function `ψ` of an exchange sector with a weak gradient `g` is approximated by smooth
functions of compact support of the same sector: `φ_n = χ_n · (σ_n ⋆ ψ)`, `σ_n(y) = Π_a k_n(y_a)` a
product of one-dimensional mollifiers (invariant under exchanges of particles) and
`χ_n(r) = F(|r|²/(n+1)²)` a cutoff. Then `φ_n → ψ` and `∂_a φ_n → g_a` in `L²`.

* `sigN`, `tendsto_sigL2`: the product mollifiers and the approximation of the identity;
* `measurePreserving_freeSwap`, `moll_freeSwap`: mollification preserves the sector;
* `cutN`, `abs_dirD_cutN_le`: the cutoffs;
* `apprN`, **`apprN_tendsto`**: the approximants and their convergence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology ENNReal Convolution Pointwise
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

variable {eta : ℕ}

/-! ## Product mollifiers -/

section Kernel

/-- The one-dimensional bump of radii `1/(2(n+1))` and `1/(n+1)`. -/
noncomputable def bump1N (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) h]
    linarith

/-- The one-dimensional mollifier `k_n`. -/
noncomputable def kN (n : ℕ) : ℝ → ℝ := (bump1N n).normed volume

/-- The product mollifier `σ_n(y) = Π_a k_n(y_a)`. -/
noncomputable def sigN (n : ℕ) (y : Rcfg eta) : ℝ := ∏ a : Fin eta × Fin 3, kN n (y a)

lemma contDiff_sigN (n : ℕ) {k : ℕ∞} : ContDiff ℝ k (sigN (eta := eta) n) :=
  contDiff_prod fun a _ => (bump1N n).contDiff_normed.comp (contDiff_apply ℝ ℝ a)

lemma continuous_sigN (n : ℕ) : Continuous (sigN (eta := eta) n) :=
  (contDiff_sigN n (k := 0)).continuous

lemma sigN_nonneg (n : ℕ) (y : Rcfg eta) : 0 ≤ sigN n y :=
  Finset.prod_nonneg fun _ _ => (bump1N n).nonneg_normed _

lemma support_sigN (n : ℕ) :
    Function.support (sigN (eta := eta) n) ⊆ Metric.ball 0 (1 / ((n : ℝ) + 1)) := by
  intro y hy
  rw [Function.mem_support] at hy
  have h : ∀ a, kN n (y a) ≠ 0 := fun a h0 => hy (Finset.prod_eq_zero (Finset.mem_univ a) h0)
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by positivity)]
  intro a
  have hm : y a ∈ Function.support (kN n) := Function.mem_support.mpr (h a)
  rw [kN, (bump1N n).support_normed_eq, Metric.mem_ball, dist_zero_right] at hm
  exact hm

lemma hasCompactSupport_sigN (n : ℕ) : HasCompactSupport (sigN (eta := eta) n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Rcfg eta) (1 / ((n : ℝ) + 1)))
    fun y hy => ?_
  by_contra h
  exact hy (Metric.ball_subset_closedBall (support_sigN n (Function.mem_support.mpr h)))

lemma integral_sigN (n : ℕ) : ∫ y, sigN (eta := eta) n y = 1 := by
  unfold sigN
  rw [integral_fintype_prod_volume_eq_prod (fun _ : Fin eta × Fin 3 => kN n)]
  simp [kN, (bump1N n).integral_normed]

lemma sigN_freeSwap (n : ℕ) (i j : Fin eta) (y : Rcfg eta) :
    sigN n (freeSwap i j y) = sigN n y := by
  unfold sigN freeSwap
  exact Fintype.prod_equiv ((Equiv.swap i j).prodCongr (Equiv.refl _)) _ _ fun a => rfl

/-- `σ_n ⋆ f` as an element of `L²`. -/
noncomputable def sigL2 (n : ℕ) (f : FreeL2 eta) : FreeL2 eta :=
  mollL2 (sigN n) (hasCompactSupport_sigN n) (continuous_sigN n) f

lemma sigL2_ae (n : ℕ) (f : FreeL2 eta) :
    (sigL2 n f : Rcfg eta → ℂ) =ᵐ[volume] moll (sigN n) f :=
  mollL2_ae _ _ f

lemma norm_sigL2_le (n : ℕ) (f : FreeL2 eta) : ‖sigL2 n f‖ ≤ ‖f‖ := by
  have := norm_mollL2_le (hasCompactSupport_sigN (eta := eta) n) (continuous_sigN n) f
  have e : ∫ t, |sigN (eta := eta) n t| = 1 := by
    rw [← integral_sigN n]
    exact integral_congr_ae (ae_of_all _ fun t => abs_of_nonneg (sigN_nonneg n t))
  rwa [e, one_mul] at this

lemma sigL2_sub (n : ℕ) (f g : FreeL2 eta) : sigL2 n (f - g) = sigL2 n f - sigL2 n g :=
  mollL2_sub _ _ f g

/-- **The approximation of the identity** for the product mollifiers: `σ_n ⋆ f → f` in `L²`. -/
theorem tendsto_sigL2 (f : FreeL2 eta) : Tendsto (fun n => sigL2 n f) atTop (𝓝 f) := by
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
  have hpt : ∀ x, ‖moll (sigN n) ψ x - ψ x‖ ≤ η := by
    intro x
    rw [← dist_eq_norm, moll_eq_conv]
    exact dist_convolution_le hη.le (support_sigN n) (sigN_nonneg n) (integral_sigN n)
      hψcont.aestronglyMeasurable fun y hy =>
        (hψδ (lt_trans (Metric.mem_ball.mp hy) hrδ)).le
  have hzero : ∀ x, x ∉ K → moll (sigN n) ψ x - ψ x = 0 := by
    intro x hx
    have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hsub h)
    rw [hψx, sub_zero, moll_apply]
    refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
    by_cases hρ : sigN (eta := eta) n (x - t) = 0
    · simp [hρ]
    · have hb : x - t ∈ Metric.ball (0 : Rcfg eta) (1 / ((n : ℝ) + 1)) :=
        support_sigN n (Function.mem_support.mpr hρ)
      by_cases hψt : ψ t = 0
      · simp [hψt]
      · exfalso
        apply hx
        have h1 : t ∈ tsupport ψ := subset_tsupport ψ hψt
        have h2 : x - t ∈ Metric.closedBall (0 : Rcfg eta) 1 :=
          Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hb).le.trans hr1.le)
        have := Set.add_mem_add h1 h2
        simpa using this
  have hdiff : (⇑(sigL2 n Ψ - Ψ) : Rcfg eta → ℂ) =ᵐ[volume]
      fun x => moll (sigN n) ψ x - ψ x := by
    filter_upwards [Lp.coeFn_sub (sigL2 n Ψ) Ψ, sigL2_ae n Ψ, hΨ] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, moll_congr_ae (sigN n) hΨ]
  have hsmall : ‖sigL2 n Ψ - Ψ‖ ≤ ε / 4 := by
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
  have hfn : ‖sigL2 n (f - Ψ)‖ ≤ ε / 4 := (norm_sigL2_le n _).trans hfΨ
  rw [dist_eq_norm]
  have e : sigL2 n f - f = sigL2 n (f - Ψ) + (sigL2 n Ψ - Ψ) + (Ψ - f) := by
    rw [sigL2_sub]
    abel
  rw [e]
  have h3 : ‖Ψ - f‖ ≤ ε / 4 := by rw [norm_sub_rev]; exact hfΨ
  calc ‖sigL2 n (f - Ψ) + (sigL2 n Ψ - Ψ) + (Ψ - f)‖
      ≤ ‖sigL2 n (f - Ψ)‖ + ‖sigL2 n Ψ - Ψ‖ + ‖Ψ - f‖ := norm_add₃_le
    _ ≤ ε / 4 + ε / 4 + ε / 4 := by gcongr
    _ < ε := by linarith

end Kernel

/-! ## Exchanges -/

section Swap

lemma freeSwap_eq_arrowCongr (i j : Fin eta) :
    (MeasurableEquiv.arrowCongr' ((Equiv.swap i j).prodCongr (Equiv.refl (Fin 3))).symm
      (MeasurableEquiv.refl ℝ) : Rcfg eta → Rcfg eta) = freeSwap i j := by
  funext r a
  rfl

lemma measurePreserving_freeSwap (i j : Fin eta) :
    MeasurePreserving (freeSwap i j) (volume : Measure (Rcfg eta)) volume := by
  have h := measurePreserving_arrowCongr' (fun _ : Fin eta × Fin 3 => (volume : Measure ℝ))
    (fun _ : Fin eta × Fin 3 => (volume : Measure ℝ))
    ((Equiv.swap i j).prodCongr (Equiv.refl (Fin 3))).symm (MeasurableEquiv.refl ℝ)
    (fun _ => MeasurePreserving.id _)
  rw [freeSwap_eq_arrowCongr] at h
  exact h

lemma measurableEmbedding_freeSwap (i j : Fin eta) :
    MeasurableEmbedding (freeSwap (eta := eta) i j) := by
  rw [← freeSwap_eq_arrowCongr]
  exact MeasurableEquiv.measurableEmbedding _

/-- **Mollification preserves the sector**: for a kernel invariant under the exchange of `i` and
`j`, `(ρ ⋆ f)(x^{ij}) = s (ρ ⋆ f)(x)` when `f(x^{ij}) = s f(x)` almost everywhere. -/
lemma moll_freeSwap {ρ : Rcfg eta → ℝ} {i j : Fin eta} (hρ : ∀ y, ρ (freeSwap i j y) = ρ y)
    {f : Rcfg eta → ℂ} {s : ℂ} (hf : ∀ᵐ r, f (freeSwap i j r) = s * f r) (x : Rcfg eta) :
    moll ρ f (freeSwap i j x) = s * moll ρ f x := by
  rw [moll_apply, moll_apply, ← (measurePreserving_freeSwap i j).integral_comp
    (measurableEmbedding_freeSwap i j) (fun t => (ρ (freeSwap i j x - t) : ℂ) * f t),
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hf] with u hu
  have e : freeSwap i j x - freeSwap i j u = freeSwap i j (x - u) := rfl
  rw [e, hρ, hu]
  ring

end Swap

/-! ## Cutoffs -/

section Cutoff

/-- The weights `w_n = (n+1)⁻²`. -/
noncomputable def wN (n : ℕ) : ℝ := (((n : ℝ) + 1)⁻¹) ^ 2

/-- The cutoff `χ_n(r) = F(|r|²/(n+1)²)`. -/
noncomputable def cutN (n : ℕ) (r : Rcfg eta) : ℝ := quadProfile (massQ (fun _ => wN n) r)

lemma contDiff_cutN (n : ℕ) {k : ℕ∞} : ContDiff ℝ k (cutN (eta := eta) n) :=
  (contDiff_quadProfile (n := k)).comp (contDiff_massQ _)

lemma cutN_nonneg (n : ℕ) (r : Rcfg eta) : 0 ≤ cutN n r := Real.smoothTransition.nonneg _

lemma cutN_le_one (n : ℕ) (r : Rcfg eta) : cutN n r ≤ 1 := Real.smoothTransition.le_one _

lemma wN_pos (n : ℕ) : 0 < wN n := by unfold wN; positivity

lemma massQ_const_freeSwap (w : ℝ) (i j : Fin eta) (r : Rcfg eta) :
    massQ (fun _ => w) (freeSwap i j r) = massQ (fun _ => w) r := by
  unfold massQ freeSwap
  exact Fintype.sum_equiv ((Equiv.swap i j).prodCongr (Equiv.refl _)) _ _ fun a => rfl

lemma cutN_freeSwap (n : ℕ) (i j : Fin eta) (r : Rcfg eta) :
    cutN n (freeSwap i j r) = cutN n r := by
  unfold cutN
  rw [massQ_const_freeSwap]

lemma sq_le_massQ_const (w : ℝ) (hw : 0 ≤ w) (r : Rcfg eta) (b : Fin eta × Fin 3) :
    w * r b ^ 2 ≤ massQ (fun _ => w) r :=
  Finset.single_le_sum (f := fun b' => w * r b' ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ b)

lemma abs_le_of_massQ_le {n : ℕ} {r : Rcfg eta} (h : massQ (fun _ => wN n) r ≤ 2)
    (b : Fin eta × Fin 3) : |r b| ≤ 2 * ((n : ℝ) + 1) := by
  have h1 := sq_le_massQ_const (wN n) (wN_pos n).le r b
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : r b ^ 2 ≤ 2 * ((n : ℝ) + 1) ^ 2 := by
    have e : wN n * ((n : ℝ) + 1) ^ 2 = 1 := by
      unfold wN
      field_simp
    nlinarith [sq_nonneg (r b)]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (r b + 2 * ((n : ℝ) + 1)),
    sq_nonneg (r b - 2 * ((n : ℝ) + 1))]

lemma hasCompactSupport_cutN (n : ℕ) : HasCompactSupport (cutN (eta := eta) n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Rcfg eta) (2 * ((n : ℝ) + 1)))
    fun r hr => ?_
  by_contra hne
  apply hr
  have hlt : massQ (fun _ => wN n) r < 2 := by
    by_contra h'
    exact hne (quadProfile_zero (not_lt.mp h'))
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
  intro b
  rw [Real.norm_eq_abs]
  exact abs_le_of_massQ_le hlt.le b

/-- `χ_n → 1` pointwise. -/
lemma tendsto_cutN (r : Rcfg eta) : Tendsto (fun n => cutN n r) atTop (𝓝 1) := by
  have hq : massQ (fun _ => wN 0) r = wN 0 * cfgSq r := by
    unfold massQ cfgSq
    rw [Finset.mul_sum]
  have hev : ∀ᶠ n : ℕ in atTop, cutN n r = 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge (cfgSq r)
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    apply quadProfile_one
    have e : massQ (fun _ => wN n) r = wN n * cfgSq r := by
      unfold massQ cfgSq
      rw [Finset.mul_sum]
    rw [e]
    have hc : 0 ≤ cfgSq r := cfgSq_nonneg r
    have hn1 : cfgSq r ≤ ((n : ℝ) + 1) ^ 2 := by
      have h1 : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hw : wN n * ((n : ℝ) + 1) ^ 2 = 1 := by
      unfold wN
      field_simp
    have hw0 := wN_pos n
    nlinarith
  exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)

/-- `|∂_a χ_n| ≤ 4M/(n+1)`, `M` a bound of `|F'|`. -/
lemma abs_dirD_cutN_le {M : ℝ} (hM : ∀ t, |deriv quadProfile t| ≤ M) (n : ℕ)
    (a : Fin eta × Fin 3) (r : Rcfg eta) :
    |dirD a (cutN n) r| ≤ 4 * M / ((n : ℝ) + 1) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have e : dirD a (cutN n) r = deriv quadProfile (massQ (fun _ => wN n) r) * (2 * wN n * r a) :=
    dirD_quad (fun _ => wN n) a r
  rw [e]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  by_cases hq : massQ (fun _ => wN n) r ∈ Icc (1 : ℝ) 2
  · have h1 := abs_le_of_massQ_le hq.2 a
    have hw : wN n * ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) := by
      unfold wN
      field_simp
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (wN_pos n), abs_two]
    have hw0 := wN_pos n
    calc |deriv quadProfile (massQ (fun _ => wN n) r)| * (2 * wN n * |r a|)
        ≤ M * (2 * wN n * (2 * ((n : ℝ) + 1))) :=
          mul_le_mul (hM _) (by gcongr) (mul_nonneg (by positivity) (abs_nonneg _)) hM0
      _ = 4 * M * (wN n * ((n : ℝ) + 1)) := by ring
      _ = 4 * M / ((n : ℝ) + 1) := by rw [hw]; ring
  · rw [deriv_quadProfile_eq_zero hq, zero_mul, abs_zero]
    positivity

end Cutoff

/-! ## The approximants -/

section Approx

variable (ψ : FreeL2 eta)

/-- The approximant `φ_n = χ_n · (σ_n ⋆ ψ)`. -/
noncomputable def apprN (n : ℕ) (r : Rcfg eta) : ℂ := (cutN n r : ℂ) * moll (sigN n) ψ r

lemma contDiff_moll_sigN (n : ℕ) {k : ℕ∞} : ContDiff ℝ k (moll (sigN (eta := eta) n) ψ) :=
  contDiff_moll (hasCompactSupport_sigN n) (contDiff_sigN n) (locInt_L2 ψ)

lemma contDiff_apprN (n : ℕ) {k : ℕ∞} : ContDiff ℝ k (apprN ψ n) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_cutN n)).mul (contDiff_moll_sigN ψ n)

lemma hasCompactSupport_apprN (n : ℕ) : HasCompactSupport (apprN ψ n) := by
  have h : HasCompactSupport (fun r => (cutN (eta := eta) n r : ℂ)) :=
    (hasCompactSupport_cutN n).comp_left Complex.ofReal_zero
  exact h.mul_right

/-- The approximants stay in the sector. -/
lemma apprN_freeSwap {i j : Fin eta} {s : ℂ} (hS : ∀ᵐ r, ψ (freeSwap i j r) = s * ψ r) (n : ℕ)
    (r : Rcfg eta) : apprN ψ n (freeSwap i j r) = s * apprN ψ n r := by
  unfold apprN
  rw [cutN_freeSwap, moll_freeSwap (sigN_freeSwap n i j) hS]
  ring

/-- `∂_a φ_n = χ_n (σ_n ⋆ g_a) + (∂_a χ_n)(σ_n ⋆ ψ)`. -/
lemma dirD_apprN {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad ψ g) (n : ℕ)
    (a : Fin eta × Fin 3) (r : Rcfg eta) :
    dirD a (apprN ψ n) r = (cutN n r : ℂ) * moll (sigN n) (g a) r +
      ((dirD a (cutN n) r : ℝ) : ℂ) * moll (sigN n) ψ r := by
  unfold apprN
  rw [dirD_ofReal_mul ((contDiff_cutN n (k := 1)).differentiable one_ne_zero r)
    ((contDiff_moll_sigN ψ n (k := 1)).differentiable one_ne_zero r)]
  have h1 : dirD a (moll (sigN n) ψ) r = moll (sigN n) (g a) r := by
    rw [dirD_moll (hasCompactSupport_sigN n) (contDiff_sigN n) (locInt_L2 ψ)]
    exact moll_dirD_eq hg (hasCompactSupport_sigN n) (contDiff_sigN n) a r
  rw [h1]
  ring

lemma memLp_apprN (n : ℕ) : MemLp (apprN ψ n) 2 volume :=
  memLp_cs (contDiff_apprN ψ n (k := 0)).continuous (hasCompactSupport_apprN ψ n)

lemma memLp_dirD_apprN (n : ℕ) (a : Fin eta × Fin 3) :
    MemLp (dirD a (apprN ψ n)) 2 volume :=
  memLp_cs (continuous_dirD (contDiff_apprN ψ n (k := 1)) one_ne_zero a)
    (hasCompactSupport_dirD (hasCompactSupport_apprN ψ n) a)

/-- The approximant in `L²`. -/
noncomputable def apprL2 (n : ℕ) : FreeL2 eta := (memLp_apprN ψ n).toLp _

/-- Its gradient in `L²`. -/
noncomputable def apprGrad (n : ℕ) (a : Fin eta × Fin 3) : FreeL2 eta :=
  (memLp_dirD_apprN ψ n a).toLp _

lemma hasWeakGrad_apprL2 (n : ℕ) : HasWeakGrad (apprL2 ψ n) (apprGrad ψ n) :=
  hasWeakGrad_of_contDiff (contDiff_apprN ψ n) (hasCompactSupport_apprN ψ n)

lemma norm_sq_sub_le_two (u v : ℂ) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := norm_add_le u v
  nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (u + v), sq_nonneg (‖u‖ - ‖v‖)]

lemma norm_sq_add3_le (u v w : ℂ) :
    ‖u + v + w‖ ^ 2 ≤ 3 * ‖u‖ ^ 2 + 3 * ‖v‖ ^ 2 + 3 * ‖w‖ ^ 2 := by
  have h := norm_add₃_le (a := u) (b := v) (c := w)
  nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg w, norm_nonneg (u + v + w),
    sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖v‖ - ‖w‖), sq_nonneg (‖u‖ - ‖w‖)]

lemma cut_sq_bound (n : ℕ) (r : Rcfg eta) : ‖(1 - cutN n r) ^ 2‖ ≤ 1 := by
  have h1 := cutN_nonneg n r
  have h2 := cutN_le_one n r
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- `∫ (1 - χ_n)² |f|² → 0` for `f ∈ L²`. -/
lemma tendsto_tail_cutN (f : FreeL2 eta) :
    Tendsto (fun n => ∫ r, (1 - cutN n r) ^ 2 * ‖f r‖ ^ 2) atTop (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ r, (0 : ℝ) * ‖f r‖ ^ 2 := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence (fun r => ‖f r‖ ^ 2) (fun n => ?_)
    (integrable_sq_L2 f) (fun n => ae_of_all _ fun r => ?_) (ae_of_all _ fun r => ?_)
  · exact (((continuous_const.sub (contDiff_cutN n (k := 0)).continuous).pow
      2).aestronglyMeasurable).mul ((Lp.aestronglyMeasurable f).norm.pow 2)
  · have h1 := cutN_nonneg n r
    have h2 := cutN_le_one n r
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have : (1 - cutN n r) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖f r‖]
  · have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_cutN r)).pow 2 |>.mul_const
      (‖f r‖ ^ 2)
    simpa using h

/-- **The approximants converge in the form norm**: `φ_n → ψ` and `∂_a φ_n → g_a` in `L²`. -/
theorem apprN_tendsto {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad ψ g) :
    Tendsto (apprL2 ψ) atTop (𝓝 ψ) ∧
      ∀ a, Tendsto (fun n => apprGrad ψ n a) atTop (𝓝 (g a)) := by
  obtain ⟨M, hM⟩ := exists_bound_deriv_quadProfile
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- a squared norm tends to `0`
  have key : ∀ (F : ℕ → FreeL2 eta) (G : FreeL2 eta),
      Tendsto (fun n => ‖F n - G‖ ^ 2) atTop (𝓝 0) → Tendsto F atTop (𝓝 G) := by
    intro F G h
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h
    rw [Real.sqrt_zero] at h2
    exact h2.congr fun n => by
      simp only [Function.comp_apply]
      exact Real.sqrt_sq (norm_nonneg _)
  -- the function part
  have hsig := fun f : FreeL2 eta => (tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_sigL2 f)).pow 2
  refine ⟨key _ _ ?_, fun a => key _ _ ?_⟩
  · have hb : ∀ n, ‖apprL2 ψ n - ψ‖ ^ 2 ≤
        2 * ‖sigL2 n ψ - ψ‖ ^ 2 + 2 * ∫ r, (1 - cutN n r) ^ 2 * ‖ψ r‖ ^ 2 := by
      intro n
      have hae : (⇑(apprL2 ψ n - ψ) : Rcfg eta → ℂ) =ᵐ[volume]
          fun r => apprN ψ n r - ψ r := by
        filter_upwards [Lp.coeFn_sub (apprL2 ψ n) ψ, (memLp_apprN ψ n).coeFn_toLp] with r h1 h2
        rw [h1, Pi.sub_apply, apprL2, h2]
      have hae2 : (⇑(sigL2 n ψ - ψ) : Rcfg eta → ℂ) =ᵐ[volume]
          fun r => moll (sigN n) ψ r - ψ r := by
        filter_upwards [Lp.coeFn_sub (sigL2 n ψ) ψ, sigL2_ae n ψ] with r h1 h2
        rw [h1, Pi.sub_apply, h2]
      rw [norm_sq_eq_of_ae hae, norm_sq_eq_of_ae hae2]
      have i1 : Integrable fun r => ‖moll (sigN n) ψ r - ψ r‖ ^ 2 :=
        (integrable_sq_L2 (sigL2 n ψ - ψ)).congr (hae2.mono fun r hr => by simp only [hr])
      have i2 : Integrable fun r => (1 - cutN n r) ^ 2 * ‖ψ r‖ ^ 2 :=
        ((integrable_sq_L2 ψ).mul_bdd (c := 1) (((continuous_const.sub
          (contDiff_cutN n (k := 0)).continuous).pow 2).aestronglyMeasurable)
          (ae_of_all _ fun r => cut_sq_bound n r)).congr (ae_of_all _ fun r => mul_comm _ _)
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
        (i2.const_mul _)]
      refine integral_mono (integrable_sq_L2 (apprL2 ψ n - ψ) |>.congr
        (hae.mono fun r hr => by simp only [hr])) ((i1.const_mul _).add (i2.const_mul _))
        fun r => ?_
      have e : apprN ψ n r - ψ r = (cutN n r : ℂ) * (moll (sigN n) ψ r - ψ r) +
          ((cutN n r : ℂ) - 1) * ψ r := by
        unfold apprN
        ring
      have h1 := cutN_nonneg n r
      have h2 := cutN_le_one n r
      have q1 : ‖(cutN n r : ℂ) * (moll (sigN n) ψ r - ψ r)‖ ^ 2 ≤
          ‖moll (sigN n) ψ r - ψ r‖ ^ 2 := by
        rw [norm_mul, Complex.norm_of_nonneg h1, mul_pow]
        have : cutN n r ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg ‖moll (sigN n) ψ r - ψ r‖]
      have q2 : ‖((cutN n r : ℂ) - 1) * ψ r‖ ^ 2 = (1 - cutN n r) ^ 2 * ‖ψ r‖ ^ 2 := by
        rw [norm_mul, mul_pow]
        congr 1
        rw [show ((cutN n r : ℂ) - 1) = ((cutN n r - 1 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, sq_abs]
        ring
      rw [e]
      have := norm_sq_sub_le_two ((cutN n r : ℂ) * (moll (sigN n) ψ r - ψ r))
        (((cutN n r : ℂ) - 1) * ψ r)
      rw [q2] at this
      linarith
    have hlim : Tendsto (fun n => 2 * ‖sigL2 n ψ - ψ‖ ^ 2 +
        2 * ∫ r, (1 - cutN n r) ^ 2 * ‖ψ r‖ ^ 2) atTop (𝓝 0) := by
      have := ((hsig ψ).const_mul 2).add ((tendsto_tail_cutN ψ).const_mul 2)
      simpa using this
    exact squeeze_zero (fun n => sq_nonneg _) hb hlim
  · have hb : ∀ n, ‖apprGrad ψ n a - g a‖ ^ 2 ≤
        3 * ‖sigL2 n (g a) - g a‖ ^ 2 + 3 * (∫ r, (1 - cutN n r) ^ 2 * ‖g a r‖ ^ 2) +
          3 * (4 * M / ((n : ℝ) + 1)) ^ 2 * ‖ψ‖ ^ 2 := by
      intro n
      have hae : (⇑(apprGrad ψ n a - g a) : Rcfg eta → ℂ) =ᵐ[volume]
          fun r => dirD a (apprN ψ n) r - g a r := by
        filter_upwards [Lp.coeFn_sub (apprGrad ψ n a) (g a),
          (memLp_dirD_apprN ψ n a).coeFn_toLp] with r h1 h2
        rw [h1, Pi.sub_apply, apprGrad, h2]
      have hae2 : (⇑(sigL2 n (g a) - g a) : Rcfg eta → ℂ) =ᵐ[volume]
          fun r => moll (sigN n) (g a) r - g a r := by
        filter_upwards [Lp.coeFn_sub (sigL2 n (g a)) (g a), sigL2_ae n (g a)] with r h1 h2
        rw [h1, Pi.sub_apply, h2]
      have hae3 : (⇑(sigL2 n ψ) : Rcfg eta → ℂ) =ᵐ[volume] fun r => moll (sigN n) ψ r :=
        sigL2_ae n ψ
      rw [norm_sq_eq_of_ae hae, norm_sq_eq_of_ae hae2]
      have hψn : ∫ r, ‖moll (sigN n) ψ r‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
        rw [← norm_sq_eq_of_ae hae3]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_sigL2_le n ψ) 2
      have i1 : Integrable fun r => ‖moll (sigN n) (g a) r - g a r‖ ^ 2 :=
        (integrable_sq_L2 (sigL2 n (g a) - g a)).congr (hae2.mono fun r hr => by simp only [hr])
      have i2 : Integrable fun r => (1 - cutN n r) ^ 2 * ‖g a r‖ ^ 2 :=
        ((integrable_sq_L2 (g a)).mul_bdd (c := 1) (((continuous_const.sub
          (contDiff_cutN n (k := 0)).continuous).pow 2).aestronglyMeasurable)
          (ae_of_all _ fun r => cut_sq_bound n r)).congr (ae_of_all _ fun r => mul_comm _ _)
      have i3 : Integrable fun r => ‖moll (sigN n) ψ r‖ ^ 2 :=
        (integrable_sq_L2 (sigL2 n ψ)).congr (hae3.mono fun r hr => by simp only [hr])
      have hB : 0 ≤ (4 * M / ((n : ℝ) + 1)) ^ 2 := sq_nonneg _
      calc ∫ r, ‖dirD a (apprN ψ n) r - g a r‖ ^ 2
          ≤ ∫ r, (3 * ‖moll (sigN n) (g a) r - g a r‖ ^ 2 +
              3 * ((1 - cutN n r) ^ 2 * ‖g a r‖ ^ 2) +
              3 * (4 * M / ((n : ℝ) + 1)) ^ 2 * ‖moll (sigN n) ψ r‖ ^ 2) := by
            refine integral_mono (integrable_sq_L2 (apprGrad ψ n a - g a) |>.congr
              (hae.mono fun r hr => by simp only [hr]))
              (((i1.const_mul _).add (i2.const_mul _)).add (i3.const_mul _)) fun r => ?_
            have e : dirD a (apprN ψ n) r - g a r =
                (cutN n r : ℂ) * (moll (sigN n) (g a) r - g a r) +
                ((cutN n r : ℂ) - 1) * g a r +
                ((dirD a (cutN n) r : ℝ) : ℂ) * moll (sigN n) ψ r := by
              rw [dirD_apprN ψ hg n a r]
              ring
            have h1 := cutN_nonneg n r
            have h2 := cutN_le_one n r
            have q1 : ‖(cutN n r : ℂ) * (moll (sigN n) (g a) r - g a r)‖ ^ 2 ≤
                ‖moll (sigN n) (g a) r - g a r‖ ^ 2 := by
              rw [norm_mul, Complex.norm_of_nonneg h1, mul_pow]
              have : cutN n r ^ 2 ≤ 1 := by nlinarith
              nlinarith [sq_nonneg ‖moll (sigN n) (g a) r - g a r‖]
            have q2 : ‖((cutN n r : ℂ) - 1) * g a r‖ ^ 2 = (1 - cutN n r) ^ 2 * ‖g a r‖ ^ 2 := by
              rw [norm_mul, mul_pow]
              congr 1
              rw [show ((cutN n r : ℂ) - 1) = ((cutN n r - 1 : ℝ) : ℂ) by push_cast; ring,
                Complex.norm_real, Real.norm_eq_abs, sq_abs]
              ring
            have q3 : ‖((dirD a (cutN n) r : ℝ) : ℂ) * moll (sigN n) ψ r‖ ^ 2 ≤
                (4 * M / ((n : ℝ) + 1)) ^ 2 * ‖moll (sigN n) ψ r‖ ^ 2 := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
              have hd := abs_dirD_cutN_le hM n a r
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hd 2)
                (sq_nonneg _)
            rw [e]
            have := norm_sq_add3_le ((cutN n r : ℂ) * (moll (sigN n) (g a) r - g a r))
              (((cutN n r : ℂ) - 1) * g a r) (((dirD a (cutN n) r : ℝ) : ℂ) * moll (sigN n) ψ r)
            rw [q2] at this
            nlinarith
        _ = 3 * (∫ r, ‖moll (sigN n) (g a) r - g a r‖ ^ 2) +
              3 * (∫ r, (1 - cutN n r) ^ 2 * ‖g a r‖ ^ 2) +
              3 * (4 * M / ((n : ℝ) + 1)) ^ 2 * ∫ r, ‖moll (sigN n) ψ r‖ ^ 2 := by
            have i12 : Integrable fun r => 3 * ‖moll (sigN n) (g a) r - g a r‖ ^ 2 +
                3 * ((1 - cutN n r) ^ 2 * ‖g a r‖ ^ 2) := (i1.const_mul _).add (i2.const_mul _)
            rw [integral_add i12 (i3.const_mul _), integral_add (i1.const_mul _) (i2.const_mul _),
              integral_const_mul, integral_const_mul, integral_const_mul]
        _ ≤ 3 * (∫ r, ‖moll (sigN n) (g a) r - g a r‖ ^ 2) +
              3 * (∫ r, (1 - cutN n r) ^ 2 * ‖g a r‖ ^ 2) +
              3 * (4 * M / ((n : ℝ) + 1)) ^ 2 * ‖ψ‖ ^ 2 := by
            gcongr
    have hd : Tendsto (fun n : ℕ => (4 * M / ((n : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => 4 * M * (1 / ((n : ℝ) + 1))) atTop (𝓝 (4 * M * 0)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
      have h2 := h1.pow 2
      simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h2
      exact h2.congr fun n => by ring
    have hlim : Tendsto (fun n => 3 * ‖sigL2 n (g a) - g a‖ ^ 2 +
        3 * (∫ r, (1 - cutN n r) ^ 2 * ‖g a r‖ ^ 2) +
        3 * (4 * M / ((n : ℝ) + 1)) ^ 2 * ‖ψ‖ ^ 2) atTop (𝓝 0) := by
      have := (((hsig (g a)).const_mul 3).add ((tendsto_tail_cutN (g a)).const_mul 3)).add
        ((hd.const_mul 3).mul_const (‖ψ‖ ^ 2))
      simpa using this
    exact squeeze_zero (fun n => sq_nonneg _) hb hlim

end Approx

end FreeBoundary
