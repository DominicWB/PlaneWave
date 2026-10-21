import PlaneWave.Auxiliary.AliasGrid

/-!
# Auxiliary claims, part 7: the potential tails of the truncated kernels
(`lem:grid-KR` (iii), eq:grid-tail, eq:grid-potential-tail)

On a cube `n`, with `g = 2π/L`, a threshold `K ≥ 1`, `Θ(u) = ‖(1 + A) u‖` and `m̄` the largest
mass:

* `fullH2Sq_le`: the full `H²` budget of every state is at most `(2 m̄ Θ(u))²`;
* `tail_domination`: Fourier domination (eq:fourier-domination) with the register-`a` tail
  restriction `Π = 1{|k_{p_a}| > K}`;
* **`tail_pair_dominated`**, **`tail_single_dominated`** (eq:grid-tail, Euclidean form): a kernel
  dominated by `C_g` times the Coulomb pair kernel of `(i, j)`, or by `C_g` times the Coulomb kernel
  of one register (this covers the translated clamped-nucleus kernels, `refKernel_dom`), satisfies,
  for every register `a`,
  `‖1{|k_{p_a}| > K} (κ u)‖ ≤ C_g c_tail (2 m̄ Θ(u)) K^{-1/2}`;
  the constant `c_tail` (`ctail`) depends only on the Coulomb strength `C`, on `L` and on the Hardy
  constant, not on `K`, `n` or `u`. The proof applies the release's all-reference tail bounds to
  `u^#` (`tail_regimes` treats the thresholds `K < 2g` and `K > 4g(n+1)` separately);
* **`grid_tail`** (eq:grid-tail): the same with the restriction `‖k_{p_a}‖_∞ > K`;
* **`grid_potential_tail`** (eq:grid-potential-tail): for `V_grid = Σ_t c_t Diag[g_t]` with every
  kernel dominated as above (`CoulombDominated`) and its outputs in the alias region of
  `lem:grid-KR` (ii),
  `‖1{‖k_{p_a}‖_∞ > K} (V_grid u)‖ ≤ 28 (Σ_t |c_t| C_{g,t}) c_tail (2 m̄ Θ(u)) K^{-1/2}`;
  `grid_potential_tail_explicit` is the same with the explicit periodic Hardy constant.

The mass factor obtained is `m̄` (the coarser bound mentioned in the text), not `√(m_a m̄)`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators
open PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν] {n : ℕ}

/-! ## The `H²` budget -/

omit [Fintype ν] in
/-- `1 + Σ_a |k_{p_a}|² ≤ 2 m̄ (1 + A(p))`. -/
lemma one_add_bo_le (sys : CoulombSystem eta ν) (L : ℝ) (p : Cfg eta n) :
    1 + boKineticSymbol (finitePlaneWaveKabs (2 * Real.pi / L) n) p ≤
      2 * sys.maxMass * (1 + Asym sys L n p) := by
  have hm : ∀ a, 0 < sys.mass a := fun a => lt_of_lt_of_le one_pos (sys.one_le_mass a)
  have h := boKineticSymbol_le_mul_massKineticSymbol hm (fun a => sys.mass_le_maxMass a)
    (finitePlaneWaveKabs (2 * Real.pi / L) n) p
  have hM := sys.one_le_maxMass
  have hA := Asym_nonneg' sys L p
  have e : massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) p =
      2 * Asym sys L n p := by unfold Asym; ring
  rw [e] at h
  nlinarith

omit [Fintype ν] in
/-- The full `H²` norm of a state is at most `(2 m̄ Θ(u))²`, `Θ(u) = ‖(1 + A) u‖`. -/
lemma fullH2Sq_le (sys : CoulombSystem eta ν) (L : ℝ) (u : En eta n) :
    fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) u.ofLp ≤
      (2 * sys.maxMass * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) ^ 2 := by
  rw [mul_pow, FSKernel.norm_sq_eq, Finset.mul_sum]
  unfold fullH2Sq coeffMass
  refine Finset.sum_le_sum fun p _ => ?_
  have hA := Asym_nonneg' sys L p
  rw [wt_one_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h1 := one_add_bo_le sys L p
  have h0 : 0 ≤ 1 + boKineticSymbol (finitePlaneWaveKabs (2 * Real.pi / L) n) p := by
    have := boKineticSymbol_nonneg (finitePlaneWaveKabs (2 * Real.pi / L) n) p; linarith
  have h2 := pow_le_pow_left₀ h0 h1 2
  calc (1 + boKineticSymbol (finitePlaneWaveKabs (2 * Real.pi / L) n) p) ^ 2 * ‖u.ofLp p‖ ^ 2
      ≤ (2 * sys.maxMass * (1 + Asym sys L n p)) ^ 2 * ‖u.ofLp p‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = (2 * sys.maxMass) ^ 2 * ((1 + Asym sys L n p) * ‖u.ofLp p‖) ^ 2 := by ring

omit [Fintype ν] in
/-- `u^#` has the same `H²` norm. -/
lemma fullH2Sq_umod (kabs : FinitePlaneWaveMode n → ℝ) (u : En eta n) :
    fullH2Sq kabs (umod u).ofLp = fullH2Sq kabs u.ofLp := by
  unfold fullH2Sq coeffMass; simp_rw [norm_umod_apply]

omit [Fintype ν] in
lemma fourierH1Sq_le_fullH2Sq (kabs : FinitePlaneWaveMode n → ℝ) (v : En eta n) :
    fourierH1Sq kabs v ≤ fullH2Sq kabs v.ofLp := by
  unfold fourierH1Sq fullH2Sq coeffMass
  refine Finset.sum_le_sum fun p _ => ?_
  have h0 := boKineticSymbol_nonneg kabs p
  exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)

omit [Fintype ν] in
/-- An `H¹` operator bound `B` gives `‖W v‖ ≤ B M₂` under the `H²` budget `M₂`. -/
lemma norm_le_of_h1 {kabs : FinitePlaneWaveMode n → ℝ} {W : En eta n →ₗ[ℂ] En eta n} {B M2 : ℝ}
    (hB : 0 ≤ B) (hM2 : 0 ≤ M2) (hW : HasH1OperatorBound kabs W B) (v : En eta n)
    (hH2 : fullH2Sq kabs v.ofLp ≤ M2 ^ 2) : ‖W v‖ ≤ B * M2 := by
  have h := (hW v).trans (mul_le_mul_of_nonneg_left
    ((fourierH1Sq_le_fullH2Sq kabs v).trans hH2) (sq_nonneg B))
  rw [← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hB hM2) two_ne_zero).mp h

/-! ## Fourier domination on the tail -/

omit [Fintype ν] in
/-- **Fourier domination with the register tail restriction** (eq:fourier-domination with
`Π = 1{|k_{p_a}| > K}`). -/
lemma tail_domination (κ W : Cfg eta n → Cfg eta n → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hW : ∀ q p, W q p = ((‖W q p‖ : ℝ) : ℂ)) (hdom : ∀ q p, ‖κ q p‖ ≤ Cg * ‖W q p‖)
    (Kt : ℝ) (kabs : FinitePlaneWaveMode n → ℝ) (a : Fin eta) (u : En eta n) :
    ‖referenceTailOperator Kt kabs a (finiteCoefficientKernelOperator κ u)‖ ≤
      Cg * ‖referenceTailOperator Kt kabs a (finiteCoefficientKernelOperator W (umod u))‖ := by
  have h := fourier_domination κ W hW hdom (fun q => if Kt < kabs (q a) then (1 : ℝ) else 0)
    (fun q => by split_ifs <;> norm_num) u
  beta_reduce at h
  have e : ∀ v : En eta n, ‖referenceTailOperator Kt kabs a v‖ ^ 2 =
      ∑ q, (if Kt < kabs (q a) then (1 : ℝ) else 0) * ‖v.ofLp q‖ ^ 2 := by
    intro v
    rw [FSKernel.norm_sq_eq]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [referenceTailOperator_apply]
    split_ifs <;> simp
  rw [← e, ← e, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

omit [Fintype ν] in
/-- The configuration Coulomb kernel of one register is real and nonnegative. -/
lemma refKernel_real (r : Fin eta) (C : ℝ) (q p : Cfg eta n) :
    referenceConfigurationKernel r (finiteCoulombKernel C n) q p =
      ((‖referenceConfigurationKernel r (finiteCoulombKernel C n) q p‖ : ℝ) : ℂ) := by
  classical
  by_cases h : outerConfigOf r q = outerConfigOf r p
  · rw [referenceConfigurationKernel_of_outer_eq r _ q p h]
    unfold finiteCoulombKernel
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  · rw [referenceConfigurationKernel_of_outer_ne r _ q p h]; simp

omit [Fintype ν] in
lemma fcko_refKernel (r : Fin eta) (kernel : FinitePlaneWaveMode n → FinitePlaneWaveMode n → ℂ)
    (v : En eta n) :
    finiteCoefficientKernelOperator (referenceConfigurationKernel r kernel) v =
      referenceKernelConvolutionOperator r kernel v := by
  ext q; rw [fcko_apply, referenceKernelConvolutionOperator_apply]

omit [Fintype ν] in
/-- A one-particle kernel dominated by `C_g √(Coulomb weight)` (for instance a translated
clamped-nucleus kernel, `finiteTranslatedCoulombKernel_norm_le`) gives a configuration kernel
dominated by `C_g` times the configuration Coulomb kernel of its register. -/
lemma refKernel_dom (r : Fin eta) {C Cg : ℝ}
    (κ₁ : FinitePlaneWaveMode n → FinitePlaneWaveMode n → ℂ)
    (hdom : ∀ v w, ‖κ₁ v w‖ ≤ Cg * Real.sqrt (finiteCoulombDifferenceSquareWeight C n v w))
    (q p : Cfg eta n) :
    ‖referenceConfigurationKernel r κ₁ q p‖ ≤
      Cg * ‖referenceConfigurationKernel r (finiteCoulombKernel C n) q p‖ := by
  classical
  by_cases h : outerConfigOf r q = outerConfigOf r p
  · rw [referenceConfigurationKernel_of_outer_eq r _ q p h,
      referenceConfigurationKernel_of_outer_eq r _ q p h]
    unfold finiteCoulombKernel
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hdom _ _
  · rw [referenceConfigurationKernel_of_outer_ne r _ q p h,
      referenceConfigurationKernel_of_outer_ne r _ q p h]; simp

/-! ## The tail constants -/

/-- The release constants `B` (Hardy), `B_low`, `B_ker`, `C_s`, chosen so that the scale conditions
of the all-reference tail bounds hold exactly. -/
noncomputable def tB (C Hunit g : ℝ) : ℝ := Real.sqrt (C * Hunit ^ 2 / physicalH1Scale g)
noncomputable def tBlow (C g : ℝ) : ℝ := 54 * Real.sqrt C / g
noncomputable def tBker (C g : ℝ) : ℝ := Real.sqrt (432 * C * g)
noncomputable def tCs (g : ℝ) : ℝ := Real.sqrt (1 + 108 / g ^ 4)

/-- The common near/far budget `Z = B + 4 B_low + C_s B_ker` of the release. -/
noncomputable def tZ (C Hunit g : ℝ) : ℝ := tB C Hunit g + (4 * tBlow C g + tCs g * tBker C g)

/-- **The tail constant** `c_tail = (1 + √(2g)) B + Z`; it depends only on `C`, `g = 2π/L` and the
Hardy constant. -/
noncomputable def ctail (C Hunit g : ℝ) : ℝ :=
  (1 + Real.sqrt (2 * g)) * tB C Hunit g + tZ C Hunit g

lemma tB_nonneg (C Hunit g : ℝ) : 0 ≤ tB C Hunit g := Real.sqrt_nonneg _
lemma tBker_nonneg (C g : ℝ) : 0 ≤ tBker C g := Real.sqrt_nonneg _
lemma tCs_nonneg (g : ℝ) : 0 ≤ tCs g := Real.sqrt_nonneg _
lemma tBlow_nonneg {C g : ℝ} (hg : 0 < g) : 0 ≤ tBlow C g := by unfold tBlow; positivity

lemma tZ_nonneg {C Hunit g : ℝ} (hg : 0 < g) : 0 ≤ tZ C Hunit g := by
  unfold tZ
  have := tB_nonneg C Hunit g; have := tBlow_nonneg (C := C) hg
  have := tCs_nonneg g; have := tBker_nonneg C g
  positivity

lemma ctail_nonneg {C Hunit g : ℝ} (hg : 0 < g) : 0 ≤ ctail C Hunit g := by
  unfold ctail
  have := tB_nonneg C Hunit g; have := tZ_nonneg (C := C) (Hunit := Hunit) hg
  positivity

lemma tB_scale {C Hunit g : ℝ} (hC : 0 ≤ C) (hg : 0 < g) :
    C * Hunit ^ 2 ≤ tB C Hunit g ^ 2 * physicalH1Scale g := by
  have hp := physicalH1Scale_pos hg
  unfold tB
  rw [Real.sq_sqrt (by positivity), div_mul_cancel₀ _ hp.ne']

lemma tBlow_amp {C g : ℝ} (hg : 0 < g) : 54 * Real.sqrt C ≤ tBlow C g * g := by
  unfold tBlow; rw [div_mul_cancel₀ _ hg.ne']

lemma tBker_scale {C g : ℝ} (hC : 0 ≤ C) (hg : 0 < g) : 432 * C * g ≤ tBker C g ^ 2 := by
  unfold tBker; rw [Real.sq_sqrt (by positivity)]

lemma tCs_scale {g : ℝ} (hg : 0 < g) : 1 + 108 / g ^ 4 ≤ tCs g ^ 2 := by
  unfold tCs; rw [Real.sq_sqrt (by positivity)]

/-- `ρ = K^{-1/2}` satisfies `ρ² K = 1`. -/
lemma rho_scale {Kt : ℝ} (hK : 0 < Kt) : (Kt ^ (-(1 / 2 : ℝ))) ^ 2 * Kt = 1 := by
  have h2 : (Kt ^ (-(1 / 2 : ℝ))) ^ 2 = Kt⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le, ← Real.rpow_neg_one]
    norm_num
  rw [h2, inv_mul_cancel₀ hK.ne']

/-! ## The release tail bounds on a cube containing the cutoff shell -/

omit [Fintype ν] in
/-- The `H¹` bound of the Coulomb kernel of one register. -/
lemma refCoulomb_h1 (r : Fin eta) {g C : ℝ} (hg : 0 < g) (hC : 0 ≤ C) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (count : ℕ) :
    HasH1OperatorBound (finitePlaneWaveKabs g count)
      (referenceKernelConvolutionOperator r (finiteCoulombKernel C count)) (tB C Hunit g) :=
  referenceKernelConvolutionOperator_h1Bound_of_oneParticle r _ _ _ fun f =>
    coulomb_dominated_kernel_oneParticle_h1 g C (tB C Hunit g) count _ (fun x y => by
      unfold finiteCoulombKernel
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)])
      (oneParticleCoulombH1Bound_of_canonicalPeriodic g C (tB C Hunit g) Hunit count hC hPeriodic
        (tB_scale hC hg)) f

omit [Fintype ν] in
/-- The release's all-reference pair tail bound, on any cube containing the cutoff shell. -/
lemma pair_tail_release {i j : Fin eta} (hij : i ≠ j) (a : Fin eta) {g C : ℝ} (hg : 0 < g)
    (hC : 0 ≤ C) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {Kt M2 : ℝ} (hK1 : 1 ≤ Kt) (h2gK : 2 * g ≤ Kt) (hn : cutoffShellIndex Kt g ≤ n)
    (hM2 : 0 ≤ M2) (v : En eta n) (hH2 : fullH2Sq (finitePlaneWaveKabs g n) v.ofLp ≤ M2 ^ 2) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs g n) a
        (finiteElectronPairCoulombOperator i j C n v)‖ ≤
      tZ C Hunit g * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hK0 : 0 < Kt := by linarith
  have h := finiteElectronPairCoulombOperator_tail_bound_any_reference i j a hij Kt g C
    (Kt ^ (-(1 / 2 : ℝ))) (tB C Hunit g) Hunit (tBlow C g) (tCs g) (tBker C g) M2 e v.ofLp
    hK1 hg hC (Real.rpow_pos_of_pos hK0 _).le (rho_scale hK0) (tB_nonneg C Hunit g)
    (tBlow_nonneg hg) (tCs_nonneg g) (tBker_nonneg C g) hM2 h2gK (tBlow_amp hg)
    (tBker_scale hC hg) (tCs_scale hg) hPeriodic (tB_scale hC hg) hH2
  have hfc : fullCoeffVector v.ofLp = v := rfl
  rw [hfc] at h
  refine h.trans (le_of_eq ?_)
  unfold tZ; ring

omit [Fintype ν] in
/-- The release's tail bounds for the Coulomb kernel of one register (the register itself:
two-scale bound; any other register: commutation and the far bound). -/
lemma single_tail_release (r a : Fin eta) {g C : ℝ} (hg : 0 < g) (hC : 0 ≤ C) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {Kt M2 : ℝ} (hK1 : 1 ≤ Kt)
    (h2gK : 2 * g ≤ Kt) (hn : cutoffShellIndex Kt g ≤ n) (hM2 : 0 ≤ M2) (v : En eta n)
    (hH2 : fullH2Sq (finitePlaneWaveKabs g n) v.ofLp ≤ M2 ^ 2) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs g n) a
        (referenceKernelConvolutionOperator r (finiteCoulombKernel C n) v)‖ ≤
      tZ C Hunit g * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hK0 : 0 < Kt := by linarith
  have hρ0 : 0 ≤ Kt ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hK0 _).le
  have hρs := rho_scale hK0
  have hsq := rho_sq_le_rho_of_cutoff_scale hK1 hρ0 hρs
  have hB0 := tB_nonneg C Hunit g
  have hBlow0 := tBlow_nonneg (C := C) hg
  have hCs0 := tCs_nonneg g
  have hBker0 := tBker_nonneg C g
  have hfc : fullCoeffVector v.ofLp = v := rfl
  unfold tZ
  by_cases har : a = r
  · rw [har]
    have h := referenceCoulombOperator_tail_bound_two_scale r Kt g C (Kt ^ (-(1 / 2 : ℝ)))
      (tBlow C g) (tCs g) (tBker C g) M2 e v.ofLp hK1 hg hC hρ0 hρs hBlow0 hCs0 hBker0 hM2 h2gK
      (tBlow_amp hg) (tBker_scale hC hg) (tCs_scale hg) hH2
    rw [hfc] at h
    refine h.trans ?_
    have h1 : 4 * tBlow C g * M2 * (Kt ^ (-(1 / 2 : ℝ))) ^ 2 ≤
        4 * tBlow C g * M2 * Kt ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h2 : 0 ≤ tB C Hunit g * M2 * Kt ^ (-(1 / 2 : ℝ)) := by positivity
    nlinarith
  · have hComm := referenceKernelConvolutionOperator_commutesWith_other_tail r a har Kt
      (finitePlaneWaveKabs g (cutoffShellIndex Kt g + e))
      (finiteCoulombKernel C (cutoffShellIndex Kt g + e))
    rw [hComm v]
    have hFar := far_bound_from_h1_h2_tail Kt (Kt ^ (-(1 / 2 : ℝ))) (tB C Hunit g) M2
      (finitePlaneWaveKabs g (cutoffShellIndex Kt g + e)) a v.ofLp _ hK1 hρs
      (finitePlaneWaveKabs_nonneg g _ hg.le) hB0 hM2 hH2
      (refCoulomb_h1 r hg hC Hunit hPeriodic (cutoffShellIndex Kt g + e))
    rw [hfc] at hFar
    refine hFar.trans ?_
    have h1 : tB C Hunit g * M2 * (Kt ^ (-(1 / 2 : ℝ))) ^ 2 ≤
        tB C Hunit g * M2 * Kt ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h2 : 0 ≤ (4 * tBlow C g + tCs g * tBker C g) * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
      positivity
    nlinarith

/-! ## All thresholds -/

omit [Fintype ν] in
lemma kabs_cube_le {L : ℝ} (hL : 0 < L) (μ : FinitePlaneWaveMode n) :
    finitePlaneWaveKabs (2 * Real.pi / L) n μ ≤ 2 * (2 * Real.pi / L) * n := by
  have h := kabs_le_cube hL μ
  have hs : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hg : 0 ≤ gF L * n := by have := gF_pos hL; positivity
  unfold gF at h hg
  nlinarith

omit [Fintype ν] in
/-- **The three threshold regimes.** If `‖w‖ ≤ B M₂` and, on cubes containing the cutoff shell
with `2g ≤ K`, `‖1{|k_{p_a}| > K} w‖ ≤ Z M₂ K^{-1/2}`, then
`‖1{|k_{p_a}| > K} w‖ ≤ ((1 + √(2g)) B + Z) M₂ K^{-1/2}` for every `K ≥ 1`: for `K > 4g(n+1)` the
restriction is empty, and for `K < 2g` the factor `√(2g) K^{-1/2} ≥ 1` absorbs the full norm. -/
lemma tail_regimes {g : ℝ} (hg : 0 < g)
    (hcube : ∀ μ : FinitePlaneWaveMode n, finitePlaneWaveKabs g n μ ≤ 2 * g * n)
    (a : Fin eta) (w : En eta n) {B Z M2 Kt : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hM2 : 0 ≤ M2)
    (hK1 : 1 ≤ Kt) (hfull : ‖w‖ ≤ B * M2)
    (hrel : 2 * g ≤ Kt → cutoffShellIndex Kt g ≤ n →
      ‖referenceTailOperator Kt (finitePlaneWaveKabs g n) a w‖ ≤ Z * M2 * Kt ^ (-(1 / 2 : ℝ))) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs g n) a w‖ ≤
      ((1 + Real.sqrt (2 * g)) * B + Z) * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
  have hK0 : 0 < Kt := by linarith
  have hρ0 : 0 < Kt ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hK0 _
  have hs0 := Real.sqrt_nonneg (2 * g)
  have hBM : 0 ≤ B * M2 := mul_nonneg hB hM2
  have hZM : 0 ≤ Z * M2 := mul_nonneg hZ hM2
  by_cases h2g : 2 * g ≤ Kt
  · by_cases hn : cutoffShellIndex Kt g ≤ n
    · refine (hrel h2g hn).trans ?_
      have e : ((1 + Real.sqrt (2 * g)) * B + Z) * M2 * Kt ^ (-(1 / 2 : ℝ)) =
          Z * M2 * Kt ^ (-(1 / 2 : ℝ)) +
            (1 + Real.sqrt (2 * g)) * (B * M2) * Kt ^ (-(1 / 2 : ℝ)) := by ring
      rw [e]
      have : 0 ≤ (1 + Real.sqrt (2 * g)) * (B * M2) * Kt ^ (-(1 / 2 : ℝ)) := by positivity
      linarith
    · push Not at hn
      have hfl : ((n : ℝ) + 1) * (4 * g) ≤ Kt := by
        have h1 : n + 1 ≤ ⌊Kt / (4 * g)⌋₊ := hn
        have h2 := (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ Kt / (4 * g))).mp h1
        push_cast at h2
        rwa [le_div_iff₀ (by positivity)] at h2
      have hzero : referenceTailOperator Kt (finitePlaneWaveKabs g n) a w = 0 := by
        ext q
        have hq : ¬ Kt < finitePlaneWaveKabs g n (q a) := by
          have h1 := hcube (q a)
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          push Not
          nlinarith [mul_nonneg hg.le hn0]
        simp [referenceTailOperator_apply, hq]
      rw [hzero, norm_zero]
      positivity
  · push Not at h2g
    have h1 : 1 ≤ Real.sqrt (2 * g) * Kt ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hK0.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv,
        one_le_div (Real.sqrt_pos.mpr hK0)]
      exact Real.sqrt_le_sqrt h2g.le
    calc ‖referenceTailOperator Kt (finitePlaneWaveKabs g n) a w‖ ≤ ‖w‖ :=
          referenceTailOperator_norm_le _ _ _ _
      _ ≤ B * M2 := hfull
      _ ≤ B * M2 * (Real.sqrt (2 * g) * Kt ^ (-(1 / 2 : ℝ))) := le_mul_of_one_le_right hBM h1
      _ ≤ ((1 + Real.sqrt (2 * g)) * B + Z) * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
          have e : ((1 + Real.sqrt (2 * g)) * B + Z) * M2 * Kt ^ (-(1 / 2 : ℝ)) =
              B * M2 * (Real.sqrt (2 * g) * Kt ^ (-(1 / 2 : ℝ))) +
                (B * M2 * Kt ^ (-(1 / 2 : ℝ)) + Z * M2 * Kt ^ (-(1 / 2 : ℝ))) := by ring
          rw [e]
          have : 0 ≤ B * M2 * Kt ^ (-(1 / 2 : ℝ)) + Z * M2 * Kt ^ (-(1 / 2 : ℝ)) := by positivity
          linarith

/-! ## eq:grid-tail -/

omit [Fintype ν] in
/-- **eq:grid-tail for pair kernels** (Euclidean restriction): a kernel dominated by `C_g` times the
Coulomb pair kernel of `(i, j)` satisfies, for every register `a` and `K ≥ 1`,
`‖1{|k_{p_a}| > K} (κ u)‖ ≤ C_g c_tail (2 m̄ Θ(u)) K^{-1/2}`. -/
theorem tail_pair_dominated (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {i j : Fin eta}
    (hij : i ≠ j) (a : Fin eta) {C : ℝ} (hC : 0 ≤ C) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (κ : Cfg eta n → Cfg eta n → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hdom : ∀ q p, ‖κ q p‖ ≤ Cg * ‖finiteElectronPairConfigurationKernel i j C n q p‖)
    {Kt : ℝ} (hK1 : 1 ≤ Kt) (u : En eta n) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs (2 * Real.pi / L) n) a
        (finiteCoefficientKernelOperator κ u)‖ ≤
      Cg * ctail C Hunit (2 * Real.pi / L) *
        (2 * sys.maxMass * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) *
          Kt ^ (-(1 / 2 : ℝ)) := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  obtain ⟨M2, hM2def⟩ : ∃ M2,
      M2 = 2 * sys.maxMass * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := ⟨_, rfl⟩
  rw [← hM2def]
  have hM2 : 0 ≤ M2 := by rw [hM2def]; have := sys.one_le_maxMass; positivity
  have hH2 : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) (umod u).ofLp ≤ M2 ^ 2 := by
    rw [fullH2Sq_umod, hM2def]; exact fullH2Sq_le sys L u
  refine (tail_domination κ _ hCg (pairKernel_real i j C) hdom Kt _ a u).trans ?_
  unfold ctail
  rw [mul_assoc Cg, mul_assoc Cg]
  refine mul_le_mul_of_nonneg_left ?_ hCg
  have hfull := norm_le_of_h1 (tB_nonneg C Hunit _) hM2
    (finiteElectronPairCoulombOperator_h1Bound_of_periodic i j hij _ C _ Hunit n hC hPeriodic
      (tB_scale hC hg)) (umod u) hH2
  exact tail_regimes hg (kabs_cube_le hL) a _ (tB_nonneg C Hunit _) (tZ_nonneg hg) hM2 hK1 hfull
    (fun h2g hn => pair_tail_release hij a hg hC Hunit hPeriodic hK1 h2g hn hM2 (umod u) hH2)

omit [Fintype ν] in
/-- **eq:grid-tail for single-register kernels** (Euclidean restriction): a kernel dominated by
`C_g` times the Coulomb kernel of register `r` (e.g. `referenceConfigurationKernel r κ₁` for a
translated clamped-nucleus kernel `κ₁`, `refKernel_dom`) satisfies, for every register `a` and
`K ≥ 1`, `‖1{|k_{p_a}| > K} (κ u)‖ ≤ C_g c_tail (2 m̄ Θ(u)) K^{-1/2}`. -/
theorem tail_single_dominated (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (r a : Fin eta)
    {C : ℝ} (hC : 0 ≤ C) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (κ : Cfg eta n → Cfg eta n → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hdom : ∀ q p, ‖κ q p‖ ≤ Cg * ‖referenceConfigurationKernel r (finiteCoulombKernel C n) q p‖)
    {Kt : ℝ} (hK1 : 1 ≤ Kt) (u : En eta n) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs (2 * Real.pi / L) n) a
        (finiteCoefficientKernelOperator κ u)‖ ≤
      Cg * ctail C Hunit (2 * Real.pi / L) *
        (2 * sys.maxMass * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) *
          Kt ^ (-(1 / 2 : ℝ)) := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  obtain ⟨M2, hM2def⟩ : ∃ M2,
      M2 = 2 * sys.maxMass * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := ⟨_, rfl⟩
  rw [← hM2def]
  have hM2 : 0 ≤ M2 := by rw [hM2def]; have := sys.one_le_maxMass; positivity
  have hH2 : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) (umod u).ofLp ≤ M2 ^ 2 := by
    rw [fullH2Sq_umod, hM2def]; exact fullH2Sq_le sys L u
  refine (tail_domination κ _ hCg (refKernel_real r C) hdom Kt _ a u).trans ?_
  rw [fcko_refKernel]
  unfold ctail
  rw [mul_assoc Cg, mul_assoc Cg]
  refine mul_le_mul_of_nonneg_left ?_ hCg
  have hfull := norm_le_of_h1 (tB_nonneg C Hunit _) hM2
    (refCoulomb_h1 r hg hC Hunit hPeriodic n) (umod u) hH2
  exact tail_regimes hg (kabs_cube_le hL) a _ (tB_nonneg C Hunit _) (tZ_nonneg hg) hM2 hK1 hfull
    (fun h2g hn => single_tail_release r a hg hC Hunit hPeriodic hK1 h2g hn hM2 (umod u) hH2)

/-- The dominated kernel classes of the grid potential: `C_g` times a Coulomb pair kernel, or `C_g`
times the Coulomb kernel of one register. -/
def CoulombDominated (C Cg : ℝ) (κ : Cfg eta n → Cfg eta n → ℂ) : Prop :=
  (∃ i j : Fin eta, i ≠ j ∧
      ∀ q p, ‖κ q p‖ ≤ Cg * ‖finiteElectronPairConfigurationKernel i j C n q p‖) ∨
    ∃ r : Fin eta,
      ∀ q p, ‖κ q p‖ ≤ Cg * ‖referenceConfigurationKernel r (finiteCoulombKernel C n) q p‖

omit [Fintype ν] in
theorem tail_dominated (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (a : Fin eta) {C : ℝ}
    (hC : 0 ≤ C) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {κ : Cfg eta n → Cfg eta n → ℂ} {Cg : ℝ} (hCg : 0 ≤ Cg) (hdom : CoulombDominated C Cg κ)
    {Kt : ℝ} (hK1 : 1 ≤ Kt) (u : En eta n) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs (2 * Real.pi / L) n) a
        (finiteCoefficientKernelOperator κ u)‖ ≤
      Cg * ctail C Hunit (2 * Real.pi / L) *
        (2 * sys.maxMass * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) *
          Kt ^ (-(1 / 2 : ℝ)) := by
  rcases hdom with ⟨i, j, hij, h⟩ | ⟨r, h⟩
  · exact tail_pair_dominated sys hL hij a hC Hunit hPeriodic κ hCg h hK1 u
  · exact tail_single_dominated sys hL r a hC Hunit hPeriodic κ hCg h hK1 u

omit [Fintype ν] in
/-- `‖k_{p_a}‖_∞ > K` (in lattice units `supTail a (K/g)`) implies `|k_{p_a}| > K`. -/
lemma supTail_imp {g : ℝ} (hg : 0 < g) (a : Fin eta) (Kt : ℝ) (p : Cfg eta n)
    (h : supTail a (Kt / g) (cidx n p)) : Kt < finitePlaneWaveKabs g n (p a) := by
  obtain ⟨c, hc⟩ := h
  rw [div_lt_iff₀ hg] at hc
  rw [kabs_eq_lattice]
  have hle : |((cidx n p a c : ℤ) : ℝ)| ≤
      Real.sqrt (latticeNormSq (finitePlaneWaveLatticeIndex n (p a))) := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have hsum : latticeNormSq (finitePlaneWaveLatticeIndex n (p a)) =
        ∑ i : Fin 3, ((finitePlaneWaveLatticeIndex n (p a) i : ℤ) : ℝ) ^ 2 := by
      unfold latticeNormSq; rw [Fin.sum_univ_three]
    rw [hsum]
    exact Finset.single_le_sum
      (f := fun i : Fin 3 => ((finitePlaneWaveLatticeIndex n (p a) i : ℤ) : ℝ) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ c)
  nlinarith [mul_le_mul_of_nonneg_right hle hg.le]

omit [Fintype ν] in
/-- The `ℓ^∞` restriction is dominated by the Euclidean one. -/
lemma norm_supMask_le {g : ℝ} (hg : 0 < g) (a : Fin eta) (Kt : ℝ) (v : En eta n) :
    ‖maskV (fun p => supTail a (Kt / g) (cidx n p)) v‖ ≤
      ‖referenceTailOperator Kt (finitePlaneWaveKabs g n) a v‖ := by
  have e1 := norm_maskV_sq (fun p => supTail a (Kt / g) (cidx n p)) v
  have e2 := FSKernel.norm_sq_eq (referenceTailOperator Kt (finitePlaneWaveKabs g n) a v)
  have h : ∑ p ∈ Finset.univ.filter (fun p => supTail a (Kt / g) (cidx n p)), ‖v.ofLp p‖ ^ 2 ≤
      ∑ p, ‖(referenceTailOperator Kt (finitePlaneWaveKabs g n) a v).ofLp p‖ ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [referenceTailOperator_apply]
    by_cases h1 : supTail a (Kt / g) (cidx n p)
    · rw [if_pos h1, if_pos (supTail_imp hg a Kt p h1)]
    · rw [if_neg h1]; positivity
  rw [← e1, ← e2] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

omit [Fintype ν] in
/-- **eq:grid-tail**: for a dominated kernel (pair or single register), every register `a` and every
`K ≥ 1`, `‖1{‖k_{p_a}‖_∞ > K} (g u)‖ ≤ C_g c_tail (2 m̄ Θ(u)) K^{-1/2}`. -/
theorem grid_tail (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (a : Fin eta) {C : ℝ}
    (hC : 0 ≤ C) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {κ : Cfg eta n → Cfg eta n → ℂ} {Cg : ℝ} (hCg : 0 ≤ Cg) (hdom : CoulombDominated C Cg κ)
    {Kt : ℝ} (hK1 : 1 ≤ Kt) (u : En eta n) :
    ‖maskV (fun p => supTail a (Kt / (2 * Real.pi / L)) (cidx n p))
        (finiteCoefficientKernelOperator κ u)‖ ≤
      Cg * ctail C Hunit (2 * Real.pi / L) *
        (2 * sys.maxMass * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) *
          Kt ^ (-(1 / 2 : ℝ)) :=
  (norm_supMask_le (by positivity) a Kt _).trans
    (tail_dominated sys hL a hC Hunit hPeriodic hCg hdom hK1 u)

/-! ## eq:grid-potential-tail -/

omit [Fintype ν] in
lemma maskV_add (P : Cfg eta n → Prop) [DecidablePred P] (x y : En eta n) :
    maskV P (x + y) = maskV P x + maskV P y := by
  ext p; by_cases h : P p <;> simp [maskV, h]

omit [Fintype ν] in
lemma maskV_smul (P : Cfg eta n → Prop) [DecidablePred P] (c : ℂ) (x : En eta n) :
    maskV P (c • x) = c • maskV P x := by
  ext p; by_cases h : P p <;> simp [maskV, h]

/-- The coordinate mask as a linear map. -/
noncomputable def maskL (P : Cfg eta n → Prop) [DecidablePred P] : En eta n →ₗ[ℂ] En eta n where
  toFun := maskV P
  map_add' := maskV_add P
  map_smul' := maskV_smul P

section GridTail

variable {ι : Type*} [Fintype ι] (M : ℕ) (cpl : ι → ℝ) (κ : ι → Cfg eta n → Cfg eta n → ℂ)
  (S : ι → Finset (Fin eta)) (Cg : ι → ℝ)

omit [Fintype ν] in
/-- **eq:grid-potential-tail**: for a grid potential `V_grid = Σ_t c_t Diag[g_t]` whose kernels are
dominated (`C_{g,t}` times a Coulomb pair or single-register kernel) and whose outputs lie in the
alias region of `lem:grid-KR` (ii), for every register `a` and every `K ≥ 1`,
`‖1{‖k_{p_a}‖_∞ > K} (V_grid u)‖ ≤ 28 (Σ_t |c_t| C_{g,t}) c_tail (2 m̄ Θ(u)) K^{-1/2}`. -/
theorem grid_potential_tail (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {C : ℝ}
    (hC : 0 ≤ C) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hS : ∀ t, (S t).card ≤ 2) (hCg : ∀ t, 0 ≤ Cg t)
    (hdom : ∀ t, CoulombDominated C (Cg t) (κ t)) (u : En eta n)
    (hv : ∀ t q, (finiteCoefficientKernelOperator (κ t) u).ofLp q ≠ 0 →
      OutReg M (S t) (cidx n q))
    (a : Fin eta) {Kt : ℝ} (hK1 : 1 ≤ Kt) :
    ‖maskV (fun p => supTail a (Kt / (2 * Real.pi / L)) (cidx n p)) (gridV M cpl κ u)‖ ≤
      28 * (∑ t, |cpl t| * Cg t) * ctail C Hunit (2 * Real.pi / L) *
        (2 * sys.maxMass * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) *
          Kt ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨R, hR⟩ : ∃ R, R = ctail C Hunit (2 * Real.pi / L) *
      (2 * sys.maxMass * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) *
        Kt ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hlin : maskV (fun p => supTail a (Kt / (2 * Real.pi / L)) (cidx n p)) (gridV M cpl κ u) =
      ∑ t, (cpl t : ℂ) • maskV (fun p => supTail a (Kt / (2 * Real.pi / L)) (cidx n p))
        (gridDiag M (κ t) u) := by
    change maskL (fun p => supTail a (Kt / (2 * Real.pi / L)) (cidx n p))
      (∑ t, (cpl t : ℂ) • gridDiag M (κ t) u) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  have hRHS : 28 * (∑ t, |cpl t| * Cg t) * ctail C Hunit (2 * Real.pi / L) *
      (2 * sys.maxMass * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) *
        Kt ^ (-(1 / 2 : ℝ)) = ∑ t, |cpl t| * (28 * (Cg t * R)) := by
    rw [hR, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hlin, hRHS]
  calc ‖∑ t, (cpl t : ℂ) • maskV (fun p => supTail a (Kt / (2 * Real.pi / L)) (cidx n p))
        (gridDiag M (κ t) u)‖
      ≤ ∑ t, ‖(cpl t : ℂ) • maskV (fun p => supTail a (Kt / (2 * Real.pi / L)) (cidx n p))
          (gridDiag M (κ t) u)‖ := norm_sum_le _ _
    _ ≤ ∑ t, |cpl t| * (28 * (Cg t * R)) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine (tail_gridDiag_le M (S t) (hS t) (κ t) u (hv t) a _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h := grid_tail sys hL a hC Hunit hPeriodic (hCg t) (hdom t) hK1 u
        calc _ ≤ _ := h
          _ = Cg t * R := by rw [hR]; ring

omit [Fintype ν] in
/-- `grid_potential_tail` with the explicit periodic Hardy constant
(`canonicalPeriodicCoulombHardyBound_explicit`): no hypotheses beyond the kernel classes and the
alias region. -/
theorem grid_potential_tail_explicit (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {C : ℝ}
    (hC : 0 ≤ C) (hS : ∀ t, (S t).card ≤ 2) (hCg : ∀ t, 0 ≤ Cg t)
    (hdom : ∀ t, CoulombDominated C (Cg t) (κ t)) (u : En eta n)
    (hv : ∀ t q, (finiteCoefficientKernelOperator (κ t) u).ofLp q ≠ 0 →
      OutReg M (S t) (cidx n q))
    (a : Fin eta) {Kt : ℝ} (hK1 : 1 ≤ Kt) :
    ‖maskV (fun p => supTail a (Kt / (2 * Real.pi / L)) (cidx n p)) (gridV M cpl κ u)‖ ≤
      28 * (∑ t, |cpl t| * Cg t) *
        ctail C molecularCanonicalUnitHardyConstant (2 * Real.pi / L) *
        (2 * sys.maxMass * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) *
          Kt ^ (-(1 / 2 : ℝ)) :=
  grid_potential_tail M cpl κ S Cg sys hL hC _ canonicalPeriodicCoulombHardyBound_explicit hS hCg
    hdom u hv a hK1

end GridTail

end FSNormal
