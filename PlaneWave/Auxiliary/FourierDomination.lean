import PlaneWave.Auxiliary.DressedTails

/-!
# Auxiliary claims, part 5: Fourier domination and the uniform Kato–Rellich bound for truncated
kernels (`lem:fourier-domination`, `lem:grid-KR` (i))

On a cube `n` (large enough to contain the register zone and every output of a band-limited kernel
applied to a register state), in the momentum (Fourier) coordinates:

* `umod` (`u^#`, eq:fourier-modulus), the coordinatewise modulus; it preserves every nonnegative
  diagonal weighted norm (`weightedNormSq_umod`, `norm_umod`);
* **`fourier_domination`** (eq:fourier-domination): if `|κ(q,p)| ≤ C_g K(q,p)` with `K ≥ 0`, then
  for every nonnegative output weight `w` (in particular every Fourier support projector `Π`)
  `Σ_q w(q) |(κ u)(q)|² ≤ C_g² Σ_q w(q) |(K u^#)(q)|²`;
* **`dominated_pair_hardy`** (eq:dominated-Hardy): a kernel dominated by `C_g` times the Coulomb pair
  kernel `ŵ` of the pair `(i, j)` satisfies `‖κ u‖² ≤ (C_g B)² Σ_p (1 + |k_{p_r}|²) |u_p|²` for either
  member `r ∈ {i, j}`;
* **`dominated_single_hardy`**: the same for a single-register kernel dominated by `C_g ŵ`, which
  covers the translated clamped-nucleus kernels (`finiteTranslatedCoulombKernel_norm_le`);
* `fcko_const`: a constant coefficient `ĝ(0)` contributes `|ĝ(0)| ‖u‖`;
* **`grid_KR`** (eq:grid-KRpair): every operator with the weighted bound of register `r` (both cases
  above) satisfies `‖κ u‖ ≤ ε ‖T u‖ + (X + X²)(1 + m_r/ε) ‖u‖` for every `ε > 0`, `X = C_g B`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators
open PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν] {n : ℕ}

/-! ## The Fourier modulus -/

/-- The Fourier modulus `u^#` (eq:fourier-modulus): `(u^#)(p) = |u(p)|`. -/
noncomputable def umod (u : En eta n) : En eta n :=
  WithLp.toLp 2 (fun p => ((‖u.ofLp p‖ : ℝ) : ℂ))

omit [Fintype ν] in
lemma umod_apply (u : En eta n) (p : Cfg eta n) : (umod u).ofLp p = ((‖u.ofLp p‖ : ℝ) : ℂ) := rfl

omit [Fintype ν] in
lemma norm_umod_apply (u : En eta n) (p : Cfg eta n) : ‖(umod u).ofLp p‖ = ‖u.ofLp p‖ := by
  rw [umod_apply, Complex.norm_real, Real.norm_eq_abs, abs_norm]

omit [Fintype ν] in
/-- `u^#` preserves every diagonal weighted norm (`‖u‖`, `‖∇_r u‖`, `Θ(u)`, …). -/
lemma weightedNormSq_umod (w : Cfg eta n → ℝ) (u : En eta n) :
    weightedNormSq w (umod u) = weightedNormSq w u := by
  unfold weightedNormSq; simp_rw [norm_umod_apply]

omit [Fintype ν] in
lemma norm_umod (u : En eta n) : ‖umod u‖ = ‖u‖ := by
  have h1 := FSKernel.norm_sq_eq (umod u)
  have h2 := FSKernel.norm_sq_eq u
  simp_rw [norm_umod_apply] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (h1.trans h2.symm)

/-! ## Fourier domination -/

omit [Fintype ν] in
lemma fcko_apply (κ : Cfg eta n → Cfg eta n → ℂ) (u : En eta n) (q : Cfg eta n) :
    (finiteCoefficientKernelOperator κ u).ofLp q = ∑ p, u.ofLp p * κ q p := rfl

omit [Fintype ν] in
/-- The pointwise domination `|(κ u)(q)| ≤ C_g (K u^#)(q)`. -/
lemma norm_fcko_apply_le (κ K : Cfg eta n → Cfg eta n → ℂ) {Cg : ℝ}
    (hK : ∀ q p, K q p = ((‖K q p‖ : ℝ) : ℂ)) (hdom : ∀ q p, ‖κ q p‖ ≤ Cg * ‖K q p‖)
    (u : En eta n) (q : Cfg eta n) :
    ‖(finiteCoefficientKernelOperator κ u).ofLp q‖ ≤
      Cg * ‖(finiteCoefficientKernelOperator K (umod u)).ofLp q‖ := by
  rw [fcko_apply, fcko_apply]
  have e : ∀ p, (umod u).ofLp p * K q p = ((‖u.ofLp p‖ * ‖K q p‖ : ℝ) : ℂ) := by
    intro p
    have h := hK q p
    rw [umod_apply, Complex.ofReal_mul, ← h]
  rw [Finset.sum_congr rfl fun p _ => e p, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun p _ => by positivity), Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul]
  calc ‖u.ofLp p‖ * ‖κ q p‖ ≤ ‖u.ofLp p‖ * (Cg * ‖K q p‖) :=
        mul_le_mul_of_nonneg_left (hdom q p) (norm_nonneg _)
    _ = Cg * (‖u.ofLp p‖ * ‖K q p‖) := by ring

omit [Fintype ν] in
/-- **Fourier domination** (eq:fourier-domination): for a kernel with `|κ(q,p)| ≤ C_g K(q,p)`,
`K ≥ 0`, and every nonnegative output weight `w` (a Fourier support projector `Π` is `w = 1_Π`),
`Σ_q w(q) |(κ u)(q)|² ≤ C_g² Σ_q w(q) |(K u^#)(q)|²`. -/
theorem fourier_domination (κ K : Cfg eta n → Cfg eta n → ℂ) {Cg : ℝ}
    (hK : ∀ q p, K q p = ((‖K q p‖ : ℝ) : ℂ)) (hdom : ∀ q p, ‖κ q p‖ ≤ Cg * ‖K q p‖)
    (w : Cfg eta n → ℝ) (hw : ∀ q, 0 ≤ w q) (u : En eta n) :
    ∑ q, w q * ‖(finiteCoefficientKernelOperator κ u).ofLp q‖ ^ 2 ≤
      Cg ^ 2 * ∑ q, w q * ‖(finiteCoefficientKernelOperator K (umod u)).ofLp q‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have h := norm_fcko_apply_le κ K hK hdom u q
  have h2 : ‖(finiteCoefficientKernelOperator κ u).ofLp q‖ ^ 2 ≤
      (Cg * ‖(finiteCoefficientKernelOperator K (umod u)).ofLp q‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  calc w q * ‖(finiteCoefficientKernelOperator κ u).ofLp q‖ ^ 2
      ≤ w q * (Cg * ‖(finiteCoefficientKernelOperator K (umod u)).ofLp q‖) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (hw q)
    _ = Cg ^ 2 * (w q * ‖(finiteCoefficientKernelOperator K (umod u)).ofLp q‖ ^ 2) := by ring

omit [Fintype ν] in
/-- The Coulomb pair kernel is real and nonnegative. -/
lemma pairKernel_real (i j : Fin eta) (C : ℝ) (q p : Cfg eta n) :
    finiteElectronPairConfigurationKernel i j C n q p =
      ((‖finiteElectronPairConfigurationKernel i j C n q p‖ : ℝ) : ℂ) := by
  classical
  unfold finiteElectronPairConfigurationKernel
  split_ifs
  · unfold finiteCoulombKernel
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  · simp

omit [Fintype ν] in
/-- **Dominated Hardy, pair version** (eq:dominated-Hardy): a kernel dominated by `C_g` times the
Coulomb pair kernel of `(i, j)` has the weighted bound of either member `r ∈ {i, j}`:
`‖κ u‖² ≤ (C_g B)² Σ_p (1 + |k_{p_r}|²) |u_p|²`. -/
theorem dominated_pair_hardy {i j : Fin eta} (hij : i ≠ j) (g C B Hunit : ℝ) (hC : 0 ≤ C)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hScale : C * Hunit ^ 2 ≤ B ^ 2 * physicalH1Scale g)
    (κ : Cfg eta n → Cfg eta n → ℂ) {Cg : ℝ}
    (hdom : ∀ q p, ‖κ q p‖ ≤ Cg * ‖finiteElectronPairConfigurationKernel i j C n q p‖)
    {r : Fin eta} (hr : r = i ∨ r = j) :
    HasWeightedOperatorBound (fun p => 1 + finitePlaneWaveKabs g n (p r) ^ 2)
      (finiteCoefficientKernelOperator κ) (Cg * B) := by
  intro u
  have hreg : HasWeightedOperatorBound (fun p => 1 + finitePlaneWaveKabs g n (p r) ^ 2)
      (finiteElectronPairCoulombOperator i j C n) B := by
    rcases hr with rfl | rfl
    · exact finiteElectronPairCoulombOperator_registerBound_first _ _ hij g C B Hunit n hC
        hPeriodic hScale
    · exact finiteElectronPairCoulombOperator_registerBound_second _ _ hij g C B Hunit n hC
        hPeriodic hScale
  have h1 := fourier_domination κ (finiteElectronPairConfigurationKernel i j C n)
    (pairKernel_real i j C) hdom (fun _ => 1) (fun _ => zero_le_one) u
  simp only [one_mul] at h1
  rw [← FSKernel.norm_sq_eq, ← FSKernel.norm_sq_eq] at h1
  have h2 := hreg (umod u)
  rw [weightedNormSq_umod] at h2
  calc ‖finiteCoefficientKernelOperator κ u‖ ^ 2
      ≤ Cg ^ 2 * ‖finiteCoefficientKernelOperator
          (finiteElectronPairConfigurationKernel i j C n) (umod u)‖ ^ 2 := h1
    _ = Cg ^ 2 * ‖finiteElectronPairCoulombOperator i j C n (umod u)‖ ^ 2 := rfl
    _ ≤ Cg ^ 2 * (B ^ 2 *
          weightedNormSq (fun p => 1 + finitePlaneWaveKabs g n (p r) ^ 2) u) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (Cg * B) ^ 2 * weightedNormSq (fun p => 1 + finitePlaneWaveKabs g n (p r) ^ 2) u := by
        ring

omit [Fintype ν] in
/-- **Dominated Hardy, single-register version**: a one-register kernel dominated by `C_g ŵ`
(e.g. a translated clamped-nucleus kernel) has the weighted bound of its register, constant
`C_g B`. -/
theorem dominated_single_hardy (r : Fin eta) (g C B Hunit : ℝ) (hC : 0 ≤ C)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hScale : C * Hunit ^ 2 ≤ B ^ 2 * physicalH1Scale g)
    (κ : FinitePlaneWaveMode n → FinitePlaneWaveMode n → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hdom : ∀ v w, ‖κ v w‖ ≤ Cg * Real.sqrt (finiteCoulombDifferenceSquareWeight C n v w)) :
    HasWeightedOperatorBound (fun p => 1 + finitePlaneWaveKabs g n (p r) ^ 2)
      (referenceKernelConvolutionOperator r κ) (Cg * B) := by
  apply referenceKernelConvolutionOperator_registerBound
  intro a
  have hOne := oneParticleCoulombH1Bound_of_canonicalPeriodic g (Cg ^ 2 * C) (Cg * B) Hunit n
    (by positivity) hPeriodic (by
      calc Cg ^ 2 * C * Hunit ^ 2 = Cg ^ 2 * (C * Hunit ^ 2) := by ring
        _ ≤ Cg ^ 2 * (B ^ 2 * physicalH1Scale g) :=
            mul_le_mul_of_nonneg_left hScale (sq_nonneg _)
        _ = (Cg * B) ^ 2 * physicalH1Scale g := by ring)
  refine coulomb_dominated_kernel_oneParticle_h1 g (Cg ^ 2 * C) (Cg * B) n κ (fun v w => ?_) hOne a
  rw [show finiteCoulombDifferenceSquareWeight (Cg ^ 2 * C) n v w =
      Cg ^ 2 * finiteCoulombDifferenceSquareWeight C n v w by
        unfold finiteCoulombDifferenceSquareWeight latticeCoulombSquareWeight; ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCg]
  exact hdom v w

omit [Fintype ν] in
/-- A constant coefficient `ĝ(0)` contributes `|ĝ(0)| ‖u‖`. -/
lemma fcko_const (c : ℂ) (u : En eta n) :
    ‖finiteCoefficientKernelOperator (fun q p => if q = p then c else 0) u‖ = ‖c‖ * ‖u‖ := by
  classical
  have e : finiteCoefficientKernelOperator (fun q p => if q = p then c else 0) u = c • u := by
    ext q
    rw [fcko_apply, Finset.sum_eq_single q (fun p _ hp => by rw [if_neg (Ne.symm hp), mul_zero])
      (fun h => absurd (Finset.mem_univ q) h), if_pos rfl]
    simp [mul_comm]
  rw [e, norm_smul]

/-! ## The uniform Kato–Rellich bound -/

omit [Fintype ν] in
/-- `Σ_p A(p) |u_p|² ≤ ‖u‖ ‖T u‖`. -/
lemma sum_Asym_le (sys : CoulombSystem eta ν) (L : ℝ) (u : En eta n) :
    ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2 ≤
      ‖u‖ * ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖ := by
  have hA : ∀ p, 0 ≤ Asym sys L n p := fun p => by
    unfold Asym; have := massKineticSymbol_nonneg sys L n p; positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p => ‖u.ofLp p‖)
    (fun p => Asym sys L n p * ‖u.ofLp p‖)
  have hk : ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖ ^ 2 =
      ∑ p, (Asym sys L n p * ‖u.ofLp p‖) ^ 2 := by
    rw [FSKernel.norm_sq_eq]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [kin_apply', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA p)]
  have hu : ‖u‖ ^ 2 = ∑ p, ‖u.ofLp p‖ ^ 2 := FSKernel.norm_sq_eq u
  have e : ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2 = ∑ p, ‖u.ofLp p‖ * (Asym sys L n p * ‖u.ofLp p‖) :=
    Finset.sum_congr rfl fun p _ => by ring
  rw [e]
  have h0 : 0 ≤ ∑ p, ‖u.ofLp p‖ * (Asym sys L n p * ‖u.ofLp p‖) :=
    Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (mul_nonneg (hA p) (norm_nonneg _))
  rw [← hu, ← hk] at hcs
  have h2 : (∑ p, ‖u.ofLp p‖ * (Asym sys L n p * ‖u.ofLp p‖)) ^ 2 ≤
      (‖u‖ * ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖) ^ 2 := by rw [mul_pow]; exact hcs
  exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).mp h2

omit [Fintype ν] in
/-- The register weight is bounded by the kinetic energy: `1 + |k_r|² ≤ 1 + 2 m_r A`. -/
lemma register_weight_le (sys : CoulombSystem eta ν) (L : ℝ) (r : Fin eta) (p : Cfg eta n) :
    1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p r) ^ 2 ≤ 1 + 2 * sys.mass r * Asym sys L n p := by
  have h := component_sq_le_mass_mul_massKineticSymbol
    (fun a => lt_of_lt_of_le one_pos (sys.one_le_mass a)) (finitePlaneWaveKabs (2 * Real.pi / L) n)
    p r
  unfold Asym
  linarith

omit [Fintype ν] in
/-- **`lem:grid-KR` (i)** (eq:grid-KRpair): an operator with the weighted bound
`‖A u‖² ≤ X² Σ_p (1 + |k_{p_r}|²) |u_p|²` (the dominated pair or single-register kernels, `X = C_g B`)
satisfies `‖A u‖ ≤ ε ‖T u‖ + (X + X²)(1 + m_r/ε) ‖u‖` for every `ε > 0`. -/
theorem grid_KR (sys : CoulombSystem eta ν) (L : ℝ) (r : Fin eta)
    {A : En eta n →ₗ[ℂ] En eta n} {X : ℝ} (hX : 0 ≤ X)
    (hA : HasWeightedOperatorBound
      (fun p => 1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p r) ^ 2) A X)
    {ε : ℝ} (hε : 0 < ε) (u : En eta n) :
    ‖A u‖ ≤ ε * ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖ +
      (X + X ^ 2) * (1 + sys.mass r / ε) * ‖u‖ := by
  set a := ‖u‖ with ha
  set k := ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖ with hk
  have ha0 : 0 ≤ a := norm_nonneg _
  have hk0 : 0 ≤ k := norm_nonneg _
  have hm : 1 ≤ sys.mass r := sys.one_le_mass r
  have hw : weightedNormSq (fun p => 1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p r) ^ 2) u ≤
      a ^ 2 + 2 * sys.mass r * (a * k) := by
    unfold weightedNormSq
    calc ∑ p, (1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p r) ^ 2) * ‖u.ofLp p‖ ^ 2
        ≤ ∑ p, (1 + 2 * sys.mass r * Asym sys L n p) * ‖u.ofLp p‖ ^ 2 :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_right (register_weight_le sys L r p) (sq_nonneg _)
      _ = ∑ p, ‖u.ofLp p‖ ^ 2 + 2 * sys.mass r * ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2 := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ a ^ 2 + 2 * sys.mass r * (a * k) := by
          rw [← FSKernel.norm_sq_eq u]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_Asym_le sys L u) (by positivity))
  have h1 : ‖A u‖ ^ 2 ≤ X ^ 2 * (a ^ 2 + 2 * sys.mass r * (a * k)) :=
    (hA u).trans (mul_le_mul_of_nonneg_left hw (sq_nonneg _))
  set Y := X ^ 2 * sys.mass r * a / ε with hY
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hεY : ε * Y = X ^ 2 * sys.mass r * a := by rw [hY]; field_simp
  have h2 : X ^ 2 * (a ^ 2 + 2 * sys.mass r * (a * k)) ≤ (ε * k + X * a + Y) ^ 2 := by
    have e : X ^ 2 * (a ^ 2 + 2 * sys.mass r * (a * k)) = (X * a) ^ 2 + 2 * k * (ε * Y) := by
      rw [hεY]; ring
    rw [e]
    nlinarith [mul_nonneg hk0 hY0, mul_nonneg (mul_nonneg hX ha0) hY0,
      mul_nonneg (mul_nonneg hε.le hk0) (mul_nonneg hX ha0), sq_nonneg (ε * k), sq_nonneg Y]
  have h3 : ‖A u‖ ≤ ε * k + X * a + Y :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h1.trans h2)
  refine h3.trans ?_
  have h4 : X * a + Y ≤ (X + X ^ 2) * (1 + sys.mass r / ε) * a := by
    rw [hY]
    have : 0 ≤ X * (sys.mass r / ε) * a + X ^ 2 * a := by positivity
    have e : (X + X ^ 2) * (1 + sys.mass r / ε) * a =
        X * a + X ^ 2 * sys.mass r * a / ε + (X * (sys.mass r / ε) * a + X ^ 2 * a) := by
      field_simp; ring
    rw [e]; linarith
  linarith

end FSNormal
